import {readFileSync} from 'node:fs';
const cases=JSON.parse(readFileSync(new URL('./workflow-concurrent-progress/cases.json',import.meta.url)));
// 11:11 PT — read-only production reproduction; outside effects bound by native fixture.
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {hostname} from 'node:os';
import {fixture} from './helpers/workflow-delivery-fixture.mjs';
import * as runner from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
for(const state of ['cancelled','completed'])for(const operation of ['stepDone','askPerson','approveRun'])test(`${operation} racing ${state}`,async t=>{
 assert.ok(cases.cases.find(c=>c.id==='ended-run-races'));const f=await fixture(t,{agent:'codex',name:'bug'});assert.equal((await f.run()).exitCode,0);
 const run=f.record();if(operation==='approveRun'){run.gate={area:'story',at:1,kind:'approve'};run.state='waiting';writeRun(run,f.ports);}
 let injected=false,terminal;
 const ports={...f.ports,now:()=>{if(!injected){injected=true;terminal=f.record();terminal.state=state;terminal.gate=null;if(state==='cancelled')terminal.cancelled={at:2000};else terminal.doneAt=2000;writeRun(terminal,f.ports);}return 3000;}};
 const count=f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length;
 const args=operation==='stepDone'?{step:'reproduce',summary:'own',cwd:run.root}:operation==='askPerson'?{text:'own question',cwd:run.root}:{ref:'17',cwd:f.source};
 const result=await runner[operation](args,ports),saved=f.record();
 console.log(JSON.stringify({operation,state,injected,result,savedState:saved.state,gate:saved.gate,area:saved.area,newChats:f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length-count,done:saved.done,question:saved.question}));
 assert.equal(result.exitCode,1,result.message);assert.equal(saved.state,state,'ended run must stay ended');assert.deepEqual(saved.gate,terminal.gate);assert.equal(saved.area,terminal.area);assert.deepEqual(saved.done,terminal.done);assert.deepEqual(saved.question,terminal.question);assert.deepEqual(saved.decisions,terminal.decisions);assert.equal(f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length,count);assert.match(result.message,/cancelled|completed|ended/);
});
test('approve refuses newer gate',async t=>{
 assert.ok(cases.cases.find(c=>c.id==='ended-run-races'));const f=await fixture(t,{agent:'codex',name:'bug'});assert.equal((await f.run()).exitCode,0);let r=f.record();r.gate={area:'story',at:1,kind:'approve'};r.state='waiting';writeRun(r,f.ports);let changed;
 const result=await runner.approveRun({ref:'17',cwd:f.source},{...f.ports,confirm:async()=>{changed=f.record();changed.gate={area:'story',at:2000,kind:'approve'};writeRun(changed,f.ports);return true;}});
 console.log(JSON.stringify({case:'newer gate',result,area:f.record().area,gate:f.record().gate}));assert.equal(result.exitCode,1);assert.equal(f.record().area,changed.area);assert.match(result.message,/gate changed.*look again/i);
});
for(const shape of ['approve','approve-pr'])for(const change of ['time','area','kind','removed'])for(const approvalVia of ['terminal','chat'])test(`2753 ${shape} approval via ${approvalVia} refuses ${change} gate`,async t=>{
 assert.ok(cases.cases.some(c=>c.id==='stale-gate-approval'));
 const f=await fixture(t,{agent:'codex',name:'bug'});await f.run();const run=f.record();run.gate={area:'story',kind:shape,at:1};run.state='waiting';
 if(shape==='approve-pr'){run.areas[0].gate='pr';run.areas[0].before='approve';}
 writeRun(run,f.ports);let newer;
 const replace=()=>{newer=f.record();if(change==='removed')newer.gate=null;else if(change==='time')newer.gate.at=2;else if(change==='kind')newer.gate.kind='ask-code';else{newer.area=1;newer.gate.area=newer.areas[1].name;}writeRun(newer,f.ports);};
 const ports=approvalVia==='terminal'?{...f.ports,confirm:async()=>{replace();return true;}}:f.agentPorts({readApprovalEvidence:async()=>{replace();return {ok:true,userMessage:'I approve',userMessageAt:3,sessionId:'00000000-0000-4000-8000-000000000017'};}});
 const beforeChats=f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length;
 const out=await runner.approveRun({ref:'17',cwd:f.source},ports);assert.equal(out.exitCode,1,out.message);assert.match(out.message,/gate changed, look again/i);assert.deepEqual(f.record(),newer);assert.equal(f.pushes.length,0);assert.equal(f.prs.length,0);assert.equal(f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length,beforeChats);
});
for(const ending of ['cancelled','completed'])test(`2753 final done gate respects ${ending}`,async t=>{
 const f=await fixture(t,{agent:'codex',name:'bug'});await f.run();const run=f.record();run.areas[0].steps=['reproduce'];writeRun(run,f.ports);let newer;
 const out=await runner.stepDone({step:'reproduce',summary:'Finished',cwd:run.root},{...f.ports,now:()=>{if(!newer){newer=f.record();newer.state=ending;newer.gate=null;writeRun(newer,f.ports);}return 3000;}});
 assert.equal(out.exitCode,1);assert.match(out.message,/run ended/i);assert.deepEqual(f.record(),newer);
});
