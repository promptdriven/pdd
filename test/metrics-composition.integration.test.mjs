import './helpers/test-home.mjs';
import { isolatedCheckCapacity } from './helpers/check-machine.mjs';
import { healthyMachine } from './helpers/healthy-machine.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {execFileSync,spawnSync} from 'node:child_process';
import { tickAutopilot } from '../src/autopilot-launcher.mjs';
const autopilotLaunchFingerprint = () => 'full-engine-launch';
import {writeRun,updateRun} from '../src/workflow-runs.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
const at=Date.parse('2026-11-05T00:00:00Z');
function selector(t,{issues=true}={}) {
 const root=fs.mkdtempSync(join(tmpdir(),'pdd-composed-selector-'));t.after(()=>fs.rmSync(root,{recursive:true,force:true}));execFileSync('git',['init','-q',root]);
 fs.writeFileSync(join(root,'pdd.json'),JSON.stringify({autopilot:{mode:'auto'}}));const stateFile=join(root,'state.json');
 const home=join(root,'home'), activatedAt='2026-11-04T00:00:00Z', coordinator={version:'pdd.autopilot-coordinator.v1',repository:'Owner/Repo',coordinatorId:'c',machine:'m',activation:activatedAt};
 fs.mkdirSync(home);
 fs.writeFileSync(stateFile,JSON.stringify({enabled:true,defaultBranch:'main',baseBranch:'main',cwd:root,repo:'Owner/Repo',activatedAt,coordinatorId:'c',machine:'m',environment:{HOME:home},agent:{id:'codex',kind:'codex',command:'codex',env:{}},stateFile,workspaceId:'w',paneId:'p',recipeDelivered:true,ownerLaunch:{paneId:'p',startedAt:1,coordinator,profile:{agent:{id:'codex',kind:'codex'},home,definitionHome:home,configHome:null},fingerprint:autopilotLaunchFingerprint({cwd:root,agent:{kind:"codex"}})}}));
 const rows=issues?[{number:1,state:'open',title:'One',body:'body',user:{login:'owner'},author_association:'OWNER',created_at:'2026-11-04T00:01:00Z',updated_at:'2026-11-04T00:01:00Z',comments:0,labels:[],html_url:'https://example.test/1'}]:[];
 const liveIssues=new Map(rows.map(row=>[row.number,row]));
 const f={root,stateFile,liveIssues,sent:[],ports:{...healthyMachine,now:()=>at,warn:()=>{},allocationCheck:async()=>({state:'ready',message:''}),queryIssues:async()=>({status:200,issues:rows}),run:async (command,args)=>({code:0,stdout:command==='git'?execFileSync('git',args,{cwd:root,encoding:'utf8'}):'{}',stderr:''})}};
 f.ports.checkCapacityPorts=isolatedCheckCapacity(f.root);
 f.ports.reconcileDependencyIntake=async()=>({eligible:rows.map(row=>row.html_url),queued:[],skipped:[]});
 f.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='get')return {result:{agent:{agent_status:'idle',agent_session:'session'}}};if(args[0]==='pane'&&args[1]==='read')return '';if(args[0]==='agent'&&args[1]==='prompt'){const text=args.at(-1),match=/Artifact path: (.+)/.exec(text);f.sent.push(match?fs.readFileSync(JSON.parse(match[1]),'utf8'):text);}return {};};
 f.tick=()=>tickAutopilot(stateFile,f.ports);return f;
}
function storage(t) {
 const root=fs.mkdtempSync(join(tmpdir(),'pdd-composed-run-'));t.after(()=>fs.rmSync(root,{recursive:true,force:true}));const commonDir=join(root,'.git'),runDir=join(commonDir,'pdd','runs','1');fs.mkdirSync(commonDir);
 return {root,runDir,run:{v:1,runId:'one',repo:'example/repo',number:1,root,sourceRoot:root,commonDir,runDir,state:'running',workflow:'small-change',areas:[{name:'code',steps:['build'],optional:[]}],area:0,chats:[],done:{},pr:[]},ports:{env:{HOME:root},stateDir:join(root,'state'),now:()=>at,skipMetricsDelivery:true,metricsWarning:()=>{}}};
}
test('composed storage retains pending capture and ordinary success under throwing warning',t=>{
 const f=storage(t);f.run.metricsObservations=[{type:'coverage',at:new Date(at).toISOString(),data:{complete:false}}];
 const originalWrite=fs.writeFileSync;const ports={...f.ports,metricsWarning:()=>{throw Error('warn failed');},runFiles:{writeFileSync:(path,...args)=>{if(String(path).includes('.identity-'))throw Error('metrics identity failed');return originalWrite(path,...args);}}};
 assert.equal(writeRun(f.run,ports),f.run);let saved=JSON.parse(fs.readFileSync(join(f.runDir,'status.json'),'utf8'));assert.equal(saved.metrics.coverageGap,true);assert.equal(saved.metricsObservations.length,1);
 saved=updateRun(f.runDir,r=>r,f.ports);assert.equal(saved.metricsObservations,undefined);assert.equal(saved.metrics.events.filter(e=>e.type==='coverage').length,1);
});
test('composed storage preserves pathname write port and native rename failure',t=>{
 const f=storage(t);let statusWrites=0;const files={writeFileSync:(path,...args)=>{assert.equal(typeof path,'string');if(path.includes('.status.json.'))statusWrites++;return fs.writeFileSync(path,...args);}};
 writeRun(f.run,{...f.ports,runFiles:files});assert.equal(statusWrites,1);const before=fs.readFileSync(join(f.runDir,'status.json'),'utf8');
 assert.throws(()=>updateRun(f.runDir,r=>{r.message='must not commit';return r;},{...f.ports,runFiles:{renameSync:(from,to)=>{if(to===join(f.runDir,'status.json'))throw Error('native rename failed');return fs.renameSync(from,to);}}}),/native rename failed/);
 assert.equal(fs.readFileSync(join(f.runDir,'status.json'),'utf8'),before);
});
test('composed storage contains post-commit drain and warning rejection',async t=>{
 const f=storage(t);f.run.done.build={at};const ports={...f.ports,skipMetricsDelivery:false,metricsAppendEvents:async()=>{throw Error('append failed');},metricsWarning:()=>{throw Error('warning failed');},metricsGap:()=>{throw Error('gap failed');}};
 writeRun(f.run,ports);assert.equal(JSON.parse(fs.readFileSync(join(f.runDir,'status.json'),'utf8')).done.build.at,at);
 await new Promise(resolve=>setImmediate(resolve));await new Promise(resolve=>setImmediate(resolve));
 const saved=JSON.parse(fs.readFileSync(join(f.runDir,'status.json'),'utf8'));assert.equal(saved.done.build.at,at);assert.equal(saved.metrics.coverageGap,true);assert.equal(saved.metrics.events.filter(e=>e.type==='step').length,1);
});
test('composed workflow dispatch forwards metadata together with draft/base/adoption',async()=>{
 let actual;const stream={write(){}};const result=await runPdd(['workflow','run','feature','17','--draft','--base','topic','--adopt-corpus','corpus.json','--origin','autopilot','--decision-id','token','--outcome','code'],{stdout:stream,stderr:stream,workflowAgents:{checkWorkflowAgents:async()=>({ok:true})},workflowRunner:{startRun:async input=>{actual=input;return {exitCode:0,message:'ok'};}},pathDiagnostic:()=>[]});
 assert.equal(result,0);assert.deepEqual([actual.draft,actual.base,actual.adoptCorpus,actual.origin,actual.decisionId,actual.outcome],[true,'topic','corpus.json','autopilot','token','code']);
});
test('real CLI recovers retained journal after process exit and discovers over 200 runs',t=>{
 const f=storage(t);execFileSync('git',['init','-q',f.root]);execFileSync('git',['remote','add','origin','https://github.com/example/repo.git'],{cwd:f.root});
 const code=`import {writeRun} from ${JSON.stringify(new URL('../src/workflow-runs.mjs',import.meta.url).href)};const run=${JSON.stringify({...f.run,done:{build:{at}}})};writeRun(run,{stateDir:${JSON.stringify(join(f.root,'state'))},metricsAppendEvents:()=>new Promise(()=>{}),metricsWarning:()=>{}});process.exit(0);`;
 const child=spawnSync(process.execPath,['--input-type=module','-e',code],{encoding:'utf8'});assert.equal(child.status,0,child.stderr);
 const journal=JSON.parse(fs.readFileSync(join(f.runDir,'status.json'),'utf8')).metrics.events;assert.equal(journal.length,1);
 for(let n=2;n<=202;n++) {const dir=join(f.run.commonDir,'pdd','runs',n===202?'202-cancelled-a1':String(n));fs.mkdirSync(dir,{recursive:true});fs.writeFileSync(join(dir,'status.json'),JSON.stringify({v:1,runId:`legacy${n}`,repo:'example/repo',number:n,state:n===202?'cancelled':'completed',done:{build:{at}}}));}
 const output=join(f.root,'export.json'),bin=new URL('../bin/pdd.mjs',import.meta.url).pathname;
 const offline=join(f.root,'offline-bin');fs.mkdirSync(offline);fs.writeFileSync(join(offline,'gh'),'#!/bin/sh\nexit 1\n',{mode:0o755});
 const exported=()=>{const result=spawnSync(process.execPath,[bin,'metrics','export',output],{cwd:f.root,encoding:'utf8',env:{...process.env,HOME:f.root,GH_CONFIG_DIR:f.root,GH_TOKEN:'',GITHUB_TOKEN:'',PATH:offline+':'+process.env.PATH}});assert.equal(result.status,0,result.stderr);return JSON.parse(fs.readFileSync(output,'utf8'));};
 const first=exported();assert.ok(first.events.some(e=>e.id===journal[0].id));assert.equal(new Set(first.events.filter(e=>e.type==='step').map(e=>e.issue)).size,202);assert.ok(first.events.some(e=>e.issue===202));
 const second=exported();assert.deepEqual(second.events.map(e=>[e.source,e.id]).sort(),first.events.map(e=>[e.source,e.id]).sort());
});
