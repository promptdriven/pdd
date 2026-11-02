import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {openRun,approveRun,stepDone,runStatus} from '../src/workflow-runner.mjs';
import {fixture,packageRoot} from './helpers/workflow-runner-fixture.mjs';
const lost=()=>Object.assign(Error('lost reply'),{code:'server_unavailable'});
const open=(f,extra={},ports=f.ports)=>openRun({ref:'17',cwd:f.source,packageRoot,...extra},ports);
const runs=f=>f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run');
test('historical lost-close recovery never launches an earlier-area agent',async t=>{
 const f=await fixture(t);assert.equal((await f.run()).exitCode,0);const original=f.record().chats.at(-1),healthy=f.ports.herdr;
 f.ports.herdr=async args=>{const reply=await healthy(args);if(args[0]==='tab'&&args[1]==='close')throw lost();return reply;};
 assert.equal((await open(f,{newSession:true})).exitCode,1);f.ports.herdr=healthy;f.tick();
 assert.equal((await stepDone({step:'scope',summary:'Plan prepared',cwd:f.record().root},f.agentPorts())).exitCode,0);
 assert.equal((await approveRun({ref:'17',cwd:f.source,packageRoot},f.ports)).exitCode,0);
 f.ports.findNativeSessions=async()=>[{id:original.session.id}];const before=f.record(),count=runs(f).length;
 const out=await open(f,{newSession:true});assert.equal(runs(f).length,count,'Historical recovery must not dispatch any fresh session');
 assert.equal(out.exitCode,0,out.message);assert.match(f.record().chatReplacement.phase,/^(rolledBack|ended)$/);
 assert.equal(f.record().area,before.area);assert.deepEqual(f.record().chats.find(c=>c.area==='build'),before.chats.find(c=>c.area==='build'));
});
test('plain open excludes a competing replacement while paused',async t=>{
 const f=await fixture(t);await f.run();const original=f.record().chats.at(-1);f.herdr.paneOf(original).agent=null;
 const healthy=f.ports.herdr;let entered,release;const reached=new Promise(r=>entered=r),gate=new Promise(r=>release=r);
 const pending=open(f,{}, {...f.ports,herdr:async args=>{if(args[0]==='status'){entered();await gate;}return healthy(args);}});
 await reached;let out;try{out=await open(f,{newSession:true});}finally{release();}
 await pending;assert.equal(out.exitCode,1,'Competing --new must refuse while plain open owns the run lock');
 assert.equal(f.herdr.panes.filter(p=>p.agent).length,1);
 assert.doesNotMatch(out.message,/chat-replacement\.lock/,'Busy advice must describe another open operation in plain words');
});
test('lost launch waits startup grace before any same-session resume',async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{const reply=await healthy(args);if(args[0]==='pane'&&args[1]==='run')throw lost();return reply;};
 await open(f,{newSession:true});f.ports.herdr=healthy;const pending=f.record().chatReplacement;
 assert.ok(pending,'A lost launch reply must retain public replacement custody for startup-grace recovery');
 assert.ok(pending.replacement,'A lost launch reply must retain the exact replacement descriptor before startup-grace recovery');
 f.herdr.paneOf(pending.replacement).agent=null;f.ports.findNativeSessions=async()=>[{id:pending.replacement.session.id}];
 const count=runs(f).length;const out=await open(f,{newSession:true});assert.equal(runs(f).length,count,'No resume dispatch during START_GRACE_MS');
 assert.equal(out.exitCode,1);assert.match(out.message,/open 17 --new/);
});
test('pending State and Next both show the resolving --new command',async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{const reply=await healthy(args);if(args[0]==='tab'&&args[1]==='close')throw lost();return reply;};
 await open(f,{newSession:true});f.ports.herdr=healthy;
 const out=await runStatus({ref:'17',cwd:f.source},f.ports);
 for(const label of ['State:','Next:']){const line=out.message.split('\n').find(line=>line.includes(label));assert.match(line??'',/pdd workflow open 17 --new/,label+' names resolver');}
});

for (const present of [false,true]) test(`pane_not_found requires inventory absence: ${present}`,async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{if(args[0]==='tab'&&args[1]==='close'){if(!present)await healthy(args);throw lost();}return healthy(args);};
 await open(f,{newSession:true});const record=f.record().chatReplacement;
 f.ports.findNativeSessions=async()=>[{id:record.original.session.id}];
 f.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='get'&&args[2]===record.original.paneId)throw Object.assign(Error('missing pane'),{code:'pane_not_found'});return healthy(args);};
 const count=runs(f).length,out=await open(f,{newSession:true});
 assert.equal(out.exitCode,present?1:0,out.message);
 if(present)assert.equal(runs(f).length,count,'Present pane never permits resume from pane_not_found');
 else assert.equal(f.record().chatReplacement.phase,'launched');
});
test('replacement tab retains the exact area label',async t=>{
 const f=await fixture(t);await f.run();const area=f.record().chats.at(-1).area;
 assert.equal((await open(f,{newSession:true})).exitCode,0);
 const chat=f.record().chats.at(-1);assert.equal(f.herdr.tabs.find(tab=>tab.tab_id===chat.tabId).label,area,'Visible label must be the area without attempt UUID');
});

for(const boundary of ['close','allocation-check','create','launch-check'])test(`progress at ${boundary} forbids a fresh historical launch`,async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;let advanced=false;
 const advance=()=>{const saved=f.record();saved.area=1;saved.done.scope={summary:'concurrent progress'};writeFileSync(saved.runDir+'/status.json',JSON.stringify(saved));advanced=true;};
 f.ports.herdr=async args=>{const reply=await healthy(args);
   if(!advanced && (boundary==='close'&&args[0]==='tab'&&args[1]==='close' || boundary==='allocation-check'&&args[0]==='workspace'&&args[1]==='list'&&f.record().chatReplacement?.phase==='createRequested' || boundary==='create'&&args[0]==='tab'&&args[1]==='create' || boundary==='launch-check'&&args[0]==='agent'&&args[1]==='get'&&f.record().chatReplacement?.phase==='prepared'))advance();
   return reply;};
 // Empty prepared panes throw agent_not_found, so publish progress before returning that inspection too.
 if(boundary==='launch-check')f.ports.herdr=async args=>{if(!advanced&&args[0]==='agent'&&args[1]==='get'&&f.record().chatReplacement?.phase==='prepared')advance();return healthy(args);};
 // Lead's historical cleanup rule now requires positive evidence of the owned empty shell.
 const observing=f.ports.herdr;
 f.ports.herdr=args=>args[0]==='pane'&&args[1]==='process-info' ? Promise.resolve({result:{type:'pane_process_info',process_info:{pane_id:args[3],shell_pid:41,foreground_process_group_id:41,foreground_processes:[{pid:41,name:'bash'}]}}}) : observing(args);
 const before=runs(f).length,out=await open(f,{newSession:true});assert.equal(advanced,true);
 assert.equal(runs(f).length,before,'Checkpoint reread must prevent dispatch after concurrent area progress');
 assert.equal(out.exitCode,0,out.message);assert.equal(f.record().chatReplacement.phase,'ended');assert.equal(f.record().area,1);
 const prepared=f.record().chatReplacement.replacement;
 if(prepared)assert.equal(f.herdr.tabs.some(tab=>tab.tab_id===prepared.tabId),false,'Historical empty owned tab is closed');
});
test('cancellation before final launch checkpoint prevents dispatch',async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;let cancelled=false;
 f.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='get'&&f.record().chatReplacement?.phase==='prepared'){
 const saved=f.record();saved.state='cancelled';saved.cancelled={state:'cancelled',at:f.clock};writeFileSync(saved.runDir+'/status.json',JSON.stringify(saved));cancelled=true;}return healthy(args);};
 const before=runs(f).length;assert.equal((await open(f,{newSession:true})).exitCode,1);assert.equal(cancelled,true);assert.equal(runs(f).length,before);assert.equal(f.record().state,'cancelled');
});
