import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync} from 'node:fs';
import {openRun, cancelRun, runStatus} from '../src/workflow-runner.mjs';
import * as runner from '../src/workflow-runner.mjs';
import * as chatModule from '../src/workflow-chat.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
const attempt = f => {const record=f.record().chatReplacement;assert.ok(record,'Replacement custody must be saved');return record;};
const open = (f, extra={}) => openRun({ref:'17',cwd:f.source,packageRoot,...extra}, f.ports);
for (const mode of ['extra pane','agent caller']) test(`replacement preclose refusal preserves saved run: ${mode}`,async t=>{
 const f=await fixture(t); assert.equal((await f.run()).exitCode,0);
 const chat=f.record().chats.at(-1), path=chat.messageFile.replace(/[^/]+$/,'status.json'), before=readFileSync(path,'utf8');
 if(mode==='extra pane') f.herdr.panes.push({...f.herdr.paneOf(chat),pane_id:'extra'});
 else f.ports.env.PDD_AGENT_SESSION='1';
 assert.equal((await open(f,{newSession:true})).exitCode,1);
 assert.equal(readFileSync(path,'utf8'),before);
});
test('pending replacement can cancel and status points to recovery',async t=>{
 const f=await fixture(t); await f.run(); const herdr=f.ports.herdr;
 f.ports.herdr=async args=>{if(args[0]==='tab'&&args[1]==='close')throw Object.assign(Error('lost'),{code:'lost'}); return herdr(args);};
 await open(f,{newSession:true});
 const status=await runStatus({ref:'17',cwd:f.source},f.ports);
 assert.match(status.message,/closeRequested/); assert.match(status.message,/open 17 --new/);
 assert.equal((await cancelRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
 assert.equal(f.record().state,'cancelled');
});
test('lost close with usable original rolls back same attempt',async t=>{
 const f=await fixture(t); await f.run(); const herdr=f.ports.herdr, original=f.record().chats.at(-1);
 f.ports.herdr=async args=>{if(args[0]==='tab'&&args[1]==='close')throw Object.assign(Error('lost'),{code:'lost'}); return herdr(args);};
 await open(f,{newSession:true}); const out=await open(f,{newSession:true});
 assert.equal(out.exitCode,0,out.message); assert.equal(attempt(f).phase,'rolledBack');
 assert.equal(f.record().chats.at(-1).paneId,original.paneId); assert.equal(f.record().abandonedChats.length,1);
});
test('replacement accepts nonempty successful launch reply',async t=>{
 const f=await fixture(t); await f.run(); const herdr=f.ports.herdr;
 f.ports.herdr=async args=>{const reply=await herdr(args); return args[0]==='pane'&&args[1]==='run'?{result:{type:'ok'}}:reply;};
 const out=await open(f,{newSession:true}); assert.equal(out.exitCode,0,out.message);
 assert.equal(attempt(f).phase,'launched');
});

test('status observation never excludes done while Herdr is delayed',async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 let entered,release;const reached=new Promise(r=>entered=r),gate=new Promise(r=>release=r);
 const status=runStatus({ref:'17',cwd:f.source},{...f.ports,herdr:async args=>{if(args[0]==='agent'&&args[1]==='get'){entered();await gate;}return healthy(args);}});
 await reached;
 try {const {stepDone}=runner; const out=await stepDone({step:'scope',summary:'Plan prepared',cwd:f.record().root},f.agentPorts()); assert.equal(out.exitCode,0,out.message); assert.doesNotMatch(out.message,/busy|chat-replacement.lock/);}
 finally {release();}
 await status;
});
for (const command of ['approve','done','ask','changes','evidence','cancel','open','area','status']) test(`pending command retains legacy behavior: ${command}`,async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{if(args[0]==='tab'&&args[1]==='close')throw Object.assign(Error('lost'),{code:'lost'});return healthy(args);};
 await open(f,{newSession:true});const run=f.record();
 const m=runner;
 const actions={approve:()=>m.approveRun({ref:'17',cwd:f.source},f.ports),done:()=>m.stepDone({step:'scope',summary:'Plan prepared',cwd:run.root},f.agentPorts()),ask:()=>m.askPerson({text:'Review this plan?',cwd:run.root},f.agentPorts()),changes:()=>m.changeRun({ref:'17',text:'Update the plan',cwd:f.source},f.ports),evidence:()=>m.recordEvidence({ref:'17',summaryFile:'/nonexistent-fixture',cwd:f.source},f.ports),cancel:()=>m.cancelRun({ref:'17',cwd:f.source},f.ports),open:()=>open(f),area:()=>open(f,{area:run.areas[run.area].name}),status:()=>m.runStatus({ref:'17',cwd:f.source},f.ports)};
 const out=await actions[command](); assert.doesNotMatch(out.message,/Inspect the saved attempt before changing|busy|chat-replacement.lock/);
 if(['open','area','status'].includes(command))assert.match(out.message,/open 17 --new/);
 if(command==='cancel')assert.equal(f.record().state,'cancelled');
});
test('alive replacement with unknown process stays pending despite exact session file',async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{if(args[0]==='pane'&&args[1]==='run')throw Object.assign(Error('lost'),{code:'lost'});return healthy(args);};
 await open(f,{newSession:true});const pending=attempt(f);
 f.tick(30_000); // Approved startup grace expires before exact-session recovery.
 f.ports.findNativeSessions=async()=>[{id:pending.replacement.session.id}]; f.ports.herdr=healthy;
 const count=f.herdr.calls.filter(args=>args[0]==='pane'&&args[1]==='run').length;
 const out=await open(f,{newSession:true});assert.notEqual(out.exitCode,0,out.message);
 const after=f.record();assert.equal(after.chatReplacement.id,pending.id);assert.equal(after.chats.at(-1).session.id,pending.replacement.session.id);
 assert.equal(after.chatReplacement.phase,'launchRequested');assert.match(out.message,/cancel/);
 assert.equal(f.herdr.calls.filter(args=>args[0]==='pane'&&args[1]==='run').length,count,'Exact native file cannot authorize dispatch into an unknown live process');
});
test('lost create reply adopts one allocated container in same attempt',async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{const reply=await healthy(args);if(args[0]==='tab'&&args[1]==='create')throw Object.assign(Error('lost'),{code:'lost'});return reply;};
 await open(f,{newSession:true});const pending=attempt(f),creates=f.herdr.calls.filter(args=>args[0]==='tab'&&args[1]==='create').length;
 f.ports.herdr=healthy;const out=await open(f,{newSession:true});assert.equal(out.exitCode,0,out.message);
 assert.equal(attempt(f).id,pending.id);assert.equal(f.herdr.calls.filter(args=>args[0]==='tab'&&args[1]==='create').length,creates);
});
test('delayed status cannot restore old chat after replacement',async t=>{
 const f=await fixture(t);await f.run();const run=f.record(),old=run.chats.at(-1),path=old.messageFile.replace(/[^/]+$/,'status.json');
 old.startUnconfirmed=true;writeFileSync(path,JSON.stringify(run));const healthy=f.ports.herdr;
 let entered,release;const reached=new Promise(r=>entered=r),gate=new Promise(r=>release=r);
 const status=runStatus({ref:'17',cwd:f.source},{...f.ports,herdr:async args=>{if(args[0]==='agent'&&args[1]==='get'){const reply=await healthy(args);entered();await gate;return reply;}return healthy(args);}});
 await reached;let replacement;
 try {assert.equal((await open(f,{newSession:true})).exitCode,0);replacement=f.record().chats.at(-1);}finally{release();}
 await status;assert.equal(f.record().chats.at(-1).paneId,replacement.paneId);assert.equal(attempt(f).phase,'launched');
});
test('cancellation during replacement checkpoint prevents later allocation and launch',async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{const reply=await healthy(args);if(args[0]==='tab'&&args[1]==='close'){const run=f.record();run.state='cancelled';run.cancelled={state:'cancelled',at:f.clock};writeFileSync(run.runDir+'/status.json',JSON.stringify(run));}return reply;};
 const out=await open(f,{newSession:true});assert.equal(out.exitCode,1);assert.equal(f.record().state,'cancelled');
 assert.equal(f.herdr.calls.filter(args=>args[0]==='tab'&&args[1]==='create').length,1,'Only initial chat allocation');
 assert.equal(f.herdr.calls.filter(args=>args[0]==='pane'&&args[1]==='run').length,1,'Only initial run launch');
});
test('progress may advance while pending and recovery preserves new area',async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{if(args[0]==='tab'&&args[1]==='close')throw Object.assign(Error('lost'),{code:'lost'});return healthy(args);};
 await open(f,{newSession:true});const run=f.record(),id=attempt(f).id;
 const {stepDone,approveRun}=runner;
 assert.equal((await stepDone({step:'scope',summary:'approved progress',cwd:run.root},f.agentPorts())).exitCode,0);
 const advanced=await approveRun({ref:'17',cwd:f.source},f.ports);assert.equal(advanced.exitCode,0,advanced.message);
 const current=f.record().chats.at(-1);
 const saved=f.record();saved.chatFailure={area:'build',phase:'open',code:'synthetic',message:'current failure'};writeFileSync(run.runDir+'/status.json',JSON.stringify(saved));
 f.ports.herdr=healthy;const out=await open(f,{newSession:true});assert.equal(out.exitCode,0,out.message);
 assert.equal(f.record().area,1);assert.equal(f.record().done.scope.summary,'approved progress');assert.equal(attempt(f).id,id);assert.equal(attempt(f).phase,'rolledBack');assert.equal(f.record().chatFailure.message,'current failure');assert.equal(f.record().chats.find(c=>c.area==='build').paneId,current.paneId);
 const fresh=await open(f,{newSession:true});assert.equal(fresh.exitCode,0,fresh.message);assert.notEqual(attempt(f).id,id);
});
for(const phase of ['intent','closed','createRequested','prepared'])test(`interrupted ${phase} resolves same pending attempt`,async t=>{
 const f=await fixture(t);await f.run();const run=f.record(),chat=run.chats.at(-1),path=run.runDir+'/status.json';
 const {restartChat}=chatModule;assert.equal(typeof restartChat,'function');
 await assert.rejects(()=>restartChat({run,chat,message:'Continue the same work.'},{...f.ports,checkpoint:async record=>{
   run.chatReplacement=record;if(record.phase==='intent')run.abandonedChats=[{...record.original,replacementId:record.id}];writeFileSync(path,JSON.stringify(run));if(record.phase===phase)throw Error('Interrupted checkpoint');
 }}));
 const pending=attempt(f);
 const out=await open(f,{newSession:true});assert.equal(out.exitCode,0,out.message);
 const after=f.record();assert.equal(after.chatReplacement.id,pending.id);assert.equal(after.abandonedChats.length,1);
 assert.equal(after.chatReplacement.phase,phase==='intent'?'rolledBack':'launched');
});
test('lost exact-session resume cannot dispatch twice before observation',async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{if(args[0]==='pane'&&args[1]==='run')throw Object.assign(Error('lost'),{code:'lost'});return healthy(args);};
 await open(f,{newSession:true});const pending=attempt(f);let resumes=0;
 // Complete inventory proves the old container absent; exact saved-session recovery may resume.
 f.herdr.tabs=f.herdr.tabs.filter(tab=>tab.tab_id!==pending.replacement.tabId);
 f.herdr.panes=f.herdr.panes.filter(pane=>pane.pane_id!==pending.replacement.paneId);
 f.tick(30_000); // Approved startup grace expires before exact-session recovery.
 f.ports.findNativeSessions=async()=>[{id:pending.replacement.session.id}];
 f.ports.herdr=async args=>{if(args[0]==='pane'&&args[1]==='run'){resumes++;throw Object.assign(Error('lost'),{code:'lost'});}return healthy(args);};
 assert.equal((await open(f,{newSession:true})).exitCode,1);
 assert.equal((await open(f,{newSession:true})).exitCode,1);
 assert.equal(resumes,1,'Unobserved resume dispatch remains uncertain');
});
for(const recovery of [{closeAcknowledged:'true'},{resumeRequested:1},{allocationLabel:''},{tabIdsBefore:['same','same']},{unknown:true}])test(`malformed recovery metadata refuses without effects: ${JSON.stringify(recovery)}`,async t=>{
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{if(args[0]==='tab'&&args[1]==='close')throw Object.assign(Error('lost'),{code:'lost'});return healthy(args);};
 await open(f,{newSession:true});const run=f.record();assert.ok(run.chatReplacement);run.chatReplacement.recovery=recovery;const path=run.runDir+'/status.json';writeFileSync(path,JSON.stringify(run));
 const before=readFileSync(path,'utf8'),count=f.herdr.calls.length;
 assert.equal((await open(f,{newSession:true})).exitCode,1);assert.equal(readFileSync(path,'utf8'),before);assert.equal(f.herdr.calls.length,count);
});

test('lost allocation recovers its unique attempt without launch after public progress creates a peer tab',async t=>{
 const f=await fixture(t);assert.equal((await f.run()).exitCode,0);
 const run=f.record(),original=run.chats.at(-1),healthy=f.ports.herdr;
 assert.equal((await runner.stepDone({step:'scope',summary:'Plan prepared',cwd:run.root},f.agentPorts())).exitCode,0);
 f.ports.herdr=async args=>{const reply=await healthy(args);if(args[0]==='tab'&&args[1]==='create')throw Object.assign(Error('lost create reply'),{code:'lost'});return reply;};
 assert.equal((await open(f,{newSession:true})).exitCode,1);
 const pending=attempt(f);assert.equal(pending.phase,'createRequested');
 f.ports.herdr=healthy;f.tick();
 const advanced=await runner.approveRun({ref:'17',cwd:f.source},f.ports);assert.equal(advanced.exitCode,0,advanced.message);
 const before=f.record(),current=before.chats.find(chat=>chat.area==='build');assert.ok(current);
 const creates=f.herdr.calls.filter(args=>args[0]==='tab'&&args[1]==='create').length;
 const recovered=await open(f,{newSession:true});assert.equal(recovered.exitCode,0,recovered.message);
 const after=f.record();assert.equal(after.chatReplacement.id,pending.id);assert.equal(after.chatReplacement.phase,'ended');
 assert.equal(after.area,before.area);assert.deepEqual(after.gate,before.gate);assert.deepEqual(after.done,before.done);assert.deepEqual(after.approvals,before.approvals);
 assert.deepEqual(after.chats.find(chat=>chat.area==='build'),current);
 assert.equal(after.abandonedChats.length,1);assert.equal(after.abandonedChats[0].paneId,original.paneId);
 assert.equal(after.chats.filter(chat=>chat.area===original.area).length,1);
 assert.equal(f.herdr.calls.filter(args=>args[0]==='tab'&&args[1]==='create').length,creates);
 assert.equal(f.herdr.calls.filter(args=>args[0]==='pane'&&args[1]==='run'&&args[2]!==current.paneId&&args[2]!==original.paneId).length,0);
});
