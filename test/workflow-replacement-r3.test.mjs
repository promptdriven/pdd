import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import {openRun} from '../src/workflow-runner.mjs';
import {fixture,packageRoot} from './helpers/workflow-runner-fixture.mjs';
const opts = f => ({ref:'17',cwd:f.source,packageRoot});
const runs = f => f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run');
// Expected results are the lead decisions in RECHECK-2627.md, fix round 3.
for (const newSession of [false,true]) test(`D attached terminal permits ${newSession?'--new':'second plain open'}`, async t=>{
 const f=await fixture(t); await f.run();
 let detach,entered;
 const hold=new Promise(r=>detach=r), entering=new Promise(r=>entered=r);
 const watching=openRun(opts(f),{...f.ports,isTTY:true,attach:async()=>{entered();await hold;return 0;}});
 await entering;
 try {
  const result=await openRun({...opts(f),newSession},{...f.ports,isTTY:false});
  assert.equal(result.exitCode,0,result.message);
 } finally {detach();await watching;}
});
for(const mode of ['shell','agent','unknown']) test(`E never-sent launch recovery: ${mode}`,async t=>{
 const f=await fixture(t);await f.run(); const healthy=f.ports.herdr;
 // The throw happens before the shared fake receives pane run: dispatch never occurred.
 f.ports.herdr=async args=>{if(args[0]==='pane'&&args[1]==='run')throw Object.assign(Error('lost before dispatch'),{code:'server_unavailable'});return healthy(args);};
 await openRun({...opts(f),newSession:true},f.ports);
 assert.equal(f.record().chatReplacement.phase,'launchRequested');
 const target=f.record().chatReplacement.replacement;
 const count=runs(f).length;
 f.ports.findNativeSessions=async()=>[];
 const processCalls=[];
 f.ports.herdr=async args=>{
  if(args[0]==='pane'&&args[1]==='process-info'){
   processCalls.push(args);
   if(mode==='unknown')throw Object.assign(Error('inspection unavailable'),{code:'server_unavailable'});
   const pid=mode==='shell'?41:77,name=mode==='shell'?'bash':'codex';
   return {result:{type:'pane_process_info',process_info:{pane_id:target.paneId,tty:'/dev/pts/99',shell_pid:41,foreground_process_group_id:pid,foreground_processes:[{pid,name,argv0:'/bin/'+name,argv:['/bin/'+name]}]}}};
  }
  return healthy(args);
 };
 // A pre-grace retry must not dispatch, even when inspection could find a shell.
 await openRun({...opts(f),newSession:true},f.ports);
 assert.equal(runs(f).length,count,'no dispatch inside startup grace');
 // Advance beyond the approved startup grace without sleeping.
 const grace=30_000;
 f.tick(grace+1);
 const result=await openRun({...opts(f),newSession:true},f.ports);
 if(mode==='shell'){
  assert.equal(runs(f).length,count+1,'authoritative shell after grace permits exactly one launch');
  assert.equal(result.exitCode,0,result.message);
  assert.equal(f.record().chatReplacement.phase,'launched');
 }else{
  assert.equal(runs(f).length,count,'agent or unknown process must never permit another launch');
  assert.equal(f.record().chatReplacement.phase,'launchRequested');
  assert.match(result.message,/pending/i);
 }
});

for (const throws of [false,true]) test(`attach handoff persists observations and never writes after ${throws?'failure':'completion'}`,async t=>{
 const f=await fixture(t);await f.run();
 const original=f.record().chats.at(-1);
 const session='00000000-0000-4000-8000-000000000088';
 f.herdr.paneOf(original).agent.agent_session.value=session;
 let detach,entered;
 const hold=new Promise(r=>detach=r),entering=new Promise(r=>entered=r);
 const watching=openRun(opts(f),{...f.ports,attach:async()=>{
  const savedSession=f.record().chats.at(-1).session.id,locked=existsSync(join(f.record().runDir,'chat-replacement.lock'));
  entered();await hold;
  assert.equal(savedSession,session,'native observations saved before attach');
  assert.equal(locked,false,'lock released before attach');
  if(throws)throw Error('attach failed');return 0;
 }});
 await entering;
 try{
  assert.equal((await openRun({...opts(f),newSession:true},f.ports)).exitCode,0);
  const latest=f.record();detach();await watching;
  assert.deepEqual(f.record(),latest,'attach return cannot overwrite replacement custody or failure');
 }finally{detach();await watching;}
});

test('ordinary open retains run lock during native resume and releases on opening error',async t=>{
 const f=await fixture(t);await f.run();f.herdr.paneOf(f.record().chats.at(-1)).agent=null;
 const healthy=f.ports.herdr;let finish,entered;
 const hold=new Promise(r=>finish=r),entering=new Promise(r=>entered=r);
 f.ports.herdr=async args=>{if(args[0]==='pane'&&args[1]==='run'){entered();await hold;throw Object.assign(Error('resume failed'),{code:'server_unavailable'});}return healthy(args);};
 const opening=openRun(opts(f),f.ports);await entering;
 try{assert.match((await openRun(opts(f),f.ports)).message,/holds this run/);}finally{finish();await opening;}
 assert.equal(existsSync(join(f.record().runDir,'chat-replacement.lock')),false);
});

const lost=()=>Object.assign(Error('lost dispatch'),{code:'server_unavailable'});
async function pending(t){
 const f=await fixture(t);await f.run();const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{if(args[0]==='pane'&&args[1]==='run')throw lost();return healthy(args);};
 await openRun({...opts(f),newSession:true},f.ports);f.ports.findNativeSessions=async()=>[];
 return {f,healthy,target:f.record().chatReplacement.replacement};
}
const shellInfo=target=>({result:{type:'pane_process_info',process_info:{pane_id:target.paneId,shell_pid:41,foreground_process_group_id:41,foreground_processes:[{pid:41,name:'bash'}]}}});
for(const variant of ['wrong-pane','missing-group','wrong-group','extra-agent','wrong-shell','bad-type','empty','resume-pending'])test(`recovery refuses ${variant} process evidence`,async t=>{
 const {f,healthy,target}=await pending(t);f.tick(31_000);let info=shellInfo(target);
 if(variant==='wrong-pane')info.result.process_info.pane_id='other';
 if(variant==='missing-group')delete info.result.process_info.foreground_process_group_id;
 if(variant==='wrong-group')info.result.process_info.foreground_process_group_id=77;
 if(variant==='extra-agent')info.result.process_info.foreground_processes.push({pid:77,name:'codex'});
 if(variant==='wrong-shell')info.result.process_info.foreground_processes[0].name='python';
 if(variant==='bad-type')info.result.type='other';
 if(variant==='empty')info.result.process_info.foreground_processes=[];
 if(variant==='resume-pending'){
  const record=f.record();record.chatReplacement.recovery.resumeRequested=true;
  writeFileSync(join(record.runDir,'status.json'),JSON.stringify(record));
 }
 const count=runs(f).length;
 f.ports.herdr=args=>args[0]==='pane'&&args[1]==='process-info'?Promise.resolve(info):healthy(args);
 assert.notEqual((await openRun({...opts(f),newSession:true},f.ports)).exitCode,0);
 assert.equal(runs(f).length,count);assert.equal(f.record().chatReplacement.phase,'launchRequested');
});

test('each proven-unsent retry records fresh request before dispatch and waits a fresh grace',async t=>{
 const {f,healthy,target}=await pending(t);let processCalls=0,dispatches=0,previous=f.record().chatReplacement.recovery.latestLaunchRequest?.id??f.record().chatReplacement.id;
 f.ports.herdr=async args=>{
  if(args[0]==='pane'&&args[1]==='process-info'){processCalls++;assert.deepEqual(args,['pane','process-info','--pane',target.paneId]);return shellInfo(target);}
  if(args[0]==='pane'&&args[1]==='run'){
   dispatches++;const record=f.record().chatReplacement;
   assert.equal(record.phase,'launchRequested');assert.equal(record.recovery.unsentProof.requestId,previous);
   assert.notEqual(record.recovery.latestLaunchRequest.id,previous);previous=record.recovery.latestLaunchRequest.id;
   assert.equal(record.recovery.latestLaunchRequest.at,f.clock);assert.equal(record.replacement.startedAt,target.startedAt);
   if(dispatches<3)throw lost();
  }
  return healthy(args);
 };
 for(let attempt=0;attempt<3;attempt++){
  f.tick(31_000);await openRun({...opts(f),newSession:true},f.ports);
  assert.equal(dispatches,attempt+1);
  if(attempt<2){await openRun({...opts(f),newSession:true},f.ports);assert.equal(dispatches,attempt+1,'old proof never dispatches twice');}
 }
 assert.equal(processCalls,3);assert.equal(f.record().chatReplacement.phase,'launched');
});
