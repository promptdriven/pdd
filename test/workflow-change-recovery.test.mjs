import test from 'node:test';
import assert from 'node:assert/strict';
import { readdirSync, readFileSync, mkdirSync, writeFileSync, unlinkSync, existsSync } from 'node:fs';
import { hostname } from 'node:os';
import { join } from 'node:path';
import { fork } from 'node:child_process';
import { once } from 'node:events';
import { fileURLToPath } from 'node:url';
const W = fileURLToPath(new URL('..', import.meta.url));
const { fixture } = await import(W + '/test/helpers/workflow-delivery-fixture.mjs');
const { changeRun, runStatus, stepDone, askPerson } = await import(W + '/src/workflow-runner.mjs');
const { writeRun } = await import(W + '/src/workflow-runs.mjs');
const missing = () => { throw Object.assign(Error('absent'), {code:'agent_not_found'}); };
const setup = async t => { const f=await fixture(t,{agent:'codex'}); assert.equal((await f.run()).exitCode,0); return f; };
const call = async (f,text,ports=f.ports) => { return changeRun({ref:'17',text,cwd:f.source},ports); };
const journal = f => { try { const value=JSON.parse(readFileSync(f.record().runDir+'/delivery-journal.json','utf8')); return value.requests ?? value; } catch(error) { if(error.code !== 'ENOENT') throw error; return f.record().deliveryRequests ?? []; } };

for (const signal of ['SIGINT','SIGTERM','SIGHUP','SIGKILL']) test(`A ${signal}: interrupted pending readiness remains retryable without a long claim`, {timeout:10000}, async t => {
 const f=await setup(t);
 const child=fork(fileURLToPath(new URL('./helpers/workflow-owned-wait-child.mjs',import.meta.url)),[f.source,f.state,String(f.clock)],{env:{...process.env,W,HOME:f.ports.env.HOME},stdio:['ignore','pipe','pipe','ipc']});
 t.after(()=>{if(child.exitCode===null&&child.signalCode===null)child.kill('SIGKILL');});
 const [message]=await once(child,'message'); assert.equal(message.waiting,true);
 assert.equal(readdirSync(f.record().runDir).filter(x=>/^\.delivery-[a-f0-9]+\.lock$/.test(x)).length,0,'readiness must not hold a dispatch lock');
 const id=journal(f)[0].id; assert.equal(journal(f)[0].state,'pending'); assert.ok(!journal(f)[0].inFlight);
 const closed=once(child,'close');child.kill(signal);await closed;
 const later=await call(f,'First');assert.equal(later.exitCode,0,later.message);
 assert.equal(journal(f).length,1);assert.equal(journal(f)[0].id,id);assert.equal(journal(f)[0].state,'delivered');
 assert.equal(f.herdr.paneOf(f.record().chats.at(-1)).agent.prompts.length,1);
});

test('B real status writer: stale pending snapshot must not revert delivered journal',async t=>{
 const f=await setup(t), healthy=f.ports.herdr, sent=[];
 f.ports.herdr=async args=>args[0]==='agent'&&args[1]==='get'?missing():healthy(args);
 f.ports.sleep=async ms=>f.tick(ms);
 assert.notEqual((await call(f,'First')).exitCode,0);
 const initial=f.record(); assert.equal(journal(f)[0].state,'pending');
 initial.chats.at(-1).startUnconfirmed=true; writeRun(initial,f.ports);
 let release,entered; const waiting=new Promise(resolve=>entered=resolve);
 const statusPorts={...f.ports,herdr:async args=>{
   if(args[0]==='agent'&&args[1]==='get'){entered();await new Promise(resolve=>release=resolve);}
   return healthy(args);
 }};
 const status=runStatus({ref:'17',cwd:f.source},statusPorts); await waiting;
 f.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='prompt')sent.push(args[3]);return healthy(args);};
 assert.equal((await call(f,'First')).exitCode,0);
 release(); assert.equal((await status).exitCode,0);
 assert.equal((await call(f,'Second')).exitCode,0);
 assert.equal(sent.filter(text=>text.includes('changes: First ')).length,1,'Status must not make First replayable');
 // Legacy snapshots retained by other public writers must also stay non-authoritative.
 const stale=f.record(); stale.deliveryRequests=journal(f).map(entry=>({...entry,state:'pending'})); writeRun(stale,f.ports);
 assert.equal((await askPerson({text:'A newer question',cwd:stale.root},f.agentPorts())).exitCode,0);
 assert.equal((await stepDone({step:'build',summary:'companion writer',cwd:stale.root},f.agentPorts())).exitCode,0);
 assert.equal((await call(f,'Third')).exitCode,0);
 assert.equal(sent.filter(text=>text.includes('changes: First ')).length,1,'Ask and done writers cannot restore a replayable legacy snapshot');
});

test('C uncertain request must not block a different new request',async t=>{
 const f=await setup(t),healthy=f.ports.herdr;let fails=1;const sent=[];
 f.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='prompt'){if(fails-->0)throw Object.assign(Error('lost acknowledgement'),{code:'herdr_failed'});sent.push(args[3]);}return healthy(args);};
 const first=await call(f,'First'), second=await call(f,'Totally different');
 assert.notEqual(first.exitCode,0);assert.equal(journal(f)[0]?.state,'uncertain');
 assert.equal(second.exitCode,0,'Uncertain First is preserved but different request must go through');
 const before=sent.length; const repeated=await call(f,'First');
 assert.notEqual(repeated.exitCode,0); assert.equal(sent.length,before,'Uncertain request is never automatically resent');
 assert.match(second.message,/uncertain.*check|check.*uncertain/is,'New delivery still warns about uncertain request');
});

const rendezvous = () => { let release, entered, firstEntered, count=0; const first=new Promise(r=>firstEntered=r),ready=new Promise(r=>entered=r),wait=new Promise(r=>release=r); return {first,ready,release,sleep:async()=>{if(++count===1)firstEntered();if(count===2)entered();await wait;}}; };
for(const kind of ['change','answer']) test(`E2 ${kind}: failed overlaps retry once then intentional identical text sends again`, {timeout:10000}, async t=>{
 const f=await setup(t), healthy=f.ports.herdr, waits=rendezvous();let ready=false;const sent=[];
 const question=text=>{const r=f.record();r.question={text,area:r.areas[r.area].name,at:f.clock};writeRun(r,f.ports);};
 if(kind==='answer')question('Continue?');const text=kind==='answer'?'yes':'Same request';
 f.ports.sleep=async()=>{await waits.sleep();f.tick(40000);};
 f.ports.herdr=async args=>{if(args[0]==='agent'&&!ready)return missing();if(args[1]==='prompt')sent.push(args[3]);return healthy(args);};
 const first=call(f,text);await Promise.race([waits.first,first]);const second=call(f,text);await Promise.race([waits.ready,second]);const id=journal(f)[0]?.id;
 waits.release();const failed=await Promise.all([first,second]);assert.ok(failed.every(r=>r.exitCode!==0));
 assert.equal(journal(f).length,1);assert.equal(journal(f)[0].id,id);
 ready=true;f.ports.sleep=async ms=>f.tick(ms);assert.equal((await call(f,text)).exitCode,0);
 if(kind==='answer')question('Continue again?');assert.equal((await call(f,text)).exitCode,0);
 assert.equal(sent.length,2,'successful retry must not consume later intentional identical work');
 assert.equal(journal(f).filter(r=>r.state==='delivered').length,2);assert.equal(new Set(journal(f).map(r=>r.id)).size,2);
 assert.ok(journal(f).every(r=>r.kind===kind));assert.equal(f.record().question??null,null);
});

for(const kind of ['change','answer']) test(`E joined ${kind} preserves accepted identity and reports delivered`,{timeout:10000},async t=>{
 const f=await setup(t),healthy=f.ports.herdr,waits=rendezvous();let ready=false,sends=0;
 if(kind==='answer'){const r=f.record();r.question={text:'Which?',at:f.clock,area:r.areas[r.area].name};writeRun(r,f.ports);}
 f.ports.sleep=async ms=>{await waits.sleep();f.tick(ms);};
 f.ports.herdr=async args=>{if(args[0]==='agent'&&!ready)return missing();if(args[1]==='prompt')sends++;return healthy(args);};
 const first=call(f,'Same');await Promise.race([waits.first,first]);const second=call(f,'Same',{...f.ports,herdr:async args=>{if(ready&&args[0]==='agent'&&args[1]==='get')await first;return f.ports.herdr(args);}});await Promise.race([waits.ready,second]);ready=true;waits.release();
 const results=await Promise.all([first,second]);assert.equal(sends,1);assert.equal(journal(f).length,1);
 const joined=results.find(r=>/already.*delivered/is.test(r.message));assert.ok(joined,JSON.stringify(results));assert.equal(joined.exitCode,0);assert.doesNotMatch(joined.message,/kept|Retry:/i);
 assert.equal(f.record().changes.length,1);
});

test('E active in-flight joined caller sees progress without kept or retry promises',async t=>{
 const f=await setup(t),healthy=f.ports.herdr;let release,entered,duplicate,sends=0;const waiting=new Promise(r=>entered=r),duplicated=new Promise(r=>duplicate=r),hold=new Promise(r=>release=r);
 f.ports.herdr=async args=>{if(args[1]==='prompt'){sends++;entered();if(sends>1)duplicate();await hold;}return healthy(args);};
 const first=call(f,'Same');await waiting;const secondTask=call(f,'Same');await Promise.race([secondTask,duplicated]);release();const second=await secondTask;assert.notEqual(second.exitCode,0);assert.match(second.message,/in progress/i);assert.doesNotMatch(second.message,/kept|Retry:/i);
 release();assert.equal((await first).exitCode,0);assert.equal(sends,1);assert.equal(journal(f).length,1);
});

test('F no chat is immediate without custody; fresh startup after open can really deliver retry',async t=>{
 const f=await setup(t),run=f.record(),chat=run.chats.at(-1),healthy=f.ports.herdr;run.chats=[];writeRun(run,f.ports);
 let waits=0,sends=0;f.ports.sleep=async ms=>{waits++;f.tick(ms);};
 const first=await call(f,'Area request');assert.notEqual(first.exitCode,0);assert.match(first.message,/area has no chat.*workflow open/is);assert.doesNotMatch(first.message,/kept|still starting/i);assert.equal(waits,0);assert.equal(journal(f).length,0);
 const opened=f.record();opened.chats.push({...chat,startedAt:f.clock});writeRun(opened,f.ports);const began=f.clock;
 f.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='get'&&f.clock-began<500)return missing();if(args[1]==='prompt')sends++;return healthy(args);};
 const retry=await call(f,'Area request');assert.equal(retry.exitCode,0,'an explicit opened chat must make retry advice work');assert.equal(sends,1);assert.ok(f.clock-began>=500);assert.equal(journal(f).length,1);assert.equal(journal(f)[0].paneId,chat.paneId);
});

test('H brief live journal contention after transport preserves acknowledgement and round',async t=>{
 const f=await setup(t),healthy=f.ports.herdr,dir=join(f.record().runDir,'.delivery-journal.lock'),leaf=join(dir,'owner-other.json');let timer,sends=0;t.after(()=>clearTimeout(timer));
 f.ports.herdr=async args=>{const result=await healthy(args);if(args[1]==='prompt'){sends++;mkdirSync(dir,{recursive:true});writeFileSync(leaf,JSON.stringify({pid:process.pid,hostname:hostname(),token:'other'}));timer=setTimeout(()=>unlinkSync(leaf),10);}return result;};
 const first=await call(f,'First');assert.equal(first.exitCode,0,'a brief live claim must release while asynchronous ACK save retries');
 f.ports.herdr=healthy;assert.equal((await call(f,'Second')).exitCode,0);assert.equal(sends,1);assert.deepEqual(journal(f).map(r=>r.state),['delivered','delivered']);assert.deepEqual(f.record().changes.map(r=>r.text),['First','Second']);
});

for(const owner of ['live','foreign','unverifiable','malformed','dead','stray'])test(`G short journal ${owner} owner is handled conservatively`,async t=>{
 const f=await setup(t),dir=join(f.record().runDir,'.delivery-journal.lock');mkdirSync(dir,{recursive:true});if(owner==='stray')writeFileSync(join(dir,'notes.json'),'{unrelated-json');const leaf=join(dir,owner==='stray'?'notes.txt':'owner-other.json');
 writeFileSync(leaf,owner==='stray'?'unrelated':owner==='malformed'?'{broken':JSON.stringify({pid:999999,hostname:owner==='foreign'?'foreign-host':hostname(),token:'other'}));
 let checks=0;f.ports.processIdentity=()=>{checks++;return {alive:owner==='dead'?false:owner==='unverifiable'?null:true};};
 const result=await call(f,'Request');
 if(['dead','stray'].includes(owner)){assert.equal(result.exitCode,0,result.message);assert.equal(journal(f).length,1);assert.equal(journal(f)[0].state,'delivered');assert.equal(existsSync(leaf),owner==='stray');if(owner==='stray')assert.equal(readFileSync(join(dir,'notes.json'),'utf8'),'{unrelated-json');}
 else{assert.notEqual(result.exitCode,0);assert.match(result.message,/wait.*retry/is);assert.ok(existsSync(leaf));if(owner==='foreign')assert.equal(checks,0,'local PID checks cannot establish a foreign owner death');}
});

test('approval hint precedes journal contention and legacy snapshots never import requests',async t=>{
 const f=await setup(t),r=f.record(),dir=join(r.runDir,'.delivery-journal.lock');r.gate={kind:'approve',area:r.areas[r.area].name,at:f.clock};writeRun(r,f.ports);mkdirSync(dir,{recursive:true});const leaf=join(dir,'owner-other.json');writeFileSync(leaf,JSON.stringify({pid:process.pid,hostname:hostname(),token:'other'}));
 const hint=await call(f,'I approve');assert.equal(hint.exitCode,2);assert.match(hint.message,/workflow approve/);assert.equal(journal(f).length,0);unlinkSync(leaf);
 const latest=f.record();latest.gate=null;latest.deliveryRequests=[{id:'old',text:'Never import',kind:'change',state:'pending',area:r.areas[r.area].name,paneId:r.chats.at(-1).paneId,at:f.clock}];writeRun(latest,f.ports);
 assert.equal((await call(f,'New request')).exitCode,0);assert.deepEqual(journal(f).map(e=>e.text),['New request']);
});

for(const state of ['dead','live','foreign','unverifiable','missing'])test(`in-flight ${state} ownership never permits automatic resend`,async t=>{
 const f=await setup(t),r=f.record(),chat=r.chats.at(-1),healthy=f.ports.herdr;let sends=0;
 const entry={id:'owned-intent',text:'Possibly sent',kind:'change',state:'pending',inFlight:true,area:chat.area,paneId:chat.paneId,at:f.clock,...(state==='missing'?{}:{owner:{pid:654321,hostname:state==='foreign'?'foreign-host':hostname(),token:'sender'}})};
 writeFileSync(join(r.runDir,'delivery-journal.json'),JSON.stringify({requests:[entry]}));
 f.ports.processIdentity=()=>({alive:state==='dead'?false:state==='unverifiable'?null:true});
 f.ports.herdr=async args=>{if(args[1]==='prompt')sends++;return healthy(args);};
 const repeated=await call(f,'Possibly sent');assert.notEqual(repeated.exitCode,0);assert.equal(sends,0);
 if(state==='dead'){
  assert.match(repeated.message,/may already be in the chat/i);assert.equal((await call(f,'Later new request')).exitCode,0);assert.equal(sends,1);assert.equal(journal(f)[0].state,'uncertain');
 }else{
  assert.match(repeated.message,/in progress/i);assert.doesNotMatch(repeated.message,/kept|Retry:/i);assert.notEqual((await call(f,'Later new request')).exitCode,0);assert.equal(sends,0);assert.equal(journal(f)[0].inFlight,true);
 }
});

test('joined caller observes an acknowledgement saved between acceptance and its next journal read',async t=>{
 const f=await setup(t),fs=await import('node:fs'),r=f.record(),chat=r.chats.at(-1),path=join(r.runDir,'delivery-journal.json');let sends=0,acknowledged=false;
 const entry={id:'joined-id',text:'Same request',kind:'change',state:'pending',inFlight:true,owner:{pid:654321,hostname:hostname(),token:'other-sender'},area:chat.area,paneId:chat.paneId,at:f.clock};
 writeFileSync(path,JSON.stringify({requests:[entry]}));f.ports.processIdentity=()=>({alive:true});
 f.ports.deliveryFiles={...fs,renameSync:(from,to)=>{fs.renameSync(from,to);if(to===path&&!acknowledged){acknowledged=true;writeFileSync(path,JSON.stringify({requests:[{...entry,state:'delivered',inFlight:false}]}));}}};
 const healthy=f.ports.herdr;f.ports.herdr=async args=>{if(args[1]==='prompt')sends++;return healthy(args);};
 const result=await call(f,'Same request');assert.equal(result.exitCode,0);assert.match(result.message,/already.*delivered/is);assert.doesNotMatch(result.message,/kept|Retry:/i);assert.equal(sends,0);assert.equal(journal(f).length,1);assert.equal(f.record().changes.length,0);
});
