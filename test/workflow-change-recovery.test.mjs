import test from 'node:test';
import assert from 'node:assert/strict';
import { readdirSync, readFileSync, lstatSync, mkdirSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
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

for (const signal of ['SIGINT','SIGTERM','SIGHUP','SIGKILL']) {
 test(`A ${signal}: reclaim dead owned sender dispatch lock`, async t => {
  const f=await setup(t);
  const child=fork(fileURLToPath(new URL('./helpers/workflow-owned-wait-child.mjs',import.meta.url)),[f.source,f.state,String(f.clock)],{env:{...process.env,W,HOME:f.ports.env.HOME},stdio:['ignore','pipe','pipe','ipc']});
  let childErr=''; child.stderr.on('data',b=>childErr+=b);
  t.after(()=>{if(child.exitCode===null && child.signalCode===null)child.kill('SIGKILL');});
  const [message]=await once(child,'message'); assert.equal(message.waiting,true,childErr);
  const lock=readdirSync(f.record().runDir).find(x=>/^\.delivery-[a-f0-9]+\.lock$/.test(x));
  assert.ok(lock); const lockPath=f.record().runDir+'/'+lock;
  const ownerText=lstatSync(lockPath).isDirectory()?readdirSync(lockPath).map(name=>readFileSync(lockPath+'/'+name,'utf8')).join(''):readFileSync(lockPath,'utf8');
  assert.ok(ownerText.includes(String(child.pid)), 'claim belongs to the private child');
  // A living owner must remain protected; only the child started above is killed.
  const live=await call(f,'Second'); assert.notEqual(live.exitCode,0); assert.match(live.message,/in progress/);
  const closed=once(child,'close'); assert.equal(child.kill(signal),true); const [code,gotSignal]=await closed;
  assert.ok(gotSignal === signal || code === 128 + ({SIGINT:2,SIGTERM:15,SIGHUP:1}[signal] ?? 9)); assert.throws(()=>process.kill(child.pid,0),e=>e.code==='ESRCH');
  f.tick(120_000);
  const later=await call(f,'Second'), again=await call(f,'Second');
  assert.equal(later.exitCode,0,'Dead sender must not permanently block later requests');
 });
}

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
 const original=f.record(); original.question={text:'Which example?',area:original.areas[original.area].name,at:f.clock}; writeRun(original,f.ports);
 const first=await call(f,'First'), second=await call(f,'Totally different');
 assert.notEqual(first.exitCode,0);assert.equal(journal(f)[0]?.state,'uncertain');
 assert.equal(second.exitCode,0,'Uncertain First is preserved but different request must go through');
 const before=sent.length; const repeated=await call(f,'First');
 assert.notEqual(repeated.exitCode,0); assert.equal(sent.length,before,'Uncertain request is never automatically resent');
 assert.match(second.message,/uncertain.*check|check.*uncertain/is,'New delivery still warns about uncertain request');
});

test('E overlapping identical request: following Retry advice must not duplicate it',async t=>{
 const f=await setup(t),healthy=f.ports.herdr;let ready=false,release,entered;const sent=[];
 const waiting=new Promise(resolve=>entered=resolve);
 f.ports.sleep=async ms=>{entered();await new Promise(resolve=>release=resolve);f.tick(ms);};
 f.ports.herdr=async args=>{if(args[0]==='agent'&&!ready)return missing();if(args[0]==='agent'&&args[1]==='prompt')sent.push(args[3]);return healthy(args);};
 const first=call(f,'Same request');assert.equal(await Promise.race([waiting.then(()=>'waiting'),first.then(()=>'returned before readiness')]),'waiting','The first call waits for readiness before an overlap can join');
 const overlap=await call(f,'Same request');
 const advisedRetry = /Retry: pdd workflow changes/.test(overlap.message);
 ready=true;release();assert.equal((await first).exitCode,0);
 const retry=advisedRetry ? await call(f,'Same request') : null;
 assert.equal(sent.length,1,'Retry advice after an overlapping identical request must not lead to duplicate submission');
 assert.equal((await call(f,'Same request')).exitCode,0);
 assert.equal(sent.length,2,'Ordinary identical request after receipt consumption is intentional new work');
});


test('E acknowledgement between dispatch contention and receipt save reports delivery', async t => {
 const f=await setup(t), fs=await import('node:fs'), run=f.record(), chat=run.chats.at(-1);
 const journalPath=join(run.runDir,'delivery-journal.json');
 const request={id:'accepted-overlap',text:'Same request',kind:'change',state:'pending',area:chat.area,paneId:chat.paneId,at:f.clock,question:null,gate:null};
 writeFileSync(journalPath,JSON.stringify({requests:[request]}));
 const lock=join(run.runDir,`.delivery-${createHash('sha256').update(`${chat.area}\0${chat.paneId}`).digest('hex')}.lock`);
 mkdirSync(lock); const other=join(lock,'winner-token.json');
 writeFileSync(other,JSON.stringify({pid:777777,birth:'winner-birth',token:'winner-token'}));
 f.ports.processIdentity=pid=>({alive:true,birth:pid===777777?'winner-birth':'test-self-birth'});
 let acknowledged=false, submits=0;const healthy=f.ports.herdr;
 f.ports.deliveryFiles={...fs,readFileSync:(path,...args)=>{
   if(path===other&&!acknowledged){acknowledged=true;writeFileSync(journalPath,JSON.stringify({requests:[{...request,state:'delivered'}]}));}
   return fs.readFileSync(path,...args);
 }};
 f.ports.herdr=async args=>{if(args[1]==='prompt')submits++;return healthy(args);};
 const result=await call(f,'Same request');
 assert.match(result.message,/already.*delivered/is,'A joined caller whose winner just acknowledged gets delivery, never another retry promise');
 assert.equal(result.exitCode,0);assert.equal(submits,0);assert.ok(!journal(f)[0].retryOwed);
});

test('2677 unbound retries retain one identity and cannot renew an expired area window', async t => {
 const f=await setup(t), run=f.record(), chat=run.chats.at(-1), healthy=f.ports.herdr;
 run.chats=[]; writeRun(run,f.ports); f.ports.sleep=async ms=>f.tick(ms);
 const first=await call(f,'Area request');
 assert.match(first.message,/kept/i,'An absent chat record must retain the area request');
 const id=journal(f)[0]?.id; assert.ok(id);
 const appeared=f.record();appeared.chats.push({...chat,startedAt:f.clock});writeRun(appeared,f.ports);
 let sends=0;f.ports.herdr=async args=>{if(args[1]==='prompt')sends++;return healthy(args);};
 const retry=await call(f,'Area request');
 assert.notEqual(retry.exitCode,0);assert.equal(sends,0,'A new chat record cannot restart an expired intent window');
 assert.equal(journal(f).length,1);assert.equal(journal(f)[0].id,id);assert.equal(journal(f)[0].paneId,null);
 assert.equal((await call(f,'Different new request')).exitCode,0);assert.equal(sends,1);
 const g=await setup(t), early=g.record(), original=early.chats.at(-1);early.chats=[];writeRun(early,g.ports);
 g.ports.sleep=async ms=>{g.tick(ms);throw Object.assign(Error('interrupted waiting for record'),{code:'test_interruption'});};
 await assert.rejects(call(g,'Early retry'),error=>error.code==='test_interruption');
 const originalId=journal(g)[0].id, live=g.record();live.chats.push(original);writeRun(live,g.ports);
 assert.equal((await call(g,'Early retry')).exitCode,0);
 assert.equal(journal(g).length,1);assert.equal(journal(g)[0].id,originalId);
 assert.equal(g.herdr.paneOf(original).agent.prompts.length,1,'Retry before expiry binds and sends the original intent once');
});
