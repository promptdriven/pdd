import {inventory} from './helpers/workflow-concurrent-cases.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { Worker } from 'node:worker_threads';
import { uptakeFixture } from './helpers/workflow-concurrent-fixture.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
// AC6: a stale run writer cannot erase uptake, a newer delivery, or newer progress.
for (const operation of inventory.cases.filter(row=>row.id.startsWith('stale-')&&row.id.endsWith('-preservation')).map(row=>row.given.writer)) test(`2753 public ${operation} reconciliation preserves unrelated changes and intended updates`,{timeout:20000},async t=>{
 const f=await uptakeFixture(t);f.save([f.entry()]);
 const run=f.record();run.done={reproduce:{at:100,summary:'Earlier reproduce',area:'story'},'prompt-story':{at:200,summary:'Earlier prompt',area:'story'}};run.pr=[{url:'https://github.com/example/project/pull/23',stage:'story',state:'open',ci:'pending'}];writeRun(run,f.ports);
 const barrier=new SharedArrayBuffer(4),worker=new Worker(new URL('./helpers/workflow-concurrent-stale-writer.mjs',import.meta.url),{workerData:{operation,root:run.root,source:f.source,stateDir:f.ports.stateDir,env:f.ports.env,barrier}});
 t.after(async()=>{Atomics.store(new Int32Array(barrier),0,1);Atomics.notify(new Int32Array(barrier),0);await worker.terminate();});
 let heldResolve,resultResolve;const held=new Promise(r=>heldResolve=r),result=new Promise((resolve,reject)=>{resultResolve=resolve;worker.on('error',reject);});
 worker.on('message',m=>{if(m.held)heldResolve();else resultResolve(m);});
 await held;f.ports.now=()=>2000;
 assert.equal((await f.ack('r1','Updated value')).exitCode,0,'delivered request uptake succeeds while stale writer is held');
 assert.equal((await f.change('Add an example')).exitCode,0);
 assert.equal((await f.done('newer-progress')).exitCode,0);
 const newer=f.record().done['newer-progress'];assert.ok(newer);
 const latest=f.record();
 latest.question={text:'Newer question',at:2100,area:'story'};
 latest.gate={area:'story',at:2100,kind:'approve'};
 latest.decisions=[...(latest.decisions??[]),{at:2100,kind:'changes',text:'Preserve decision'}];
 latest.area=1;latest.deliveryRequests=[{id:'legacy-effect',state:'delivered'}];
 latest.pr[0].review={state:'approved',at:2100};
 latest.pr.push({url:'https://github.com/example/project/pull/24',stage:'code',state:'open',ci:'pending'});
 writeRun(latest,f.ports);
 const preserved=f.record();
 Atomics.store(new Int32Array(barrier),0,1);Atomics.notify(new Int32Array(barrier),0);
 const outcome=await result;assert.equal(outcome.error,undefined);assert.equal(outcome.result.exitCode,0);
 const requests=f.read();assert.equal(requests.length,2);assert.equal(requests[0].ackedAt,2000);assert.equal(requests[0].ackSummary,'Updated value');assert.notEqual(requests[1].id,'r1');assert.equal(requests[1].state,'delivered');assert.equal(requests[1].ackedAt??null,null);
 const saved=f.record();
 assert.deepEqual(saved.done['newer-progress'],newer);
 for(const key of ['gate','decisions','area','deliveryRequests'])assert.deepEqual(saved[key],preserved[key],`preserves unrelated newer ${key}`);
 if(operation==='askPerson')assert.equal(saved.question.text,'Stale question?','the requested question still takes effect');
 else assert.deepEqual(saved.question,preserved.question,'an unchanged or already-cleared question does not erase a newer question');
 assert.deepEqual(saved.pr[0].review,preserved.pr[0].review);
 assert.deepEqual(saved.pr[1],preserved.pr[1]);
 if(operation==='runStatus')assert.equal(saved.pr[0].ci,'success','nested PR refresh takes effect');
 if(operation==='stepDone'){
  assert.equal(saved.done.reproduce.summary,'Stale writer');
  assert.equal(Object.hasOwn(saved.done,'prompt-story'),false,'rerunning a completed step still removes its later completed step');
 }

});
