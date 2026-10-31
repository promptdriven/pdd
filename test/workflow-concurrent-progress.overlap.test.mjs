import test from 'node:test';
import assert from 'node:assert/strict';
import {Worker} from 'node:worker_threads';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-delivery-fixture.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
const observations=[];
test('2753 overlapping and sequential public done retain union',{timeout:60000},async t=>{
 const f=await fixture(t,{agent:'codex',name:'bug'});assert.equal((await f.run()).exitCode,0);
 const inventory=JSON.parse(readFileSync(new URL('./workflow-concurrent-progress/cases.json',import.meta.url)));assert.ok(inventory.cases.find(c=>c.id==='overlapping-public-done-union'));assert.ok(inventory.cases.find(c=>c.id==='sequential-public-done-union'));
 const base=f.record(),commonDir=f.git(base.root,'rev-parse','--path-format=absolute','--git-common-dir');
 function launch(step,barrier){
  const worker=new Worker(new URL('./helpers/workflow-concurrent-done-worker.mjs',import.meta.url),{workerData:{root:base.root,commonDir,stateDir:f.ports.stateDir,env:f.ports.env,barrier,step}});
  let heldResolve,resultResolve,resultReject;
  const held=new Promise(r=>heldResolve=r),result=new Promise((r,j)=>{resultResolve=r;resultReject=j;});
  worker.on('error',resultReject);worker.on('message',m=>m.held?heldResolve():resultResolve(m));
  return {worker,held,result};
 }
 const release=b=>{Atomics.store(new Int32Array(b),0,1);Atomics.notify(new Int32Array(b),0);};
 for(let pair=0;pair<36;pair++){
  const mode=pair<4?'sequential-control':pair<20?'overlap-small':'overlap-64KiB-summary';
  const run=structuredClone(base);run.done=mode==='overlap-64KiB-summary'?{prior:{at:1,area:'story',summary:'x'.repeat(65536)}}:{};writeRun(run,f.ports);
  const a=`audit-a-${pair}`,b=`audit-b-${pair}`,barrier=new SharedArrayBuffer(4);
  const wa=launch(a,barrier);let wb;
  try {
   await wa.held;
   if(mode==='sequential-control'){release(barrier);assert.equal((await wa.result).result?.exitCode,0);wb=launch(b,barrier);}
   else {wb=launch(b,barrier);await wb.held;release(barrier);}
   const outcomes=await Promise.all([wa.result,wb.result]);
   for(const outcome of outcomes){assert.equal(outcome.error,undefined);assert.equal(outcome.result.exitCode,0);}
   const saved=f.record(),missing=[a,b].filter(key=>!Object.hasOwn(saved.done,key));
   observations.push({pair,mode,missing,keys:Object.keys(saved.done),exitCodes:outcomes.map(o=>o.result.exitCode)});
  }finally{release(barrier);await wa.worker.terminate();if(wb)await wb.worker.terminate();}
 }
 console.log(JSON.stringify({observations}));
 const controls=observations.filter(o=>o.mode==='sequential-control');assert.equal(controls.filter(o=>o.missing.length).length,0,'sequential control keeps union');
 console.log(JSON.stringify({pairs:observations.length,controlsLost:controls.filter(o=>o.missing.length).length,overlapLost:observations.filter(o=>o.mode!=='sequential-control'&&o.missing.length).length}));
 assert.equal(observations.filter(o=>o.missing.length).length,0,'both successful unrelated public done calls remain recorded');
});
