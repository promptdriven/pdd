import test from 'node:test';
import assert from 'node:assert/strict';
import {Worker} from 'node:worker_threads';
import {readFileSync} from 'node:fs';
import {fixture} from './helpers/workflow-delivery-fixture.mjs';
import {writeRun} from '../src/workflow-runs.mjs';

test('2753 overlapping and sequential public done retain union',{timeout:60000},async t=>{
 const f=await fixture(t,{agent:'codex',name:'bug'});
 const started=await f.run();assert.equal(started.exitCode,0,started.message);
 const inventory=JSON.parse(readFileSync(new URL('./workflow-concurrent-progress/cases.json',import.meta.url)));
 assert.ok(inventory.cases.find(c=>c.id==='overlapping-public-done-union'));
 assert.ok(inventory.cases.find(c=>c.id==='sequential-public-done-union'));
 const base=f.record(),commonDir=f.git(base.root,'rev-parse','--path-format=absolute','--git-common-dir');
 const observations=[];
 const release=barrier=>{const view=new Int32Array(barrier);Atomics.store(view,0,1);Atomics.notify(view,0);};
 for(let pair=0;pair<36;pair++){
  const mode=pair<4?'sequential-control':pair<20?'overlap-small':'overlap-64KiB-summary';
  const run=structuredClone(base);
  run.done=mode==='overlap-64KiB-summary'?{prior:{at:1,area:'story',summary:'x'.repeat(65536)}}:{};
  writeRun(run,f.ports);
  const a=`audit-a-${pair}`,b=`audit-b-${pair}`,steps=[a,b];
  const barriers=[new SharedArrayBuffer(4),new SharedArrayBuffer(4)];
  const workers=[],outcomes=[{state:'not-started'},{state:'not-started'}];
  const releaseOrder=mode==='sequential-control'||pair%2===0?[0,1]:[1,0];
  function diagnostic(workerIndex,phase){
   let savedDone;
   try{savedDone=f.record().done;}catch(error){savedDone={readError:error.stack};}
   return JSON.stringify({pair,mode,workerIndex,step:steps[workerIndex],a,b,phase,releaseOrder,outcomes,savedDone});
  }
  function launch(workerIndex){
   const worker=new Worker(new URL('./helpers/workflow-concurrent-done-worker.mjs',import.meta.url),{workerData:{root:base.root,commonDir,stateDir:f.ports.stateDir,env:f.ports.env,barrier:barriers[workerIndex],step:steps[workerIndex]}});
   let heldResolve,resultResolve,finished=false;
   const held=new Promise(resolve=>heldResolve=resolve),result=new Promise(resolve=>resultResolve=resolve);
   outcomes[workerIndex]={state:'started'};
   const finish=outcome=>{if(finished)return;finished=true;outcomes[workerIndex]=outcome;resultResolve(outcome);};
   worker.on('error',error=>finish({error:error.stack}));
   worker.on('exit',exitCode=>{if(!finished)finish({error:`Worker exited before returning a completion (exit ${exitCode})`,exitCode});});
   worker.on('message',message=>{
    if(message.held){outcomes[workerIndex]={state:'held'};heldResolve();}
    else finish(message);
   });
   workers[workerIndex]={worker,held,result};
  }
  async function bounded(promise,workerIndex,phase){
   let timer;
   try{return await Promise.race([promise,new Promise((_,reject)=>{timer=setTimeout(()=>reject(new Error(diagnostic(workerIndex,`${phase} timeout`))),15000);})]);}
   finally{clearTimeout(timer);}
  }
  async function awaitHeld(workerIndex){
   const worker=workers[workerIndex];
   const held=await bounded(Promise.race([worker.held.then(()=>true),worker.result.then(()=>false)]),workerIndex,'await hold');
   assert.equal(held,true,diagnostic(workerIndex,'worker must select run and hold'));
  }
  async function awaitSuccess(workerIndex){
   const outcome=await bounded(workers[workerIndex].result,workerIndex,'await completion');
   const context=diagnostic(workerIndex,'completion');
   assert.equal(outcome.error,undefined,context);
   assert.equal(outcome.result?.exitCode,0,context);
  }
  try{
   launch(0);await awaitHeld(0);
   if(mode==='sequential-control'){
    release(barriers[0]);await awaitSuccess(0);
    launch(1);await awaitHeld(1);
    release(barriers[1]);await awaitSuccess(1);
   }else{
    // Both calls have selected the original run before either can acquire ownership.
    launch(1);await awaitHeld(1);
    const [first,second]=releaseOrder;
    release(barriers[first]);await awaitSuccess(first);
    release(barriers[second]);await awaitSuccess(second);
   }
   const saved=f.record();
   const expected={...run.done,[a]:{at:5000,summary:`Completed ${a}`,area:'story'},[b]:{at:5000,summary:`Completed ${b}`,area:'story'}};
   assert.deepEqual(saved.done,expected,diagnostic(null,'full successful completion union'));
   observations.push({pair,mode,releaseOrder,keys:Object.keys(saved.done),exitCodes:outcomes.map(outcome=>outcome.result.exitCode)});
  }finally{
   for(const barrier of barriers)release(barrier);
   await Promise.all(workers.map(({worker})=>worker.terminate()));
  }
 }
 console.log(JSON.stringify({observations}));
 assert.equal(observations.filter(item=>item.mode==='sequential-control').length,4);
 assert.equal(observations.filter(item=>item.mode==='overlap-small').length,16);
 assert.equal(observations.filter(item=>item.mode==='overlap-64KiB-summary').length,16);
});
