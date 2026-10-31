import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {Worker} from 'node:worker_threads';
import {uptakeFixture,runner} from './helpers/workflow-concurrent-fixture.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {nativeCase,observations} from './helpers/workflow-concurrent-cases.mjs';
function release(barrier){Atomics.store(new Int32Array(barrier),0,1);Atomics.notify(new Int32Array(barrier),0);}
async function heldWriter(t,f,operation,extra={}){
 const barrier=new SharedArrayBuffer(4),run=f.record();
 const worker=new Worker(new URL('./helpers/workflow-concurrent-stale-writer.mjs',import.meta.url),{workerData:{operation,root:run.root,source:f.source,stateDir:f.ports.stateDir,env:f.ports.env,barrier,...extra}});
 t.after(async()=>{release(barrier);await worker.terminate();});
 let ready,result;
 const held=new Promise((r,j)=>{ready=r;worker.on('error',j);});
 const reply=new Promise((r,j)=>{result=r;worker.on('error',j);});
 worker.on('message',m=>m.held?ready():result(m));
 await held;return async()=>{release(barrier);return reply;};
}
for(const [id,operation] of [['ask-own-question-retains-newer-gate','askPerson'],['status-own-ci-retains-newer-pr-fields','runStatus']])test(`2753 ${id}: independent preservation and own effects`,async t=>{
 const row=nativeCase(id),f=await uptakeFixture(t);f.save([f.entry('r1',{ackedAt:700,ackSummary:'Kept ACK'})]);
 const run=f.record();run.pr=[{url:'https://github.com/example/project/pull/23',stage:'story',number:23,state:'open',ci:'pending',base:'old-base'}];writeRun(run,f.ports);
 const finish=await heldWriter(t,f,operation,{text:row.operations[0].text??'Own question'});
 const latest=f.record();latest.done.independent={at:2000,summary:'Newer independent work',area:'story'};latest.question={text:'Independent question',at:2000,area:'story'};latest.gate={area:'story',at:2000,kind:'approve'};latest.decisions.push({stage:'story',decision:'changes',at:2000});latest.area=1;latest.pr[0].base='newer-base';latest.pr.push({url:'https://github.com/example/project/pull/24',stage:'code',number:24,state:'open',ci:'pending'});writeRun(latest,f.ports);const before=f.bytes();
 const outcome=await finish(),saved=f.record();
 observations(id,{success:()=>assert.equal(outcome.result?.exitCode,0),done:()=>assert.deepEqual(saved.done,latest.done),gate:()=>assert.deepEqual(saved.gate,latest.gate),decisions:()=>assert.deepEqual(saved.decisions,latest.decisions),area:()=>assert.equal(saved.area,latest.area),prBase:()=>assert.equal(saved.pr[0].base,'newer-base'),separatePr:()=>assert.deepEqual(saved.pr[1],latest.pr[1]),question:()=>assert.equal(saved.question?.text,operation==='askPerson'?(row.operations[0].text??'Own question'):latest.question.text),ownCI:()=>{if(operation==='runStatus')assert.equal(saved.pr[0].ci,'success');},journal:()=>assert.equal(f.bytes(),before)});
});
const rerun=nativeCase('rerun-clears-latest-later-known-steps');
for(const variant of rerun.given.laterUpdateVariants)test(`2753 rerun clears latest ${variant.step} independently of unrelated progress`,async t=>{
 const f=await uptakeFixture(t),run=f.record();run.areas[0].steps=['build','verify','formal'];run.done={build:{at:1,summary:'Old build',area:'story'},verify:{at:2,summary:'Old verify',area:'story'},unrelated:{at:2,summary:'Keep unknown',area:'story'},check:{at:2,summary:'Keep other area',area:'code'}};writeRun(run,f.ports);
 const finish=await heldWriter(t,f,'stepDone',{step:'build',summary:'Rebuilt'});
 const current=f.record();current.done[variant.step]={at:2000,summary:variant.summary,area:'story'};current.done.independent={at:2000,summary:'Unrelated new progress',area:'story'};writeRun(current,f.ports);
 const outcome=await finish(),saved=f.record();
 observations(`rerun-${variant.step}`,{success:()=>assert.equal(outcome.result?.exitCode,0),own:()=>assert.equal(saved.done.build.summary,'Rebuilt'),invalidates:()=>{assert.equal(saved.done.verify,undefined);assert.equal(saved.done.formal,undefined);},unrelated:()=>assert.deepEqual(saved.done.independent,current.done.independent),unknown:()=>assert.deepEqual(saved.done.unrelated,current.done.unrelated),otherArea:()=>assert.deepEqual(saved.done.check,current.done.check),warning:()=>assert.match(outcome.result.message,/warning:/)});
});
const identity=nativeCase('replacement-run-identity');
for(const operation of identity.given.writerVariants)test(`2753 ${operation} refuses replacement run`,async t=>{
 const f=await uptakeFixture(t);const old=f.record();old.pr=[{url:'https://github.com/example/project/pull/23',state:'open',ci:'pending',stage:'story'}];writeRun(old,f.ports);
 const finish=await heldWriter(t,f,operation),replacement=f.record();replacement.runId='replacement-run';writeRun(replacement,f.ports);const path=join(replacement.runDir,'status.json'),before=fs.readFileSync(path,'utf8');
 const outcome=await finish();observations(`replacement-${operation}`,{failure:()=>assert.equal(outcome.result?.exitCode,1),diagnostic:()=>assert.ok(outcome.result.message.length),bytes:()=>assert.equal(fs.readFileSync(path,'utf8'),before)});
});
const failures=nativeCase('existing-save-failure');
for(const writer of failures.given.writerVariants)for(const failure of failures.given.failureVariants)test(`2753 ${writer}: ${failure}`,async t=>{
 const operation=writer.split(' ')[0],f=await uptakeFixture(t);f.save([f.entry()]);const run=f.record();run.pr=[{url:'https://github.com/example/project/pull/23',state:'open',ci:'pending',stage:'story'}];writeRun(run,f.ports);
 const path=join(run.runDir,'status.json'),before=fs.readFileSync(path,'utf8'),journal=f.bytes();let injected=false,releases=0;
 const ports={...f.ports,readPrStatus:async()=>({state:'open',ci:'success'}),now:()=>{
  if(!injected){injected=true;if(failure==='missing record')fs.unlinkSync(path);if(failure==='malformed record')fs.writeFileSync(path,'{invalid');}return 3000;
 }};
 if(failure==='ownership unavailable')ports.acquireRunOwnership=()=>{throw Error('Owner unavailable');};
 if(failure==='read error')ports.runFiles={readFileSync:()=>{throw Object.assign(Error('Read refused'),{code:'EIO'});}};
 if(failure==='atomic publication failure')ports.runFiles={renameSync:()=>{throw Object.assign(Error('Publish refused'),{code:'EIO'});}};
 const args=operation==='runStatus'?{ref:'17',cwd:f.source}:operation==='stepDone'?{step:'independent',summary:'Own work',cwd:run.root}:{text:'Own question',cwd:run.root};
 let result;try{result=await runner[operation](args,ports);}catch(error){result={exitCode:9,message:String(error)};}
 observations(`failure-${operation}-${failure}`,{failure:()=>assert.equal(result.exitCode,1),diagnostic:()=>assert.ok(result.message.length),noSuccessClaim:()=>assert.doesNotMatch(result.message,/pdd recorded|pdd shows the person/),bytes:()=>{if(failure==='missing record')assert.equal(fs.existsSync(path),false);else assert.equal(fs.readFileSync(path,'utf8'),failure==='malformed record'?'{invalid':before);},journal:()=>assert.equal(f.bytes(),journal)});
});
