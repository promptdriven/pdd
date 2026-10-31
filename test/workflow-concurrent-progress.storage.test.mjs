import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import * as storage from '../src/workflow-runs.mjs';
import {fixture} from './helpers/workflow-delivery-fixture.mjs';
import {readFileSync} from 'node:fs';
const inventory=JSON.parse(readFileSync(new URL('./workflow-concurrent-progress/cases.json',import.meta.url)));
function row(id){const value=inventory.cases.find(c=>c.id===id);assert.ok(value);return value;}
// Native replay of the approved callback cases. The baseline must fail by assertion,
// not by importing an export that it does not have.
test('2753 storage compatibility and local callback boundary',async t=>{
 row('storage-compatibility-and-local-boundary');
 await indexControl(t);
 assert.equal(typeof storage.updateRun,'function','native atomic update is exported');
 const f=await fixture(t,{agent:'codex',name:'bug'});assert.equal((await f.run()).exitCode,0);
 const run=f.record(),seq=run.journalSeq;
 const returned=storage.writeRun(run,{...f.ports,now:()=>4000});assert.equal(returned,run);assert.equal(run.journalSeq,seq+1);assert.equal(run.updatedAt,4000);
 let calls=0;
 const saved=storage.updateRun(run.runDir,latest=>{calls++;latest.question={text:'Local callback',at:5000,area:'story'};return latest;},{...f.ports,now:()=>5000,execFile:()=>assert.fail('no external effects in local save'),herdr:()=>assert.fail('no Herdr in local save')});
 assert.equal(calls,1);assert.equal(saved?.then,undefined);assert.equal(saved.question.text,'Local callback');assert.equal(saved.journalSeq,seq+2);assert.equal(saved.updatedAt,5000);assert.equal(saved.waitingFor.what,'Local callback');assert.deepEqual(storage.readRun(run.runDir),saved);
 const before=fs.readFileSync(join(run.runDir,'status.json'),'utf8');
 for(const update of [()=>{throw Error('callback refused');},latest=>({...latest,runId:'replacement'}),async latest=>latest])assert.throws(()=>storage.updateRun(run.runDir,update,f.ports));
 assert.equal(fs.readFileSync(join(run.runDir,'status.json'),'utf8'),before,'callback failure and identity change leave prior bytes');
 const bad=join(f.base,'index-file');fs.writeFileSync(bad,'file');const indexed=storage.updateRun(run.runDir,latest=>{latest.message='Callback committed despite index failure';return latest;},{...f.ports,stateDir:bad});assert.equal(f.record().message,indexed.message);
});
async function indexControl(t){
 row('index-failure-after-successful-commit');
 const f=await fixture(t,{agent:'codex',name:'bug'});await f.run();const run=f.record();const bad=join(f.base,'not-a-directory');fs.writeFileSync(bad,'file');
 run.message='Committed despite index failure';const saved=storage.writeRun(run,{...f.ports,stateDir:bad});
 assert.equal(saved.message,'Committed despite index failure');assert.equal(f.record().message,saved.message);
 console.log(JSON.stringify({case:'index-failure-after-successful-commit',writeRunCommit:true}));
}

test('2753 compatible whole write waits for an in-progress native callback commit',async t=>{
 row('storage-compatibility-and-local-boundary');assert.equal(typeof storage.updateRun,'function');
 const {Worker}=await import('node:worker_threads');
 const f=await fixture(t,{agent:'codex',name:'bug'});await f.run();const run=f.record(),barrier=new SharedArrayBuffer(4),states=[];
 const release=()=>{Atomics.store(new Int32Array(barrier),0,1);Atomics.notify(new Int32Array(barrier),0);};
 function launch(mode,record){const worker=new Worker(new URL('./helpers/workflow-concurrent-storage-worker.mjs',import.meta.url),{workerData:{runDir:run.runDir,mode,barrier,record,stateDir:f.ports.stateDir}});t.after(async()=>{release();await worker.terminate();});let ready,complete;const held=new Promise((r,j)=>{ready=r;worker.on('error',j);}),result=new Promise((r,j)=>{complete=r;worker.on('error',j);});worker.on('message',m=>{if(m.held||m.attempting)ready();else{states.push({mode,...m});complete(m);}});return {held,result};}
 const updater=launch('update');await updater.held;
 const writer=launch('write',{...run,message:'Compatible replacement committed last'});await writer.held;
 // Give the whole writer an opportunity to publish while callback ownership
 // is held, then observe native storage before releasing the first update.
 await new Promise(resolve=>setTimeout(resolve,30));
 const before=storage.readRun(run.runDir);assert.notEqual(before.message,'Compatible replacement committed last','whole write cannot publish inside callback ownership');
 release();const outcomes=await Promise.all([updater.result,writer.result]);for(const out of outcomes)assert.equal(out.error,undefined);
 assert.equal(f.record().message,'Compatible replacement committed last');
});

test('2753 native ownership failures release only acquired ownership and retain commit truth',async t=>{
 row('storage-compatibility-and-local-boundary');assert.equal(typeof storage.updateRun,'function');
 const f=await fixture(t,{agent:'codex',name:'bug'});await f.run();const run=f.record(),path=join(run.runDir,'status.json'),before=fs.readFileSync(path,'utf8');let acquisitions=0;
 assert.throws(()=>storage.updateRun(run.runDir,latest=>{assert.fail('callback cannot run without acquisition');return latest;},{...f.ports,runFiles:{lstatSync:()=>{acquisitions++;throw Error('Ownership identity read failed');}}}));
 assert.equal(acquisitions,1);assert.equal(fs.readFileSync(path,'utf8'),before);
 const recovered=storage.updateRun(run.runDir,latest=>{latest.message='Acquisition recovered';return latest;},f.ports);assert.equal(recovered.message,'Acquisition recovered');
 let released=0;
 const committed=storage.updateRun(run.runDir,latest=>{latest.message='Published before release trouble';return latest;},{...f.ports,acquireRunOwnership:()=>()=>{released++;throw Error('Release unavailable');}});
 assert.equal(released,1);assert.equal(committed.message,'Published before release trouble');assert.equal(f.record().message,committed.message);
});
