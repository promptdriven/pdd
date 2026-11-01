import test from 'node:test';
import assert from 'node:assert/strict';
import {Worker} from 'node:worker_threads';
import {uptakeFixture} from './helpers/workflow-concurrent-fixture.mjs';
import * as storage from '../src/workflow-runs.mjs';

// Story Rules to check: exhaustive finite intent schedules, not arbitrary overlap.
function record(rows,label,checks){
 const checksResult={};
 for(const [name,check] of Object.entries(checks))try{check();checksResult[name]=true;}catch(error){checksResult[name]={code:error.code,message:error.message};}
 rows.push({label,checks:checksResult});
}
function conclude(rows){
 console.log(JSON.stringify({formalObservations:rows}));
 assert.deepEqual(rows.flatMap(row=>Object.entries(row.checks).filter(([,v])=>v!==true).map(([name])=>`${row.label}:${name}`)),[],'Story forbids loss of unrelated durable work or failure of own intended effects');
}
async function held(t,f,operation,extra={}){
 const run=f.record(),barrier=new SharedArrayBuffer(4);
 const worker=new Worker(new URL('./helpers/workflow-concurrent-stale-writer.mjs',import.meta.url),{workerData:{operation,root:run.root,source:f.source,stateDir:f.ports.stateDir,env:f.ports.env,barrier,...extra}});
 const release=()=>{Atomics.store(new Int32Array(barrier),0,1);Atomics.notify(new Int32Array(barrier),0);};
 t.after(async()=>{release();await worker.terminate();});
 let ready,done;
 const waiting=new Promise((r,j)=>{ready=r;worker.on('error',j);});
 const result=new Promise((r,j)=>{done=r;worker.on('error',j);});
 worker.on('message',m=>m.held?ready():done(m));
 await waiting;return async()=>{release();return result;};
}
const fact=(summary,area='story',at=2000)=>({summary,area,at});
const save=(f,run)=>storage.writeRun(run,f.ports);

test('2753 formal bounded rerun invalidation retains disjoint latest work (12 schedules)',{timeout:120000},async t=>{
 const rows=[];
 for(const [target,later] of [['build','verify'],['build','formal'],['verify','formal']])for(const existed of [false,true])for(const extra of [false,true]){
  const f=await uptakeFixture(t),run=f.record();run.areas[0].steps=['build','verify','formal'];
  run.done={[target]:fact('Old own'),unknown:fact('Keep unknown'),check:fact('Keep other area','code')};
  if(existed)run.done[later]=fact('Old later');save(f,run);
  const finish=await held(t,f,'stepDone',{step:target,summary:'Rebuilt'}),latest=f.record();
  latest.done[later]=fact('New later');latest.done.independent=fact('New unrelated');if(extra)latest.done.extra=fact('Extra unrelated');save(f,latest);
  const outcome=await finish(),saved=f.record();
  record(rows,`${target}/${later}/${existed}/${extra}`,{
   success:()=>assert.equal(outcome.result?.exitCode,0),own:()=>assert.equal(saved.done[target]?.summary,'Rebuilt'),
   invalidation:()=>{for(const key of ['build','verify','formal'].slice(['build','verify','formal'].indexOf(target)+1))assert.equal(saved.done[key],undefined);},
   independent:()=>assert.deepEqual(saved.done.independent,latest.done.independent),extra:()=>assert.deepEqual(saved.done.extra,latest.done.extra),
   unknown:()=>assert.deepEqual(saved.done.unknown,latest.done.unknown),otherArea:()=>assert.deepEqual(saved.done.check,latest.done.check)
  });
 }
 conclude(rows);
});

test('2753 formal bounded completion preserves independently newer question (6 schedules)',{timeout:120000},async t=>{
 const rows=[];
 // Absent initial question has two distinct replacements; present initial has
 // every nonidentical combination of text/time, plus same text/time other area.
 const variants=[[null,'New',2000,'story'],[null,'New',0,'story'],['Old','Old',2000,'story'],['Old','New',100,'story'],['Old','New',2000,'story'],['Old','Old',100,'code']];
 for(const [initial,text,at,area] of variants){
  const f=await uptakeFixture(t),run=f.record();run.question=initial===null?null:{text:initial,at:100,area:'story'};save(f,run);
  const finish=await held(t,f,'stepDone',{step:'independent-own',summary:'Own completion'}),latest=f.record();
  latest.question={text,at,area};latest.done.independent=fact('New unrelated');save(f,latest);
  const outcome=await finish(),saved=f.record();
  record(rows,JSON.stringify([initial,text,at,area]),{success:()=>assert.equal(outcome.result?.exitCode,0),question:()=>assert.deepEqual(saved.question,latest.question),own:()=>assert.equal(saved.done['independent-own']?.summary,'Own completion'),independent:()=>assert.deepEqual(saved.done.independent,latest.done.independent)});
 }
 conclude(rows);
});

test('2753 formal bounded own ask and CI effects preserve disjoint fields (8 schedules)',{timeout:120000},async t=>{
 const rows=[];
 for(const operation of ['askPerson','runStatus'])for(const questionGroup of [false,true])for(const prGroup of [false,true]){
  const f=await uptakeFixture(t),run=f.record();run.pr=[{url:'https://github.com/example/project/pull/23',stage:'story',number:23,state:'open',ci:'pending',base:'old-base'}];save(f,run);
  const finish=await held(t,f,operation,{text:'Own question'}),latest=f.record();latest.done.independent=fact('New unrelated');
  if(questionGroup){latest.question={text:'Independent question',at:2000,area:'story'};latest.gate={area:'story',at:2000,kind:'approve'};latest.decisions.push({stage:'story',decision:'changes',at:2000});latest.area=1;}
  if(prGroup){latest.pr[0].base='newer-base';latest.pr.push({url:'https://github.com/example/project/pull/24',stage:'code',number:24,state:'open',ci:'pending'});}save(f,latest);
  const outcome=await finish(),saved=f.record();
  record(rows,`${operation}/${questionGroup}/${prGroup}`,{success:()=>assert.equal(outcome.result?.exitCode,0),independent:()=>assert.deepEqual(saved.done.independent,latest.done.independent),question:()=>operation==='askPerson'?assert.equal(saved.question?.text,'Own question'):assert.deepEqual(saved.question,latest.question),gate:()=>assert.deepEqual(saved.gate,latest.gate),decisions:()=>assert.deepEqual(saved.decisions,latest.decisions),area:()=>assert.equal(saved.area,latest.area),base:()=>assert.equal(saved.pr[0].base,latest.pr[0].base),separatePr:()=>assert.deepEqual(saved.pr[1],latest.pr[1]),ownCI:()=>{if(operation==='runStatus')assert.equal(saved.pr[0].ci,'success');}});
 }
 conclude(rows);
});
