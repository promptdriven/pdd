import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-delivery-fixture.mjs';
import {stepDone,approveRun} from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';

// AC1: publication owns its PR facts, not another area's newer gate/state.
for(const action of ['done-pr','done-ask-code','approve-pr'])test(`2753 ${action} publication preserves a newer area's gate and state`,async t=>{
 const results={};
 for(const concurrent of [true,false]){
  const f=await fixture(t,{agent:'codex',name:'bug'});assert.equal((await f.run()).exitCode,0);
  const run=f.record();run.areas[0].steps=['finish'];run.areas[0].optional=[];run.areas[0].gate='pr';
  delete run.areas[0].before;delete run.areas[0].then;
  if(action==='done-ask-code')run.areas[0].then='ask-code';
  if(action==='approve-pr'){
   run.areas[0].before='approve';run.done.finish={at:1,summary:'Own completed work',area:run.areas[0].name};
   run.gate={kind:'approve-pr',area:run.areas[0].name,at:1};run.state='waiting';
  }
  writeRun(run,f.ports);writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
  let injected=false,newer;const original=f.ports.execFile;
  const ports={...f.ports,execFile:async(file,args,opts)=>{
   if(concurrent&&!injected&&file==='git'&&args[0]==='status'){
    injected=true;newer=f.record();newer.area=1;
    newer.gate={area:newer.areas[1].name,kind:'approve',at:9000};
    newer.state='running';newer.question={text:'Independent newer question',area:newer.areas[1].name,at:9000};
    newer.done.independent={summary:'Newer durable work',area:newer.areas[1].name,at:9000};writeRun(newer,f.ports);
   }
   return original(file,args,opts);
  }};
  const out=action==='approve-pr'?await approveRun({ref:'17',cwd:f.source},ports):await stepDone({step:'finish',summary:'Own publication',cwd:run.root},ports);
  const saved=f.record(),checks={
   outcome:()=>assert.equal(out.exitCode,0,out.message),boundary:()=>assert.equal(injected,concurrent),
   publication:()=>{assert.equal(saved.pr.length,1);assert.equal(saved.pr[0].stage,run.areas[0].name);assert.equal(f.prs.length,1);},
   ownWork:()=>assert.ok(saved.done.finish),
   gate:()=>assert.deepEqual(saved.gate,concurrent?newer.gate:action==='done-ask-code'?{area:run.areas[0].name,at:f.clock,kind:'ask-code'}:null),
   area:()=>assert.equal(saved.area,concurrent?1:0),state:()=>assert.equal(saved.state,concurrent?newer.state:'waiting'),
   question:()=>assert.deepEqual(saved.question??null,concurrent?newer.question:null),
   unrelatedWork:()=>assert.deepEqual(saved.done.independent,newer?.done.independent),
   approval:()=>{if(action==='approve-pr')assert.ok(saved.decisions.some(d=>d.stage===run.areas[0].name&&d.decision==='approve'));}
  };
  results[concurrent?'overlap':'sequential']=Object.fromEntries(Object.entries(checks).map(([key,check])=>{try{check();return [key,true];}catch(error){return [key,{code:error.code,message:error.message}];}}));
 }
 console.log(JSON.stringify({action,results}));
 assert.deepEqual(Object.entries(results).filter(([,checks])=>Object.values(checks).some(value=>value!==true)).map(([variant])=>variant),[],`${action} preserves each independent fact and its own publication`);
});
