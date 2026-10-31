import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join,resolve} from 'node:path';
import {fixture} from './helpers/workflow-delivery-fixture.mjs';
import * as runner from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {captureSource} from '../src/runtime-preflight.mjs';
import {nativeCase,observations} from './helpers/workflow-concurrent-cases.mjs';
const packageRoot=resolve(import.meta.dirname,'..');
// Each variant gets its own real Git worktree, HOME and injected outside effects.
// A one-shot outside boundary records unrelated work after public selection.
// Controls that already pass on the base remain independent observations.
test('2753 every ordinary writer family retains unrelated progress and its own effects',async t=>{
 const row=nativeCase('all-ordinary-writer-families-preserve-unrelated-progress');
 const results={};
 const variants=['start-success','start-failure','open-success','open-failure','open-recovery','open-reset','open-newchat','evidence','done-next','done-gate','done-pr-gate','done-publication','approve-transition','approve-publication','cancel','status-detail','status-list','status-all','status-recovery','change'];
 for(const variant of variants){
  const f=await fixture(t,{agent:'codex',name:'bug'});let injected=false,retained,initial;
  const inject=()=>{
   if(injected)return;injected=true;
   const latest=f.record();latest.done.independent={at:2000,summary:'Other writer finished',area:'another'};
   latest.decisions.push({stage:'another',decision:'changes',at:2000});(latest.evidence??=[]).push({at:2000,summary:'Other evidence'});
   writeRun(latest,f.ports);retained=structuredClone(latest);
  };
  const originalHerdr=f.ports.herdr;
  if(variant.startsWith('start-'))f.ports.herdr=async args=>{
   if(args[0]==='pane'&&args[1]==='run'){inject();if(variant==='start-failure')throw Object.assign(Error('Startup unavailable'),{code:'server_unavailable'});}
   return originalHerdr(args);
  };
  let out=await f.run();initial=f.record();
  if(!variant.startsWith('start-')){
   let run=f.record();
   if(variant.startsWith('done-')){
    run.areas[0].steps=['finish',...(variant==='done-next'?['next']:[])];run.areas[0].optional=[];
    run.areas[0].gate=variant==='done-pr-gate'||variant==='done-publication'?'pr':'approve';
    if(variant==='done-pr-gate')run.areas[0].before='approve';
    if(variant==='done-publication'){run.areas[0].then='ask-code';fs.writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');}
   }
   if(variant.startsWith('approve-')){
    run.done={reproduce:{at:1,summary:'Finished',area:'story'}};run.gate={area:'story',at:1,kind:variant==='approve-publication'?'approve-pr':'approve'};
    if(variant==='approve-publication'){run.areas[0].gate='pr';fs.writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');}
   }
   if(variant.startsWith('status-')){run.pr=[{url:'https://github.com/example/project/pull/23',stage:'story',number:23,state:'open',ci:'pending'}];run.state='waiting';}
   if(variant==='open-recovery'||variant==='status-recovery'){run.chatFailure={area:'story',phase:'start',code:'unconfirmed',message:'Previous failure',at:1};run.chats[0].startUnconfirmed=true;run.state='waiting';}
   if(variant==='open-reset'){f.herdr.tabs=[];for(const pane of f.herdr.panes)pane.agent=null;}
   if(variant==='open-newchat')run.chats=[];
   writeRun(run,f.ports);
   const ports={...f.ports};
   if(variant.startsWith('open-')||variant==='status-recovery')ports.herdr=async args=>{inject();if(variant==='open-failure')throw Object.assign(Error('Unavailable'),{code:'server_unavailable'});return originalHerdr(args);};
   else ports.now=()=>{inject();return 3000;};
   if(variant.startsWith('status-'))ports.readPrStatus=async()=>{inject();return {state:'open',ci:'success'};};
   if(variant==='evidence'){
    const root=join(packageRoot,'test/fixtures/harbor');for(const dir of ['prompts','tests','user_stories'])fs.cpSync(join(root,dir),join(run.root,dir),{recursive:true});
    const tests=['tests/place-order.json','tests/unknown-item.json'];const source=captureSource(run.root,{tests,appMap:null});
    const rows=tests.map(test=>{const story=test.split('/').at(-1).replace('.json','');return {test,story,state:'passed',criteria:{passed:1,total:1},checks:{passed:1,total:1},calls:0,summary_line:`Runtime check (${story}): ✓ 1 of 1 criterion · 1/1 checks · 0 AI calls`};});
    const file=join(f.base,'receipt.json');fs.writeFileSync(file,JSON.stringify({repo:run.root,source_sha256:source.sha256,rows}));
    out=await runner.recordEvidence({ref:'17',summaryFile:file,cwd:run.root},ports);
   }else if(variant.startsWith('done-'))out=await runner.stepDone({step:'finish',summary:'Own step finished',cwd:run.root},ports);
   else if(variant.startsWith('approve-'))out=await runner.approveRun({ref:'17',cwd:f.source},ports);
   else if(variant.startsWith('open-'))out=await runner.openRun({ref:'17',cwd:f.source},ports);
   else if(variant==='cancel')out=await runner.cancelRun({ref:'17',cwd:f.source},ports);
   else if(variant==='change')out=await runner.changeRun({ref:'17',text:'Own requested change',cwd:f.source},ports);
   else out=await runner.runStatus({ref:variant==='status-detail'||variant==='status-recovery'?'17':undefined,cwd:variant==='status-list'?f.source:run.root,all:variant==='status-all'},ports);
  }
  const saved=f.record(),expectedFailure=['start-failure','open-failure','open-reset'].includes(variant);
  const checks={injected:()=>assert.equal(injected,true),outcome:()=>assert.equal(out.exitCode,expectedFailure?1:0,out.message),done:()=>assert.deepEqual(saved.done.independent,retained?.done.independent),decisions:()=>assert.ok(saved.decisions.some(d=>d.at===2000)),evidence:()=>assert.ok(saved.evidence?.some(e=>e.summary==='Other evidence')),own:()=>{
   if(variant.startsWith('done-'))assert.equal(saved.done.finish.summary,'Own step finished');
   if(variant==='cancel')assert.equal(saved.state,'cancelled');
   if(variant==='evidence')assert.equal(saved.evidence.at(-1).receipt.rows.length,2);
   if(variant==='approve-transition')assert.equal(saved.area,1);
   if(variant==='done-publication'||variant==='approve-publication')assert.equal(saved.pr.length,1);
   if(variant==='change')assert.equal(saved.changes.at(-1).text,'Own requested change');
   if(variant.includes('recovery'))assert.equal(saved.chatFailure,undefined);
   if(variant==='open-failure'||variant==='start-failure')assert.ok(saved.chatFailure);
  }};
  results[variant]=Object.fromEntries(Object.entries(checks).map(([key,check])=>{try{check();return [key,true];}catch(error){return [key,{code:error.code,message:error.message}];}}));
 }
 console.log(JSON.stringify({case:row.id,variants:results}));
 assert.deepEqual(Object.entries(results).filter(([,checks])=>Object.values(checks).some(value=>value!==true)).map(([name])=>name),[],'all native writer families preserve concurrent facts and own effects');
});
