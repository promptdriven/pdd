import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { createWorkflowProgress } from '../src/workflow-progress.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
const id='12345678-1234-4123-8123-123456789abc';
const capture=()=>({text:'',write(value){this.text+=value;}});
const view={runId:id,name:'small-change',issue:17,stage:{id:'scope',kind:'agent'},ordinal:1,total:5,root:'/project worktree',branch:'pdd/change',journal:'/git/run/journal.jsonl',files:[],prs:[]};
const stages=Object.fromEntries(['runHerdrStage','inspectHerdrStage','attachHerdrStage','closeHerdrStage'].map(name=>[name,()=>assert.fail('No stage effects')]));

test('progress deduplicates polling, shows actual location, review artifacts, short approval command and PR',()=>{
 const stdout=capture(),progress=createWorkflowProgress({stdout,now:()=>0});
 progress.observe({...view,event:'run.started'});
 progress.observe({...view,event:'agent.intent'});
 const backend={session:'pdd-real-hash',workspaceId:'workspace-42'};
 for(let i=0;i<50;i++)progress.observe({...view,event:'agent.backend',backend});
 assert.equal(stdout.text.match(/workspace-42/g).length,1);
 assert.equal(stdout.text.match(/scope started/g).length,1);
 assert.match(stdout.text,/^\d{2}:\d{2}  scope started$/m);
 progress.observe({...view,event:'agent.completed',ended:'scope',stage:{id:'change',kind:'agent'}});
 progress.observe({...view,event:'result',state:'waiting',stage:{id:'change',kind:'agent'},summary:'Recommend feature.\n\x1b[2J',files:['/git/run/scope.json','/project worktree/cases.md']});
 assert.match(stdout.text,/Read: \/git\/run\/scope.json/);
 assert.match(stdout.text,/Read: \/project worktree\/cases.md/);
 assert.match(stdout.text,/Summary: Recommend feature/);assert.doesNotMatch(stdout.text,/\x1b/);
 assert.ok(stdout.text.includes('Approve: pdd workflow approve #17'));
 const before=stdout.text.length;
 progress.observe({...view,event:'result',state:'waiting',stage:{id:'wait-merge',kind:'merge'},prs:['https://github.com/example/repo/pull/2']});
 assert.match(stdout.text.slice(before),/PR: https:\/\/github.com\/example\/repo\/pull\/2/);
 assert.doesNotMatch(stdout.text.slice(before),/--decision approve/);
 progress.interrupt();assert.match(stdout.text,/agent may keep working in Herdr/);
 assert.match(stdout.text,/PDD moves on when you run:/);
 assert.doesNotMatch(stdout.text,/run goes on in the background/);
});

test('CLI prints before awaiting runner, preserves result and cleans up SIGINT handler',async()=>{
 const stdout=capture(),stderr=capture(),signalSource=new EventEmitter();let finish;
 const waiting=new Promise(resolve=>{finish=resolve;});let entered;
 const started=new Promise(resolve=>{entered=resolve;});
 const workflowRunner={async runWorkflow(input,ports){assert.match(stdout.text,/Starting small-change/);assert.equal('runId' in input,false);ports.onProgress({...view,event:'run.started'});entered();await waiting;return {state:'waiting',exitCode:2,message:'FINAL RESULT'};}};
 const result=runPdd(['workflow','run','small-change','17'],{stdout,stderr,signalSource,workflowRunner,workflowStages:stages});
 await started;assert.match(stdout.text,new RegExp(id));assert.equal(signalSource.listenerCount('SIGINT'),1);
 finish();assert.equal(await result,2);assert.equal(signalSource.listenerCount('SIGINT'),0);
 assert.equal(stdout.text.match(/FINAL RESULT/g).length,1);assert.equal(stderr.text,'');
});

test('SIGINT reports same saved run and exits 130; early interruption invents no ID',async()=>{
 for(const prepared of [false,true]){
  const stdout=capture(),signalSource=new EventEmitter();let exitCode;
  const workflowRunner={async runWorkflow(input,ports){if(prepared)ports.onProgress({...view,event:'run.started'});signalSource.emit('SIGINT');return {state:'waiting',exitCode:2,message:'stopped'};}};
  await runPdd(['workflow','run','small-change','17'],{stdout,stderr:capture(),signalSource,exit:code=>{exitCode=code;},workflowRunner,workflowStages:stages});
  assert.equal(exitCode,130);assert.equal(signalSource.listenerCount('SIGINT'),0);
  if(prepared)assert.ok(stdout.text.includes('pdd workflow approve #17'));
  else {assert.match(stdout.text,/before a run identity was confirmed/);assert.doesNotMatch(stdout.text,/pdd workflow resume/);}
 }
});

test('interrupted resume retains its explicit UUID before saved state lookup',async()=>{
 const stdout=capture(),signalSource=new EventEmitter();let status;
 await runPdd(['workflow','resume',id],{stdout,stderr:capture(),signalSource,exit:code=>{status=code;},workflowStages:stages,
  workflowRunner:{async resumeWorkflow(){signalSource.emit('SIGINT');return {state:'waiting',exitCode:2,message:'lookup interrupted'};}}});
 assert.equal(status,130);assert.ok(stdout.text.includes(`Inspect: pdd workflow resume ${id}`));
 assert.doesNotMatch(stdout.text,/before a run identity was confirmed/);
});

test('header names the issue title, times are local HH:MM, one watch line, no internal file paths',()=>{
 const stdout=capture(),progress=createWorkflowProgress({stdout,now:()=>0,timeZone:'America/Los_Angeles'});
 const v={...view,title:'Always show prices with 2 decimals',agent:'codex'};
 progress.observe({...v,event:'run.started'});
 progress.observe({...v,event:'agent.intent'});
 progress.observe({...v,event:'agent.backend',backend:{session:'pdd-real-hash'}});
 for(let i=0;i<3;i++)progress.observe({...v,event:'agent.backend',backend:{session:'pdd-real-hash',workspaceId:'w1'}});
 progress.observe({...v,event:'agent.completed',ended:'scope',stage:{id:'change',kind:'agent'}});
 progress.observe({...v,event:'result',state:'waiting',stage:{id:'change',kind:'agent'},summary:'Plan ready',files:[]});
 const out=stdout.text;
 progress.interrupt();
 assert.doesNotMatch(stdout.text,/journal\.jsonl|Saved run/);
 assert.ok(out.includes(`Run ${id}: small-change for #17 "Always show prices with 2 decimals". Stage 1/5: scope.`),out);
 assert.match(out,/^Working copy: \/project worktree \(branch pdd\/change\)$/m);
 assert.match(out,/^16:00  scope started$/m);
 assert.match(out,/^16:00  scope done$/m);
 assert.match(out,/^16:00  waiting for you before change$/m);
 assert.doesNotMatch(out,/\d{4}-\d{2}-\d{2}T/);
 assert.equal(out.match(/pdd workflow attach/g).length,1);
 assert.match(out,/^Open the agent: pdd workflow attach \S+ \(opens a view; the run keeps working\)$/m);
 assert.doesNotMatch(out,/journal\.jsonl|Saved run/);
 assert.doesNotMatch(out,/preparing/);
 assert.equal(out.match(/Herdr session/g).length,1);
 assert.match(out,/^Codex is working in Herdr session pdd-real-hash, workspace w1\.$/m);
});

test('a long stage prints a still-working line every two minutes, not on every poll',()=>{
 let t=0;const stdout=capture(),progress=createWorkflowProgress({stdout,now:()=>t,timeZone:'UTC'});
 const backend={session:'pdd-real-hash',workspaceId:'w1'};
 progress.observe({...view,event:'agent.intent'});
 for(t=0;t<=5*60000;t+=5000)progress.observe({...view,event:'agent.backend',backend});
 assert.deepEqual(stdout.text.match(/scope still working \(\d+ min\)/g),['scope still working (2 min)','scope still working (4 min)']);
 progress.observe({...view,event:'agent.completed',ended:'scope',stage:{id:'change',kind:'agent'}});
 const before=stdout.text.length;t+=10*60000;
 progress.observe({...view,event:'agent.backend',backend,stage:{id:'change',kind:'agent'}});
 assert.doesNotMatch(stdout.text.slice(before),/still working/);
});

test('merge wait says the person merges, with a local time',()=>{
 const stdout=capture(),progress=createWorkflowProgress({stdout,now:()=>0,timeZone:'UTC'});
 progress.observe({...view,event:'result',state:'waiting',stage:{id:'wait-merge',kind:'merge'},prs:['https://github.com/example/repo/pull/2']});
 assert.match(stdout.text,/^00:00  waiting for you to merge the PR$/m);
});

test('CLI start line marks a bare issue number with #',async()=>{
 const stdout=capture(),signalSource=new EventEmitter();
 const workflowRunner={async runWorkflow(){return {state:'waiting',exitCode:2,message:'done'};}};
 await runPdd(['workflow','run','small-change','17'],{stdout,stderr:capture(),signalSource,workflowRunner,workflowStages:stages});
 assert.match(stdout.text,/^Starting small-change for issue #17\. /m);
});
