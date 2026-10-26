import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { createWorkflowProgress } from '../src/workflow-progress.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
const id='12345678-1234-4123-8123-123456789abc';
const capture=()=>({text:'',write(value){this.text+=value;}});
const view={runId:id,name:'small-change',issue:17,stage:{id:'scope',kind:'agent'},ordinal:1,total:5,root:'/project worktree',branch:'pdd/change',journal:'/git/run/journal.jsonl',files:[],prs:[]};
const stages=Object.fromEntries(['runHerdrStage','inspectHerdrStage','attachHerdrStage','closeHerdrStage'].map(name=>[name,()=>assert.fail('No stage effects')]));

test('progress deduplicates polling, shows actual location, review artifacts, full resume command and PR',()=>{
 const stdout=capture(),progress=createWorkflowProgress({stdout,now:()=>0});
 progress.observe({...view,event:'run.started'});
 progress.observe({...view,event:'agent.intent'});
 const backend={session:'pdd-real-hash',workspaceId:'workspace-42'};
 for(let i=0;i<50;i++)progress.observe({...view,event:'agent.backend',backend});
 assert.equal(stdout.text.match(/workspace-42/g).length,1);
 assert.equal(stdout.text.match(/stage scope started/g).length,1);
 assert.match(stdout.text,/\[1970-01-01T00:00:00.000Z\]/);
 progress.observe({...view,event:'agent.completed',ended:'scope',stage:{id:'change',kind:'agent'}});
 progress.observe({...view,event:'result',state:'waiting',stage:{id:'change',kind:'agent'},summary:'Recommend feature.\n\x1b[2J',files:['/git/run/scope.json','/project worktree/cases.md']});
 assert.match(stdout.text,/Read: \/git\/run\/scope.json/);
 assert.match(stdout.text,/Read: \/project worktree\/cases.md/);
 assert.match(stdout.text,/Summary: Recommend feature/);assert.doesNotMatch(stdout.text,/\x1b/);
 assert.ok(stdout.text.includes(`Approve: pdd workflow resume ${id} --decision approve`));
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
  if(prepared)assert.ok(stdout.text.includes(`pdd workflow resume ${id} --decision approve`));
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
