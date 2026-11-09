import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync,readFileSync,existsSync} from 'node:fs';
import {join} from 'node:path';
import {fixture,packageRoot,matchingClaimPorts} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {factoryWorld} from './helpers/factory/world.mjs';
import * as manualGithub from '../src/issue-dependencies-github.mjs';
const readManualHold=manualGithub.readManualHold ?? (async()=>({held:false,known:false}));
import {githubLedger} from '../src/github-calls.mjs';
import {tickAutopilot} from '../src/autopilot-launcher.mjs';

test('final review: retained held group run gets no automatic worker request', async t => {
 const f=await fixture(t);
 assert.equal((await f.run()).exitCode,0);
 const run=f.record();
 run.automaticOrigin={repository:run.repo,coordinatorId:'owner',machine:'machine',claim:{commentId:'11',labelEventId:'12'}};
 writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
 writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',trust:[],github:{share:1,floor:0}}}));
 const stateFile=join(f.state,'launcher.json');
 writeFileSync(stateFile,JSON.stringify({enabled:true,defaultBranch:'main',baseBranch:'main',stateFile,cwd:f.source,repo:run.repo,packageRoot,runs:2,coordinatorId:'owner',machine:'machine',activatedAt:1,agent:{id:'claude',kind:'claude',command:'claude'},environment:f.ports.env}));
 const member='https://github.com/example/project/issues/18';
 const issue={number:18,state:'open',title:'Another group member',body:'Same root cause',user:{login:'example'},labels:[],html_url:member,comments:0,created_at:new Date(f.clock).toISOString(),updated_at:new Date(f.clock).toISOString()};
 const originalHerdr=f.herdr.herdr;
 const herdr=async args=>{
  if(args[0]==='pane'&&args[1]==='get') {
   const p=f.herdr.panes.find(p=>p.pane_id===args[2]);
   if(!p)throw Object.assign(Error('pane_not_found'),{code:'pane_not_found'});
   return {result:{pane:{...p,agent:p.agent?.agent,agent_status:p.agent?.agent_status,agent_session:p.agent?.agent_session,foreground_cwd:p.cwd}}};
  }
  return originalHerdr(args);
 };
 const ports={...healthyMachine,...f.ports,herdr,workflowHerdr:herdr,sendDigest:async()=>({exitCode:0}),checkCapacityPorts:isolatedCheckCapacity(f.base),owners:matchingClaimPorts(run),
  run:async(file,args,options)=>({code:0,...await f.ports.execFile(file,args,options)}),warn:()=>{},
  readManualHold:async({issue})=>({known:true,held:Number(issue)===17}),readSuiteProgress:()=>({state:'running'}),
  queryIssues:async()=>({status:200,issues:[issue]}),comments:async()=>[],
  reconcileDependencyIntake:async()=>({eligible:[member],queued:[],skipped:[],claims:[],groups:[{area:'cli',rootCause:'common',umbrella:run.issue.url,members:[run.issue.url,member]}]})};
 const saved=JSON.parse(readFileSync(stateFile));
 saved.githubIntake={at:f.clock,eligible:[member],claims:[],groups:[{area:'cli',rootCause:'common',umbrella:run.issue.url,members:[run.issue.url,member]}]};
 writeFileSync(stateFile,JSON.stringify(saved));
 const ledger=githubLedger({root:f.state,repository:run.repo});
 for(let n=0;n<3;n++)ledger.record({at:f.clock,api:'rest',purpose:'dependencies',status:200,resource:'core',remaining:90,limit:100,resetAt:f.clock+3600000});
 ports.reconcileDependencyIntake=async()=>assert.fail('cached low-budget intake should be used');
 f.herdr.idle();
 const start=f.herdr.calls.length;
 const result=await tickAutopilot(stateFile,ports);
 const state=JSON.parse(readFileSync(stateFile));
 assert.deepEqual(state.manualIssues,[17],'hold must be confirmed before the worker effect');
 const workerPanes=new Set(run.chats.map(chat=>chat.paneId));
 const prompts=f.herdr.calls.slice(start).filter(args=>args[0]==='agent'&&args[1]==='prompt'&&workerPanes.has(args[2]));
 assert.equal(prompts.length,0,'held retained worker received automatic group work');
 assert.deepEqual(f.record().changes,run.changes);
 assert.ok(state.githubIntake.eligible.includes(member));
});

test('final review: manual label during post-admission fetch prevents worker start',async t=>{
 const w=await factoryWorld(t);
 await w.start();await w.reviewDependencies();await w.tick();w.messages();
 const packet=[...w.packets].reverse().find(p=>p.issues.some(i=>i.number===17&&i.eligible));
 assert.ok(packet);
 const issue=packet.issues.find(i=>i.number===17);
 await w.github.gh(['issue','edit','17','--add-label','pdd:working']);
 const event=w.github.issues.get(17).timeline.at(-1);
 await w.github.gh(['issue','comment','17','--body-file','-'],{input:'Factory coordinator claim.\n\n```json\n'+JSON.stringify({repository:packet.repository,coordinatorId:packet.coordinatorId,machine:packet.machine,labelEventId:String(event.id),lastSeen:new Date(w.time).toISOString()})+'\n```'});
 const execute=w.execute;let injected=false;let holdEvent;
 w.execute=async(file,args,options)=>{
  if(!injected&&file==='git'&&args[0]==='fetch') {
   injected=true;
   await w.github.gh(['issue','edit','17','--add-label','pdd:manual']);
   holdEvent=w.github.issues.get(17).timeline.at(-1);
  }
  return execute(file,args,options);
 };
 const start=w.herdr.calls.length;
 const result=await w.command(['workflow','run','small-change','17','--agent','codex','--origin','autopilot','--decision-id',issue.decisionId,'--outcome','code'],{actor:'coordinator',env:w.context(),allowFailure:true});
 assert.equal(injected,true,'post-admission Git fetch boundary must be reached');
 assert.equal(holdEvent?.label?.name??holdEvent?.label,'pdd:manual');
 const authority=await readManualHold({repository:w.repository,issue:17,cwd:w.cwd},{env:w.env,execFile:w.execute});
 assert.deepEqual(authority,{held:true,known:true},'the writer hold must be effective');
 const launches=w.herdr.calls.slice(start).filter(args=>args[0]==='pane'&&args[1]==='run'&&args[3].includes('codex'));
 assert.equal(launches.length,0,'worker launched after a writer added the manual hold during startup fetch');
 assert.notEqual(result.code,0);
 assert.equal(existsSync(join(w.commonDir,'pdd/runs/17/status.json')),false);
});

test('3129 shared GitHub port blocks each held automatic write target and permits person commands', async () => {
 const api = await import('../src/issue-dependencies-github.mjs');
 const writes = [], reads = [];
 const execute = async (file,args) => {
  if (args[0]==='api' && !args.includes('--method')) {reads.push(args);return {stdout:JSON.stringify({issue_url:'https://api.github.com/repos/example/project/issues/17'})};}
  writes.push(args);return {stdout:'{}'};
 };
 const wrap = api.guardAutomaticGithubWrites ?? (execute=>execute);
 const ports = {readManualHold:async()=>({known:true,held:true})};
 const guarded = wrap(execute,ports,{repository:'example/project',issue:17});
 const cases = [
  ['api','--method','POST','repos/example/project/issues/17/comments'],
  ['api','--method','POST','repos/example/project/issues/17/labels'],
  ['api','--method','PATCH','repos/example/project/issues/comments/123'],
  ['api','--method','POST','repos/example/project/issues/17/dependencies/blocked_by'],
  ['api','--method','PATCH','repos/example/project/issues/17'],
  ['pr','comment','100','--body','audit'],
  ['issue','edit','17','--add-label','pdd:working'],
  ['api','--method','POST','graphql','--input','-'],
 ];
 const results=[];
 for(const args of cases) {try {await guarded('gh',args,{input:args.includes('graphql')?JSON.stringify({query:'mutation { updateIssue { clientMutationId } }'}):undefined});results.push('sent');}catch(error){results.push(error.code);}}
 assert.deepEqual(results,cases.map(()=> 'manual-hold'));
 assert.equal(writes.length,0);
 assert.equal(reads.length,1);
 await wrap(execute,ports,{repository:'example/project',issue:17,personDirected:true})('gh',cases[0]);
 assert.equal(writes.length,1);
});

test('3129 worker boundary rechecks authority after delivery waits and preserves person changes', async t => {
 const f=await fixture(t);assert.equal((await f.run()).exitCode,0);
 const run=f.record();run.automaticOrigin={repository:run.repo,coordinatorId:'owner',machine:'machine',claim:{commentId:'11',labelEventId:'12'}};
 writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
 const {changeRun}=await import('../src/workflow-runner.mjs');
 let held=false,reads=0;
 const ports={...f.ports,readManualHold:async()=>{reads++;return {known:true,held};},beforeDeliverySubmit:async()=>{held=true;return true;}};
 const start=f.herdr.calls.length;
 const result=await changeRun({ref:'17',cwd:f.source,text:'Inspect the saved work.'},ports);
 assert.equal(held,true);
 assert.notEqual(result.exitCode,0);
 assert.ok(reads>=2);
 assert.equal(f.herdr.calls.slice(start).filter(a=>a[0]==='agent'&&a[1]==='prompt').length,0);
 const manual=await changeRun({ref:'17',cwd:f.source,text:'Inspect the saved work.'},{...ports,personDirected:true,beforeDeliverySubmit:undefined});
 assert.equal(manual.exitCode,0);
 assert.equal(f.herdr.calls.slice(start).filter(a=>a[0]==='agent'&&a[1]==='prompt').length,1);
});

test('3129 native launch rechecks a hold after allocation and capacity observation',async t=>{
 const w=await factoryWorld(t);
 let injected=false;
 await w.begin({beforeRun:async()=>{
  const herdr=w.herdr.herdr;
  w.herdr.herdr=async args=>{
   if(!injected&&args[0]==='pane'&&args[1]==='list'&&existsSync(join(w.commonDir,'pdd/runs/17/status.json'))) {
    injected=true;await w.github.gh(['issue','edit','17','--add-label','pdd:manual']);
   }
   return herdr(args);
  };
  // This case deliberately refuses startup after the durable allocation.
  const command=w.command;
  w.command=(argv,options)=>command(argv,{...options,allowFailure:true});
 }});
 assert.equal(injected,true);
 const run=w.record();
 assert.ok(existsSync(run.root));
 assert.equal(w.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run'&&a[3].includes('codex')&&a[3].includes(run.root)).length,0);
 assert.ok(!run.chats.some(chat=>chat.startUnconfirmed));
});
