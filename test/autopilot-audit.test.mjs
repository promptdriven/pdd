import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as nativeFs from 'node:fs';
import {readFileSync,writeFileSync,mkdirSync,readdirSync,unlinkSync} from 'node:fs';
import {join} from 'node:path';
import {createHash,randomUUID} from 'node:crypto';
import {runPdd} from '../src/pdd-cli.mjs';
import {captureCosts} from '../src/cost-ledger.mjs';
import {updateRunCosts} from '../src/workflow-runs.mjs';
import {fixture} from './helpers/workflow-runner-fixture.mjs';

const merge='a'.repeat(40),parent='b'.repeat(40);
const result = (verdict='OK') => ({verdict,kind:verdict==='CONCERN'?'missing-reproduction':'',summary:'Synthetic audit observation',evidence:'1. Parent fails and merge passes.\n2. Scope retained.\n3. Observable cases.\n4. Old test fails.\n5. Native evidence.\n6. Checks retained.\n7. Gates confirmed.',revert:verdict==='BAD'});
async function world(t) {
  const f=await fixture(t);f.ports.skipMetricsDelivery=true;assert.equal((await f.run()).exitCode,0);
  const run=f.record();run.agent='codex';delete run.launchProfile;run.configDir=join(f.ports.env.HOME,'.codex');run.runId??=randomUUID();run.baseBranch='main';run.automaticOrigin={coordinatorId:'factory',machine:'test'};
  run.pr=[{number:23,state:'merged',stage:'change'}];
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto'}}));
  const w={...f,run,agent:'codex',calls:[],launches:[],alerts:[],answer:result(),session:randomUUID(),limit:'healthy',usage:{known:true,total:0},merged:true};
  w.concernFolder=()=>join(w.ports.stateDir,'autopilot-audits',createHash('sha256').update(w.run.repo.toLowerCase()).digest('hex').slice(0,20),'concerns');
  w.file=n=>join(run.runDir,'audits',`${n??23}.json`);
  w.audit=n=>JSON.parse(readFileSync(w.file(n),'utf8'));
  const execute=async(file,args,options={})=>{
    w.calls.push({file,args,options});
    if(file==='gh' && args[0]==='api') {
      const path=args.find(a=>a.startsWith('repos/'));
      if(args.includes('POST')) {
        if(w.writeFailure) throw Error('synthetic uncertain write');
        return {code:0,stdout:JSON.stringify({html_url:'https://github.com/example/project/issues/99'})};
      }
      if(/\/pulls\//.test(path))return {code:0,stdout:JSON.stringify({number:Number(path.split('/').at(-1)),merged:w.merged,merge_commit_sha:merge,base:{ref:w.targetBase??'main',repo:{full_name:w.repo??run.repo}}})};
      if(/\/commits\//.test(path))return {code:0,stdout:JSON.stringify({sha:merge,parents:[{sha:parent}]})};
    }
    if(file==='gh' && args[0]==='pr' && args[1]==='create' && w.uncertain==='revert-pr')throw Error('unconfirmed PR');
    if(file==='git' && args[0]==='push' && w.uncertain==='push')throw Error('unconfirmed push');
    if(file==='gh' && args[0]==='pr' && args[1]==='create')return {code:0,stdout:'https://github.com/example/project/pull/99\n'};
    if(file==='git' && ['clone','checkout','switch','push'].includes(args[0]))return {code:0,stdout:''};
    if(file==='git' && args[0]==='rev-list')return {code:0,stdout:merge+' '+parent+(w.squash?'':' '+'c'.repeat(40))};
    if(file==='git' && args.includes('revert')) {if(w.conflict) return {code:1,stdout:'',stderr:'conflict'};return {code:0,stdout:''};}
    const reply=await f.ports.execFile(file,args,options);return {code:reply.code??0,...reply};
  };
  w.check=async(pr=23)=>{
    const stdout={text:'',write(s){this.text+=s;}},stderr={text:'',write(s){this.text+=s;}};
    const code=await runPdd(['autopilot','audit','17',String(pr)],{cwd:f.source,env:f.ports.env,stdout,stderr,autopilotLauncherPorts:{...f.ports,...(w.fs?{fs:w.fs}:{}),run:execute,
      agentDefinitions:()=>[{kind:w.agent,name:w.agent,command:'configured-codex',env:{}}],codexLimits:async()=>({state:w.limit}),...(w.nativeUsage?{}:{dailyUsage:async()=>w.usage}),...(w.refreshCosts?{refreshCosts:w.refreshCosts}:{}),
      runAuditor:async(command,args,options)=>{w.launches.push({command,args,options});await w.delay?.();if(w.agent==='claude') return {code:0,stdout:JSON.stringify({session_id:w.session,result:JSON.stringify(w.answer)})};return {code:w.providerExit??0,stdout:JSON.stringify({type:'thread.started',thread_id:w.session})+'\n'+JSON.stringify({type:'item.completed',item:{type:'agent_message',text:w.raw??JSON.stringify(w.answer)}})+'\n'};},
      sendAlert:async input=>{w.alerts.push(input);return {exitCode:w.uncertain==='alert'?1:0};},
    }});
    return {code,text:stdout.text+stderr.text};
  };
  w.config=value=>writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',...value}}));
  return w;
}
async function atLaunch(ready,pending) {
  assert.equal(await Promise.race([ready.then(()=>true),pending.then(()=>false)]),true,'an automatic merge must start its auditor');
}
const comments = w=>w.calls.filter(c=>c.file==='gh'&&c.args.includes('POST')&&c.args.some(a=>a.endsWith('/comments')));

test('3111 automatic merged PR launches one fresh auditor, saves pinned evidence and comments once',async t=>{
  const w=await world(t),out=await w.check();assert.equal(out.code,0,out.text);
  const saved=w.audit();assert.equal(saved.result.verdict,'OK');assert.equal(saved.merge,merge);assert.equal(saved.parent,parent);assert.equal(saved.runId,w.run.runId);
  assert.equal(saved.chat.session.id,w.session);assert.equal(w.launches.length,1);assert.equal(w.launches[0].command,'configured-codex');
  assert.equal(w.launches[0].args.includes('resume'),false);assert.ok(w.launches[0].options.input.includes(parent));assert.ok(w.launches[0].options.input.includes(merge));
  assert.equal(comments(w).length,1);assert.equal((await w.check()).code,0);assert.equal(w.launches.length,1);assert.equal(comments(w).length,1);
});
test('3111 concurrent calls cannot start a second auditor',async t=>{
  const w=await world(t);let release,started;const ready=new Promise(r=>{started=r;});w.delay=()=>new Promise(r=>{release=r;started();});
  const first=w.check();await atLaunch(ready,first);const second=await w.check();assert.equal(second.code,1);release();assert.equal((await first).code,0);assert.equal(w.launches.length,1);
});
for(const [name,configure] of [
  ['unmerged',w=>{w.merged=false;}],['foreign target',w=>{w.repo='other/repo';}],['wrong base',w=>{w.targetBase='other';}],
  ['account limited',w=>{w.limit='limited';}],['account unknown',w=>{w.limit='unknown';}],
  ['daily cap',w=>{w.config({auditTokenLimit:100});w.usage={known:true,total:100};}],
  ['daily unknown',w=>{w.config({auditTokenLimit:100});w.usage={known:false,total:0};}],
  ['observe',w=>{w.config({mode:'observe'});}]
]) test(`3111 ${name} holds without a model call or GitHub write`,async t=>{
  const w=await world(t);configure(w);assert.equal((await w.check()).code,1);assert.equal(w.launches.length,0);assert.equal(comments(w).length,0);
});
test('3111 per-repository disable makes no model or GitHub call',async t=>{
  const w=await world(t);w.config({audit:false});const out=await w.check();assert.equal(out.code,0,out.text);assert.equal(w.launches.length,0);assert.equal(w.calls.filter(c=>c.file==='gh').length,0);
});
for(const mode of ['invalid-json','invalid-verdict','provider-refusal','reused-session'])test(`3111 ${mode} remains unknown and is never relaunched`,async t=>{
  const w=await world(t);
  if(mode==='invalid-json')w.raw='not json';if(mode==='invalid-verdict')w.answer.verdict='GOOD';if(mode==='provider-refusal')w.providerExit=1;
  if(mode==='reused-session') {w.run.chats.push({agent:'codex',session:{id:w.session}});writeFileSync(join(w.run.runDir,'status.json'),JSON.stringify(w.run));}
  assert.equal((await w.check()).code,1);assert.equal(w.audit().state,'unknown');assert.equal(w.audit().chat.session.id,w.session);assert.equal((await w.check()).code,1);assert.equal(w.launches.length,1);assert.equal(comments(w).length,0);
});
test('3111 BAD pushes only a unique revert branch, opens one PR and alerts once',async t=>{
  const w=await world(t);w.answer=result('BAD');const out=await w.check();assert.equal(out.code,0,out.text);
  const pushes=w.calls.filter(c=>c.file==='git'&&c.args[0]==='push');assert.equal(pushes.length,1);assert.match(pushes[0].args.at(-1),/^HEAD:refs\/heads\/pdd\/revert-23-/);
  assert.ok(w.calls.find(c=>c.file==='git'&&c.args.includes('revert')).args.includes('-m'));assert.equal(w.calls.filter(c=>c.file==='gh'&&c.args[0]==='pr'&&c.args[1]==='create').length,1);
  assert.equal(w.alerts.length,1);assert.equal(w.audit().revert.state,'sent');assert.equal((await w.check()).code,0);assert.equal(w.alerts.length,1);assert.equal(w.launches.length,1);
});
test('3111 BAD squash merge uses its first parent without a mainline flag',async t=>{
  const w=await world(t);w.squash=true;w.answer=result('BAD');assert.equal((await w.check()).code,0);
  assert.equal(w.calls.find(c=>c.file==='git'&&c.args.includes('revert')).args.includes('-m'),false);
});
test('3111 revert conflict retains failure and sends one alert without any push',async t=>{
  const w=await world(t);w.answer=result('BAD');w.conflict=true;assert.equal((await w.check()).code,1);
  assert.equal(w.audit().revert.state,'unknown');assert.equal(w.calls.filter(c=>c.file==='git'&&c.args[0]==='push').length,0);assert.equal(w.alerts.length,1);
  await w.check();assert.equal(w.alerts.length,1);assert.equal(w.calls.filter(c=>c.file==='git'&&c.args.includes('revert')).length,1);
});
test('3111 uncertain comment is reserved once across restart',async t=>{
  const w=await world(t);w.writeFailure=true;assert.equal((await w.check()).code,1);assert.equal(w.audit().comment.state,'unknown');w.writeFailure=false;
  assert.equal((await w.check()).code,1);assert.equal(comments(w).length,1);assert.equal(w.launches.length,1);
});
test('3111 saved verdict resumes a known unsent comment without another auditor',async t=>{
  const w=await world(t);assert.equal((await w.check()).code,0);const a=w.audit();delete a.comment;writeFileSync(w.file(),JSON.stringify(a));
  // Damage the authority to model a crash after reservation but before journaling.
  const identity=createHash('sha256').update(JSON.stringify([a.runId,a.pr,a.merge])).digest('hex');
  writeFileSync(join(w.concernFolder(),'..','records',`${identity}.json`),JSON.stringify(a));
  // The exclusive reservation proves that a crashed publication cannot be sent again.
  assert.equal((await w.check()).code,1);assert.equal(comments(w).length,1);assert.equal(w.audit().comment.state,'unknown');
});
test('3111 two same-kind CONCERNs open one process issue for three merges',async t=>{
  const w=await world(t);w.answer=result('CONCERN');w.run.pr.push({number:24,state:'merged'},{number:25,state:'merged'});writeFileSync(join(w.run.runDir,'status.json'),JSON.stringify(w.run));
  for(const pr of [23,24,25]) {w.session=randomUUID();const out=await w.check(pr);assert.equal(out.code,0,out.text);}
  const issues=w.calls.filter(c=>c.file==='gh'&&c.args.includes('POST')&&c.args.includes(`repos/${w.run.repo}/issues`));assert.equal(issues.length,1);
  const group=JSON.parse(readFileSync(join(w.concernFolder(),'missing-reproduction.json'),'utf8'));assert.equal(group.records.length,3);assert.equal(group.issue.state,'sent');
  assert.equal((await w.check(24)).code,0);assert.equal(w.launches.length,3);
});
test('3111 auditor native token usage enters the cost ledger once',async t=>{
  const w=await world(t);assert.equal((await w.check()).code,0);
  const date=new Date(w.clock).toISOString().slice(0,10).split('-'),folder=join(w.ports.env.HOME,'.codex','sessions',...date);mkdirSync(folder,{recursive:true});
  writeFileSync(join(folder,`rollout-audit-${w.session}.jsonl`),JSON.stringify({type:'event_msg',payload:{type:'token_count',info:{total_token_usage:{input_tokens:100,cached_input_tokens:20,output_tokens:30,reasoning_output_tokens:10,total_tokens:130}}}})+'\n');
  const capture=()=>updateRunCosts(w.run.runDir,r=>r,{...w.ports,now:()=>w.clock});
  const first=capture();assert.equal(first.cost.tokens.reduce((n,r)=>n+r.total,0),130);assert.equal(capture().cost.tokens.reduce((n,r)=>n+r.total,0),130);
  assert.ok(readdirSync(join(w.run.runDir,'audits')).includes('23.json'));
  // Complete native usage admits the next audit below the cap.
  seedWorkflowUsage(w);w.run.pr.push({number:24,state:'merged'});writeFileSync(join(w.run.runDir,'status.json'),JSON.stringify(w.run));
  w.config({auditTokenLimit:1000});w.nativeUsage=true;w.session=randomUUID();
  const out=await w.check(24);assert.equal(out.code,0,out.text);assert.equal(w.launches.length,2);
});


test('3111 repository custody serializes admission of distinct PR audits',async t=>{
  const w=await world(t);w.run.pr.push({number:24,state:'merged'});writeFileSync(join(w.run.runDir,'status.json'),JSON.stringify(w.run));
  w.config({auditTokenLimit:1000});let release,started;const ready=new Promise(r=>{started=r;});w.delay=()=>new Promise(r=>{release=r;started();});
  const first=w.check();await atLaunch(ready,first);assert.equal((await w.check(24)).code,1);assert.equal(w.launches.length,1);release();assert.equal((await first).code,0);
});
test('3111 saved merge mismatch refuses before a paid auditor',async t=>{
  const w=await world(t);w.run.pr[0].mergeCommit='c'.repeat(40);writeFileSync(join(w.run.runDir,'status.json'),JSON.stringify(w.run));
  assert.equal((await w.check()).code,1);assert.equal(w.launches.length,0);
});
test('3111 Claude audit captures usage from its private checkout, distinct from the builder',async t=>{
  const w=await world(t);w.agent='claude';w.run.agent='claude';w.run.configDir=join(w.ports.env.HOME,'.claude');writeFileSync(join(w.run.runDir,'status.json'),JSON.stringify(w.run));
  const out=await w.check();assert.equal(out.code,0,out.text);const a=w.audit();assert.notEqual(a.chat.root,w.run.root);
  assert.ok(w.launches[0].args.includes('--session-id'));assert.equal(w.launches[0].args.includes('--resume'),false);
  const folder=join(w.run.configDir,'projects',a.chat.root.replace(/[^a-zA-Z0-9]/g,'-'));mkdirSync(folder,{recursive:true});
  writeFileSync(join(folder,`${a.chat.session.id}.jsonl`),JSON.stringify({type:'assistant',message:{id:'audit-message',usage:{input_tokens:40,output_tokens:10}}})+'\n');
  const capture=()=>updateRunCosts(w.run.runDir,r=>r,{...w.ports,now:()=>w.clock});
  assert.equal(capture().cost.tokens.reduce((n,r)=>n+r.total,0),50);assert.equal(capture().cost.tokens.reduce((n,r)=>n+r.total,0),50);
});


test('3111 a process-issue sending reservation stays unknown after recovery',async t=>{
  const w=await world(t);w.answer=result('CONCERN');
  const folder=w.concernFolder();mkdirSync(folder,{recursive:true});
  writeFileSync(join(folder,'missing-reproduction.json'),JSON.stringify({repository:w.run.repo,kind:'missing-reproduction',records:[{identity:'other:22',pr:22,issue:16,summary:'Earlier concern'}],issue:{state:'sending',at:w.clock-1000}}));
  assert.equal((await w.check()).code,1);assert.equal(w.audit().concern.state,'unknown');
  const issues=w.calls.filter(c=>c.file==='gh'&&c.args.includes('POST')&&c.args.includes(`repos/${w.run.repo}/issues`));assert.equal(issues.length,0);
  assert.equal((await w.check()).code,1);assert.equal(w.launches.length,1);
});
test('3111 auditor keeps the saved model and removes caller session markers',async t=>{
  const w=await world(t);w.run.launchProfile={agent:'codex',model:'configured-model',configDir:w.run.configDir,herdrAgentName:'factory',codexThreads:null};writeFileSync(join(w.run.runDir,'status.json'),JSON.stringify(w.run));
  w.ports.env.CLAUDECODE='1';w.ports.env.CODEX_THREAD_ID='caller';w.ports.env.HERDR_PANE_ID='caller-pane';w.ports.env.PDD_AUTOPILOT_CONTEXT='caller';
  const out=await w.check();assert.equal(out.code,0,out.text);const launch=w.launches[0];assert.equal(launch.args[launch.args.indexOf('--model')+1],'configured-model');
  for(const key of ['CLAUDECODE','CODEX_THREAD_ID','HERDR_PANE_ID','PDD_AUTOPILOT_CONTEXT'])assert.equal(Object.hasOwn(launch.options.env,key),false);
  assert.equal(launch.options.env.CODEX_HOME,w.run.configDir);assert.equal(launch.options.env.PDD_INTERPRETER_QUEUE,w.ports.env.PDD_INTERPRETER_QUEUE);
});


test('3111 independent clones of one repository share audit admission custody',async t=>{
  const first=await world(t),second=await world(t);second.ports.stateDir=first.ports.stateDir;
  assert.notEqual(first.run.commonDir,second.run.commonDir);let release,started;const ready=new Promise(r=>{started=r;});first.delay=()=>new Promise(r=>{release=r;started();});
  const pending=first.check();await atLaunch(ready,pending);assert.equal((await second.check()).code,1);assert.equal(second.launches.length,0);release();assert.equal((await pending).code,0);
});


for(const kind of ['missing','malformed','saturated'])test(`3111 ${kind} cost index cannot admit an audit as zero cost`,async t=>{
  const w=await world(t);w.config({auditTokenLimit:1000});w.nativeUsage=true;const file=join(w.ports.stateDir,'runs.json');
  if(kind==='missing')unlinkSync(file);
  else if(kind==='malformed')writeFileSync(file,'{');
  else writeFileSync(file,JSON.stringify({version:1,runs:Array.from({length:200},(_,n)=>({number:n+1,repo:w.run.repo,runDir:join(w.base,`absent-${n}`,'pdd/runs/17')}))}));
  const out=await w.check();assert.equal(out.code,1,out.text);assert.equal(w.launches.length,0);
});


test('3111 a failed cost refresh cannot admit an audit from a stale complete snapshot',async t=>{
  const w=await world(t);w.config({auditTokenLimit:1000});w.nativeUsage=true;let refreshes=0;
  assert.ok(w.run.cost);w.run.cost.coverage=[];writeFileSync(join(w.run.runDir,'status.json'),JSON.stringify(w.run));
  w.refreshCosts=()=>{refreshes++;throw Error('synthetic attempt changed during refresh');};
  const out=await w.check();assert.equal(out.code,1,out.text);assert.equal(refreshes,1);assert.equal(w.launches.length,0);
});

function seedWorkflowUsage(w) {
  for(const chat of w.run.chats) {
    const agent=chat.agent??w.run.agent,id=chat.session.id;
    const config=chat.configDir??w.run.configDir??w.ports.env[agent==='codex'?'CODEX_HOME':'CLAUDE_CONFIG_DIR'];
    const folder=agent==='claude'
      ?join(config,'projects',(chat.root??w.run.root).replace(/[^a-zA-Z0-9]/g,'-'))
      :join(config,'sessions',...new Date(w.clock).toISOString().slice(0,10).split('-'));
    mkdirSync(folder,{recursive:true});
    const row=agent==='claude'?{type:'assistant',message:{id:'builder-usage',usage:{input_tokens:10,output_tokens:10}}}
      :{type:'event_msg',payload:{type:'token_count',info:{total_token_usage:{input_tokens:10,output_tokens:10,total_tokens:20}}}};
    writeFileSync(join(folder,agent==='claude'?`${id}.jsonl`:`rollout-builder-${id}.jsonl`),JSON.stringify(row)+'\n');
  }
}
function sameAttempt(first,second) {
  second.ports.stateDir=first.ports.stateDir;second.run.runId=first.run.runId;
  writeFileSync(join(second.run.runDir,'status.json'),JSON.stringify(second.run));
}
const effects=worlds=>{
  const calls=worlds.flatMap(w=>w.calls);
  return {auditors:worlds.reduce((n,w)=>n+w.launches.length,0),comments:worlds.reduce((n,w)=>n+comments(w).length,0),
    pushes:calls.filter(c=>c.file==='git'&&c.args[0]==='push').length,
    revertPRs:calls.filter(c=>c.file==='gh'&&c.args[0]==='pr'&&c.args[1]==='create').length,
    alerts:worlds.reduce((n,w)=>n+w.alerts.length,0),
    processIssues:calls.filter(c=>c.file==='gh'&&c.args.includes('POST')&&c.args.includes('repos/example/project/issues')).length};
};
for(const uncertain of ['none','comment','push','revert-pr','alert'])test(`3111 repair sequential clones retain every BAD effect after lock release, uncertain=${uncertain}`,async t=>{
  const first=await world(t),second=await world(t);sameAttempt(first,second);
  first.answer=result('BAD');second.answer=result('BAD');first.writeFailure=uncertain==='comment';first.uncertain=uncertain;
  const firstOut=await first.check(),secondOut=await second.check();
  assert.deepEqual(effects([first,second]),{auditors:1,comments:1,pushes:1,revertPRs:uncertain==='push'?0:1,alerts:1,processIssues:0});
  assert.equal(firstOut.code,uncertain==='none'?0:1);assert.equal(secondOut.code,uncertain==='none'?0:1);
  assert.equal(second.audit().result.verdict,'BAD');
});
test('3111 repair sequential clones retain an uncertain auditor launch',async t=>{
  const first=await world(t),second=await world(t);sameAttempt(first,second);first.raw='invalid';
  const firstOut=await first.check(),secondOut=await second.check();
  assert.deepEqual(effects([first,second]),{auditors:1,comments:0,pushes:0,revertPRs:0,alerts:0,processIssues:0});
  assert.equal(firstOut.code,1);assert.equal(secondOut.code,1);
});
for(const uncertain of [false,true])test(`3111 repair sequential clones retain process issue custody, uncertain=${uncertain}`,async t=>{
  const first=await world(t),second=await world(t);sameAttempt(first,second);
  for(const w of [first,second]) {w.answer=result('CONCERN');w.run.pr.push({number:24,state:'merged'});writeFileSync(join(w.run.runDir,'status.json'),JSON.stringify(w.run));}
  assert.equal((await first.check()).code,0);first.session=randomUUID();first.writeFailure=uncertain;
  assert.equal((await first.check(24)).code,uncertain?1:0);
  const secondOut=await second.check(),nextOut=await second.check(24);
  assert.deepEqual(effects([first,second]),{auditors:2,comments:2,pushes:0,revertPRs:0,alerts:0,processIssues:1});
  assert.equal(secondOut.code,0);assert.equal(nextOut.code,uncertain?1:0);
});
for(const kind of ['invalid-schema','wrong-identity','omitted','invalid-index-row'])test(`3111 repair indexed ${kind} record holds native cost admission before launch`,async t=>{
  const w=await world(t);w.config({auditTokenLimit:1000});w.nativeUsage=true;seedWorkflowUsage(w);
  const dir=join(w.run.commonDir,'pdd','runs',kind==='omitted'?'outside-discovery':'18');mkdirSync(dir,{recursive:true});
  const file=join(dir,'status.json');
  if(kind==='invalid-json')writeFileSync(file,'{');
  else if(kind==='unreadable')mkdirSync(file);
  else if(kind==='invalid-schema')writeFileSync(file,JSON.stringify({repo:w.run.repo,number:18}));
  else if(kind!=='missing')writeFileSync(file,JSON.stringify({...w.run,number:kind==='wrong-identity'?19:18,runDir:dir}));
  const indexPath=join(w.ports.stateDir,'runs.json'),index=JSON.parse(readFileSync(indexPath,'utf8'));
  index.runs.push({...(kind==='invalid-index-row'?{}:{repo:w.run.repo}),number:18,runDir:dir});writeFileSync(indexPath,JSON.stringify(index));
  assert.equal((await w.check()).code,1);assert.equal(w.launches.length,0);
});
for(const kind of ['damaged','invalid-schema','unreadable-file','unreadable-folder'])test(`3111 repair earlier ${kind} audit holds CLI before any additional launch`,async t=>{
  const w=await world(t);assert.equal((await w.check()).code,0);seedWorkflowUsage(w);
  if(kind==='damaged')writeFileSync(w.file(),'{');
  else if(kind==='invalid-schema')writeFileSync(w.file(),JSON.stringify({runId:null}));
  else if(kind==='unreadable-file') {unlinkSync(w.file());mkdirSync(w.file());}
  else w.fs={...nativeFs,readdirSync(path,...args) {if(path===join(w.run.runDir,'audits'))throw Object.assign(Error('denied'),{code:'EACCES'});return nativeFs.readdirSync(path,...args);}};
  w.run.pr.push({number:24,state:'merged'});writeFileSync(join(w.run.runDir,'status.json'),JSON.stringify(w.run));
  const captured=captureCosts(null,w.run,{...w.ports,fs:w.fs??nativeFs});
  w.config({auditTokenLimit:1000});w.nativeUsage=true;w.session=randomUUID();
  const out=await w.check(24);assert.equal(w.launches.length,1);assert.equal(out.code,1);
  assert.ok(captured.coverage.includes('audit-session-unavailable'));
});
