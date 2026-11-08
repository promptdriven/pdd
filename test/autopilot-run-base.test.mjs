import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { execFile as callback } from 'node:child_process';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
import { startRun } from '../src/workflow-runner.mjs';

async function automaticFixture(t, base) {
  const f=await fixture(t,{name:'bug',agent:'codex'});
  const origin={repository:'example/project',coordinatorId:'coordinator-a',machine:'machine-a',claim:{commentId:'11',labelEventId:'12'}};
  const envelope={version:'pdd.autopilot-coordinator.v1',repository:origin.repository,coordinatorId:origin.coordinatorId,machine:origin.machine,activation:'activation'};
  const stateRoot=join(f.state,'autopilot');mkdirSync(stateRoot,{recursive:true});
  writeFileSync(join(stateRoot,`${createHash('sha256').update(f.source).digest('hex').slice(0,20)}.json`),JSON.stringify({enabled:true,repo:origin.repository,cwd:f.source,coordinatorId:origin.coordinatorId,machine:origin.machine,activatedAt:'activation',startAction:{command:'pdd autopilot start',repository:origin.repository,mode:'auto'},paneId:'coordinator-pane',ownerLaunch:{paneId:'coordinator-pane',coordinator:envelope}}));
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',...(base===undefined?{}:{base})}}));
  writeFileSync(join(f.source,'CONTRIBUTING.md'),'Open pull requests against alpha.');
  f.git(f.source,'add','.');f.git(f.source,'commit','-qm','Synthetic configuration and conflicting docs');
  for(const name of ['main','integration/topic','alpha']) f.git(f.source,'update-ref',`refs/remotes/origin/${name}`,f.git(f.source,'rev-parse','HEAD'));
  const fixturePath=join(f.base,'reader.json'),logPath=join(f.base,'gh.log');
  writeFileSync(fixturePath,JSON.stringify({labels:['pdd:working'],events:[{id:12,event:'labeled',label:{name:'pdd:working'},actor:{login:'example'}}],comments:[{id:11,user:{login:'example'},body:JSON.stringify({repository:origin.repository,coordinatorId:origin.coordinatorId,machine:origin.machine,labelEventId:'12'})}]}));
  const exec=promisify(callback), original=f.ports.execFile;
  const ports={...f.ports,env:{...f.ports.env,HERDR_SOCKET_PATH:'/fixture/sessions/pdd-autopilot/socket',HERDR_PANE_ID:'coordinator-pane'},autopilotStateRoot:stateRoot,checkDependencyStart:async()=>({allowed:true,reason:'ok'}),execFile:(file,args,opts)=>file==='gh'&&args[0]==='api'&&args[1]==='--include'?exec(process.execPath,[join(packageRoot,'test/helpers/continuation-fake-gh.mjs'),...args],{...opts,env:{...process.env,READER_FIXTURE_FILE:fixturePath,READER_GH_LOG:logPath}}):original(file,args,opts)};
  f.begin=(extra={})=>startRun({name:'bug',issue:'17',agent:'codex',cwd:f.source,packageRoot,...extra},ports);
  f.automaticPorts=ports;
  return f;
}
for(const configured of [undefined,'integration/topic'])test(`3071 automatic start saves ${configured??'default'} despite docs`,async t=>{
  const f=await automaticFixture(t,configured),out=await f.begin();assert.equal(out.exitCode,0,out.message);
  const run=f.record(), expected=configured??'main';assert.equal(run.baseBranch,expected);
  assert.equal(run.baseSha,f.git(f.source,'rev-parse',`refs/remotes/origin/${expected}`));
  const brief=readFileSync(run.chats[0].messageFile,'utf8');assert.ok(brief.includes(`Saved base: ${expected}`));assert.match(brief,/documents/);
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',base:'alpha'}}));
  assert.equal(f.record().baseBranch,expected);assert.equal(f.record().baseSha,run.baseSha);
});
test('3071 automatic start refuses a document-selected conflicting override',async t=>{
  const f=await automaticFixture(t),out=await f.begin({base:'alpha'});
  assert.equal(out.exitCode,1,out.message);assert.match(out.message,/main/);assert.match(out.message,/alpha/);
  assert.throws(()=>f.record());assert.equal(f.herdr.calls.some(args=>args[0]==='pane'&&args[1]==='run'),false);
});
for(const base of ['',null,'HEAD','refs/heads/main','main~1','--help'])test(`3071 invalid configured base ${JSON.stringify(base)} refuses allocation`,async t=>{
  const f=await automaticFixture(t,base),out=await f.begin();assert.equal(out.exitCode,1,out.message);assert.throws(()=>f.record());
});
test('3071 automatic default fetch failure cannot use stale remote-tracking ref',async t=>{
  const f=await automaticFixture(t), original=f.automaticPorts.execFile;
  f.automaticPorts.execFile=async(file,args,opts)=>file==='git'&&args[0]==='fetch'?{code:1,stdout:'',stderr:'synthetic fetch failure'}:original(file,args,opts);
  const out=await f.begin();assert.equal(out.exitCode,1,out.message);assert.throws(()=>f.record());
});
test('3071 manual workflow keeps explicit base selection',async t=>{
  const f=await fixture(t);f.git(f.source,'update-ref','refs/remotes/origin/alpha',f.git(f.source,'rev-parse','HEAD'));
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',base:'main'}}));
  const out=await startRun({name:'small-change',issue:'17',agent:'claude',cwd:f.source,packageRoot,base:'alpha'},f.ports);
  assert.equal(out.exitCode,0,out.message);assert.equal(f.record().baseBranch,'alpha');
});
