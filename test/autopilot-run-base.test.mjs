import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
import { automaticFixture } from './helpers/autopilot-run-base-fixture.mjs';
import { startRun } from '../src/workflow-runner.mjs';

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
