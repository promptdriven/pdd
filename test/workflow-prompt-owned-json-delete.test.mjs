import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {approveRun} from '../src/workflow-runner.mjs';
import {prepared} from './helpers/workflow-prompt-reentry-fixture.mjs';

test('2897 publication: deleted ordinary owned JSON does not block the retained anchor',async t=>{
  const f=await prepared(t,{code:false,realRemote:true});
  assert.equal((await approveRun({ref:'17',cwd:f.source,said:'Publish PR 1.'},f.ports)).exitCode,0);
  const before=f.record(),pr1=before.pr[0];
  writeFileSync(join(before.root,'metadata.json'),JSON.stringify({theme:'dark'}));
  await f.done('check');
  assert.ok(f.record().pr[0].sourcePaths.includes('metadata.json'));
  f.git(before.root,'rm','metadata.json'); f.git(before.root,'commit','-qm','Remove ordinary metadata');
  await f.ports.execFile('git',['push','origin',`HEAD:refs/heads/${pr1.branch}`],{cwd:before.root,encoding:'utf8'});
  const peer=join(f.base,'merge-peer');
  f.git(f.base,'clone','-q',f.remote,peer); f.git(peer,'config','user.name','Peer'); f.git(peer,'config','user.email','peer@example.invalid');
  f.git(peer,'switch','-q','main'); f.git(peer,'merge','--no-ff','--no-edit',`origin/${pr1.branch}`); f.git(peer,'push','-q','origin','main');
  // Keep the PR open in the fake until publication records the latest anchor.
  await f.done('check');
  assert.equal(f.record().replayBaseline.outcome,undefined,'ordinary-json-not-a-vector');
  assert.deepEqual(f.record().replayBaseline.vectors,before.replayBaseline.vectors,'owned-anchor-retained');
});
