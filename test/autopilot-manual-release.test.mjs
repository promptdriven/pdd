import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {tickAutopilot} from '../src/autopilot-launcher.mjs';

test('manual hold waits for check custody and retains the run', async t => {
  const f = await fixture(t, {agent:'claude', name:'small-change'});
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.automaticOrigin = {repository:run.repo, coordinatorId:'owner', machine:'machine', claim:{commentId:'11', labelEventId:'12'}};
  writeFileSync(join(run.runDir,'status.json'), JSON.stringify(run));
  f.ports.owners = {read:async input => ({json:JSON.stringify({localOwner:'owner', claims:input.issues.map(issue => ({issue, active:true, owner:'owner', coordinatorId:'owner', machine:'machine', commentId:'11', labelEventId:'12'}))})})};
  writeFileSync(join(f.source,'pdd.json'), JSON.stringify({autopilot:{mode:'auto',trust:[]}}));
  const stateFile = join(f.state,'launcher.json');
  writeFileSync(stateFile, JSON.stringify({enabled:true,defaultBranch:'main',baseBranch:'main',stateFile,cwd:f.source,repo:run.repo,packageRoot,runs:1,coordinatorId:'owner',machine:'machine',activatedAt:1,agent:{id:'claude',kind:'claude',command:'claude'},environment:f.ports.env,retryAt:f.clock+86400000}));
  let busy = true, released = 0;
  const ports = {...healthyMachine,...f.ports,sendDigest:async()=>({exitCode:0}),checkCapacityPorts:isolatedCheckCapacity(f.base),
    run:async(file,args,options)=>({code:0,...await f.ports.execFile(file,args,options)}),warn:()=>{},
    readManualHold:async()=>({known:true,held:true}), readSuiteProgress:()=>({state:busy?'running':'finished'}),
    releaseParkedClaim:async()=>{released++;return {state:'released'};}};
  await tickAutopilot(stateFile,ports);
  assert.equal(released,0); assert.equal(f.record().runId,run.runId); assert.ok(existsSync(run.root));
  busy=false; await tickAutopilot(stateFile,ports);
  assert.equal(released,0); assert.equal(f.record().parking,undefined);
  for (const pane of f.herdr.panes) if (pane.agent) pane.agent.agent_status = 'unknown';
  await tickAutopilot(stateFile,ports); assert.equal(released,0);
  f.herdr.idle(); await tickAutopilot(stateFile,ports);
  assert.equal(released,1); assert.equal(f.record().state,'cancelled');
  assert.equal(f.record().branch,run.branch); assert.deepEqual(f.record().done,run.done); assert.ok(existsSync(run.root));
  assert.deepEqual(JSON.parse(readFileSync(stateFile)).manualIssues,[17]);
});

