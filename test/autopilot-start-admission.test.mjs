import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {createHash} from 'node:crypto';
import {fixture} from './helpers/workflow-runner-fixture.mjs';
import {createDependencyReadPorts} from '../src/issue-dependencies-github.mjs';
import {checkDependencyStart} from '../src/issue-dependencies-intake.mjs';
import {parkingSummary} from '../src/autopilot-parking.mjs';

async function setup(t, {working = 1, maxParked} = {}) {
  const f = await fixture(t), repository = 'example/project', issue = `https://github.com/${repository}/issues/99`;
  const coordinator = {repository, coordinatorId: 'c', machine: 'm', activation: 'a', runs: 10, claim: {commentId: '1', labelEventId: '2'}};
  const stateRoot = join(f.state, 'autopilot'); mkdirSync(stateRoot, {recursive: true});
  const stateFile = join(stateRoot, `${createHash('sha256').update(f.source).digest('hex').slice(0,20)}.json`);
  writeFileSync(stateFile, JSON.stringify({repo: repository, cwd: f.source, coordinatorId: 'c', enabled: true, activatedAt: 'a', runs: 10}));
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', ...(maxParked ? {parking: {maxParked}} : {})}}));
  const commonDir = f.git(f.source, 'rev-parse', '--git-common-dir'), runs = [];
  for (let i = 1; i <= 8 + working; i++) {
    const runDir = join(f.source, commonDir, 'pdd', 'runs', String(i)); mkdirSync(runDir, {recursive: true});
    const parked = i > 6 && i <= 8;
    const run = {v: 1, number: i, repo: repository, runId: `run-${i}`, runDir, root: f.source,
      state: i <= 6 ? 'stuck' : parked ? 'paused' : 'running', areas: [], chats: [],
      ...(parked ? {parking: {phase: 'parked', blocker: {kind: 'person'}}, layout: {phase: 'closed'}} : {})};
    writeFileSync(join(runDir, 'status.json'), JSON.stringify(run)); runs.push(run);
  }
  const readPorts = {...f.ports, autopilotStateRoot: stateRoot,
    readSuiteProgress: () => ({state: 'idle'}),
    readInterpreterProgress: () => ({state: 'idle'})};
  const native = createDependencyReadPorts({cwd: f.source}, readPorts);
  const owners = JSON.parse((await native.owners.read({repository, issues: []})).json);
  const settings = await native.settings.read({cwd: f.source, repository});
  const revision = 'a'.repeat(64);
  const ports = {...readPorts, settings: {read: async () => settings},
    owners: {read: async () => ({json: JSON.stringify({...owners, localOwner: 'c', claims: [{issue, active: true, owner: 'c', coordinatorId: 'c', machine: 'm', ...coordinator.claim}]})})},
    snapshots: {read: async () => ({snapshot: {repository, complete: true,
      issues: [{key: issue, nodeId: '99', title: 'Independent', revision, state: 'open', authority: 'trusted', assignees: [], conditions: [], execution: 'idle', holds: []}],
      reviews: [{id: 'r', issue, authority: 'trusted', intact: true, outcome: 'complete', analysis: 'Independent work', base: [], continuation: '', inputs: [{key: issue, revision}], candidates: [{key: issue, revision}], dependencies: [], questions: [], effects: 'none'}], edges: [], impacts: [], inputs: []}})}};
  return {f, repository, issue, coordinator, ports, owners, runs, settings};
}

test('#3102 six stuck, two parked and one working run backfill below ten', async t => {
  const f = await setup(t);
  assert.equal(parkingSummary(f.runs, 10).working, 1);
  assert.deepEqual(await checkDependencyStart(f, f.ports), {allowed: true, reason: 'ok'}, 'idle backlog must not consume working capacity');
  // Admit three working starts. All remain below ten working slots. The old
  // admission wrongly adds the six stuck rows and refuses the fourth start.
  for (let i = 10; i <= 12; i++) f.owners.runs.push({issue: `https://github.com/${f.repository}/issues/${i}`, runId: `run-${i}`, state: 'running'});
  assert.deepEqual(await checkDependencyStart(f, f.ports), {allowed: true, reason: 'ok'}, 'stuck runs must not block backfill below the working limit');
  assert.equal(f.owners.runs.filter(run => run.working).length, 1, 'native count must match the initial status');
});

test('#3102 stuck and parked backlog uses the configured parked limit', async t => {
  const f = await setup(t, {maxParked: 8});
  assert.deepEqual(await checkDependencyStart(f, f.ports), {allowed: false, reason: 'parked'}, 'backlog saturation must name its own limit');
});

test('#3102 default parked limit is twice the working limit', async t => {
  const f = await setup(t);
  f.settings.runs = f.coordinator.runs = 4;
  assert.deepEqual(await checkDependencyStart(f, f.ports), {allowed: false, reason: 'parked'}, 'default backlog limit must apply independently');
});

for (const observation of ['done','absent']) test(`3132 ten working slots include closing ${observation} custody in native admission`, async t => {
  const f = await setup(t, {working:8});
  assert.equal((await f.f.run()).exitCode, 0);
  const run = f.f.record(), chat = run.chats.at(-1);
  run.state = 'waiting'; run.parking = {at:f.f.clock,phase:'closing',blocker:{kind:'person'}};
  if (observation === 'done') f.f.herdr.paneOf(chat).agent.agent_status = 'done';
  else {chat.state = 'ended'; await f.f.herdr.herdr(['workspace','close',run.layout.workspaceId]);}
  writeFileSync(join(run.runDir,'status.json'), JSON.stringify(run));
  const extra = {...f.runs.at(-1),number:18,runId:'run-18',runDir:join(run.commonDir,'pdd/runs/18')};
  mkdirSync(extra.runDir,{recursive:true}); writeFileSync(join(extra.runDir,'status.json'),JSON.stringify(extra));
  const rows = [...f.runs,run,extra];
  assert.equal(parkingSummary(rows,10).working,10);
  const native = createDependencyReadPorts({cwd:f.f.source},{...f.ports,owners:undefined});
  const owners = JSON.parse((await native.owners.read({repository:f.repository,issues:[]})).json);
  assert.equal(owners.runs.filter(r=>r.working).length,10);
  f.owners.runs = owners.runs;
  assert.deepEqual(await checkDependencyStart(f,f.ports),{allowed:false,reason:'runs'});
});
