import './helpers/test-home.mjs';
import test from 'node:test';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
import {existsSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {tickAutopilot} from '../src/autopilot-launcher.mjs';
import {startRun, runStatus, openRun, changeRun} from '../src/workflow-runner.mjs';

const save = run => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
const read = run => JSON.parse(readFileSync(join(run.runDir, 'status.json')));
const closes = f => f.herdr.calls.filter(a => ['tab', 'workspace'].includes(a[0]) && a[1] === 'close');
const launches = f => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run');

async function setup(t) {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  const run = f.record();
  run.automaticOrigin = {repository: run.repo, coordinatorId: 'idle-owner', machine: 'idle-machine', claim: {commentId: '11', labelEventId: '12'}};
  save(run);
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: []}}));
  f.ports.autopilotStateRoot = f.state;
  const stateFile = join(f.state, createHash('sha256').update(f.source).digest('hex').slice(0, 20) + '.json');
  writeFileSync(stateFile, JSON.stringify({enabled: true, defaultBranch: 'main', baseBranch: 'main', stateFile,
    cwd: f.source, repo: run.repo, packageRoot, runs: 1, coordinatorId: 'idle-owner', machine: 'idle-machine', activatedAt: 1,
    agent: {id: 'claude', kind: 'claude', command: 'claude'}, environment: f.ports.env, retryAt: f.clock + 86400000}));
  const ports = {...healthyMachine, ...f.ports, sendDigest: async () => ({exitCode: 0}), sendAlert: async () => ({exitCode: 0}),
    checkCapacityPorts: isolatedCheckCapacity(f.base), run: async (file, args, options) => ({code: 0, ...await f.ports.execFile(file, args, options)}), warn: () => {}};
  f.herdr.calls.length = 0;
  return {f, run, ports, tick: () => tickAutopilot(stateFile, ports)};
}

for (const kind of ['idle-ceiling', 'resume-ceiling', 'pause']) test(`3110 ${kind} releases panes after grace and retains saved custody`, async t => {
  const {f, run, tick} = await setup(t);
  run.state = kind === 'pause' ? 'paused' : 'stuck';
  if (kind !== 'pause') {
    run.parkReason = 'Controlled recovery ceiling';
    run[kind === 'idle-ceiling' ? 'chatIdleLimit' : 'chatResumeLimit'] = {at: f.clock, area: run.chats.at(-1).area};
  }
  save(run);
  await tick();
  assert.equal(closes(f).length, 0);
  f.tick(59_999); await tick(); assert.equal(closes(f).length, 0);
  f.tick(1); await tick();
  const parked = f.record();
  assert.equal(parked.parking?.phase, 'parked', '3110 idle stop must release its native panes');
  assert.equal(f.herdr.panes.some(p => p.workspace_id === run.layout.workspaceId), false);
  for (const key of ['state', 'root', 'runDir', 'branch', 'automaticOrigin', 'gate', 'question', 'done', 'parkReason', 'chatIdleLimit', 'chatResumeLimit'])
    assert.deepEqual(parked[key], run[key]);
  assert.deepEqual(parked.chats.at(-1).session, run.chats.at(-1).session);
  assert.ok(existsSync(run.root)); assert.ok(existsSync(run.runDir));
  f.herdr.calls.length = 0; await tick();
  assert.equal(closes(f).length, 0); assert.equal(launches(f).length, 0);
  const result = await openRun({ref: '17', cwd: f.source, packageRoot}, f.ports);
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(f.record().chats.at(-1).session.id, run.chats.at(-1).session.id);
  assert.notEqual(f.record().chats.at(-1).paneId, run.chats.at(-1).paneId);
});

for (const wait of ['gate', 'question']) test(`3110 running record with ${wait} parks and resumes its saved session`, async t => {
  const {f, run, tick} = await setup(t);
  run.state = 'running';
  if (wait === 'gate') run.gate = {kind: 'approve', area: run.areas[run.area].name, at: f.clock};
  else run.question = {at: f.clock, text: 'Select the next option'};
  save(run); await tick();
  const parked = f.record();
  assert.equal(parked.parking?.phase, 'parked', '3110 person wait must release its native panes');
  assert.equal(parked.parking.blocker.kind, 'person');
  assert.deepEqual(parked.gate, run.gate); assert.deepEqual(parked.question, run.question);
  if (wait === 'question') {
    const result = await changeRun({ref: '17', cwd: f.source, packageRoot, text: 'Use the selected option'}, f.ports);
    assert.equal(result.exitCode, 0, result.message);
    assert.equal(launches(f).length, 0, 'a parked reply waits for admission');
    await tick();
    assert.equal(f.record().parking, undefined);
    assert.equal(launches(f).length, 1);
    assert.equal(f.record().chats.at(-1).session.id, run.chats.at(-1).session.id);
    await tick(); assert.equal(launches(f).length, 1);
  }
});

async function nextRun(f, number) {
  const exec = f.ports.execFile;
  f.ports.execFile = async (file, args, options) => file === 'gh' && args[0] === 'api' && args[1] === `repos/example/project/issues/${number}`
    ? {stdout: JSON.stringify({number, html_url: `https://github.com/example/project/issues/${number}`, title: 'Independent work', body: 'Controlled work'})}
    : exec(file, args, options);
  return startRun({name: 'small-change', issue: String(number), agent: 'claude', cwd: f.source, packageRoot}, f.ports);
}

test('3110 pane admission parks oldest idle chat before refusing new work', async t => {
  const {f, run} = await setup(t);
  assert.equal((await nextRun(f, 18)).exitCode, 0);
  const second = JSON.parse(readFileSync(join(run.commonDir, 'pdd/runs/18/status.json')));
  second.automaticOrigin = run.automaticOrigin;
  second.state = 'stuck'; second.chatResumeLimit = {area: second.chats.at(-1).area, at: f.clock};
  second.progressAt = f.clock; save(second);
  run.state = 'stuck'; run.chatIdleLimit = {area: run.chats.at(-1).area, at: f.clock - 1};
  run.progressAt = f.clock - 1; save(run);
  f.ports.env.PDD_HERDR_PANE_BUDGET = String(f.herdr.panes.length + 1);
  f.herdr.calls.length = 0;
  const result = await nextRun(f, 19);
  assert.equal(result.exitCode, 0, `3110 admission must reclaim idle panes: ${result.message}`);
  assert.equal(f.record().parking?.phase, 'parked');
  assert.equal(read(second).parking, undefined, 'stop reclaiming once admission fits');
  const closedWorkspaces = closes(f).filter(a => a[0] === 'workspace').map(a => a[2]);
  assert.deepEqual(closedWorkspaces, [run.layout.workspaceId]);
  const create = f.herdr.calls.findIndex(a => a[0] === 'worktree' && a[1] === 'open');
  const close = f.herdr.calls.findIndex(a => a[0] === 'workspace' && a[1] === 'close');
  assert.ok(close >= 0 && create > close);
});

for (const guard of ['manual', 'foreign', 'unowned-workspace', 'busy-check', 'unknown-check', 'session']) test(`3110 idle cleanup keeps ${guard} custody`, async t => {
  const {f, run, ports, tick} = await setup(t);
  run.state = 'stuck'; run.chatIdleLimit = {at: f.clock - 120_000}; run.progressAt = f.clock - 120_000;
  if (guard === 'manual') delete run.automaticOrigin;
  if (guard === 'foreign') run.automaticOrigin.coordinatorId = 'another-owner';
  if (guard === 'unowned-workspace') delete run.layout.createdWorkspaceId;
  if (guard === 'session') delete run.chats.at(-1).session;
  if (guard === 'busy-check' || guard === 'unknown-check') ports.readSuiteProgress = () => ({state: guard === 'busy-check' ? 'running' : 'unavailable'});
  save(run); await tick();
  assert.equal(closes(f).length, 0, '3110 uncertain or unowned resources must stay open');
  assert.notEqual(f.record().parking?.phase, 'parked');
});

for (const authority of ['foreign', 'missing']) test(`3110 admission preserves ${authority} coordinator authority`, async t => {
  const {f, run} = await setup(t);
  run.state = 'stuck'; run.progressAt = f.clock - 120_000;
  run.chatIdleLimit = {at: run.progressAt};
  if (authority === 'foreign') run.automaticOrigin.coordinatorId = 'foreign-owner';
  else f.ports.autopilotStateRoot = join(f.base, 'missing-state');
  save(run);
  f.ports.env.PDD_HERDR_PANE_BUDGET = String(f.herdr.panes.length);
  f.herdr.calls.length = 0;
  const result = await nextRun(f, 18);
  assert.equal(result.exitCode, 1);
  assert.equal(closes(f).length, 0);
  assert.equal(f.record().parking, undefined);
});

for (const boundary of ['check-probe', 'close-checkpoint', 'final-native-read']) test(`3110 progress at ${boundary} cancels stale cleanup`, async t => {
  const {f, run, ports, tick} = await setup(t);
  run.state = 'stuck'; run.progressAt = f.clock - 120_000;
  run.parkReason = 'Controlled unclassified stop'; save(run);
  let changed = false;
  const advance = () => {
    if (changed) return;
    changed = true;
    const latest = f.record(); latest.progressAt = f.clock;
    latest.chatIdleLimit = {at: f.clock}; latest.updatedAt = f.clock + 1; save(latest);
  };
  if (boundary === 'check-probe') ports.readSuiteProgress = () => {advance(); return null;};
  else {
    const herdr = ports.herdr;
    let screenRead = false;
    ports.herdr = async args => {
      if (boundary === 'close-checkpoint' && args[0] === 'pane' && args[1] === 'read') advance();
      if (boundary === 'final-native-read' && screenRead && args[0] === 'agent' && args[1] === 'get') advance();
      if (args[0] === 'pane' && args[1] === 'read') screenRead = true;
      return herdr(args);
    };
  }
  await tick();
  assert.equal(changed, true);
  assert.equal(closes(f).length, 0, '3110 progress must invalidate the selected idle stop');
  assert.notEqual(f.record().parking?.phase, 'parked');
  assert.equal(f.record().progressAt, f.clock);
});


for (const kind of ['idle', 'resume']) test(`3110 explicit retry resumes a parked ${kind} ceiling once`, async t => {
  const {f, run, ports, tick} = await setup(t);
  Object.assign(ports, retryPorts(f));
  run.state = 'stuck'; run.progressAt = f.clock - 120_000;
  run[kind === 'idle' ? 'chatIdleLimit' : 'chatResumeLimit'] = {at: run.progressAt, area: run.chats.at(-1).area};
  save(run); await tick();
  assert.equal(f.record().parking?.phase, 'parked');
  const result = await changeRun({ref: '17', cwd: f.source, packageRoot, text: 'Please retry the failed step'}, retryPorts(f));
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(launches(f).length, 0);
  await tick();
  const resumed = f.record();
  assert.equal(resumed.parking, undefined, '3110 an explicit retry must clear the idle park');
  assert.equal(resumed.state, 'running');
  assert.equal(resumed.chats.at(-1).session.id, run.chats.at(-1).session.id);
  assert.notEqual(resumed.chats.at(-1).paneId, run.chats.at(-1).paneId);
  assert.deepEqual(resumed.done, run.done);
  assert.equal(launches(f).length, 1);
  const deliveries = f.herdr.calls.filter(a => a[0] === 'agent' && a[1] === 'prompt');
  assert.equal(deliveries.length, 1);
  await tick();
  assert.equal(launches(f).length, 1);
  assert.equal(f.herdr.calls.filter(a => a[0] === 'agent' && a[1] === 'prompt').length, 1);
});


function retryPorts(f) {
  return {...f.ports, owners: {read: async () => ({json: JSON.stringify({localOwner: 'idle-owner', runsKnown: true, runs: [],
    claims: [{issue: f.record().issue.url, active: true, owner: 'idle-owner', coordinatorId: 'idle-owner', machine: 'idle-machine', commentId: '11', labelEventId: '12'}]})})}};
}

for (const timing of ['queued', 'before-delivery']) test(`3110 parked retry rechecks repair limit ${timing}`, async t => {
  const {f, run, ports, tick} = await setup(t);
  Object.assign(ports, retryPorts(f));
  run.state = 'stuck'; run.progressAt = f.clock - 120_000;
  run.chatIdleLimit = {at: run.progressAt, area: run.chats.at(-1).area}; save(run);
  await tick(); assert.equal(f.record().parking?.phase, 'parked');
  const result = await changeRun({ref: '17', cwd: f.source, packageRoot, text: 'Please retry the failed step'}, retryPorts(f));
  assert.equal(result.exitCode, 0, result.message);
  let changed = false;
  const setLimit = () => {if (changed) return; changed = true; const current = f.record(); current.repairLimit = {at: f.clock, count: 2}; save(current);};
  if (timing === 'queued') setLimit();
  else {
    const herdr = ports.herdr;
    ports.herdr = async args => {if (launches(f).length && args[0] === 'agent' && args[1] === 'get') setLimit(); return herdr(args);};
  }
  await tick();
  assert.equal(changed, true);
  assert.equal(f.herdr.calls.filter(a => a[0] === 'agent' && a[1] === 'prompt').length, 0, '3110 queued retry must preserve the repair ceiling');
  if (timing === 'queued') assert.equal(launches(f).length, 0);
  assert.ok(f.record().repairLimit);
  assert.ok(f.record().parking);
});
