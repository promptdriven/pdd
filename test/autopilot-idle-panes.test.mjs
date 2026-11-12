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

async function setup(t, stateName) {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  f.herdr.idle(); // A stopped worker has completed its native turn.
  const run = f.record();
  run.automaticOrigin = {repository: run.repo, coordinatorId: 'idle-owner', machine: 'idle-machine', claim: {commentId: '11', labelEventId: '12'}};
  save(run);
  f.ports.owners = {read: async ({issues}) => ({json: JSON.stringify({localOwner: 'idle-owner',
    claims: issues.map(issue => ({issue, active: true, owner: 'idle-owner', coordinatorId: 'idle-owner',
      machine: 'idle-machine', commentId: '11', labelEventId: '12'}))})})};
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: []}}));
  f.ports.autopilotStateRoot = f.state;
  const stateFile = join(f.state, stateName ?? createHash('sha256').update(f.source).digest('hex').slice(0, 20) + '.json');
  writeFileSync(stateFile, JSON.stringify({enabled: true, defaultBranch: 'main', baseBranch: 'main', stateFile,
    cwd: f.source, repo: run.repo, packageRoot, runs: 1, coordinatorId: 'idle-owner', machine: 'idle-machine', activatedAt: 1,
    agent: {id: 'claude', kind: 'claude', command: 'claude'}, environment: f.ports.env, retryAt: f.clock + 86400000}));
  const ports = {...healthyMachine, ...f.ports, sendDigest: async () => ({exitCode: 0}), sendAlert: async () => ({exitCode: 0}),
    checkCapacityPorts: isolatedCheckCapacity(f.base), run: async (file, args, options) => ({code: 0, ...await f.ports.execFile(file, args, options)}), warn: () => {}};
  f.herdr.calls.length = 0;
  return {f, run, ports, stateFile, tick: () => tickAutopilot(stateFile, ports)};
}

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
  f.herdr.idle();
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

for (const guard of ['manual']) test(`3110 idle cleanup keeps ${guard} custody`, async t => {
  const {f, run, ports, tick} = await setup(t);
  run.state = 'stuck'; run.chatIdleLimit = {at: f.clock - 120_000}; run.progressAt = f.clock - 120_000;
  if (guard === 'manual') delete run.automaticOrigin;
  if (guard === 'foreign') run.automaticOrigin.coordinatorId = 'another-owner';
  if (guard === 'unowned-workspace') run.layout.createdWorkspaceId = null;
  if (guard === 'busy-agent') f.herdr.paneOf(run.chats.at(-1)).agent.agent_status = 'working';
  if (guard === 'session') {
    delete run.chats.at(-1).session;
    f.herdr.paneOf(run.chats.at(-1)).agent = null;
    f.herdr.sessions = []; // No live or saved native proof for the current chat.
  }
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

function retryPorts(f) {
  return {...f.ports, owners: {read: async () => ({json: JSON.stringify({localOwner: 'idle-owner', runsKnown: true, runs: [],
    claims: [{issue: f.record().issue.url, active: true, owner: 'idle-owner', coordinatorId: 'idle-owner', machine: 'idle-machine', commentId: '11', labelEventId: '12'}]})})}};
}

