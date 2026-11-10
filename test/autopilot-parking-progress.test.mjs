import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {parkBlockedRun, runStatus} from '../src/workflow-runner.mjs';
import {runAutopilotLauncher} from '../src/autopilot-launcher.mjs';
import {parkingSummary, parkingWords, reconcileParking} from '../src/autopilot-parking.mjs';

const save = run => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));

async function closingFixture(t) {
  const f = await fixture(t, {agent: 'codex'});
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  f.herdr.idle();
  const run = f.record();
  run.automaticOrigin = {repository: run.repo, coordinatorId: 'progress-owner', machine: 'progress-machine',
    claim: {commentId: '11', labelEventId: '12'}};
  run.state = 'paused'; run.blockedOn = {kind: 'dependency', until: '2897'};
  save(run);
  const state = {cwd: f.source, repo: run.repo, coordinatorId: 'progress-owner', machine: 'progress-machine', runs: 1};
  f.ports.autopilotStateFile = join(f.state, 'owner.json');
  writeFileSync(f.ports.autopilotStateFile, JSON.stringify({...state, enabled: true, packageRoot,
    stateFile: f.ports.autopilotStateFile, baseBranch: 'main', agent: {id: 'codex', kind: 'codex', command: 'codex'}}));
  const herdr = f.ports.herdr;
  let refuseScreen = true;
  f.ports.herdr = async args => {
    if (refuseScreen && args[0] === 'pane' && args[1] === 'read')
      throw Object.assign(Error('no screen'), {code: 'screen_unavailable'});
    return herdr(args);
  };
  const ports = {now: () => f.clock, list: async () => [f.record()], checkProgress: async () => false,
    park: (held, blocker) => parkBlockedRun({ref: '17', cwd: f.source,
      coordinatorId: state.coordinatorId, machine: state.machine, blocker, expected: held}, f.ports)};
  const tick = () => reconcileParking(state, ports, {release: false});
  const status = async () => {
    const statusPath = join(f.state, createHash('sha256').update(f.source).digest('hex').slice(0, 20) + '.json');
    writeFileSync(statusPath, readFileSync(f.ports.autopilotStateFile));
    return runAutopilotLauncher({command: 'status', cwd: f.source, env: f.ports.env, packageRoot},
      {...healthyMachine, ...f.ports, stateRoot: f.state, timer: async () => false,
        checkCapacityPorts: isolatedCheckCapacity(f.base), allocationCheck: async () => ({state: 'ready'}),
        costRuns: async () => [], // Cost sampling is independent of parking custody.
        alertStatusLine: () => '', run: async (file, args, options) => ({code: 0, ...await f.ports.execFile(file, args, options)})});
  };
  await tick(); assert.equal(f.record().parking.phase, 'closing');
  refuseScreen = false; f.herdr.calls.length = 0;
  return {f, tick, status};
}

for (const mode of ['running', 'running-progressAt', 'running-updatedAt', 'recovery-grace', 'recovery-grace-without-progress'])
  test(`3132 repair 2 closing keeps custody for fresh ${mode}`, async t => {
    const {f, tick, status} = await closingFixture(t);
    const run = f.record();
    delete run.blockedOn; delete run.parkReason; delete run.stuckCause;
    run.gate = null; run.question = null;
    f.tick(1000);
    run.progressAt = run.updatedAt = run.parking.at;
    if (mode !== 'recovery-grace-without-progress') {
      if (mode !== 'running-updatedAt') run.progressAt = f.clock;
      if (mode !== 'running-progressAt') run.updatedAt = f.clock;
    }
    if (mode.startsWith('running')) run.state = 'running';
    else {run.state = 'paused'; run.chatResumeLimit = {at: f.clock};}
    save(run);
    const summary = await tick();
    assert.equal(f.record().parking.phase, 'closing', '3132_NEW_PROGRESS_WAS_PARKED');
    assert.equal(f.herdr.calls.filter(args => args[1] === 'close').length, 0, '3132_NEW_PROGRESS_CHAT_WAS_CLOSED');
    assert.deepEqual(f.record(), run, 'A held retry must preserve all durable custody and progress');
    assert.ok(f.herdr.paneOf(run.chats.at(-1)));
    assert.deepEqual([summary.working, summary.parked], [1, 0]);
    const reason = mode.startsWith('running') ? 'new progress since park'
      : `recovery grace until ${new Date(f.clock + 60_000).toISOString()}`;
    assert.equal(summary.closing[0].reasons[reason], 1);
    assert.ok(parkingWords(summary).includes(reason));
    // Status derives the same hold using a fresh summary and the injected clock.
    assert.equal(parkingSummary([f.record()], 1, f.clock).closing[0].reasons[reason], 1);
    const shown = await status();
    assert.equal(shown.exitCode, 0, shown.message);
    assert.ok(shown.message.includes(reason));
    assert.match(shown.message, /working 1 of 1/);
    assert.deepEqual(f.record(), run);
    if (!mode.startsWith('running')) {
      f.tick(59_999);
      const held = await tick();
      assert.equal(held.working, 1); assert.equal(held.closing[0].reasons[reason], 1);
      assert.equal(held.closing[0].reasons['closing-retry'], 1);
      assert.deepEqual(f.record(), run);
      assert.equal(f.herdr.calls.filter(args => args[1] === 'close').length, 0);
      f.tick(1); await tick();
      assert.equal(f.record().parking.phase, 'parked');
      assert.equal(f.herdr.paneOf(run.chats.at(-1)), undefined);
    }
  });

for (const mode of ['equal', 'older', 'stale-blocker', 'expired-running-grace'])
  test(`3132 repair 2 closing retries without fresh progress: ${mode}`, async t => {
    const {f, tick} = await closingFixture(t);
    const run = f.record(), session = run.chats.at(-1).session;
    if (mode !== 'stale-blocker') {delete run.blockedOn; run.state = 'running';}
    if (mode === 'expired-running-grace') run.chatResumeLimit = {at: run.parking.at};
    run.progressAt = run.updatedAt = run.parking.at - (mode === 'older' ? 1 : 0);
    save(run); f.tick(61_000);
    const summary = await tick(), after = f.record();
    assert.equal(after.parking.phase, 'parked');
    assert.deepEqual([summary.working, summary.parked], [0, 1]);
    assert.equal(after.parking.at, run.parking.at);
    assert.deepEqual(after.chats.at(-1).session, session);
    assert.ok(Number.isFinite(after.chats.at(-1).closed.confirmedAt));
    assert.equal(f.herdr.paneOf(run.chats.at(-1)), undefined);
  });
