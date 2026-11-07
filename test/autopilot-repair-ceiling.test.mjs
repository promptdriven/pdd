import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile as callbackExec } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdirSync, realpathSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { startRun, stepDone, approveRun, runStatus } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const exec = promisify(callbackExec), hour = 3600e3;
const at = ms => new Date(ms).toISOString();
const sha = value => createHash('sha256').update(value).digest('hex');

// Issue #3041: an Autopilot run gets at most 5 repair rounds in one area. A manual run
// keeps its skill's own 2-repair rule, and pdd does not refuse its reruns.
async function buildArea(t, { automatic }) {
  const f = await fixture(t, { name: 'small-change', agent: 'codex' });
  f.ports.env = { HOME: f.ports.env.HOME };
  assert.equal((await startRun({ name: 'small-change', issue: '17', agent: 'codex', cwd: f.source, packageRoot }, f.ports)).exitCode, 0);
  const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  if (automatic) {
    const saved = f.record();
    saved.automaticOrigin = { repository: 'example/project', coordinatorId: 'coordinator-a', machine: 'machine-a', claim: { commentId: '11', labelEventId: '12' } };
    writeRun(saved);
  }
  const done = async (step, summary) => { f.tick(); return stepDone({ step, summary, cwd: run.root }, f.agentPorts()); };
  return { f, done };
}

test('repair ceiling: the 5th failed round refuses a 6th in an Autopilot run; a manual run is not refused', async t => {
  const auto = await buildArea(t, { automatic: true });
  assert.equal((await auto.done('change', 'first change')).exitCode, 0);
  for (let round = 1; round <= 5; round++) {
    assert.equal((await auto.done('verify', `✗ round ${round - 1} fails`)).exitCode, 0);
    const again = await auto.done('change', `repair ${round}`);
    assert.equal(again.exitCode, 0, again.message);
    assert.match(again.message, /warning: change ran again after verify/);
    assert.match(again.message, new RegExp(`Repair round ${round} of 5 in the build area`));
  }
  assert.equal((await auto.done('verify', '✗ round 5 fails')).exitCode, 0);
  const refused = await auto.done('change', 'repair 6');
  assert.equal(refused.exitCode, 1);
  assert.match(refused.message, /refused another repair round: the build area of this Autopilot run has had 5 repair rounds/);
  assert.match(refused.message, /pdd:stuck.*one comment with the cause.*one stuck alert.*keep the claim and progress/);
  const kept = auto.f.record();
  assert.deepEqual(kept.repairRounds, { build: 5 });
  assert.equal(kept.done.change.summary, 'repair 5', 'the refused round is not recorded');
  assert.equal(kept.done.verify.summary, '✗ round 5 fails', 'the failed check stays as the cause');
  assert.equal(auto.f.pushes.length, 0);

  const manual = await buildArea(t, { automatic: false });
  assert.equal((await manual.done('change', 'first change')).exitCode, 0);
  for (let round = 1; round <= 6; round++) {
    assert.equal((await manual.done('verify', `✗ round ${round - 1} fails`)).exitCode, 0);
    const again = await manual.done('change', `repair ${round}`);
    assert.equal(again.exitCode, 0, again.message);
    assert.match(again.message, /warning: change ran again after verify/);
    assert.doesNotMatch(again.message, /Repair round/);
  }
  assert.equal(manual.f.record().repairRounds, undefined, 'a manual run saves no count');
});

// An Autopilot run that can publish: a live claim on fake GitHub, so that pdd opens the PR.
async function publishingRun(t, { rounds } = {}) {
  const f = await fixture(t, { name: 'small-change', agent: 'codex' });
  f.ports.env = { HOME: f.ports.env.HOME };
  assert.equal((await startRun({ name: 'small-change', issue: '17', agent: 'codex', cwd: f.source, packageRoot }, f.ports)).exitCode, 0);
  const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const origin = { repository: 'example/project', coordinatorId: 'coordinator-a', machine: 'machine-a', claim: { commentId: '11', labelEventId: '12' } };
  const saved = f.record(); saved.automaticOrigin = structuredClone(origin); if (rounds) saved.repairRounds = rounds; writeRun(saved);
  const root = realpathSync(f.source), stateRoot = join(f.state, 'autopilot'); mkdirSync(stateRoot, { recursive: true });
  writeFileSync(join(stateRoot, `${sha(root).slice(0, 20)}.json`), JSON.stringify({ repo: 'example/project', cwd: root, coordinatorId: origin.coordinatorId }));
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const fixturePath = join(f.base, 'reader.json'), logPath = join(f.base, 'gh.log'), claimedAt = at(f.clock - 2 * hour);
  const original = f.ports.execFile;
  const execFile = (file, args, opts) => file === 'gh' && args[0] === 'api' && args[1] === '--include'
    ? exec(process.execPath, [join(packageRoot, 'test/helpers/continuation-fake-gh.mjs'), ...args], { ...opts, env: { ...process.env, READER_FIXTURE_FILE: fixturePath, READER_GH_LOG: logPath } })
    : original(file, args, opts);
  let value = 2;
  const edit = () => { writeFileSync(join(run.root, 'value.mjs'), `export const value = ${value++};\n`); f.git(run.root, 'commit', '-qam', `value ${value}`); };
  const done = async (step, summary = step) => {
    f.tick();
    // The live claim, with its last heartbeat now.
    writeFileSync(fixturePath, JSON.stringify({ labels: ['pdd:working'], events: [{ id: 12, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: claimedAt }],
      comments: [{ id: 11, user: { login: 'example' }, created_at: claimedAt, updated_at: at(f.clock), body: JSON.stringify({ repository: origin.repository, coordinatorId: origin.coordinatorId, machine: origin.machine, labelEventId: '12', lastSeen: at(f.clock) }) }] }));
    return stepDone({ step, summary, cwd: run.root }, f.agentPorts({ execFile, autopilotStateRoot: stateRoot }));
  };
  return { f, run, done, edit };
}

test('repair ceiling: a retry of the PR open after a clean first pass is not a repair round, and the PR opens', async t => {
  const { f, done, edit } = await publishingRun(t);
  edit();
  for (const step of ['change', 'verify']) assert.equal((await done(step)).exitCode, 0);
  f.createError = 'HTTP 502: Bad Gateway';
  const failed = await done('formal');
  assert.equal(failed.exitCode, 1);
  assert.match(failed.message, /Run done formal again to retry/);
  const retry = await done('formal');
  assert.equal(retry.exitCode, 0, retry.message);
  assert.doesNotMatch(retry.message, /Repair round/);
  assert.equal(f.prs.length, 1, 'the PR opens');
  assert.equal(f.record().repairRounds, undefined, 'no round is counted');
});

test('repair ceiling: after 5 real rounds and a green 6th pass, a retry of a failed PR open is allowed', async t => {
  const { f, done, edit } = await publishingRun(t);
  edit();
  assert.equal((await done('change')).exitCode, 0);
  for (let round = 1; round <= 5; round++) {
    assert.equal((await done('verify', `✗ round ${round - 1} fails`)).exitCode, 0);
    edit();
    const again = await done('change', `repair ${round}`);
    assert.equal(again.exitCode, 0, again.message);
    assert.match(again.message, new RegExp(`Repair round ${round} of 5 in the build area`));
  }
  assert.equal((await done('verify', '✓ green')).exitCode, 0);
  f.createError = 'HTTP 502: Bad Gateway';
  assert.equal((await done('formal')).exitCode, 1);
  const retry = await done('formal');
  assert.equal(retry.exitCode, 0, retry.message);
  assert.doesNotMatch(retry.message, /refused|Repair round/);
  assert.equal(f.prs.length, 1, 'the PR opens');
  assert.deepEqual(f.record().repairRounds, { build: 5 });
  assert.equal(f.record().repairLimit, undefined);
});

test('repair ceiling: verify recorded again with no code change is not a round; a code change before it is', async t => {
  const { f, done, edit } = await publishingRun(t);
  edit();
  assert.equal((await done('change')).exitCode, 0);
  assert.equal((await done('verify', 'Prompt tests: no verdict')).exitCode, 0);
  const same = await done('verify', 'Prompt tests: 3 of 3');
  assert.doesNotMatch(same.message, /Repair round/, 'a retry of the same step');
  assert.equal((await done('formal', '✗ formal fails')).exitCode, 0);
  const again = await done('verify', 'verify again, no change');
  assert.match(again.message, /warning: verify ran again after formal/);
  assert.doesNotMatch(again.message, /Repair round/, 'verify again after formal, on unchanged worktree content');
  assert.equal(f.record().repairRounds, undefined);
  assert.equal((await done('formal', '✗ formal fails')).exitCode, 0);
  edit();
  const changed = await done('verify', 'verify after a fix');
  assert.match(changed.message, /Repair round 1 of 5 in the build area/, 'a fix, then verify again after formal');
});

test('repair ceiling: after the refusal the run is stuck in status, and no later done opens the PR', async t => {
  const { f, done, edit } = await publishingRun(t, { rounds: { build: 5 } });
  edit();
  assert.equal((await done('change', 'repair 5')).exitCode, 0);
  assert.equal((await done('verify', '✗ 2 vectors fail')).exitCode, 0);
  edit();
  const refused = await done('change', 'repair 6');
  assert.equal(refused.exitCode, 1);
  assert.match(refused.message, /refused another repair round/);
  assert.match(refused.message, /A person lets Autopilot try again with a new run and a new count: they remove pdd:stuck and pdd:working/);
  const status = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.match(status.message, /^State: stuck: Repair limit reached in build: take the stuck path$/m);
  const forward = await done('formal');
  assert.equal(forward.exitCode, 1, 'a forward step after the refusal is refused too');
  assert.match(forward.message, /pdd refused formal: the build area of this Autopilot run has had 5 repair rounds/);
  assert.equal(f.prs.length, 0, 'no PR with failing vectors');
  assert.equal(f.pushes.length, 0);
  const kept = f.record();
  assert.equal(kept.done.formal, undefined);
  assert.equal(kept.done.verify.summary, '✗ 2 vectors fail');
  assert.equal(kept.state, 'stuck');
});
