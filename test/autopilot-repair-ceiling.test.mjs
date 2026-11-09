import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile as callbackExec } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdirSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { startRun, stepDone, approveRun, runStatus, cancelRun, parkAutomaticRun } from '../src/workflow-runner.mjs';
import { environmentRecovery } from '../src/autopilot-environment.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const exec = promisify(callbackExec), hour = 3600e3;
const at = ms => new Date(ms).toISOString();
const sha = value => createHash('sha256').update(value).digest('hex');

// Issue #3041: an Autopilot run gets at most 5 repair rounds in one area. A manual run
// keeps its skill's own 2-repair rule, and pdd does not refuse its reruns.
async function buildArea(t, { automatic }) {
  const f = await fixture(t, { name: 'small-change', agent: 'codex' });
  f.ports.env = { HOME: f.ports.env.HOME, PDD_INTERPRETER_QUEUE: f.ports.env.PDD_INTERPRETER_QUEUE };
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
async function publishingRun(t, { rounds, unavailableMerge = false } = {}) {
  const f = await fixture(t, { name: 'small-change', agent: 'codex' });
  f.ports.env = { HOME: f.ports.env.HOME, PDD_INTERPRETER_QUEUE: f.ports.env.PDD_INTERPRETER_QUEUE };
  assert.equal((await startRun({ name: 'small-change', issue: '17', agent: 'codex', cwd: f.source, packageRoot }, f.ports)).exitCode, 0);
  const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const origin = { repository: 'example/project', coordinatorId: 'coordinator-a', machine: 'machine-a', claim: { commentId: '11', labelEventId: '12' } };
  const saved = f.record(); saved.automaticOrigin = structuredClone(origin); if (rounds) saved.repairRounds = rounds; writeRun(saved);
  const root = realpathSync(f.source), stateRoot = join(f.state, 'autopilot'); mkdirSync(stateRoot, { recursive: true });
  writeFileSync(join(stateRoot, `${sha(root).slice(0, 20)}.json`), JSON.stringify({ enabled: true, repo: 'example/project', cwd: root, coordinatorId: origin.coordinatorId, machine: origin.machine,
    activatedAt: 'activation', startAction: { command: 'pdd autopilot start', repository: 'example/project', mode: 'auto' } }));
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const fixturePath = join(f.base, 'reader.json'), logPath = join(f.base, 'gh.log'), claimedAt = at(f.clock - 2 * hour);
  const original = f.ports.execFile;
  const execFile = (file, args, opts) => file === 'gh' && args[0] === 'api' && args[1] === '--include'
    ? exec(process.execPath, [join(packageRoot, 'test/helpers/continuation-fake-gh.mjs'), ...args], { ...opts, env: { ...process.env, READER_FIXTURE_FILE: fixturePath, READER_GH_LOG: logPath } })
    : file === 'git' && args[0] === 'merge-tree' && unavailableMerge
      ? Promise.resolve({ code: 1, stdout: '', stderr: 'unavailable' }) : original(file, args, opts);
  let value = 2;
  const edit = () => { writeFileSync(join(run.root, 'value.mjs'), `export const value = ${value++};\n`); f.git(run.root, 'commit', '-qam', `value ${value}`); };
  // Fake GitHub: the claim eras of issue 17. The last era is the live claim, with its last heartbeat now.
  const github = { labels: ['pdd:working'], eras: [{ event: 12, comment: 11, at: claimedAt }] };
  const claimComment = era => ({ id: era.comment, user: { login: 'example' }, created_at: era.at, updated_at: at(f.clock),
    body: JSON.stringify({ repository: origin.repository, coordinatorId: origin.coordinatorId, machine: origin.machine, labelEventId: String(era.event), lastSeen: at(f.clock) }) });
  const writeGitHub = () => writeFileSync(fixturePath, JSON.stringify({ labels: github.labels,
    events: github.eras.flatMap(era => [{ id: era.event, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: era.at },
      ...(era.removed ? [{ id: era.event + 1, event: 'unlabeled', label: { name: 'pdd:working' }, actor: { login: 'example' }, created_at: era.removed }] : [])]),
    comments: github.eras.map(claimComment) }));
  const done = async (step, summary = step) => {
    f.tick(); writeGitHub();
    return stepDone({ step, summary, cwd: run.root }, f.agentPorts({ execFile, autopilotStateRoot: stateRoot }));
  };
  // A new automatic start by this coordinator for its current claim, as the next tick's agent runs it.
  const start = () => {
    f.tick(); writeGitHub();
    const era = github.eras.at(-1), coordinator = { ...origin, claim: { commentId: String(era.comment), labelEventId: String(era.event) }, activation: 'activation' };
    return startRun({ name: 'small-change', issue: '17', agent: 'codex', cwd: f.source, packageRoot, coordinator },
      { ...f.ports, execFile, autopilotStateRoot: stateRoot, checkDependencyStart: async () => ({ allowed: true, reason: 'ok' }) });
  };
  return { f, run, done, edit, github, start };
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
  assert.ok(refused.message.includes('To let Autopilot try again, a person removes pdd:stuck and pdd:working, then runs pdd workflow cancel 17 in the checkout that holds the stuck run; the next tick starts a new run with a fresh repair count.'), refused.message);
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

// The way out after the repair limit (#3041 repair 2): a stuck run is not ended, so the person
// also cancels it in the checkout that holds it; the next automatic start then gets a fresh count.
async function stuckAtLimit(t) {
  const r = await publishingRun(t, { rounds: { build: 5 } });
  r.edit();
  assert.equal((await r.done('change', 'repair 5')).exitCode, 0);
  assert.equal((await r.done('verify', '✗ 2 vectors fail')).exitCode, 0);
  r.edit();
  const refused = await r.done('change', 'repair 6');
  assert.equal(refused.exitCode, 1);
  assert.match(refused.message, /then runs pdd workflow cancel 17 in the checkout that holds the stuck run/);
  assert.equal(r.f.record().state, 'stuck');
  return r;
}
// The person removes pdd:stuck and pdd:working; on the next tick this coordinator claims the issue again.
function removeLabelsAndClaimAgain(r) {
  r.f.tick(); r.github.eras.at(-1).removed = at(r.f.clock); r.github.labels = [];
  r.f.tick(60e3); r.github.eras.push({ event: 22, comment: 21, at: at(r.f.clock) }); r.github.labels = ['pdd:working'];
}

test('repair ceiling: after the limit, labels removed and pdd workflow cancel, the next automatic start gets a fresh count', async t => {
  const r = await stuckAtLimit(t);
  const stuck = r.f.record();
  removeLabelsAndClaimAgain(r);
  const cancelled = await cancelRun({ ref: '17', cwd: r.f.source }, r.f.ports);
  assert.equal(cancelled.exitCode, 0, cancelled.message);
  const started = await r.start();
  assert.equal(started.exitCode, 0, started.message);
  const fresh = r.f.record();
  assert.notEqual(fresh.runId, stuck.runId, 'a new run');
  assert.notEqual(fresh.state, 'stuck');
  assert.equal(fresh.repairRounds, undefined, 'a fresh repair count');
  assert.equal(fresh.repairLimit, undefined);
  assert.deepEqual(fresh.automaticOrigin.claim, { commentId: '21', labelEventId: '22' }, 'the new run holds the new claim');
});

test('repair ceiling: after the limit and labels removed, without the cancel a new automatic start is deferred', async t => {
  const r = await stuckAtLimit(t);
  const stuck = r.f.record();
  removeLabelsAndClaimAgain(r);
  const deferred = await r.start();
  assert.equal(deferred.exitCode, 1);
  assert.match(deferred.message, /^Automatic start deferred: issue has an active run\.$/);
  const kept = r.f.record();
  assert.equal(kept.runId, stuck.runId, 'the stuck run stays');
  assert.equal(kept.state, 'stuck');
  assert.deepEqual(kept.repairRounds, { build: 5 });
  assert.ok(kept.repairLimit);
  const again = await r.done('change', 'repair 7');
  assert.equal(again.exitCode, 1, 'the stuck run still refuses every done');
  assert.match(again.message, /pdd refused change: the build area of this Autopilot run has had 5 repair rounds/);
});

test('repair ceiling: an unknown worktree fingerprint does not make verify again a repair round', async t => {
  const { f, run, done, edit } = await publishingRun(t);
  edit();
  assert.equal((await done('change')).exitCode, 0);
  assert.equal((await done('verify', 'Prompt tests: 3 of 3')).exitCode, 0);
  assert.equal((await done('formal', '✗ formal fails')).exitCode, 0);
  // A tracked path that is not a regular file or link: pdd cannot fingerprint the worktree (unknown now).
  const path = join(run.root, 'value.mjs');
  rmSync(path); mkdirSync(path); writeFileSync(join(path, 'inner.txt'), 'x\n');
  const unknownNow = await done('verify', 'verify again, fingerprint unknown');
  assert.equal(unknownNow.exitCode, 0, unknownNow.message);
  assert.match(unknownNow.message, /warning: verify ran again after formal/);
  assert.doesNotMatch(unknownNow.message, /Repair round/);
  assert.equal(f.record().done.verify.worktreeSha256, undefined, 'no fingerprint saved');
  // The worktree is readable again, but the last verify record has no fingerprint (unknown then).
  rmSync(path, { recursive: true }); f.git(run.root, 'checkout', '--', 'value.mjs');
  assert.equal((await done('formal', '✗ formal fails')).exitCode, 0);
  const unknownThen = await done('verify', 'verify again, fingerprint known now');
  assert.doesNotMatch(unknownThen.message, /Repair round/);
  assert.equal(f.record().repairRounds, undefined, 'unknown counts as no change');
});

function advanceBase(f, run, n) {
  writeFileSync(join(f.source, `base-${n}.txt`), `base ${n}\n`);
  f.git(f.source, 'add', '.'); f.git(f.source, 'commit', '-qm', `Base advance ${n}`);
  f.git(f.source, 'update-ref', 'refs/remotes/origin/main', 'HEAD');
  f.git(run.root, 'merge', '--no-edit', 'refs/remotes/origin/main');
}

test('base integration: two clean base merges retain the issue patch and the two used defect repairs', async t => {
  const { f, run, done, edit } = await publishingRun(t);
  edit(); await done('change');
  for (let n = 1; n <= 2; n++) {
    await done('verify', `defect failure ${n}`); edit(); await done('change');
  }
  assert.deepEqual(f.record().repairRounds, { build: 2 });
  for (let n = 1; n <= 2; n++) {
    await done('verify', `base validation failure ${n}`);
    await done('formal', `formal failure ${n}`);
    const before = f.record(); advanceBase(f, run, n);
    const result = await done('change', 'integrate saved base');
    assert.equal(result.exitCode, 0, result.message);
    const after = f.record();
    assert.deepEqual(after.repairRounds, { build: 2 }, 'base refresh must not consume a defect repair');
    assert.deepEqual(after.integrationRounds, { build: n });
    assert.equal(after.done.verify, undefined); assert.equal(after.done.formal, undefined);
    assert.ok(after.stepHistory.some(row => row.step === 'verify' && row.record.summary === before.done.verify.summary));
    assert.ok(after.stepHistory.some(row => row.step === 'formal' && row.record.summary === before.done.formal.summary));
    assert.equal(after.done.change.integration.from.head, before.done.change.integrationSource.head);
    assert.notEqual(after.done.change.integration.from.base, after.done.change.integration.to.base);
  }
  await done('verify', 'retained failure at integration ceiling');
  const before = f.record(), pushes = f.pushes.length; advanceBase(f, run, 3);
  assert.equal((await done('change')).exitCode, 1);
  const after = f.record();
  assert.equal(after.state, 'stuck'); assert.equal(after.integrationLimit.area, 'build');
  assert.deepEqual(after.integrationRounds, { build: 2 }); assert.deepEqual(after.repairRounds, { build: 2 });
  assert.deepEqual(after.done, before.done); assert.deepEqual(after.stepHistory, before.stepHistory);
  assert.equal((await done('review')).exitCode, 1); assert.equal(f.pushes.length, pushes);
  const status = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.match(status.message, /integration/i);
  await parkAutomaticRun({ cwd: run.root, reason: 'Native validation timeout', step: 'verify' }, f.agentPorts());
  assert.equal(environmentRecovery(f.record()), null);
  assert.equal((await done('change')).exitCode, 1);
});

test('base integration: repeating verify after a pure base merge also uses the integration budget', async t => {
  const { f, run, done, edit } = await publishingRun(t);
  edit(); await done('change'); await done('verify'); await done('formal', 'failed formal');
  advanceBase(f, run, 1);
  assert.equal((await done('verify')).exitCode, 0);
  assert.equal(f.record().repairRounds, undefined);
  assert.deepEqual(f.record().integrationRounds, { build: 1 });
  assert.equal(f.record().done.formal, undefined);
  edit();
  assert.equal((await done('change')).exitCode, 0);
  assert.deepEqual(f.record().repairRounds, { build: 1 }, 'a later defect still consumes a repair');
  assert.deepEqual(f.record().integrationRounds, { build: 1 }, 'a defect cannot reset integration history');
});

test('base integration: verify then formal then change charges each merged source once per area', async t => {
  const { f, run, done, edit } = await publishingRun(t, { rounds: { build: 2 } });
  edit(); await done('change'); await done('verify'); await done('formal', 'failed formal');
  const original = f.record();
  advanceBase(f, run, 1);
  assert.equal((await done('verify')).exitCode, 0);
  const verified = f.record();
  assert.deepEqual(verified.integrationRounds, { build: 1 });
  assert.equal(verified.done.change, undefined, 'the earlier step on old source must be recorded again');
  assert.ok(verified.stepHistory.some(row => row.step === 'change'
    && JSON.stringify(row.record) === JSON.stringify(original.done.change)),
    'the earlier step keeps its actual source identity in history');
  assert.notDeepEqual(verified.done.verify.integrationSource, original.done.verify.integrationSource);
  await done('formal', 'failed formal on integrated source');
  assert.equal((await done('verify')).exitCode, 0, 'repeated verify is free');
  await done('formal', 'failed formal on same source');
  const beforeChange = f.record();
  assert.equal((await done('change')).exitCode, 0);
  const changed = f.record();
  assert.deepEqual(changed.integrationRounds, { build: 1 }, 'one merge costs one integration across steps');
  assert.deepEqual(changed.repairRounds, { build: 2 }, 'repeating change on accounted source is free');
  assert.deepEqual(changed.done.change.integrationSource, verified.done.verify.integrationSource);
  for (const step of ['change', 'verify', 'formal']) {
    const previous = beforeChange.done[step] ?? original.done[step];
    const retained = step !== 'change' && JSON.stringify(changed.done[step]) === JSON.stringify(previous);
    assert.ok(retained || changed.stepHistory.some(row => row.step === step
      && JSON.stringify(row.record) === JSON.stringify(previous)), 'retain current or archived source evidence');
  }
  await done('verify'); advanceBase(f, run, 2);
  const second = await done('change');
  assert.equal(second.exitCode, 0, second.message);
  assert.deepEqual(f.record().integrationRounds, { build: 2 });
  assert.deepEqual(f.record().repairRounds, { build: 2 });
  await done('verify'); await done('formal', 'failed formal at ceiling');
  assert.equal((await done('change')).exitCode, 0, 'accounted source stays free at the ceiling');
  await done('verify', 'failed before third merge');
  const beforeThird = f.record(); advanceBase(f, run, 3);
  assert.equal((await done('change')).exitCode, 1);
  const refused = f.record();
  assert.equal(refused.state, 'stuck'); assert.equal(refused.integrationLimit.area, 'build');
  assert.deepEqual(refused.integrationRounds, { build: 2 });
  assert.deepEqual(refused.repairRounds, { build: 2 });
  assert.deepEqual(refused.done, beforeThird.done); assert.deepEqual(refused.stepHistory, beforeThird.stepHistory);
});

function advanceEmptyBase(f, run) {
  f.git(f.source, 'commit', '--allow-empty', '-qm', 'Base metadata only');
  f.git(f.source, 'update-ref', 'refs/remotes/origin/main', 'HEAD');
  f.git(run.root, 'merge', '--no-edit', 'refs/remotes/origin/main');
}

test('base integration: formal first archives all older source records before publication', async t => {
  const { f, run, done, edit } = await publishingRun(t);
  edit(); await done('change'); await done('verify');
  f.createError = 'HTTP 502: Bad Gateway';
  assert.equal((await done('formal')).exitCode, 1);
  const before = f.record(), publications = f.prs.length, pushes = f.pushes.length;
  advanceBase(f, run, 1);
  const result = await done('formal', 'formal on integrated source');
  assert.equal(result.exitCode, 0, result.message);
  const after = f.record();
  assert.equal(after.done.verify, undefined, 'changed source requires fresh verification; the old result must be history');
  assert.equal(after.done.change, undefined, 'all earlier records on the old source must leave current results');
  for (const step of ['change', 'verify', 'formal']) {
    assert.ok(after.stepHistory.some(row => row.step === step
      && JSON.stringify(row.record) === JSON.stringify(before.done[step])), 'keep each old record with its actual source');
  }
  assert.notEqual(after.done.formal.integrationSource.tree, before.done.formal.integrationSource.tree);
  assert.deepEqual(after.integrationRounds, { build: 1 });
  assert.equal(after.repairRounds, undefined);
  assert.equal(f.prs.length, publications, 'publishing waits for fresh verification');
  assert.equal(f.pushes.length, pushes, 'do not push before fresh step records');
  assert.match(result.message, /Next step: change\b/);
  assert.match((await done('formal')).message, /Next step: change\b/);
  assert.equal(f.prs.length, publications);
  assert.match((await done('change')).message, /Next step: verify\b/);
  assert.equal(f.prs.length, publications);
  assert.equal((await done('verify')).exitCode, 0);
  assert.equal(f.prs.length, publications + 1, 'fresh records allow publication');
  const fresh = f.record();
  for (const step of ['change', 'verify', 'formal']) {
    assert.equal(fresh.done[step].integrationSource.tree, after.done.formal.integrationSource.tree);
  }
  assert.deepEqual(fresh.integrationRounds, { build: 1 }, 'rerecording missing steps does not charge again');
  assert.equal(fresh.repairRounds, undefined);
  advanceBase(f, run, 2);
  assert.equal((await done('formal')).exitCode, 0);
  const second = f.record();
  assert.equal(second.done.change, undefined); assert.equal(second.done.verify, undefined);
  assert.deepEqual(second.integrationRounds, { build: 2 });
  advanceBase(f, run, 3);
  assert.equal((await done('change')).exitCode, 1, 'a missing current step cannot bypass the integration bound');
  const refused = f.record();
  assert.deepEqual(refused.integrationRounds, { build: 2 });
  assert.equal(refused.repairRounds, undefined);
  assert.deepEqual(refused.done, second.done); assert.deepEqual(refused.stepHistory, second.stepHistory);
  assert.equal(refused.integrationLimit.area, 'build');
});

test('base integration: native assertion failing after a formal-first merge leaves the PR blocked', async t => {
  const { f, run, done, edit } = await publishingRun(t);
  writeFileSync(join(f.source, 'ready.mjs'), 'export const ready = true;\n');
  f.git(f.source, 'add', 'ready.mjs'); f.git(f.source, 'commit', '-qm', 'Old base passes native validation');
  f.git(f.source, 'update-ref', 'refs/remotes/origin/main', 'HEAD');
  f.git(run.root, 'merge', '--no-edit', 'refs/remotes/origin/main');
  const validate = () => exec(process.execPath, ['--input-type=module', '-e',
    "import {ready} from './ready.mjs'; import assert from 'node:assert/strict'; assert.equal(ready,true,'REVIEW_BASE_READY');"],
    { cwd: run.root, env: { ...process.env, ...f.ports.env }, encoding: 'utf8' });
  edit(); await done('change');
  await validate(); await done('verify', 'native assertion passed on old source');
  f.createError = 'HTTP 502: Bad Gateway';
  assert.equal((await done('formal')).exitCode, 1);
  const before = f.record(), publications = f.prs.length;
  writeFileSync(join(f.source, 'ready.mjs'), 'export const ready = false;\n');
  advanceBase(f, run, 1);
  await assert.rejects(validate, error => error.code === 1 && /REVIEW_BASE_READY/.test(error.stderr));
  const result = await done('formal', 'formal on source with failed native assertion');
  assert.equal(f.prs.length, publications, 'a failed fresh assertion cannot publish with stale verification');
  assert.equal(f.record().done.verify, undefined);
  assert.match(result.message, /Next step: change\b/);
  await done('change');
  const retry = await done('formal', 'publication retry while fresh verification is missing');
  assert.match(retry.message, /Next step: verify\b/);
  assert.equal(f.prs.length, publications);
  assert.equal(f.record().done.verify, undefined, 'the failed assertion supplies no completed fresh verify step');
  assert.ok(f.record().stepHistory.some(row => row.step === 'verify'
    && JSON.stringify(row.record) === JSON.stringify(before.done.verify)));
  assert.deepEqual(f.record().integrationRounds, { build: 1 });
  assert.equal(f.record().repairRounds, undefined);
});

test('base integration: mixed returns after an empty base advance keep the second merge available', async t => {
  const { f, run, done, edit } = await publishingRun(t, { rounds: { build: 2 } });
  const accepted = async step => {
    const result = await done(step, step === 'formal' ? 'failed formal' : step);
    assert.equal(result.exitCode, 0, result.message);
  };
  edit(); await accepted('change'); await accepted('verify'); await accepted('formal');
  const originalChange = f.record().done.change;
  advanceBase(f, run, 1);
  await accepted('verify'); await accepted('formal');
  const beforeEmpty = f.record();
  advanceEmptyBase(f, run);
  await accepted('verify'); await accepted('formal');
  const afterEmpty = f.record();
  assert.equal(afterEmpty.done.verify.integrationSource.tree, beforeEmpty.done.verify.integrationSource.tree);
  assert.notEqual(afterEmpty.done.verify.integrationSource.base, beforeEmpty.done.verify.integrationSource.base);
  assert.equal(afterEmpty.done.change, undefined, 'old source records cannot stay current after integration');
  assert.ok(afterEmpty.stepHistory.some(row => row.step === 'change'
    && JSON.stringify(row.record) === JSON.stringify(originalChange)), 'old results keep their real source in history');
  assert.deepEqual(afterEmpty.integrationRounds, { build: 1 });
  assert.deepEqual(afterEmpty.repairRounds, { build: 2 });
  await accepted('change');
  assert.deepEqual(f.record().integrationRounds, { build: 1 }, 'the same tree must not be charged again');
  assert.deepEqual(f.record().repairRounds, { build: 2 });
  for (const step of ['change', 'verify', 'formal']) {
    const previous = afterEmpty.done[step] ?? originalChange;
    const current = f.record();
    const retained = current.done[step] && JSON.stringify(current.done[step]) === JSON.stringify(previous);
    assert.ok(retained || current.stepHistory.some(row => row.step === step
      && JSON.stringify(row.record) === JSON.stringify(previous)));
  }
  advanceBase(f, run, 2); await accepted('change');
  assert.deepEqual(f.record().integrationRounds, { build: 2 }, 'a new tree charges even with no later records');
  assert.deepEqual(f.record().repairRounds, { build: 2 });
  const beforeThird = f.record(); advanceBase(f, run, 3);
  assert.equal((await done('change')).exitCode, 1);
  const refused = f.record();
  assert.equal(refused.state, 'stuck'); assert.equal(refused.integrationLimit.area, 'build');
  assert.deepEqual(refused.integrationRounds, { build: 2 });
  assert.deepEqual(refused.repairRounds, { build: 2 });
  assert.deepEqual(refused.done, beforeThird.done); assert.deepEqual(refused.stepHistory, beforeThird.stepHistory);
  assert.equal((await done('formal')).exitCode, 1);
});

test('base integration: charged trees stay free across every mixed return order and empty base advances', async t => {
  const orders = [
    ['change', 'verify', 'formal'], ['change', 'formal', 'verify'],
    ['verify', 'change', 'formal'], ['verify', 'formal', 'change'],
    ['formal', 'change', 'verify'], ['formal', 'verify', 'change'],
  ];
  for (const order of orders) await t.test(order.join(' -> '), async t => {
    const { f, run, done, edit } = await publishingRun(t, { rounds: { build: 2 } });
    const accepted = async step => {
      const result = await done(step, step === 'formal' ? 'failed formal' : step);
      assert.equal(result.exitCode, 0, result.message);
    };
    edit(); await accepted('change'); await accepted('verify'); await accepted('formal');
    for (let n = 1; n <= 2; n++) {
      advanceBase(f, run, n);
      await accepted(n === 1 ? 'verify' : order[0]);
      assert.deepEqual(f.record().integrationRounds, { build: n }, 'the first return charges the new tree');
      await accepted('verify'); await accepted('formal');
      const charged = f.record();
      advanceEmptyBase(f, run); await accepted('verify'); await accepted('formal');
      assert.equal(f.record().done.verify.integrationSource.tree, charged.done.verify.integrationSource.tree);
      assert.notEqual(f.record().done.verify.integrationSource.base, charged.done.verify.integrationSource.base);
      for (const step of order) {
        await accepted(step);
        assert.deepEqual(f.record().integrationRounds, { build: n }, 'step order must not charge the same tree twice');
        assert.deepEqual(f.record().repairRounds, { build: 2 });
        assert.equal(f.record().integrationLimit, undefined);
      }
      // Change can clear both checks. Record their snapshots before the next merge.
      await accepted('verify'); await accepted('formal');
    }
    const beforeThird = f.record(); advanceBase(f, run, 3);
    assert.equal((await done('change')).exitCode, 1);
    assert.deepEqual(f.record().integrationRounds, { build: 2 });
    assert.deepEqual(f.record().repairRounds, { build: 2 });
    assert.deepEqual(f.record().done, beforeThird.done);
    assert.deepEqual(f.record().stepHistory, beforeThird.stepHistory);
  });
});

for (const rounds of [0, 2]) for (const step of ['verify', 'change']) {
  test(`base integration: source-identical base advance is free for ${step} after ${rounds} integrations`, async t => {
    const { f, run, done, edit } = await publishingRun(t, { rounds: { build: 2 } });
    edit(); await done('change');
    for (let n = 1; n <= rounds; n++) {
      await done('verify'); advanceBase(f, run, n);
      assert.equal((await done('change')).exitCode, 0);
    }
    await done('verify'); await done('formal', 'failed formal');
    const before = f.record();
    f.git(f.source, 'commit', '--allow-empty', '-qm', 'Base metadata only');
    f.git(f.source, 'update-ref', 'refs/remotes/origin/main', 'HEAD');
    f.git(run.root, 'merge', '--no-edit', 'refs/remotes/origin/main');
    assert.equal((await done(step)).exitCode, 0);
    const after = f.record();
    assert.equal(after.done[step].worktreeSha256, before.done[step].worktreeSha256);
    assert.equal(after.done[step].integrationSource.tree, before.done[step].integrationSource.tree);
    assert.notEqual(after.done[step].integrationSource.base, before.done[step].integrationSource.base);
    assert.deepEqual(after.integrationRounds, before.integrationRounds);
    assert.deepEqual(after.repairRounds, { build: 2 }); assert.equal(after.integrationLimit, undefined);
    assert.equal(after.done.formal, undefined);
    assert.ok(after.stepHistory.some(row => row.step === 'formal'
      && JSON.stringify(row.record) === JSON.stringify(before.done.formal)));
  });
}

for (const kind of ['committed defect', 'dirty source', 'missing snapshot', 'unavailable merge']) {
  test(`base integration: ${kind} cannot claim a base-only exemption`, async t => {
    const { f, run, done, edit } = await publishingRun(t, { unavailableMerge: kind === 'unavailable merge' });
    edit(); await done('change'); await done('verify', 'failed verification');
    if (kind === 'missing snapshot') { const saved = f.record(); delete saved.done.change.integrationSource; writeRun(saved); }
    advanceBase(f, run, 1);
    if (kind === 'committed defect') edit();
    if (kind === 'dirty source') writeFileSync(join(run.root, 'untracked-defect.mjs'), 'export const defect = true;\n');
    assert.equal((await done('change', 'base-only refresh')).exitCode, 0);
    assert.deepEqual(f.record().repairRounds, { build: 1 });
    assert.equal(f.record().integrationRounds, undefined);
  });
}

test('base integration: a saved defect repair refusal cannot be bypassed by merging the base', async t => {
  const { f, run, done, edit } = await publishingRun(t, { rounds: { build: 5 } });
  edit(); await done('change'); await done('verify', 'failed verification');
  assert.equal((await done('change')).exitCode, 1);
  const before = f.record(); advanceBase(f, run, 1);
  assert.equal((await done('change')).exitCode, 1);
  assert.deepEqual(f.record().repairLimit, before.repairLimit);
  assert.equal(f.record().integrationRounds, undefined); assert.deepEqual(f.record().done, before.done);
});
