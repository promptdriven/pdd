import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { spawn } from 'node:child_process';
import { appendFileSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { coreWorld } from './helpers/core-world.mjs';
import { checkMachine, isolatedCheckCapacity, withCheckLifetime } from './helpers/check-machine.mjs';
import { healthyDoctorPorts } from './helpers/doctor-fixture.mjs';
import { healthyMachine } from './helpers/healthy-machine.mjs';
import { runAutopilotLauncher } from '../src/autopilot-launcher.mjs';
import { intakeRows } from '../src/autopilot-intake.mjs';
import { acquireSuiteLock, calculateCheckCapacity, readSuiteProgress, runTestSuite } from '../src/test-suite-queue.mjs';

const REPO_ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');
const MIN = 60 * 1000;

function readMachineState(w) {
  return JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
}

function readJobFile(w, issue) {
  return JSON.parse(readFileSync(join(w.root, 'jobs', `${issue}.json`), 'utf8'));
}

test('P0-9A: terminal auth-unavailable and zero-quota errors park immediately with concrete resetAt, zero retry storms, and zero burned repair/review strikes', async t => {
  // 1. Pre-PR build hitting 401 Unauthorized on a single-login host parks immediately (0 streak strikes, 0 slot held, intake parked).
  const w1 = await coreWorld(t, { settings: { runs: 1 } });
  w1.issue(10);
  w1.issue(11);
  const alerts1 = [];
  let ready = true;
  const ports1 = { alert: async a => alerts1.push(a), agentReady: async () => ready };
  await w1.tick(ports1);
  assert.ok(w1.job(10, 'build'));
  ready = false;
  w1.say(10, 'build', JSON.stringify({ type: 'error', message: 'API Error: 401 Unauthorized (oauth access token is invalid)' }));
  w1.finish(10, 'build', { code: 1 });
  await w1.tick(ports1);

  const m1 = readMachineState(w1);
  assert.ok(m1.poolOut && Number.isFinite(m1.poolOut.resetAt) && m1.poolOut.resetAt > w1.now(), 'poolOut sets concrete future resetAt');
  assert.equal(m1.streak, 0, 'terminal auth park does not burn streak strikes');
  assert.equal(alerts1.length, 1, 'emits one deduplicated usage-limit alert');

  // Subsequent ticks while parked never claim #11 or spin into retry storms.
  for (let i = 0; i < 5; i++) {
    w1.advance(5 * MIN);
    const held = await w1.tick(ports1);
    assert.match(held.message, /every login in the pool is exhausted until/);
    assert.equal(w1.job(11, 'build'), undefined, 'no issue claimed while parked');
  }

  // Once cooldown elapses and agentReady returns true, park clears and #11 starts cleanly.
  ready = true;
  w1.advance(30 * MIN);
  await w1.tick(ports1);
  assert.equal(readMachineState(w1).poolOut, null, 'poolOut clears once agentReady recovers');
  assert.ok(w1.job(10, 'build') || w1.job(11, 'build'), 'resumes claiming after recovery');

  // 2. Phase-PR repair and review hitting zero-quota / exhaustLogin() => null park PR immediately with 0 burned repair/review strikes.
  const w2 = await coreWorld(t, { settings: { runs: 1, maxRepairs: 2 } });
  w2.issue(20);
  await w2.tick();
  w2.build(20, { body: 'Fixes #20\n\nRuntime: not run (no prompt)', result: { promptChanged: false } });
  await w2.tick();
  assert.ok(w2.job(20, 'review'));
  w2.say(20, 'review', JSON.stringify({ type: 'error', message: 'Zero quota: 0 remaining quota for this account' }));
  w2.finish(20, 'review', { code: 1 });
  await w2.tick({ selectLogin: async () => ({ state: 'exhausted', resetAt: null }), exhaustLogin: async () => null });

  const parkedJob = readJobFile(w2, 20);
  assert.equal(parkedJob.stepStop?.poolExhausted, true, 'PR paused via poolExhausted');
  assert.equal(parkedJob.stepStop?.code, 'pool-exhausted');
  assert.equal(parkedJob.review, null, 'review attempt rolled back cleanly');
  const m2 = readMachineState(w2);
  assert.ok(Number.isFinite(m2.poolOut?.resetAt) && m2.poolOut.resetAt > w2.now(), 'null provider resetAt falls back to concrete future cooldown');
  assert.equal(m2.streak, 0, 'zero streak strikes burned on PR park');
});

test('P0-9B: --issues / --issue allowlist filters launcher start/status, core readyRows, and intakeRows with 4-part error diagnostics', async t => {
  // Invalid allowlist returns exit 2 with 4-part agent-teaching diagnostic before touching state.
  const badRes = await runAutopilotLauncher({ command: 'start', cwd: REPO_ROOT, packageRoot: REPO_ROOT, issues: ['abc'] });
  assert.equal(badRes.exitCode, 2);
  assert.match(badRes.message, /Invariant:/);
  assert.match(badRes.message, /Fix:/);
  assert.match(badRes.message, /Rerun:/);

  // Launcher start with --issues works WITHOUT --label, persists allowedIssues, surfaces in status + JSON, and clears with off.
  const dir = mkdtempSync(join(tmpdir(), 'pdd-allowlist-launcher-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = join(dir, 'repo'), home = join(dir, 'home');
  mkdirSync(cwd); mkdirSync(home);
  // Deliberately omit autopilot.label in pdd.json to prove --issues satisfies opt-in scope.
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: ['helper'] } }));
  let timerActive = false;
  const launcherPorts = {
    ...healthyMachine,
    checkCapacityPorts: isolatedCheckCapacity(dir),
    stateRoot: join(home, 'state'),
    now: () => Date.parse('2026-11-20T00:00:00Z'),
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }),
    pathDiagnostic: () => [],
    doctorPorts: healthyDoctorPorts(cwd),
    run: async (command, args) => {
      if (command === 'git') return { code: 0, stdout: (args.includes('--git-common-dir') ? join(cwd, '.git') : cwd) + '\n', stderr: '' };
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"acme/app","defaultBranchRef":{"name":"main"},"url":"https://github.com/acme/app"}', stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      return { code: 0, stdout: '{}', stderr: '' };
    },
    timer: async action => {
      if (action === 'start') timerActive = true;
      if (action === 'stop') timerActive = false;
      return timerActive;
    },
    queryIssues: async () => ({ status: 200, etag: '"e1"', issues: [] }),
  };

  const started = await runAutopilotLauncher(
    { command: 'start', cwd, packageRoot: REPO_ROOT, env: { HOME: home, PATH: process.env.PATH }, issues: ['#45, 42, 45'] },
    launcherPorts,
  );
  assert.equal(started.exitCode, 0, started.message);
  assert.match(started.message, /only issues #42, #45/);

  const statusText = await runAutopilotLauncher(
    { command: 'status', cwd, packageRoot: REPO_ROOT, env: { HOME: home, PATH: process.env.PATH } },
    launcherPorts,
  );
  assert.equal(statusText.exitCode, 0);
  assert.match(statusText.message, /only issues #42, #45/);
  assert.doesNotMatch(statusText.message, /No opt-in label/);

  const statusJson = await runAutopilotLauncher(
    { command: 'status', json: true, cwd, packageRoot: REPO_ROOT, env: { HOME: home, PATH: process.env.PATH } },
    launcherPorts,
  );
  assert.equal(statusJson.exitCode, 0);
  const parsedJson = JSON.parse(statusJson.message);
  assert.deepEqual(parsedJson.repositories[0].allowedIssues, [42, 45]);

  // Clear allowlist with --issues off + --label pdd:autopilot
  const cleared = await runAutopilotLauncher(
    { command: 'start', cwd, packageRoot: REPO_ROOT, env: { HOME: home, PATH: process.env.PATH }, label: 'pdd:autopilot', issues: ['off'] },
    launcherPorts,
  );
  assert.equal(cleared.exitCode, 0, cleared.message);
  assert.doesNotMatch(cleared.message, /only issues #42/);

  // Core intake and intakeRows strictly filter to allowedIssues.
  const w = await coreWorld(t, { settings: { runs: 2, label: null, labelRequired: true, allowedIssues: [42, 45] } });
  w.issue(41, { labels: [] });
  w.issue(42, { labels: [] });
  w.issue(43, { labels: [] });
  w.issue(45, { labels: [] });
  await w.tick();
  assert.equal(w.job(41, 'build'), undefined, '#41 is excluded by allowlist');
  assert.equal(w.job(43, 'build'), undefined, '#43 is excluded by allowlist');
  assert.ok(w.job(42, 'build'), '#42 is claimed from allowlist');
  assert.ok(w.job(45, 'build'), '#45 is claimed from allowlist');

  const filtered = intakeRows(
    [{ number: 41, state: 'open' }, { number: 42, state: 'open' }, { number: 45, state: 'open' }],
    null,
    [42, 45],
  );
  assert.deepEqual(filtered.map(r => r.number), [42, 45]);
});

test('P0-9C: test-suite-queue has zero workflow-runner import, passes toolchain/PDD_TEST_ENV vars, logs SIGTERM diagnostics, and core uses direct test-suite-entry.mjs', async t => {
  // 1. Verify test-suite-queue.mjs has zero static or dynamic import of workflow-runner.mjs and local lock works.
  const queueSrc = readFileSync(join(REPO_ROOT, 'src/test-suite-queue.mjs'), 'utf8');
  assert.equal(/workflow-runner\.mjs/.test(queueSrc), false, 'test-suite-queue.mjs must not import workflow-runner.mjs');

  const dir = mkdtempSync(join(tmpdir(), 'pdd-suite-p09c-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const queueDir = join(dir, 'queue'), repoDir = join(dir, 'repo'), stateDir = join(dir, 'state');
  mkdirSync(queueDir); mkdirSync(repoDir); mkdirSync(stateDir);

  // Verify self-contained acquireSuiteLock acquires, blocks busy, and recovers stale PID lock.
  const release = acquireSuiteLock(queueDir);
  assert.throws(() => acquireSuiteLock(queueDir), err => err.code === 'run_busy');
  release();
  writeFileSync(join(queueDir, 'suite-admission.lock'), JSON.stringify({ pid: 999999, token: 'dead-token' }));
  const releaseRecovered = acquireSuiteLock(queueDir);
  releaseRecovered();

  // 2. Verify toolchain & PDD_TEST_ENV_* pass-through while stripping credentials/agent env.
  const machine = checkMachine({ taskset: null });
  writeFileSync(join(queueDir, 'capacity.json'), JSON.stringify(withCheckLifetime(calculateCheckCapacity({ checks: 2 }, machine.ports))));
  let seenChildEnv = null;
  const env = {
    PATH: process.env.PATH,
    HOME: dir,
    PDD_SUITE_QUEUE: queueDir,
    PDD_STATE_DIR: stateDir,
    GOPATH: '/opt/gopath',
    CARGO_HOME: '/opt/cargo',
    RUSTUP_HOME: '/opt/rustup',
    VIRTUAL_ENV: '/opt/venv',
    PDD_TEST_ENV_MODE: 'sandbox',
    PDD_TEST_ENV_PORT: '5432',
    OPENAI_API_KEY: 'sk-must-not-leak',
    CODEX_HOME: '/tmp/must-not-leak',
    BASH_ENV: '/tmp/must-not-leak-hook',
  };
  const passRes = await runTestSuite({ cwd: repoDir, command: 'echo ok', env }, {
    ...machine.ports,
    say: () => {},
    execute: async (_cmd, opts) => { seenChildEnv = opts.env; opts.onChild(process.pid); return { exitCode: 0 }; },
  });
  assert.equal(passRes.exitCode, 0);
  assert.equal(seenChildEnv.GOPATH, '/opt/gopath');
  assert.equal(seenChildEnv.CARGO_HOME, '/opt/cargo');
  assert.equal(seenChildEnv.RUSTUP_HOME, '/opt/rustup');
  assert.equal(seenChildEnv.VIRTUAL_ENV, '/opt/venv');
  assert.equal(seenChildEnv.PDD_TEST_ENV_MODE, 'sandbox');
  assert.equal(seenChildEnv.PDD_TEST_ENV_PORT, '5432');
  assert.equal(seenChildEnv.OPENAI_API_KEY, undefined);
  assert.equal(seenChildEnv.CODEX_HOME, undefined);
  assert.equal(seenChildEnv.BASH_ENV, undefined);

  // 3. Verify SIGTERM while waiting persists structured signalDiagnostics & emits Signal diagnostic line.
  const queue2 = join(dir, 'queue2'), repoWait = join(dir, 'repo-wait');
  mkdirSync(queue2); mkdirSync(repoWait);
  writeFileSync(join(queue2, 'capacity.json'), JSON.stringify(withCheckLifetime(calculateCheckCapacity({ checks: 1 }, machine.ports))));
  let releaseBlocker;
  const env2 = { PATH: process.env.PATH, HOME: dir, PDD_SUITE_QUEUE: queue2, PDD_STATE_DIR: stateDir };
  const blocker = runTestSuite({ cwd: repoDir, command: 'block', env: env2 }, {
    ...machine.ports,
    say: () => {},
    execute: async (_cmd, opts) => {
      opts.onChild(process.pid);
      await new Promise(r => { releaseBlocker = r; });
      return { exitCode: 0 };
    },
  });
  for (let i = 0; i < 100 && !releaseBlocker; i++) await new Promise(r => setTimeout(r, 10));
  const fakeSignals = new EventEmitter();
  const said = [];
  const waiterPromise = runTestSuite({ cwd: repoWait, command: 'wait-cmd', env: env2 }, {
    ...machine.ports,
    signals: fakeSignals,
    say: line => said.push(line),
    execute: async () => ({ exitCode: 0 }),
  });
  for (let i = 0; i < 100 && !said.some(line => line.includes('waiting for a check slot')); i++) await new Promise(r => setTimeout(r, 10));
  fakeSignals.emit('SIGTERM');
  const waitRes = await waiterPromise;
  releaseBlocker();
  await blocker;

  assert.equal(waitRes.exitCode, 143);
  assert.equal(waitRes.signal, 'SIGTERM');
  assert.ok(said.some(line => /^Signal diagnostic: signal=SIGTERM exit=143 phase=waiting source=process-signal /.test(line)), said.join('\n'));
  const progress = readSuiteProgress({ cwd: repoWait, env: env2 });
  assert.equal(progress.signal, 'SIGTERM');
  assert.equal(progress.signalDiagnostics?.signal, 'SIGTERM');
  assert.equal(progress.signalDiagnostics?.phase, 'waiting');
  assert.equal(progress.signalDiagnostics?.exitCode, 143);

  // 4. Direct src/test-suite-entry.mjs CLI invocation works without pdd workflow suite.
  const entryPath = join(REPO_ROOT, 'src/test-suite-entry.mjs');
  const runChild = args => new Promise((done, fail) => {
    const child = spawn(process.execPath, [entryPath, ...args], { cwd: repoDir, env: env2, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '', stderr = '';
    child.stdout.on('data', d => stdout += d);
    child.stderr.on('data', d => stderr += d);
    child.once('error', fail);
    child.once('close', code => done({ code, stdout, stderr }));
  });
  const okChild = await runChild(['suite', '--command', `${JSON.stringify(process.execPath)} -e "console.log('direct-suite-ok')"`, '--timeout', '1']);
  assert.equal(okChild.code, 0, okChild.stderr);
  assert.match(okChild.stdout, /direct-suite-ok/);
  const badChild = await runChild(['suite']);
  assert.equal(badChild.code, 2);
  assert.match(badChild.stderr, /Invariant:/);

  // 5. Autopilot core spawns src/test-suite-entry.mjs suite (not bin/pdd.mjs workflow suite).
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(30);
  await w.tick();
  w.build(30, { body: 'Fixes #30\n\nRuntime: not run (no prompt)', result: { promptChanged: false } });
  await w.tick();
  const suiteJob = w.job(30, 'suite');
  assert.ok(suiteJob);
  assert.match(suiteJob.args[0], /test-suite-entry\.mjs$/);
  assert.deepEqual(suiteJob.args.slice(-5), ['suite', '--command', 'npm test', '--timeout', '0']);
  assert.equal(suiteJob.args.includes('workflow'), false, 'core suite must not depend on pdd workflow suite');
});
