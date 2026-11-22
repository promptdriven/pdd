import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readdirSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { machineCheckPorts } from '../src/machine-resources.mjs';
import { calculateCheckCapacity, configureCheckCapacity, readCheckStatus, runTestSuite } from '../src/test-suite-queue.mjs';
import { chatCommand, chatLaunch } from '../src/workflow-chat.mjs';
import { checkMachine, GiB } from './helpers/check-machine.mjs';

const until = async (predicate, label = 'queue state') => {
  for (let i = 0; i < 1000; i++) {
    if (predicate()) return;
    await new Promise(done => setTimeout(done, 2));
  }
  assert.fail(`Timed out waiting for ${label}`);
};

function makeMacPorts({ count = 16, freeGiB = 24, load = 0, pressure = 1, env = {}, sysctl } = {}) {
  const { ports } = checkMachine({ count, free: freeGiB * GiB, load, platform: 'darwin', taskset: null });
  return {
    ...ports,
    env,
    ...(sysctl !== undefined ? { sysctl } : { memoryPressure: () => pressure }),
  };
}

function makeTempDir(t, prefix = 'pdd-macos-suite-3615-') {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), prefix)));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

test('#3615: machineCheckPorts exposes memoryPressure on darwin via memoryPressure or sysctl and returns null elsewhere', () => {
  assert.equal(machineCheckPorts({}, { platform: 'darwin', sysctl: () => '1\n' }).memoryPressure(), 1);
  assert.equal(machineCheckPorts({}, { platform: 'darwin', sysctl: () => '2\n' }).memoryPressure(), 2);
  assert.equal(machineCheckPorts({}, { platform: 'darwin', sysctl: () => '4' }).memoryPressure(), 4);
  assert.equal(machineCheckPorts({}, { platform: 'darwin', sysctl: () => 'invalid' }).memoryPressure(), null);
  assert.equal(machineCheckPorts({}, { platform: 'darwin', sysctl: () => { throw Error('no sysctl'); } }).memoryPressure(), null);
  assert.equal(machineCheckPorts({}, { platform: 'darwin', memoryPressure: () => 2 }).memoryPressure(), 2);
  assert.equal(machineCheckPorts({}, { platform: 'linux', sysctl: () => '4' }).memoryPressure(), null);
  assert.equal(machineCheckPorts({}, { platform: 'linux', memoryPressure: () => 4 }).memoryPressure(), null);
});

test('#3615: macOS default stays 1 when no override is configured across 16-64 GiB and 10-24 cores', () => {
  for (const [count, freeGiB] of [[10, 12], [10, 16], [16, 32], [24, 64]]) {
    let pressureCalled = false;
    const ports = makeMacPorts({ count, freeGiB, env: {} });
    ports.memoryPressure = () => { pressureCalled = true; return 1; };
    const got = calculateCheckCapacity({}, ports);
    assert.equal(got.personal, true);
    assert.equal(got.affinity, false);
    assert.equal(got.calculatedChecks, 1);
    assert.equal(got.checks, 1, `macOS default must remain 1 for ${count} cores / ${freeGiB} GiB`);
    assert.equal(got.usableCores, Math.max(1, Math.floor(count / 2)));
    assert.equal(got.coresPerCheck, got.usableCores);
    assert.equal(pressureCalled, false, 'default macOS path should not probe sysctl unnecessarily');
  }
});

test('#3615: PDD_SUITE_CONCURRENCY=4 on 32 GiB / 16-core macOS allows 4 slots and runs concurrent suites without taskset', async t => {
  const ports = makeMacPorts({ count: 16, freeGiB: 24, pressure: 1, env: { PDD_SUITE_CONCURRENCY: '4' } });
  const got = calculateCheckCapacity({}, ports);
  assert.equal(got.usableCores, 8);
  assert.equal(got.calculatedChecks, 1);
  assert.equal(got.checks, 4);
  assert.equal(got.runs, 8);
  assert.equal(got.coresPerCheck, 2);

  // Verify two+ runTestSuite tickets actually execute simultaneously on macOS without taskset.
  const root = makeTempDir(t);
  const queueDir = join(root, 'queue');
  const homeDir = join(root, 'home');
  mkdirSync(queueDir, { recursive: true });
  mkdirSync(homeDir, { recursive: true });
  const env = { HOME: homeDir, PDD_SUITE_QUEUE: queueDir, PDD_SUITE_CONCURRENCY: '4' };
  const calls = [];
  const jobs = [];
  let stop = false;
  const runPorts = {
    ...makeMacPorts({ count: 16, freeGiB: 24, pressure: 1, env }),
    now: () => 10_000,
    alive: () => true,
    say: () => {},
    sleep: () => new Promise(done => setTimeout(done, 2)),
    source: () => ({ head: null, fingerprint: null, runId: null, issue: null, error: null }),
    execute: async (command, options) => {
      const call = { command, options };
      calls.push(call);
      options.onChild(200 + calls.length);
      if (stop) return { exitCode: 0 };
      return new Promise(done => { call.finish = () => done({ exitCode: 0 }); });
    },
  };
  t.after(async () => {
    stop = true;
    for (const c of calls) c.finish?.();
    await Promise.all(jobs);
  });

  const readTickets = () =>
    readdirSync(queueDir)
      .filter(name => /^ticket-.*\.json$/.test(name))
      .map(name => JSON.parse(readFileSync(join(queueDir, name), 'utf8')));

  for (let i = 0; i < 5; i++) {
    const repoDir = join(root, `repo-${i}`);
    mkdirSync(repoDir, { recursive: true });
    jobs.push(runTestSuite({ cwd: repoDir, command: `suite-${i}`, env }, runPorts));
    await until(() => readTickets().length === i + 1, `ticket ${i + 1}`);
  }
  await until(() => calls.length === 4, '4 concurrent macOS suites running');
  await new Promise(done => setTimeout(done, 20));
  assert.equal(calls.length, 4, 'exactly 4 suites should run concurrently on 4-slot macOS opt-in');
  const runningTickets = readTickets().filter(r => r.state === 'running');
  assert.equal(runningTickets.length, 4);
  for (const call of calls) {
    assert.equal(call.options.taskset, null);
    assert.deepEqual(call.options.cpuIds, []);
    assert.equal(call.options.env.PDD_CHECK_CPUS, '2');
    assert.equal(call.options.env.PDD_SUITE_CONCURRENCY, undefined, 'clean-v1 must strip PDD_SUITE_CONCURRENCY from child env');
  }
  const status = readCheckStatus({ env }, runPorts);
  assert.equal(status.checks, 4);
  assert.equal(status.busyChecks, 4);
  assert.equal(status.waitingChecks, 1);

  calls[0].finish();
  await until(() => calls.length === 5, '5th queued suite starts once a slot frees');
  stop = true;
  for (const c of calls) c.finish?.();
  assert.deepEqual((await Promise.all(jobs)).map(r => r.exitCode), [0, 0, 0, 0, 0]);
});

test('#3615: RAM, macOS VM memory pressure, core, and opt-down ceilings clamp opt-in overrides safely', () => {
  // RAM ceiling: 10 GiB free -> floor(10/4) = 2.
  const ramCapped = calculateCheckCapacity({}, makeMacPorts({
    count: 16, freeGiB: 10, pressure: 1, env: { PDD_SUITE_CONCURRENCY: '8' },
  }));
  assert.equal(ramCapped.checks, 2);
  assert.equal(ramCapped.coresPerCheck, 4);

  // Very low free RAM (< 4 GiB) clamps to 1 (never 0).
  const lowRam = calculateCheckCapacity({}, makeMacPorts({
    count: 16, freeGiB: 2, pressure: 1, env: { PDD_SUITE_CONCURRENCY: '4' },
  }));
  assert.equal(lowRam.checks, 1);

  // macOS VM memory pressure: 2 (warning) and 4 (critical) clamp to 1 even with 64 GiB free!
  for (const level of [2, 4]) {
    const pressured = calculateCheckCapacity({}, makeMacPorts({
      count: 24, freeGiB: 64, pressure: level, env: { PDD_SUITE_CONCURRENCY: '4' },
    }));
    assert.equal(pressured.checks, 1, `pressure ${level} must clamp macOS opt-in concurrency to 1`);
    assert.equal(pressured.coresPerCheck, 12);

    const viaSysctl = calculateCheckCapacity({}, makeMacPorts({
      count: 24, freeGiB: 64, sysctl: () => `${level}\n`, env: { PDD_SUITE_CONCURRENCY: '4' },
    }));
    assert.equal(viaSysctl.checks, 1, `sysctl pressure ${level} must clamp macOS opt-in concurrency to 1`);
  }

  // Normal (1) and unavailable (null) pressure allow RAM & core ceiling.
  for (const pressure of [1, null]) {
    const ok = calculateCheckCapacity({}, makeMacPorts({
      count: 24, freeGiB: 64, pressure, env: { PDD_SUITE_CONCURRENCY: '4' },
    }));
    assert.equal(ok.checks, 4, `pressure ${String(pressure)} should permit 4 slots`);
    assert.equal(ok.coresPerCheck, 3);
  }

  // Invalid injected memoryPressure fails closed.
  for (const bad of [-1, 1.5, NaN, 'warn', true]) {
    assert.throws(
      () => calculateCheckCapacity({}, makeMacPorts({
        count: 16, freeGiB: 32, pressure: bad, env: { PDD_SUITE_CONCURRENCY: '2' },
      })),
      /Machine check capacity is unavailable or invalid/,
      `invalid memoryPressure ${String(bad)} must fail closed`,
    );
  }

  // Core ceiling: 10-core macOS -> 5 usable cores; override=16 clamps to 5, coresPerCheck=1.
  const coreCapped = calculateCheckCapacity({}, makeMacPorts({
    count: 10, freeGiB: 64, pressure: 1, env: { PDD_SUITE_CONCURRENCY: '16' },
  }));
  assert.equal(coreCapped.usableCores, 5);
  assert.equal(coreCapped.checks, 5);
  assert.equal(coreCapped.coresPerCheck, 1);

  // Opt-down on high-core Linux VM: calculated=5, PDD_SUITE_CONCURRENCY=1 clamps down to 1!
  const { ports: linuxPorts } = checkMachine({ count: 64, free: 128 * GiB, platform: 'linux', battery: false, virtualized: true, taskset: '/fake/taskset' });
  const optedDown = calculateCheckCapacity({}, { ...linuxPorts, env: { PDD_SUITE_CONCURRENCY: '1' } });
  assert.equal(optedDown.calculatedChecks, 5);
  assert.equal(optedDown.checks, 1);
  assert.equal(optedDown.coresPerCheck, 64);
});

test('#3615: pdd.json suite.checks works from subdirs, PDD_SUITE_CONCURRENCY wins, search stops at .git, and symlinked pdd.json fails closed', t => {
  const outer = makeTempDir(t);
  // Put a decoy pdd.json OUTSIDE the git repo to verify upward walk stops at .git!
  writeFileSync(join(outer, 'pdd.json'), JSON.stringify({ suite: { checks: 7 } }));

  const repoWithoutConfig = join(outer, 'repo-no-config');
  const subdirNoConfig = join(repoWithoutConfig, 'packages', 'app');
  mkdirSync(join(repoWithoutConfig, '.git'), { recursive: true });
  mkdirSync(subdirNoConfig, { recursive: true });

  const noLeak = calculateCheckCapacity({ cwd: subdirNoConfig }, makeMacPorts({ count: 24, freeGiB: 64, pressure: 1, env: {} }));
  assert.equal(noLeak.checks, 1, 'pdd.json search must stop at .git and never read parent directory outside repo');

  // Linked worktree (.git as a file) must also stop the upward walk.
  const linkedWorktree = join(outer, 'linked-wt');
  const linkedSub = join(linkedWorktree, 'src');
  mkdirSync(linkedSub, { recursive: true });
  writeFileSync(join(linkedWorktree, '.git'), 'gitdir: ../repo-no-config/.git/worktrees/wt\n');
  const linkedNoLeak = calculateCheckCapacity({ cwd: linkedSub }, makeMacPorts({ count: 24, freeGiB: 64, pressure: 1, env: {} }));
  assert.equal(linkedNoLeak.checks, 1, 'pdd.json search must stop at .git worktree file');

  // Repo with valid pdd.json suite.checks = 3 discovered from nested subdir (and symlinked subdir).
  const repo = join(outer, 'repo-with-config');
  const nested = join(repo, 'src', 'deep');
  mkdirSync(join(repo, '.git'), { recursive: true });
  mkdirSync(nested, { recursive: true });
  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'observe' }, suite: { checks: 3 } }));
  const symlinkSubdir = join(outer, 'nested-link');
  symlinkSync(nested, symlinkSubdir);

  const fromSubdir = calculateCheckCapacity({ cwd: nested }, makeMacPorts({ count: 16, freeGiB: 24, pressure: 1, env: {} }));
  assert.equal(fromSubdir.checks, 3);
  assert.equal(fromSubdir.coresPerCheck, 2);

  const fromSymlinkCwd = calculateCheckCapacity({ cwd: symlinkSubdir }, makeMacPorts({ count: 16, freeGiB: 24, pressure: 1, env: {} }));
  assert.equal(fromSymlinkCwd.checks, 3);

  // readCheckStatus threads cwd for pdd.json discovery when no capacity.json is present.
  const queueDir = join(outer, 'status-queue');
  mkdirSync(queueDir, { recursive: true });
  const statusFromRepo = readCheckStatus(
    { env: { PDD_SUITE_QUEUE: queueDir }, cwd: nested },
    makeMacPorts({ count: 16, freeGiB: 24, pressure: 1, env: { PDD_SUITE_QUEUE: queueDir } }),
  );
  assert.equal(statusFromRepo.checks, 3);

  // PDD_SUITE_CONCURRENCY overrides pdd.json suite.checks.
  const envWins = calculateCheckCapacity({ cwd: nested }, makeMacPorts({
    count: 16, freeGiB: 24, pressure: 1, env: { PDD_SUITE_CONCURRENCY: '5' },
  }));
  assert.equal(envWins.checks, 5);

  // Empty or whitespace-only PDD_SUITE_CONCURRENCY falls back to pdd.json (and default when absent).
  for (const blank of ['', '   ', '\t\n']) {
    const fallbackRepo = calculateCheckCapacity({ cwd: nested }, makeMacPorts({
      count: 16, freeGiB: 24, pressure: 1, env: { PDD_SUITE_CONCURRENCY: blank },
    }));
    assert.equal(fallbackRepo.checks, 3, `blank PDD_SUITE_CONCURRENCY ${JSON.stringify(blank)} should fall back to pdd.json`);
    const fallbackDefault = calculateCheckCapacity({ cwd: subdirNoConfig }, makeMacPorts({
      count: 16, freeGiB: 24, pressure: 1, env: { PDD_SUITE_CONCURRENCY: blank },
    }));
    assert.equal(fallbackDefault.checks, 1);
  }

  // Symlinked pdd.json fails closed.
  const symlinkRepo = join(outer, 'repo-symlink-config');
  mkdirSync(join(symlinkRepo, '.git'), { recursive: true });
  symlinkSync(join(repo, 'pdd.json'), join(symlinkRepo, 'pdd.json'));
  assert.throws(
    () => calculateCheckCapacity({ cwd: symlinkRepo }, makeMacPorts({ count: 16, freeGiB: 24, pressure: 1, env: {} })),
    /symbolic links are not allowed/i,
  );
});

test('#3615: invalid PDD_SUITE_CONCURRENCY and invalid/malformed pdd.json fail closed', async t => {
  for (const bad of ['0', '-1', '-2', '1.5', 'abc', '2foo', '+2', 'NaN', '9007199254740992']) {
    assert.throws(
      () => calculateCheckCapacity({}, makeMacPorts({ env: { PDD_SUITE_CONCURRENCY: bad } })),
      /Invalid PDD_SUITE_CONCURRENCY: must be a positive integer/,
      `PDD_SUITE_CONCURRENCY=${JSON.stringify(bad)} must fail closed`,
    );
  }

  const root = makeTempDir(t);
  const badConfigs = [
    ['zero', JSON.stringify({ suite: { checks: 0 } }), /Invalid pdd\.json suite\.checks: must be a positive integer/],
    ['negative', JSON.stringify({ suite: { checks: -3 } }), /Invalid pdd\.json suite\.checks: must be a positive integer/],
    ['string', JSON.stringify({ suite: { checks: '2' } }), /Invalid pdd\.json suite\.checks: must be a positive integer/],
    ['float', JSON.stringify({ suite: { checks: 1.5 } }), /Invalid pdd\.json suite\.checks: must be a positive integer/],
    ['boolean', JSON.stringify({ suite: { checks: true } }), /Invalid pdd\.json suite\.checks: must be a positive integer/],
    ['null-suite', JSON.stringify({ suite: null }), /Invalid pdd\.json suite\.checks: must be a positive integer/],
    ['malformed', '{not json', /Invalid JSON in pdd\.json/],
  ];
  for (const [name, content, pattern] of badConfigs) {
    const repo = join(root, name);
    mkdirSync(join(repo, '.git'), { recursive: true });
    writeFileSync(join(repo, 'pdd.json'), content);
    assert.throws(
      () => calculateCheckCapacity({ cwd: repo }, makeMacPorts({ env: {} })),
      pattern,
      `bad pdd.json (${name}) must fail closed`,
    );
  }

  // runTestSuite also fails closed without executing the command when PDD_SUITE_CONCURRENCY is invalid.
  const queueDir = join(root, 'bad-env-queue');
  const homeDir = join(root, 'bad-env-home');
  mkdirSync(queueDir, { recursive: true });
  mkdirSync(homeDir, { recursive: true });
  let executed = 0;
  const res = await runTestSuite(
    { cwd: root, command: 'never-run', env: { HOME: homeDir, PDD_SUITE_QUEUE: queueDir, PDD_SUITE_CONCURRENCY: '0' } },
    {
      ...makeMacPorts({ env: { HOME: homeDir, PDD_SUITE_QUEUE: queueDir, PDD_SUITE_CONCURRENCY: '0' } }),
      say: () => {},
      source: () => ({ head: null, fingerprint: null, runId: null, issue: null, error: null }),
      execute: async () => { executed++; return { exitCode: 0 }; },
    },
  );
  assert.equal(res.exitCode, 1);
  assert.equal(executed, 0);
  assert.match(res.message, /Invalid PDD_SUITE_CONCURRENCY/);
});

test('#3615: saved capacity.json revalidation stays valid when PDD_SUITE_CONCURRENCY is set in env', async t => {
  const root = makeTempDir(t);
  const queueDir = join(root, 'queue');
  mkdirSync(queueDir, { recursive: true });
  const baseEnv = { PDD_SUITE_QUEUE: queueDir };
  const ports = { ...makeMacPorts({ count: 16, freeGiB: 24, pressure: 1, env: baseEnv }), now: () => 50_000 };

  const saved = await configureCheckCapacity({ env: baseEnv, checks: 2, runs: 4, owner: 'autopilot-owner' }, ports);
  assert.equal(saved.checks, 2);

  // Reading status with PDD_SUITE_CONCURRENCY=4 (or even invalid) must revalidate and honor unexpired capacity.json!
  const withEnv = { PDD_SUITE_QUEUE: queueDir, PDD_SUITE_CONCURRENCY: '4' };
  const status = readCheckStatus({ env: withEnv, cwd: root }, { ...ports, env: withEnv });
  assert.equal(status.checks, 2, 'active unexpired capacity.json must win over PDD_SUITE_CONCURRENCY');
  assert.equal(status.runs, 4);

  // Once capacity.json expires, admission/status falls back to PDD_SUITE_CONCURRENCY=4 on macOS.
  const expiredStatus = readCheckStatus(
    { env: withEnv, cwd: root },
    { ...ports, env: withEnv, now: () => saved.expiresAt },
  );
  assert.equal(expiredStatus.checks, 4, 'expired capacity.json should fall back to opt-in PDD_SUITE_CONCURRENCY');
});

test('#3615: workflow-chat forwards PDD_SUITE_CONCURRENCY into worker panes and unsets it when absent', t => {
  const root = makeTempDir(t);
  const bin = join(root, 'bin');
  const cwd = join(root, 'worktree');
  mkdirSync(bin, { recursive: true });
  mkdirSync(cwd, { recursive: true });
  for (const agent of ['codex', 'claude', 'gemini', 'agy']) {
    writeFileSync(
      join(bin, agent),
      `#!${process.execPath}\nprocess.stdout.write(JSON.stringify({ conc: process.env.PDD_SUITE_CONCURRENCY ?? null, argv: process.argv.slice(2) }));\n`,
      { mode: 0o755 },
    );
  }

  // Forward when caller sets PDD_SUITE_CONCURRENCY.
  for (const agent of ['codex', 'claude', 'gemini', 'agy']) {
    const launch = chatLaunch({ run: { runDir: root, root: cwd }, agent, env: { PDD_SUITE_CONCURRENCY: '4' } });
    assert.equal(launch.queueEnv.PDD_SUITE_CONCURRENCY, '4');
    const line = chatCommand({ agent, cwd, ...launch });
    const actual = JSON.parse(execFileSync('/bin/sh', ['-c', line], { env: { PATH: `${bin}:/usr/bin:/bin` }, encoding: 'utf8' }));
    assert.equal(actual.conc, '4', `${agent} pane must receive caller PDD_SUITE_CONCURRENCY`);
    if (agent === 'codex') {
      assert.ok(actual.argv.includes('shell_environment_policy.set.PDD_SUITE_CONCURRENCY="4"'));
    }
  }

  // Unset when caller omits PDD_SUITE_CONCURRENCY so stale Herdr server env cannot leak.
  for (const agent of ['codex', 'claude', 'gemini', 'agy']) {
    const launch = chatLaunch({ run: { runDir: root, root: cwd }, agent, env: {} });
    assert.equal(launch.queueEnv.PDD_SUITE_CONCURRENCY, undefined);
    assert.ok(launch.unset.includes('PDD_SUITE_CONCURRENCY'));
    const line = chatCommand({ agent, cwd, ...launch });
    const actual = JSON.parse(
      execFileSync('/bin/sh', ['-c', line], { env: { PATH: `${bin}:/usr/bin:/bin`, PDD_SUITE_CONCURRENCY: '8' }, encoding: 'utf8' }),
    );
    assert.equal(actual.conc, null, `${agent} pane must unset stale server PDD_SUITE_CONCURRENCY`);
  }
});
