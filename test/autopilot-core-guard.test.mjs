// #3231: the core uses the machine guard: the machine's --runs reaches the tick, the room check holds intake with a
// reason, every job gets the guard's priority and PDD_CHECK_CPUS, and old files go.
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, readdirSync, truncateSync, utimesSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { coreWorld } from './helpers/core-world.mjs';
import { coreStatus } from '../src/autopilot-core.mjs';
import { readMachineGuard } from '../src/machine-guard.mjs';
import { tickAutopilot, runAutopilotLauncher } from '../src/autopilot-launcher.mjs';

const MIN = 60 * 1000, DAY = 24 * 60 * MIN, GiB = 1024 ** 3, MiB = 1024 ** 2;
const room = reason => ({ room: reason ? { ok: false, reason } : { ok: true, reason: null }, priority: () => ({ nice: 19, qos: 'utility', cpus: null, taskset: null, checkCpus: 5 }) });

test('T2 the machine --runs reaches a core tick through the launcher: 3 ready issues, runs 1, one claim', async t => {
  const w = await coreWorld(t);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], engine: 'core', testCommand: 'npm test' } }));
  for (const n of [17, 18, 19]) w.issue(n);
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel'), stateRoot = join(w.dir, 'state');
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
  mkdirSync(stateRoot, { recursive: true });
  writeFileSync(stateFile, JSON.stringify({ enabled: true, cwd, repo: 'acme/widgets', defaultBranch: 'main', coordinatorId: 'coord-a', machine: 'machine-a', runs: 1,
    agent: { id: 'codex', kind: 'codex', command: 'codex' }, packageRoot: join(w.dir, 'pkg') }));
  // A big server (4 automatic slots) whose start said --runs 1.
  const server = { cpuCount: 64, load: 1, memory: { available: 200 * GiB, total: 251 * GiB }, pressure: { io: 0, memory: 0, level: null }, disk: { available: 500 * GiB, total: 1000 * GiB },
    power: null, cgroup: { cpus: null, memory: null }, check: { cpuIds: Array.from({ length: 64 }, (_, i) => i), platform: 'linux', battery: false, virtualized: true, taskset: '/usr/bin/taskset' } };
  const reads = [];
  const ports = { stateRoot, now: w.now, env: { HOME: process.env.HOME, PATH: process.env.PATH }, timer: async () => true, warn: () => {},
    machineGuard: input => { reads.push(input); return readMachineGuard(input, { machineResources: async () => server }); },
    run: async (command, args, options = {}) => {
      if (command === 'gh') return w.gh(args, options);
      const { spawnSync } = await import('node:child_process'); const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr };
    },
    corePorts: { jobs: w.jobs, checkBase: async () => ({ exitCode: 0, message: 'ok' }), agentReady: async () => true } };
  const result = await tickAutopilot(stateFile, ports);
  assert.match(result.message, /Autopilot core: 1 started.*1 of 1 slots busy/);
  assert.equal(w.started.filter(job => job.role === 'build').length, 1, 'one claim of 3 ready issues');
  assert.equal(reads[0].runs, 1, 'the saved --runs goes to the guard');
  const status = await runAutopilotLauncher({ command: 'status', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env }, ports);
  assert.match(status.message, /Jobs: 1 of 1 slots busy/);
  assert.match(status.message, /Machine: server · 64 cores, Autopilot uses 64 · .* · 1 slot \(this machine \(--runs 1\)\) · new work: ok/);
});

test('T9 no room: intake claims nothing and says why; running work goes on; with room again it claims', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  w.issue(17);
  await w.tick({ machine: room() });
  assert.ok(w.job(17, 'build'));
  w.issue(18);
  const held = await w.tick({ machine: room('on battery power') });
  assert.match(held.message, /intake held: on battery power/);
  assert.equal(w.job(18), undefined, 'no claim on battery');
  assert.deepEqual(w.stopped, [], 'the running build goes on');
  w.build(17);
  await w.tick({ machine: room('memory pressure') });
  assert.ok(w.job(17, 'review') && w.job(17, 'suite'), 'reviews and suites of running work start');
  const ac = await w.tick({ machine: room() });
  assert.doesNotMatch(ac.message, /intake held/);
  assert.ok(w.job(18, 'build'), 'on AC power the next issue starts');
});

test('every job gets the guard priority and PDD_CHECK_CPUS; the build brief names the worker count', async t => {
  const w = await coreWorld(t);
  w.issue(17);
  await w.tick({ machine: room() });
  const build = w.job(17, 'build');
  assert.deepEqual(build.priority, { nice: 19, qos: 'utility', cpus: null, taskset: null });
  assert.equal(build.env.PDD_CHECK_CPUS, '5');
  assert.match(build.input, /pass `\$PDD_CHECK_CPUS` as the worker count/);
  w.build(17); await w.tick({ machine: room() });
  for (const role of ['review', 'suite']) { assert.equal(w.job(17, role).env.PDD_CHECK_CPUS, '5', role); assert.equal(w.job(17, role).priority.nice, 19, role); }
  const plain = await coreWorld(t); plain.issue(17); await plain.tick();
  assert.equal(plain.job(17, 'build').priority, undefined, 'with no machine port the runner defaults apply');
});

test('T13 cleanup: orphan worktrees and old free logs go; a live job keeps its files; the 500 MiB cap removes the oldest first', async t => {
  const w = await coreWorld(t);
  w.issue(17);
  await w.tick();
  const logs = join(w.root, 'logs'), trees = join(w.root, 'worktrees'), old = (w.now() - 20 * DAY) / 1000;
  const file = (name, { age = old, size = 10 } = {}) => { const path = join(logs, name); writeFileSync(path, 'x'); truncateSync(path, size); utimesSync(path, age, age); return path; };
  // A live job's old log stays; another issue's old log and an orphan worktree go; a fresh free log stays.
  const live = file('17-build-old-aaaa.log'), stale = file('5-build-old-bbbb.log'), fresh = file('6-build-new-cccc.log', { age: w.now() / 1000 });
  mkdirSync(join(trees, '5-review'), { recursive: true }); mkdirSync(join(trees, '17-suite'), { recursive: true });
  await w.tick();
  assert.ok(existsSync(live), 'a live job keeps its files'); assert.ok(!existsSync(stale), 'an old free log goes'); assert.ok(existsSync(fresh), 'a fresh free log stays');
  assert.ok(!existsSync(join(trees, '5-review')), 'an orphan worktree goes'); assert.ok(existsSync(join(trees, '17-suite')) && existsSync(join(trees, '17')), 'a live job keeps its worktrees');
  // Over 500 MiB of free logs: the oldest go until the folder is under the cap.
  const a = file('7-build-a-dddd.log', { age: (w.now() - 3 * DAY) / 1000, size: 300 * MiB }), b = file('8-build-b-eeee.log', { age: (w.now() - 2 * DAY) / 1000, size: 300 * MiB });
  await w.tick();
  assert.ok(!existsSync(a), 'the oldest goes'); assert.ok(existsSync(b), 'the newer one stays under the cap'); assert.ok(existsSync(fresh));
  assert.ok(readdirSync(logs).some(name => name.startsWith('17-build-')), 'the live build log stays');
});

test('status shows the guard line from the launcher', async t => {
  const w = await coreWorld(t);
  const text = coreStatus({ state: w.state, settings: w.settings, guard: 'Machine: laptop · … · new work: held (on battery power)' }, { root: w.root, now: w.now });
  assert.match(text, /\nMachine: laptop · … · new work: held \(on battery power\)\n/);
  assert.doesNotMatch(coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now }), /Machine:/);
});
