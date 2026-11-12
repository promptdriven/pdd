// #3231: the core uses the machine guard: the machine's --runs reaches the tick, the room check holds intake with a
// reason, every job gets the guard's priority and PDD_CHECK_CPUS, and old files go.
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, readdirSync, truncateSync, utimesSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { coreWorld } from './helpers/core-world.mjs';
import { coreStatus } from '../src/autopilot-core.mjs';
import { readMachineGuard } from '../src/machine-guard.mjs';
import { tickAutopilot, runAutopilotLauncher } from '../src/autopilot-launcher.mjs';

const MIN = 60 * 1000, DAY = 24 * 60 * MIN, GiB = 1024 ** 3, MiB = 1024 ** 2;
const room = reason => ({ room: reason ? { ok: false, reason } : { ok: true, reason: null }, priority: () => ({ nice: 19, qos: 'utility', cpus: null, taskset: null, checkCpus: 5 }) });

test('T2 the machine --runs reaches a core tick through the launcher: 3 ready issues, runs 1, one claim', async t => {
  const w = await coreWorld(t);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], engine: 'core', testCommand: 'npm test' } }));
  // The opt-in label (#3242): a launcher tick takes only labeled issues.
  for (const n of [17, 18, 19]) w.issue(n, { labels: ['pdd:autopilot'] });
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel'), stateRoot = join(w.dir, 'state');
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
  mkdirSync(stateRoot, { recursive: true });
  writeFileSync(stateFile, JSON.stringify({ enabled: true, cwd, repo: 'acme/widgets', defaultBranch: 'main', coordinatorId: 'coord-a', machine: 'machine-a', runs: 1, share: 70, label: 'pdd:autopilot',
    agent: { id: 'codex', kind: 'codex', command: 'codex' }, packageRoot: join(w.dir, 'pkg') }));
  // A big machine (4 automatic slots at the default share of 50%) whose start said --runs 1 and --share 70.
  const server = { cpuCount: 64, load: 1, memory: { available: 200 * GiB, total: 251 * GiB }, pressure: { io: 0, memory: 0, level: null }, disk: { available: 500 * GiB, total: 1000 * GiB },
    cgroup: { cpus: null, memoryMax: null, memoryFree: null }, check: { cpuIds: Array.from({ length: 64 }, (_, i) => i), platform: 'linux', battery: false, virtualized: true, taskset: '/usr/bin/taskset' } };
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
  assert.equal(reads[0].runs, 1, 'the saved --runs goes to the guard'); assert.equal(reads[0].share, 70, 'and the saved --share');
  const status = await runAutopilotLauncher({ command: 'status', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env }, ports);
  assert.match(status.message, /Jobs: 1 of 1 slots busy/);
  assert.match(status.message, /Machine: share 70% \(this machine, --share\) of 64 cores and 251 GiB · slots min\(4, 44\.8 cores ÷ 2, 175\.7 GiB ÷ 3 GiB\) = 4 → 1 \(this machine, --runs 1\) · .* · new work: ok/);
});

test('T9 no room for the share: intake claims nothing and says why; running work goes on; with room again it claims', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  w.issue(17);
  await w.tick({ machine: room() });
  assert.ok(w.job(17, 'build'));
  w.issue(18);
  const held = await w.tick({ machine: room("load 6 is above 5 cores, Autopilot's 50% share") });
  assert.match(held.message, /intake held: load 6 is above 5 cores, Autopilot's 50% share/);
  assert.equal(w.job(18), undefined, 'no claim while the machine is busier than the share');
  assert.deepEqual(w.stopped, [], 'the running build goes on');
  w.build(17);
  await w.tick({ machine: room('memory pressure') });
  assert.ok(w.job(17, 'review') && w.job(17, 'suite'), 'reviews and suites of running work start');
  const ac = await w.tick({ machine: room() });
  assert.doesNotMatch(ac.message, /intake held/);
  assert.ok(w.job(18, 'build'), 'with room again the next issue starts');
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
  const text = coreStatus({ state: w.state, settings: w.settings, guard: 'Machine: share 50% (default) · … · new work: held (memory pressure)' }, { root: w.root, now: w.now });
  assert.match(text, /\nMachine: share 50% \(default\) · … · new work: held \(memory pressure\)\n/);
  assert.doesNotMatch(coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now }), /Machine:/);
});

test('the share is for the whole machine: with 2 repositories the jobs of both count, so 2 repositories never get 4 + 4', async t => {
  for (const [other, started, held] of [[3, 1, null], [4, 0, /intake held: 4 of 4 Autopilot jobs on this machine run \(all repositories, 50% share\)/]]) {
    const w = await coreWorld(t);
    writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], engine: 'core', testCommand: 'npm test' } }));
    for (const n of [17, 18, 19]) w.issue(n, { labels: ['pdd:autopilot'] });
    const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel'), stateRoot = join(w.dir, 'state');
    const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
    mkdirSync(stateRoot, { recursive: true });
    writeFileSync(stateFile, JSON.stringify({ enabled: true, cwd, repo: 'acme/widgets', defaultBranch: 'main', coordinatorId: 'coord-a', machine: 'machine-a', label: 'pdd:autopilot',
      agent: { id: 'codex', kind: 'codex', command: 'codex' }, packageRoot: join(w.dir, 'pkg') }));
    // A second enabled repository on this machine (the sandbox beside pdd) with OTHER jobs that hold a slot, and a
    // stopped one whose leftover job file does not count.
    const sandbox = join(stateRoot, 'sandbox.json'), stopped = join(stateRoot, 'stopped.json');
    writeFileSync(sandbox, JSON.stringify({ enabled: true, cwd: '/elsewhere', repo: 'acme/sandbox', engine: 'core' }));
    writeFileSync(stopped, JSON.stringify({ enabled: false, cwd: '/old', repo: 'acme/old', engine: 'core' }));
    for (const [file, n] of [[sandbox, other], [stopped, 4]]) {
      const jobs = join(file.replace(/\.json$/, '-core'), 'jobs'); mkdirSync(jobs, { recursive: true });
      for (let i = 1; i <= n; i++) writeFileSync(join(jobs, `${i}.json`), JSON.stringify({ issue: i, phase: i === 1 ? 'pr' : 'running', role: 'build' }));
    }
    const vm = { cpuCount: 64, load: 1, memory: { available: 200 * GiB, total: 251 * GiB }, pressure: { io: 0, memory: 0, level: null }, disk: { available: 500 * GiB, total: 1000 * GiB },
      cgroup: { cpus: null, memoryMax: null, memoryFree: null }, check: { cpuIds: Array.from({ length: 64 }, (_, i) => i), platform: 'linux', battery: false, virtualized: true, taskset: '/usr/bin/taskset' } };
    const reads = [];
    const ports = { stateRoot, now: w.now, env: { HOME: process.env.HOME, PATH: process.env.PATH }, timer: async () => true, warn: () => {},
      machineGuard: input => { reads.push(input); return readMachineGuard(input, { machineResources: async () => vm, autopilotUse: async () => ({ rss: 2 * GiB, cores: 2 }) }); },
      run: async (command, args, options = {}) => {
        if (command === 'gh') return w.gh(args, options);
        const { spawnSync } = await import('node:child_process'); const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr };
      },
      corePorts: { jobs: w.jobs, checkBase: async () => ({ exitCode: 0, message: 'ok' }), agentReady: async () => true } };
    const result = await tickAutopilot(stateFile, ports);
    assert.equal(reads[0].jobs, other, 'the jobs of the other enabled repository count; a stopped one does not');
    assert.equal(w.started.filter(job => job.role === 'build').length, started, `${other} jobs elsewhere: ${started} new here, though this repository has 4 slots of its own`);
    if (held) assert.match(result.message, held); else assert.match(result.message, /1 started.*1 of 4 slots busy/);
  }
});

test('#3177 every job gets PDD_CLI and PDD_SKILLS; agent roles get the pdd and skills checks; status shows their notes', async t => {
  const w = await coreWorld(t);
  w.issue(17);
  await w.tick();
  const build = w.job(17, 'build'), cli = join(w.root, 'bin', 'pdd');
  assert.equal(build.env.PDD_CLI, cli); assert.equal(build.env.PATH.split(':')[0], join(w.root, 'bin'));
  const skillsDir = join(fileURLToPath(new URL('..', import.meta.url)), 'skills');
  assert.equal(build.env.PDD_SKILLS, skillsDir, 'the skills of the engine\'s own package');
  const engineSkills = /pdd-skills:\s*(\S+)/.exec(readFileSync(join(skillsDir, 'pdd-feature', 'SKILL.md'), 'utf8'))[1];
  assert.deepEqual(build.pddCheck, { version: '0.1.27', cli, skills: { dir: skillsDir, version: engineSkills, read: [join(process.env.HOME, '.agents', 'skills')] } }, 'a Codex job checks ~/.agents/skills');
  const line = `pdd path check: the agent shell finds pdd 0.1.15 at /home/u/.local/bin/pdd; the engine is 0.1.27; using PDD_CLI (${cli})`;
  writeFileSync(build.log.replace(/\.log$/, '.pdd-check.json'), JSON.stringify({ found: true, version: '0.1.15', line }));
  assert.ok(coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now }).includes(`; ${line}`), 'status names the mismatch beside the build');
  const skillsLine = `pdd skills check: installed skills are 0.1.20 at /home/u/.agents/skills, the engine is ${engineSkills}; jobs use PDD_SKILLS (${skillsDir})`;
  writeFileSync(build.log.replace(/\.log$/, '.skills-check.json'), JSON.stringify({ line: skillsLine }));
  assert.ok(coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now }).includes(`; ${line}; ${skillsLine}`), 'and the skills note');
  w.build(17); await w.tick();
  assert.ok(w.job(17, 'review').pddCheck, 'the reviewer is checked too');
  assert.equal(w.job(17, 'suite').pddCheck, undefined, 'the suite runs no agent shell');
  assert.equal(w.job(17, 'suite').env.PDD_CLI, cli);
  assert.equal(w.reports.calls?.length ?? 0, 0, 'nothing is filed');
});
