// #3231: the machine guard decides the class, the slots, the room for new work and the priority from the machine.
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, rmSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { GUARD, validShare, shareOf, autoSlots, slotMath, slotCount, machineRoom, jobPriority, timerPriority, guardLine, readMachineGuard, usableCores, freeMemory, memoryLimit } from '../src/machine-guard.mjs';
import { readAutopilotUse } from '../src/machine-resources.mjs';
import { coreSettings } from '../src/autopilot-core.mjs';
import { readMachineResources } from '../src/machine-resources.mjs';
import { jobCommand, startAgentJob, readAgentJob, pddCheckFile, pddCheckLine, skillsCheckFile } from '../src/agent-job.mjs';

const GiB = 1024 ** 3;
const ids = n => Array.from({ length: n }, (_, i) => i);
// A healthy machine: n cores, plenty of memory and disk, low load, on AC power.
const machine = (n = 8, extra = {}) => ({ cpuCount: n, load: 1, memory: { available: 12 * GiB, total: 16 * GiB }, pressure: { io: null, memory: null, level: 1 },
  disk: { available: 200 * GiB, total: 500 * GiB }, cgroup: { cpus: null, memoryMax: null, memoryFree: null },
  check: { cpuIds: ids(n), platform: 'linux', battery: false, virtualized: false, taskset: '/usr/bin/taskset' }, ...extra });

test('the share: a whole percent from 1 to 100, default 50', () => {
  assert.equal(GUARD.share, 50);
  for (const value of [1, 50, 100]) { assert.equal(validShare(value), true); assert.equal(shareOf(value), value); }
  for (const value of [0, 101, 49.5, '70', null, undefined, NaN]) { assert.equal(validShare(value), false, String(value)); assert.equal(shareOf(value), 50); }
});

// One test per row of the slot table (the examples in the prompt). Each machine is on Linux or macOS; the OS decides
// nothing.
const box = (cores, gb, extra = {}) => machine(cores, { memory: { available: gb * GiB * 0.6, total: gb * GiB }, ...extra });
for (const [name, resources, share, slots, use, room] of [
  ['an 8 GB, 8-core Mac at 50%', box(8, 8, { check: { cpuIds: ids(8), platform: 'darwin' } }), 50, 1],
  ['a 32 GB, 10-core Mac at 50%', box(10, 32, { check: { cpuIds: ids(10), platform: 'darwin' } }), 50, 2],
  ['pdd-vm (64 cores, 251 GB) at 50%', box(64, 251), 50, 4],
  ['pdd-vm at 50% with 2 repositories and 2 jobs each: no room', box(64, 251), 50, 4, { jobs: 4, rss: 2 * GiB, cores: 3 }, '4 of 4 Autopilot jobs on this machine run (all repositories, 50% share)'],
  ['pdd-vm at 50% with 2 repositories and 3 jobs in all: 1 more', box(64, 251), 50, 4, { jobs: 3, rss: 2 * GiB, cores: 3 }, 1],
  ['a 4-CPU, 8 GB Linux container at 50%', box(4, 8), 50, 1],
  ['a 64-core host whose cgroup allows 4 CPUs and 8 GiB, at 50%', box(64, 251, { cgroup: { cpus: 4, memoryMax: 8 * GiB, memoryFree: 6 * GiB } }), 50, 1],
  ['a 32 GB, 10-core Mac at 100%', box(10, 32), 100, 4],
  ['a share of 100 on pdd-vm', box(64, 251), 100, 4],
  ['an 8 GB, 8-core Mac at 10%', box(8, 8), 10, 1],
]) test(`T1 slots: ${name} gets ${slots}`, () => {
  assert.equal(autoSlots(resources, share), slots);
  if (typeof room === 'string') assert.deepEqual(machineRoom(resources, share, use), { ok: false, reason: room, free: 0 });
  else if (typeof room === 'number') assert.deepEqual(machineRoom(resources, share, use), { ok: true, reason: null, free: room });
});

test('T1 the machine --runs wins, pdd.json only lowers the automatic slots; the core uses them', () => {
  assert.equal(usableCores(machine(8, { cgroup: { cpus: 3, memoryMax: null, memoryFree: null } })), 3);
  assert.equal(memoryLimit(machine(8, { cgroup: { cpus: null, memoryMax: 4 * GiB, memoryFree: GiB } })), 4 * GiB);
  assert.equal(freeMemory(machine(8, { cgroup: { cpus: null, memoryMax: 4 * GiB, memoryFree: GiB } })), GiB);
  assert.deepEqual(slotMath(box(10, 32), 50), { slots: 2, share: 50, cores: 10, limit: 32 * GiB, byCores: 2, byMemory: 5 });
  const runs = (auto, repoRuns, machineRuns) => coreSettings({ autopilot: repoRuns === undefined ? {} : { runs: repoRuns } }, null, { auto, runs: machineRuns }).runs;
  assert.equal(runs(4), 4, 'automatic');
  assert.equal(runs(4, 3), 3, 'pdd.json lowers');
  assert.equal(runs(1, 3), 1, 'pdd.json never raises');
  assert.equal(runs(1, undefined, 2), 2, 'the machine --runs wins');
  assert.equal(runs(4, 1, 2), 2, 'also over pdd.json');
  assert.equal(runs(4, undefined, 0), 4, 'an invalid --runs is absent');
  assert.equal(coreSettings({ autopilot: { runs: 3 } }).runs, 3, 'without machine facts: pdd.json, as before');
  assert.deepEqual(slotCount({ auto: 4, runs: 2 }), { slots: 2, source: 'this machine, --runs 2' });
  assert.deepEqual(slotCount({ auto: 4, repoRuns: 3 }), { slots: 3, source: 'pdd.json autopilot.runs' });
  assert.deepEqual(slotCount({ auto: 2 }), { slots: 2, source: 'automatic' });
});

test('T7 the room check for the whole machine: each cause holds new work; all fine passes; no battery check', () => {
  const room = (extra, share = 50, use = { jobs: 0, rss: 0, cores: 0 }) => machineRoom(machine(8, extra), share, use);
  assert.deepEqual(room({}), { ok: true, reason: null, free: 2 }, '8 cores and 16 GiB at 50%: 2 slots, both free');
  assert.deepEqual(room({ power: 'battery' }), { ok: true, reason: null, free: 2 }, 'power is not read');
  assert.equal(room({ memory: { available: 2.5 * GiB, total: 16 * GiB } }).reason, 'only 2.5 GiB of memory free; a job needs 3 GiB');
  assert.equal(room({ memory: { available: 12 * GiB, total: 16 * GiB }, cgroup: { cpus: null, memoryMax: 4 * GiB, memoryFree: GiB } }).reason, 'only 1 GiB of memory free; a job needs 3 GiB', 'the cgroup room counts');
  assert.equal(room({ pressure: { level: 2 } }).reason, 'memory pressure', 'macOS pressure warn');
  assert.equal(room({ pressure: { memory: 12, level: null } }).reason, 'memory pressure', 'Linux PSI some avg10 of 10 or more');
  assert.equal(room({ pressure: { memory: null, level: null } }).ok, true, 'unreadable pressure falls back to the memory numbers');
  assert.equal(room({ memory: { available: null, total: null } }).reason, 'memory cannot be read');
  assert.equal(room({ disk: { available: 5 * GiB, total: 500 * GiB } }).reason, 'only 5 GiB of disk free; a job needs 10 GiB and 5%');
  assert.equal(room({ disk: { available: 20 * GiB, total: 500 * GiB } }).reason, 'only 20 GiB of disk free; a job needs 10 GiB and 5%');
  assert.equal(room({ disk: { available: null, total: null } }).reason, 'disk cannot be read');
  // What all Autopilot jobs on this machine use now (every repository) against the share.
  assert.deepEqual(room({}, 50, { jobs: 1, rss: GiB, cores: 1 }), { ok: true, reason: null, free: 1 });
  assert.equal(room({}, 50, { jobs: 2, rss: GiB, cores: 1 }).reason, '2 of 2 Autopilot jobs on this machine run (all repositories, 50% share)');
  assert.equal(room({}, 50, { jobs: 1, rss: 5.5 * GiB, cores: 1 }).reason, 'Autopilot uses 5.5 GiB on this machine; a new job would pass its 8 GiB share (50%)');
  assert.equal(room({}, 50, { jobs: 1, rss: GiB, cores: 4 }).reason, 'Autopilot uses 4 cores on this machine, its 50% share is 4');
  assert.equal(room({ load: 30 }, 50, { jobs: 0, rss: 0, cores: 0 }).ok, true, 'the person\'s own load does not hold Autopilot (lowest priority, CPUWeight=1)');
  assert.equal(room({}, 50, { jobs: 1, rss: null, cores: null }).ok, true, 'an unknown use is not checked');
  assert.equal(room({}, 50, {}).free, 2, 'no use given: no job counted');
});

test('the machine-wide use reader sums every Autopilot job tree once, of any repository', () => {
  const ps = [
    '  100     1  20480   0.5 node /pkg/src/agent-job.mjs --wrapper /a/core-1/logs/17-build-x.spec.json',
    '  101   100 307200  80.0 codex exec --json -',
    '  102   101 102400 150.0 node --test',
    '  200     1  20480   0.1 node /pkg/src/agent-job.mjs --wrapper /a/core-2/logs/9-suite-y.spec.json',
    '  201   200 2097152 300.0 npm test',
    '  300     1 999999 400.0 node my-own-app.js',
  ].join('\n');
  assert.deepEqual(readAutopilotUse({ spawnSync: () => ({ status: 0, stdout: ps }) }), { processes: 5, wrappers: 2, rss: (20480 + 307200 + 102400 + 20480 + 2097152) * 1024, cores: 5.31 });
  assert.equal(readAutopilotUse({ spawnSync: () => ({ status: 1, stdout: '' }) }), null);
});

test('T3 priority: nice 19 everywhere, macOS utility QoS through taskpolicy, Linux pins agent roles to the share', () => {
  const linux = (role, share = 50, n = 8) => jobPriority({ platform: 'linux', role, resources: machine(n), share, taskset: '/usr/bin/taskset' });
  assert.deepEqual(linux('build'), { nice: 19, qos: null, cpus: '0-3', taskset: '/usr/bin/taskset', checkCpus: 4 });
  assert.equal(linux('review').cpus, '0-3');
  for (const role of ['suite', 'vectors', 'runtime']) assert.equal(linux(role).cpus, null, `${role} is not pinned (the queue pins suites)`);
  assert.deepEqual(linux('build', 100), { nice: 19, qos: null, cpus: null, taskset: null, checkCpus: 8 }, 'the whole machine needs no list');
  assert.equal(linux('build', 50, 64).cpus, '0-31', 'pdd-vm at 50%');
  assert.deepEqual(jobPriority({ platform: 'darwin', role: 'build', resources: machine(10), share: 50 }), { nice: 19, qos: 'utility', cpus: null, taskset: null, checkCpus: 5 });
  assert.equal(jobPriority({ platform: 'linux', role: 'build', resources: machine(8, { check: { cpuIds: [0, 2, 4, 6, 8, 10], platform: 'linux' } }), share: 50, taskset: '/usr/bin/taskset' }).cpus, '0,2,4');
  // The wrapper's command: taskpolicy on macOS, taskset on Linux, else the command.
  const spec = priority => ({ command: 'codex', args: ['exec', '-'], ...(priority ? { priority } : {}) });
  const all = { executable: () => true }, none = { executable: () => false };
  assert.deepEqual(jobCommand(spec(), 'darwin', all), { command: '/usr/bin/nice', args: ['-n', '19', '/usr/sbin/taskpolicy', '-c', 'utility', 'codex', 'exec', '-'] });
  assert.deepEqual(jobCommand(spec({ qos: null }), 'darwin', all), { command: '/usr/bin/nice', args: ['-n', '19', 'codex', 'exec', '-'] });
  assert.deepEqual(jobCommand(spec(), 'darwin', none), { command: 'codex', args: ['exec', '-'] }, 'no nice or taskpolicy: the command itself (the wrapper lowers its own nice value)');
  assert.deepEqual(jobCommand(spec(linux('build')), 'linux', all), { command: '/usr/bin/nice', args: ['-n', '19', '/usr/bin/taskset', '--cpu-list', '0-3', 'codex', 'exec', '-'] });
  assert.deepEqual(jobCommand(spec(linux('suite')), 'linux', all), { command: '/usr/bin/nice', args: ['-n', '19', 'codex', 'exec', '-'] });
  assert.deepEqual(jobCommand(spec({ nice: 0 }), 'linux', all), { command: 'codex', args: ['exec', '-'] }, 'nice 0 adds nothing');
  assert.deepEqual(jobCommand(spec({ cpus: '0-3; rm -rf /', taskset: '/usr/bin/taskset' }), 'linux', all), { command: '/usr/bin/nice', args: ['-n', '19', 'codex', 'exec', '-'] }, 'only a plain CPU list');
});

test('T4 a real job runs at nice 19 (nice starts the child; its children inherit it)', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-guard-job-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  const job = startAgentJob({ id: 'nice-1', dir, cwd: dir, command: '/bin/sh', args: ['-c', 'ps -o ni= -p $$'], env: { PATH: process.env.PATH } });
  const end = Date.now() + 15000;
  while (Date.now() < end && !existsSync(job.exit)) await new Promise(r => setTimeout(r, 50));
  assert.equal(readAgentJob(job).state, 'exited');
  // At least 19: when another test of this process already lowered its own priority, nice adds to it (macOS caps at 20).
  assert.ok(Number(readFileSync(job.log, 'utf8').trim()) >= 19, readFileSync(job.log, 'utf8'));
});

test('T6 timer lines: launchd Nice 19; systemd Nice=19, CPUWeight=1 below a share of 100 (100 at 100), MemoryHigh at the share', () => {
  assert.deepEqual(timerPriority('darwin', 70), { plist: '<key>Nice</key><integer>19</integer>', unit: '' });
  assert.deepEqual(timerPriority('linux'), { plist: '', unit: 'Nice=19\nCPUWeight=1\nMemoryHigh=50%\n' });
  assert.deepEqual(timerPriority('linux', 70), { plist: '', unit: 'Nice=19\nCPUWeight=1\nMemoryHigh=70%\n' });
  assert.deepEqual(timerPriority('linux', 100), { plist: '', unit: 'Nice=19\nCPUWeight=100\nMemoryHigh=100%\n' });
  assert.deepEqual(timerPriority('win32'), { plist: '', unit: '' });
  assert.equal(GUARD.nice, 19); assert.equal(GUARD.cpuWeight, 1); assert.equal(GUARD.cpuWeightFull, 100);
});

test('T12 the status line names the share and its source, the slot math, memory, the slots and the hold reason', async () => {
  const resources = machine(10, { check: { cpuIds: ids(10), platform: 'darwin', battery: true, virtualized: false, taskset: null }, memory: { available: 2.1 * GiB, total: 16 * GiB } });
  const guard = await readMachineGuard({ cwd: '/', jobs: 1 }, { machineResources: async () => resources, autopilotUse: async () => ({ rss: 0.4 * GiB, cores: 0.3 }) });
  assert.equal(guard.share, 50); assert.equal(guard.slots, 2); assert.equal(guard.room.reason, 'only 2.1 GiB of memory free; a job needs 3 GiB');
  assert.equal(guard.line, 'Machine: share 50% (default) of 10 cores and 16 GiB · slots min(4, 5 cores ÷ 2, 8 GiB ÷ 3 GiB) = 2 → 2 (automatic) · Autopilot on this machine now: 1 job, 0.4 GiB, 0.3 cores · memory 2.1 GiB free, pressure normal · disk 200 GiB free · load 1 · priority low · new work: held (only 2.1 GiB of memory free; a job needs 3 GiB)');
  assert.deepEqual(guard.priority('build'), { nice: 19, qos: 'utility', cpus: null, taskset: null, checkCpus: 5 });
  const set = await readMachineGuard({ cwd: '/', share: 70, runs: 1 }, { machineResources: async () => machine(10), autopilotUse: async () => ({ rss: 0, cores: 0 }) });
  assert.match(set.line, /^Machine: share 70% \(this machine, --share\) of 10 cores and 16 GiB · slots min\(4, 7 cores ÷ 2, 11\.2 GiB ÷ 3 GiB\) = 3 → 1 \(this machine, --runs 1\) · .* · new work: ok$/);
  const failed = await readMachineGuard({ runs: 2 }, { machineResources: async () => { throw Error('no proc'); }, autopilotUse: async () => null, platform: 'linux' });
  assert.deepEqual([failed.slots, failed.room.ok, failed.room.reason], [2, false, 'machine resources cannot be read']);
  assert.match(guardLine({ slots: 4, source: 'automatic', room: { ok: true }, resources: {} }), /of unknown cores and unknown GiB · slots min\(4, \? cores ÷ 2, \? GiB ÷ 3 GiB\) = 1 → 4 \(automatic\) · Autopilot on this machine now: 0 jobs, \? GiB, \? cores.* · new work: ok$/);
});

test('T8 readers: the macOS pressure level and cgroup v2 limits', async () => {
  const mac = async sysctl => readMachineResources({ cwd: '/' }, { platform: 'darwin', includeGuard: true, sysctl: () => sysctl,
    vmStat: () => '', freeMemory: () => GiB, totalMemory: () => 16 * GiB, statfs: () => ({ bavail: 1, blocks: 2, bsize: 4096 }), cpuCount: () => 10, load: () => 1 });
  assert.equal((await mac('1\n')).pressure.level, 1);
  assert.equal((await mac('2\n')).pressure.level, 2);
  assert.equal((await mac('')).pressure.level, null, 'an unreadable level is null');
  assert.equal((await mac('1\n')).power, undefined, 'no power read');
  // Linux: the cgroup path of this process with its parents.
  const tree = files => ({ platform: 'linux', includeGuard: true, readFile: path => { if (path in files) return files[path]; throw Object.assign(Error('ENOENT'), { code: 'ENOENT' }); },
    statfs: () => ({ bavail: 1, blocks: 2, bsize: 4096 }), cpuCount: () => 4, load: () => 1 });
  const base = { '/proc/meminfo': 'MemTotal: 16384 kB\nMemAvailable: 8192 kB\n', '/proc/self/cgroup': '0::/user.slice/pdd.service\n',
    '/sys/fs/cgroup/user.slice/pdd.service/cpu.max': '200000 100000', '/sys/fs/cgroup/user.slice/pdd.service/memory.max': 'max',
    '/sys/fs/cgroup/user.slice/pdd.service/memory.high': String(6 * GiB), '/sys/fs/cgroup/user.slice/pdd.service/memory.current': String(2 * GiB),
    '/sys/fs/cgroup/user.slice/cpu.max': 'max 100000', '/sys/fs/cgroup/user.slice/memory.max': String(3 * GiB), '/sys/fs/cgroup/user.slice/memory.current': String(1 * GiB) };
  const limited = await readMachineResources({ cwd: '/' }, tree(base));
  assert.deepEqual(limited.cgroup, { cpus: 2, memoryMax: 3 * GiB, memoryFree: 2 * GiB }, 'the lowest quota, limit and room of all levels');
  const open = await readMachineResources({ cwd: '/' }, tree({ '/proc/meminfo': base['/proc/meminfo'], '/proc/self/cgroup': '0::/\n', '/sys/fs/cgroup/cpu.max': 'max 100000' }));
  assert.deepEqual(open.cgroup, { cpus: null, memoryMax: null, memoryFree: null });
  const legacy = await readMachineResources({ cwd: '/' }, { ...tree(base), includeGuard: false });
  assert.equal(legacy.cgroup, undefined, 'without includeGuard the observation is as before'); assert.equal(legacy.pressure.level, undefined);
});

// #3177: a login shell can put an old pdd first on PATH; the job uses PDD_CLI and the wrapper notes the mismatch.
for (const [name, old] of [['an old pdd first in the login shell', true], ['the engine\'s own pdd', false]]) test(`#3177 pdd check with ${name}`, async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-guard-cli-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  const { mkdirSync, writeFileSync, chmodSync } = await import('node:fs');
  const fake = join(dir, 'oldbin'), engine = join(dir, 'enginebin');
  for (const [folder, version] of [[fake, '0.1.15'], [engine, '0.1.29']]) {
    mkdirSync(folder); writeFileSync(join(folder, 'pdd'), `#!/bin/sh\necho ${version}\n`); chmodSync(join(folder, 'pdd'), 0o755);
  }
  // A login shell whose profile puts the old pdd first again, like ~/.profile with ~/.local/bin on pdd-vm.
  const shell = join(dir, 'login-sh');
  writeFileSync(shell, `#!/bin/sh\necho "Welcome from the profile"\n${old ? `PATH="${fake}:$PATH"; export PATH\n` : ''}shift\nexec /bin/sh -c "$1"\n`); chmodSync(shell, 0o755);
  const job = startAgentJob({ id: 'cli-1', dir, cwd: dir, command: '/bin/sh', args: ['-c', 'sleep 1; echo "agent uses $PDD_CLI"'], pddCheck: { version: '0.1.29', cli: join(engine, 'pdd') },
    env: { PATH: `${engine}:${process.env.PATH}`, SHELL: shell, PDD_CLI: join(engine, 'pdd') } });
  const end = Date.now() + 20000;
  while (Date.now() < end && !(existsSync(job.exit) && existsSync(pddCheckFile(job.log)))) await new Promise(r => setTimeout(r, 50));
  const log = readFileSync(job.log, 'utf8'), record = JSON.parse(readFileSync(pddCheckFile(job.log), 'utf8'));
  assert.match(log, new RegExp(`agent uses ${join(engine, 'pdd').replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`), 'the agent gets PDD_CLI');
  if (old) {
    assert.equal(record.line, `pdd path check: the agent shell finds pdd 0.1.15 at ${join(fake, 'pdd')}; the engine is 0.1.29; using PDD_CLI (${join(engine, 'pdd')})`);
    assert.ok(log.includes(record.line), 'one line in the job log');
  } else {
    assert.deepEqual([record.found, record.version, record.line], [true, '0.1.29', null]); assert.doesNotMatch(log, /pdd path check/);
  }
  assert.equal(pddCheckLine({ found: false, engine: '0.1.29', cli: '/c/pdd' }), 'pdd path check: the agent shell finds no pdd on PATH; the engine is 0.1.29; using PDD_CLI (/c/pdd)');
});

// #3177, the skills part: the agent's tools load ~/.agents/skills by default; the job reads "$PDD_SKILLS".
for (const [name, installed, line] of [['an old installed skills folder', '0.1.20', true], ['skills of the engine\'s version', '0.1.29', false], ['no installed skills', null, false]]) test(`#3177 skills check with ${name}`, async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-guard-skills-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  const { mkdirSync, writeFileSync } = await import('node:fs');
  const home = join(dir, 'home'), installedDir = join(home, '.agents', 'skills'), engineDir = join(dir, 'pkg', 'skills');
  if (installed) { mkdirSync(join(installedDir, 'pdd-feature'), { recursive: true }); writeFileSync(join(installedDir, 'pdd-feature', 'SKILL.md'), `---\nname: pdd-feature\nmetadata:\n  pdd-skills: ${installed}\n---\n`); }
  const job = startAgentJob({ id: 'skills-1', dir, cwd: dir, command: '/bin/sh', args: ['-c', 'echo "skills in $PDD_SKILLS"'],
    pddCheck: { version: '0.1.29', cli: '/engine/bin/pdd', skills: { dir: engineDir, version: '0.1.29', read: [installedDir] } }, env: { PATH: process.env.PATH, HOME: home, SHELL: '/bin/sh', PDD_SKILLS: engineDir } });
  const end = Date.now() + 20000;
  while (Date.now() < end && !(existsSync(job.exit) && existsSync(skillsCheckFile(job.log)))) await new Promise(r => setTimeout(r, 50));
  const log = readFileSync(job.log, 'utf8'), record = JSON.parse(readFileSync(skillsCheckFile(job.log), 'utf8'));
  assert.match(log, new RegExp(`skills in ${engineDir.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`), 'the agent gets PDD_SKILLS');
  if (line) {
    assert.equal(record.line, `pdd skills check: installed skills are 0.1.20 at ${installedDir}, the engine is 0.1.29; jobs use PDD_SKILLS (${engineDir})`);
    assert.ok(log.includes(record.line), 'one line in the job log');
  } else { assert.equal(record.line, null); assert.doesNotMatch(log, /installed skills/); }
});

test('a child that a stop signal ends before the wrapper sees the stop still ends the whole group (no orphan)', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-guard-race-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  const mark = join(dir, 'grandchild.pid');
  const grandchild = `require('fs').writeFileSync(${JSON.stringify(mark)}, String(process.pid)); process.on('SIGTERM', () => {}); setInterval(() => {}, 1000);`;
  // The child starts a grandchild that ignores SIGTERM, waits for it, then dies by SIGTERM itself: the wrapper never got
  // a signal, so only the child's exit signal tells it that a stop ended the job.
  const job = startAgentJob({ id: 'race-1', dir, cwd: dir, command: '/bin/sh', args: ['-c', `${JSON.stringify(process.execPath)} -e ${JSON.stringify(grandchild)} & while [ ! -s ${JSON.stringify(mark)} ]; do sleep 0.1; done; kill -TERM $$`], env: { PATH: process.env.PATH } });
  const end = Date.now() + 25000;
  while (Date.now() < end && !existsSync(mark)) await new Promise(r => setTimeout(r, 50));
  const pid = Number(readFileSync(mark, 'utf8'));
  t.after(() => { try { process.kill(pid, 'SIGKILL'); } catch {} });
  const gone = () => { try { process.kill(pid, 0); return false; } catch (error) { return error.code === 'ESRCH'; } };
  while (Date.now() < end && !gone()) await new Promise(r => setTimeout(r, 100));
  assert.equal(gone(), true, 'the grandchild that ignores SIGTERM is gone');
  assert.equal(JSON.parse(readFileSync(job.exit, 'utf8')).signal, 'SIGTERM');
});
