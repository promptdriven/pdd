// #3231: the machine guard decides the class, the slots, the room for new work and the priority from the machine.
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, rmSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { GUARD, machineClass, autoSlots, slotCount, machineRoom, jobPriority, timerPriority, guardLine, readMachineGuard, usableCores, freeMemory } from '../src/machine-guard.mjs';
import { coreSettings } from '../src/autopilot-core.mjs';
import { readMachineResources } from '../src/machine-resources.mjs';
import { jobCommand, startAgentJob, readAgentJob } from '../src/agent-job.mjs';

const GiB = 1024 ** 3;
const ids = n => Array.from({ length: n }, (_, i) => i);
// A healthy machine: n cores, plenty of memory and disk, low load, on AC power.
const machine = (n = 8, extra = {}) => ({ cpuCount: n, load: 1, memory: { available: 12 * GiB, total: 16 * GiB }, pressure: { io: null, memory: null, level: 1 },
  disk: { available: 200 * GiB, total: 500 * GiB }, power: 'ac', cgroup: { cpus: null, memory: null },
  check: { cpuIds: ids(n), platform: 'linux', battery: false, virtualized: false, taskset: '/usr/bin/taskset' }, ...extra });

test('the machine class: macOS and a Linux machine with a battery or not a VM are laptops; a Linux VM is a server', () => {
  assert.equal(machineClass({ platform: 'darwin', battery: false, virtualized: true }), 'laptop');
  assert.equal(machineClass({ platform: 'linux', battery: true, virtualized: true }), 'laptop');
  assert.equal(machineClass({ platform: 'linux', battery: false, virtualized: false }), 'laptop');
  assert.equal(machineClass({ platform: 'linux', battery: false, virtualized: null }), 'laptop', 'unknown virtualization reserves the person');
  assert.equal(machineClass({ platform: 'linux', battery: false, virtualized: true }), 'server');
  assert.equal(machineClass({ platform: 'win32' }), 'server');
});

test('T1 slots: laptop 1, server from its real limits (cgroup too) at most 4, the machine --runs wins, pdd.json only lowers a server', () => {
  assert.equal(autoSlots(machine(64, { memory: { available: 232 * GiB, total: 251 * GiB } }), 'server'), 4, 'pdd-vm: the cap');
  assert.equal(autoSlots(machine(4), 'server'), 2, '4 cores: 2 slots');
  assert.equal(autoSlots(machine(64, { memory: { available: 7 * GiB, total: 8 * GiB } }), 'server'), 2, '7 GiB free: 2 slots');
  assert.equal(autoSlots(machine(64, { cgroup: { cpus: 2.5, memory: null } }), 'server'), 1, 'a 2.5-CPU cgroup quota counts, not the 64 host cores');
  assert.equal(autoSlots(machine(64, { memory: { available: 200 * GiB, total: 251 * GiB }, cgroup: { cpus: null, memory: 4 * GiB } }), 'server'), 1, 'the cgroup memory room counts');
  assert.equal(autoSlots(machine(1), 'server'), 1, 'at least 1');
  assert.equal(autoSlots(machine(64), 'laptop'), 1);
  assert.equal(usableCores(machine(8, { cgroup: { cpus: 3, memory: null } })), 3); assert.equal(freeMemory(machine(8, { cgroup: { cpus: null, memory: GiB } })), GiB);
  // The coreSettings table: class x pdd.json runs x machine --runs.
  const runs = (klass, repoRuns, machineRuns, auto = klass === 'laptop' ? 1 : 4) => coreSettings({ autopilot: repoRuns === undefined ? {} : { runs: repoRuns } }, null, { klass, auto, runs: machineRuns }).runs;
  assert.equal(runs('laptop'), 1, 'a laptop with no value: 1');
  assert.equal(runs('server'), 4, 'a server with no value: its automatic slots');
  assert.equal(runs('laptop', 3), 1, 'pdd.json does not raise a laptop');
  assert.equal(runs('server', 3), 3, 'pdd.json lowers a server');
  assert.equal(runs('server', 9), 4, 'pdd.json never raises a server above its room');
  assert.equal(runs('laptop', undefined, 2), 2, 'the machine --runs wins on a laptop');
  assert.equal(runs('server', 1, 2), 2, 'and on a server');
  assert.equal(runs('server', undefined, 0), 4, 'an invalid --runs is absent');
  assert.equal(coreSettings({ autopilot: { runs: 3 } }).runs, 3, 'without machine facts: pdd.json, as before');
  assert.deepEqual(slotCount({ klass: 'server', auto: 4, runs: 2 }), { slots: 2, source: 'this machine (--runs 2)' });
  assert.deepEqual(slotCount({ klass: 'server', auto: 4, repoRuns: 3 }), { slots: 3, source: 'pdd.json autopilot.runs' });
});

test('T7 the room check: each cause holds new work on a laptop; all fine passes; a server keeps today\'s floors', () => {
  const room = (klass, extra) => machineRoom(machine(8, extra), klass);
  assert.deepEqual(room('laptop', {}), { ok: true, reason: null });
  assert.equal(room('laptop', { power: 'battery' }).reason, 'on battery power');
  assert.equal(room('laptop', { power: null }).ok, true, 'unreadable power counts as AC');
  assert.match(room('laptop', { memory: { available: 1.5 * GiB, total: 16 * GiB } }).reason, /^only 1\.5 GiB of memory free \(needs 2 GiB and 15%\)$/);
  assert.match(room('laptop', { memory: { available: 2.2 * GiB, total: 16 * GiB } }).reason, /memory free/, '2.2 GiB is under 15% of 16 GiB');
  assert.equal(room('laptop', { pressure: { level: 2 } }).reason, 'memory pressure', 'macOS pressure warn');
  assert.equal(room('laptop', { pressure: { memory: 12, level: null } }).reason, 'memory pressure', 'Linux PSI some avg10 of 10 or more');
  assert.equal(room('laptop', { pressure: { memory: null, level: null } }).ok, true, 'unreadable pressure falls back to the memory numbers');
  assert.equal(room('laptop', { memory: { available: null, total: null } }).reason, 'memory cannot be read');
  assert.match(room('laptop', { disk: { available: 5 * GiB, total: 500 * GiB } }).reason, /^only 5 GiB of disk free \(needs 10 GiB and 5%\)$/);
  assert.equal(room('laptop', { disk: { available: null, total: null } }).reason, 'disk cannot be read');
  assert.equal(room('laptop', { load: 4.5 }).reason, "load 4.5 is above Autopilot's share of 4 cores");
  assert.equal(room('laptop', { load: 4 }).ok, true);
  // A server: no power, pressure or load check; memory 10% and disk 1 GiB and 5%.
  assert.equal(room('server', { power: 'battery', load: 60, pressure: { level: 4 } }).ok, true);
  assert.match(room('server', { memory: { available: 1 * GiB, total: 16 * GiB } }).reason, /needs 10%/);
  assert.match(room('server', { disk: { available: 0.5 * GiB, total: 100 * GiB } }).reason, /needs 1 GiB and 5%/);
});

test('T3 priority: nice 19 everywhere, macOS utility QoS through taskpolicy, a Linux laptop pins agent roles to its share', () => {
  const linux = role => jobPriority({ klass: 'laptop', platform: 'linux', role, resources: machine(8), taskset: '/usr/bin/taskset' });
  assert.deepEqual(linux('build'), { nice: 19, qos: null, cpus: '0-3', taskset: '/usr/bin/taskset', checkCpus: 4 });
  assert.equal(linux('review').cpus, '0-3');
  for (const role of ['suite', 'vectors', 'runtime']) assert.equal(linux(role).cpus, null, `${role} is not pinned (the queue pins suites)`);
  assert.deepEqual(jobPriority({ klass: 'server', platform: 'linux', role: 'build', resources: machine(8), taskset: '/usr/bin/taskset' }), { nice: 19, qos: null, cpus: null, taskset: null, checkCpus: 8 });
  assert.deepEqual(jobPriority({ klass: 'laptop', platform: 'darwin', role: 'build', resources: machine(10) }), { nice: 19, qos: 'utility', cpus: null, taskset: null, checkCpus: 5 });
  assert.equal(jobPriority({ klass: 'laptop', platform: 'linux', role: 'build', resources: machine(8, { check: { cpuIds: [0, 2, 4, 6, 8, 10], platform: 'linux' } }), taskset: '/usr/bin/taskset' }).cpus, '0,2,4');
  // The wrapper's command: taskpolicy on macOS, taskset on Linux, else the command.
  const spec = priority => ({ command: 'codex', args: ['exec', '-'], ...(priority ? { priority } : {}) });
  assert.deepEqual(jobCommand(spec(), 'darwin', { executable: () => true }), { command: '/usr/sbin/taskpolicy', args: ['-c', 'utility', '-d', 'throttle', 'codex', 'exec', '-'] });
  assert.deepEqual(jobCommand(spec({ qos: null }), 'darwin', { executable: () => true }), { command: 'codex', args: ['exec', '-'] });
  assert.deepEqual(jobCommand(spec(), 'darwin', { executable: () => false }), { command: 'codex', args: ['exec', '-'] }, 'no taskpolicy: the command itself');
  assert.deepEqual(jobCommand(spec(linux('build')), 'linux'), { command: '/usr/bin/taskset', args: ['--cpu-list', '0-3', 'codex', 'exec', '-'] });
  assert.deepEqual(jobCommand(spec(linux('suite')), 'linux'), { command: 'codex', args: ['exec', '-'] });
  assert.deepEqual(jobCommand(spec({ cpus: '0-3; rm -rf /', taskset: '/usr/bin/taskset' }), 'linux'), { command: 'codex', args: ['exec', '-'] }, 'only a plain CPU list');
});

test('T4 a real job runs at nice 19 (the wrapper sets it; children inherit it)', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-guard-job-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  const job = startAgentJob({ id: 'nice-1', dir, cwd: dir, command: '/bin/sh', args: ['-c', 'ps -o ni= -p $$'], env: { PATH: process.env.PATH } });
  const end = Date.now() + 15000;
  while (Date.now() < end && !existsSync(job.exit)) await new Promise(r => setTimeout(r, 50));
  assert.equal(readAgentJob(job).state, 'exited');
  assert.equal(readFileSync(job.log, 'utf8').trim(), '19');
});

test('T6 timer lines: launchd Nice 19; systemd Nice=19 and CPUWeight=20, MemoryHigh=50% only on a laptop', () => {
  assert.deepEqual(timerPriority('laptop', 'darwin'), { plist: '<key>Nice</key><integer>19</integer>', unit: '' });
  assert.deepEqual(timerPriority('laptop', 'linux'), { plist: '', unit: 'Nice=19\nCPUWeight=20\nMemoryHigh=50%\n' });
  assert.deepEqual(timerPriority('server', 'linux'), { plist: '', unit: 'Nice=19\nCPUWeight=20\n' });
  assert.equal(GUARD.nice, 19); assert.equal(GUARD.cpuWeight, 20);
});

test('T12 the status line names the class, the share, memory, power, the slots and the hold reason', async () => {
  const resources = machine(10, { power: 'battery', check: { cpuIds: ids(10), platform: 'darwin', battery: true, virtualized: false, taskset: null }, memory: { available: 3.1 * GiB, total: 16 * GiB } });
  const guard = await readMachineGuard({ cwd: '/', runs: undefined }, { machineResources: async () => resources });
  assert.equal(guard.klass, 'laptop'); assert.equal(guard.slots, 1); assert.equal(guard.room.reason, 'on battery power');
  assert.match(guard.line, /^Machine: laptop · 10 cores, Autopilot uses 5 · memory 3\.1 of 16 GiB free, pressure normal · disk 200 GiB free · load 1 · battery power · priority low · 1 slot \(automatic\) · new work: held \(on battery power\)$/);
  assert.deepEqual(guard.priority('build'), { nice: 19, qos: 'utility', cpus: null, taskset: null, checkCpus: 5 });
  const failed = await readMachineGuard({ runs: 2 }, { machineResources: async () => { throw Error('no proc'); }, platform: 'linux' });
  assert.deepEqual([failed.slots, failed.room.ok, failed.room.reason], [2, false, 'machine resources cannot be read']);
  assert.match(guardLine({ klass: 'server', slots: 4, source: 'automatic', room: { ok: true }, resources: {} }), /unknown cores.*power unknown \(counts as AC\).*4 slots \(automatic\) · new work: ok$/);
});

test('T8 readers: pmset, the macOS pressure level, Linux power supplies and cgroup v2 limits', async () => {
  const mac = async (pmset, sysctl) => readMachineResources({ cwd: '/' }, { platform: 'darwin', includeGuard: true, pmset: () => pmset, sysctl: () => sysctl,
    vmStat: () => '', freeMemory: () => GiB, totalMemory: () => 16 * GiB, statfs: () => ({ bavail: 1, blocks: 2, bsize: 4096 }), cpuCount: () => 10, load: () => 1 });
  assert.equal((await mac("Now drawing from 'AC Power'\n -InternalBattery-0 (id=1)\t100%; charged;", '1\n')).power, 'ac');
  const battery = await mac("Now drawing from 'Battery Power'\n -InternalBattery-0 (id=1)\t81%; discharging;", '2\n');
  assert.equal(battery.power, 'battery'); assert.equal(battery.pressure.level, 2);
  const desktop = await mac("Now drawing from 'AC Power'\n", '');
  assert.equal(desktop.power, 'ac'); assert.equal(desktop.pressure.level, null, 'an unreadable level is null');
  // Linux: /sys/class/power_supply and the cgroup path of this process with its parents.
  const tree = files => ({ platform: 'linux', includeGuard: true, readFile: path => { if (path in files) return files[path]; throw Object.assign(Error('ENOENT'), { code: 'ENOENT' }); },
    readDir: path => [...new Set(Object.keys(files).filter(f => f.startsWith(`${path}/`)).map(f => f.slice(path.length + 1).split('/')[0]))],
    statfs: () => ({ bavail: 1, blocks: 2, bsize: 4096 }), cpuCount: () => 4, load: () => 1 });
  const base = { '/proc/meminfo': 'MemTotal: 16384 kB\nMemAvailable: 8192 kB\n', '/proc/self/cgroup': '0::/user.slice/pdd.service\n',
    '/sys/fs/cgroup/user.slice/pdd.service/cpu.max': '200000 100000', '/sys/fs/cgroup/user.slice/pdd.service/memory.max': 'max',
    '/sys/fs/cgroup/user.slice/pdd.service/memory.high': String(6 * GiB), '/sys/fs/cgroup/user.slice/pdd.service/memory.current': String(2 * GiB),
    '/sys/fs/cgroup/user.slice/cpu.max': 'max 100000', '/sys/fs/cgroup/user.slice/memory.max': String(3 * GiB), '/sys/fs/cgroup/user.slice/memory.current': String(1 * GiB) };
  const onBattery = await readMachineResources({ cwd: '/' }, tree({ ...base, '/sys/class/power_supply/AC/type': 'Mains', '/sys/class/power_supply/AC/online': '0',
    '/sys/class/power_supply/BAT0/type': 'Battery', '/sys/class/power_supply/BAT0/status': 'Discharging' }));
  assert.equal(onBattery.power, 'battery');
  assert.deepEqual(onBattery.cgroup, { cpus: 2, memory: 2 * GiB }, 'the lowest quota and the lowest room of all levels');
  const plugged = await readMachineResources({ cwd: '/' }, tree({ ...base, '/sys/class/power_supply/AC/type': 'Mains', '/sys/class/power_supply/AC/online': '1', '/sys/class/power_supply/BAT0/type': 'Battery', '/sys/class/power_supply/BAT0/status': 'Discharging' }));
  assert.equal(plugged.power, 'ac');
  const server = await readMachineResources({ cwd: '/' }, tree({ '/proc/meminfo': base['/proc/meminfo'], '/proc/self/cgroup': '0::/\n', '/sys/fs/cgroup/cpu.max': 'max 100000' }));
  assert.equal(server.power, null, 'no power supply: null (counts as AC)'); assert.deepEqual(server.cgroup, { cpus: null, memory: null });
  const legacy = await readMachineResources({ cwd: '/' }, { ...tree(base), includeGuard: false });
  assert.equal(legacy.power, undefined, 'without includeGuard the observation is as before'); assert.equal(legacy.cgroup, undefined);
});
