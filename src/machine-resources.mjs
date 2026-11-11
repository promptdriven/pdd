// Generated from prompts/cli/machine-resources.prompt.md (sha256: 21304cf317d71fef182414a331925a4d37914f3deaf6836936c0cd1d155a8c1c).
import * as files from 'node:fs';
import { readFileSync, statfsSync } from 'node:fs';
import { join, isAbsolute } from 'node:path';
import { spawnSync } from 'node:child_process';
import { availableParallelism, cpus, loadavg, freemem, totalmem } from 'node:os';
const finite = value => typeof value === 'number' && Number.isFinite(value) && value >= 0;
const pair = value => value && finite(value.available) && finite(value.total) && value.total > 0 && value.available <= value.total ? value : { available: null, total: null };
const pressure = text => {
  const match = /^some\s+.*?\bavg10=([\d.]+)(?:\s|$)/m.exec(text);
  return match && finite(Number(match[1])) ? Number(match[1]) : null;
};
export async function readMachineResources({ cwd } = {}, ports = {}) {
  const read = ports.readFile ?? (path => readFileSync(path, 'utf8'));
  const linux = (ports.platform ?? process.platform) === 'linux';
  const observe = async fn => { try { return await fn(); } catch { return null; } };
  let check;
  if (ports.includeChecks) {
    const p = {...machineCheckPorts(ports.env, ports), ...ports};
    check = {cpuIds:await observe(p.cores),platform:p.platform,
      battery:await observe(p.battery),virtualized:await observe(p.virtualized),taskset:await observe(p.taskset)};
  }
  const cpuCount = await observe(ports.cpuCount ?? (() => cpus().length));
  const load = await observe(ports.load ?? (() => loadavg()[0]));
  const memory = pair(await observe(ports.memory ?? (async () => {
    if (!linux) return { available: availableMemory(ports), total: (ports.totalMemory ?? totalmem)() };
    const text = await read('/proc/meminfo');
    return { available: Number(/^MemAvailable:\s+(\d+)\s+kB$/m.exec(text)?.[1]) * 1024,
      total: Number(/^MemTotal:\s+(\d+)\s+kB$/m.exec(text)?.[1]) * 1024 };
  })));
  const io = linux ? await observe(async () => pressure(await read('/proc/pressure/io'))) : null;
  const memoryPressure = linux ? await observe(async () => pressure(await read('/proc/pressure/memory'))) : null;
  const disk = pair(await observe(async () => {
    const row = await (ports.statfs ?? statfsSync)(cwd);
    return { available: Number(row.bavail) * Number(row.bsize), total: Number(row.blocks) * Number(row.bsize) };
  }));
  // The machine guard's facts (#3231): power, the macOS memory pressure level and the cgroup v2 limits.
  const guard = ports.includeGuard ? {
    power: await observe(() => linux ? linuxPower(read, ports.readDir ?? (path => files.readdirSync(path))) : (ports.platform ?? process.platform) === 'darwin' ? macPower(ports) : null),
    level: (ports.platform ?? process.platform) === 'darwin' ? await observe(() => macPressure(ports)) : null,
    cgroup: linux ? (await observe(() => cgroupLimits(read))) ?? { cpus: null, memory: null } : { cpus: null, memory: null },
  } : null;
  return { ...(check ? {check} : {}), cpuCount: Number.isSafeInteger(cpuCount) && cpuCount > 0 ? cpuCount : null,
    load: finite(load) ? load : null, memory, pressure: { io, memory: memoryPressure, ...(guard ? { level: guard.level } : {}) }, disk,
    ...(guard ? { power: guard.power, cgroup: guard.cgroup } : {}) };
}
const run = (ports, name, file, args) => String((ports[name] ?? (() => spawnSync(file, args, { encoding: 'utf8', timeout: 2000 }).stdout))() ?? '');
function macPower(ports) {
  const first = run(ports, 'pmset', 'pmset', ['-g', 'batt']).split('\n')[0] ?? '';
  return /'AC Power'/.test(first) ? 'ac' : /'Battery Power'/.test(first) ? 'battery' : null;
}
function macPressure(ports) {
  const text = (ports.sysctl ? String(ports.sysctl('kern.memorystatus_vm_pressure_level') ?? '') : run(ports, 'sysctl', 'sysctl', ['-n', 'kern.memorystatus_vm_pressure_level'])).trim();
  return /^\d+$/.test(text) ? Number(text) : null;
}
async function linuxPower(read, list) {
  const root = '/sys/class/power_supply', names = await list(root), value = async (name, key) => { try { return String(await read(join(root, name, key))).trim(); } catch { return null; } };
  let battery = false;
  for (const name of names) {
    const type = await value(name, 'type');
    if (['Mains', 'USB'].includes(type) && await value(name, 'online') === '1') return 'ac';
    if (type === 'Battery' && await value(name, 'status') === 'Discharging') battery = true;
  }
  return battery ? 'battery' : null;
}
// cgroup v2: the lowest CPU quota and the lowest memory room of this process's cgroup and its parents.
async function cgroupLimits(read) {
  const line = String(await read('/proc/self/cgroup')).split('\n').find(row => row.startsWith('0::'));
  if (!line) return { cpus: null, memory: null };
  const parts = line.slice(3).trim().split('/').filter(Boolean);
  let cpus = null, memory = null;
  for (let depth = parts.length; depth >= 0; depth--) {
    const dir = join('/sys/fs/cgroup', ...parts.slice(0, depth)), text = async name => { try { return String(await read(join(dir, name))).trim(); } catch { return null; } };
    const [quota, period] = (await text('cpu.max') ?? 'max').split(/\s+/);
    if (quota !== 'max' && Number(quota) > 0 && Number(period) > 0) cpus = Math.min(cpus ?? Infinity, Number(quota) / Number(period));
    const limits = [await text('memory.max'), await text('memory.high')].filter(v => v && v !== 'max').map(Number).filter(v => Number.isFinite(v) && v >= 0);
    const used = Number(await text('memory.current'));
    if (limits.length && Number.isFinite(used)) memory = Math.min(memory ?? Infinity, Math.max(0, Math.min(...limits) - used));
  }
  return { cpus, memory };
}

// macOS keeps reclaimable pages out of free memory: count free, inactive and purgeable pages.
function macAvailable(text) {
  const size = Number(/page size of (\d+) bytes/.exec(text)?.[1]);
  const pages = ['free', 'inactive', 'purgeable'].map(name => Number(new RegExp(`^Pages ${name}:\\s+(\\d+)\\.?$`, 'm').exec(text)?.[1]));
  return size > 0 && pages.every(Number.isSafeInteger) ? pages.reduce((a, b) => a + b, 0) * size : null;
}
function availableMemory(ports = {}) {
  const free = ports.freeMemory ?? freemem;
  if ((ports.platform ?? process.platform) !== 'darwin') return free();
  let text = null;
  try { text = String((ports.vmStat ?? (() => spawnSync('vm_stat', [], { encoding: 'utf8', timeout: 2000 }).stdout))()); } catch { /* Fall back to free memory. */ }
  // Empty output (vm_stat timed out) is a failed read, like malformed text: use free memory.
  return (text ? macAvailable(text) : null) ?? free();
}

function nativeCores() {
  if (process.platform === 'linux') {
    let list;
    try { list = /^Cpus_allowed_list:\s*(.+)$/m.exec(files.readFileSync('/proc/self/status', 'utf8'))?.[1]; } catch { /* Use available parallelism without procfs. */ }
    if (list) return list.split(',').flatMap(part => {
      const [first, last = first] = part.split('-').map(Number);
      return Array.from({length:last - first + 1}, (_, index) => first + index);
    });
  }
  return Array.from({length:availableParallelism()}, (_, index) => index);
}
function nativeBattery() {
  if (process.platform !== 'linux') return false;
  let names;
  try { names = files.readdirSync('/sys/class/power_supply'); } catch (error) { if (error.code === 'ENOENT') return false; throw error; }
  return names.some(name => files.readFileSync(join('/sys/class/power_supply', name, 'type'), 'utf8').trim() === 'Battery');
}
function nativeVirtualized(run = spawnSync) {
  // Unknown detection reserves the person's CPU budget.
  const result = run('systemd-detect-virt', ['--quiet'], {timeout:1000,stdio:'ignore'});
  return result.status === 0;
}
function nativeTaskset(env) {
  if (process.platform !== 'linux') return null;
  for (const folder of (env.PATH ?? '').split(':').filter(isAbsolute)) {
    const path = join(folder, 'taskset');
    try { files.accessSync(path, files.constants.X_OK); if (files.statSync(path).isFile()) return path; } catch {}
  }
  return null;
}

export function machineCheckPorts(env = process.env, ports = {}) {
  return {cores:nativeCores, platform:process.platform, battery:nativeBattery,
    virtualized:()=>nativeVirtualized(ports.spawnSync ?? spawnSync), taskset:()=>nativeTaskset(env),
    memory:()=>availableMemory(ports), load:()=>loadavg()[0]};
}
