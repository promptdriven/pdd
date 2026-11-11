// Generated from prompts/cli/machine-resources.prompt.md (sha256: 9bd70397290ec4f6da93d360f8ce25237da90c79703e21369cd0debf70bafab0).
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
  // The machine guard's facts (#3231): the macOS memory pressure level and the cgroup v2 limits.
  const none = { cpus: null, memoryMax: null, memoryFree: null };
  const guard = ports.includeGuard ? {
    level: (ports.platform ?? process.platform) === 'darwin' ? await observe(() => macPressure(ports)) : null,
    cgroup: linux ? (await observe(() => cgroupLimits(read))) ?? none : none,
  } : null;
  return { ...(check ? {check} : {}), cpuCount: Number.isSafeInteger(cpuCount) && cpuCount > 0 ? cpuCount : null,
    load: finite(load) ? load : null, memory, pressure: { io, memory: memoryPressure, ...(guard ? { level: guard.level } : {}) }, disk,
    ...(guard ? { cgroup: guard.cgroup } : {}) };
}
const run = (ports, name, file, args) => String((ports[name] ?? (() => spawnSync(file, args, { encoding: 'utf8', timeout: 2000 }).stdout))() ?? '');
// The CPU and memory that all Autopilot jobs on this machine use now (#3231, every repository): each job wrapper
// (agent-job.mjs --wrapper) and its process tree, from one process table read. rss in bytes, cores = %CPU / 100.
export function readAutopilotUse(ports = {}) {
  const table = (ports.spawnSync ?? spawnSync)('ps', ['-A', '-o', 'pid=,ppid=,rss=,pcpu=,command='], { encoding: 'utf8', timeout: 5000 });
  if (table.status !== 0) return null;
  const rows = String(table.stdout).split('\n').map(line => /^\s*(\d+)\s+(\d+)\s+(\d+)\s+([\d.]+)\s+(.*)$/.exec(line)).filter(Boolean)
    .map(([, pid, ppid, rss, cpu, command]) => ({ pid: Number(pid), ppid: Number(ppid), rss: Number(rss) * 1024, cpu: Number(cpu) / 100, command }));
  const children = new Map();
  for (const row of rows) children.set(row.ppid, [...(children.get(row.ppid) ?? []), row]);
  const wrappers = rows.filter(row => /agent-job\.mjs\s+--wrapper\s/.test(row.command)), seen = new Set();
  let rss = 0, cores = 0;
  for (const queue = [...wrappers]; queue.length && seen.size < 20000;) {
    const row = queue.shift();
    if (seen.has(row.pid)) continue;
    seen.add(row.pid); rss += row.rss; cores += row.cpu;
    queue.push(...(children.get(row.pid) ?? []));
  }
  return { processes: seen.size, wrappers: wrappers.length, rss, cores: Math.round(cores * 100) / 100 };
}
function macPressure(ports) {
  const text = (ports.sysctl ? String(ports.sysctl('kern.memorystatus_vm_pressure_level') ?? '') : run(ports, 'sysctl', 'sysctl', ['-n', 'kern.memorystatus_vm_pressure_level'])).trim();
  return /^\d+$/.test(text) ? Number(text) : null;
}
// cgroup v2: the lowest CPU quota, the lowest memory limit and the lowest memory room of this process's cgroup and its
// parents.
async function cgroupLimits(read) {
  const line = String(await read('/proc/self/cgroup')).split('\n').find(row => row.startsWith('0::'));
  if (!line) return { cpus: null, memoryMax: null, memoryFree: null };
  const parts = line.slice(3).trim().split('/').filter(Boolean);
  let cpus = null, memoryMax = null, memoryFree = null;
  for (let depth = parts.length; depth >= 0; depth--) {
    const dir = join('/sys/fs/cgroup', ...parts.slice(0, depth)), text = async name => { try { return String(await read(join(dir, name))).trim(); } catch { return null; } };
    const [quota, period] = (await text('cpu.max') ?? 'max').split(/\s+/);
    if (quota !== 'max' && Number(quota) > 0 && Number(period) > 0) cpus = Math.min(cpus ?? Infinity, Number(quota) / Number(period));
    const limits = [await text('memory.max'), await text('memory.high')].filter(v => v && v !== 'max').map(Number).filter(v => Number.isFinite(v) && v >= 0);
    const used = Number(await text('memory.current'));
    if (limits.length) memoryMax = Math.min(memoryMax ?? Infinity, ...limits);
    if (limits.length && Number.isFinite(used)) memoryFree = Math.min(memoryFree ?? Infinity, Math.max(0, Math.min(...limits) - used));
  }
  return { cpus, memoryMax, memoryFree };
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
