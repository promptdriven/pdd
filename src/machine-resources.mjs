// Generated from prompts/cli/machine-resources.prompt.md (sha256: b0cbcac8d1670bc0fae7973e6325220c3fc2fcb876ee1b006101ca79b8f46f2e).
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
  return { ...(check ? {check} : {}), cpuCount: Number.isSafeInteger(cpuCount) && cpuCount > 0 ? cpuCount : null,
    load: finite(load) ? load : null, memory, pressure: { io, memory: memoryPressure }, disk };
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
  return (text && macAvailable(text)) ?? free();
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
