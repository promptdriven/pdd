// Owned by prompts/cli/machine-resources.prompt.md.
import { readFileSync, statfsSync } from 'node:fs';
import { cpus, loadavg, freemem, totalmem } from 'node:os';
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
  const cpuCount = await observe(ports.cpuCount ?? (() => cpus().length));
  const load = await observe(ports.load ?? (() => loadavg()[0]));
  const memory = pair(await observe(ports.memory ?? (async () => {
    if (!linux) return { available: freemem(), total: totalmem() };
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
  return { cpuCount: Number.isSafeInteger(cpuCount) && cpuCount > 0 ? cpuCount : null,
    load: finite(load) ? load : null, memory, pressure: { io, memory: memoryPressure }, disk };
}
