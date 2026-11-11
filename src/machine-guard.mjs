// Generated from prompts/cli/machine-guard.prompt.md (sha256: 94020734119888c501789d931bbbd02710f32c13a049ddccfbfeb21d53dce0ae).
// The small resource governor of the Autopilot core (#3231): machine class, slots, room for new work, process priority
// and cleanup limits, from the machine itself. Only readMachineGuard reads (through the machine observations).
import { readMachineResources } from './machine-resources.mjs';

const GiB = 1024 ** 3, MiB = 1024 ** 2;
// Every number of the guard, in one place.
export const GUARD = Object.freeze({
  laptop: Object.freeze({ slots: 1, memoryBytes: 2 * GiB, memoryShare: 0.15, diskBytes: 10 * GiB, diskShare: 0.05, cpuShare: 0.5, checkLoad: true, checkPower: true, memoryHigh: '50%' }),
  server: Object.freeze({ maxSlots: 4, coresPerSlot: 2, bytesPerSlot: 3 * GiB, memoryShare: 0.10, diskBytes: 1 * GiB, diskShare: 0.05, cpuShare: 1, checkLoad: false, checkPower: false, memoryHigh: null }),
  nice: 19, cpuWeight: 20, qos: 'utility', logDays: 14, logBytes: 500 * MiB,
});
const PRESSURE_PSI = 10;
const count = value => Number.isSafeInteger(value) && value > 0 ? value : null;
const finite = value => typeof value === 'number' && Number.isFinite(value) && value >= 0;
const gib = bytes => `${Math.round(bytes / GiB * 10) / 10}`;
const one = value => `${Math.round(value * 10) / 10}`;

export function machineClass({ platform, battery, virtualized } = {}) {
  // Unknown virtualization reserves the person's machine, like the suite queue's personal rule.
  return platform === 'darwin' || platform === 'linux' && (battery === true || virtualized !== true) ? 'laptop' : 'server';
}
export function usableCores(resources) {
  const ids = Array.isArray(resources?.check?.cpuIds) && resources.check.cpuIds.length ? resources.check.cpuIds.length : count(resources?.cpuCount);
  const quota = finite(resources?.cgroup?.cpus) && resources.cgroup.cpus > 0 ? Math.max(1, Math.floor(resources.cgroup.cpus)) : null;
  return ids === null ? quota : quota === null ? ids : Math.min(ids, quota);
}
export function freeMemory(resources) {
  const host = finite(resources?.memory?.available) ? resources.memory.available : null, room = finite(resources?.cgroup?.memory) ? resources.cgroup.memory : null;
  return host === null ? room : room === null ? host : Math.min(host, room);
}
export const cpuShare = (resources, klass) => Math.max(1, Math.floor((usableCores(resources) ?? 1) * GUARD[klass === 'laptop' ? 'laptop' : 'server'].cpuShare));
export function autoSlots(resources, klass) {
  if (klass === 'laptop') return GUARD.laptop.slots;
  const g = GUARD.server, cores = usableCores(resources), memory = freeMemory(resources);
  return Math.max(1, Math.min(g.maxSlots, cores === null ? Infinity : Math.floor(cores / g.coresPerSlot), memory === null ? Infinity : Math.floor(memory / g.bytesPerSlot)));
}
export function slotCount({ klass, auto, runs, repoRuns } = {}) {
  if (count(runs)) return { slots: runs, source: `this machine (--runs ${runs})` };
  const automatic = count(auto) ?? 1;
  if (klass !== 'laptop' && count(repoRuns) && repoRuns < automatic) return { slots: repoRuns, source: 'pdd.json autopilot.runs' };
  return { slots: automatic, source: 'automatic' };
}
const pressured = resources => (finite(resources?.pressure?.level) && resources.pressure.level > 1) || (finite(resources?.pressure?.memory) && resources.pressure.memory >= PRESSURE_PSI);
export function machineRoom(resources, klass) {
  const laptop = klass === 'laptop', g = GUARD[laptop ? 'laptop' : 'server'];
  const no = reason => ({ ok: false, reason });
  if (g.checkPower && resources?.power === 'battery') return no('on battery power');
  const memory = resources?.memory, free = freeMemory(resources);
  if (!finite(memory?.total) || memory.total <= 0 || free === null) return no('memory cannot be read');
  const needMemory = laptop ? Math.max(g.memoryBytes, g.memoryShare * memory.total) : g.memoryShare * memory.total;
  if (free < needMemory) return no(`only ${gib(free)} GiB of memory free (needs ${laptop ? `${gib(g.memoryBytes)} GiB and ` : ''}${Math.round(g.memoryShare * 100)}%)`);
  if (laptop && pressured(resources)) return no('memory pressure');
  const disk = resources?.disk;
  if (!finite(disk?.available) || !finite(disk?.total) || disk.total <= 0) return no('disk cannot be read');
  if (disk.available < g.diskBytes || disk.available < g.diskShare * disk.total) return no(`only ${gib(disk.available)} GiB of disk free (needs ${gib(g.diskBytes)} GiB and ${Math.round(g.diskShare * 100)}%)`);
  if (g.checkLoad && finite(resources?.load)) {
    const share = cpuShare(resources, klass);
    if (resources.load > share) return no(`load ${one(resources.load)} is above Autopilot's share of ${share} cores`);
  }
  return { ok: true, reason: null };
}
const cpuList = ids => {
  const parts = [];
  for (let i = 0; i < ids.length; i++) {
    let j = i; while (j + 1 < ids.length && ids[j + 1] === ids[j] + 1) j++;
    parts.push(j > i ? `${ids[i]}-${ids[j]}` : `${ids[i]}`); i = j;
  }
  return parts.join(',');
};
const UNPINNED = new Set(['suite', 'vectors', 'runtime']);
export function jobPriority({ klass, platform, role, resources, taskset } = {}) {
  const share = cpuShare(resources, klass), ids = Array.isArray(resources?.check?.cpuIds) ? resources.check.cpuIds : [];
  const pin = platform === 'linux' && klass === 'laptop' && typeof taskset === 'string' && taskset.startsWith('/') && !UNPINNED.has(role) && ids.length > share;
  return { nice: GUARD.nice, qos: platform === 'darwin' ? GUARD.qos : null, cpus: pin ? cpuList(ids.slice(0, share)) : null, taskset: pin ? taskset : null, checkCpus: share };
}
export function timerPriority(klass, platform) {
  return { plist: platform === 'darwin' ? `<key>Nice</key><integer>${GUARD.nice}</integer>` : '',
    unit: platform === 'linux' ? `Nice=${GUARD.nice}\nCPUWeight=${GUARD.cpuWeight}\n${klass === 'laptop' ? `MemoryHigh=${GUARD.laptop.memoryHigh}\n` : ''}` : '' };
}
export function guardLine({ klass, slots, source, room, resources } = {}) {
  const cores = usableCores(resources), memory = resources?.memory, free = freeMemory(resources), disk = resources?.disk;
  const pressure = finite(resources?.pressure?.level) ? ({ 1: 'normal', 2: 'warn', 4: 'critical' }[resources.pressure.level] ?? `level ${resources.pressure.level}`)
    : finite(resources?.pressure?.memory) ? `PSI ${one(resources.pressure.memory)}` : 'unknown';
  return [`Machine: ${klass}`, `${cores ?? 'unknown'} cores, Autopilot uses ${cores ? cpuShare(resources, klass) : 'unknown'}`,
    `memory ${free === null ? 'unknown' : gib(free)} of ${finite(memory?.total) ? gib(memory.total) : 'unknown'} GiB free, pressure ${pressure}`,
    `disk ${finite(disk?.available) ? gib(disk.available) : 'unknown'} GiB free`, `load ${finite(resources?.load) ? one(resources.load) : 'unknown'}`,
    resources?.power === 'battery' ? 'battery power' : resources?.power === 'ac' ? 'AC power' : 'power unknown (counts as AC)', 'priority low',
    `${slots} slot${slots === 1 ? '' : 's'} (${source})`, `new work: ${room?.ok ? 'ok' : `held (${room?.reason ?? 'unknown'})`}`].join(' · ');
}
export async function readMachineGuard({ cwd, runs, repoRuns } = {}, ports = {}) {
  let resources = null;
  try { resources = await (ports.machineResources ?? (input => readMachineResources(input, { ...ports, includeChecks: true, includeGuard: true })))({ cwd }); } catch { resources = null; }
  const platform = resources?.check?.platform ?? ports.platform ?? process.platform;
  const klass = machineClass({ platform, battery: resources?.check?.battery, virtualized: resources?.check?.virtualized });
  const auto = resources ? autoSlots(resources, klass) : 1, { slots, source } = slotCount({ klass, auto, runs, repoRuns });
  const room = resources ? machineRoom(resources, klass) : { ok: false, reason: 'machine resources cannot be read' };
  const guard = { klass, slots, source, auto, room, resources,
    priority: role => jobPriority({ klass, platform, role, resources, taskset: resources?.check?.taskset ?? null }) };
  guard.line = guardLine(guard);
  return guard;
}
