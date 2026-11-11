// Generated from prompts/cli/machine-guard.prompt.md (sha256: 72c88d0eab14f0aa85745d4ed18612b396700bc37acd1d57c9bf99d4b9bacf1a).
// The small resource governor of the Autopilot core (#3231): Autopilot may use a share of this machine's CPU and
// memory (default 50%, `pdd autopilot start --share N`). The share of the real limits gives the slots and the room for
// new work; the priority and the cleanup limits are fixed. Only readMachineGuard reads (through the machine
// observations).
import { readMachineResources } from './machine-resources.mjs';

const GiB = 1024 ** 3, MiB = 1024 ** 2;
// Every number of the guard, in one place.
export const GUARD = Object.freeze({
  share: 50,                       // percent of the CPU and memory that Autopilot may use, by default
  maxSlots: 4,                     // never more jobs at once
  jobCores: 2, jobBytes: 3 * GiB,  // one job: an agent (0.1-0.3 GiB, under 1 core) and its part of one full suite (2.3-2.8 GiB)
  diskBytes: 10 * GiB, diskShare: 0.05,  // a job makes up to 3 checkouts and installs dependencies
  pressurePsi: 10,                 // Linux PSI memory some avg10; macOS: a pressure level above 1 (normal)
  nice: 19, cpuWeight: 20, qos: 'utility',
  logDays: 14, logBytes: 500 * MiB,
});
const count = value => Number.isSafeInteger(value) && value > 0 ? value : null;
const finite = value => typeof value === 'number' && Number.isFinite(value) && value >= 0;
const gib = bytes => `${Math.round(bytes / GiB * 10) / 10}`;
const one = value => `${Math.round(value * 10) / 10}`;

// A share is a whole percent from 1 to 100; anything else is the default.
export const validShare = value => Number.isSafeInteger(value) && value >= 1 && value <= 100;
export const shareOf = value => validShare(value) ? value : GUARD.share;
export function usableCores(resources) {
  const ids = Array.isArray(resources?.check?.cpuIds) && resources.check.cpuIds.length ? resources.check.cpuIds.length : count(resources?.cpuCount);
  const quota = finite(resources?.cgroup?.cpus) && resources.cgroup.cpus > 0 ? Math.max(1, Math.floor(resources.cgroup.cpus)) : null;
  return ids === null ? quota : quota === null ? ids : Math.min(ids, quota);
}
const lower = (a, b) => a === null ? b : b === null ? a : Math.min(a, b);
export const memoryLimit = resources => lower(finite(resources?.memory?.total) && resources.memory.total > 0 ? resources.memory.total : null, finite(resources?.cgroup?.memoryMax) ? resources.cgroup.memoryMax : null);
export const freeMemory = resources => lower(finite(resources?.memory?.available) ? resources.memory.available : null, finite(resources?.cgroup?.memoryFree) ? resources.cgroup.memoryFree : null);
export const shareCores = (resources, share = GUARD.share) => Math.max(1, Math.floor((usableCores(resources) ?? 1) * shareOf(share) / 100));
// The slot math: the share of the cores per job and the share of the memory per job, at least 1, at most maxSlots.
export function slotMath(resources, share = GUARD.share) {
  const s = shareOf(share), cores = usableCores(resources), limit = memoryLimit(resources);
  const byCores = cores === null ? null : Math.floor(cores * s / 100 / GUARD.jobCores), byMemory = limit === null ? null : Math.floor(limit * s / 100 / GUARD.jobBytes);
  // An unknown value leaves out its term; with no known term the guard takes 1.
  const slots = byCores === null && byMemory === null ? 1 : Math.max(1, Math.min(GUARD.maxSlots, byCores ?? Infinity, byMemory ?? Infinity));
  return { slots, share: s, cores, limit, byCores, byMemory };
}
export const autoSlots = (resources, share) => slotMath(resources, share).slots;
export function slotCount({ auto, runs, repoRuns } = {}) {
  if (count(runs)) return { slots: runs, source: `this machine, --runs ${runs}` };
  const automatic = count(auto) ?? 1;
  if (count(repoRuns) && repoRuns < automatic) return { slots: repoRuns, source: 'pdd.json autopilot.runs' };
  return { slots: automatic, source: 'automatic' };
}
const pressured = resources => (finite(resources?.pressure?.level) && resources.pressure.level > 1) || (finite(resources?.pressure?.memory) && resources.pressure.memory >= GUARD.pressurePsi);
export function machineRoom(resources, share = GUARD.share) {
  const no = reason => ({ ok: false, reason }), free = freeMemory(resources);
  if (free === null) return no('memory cannot be read');
  if (free < GUARD.jobBytes) return no(`only ${gib(free)} GiB of memory free; a job needs ${gib(GUARD.jobBytes)} GiB`);
  if (pressured(resources)) return no('memory pressure');
  const disk = resources?.disk;
  if (!finite(disk?.available) || !finite(disk?.total) || disk.total <= 0) return no('disk cannot be read');
  if (disk.available < GUARD.diskBytes || disk.available < GUARD.diskShare * disk.total) return no(`only ${gib(disk.available)} GiB of disk free; a job needs ${gib(GUARD.diskBytes)} GiB and ${Math.round(GUARD.diskShare * 100)}%`);
  const cores = shareCores(resources, share);
  if (finite(resources?.load) && resources.load > cores) return no(`load ${one(resources.load)} is above ${cores} cores, Autopilot's ${shareOf(share)}% share`);
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
// The suite queue pins suites to its own CPU list (pinning them here would halve it again); pdd test is a waiting client.
const UNPINNED = new Set(['suite', 'vectors', 'runtime']);
export function jobPriority({ platform, role, resources, share = GUARD.share, taskset } = {}) {
  const cores = shareCores(resources, share), ids = Array.isArray(resources?.check?.cpuIds) ? resources.check.cpuIds : [];
  const pin = platform === 'linux' && typeof taskset === 'string' && taskset.startsWith('/') && !UNPINNED.has(role) && ids.length > cores;
  return { nice: GUARD.nice, qos: platform === 'darwin' ? GUARD.qos : null, cpus: pin ? cpuList(ids.slice(0, cores)) : null, taskset: pin ? taskset : null, checkCpus: cores };
}
export function timerPriority(platform, share = GUARD.share) {
  return { plist: platform === 'darwin' ? `<key>Nice</key><integer>${GUARD.nice}</integer>` : '',
    unit: platform === 'linux' ? `Nice=${GUARD.nice}\nCPUWeight=${GUARD.cpuWeight}\nMemoryHigh=${shareOf(share)}%\n` : '' };
}
export function guardLine({ share, shareSource, slots, source, room, resources } = {}) {
  const m = slotMath(resources, share), free = freeMemory(resources), disk = resources?.disk;
  const pressure = finite(resources?.pressure?.level) ? ({ 1: 'normal', 2: 'warn', 4: 'critical' }[resources.pressure.level] ?? `level ${resources.pressure.level}`)
    : finite(resources?.pressure?.memory) ? `PSI ${one(resources.pressure.memory)}` : 'unknown';
  const math = `min(${GUARD.maxSlots}, ${m.cores === null ? '?' : one(m.cores * m.share / 100)} cores ÷ ${GUARD.jobCores}, ${m.limit === null ? '?' : gib(m.limit * m.share / 100)} GiB ÷ ${gib(GUARD.jobBytes)} GiB) = ${m.slots}`;
  return [`Machine: share ${m.share}% (${shareSource ?? 'default'}) of ${m.cores ?? 'unknown'} cores and ${m.limit === null ? 'unknown' : gib(m.limit)} GiB`,
    `slots ${math} → ${slots} (${source})`, `memory ${free === null ? 'unknown' : gib(free)} GiB free, pressure ${pressure}`,
    `disk ${finite(disk?.available) ? gib(disk.available) : 'unknown'} GiB free`, `load ${finite(resources?.load) ? one(resources.load) : 'unknown'}`, 'priority low',
    `new work: ${room?.ok ? 'ok' : `held (${room?.reason ?? 'unknown'})`}`].join(' · ');
}
export async function readMachineGuard({ cwd, runs, repoRuns, share } = {}, ports = {}) {
  let resources = null;
  try { resources = await (ports.machineResources ?? (input => readMachineResources(input, { ...ports, includeChecks: true, includeGuard: true })))({ cwd }); } catch { resources = null; }
  const platform = resources?.check?.platform ?? ports.platform ?? process.platform, s = shareOf(share);
  const auto = resources ? autoSlots(resources, s) : 1, { slots, source } = slotCount({ auto, runs, repoRuns });
  const room = resources ? machineRoom(resources, s) : { ok: false, reason: 'machine resources cannot be read' };
  const guard = { share: s, shareSource: validShare(share) ? 'this machine, --share' : 'default', slots, source, auto, room, resources,
    priority: role => jobPriority({ platform, role, resources, share: s, taskset: resources?.check?.taskset ?? null }) };
  guard.line = guardLine(guard);
  return guard;
}
