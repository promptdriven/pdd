// Owned by prompts/cli/autopilot-environment.prompt.md.
import { readFileSync, readdirSync, accessSync, constants } from 'node:fs';
import { loadavg, cpus, freemem, totalmem } from 'node:os';
import { join, isAbsolute } from 'node:path';

export const ENVIRONMENT_BACKOFF = Object.freeze([15 * 60_000, 60 * 60_000, 4 * 60 * 60_000]);
const validations = new Set(['check', 'verify', 'formal']);
export function classifyStuckCause(reason, runtime = false) {
  if (runtime) return 'interpreter';
  const text = String(reason ?? '');
  const validation = /\b(?:tests?|checks?|expectations?|suite|validations?)\b/i.test(text);
  const failure = /\bfail(?:s|ed|ing|ure|ures)?\b|\bred\b/i.test(text);
  if (/assertion|must[- ]fix|\bdecision\b|unresolved|separate code.*blocker/i.test(text) || validation && failure) return 'work';
  if (/unknown (outcome|result)|no[- ]verdict|saved[- ]batch|interpreter.*(unknown|reconcil|outage|wake)/i.test(text)) return 'interpreter';
  if (validation && /stall|timed? out|timeout|killed|cancelled|canceled|incomplete|ETIMEDOUT/i.test(text)) return 'environment';
  return /filesystem journal|(?:disk|memory|I\/O) (?:pressure|stall|contention|full)|(?:native|test|suite|validation)[^.;\n]*(?:stall|timed? out|timeout|killed|cancelled|incomplete|ETIMEDOUT)|(?:full|suite) queue|queue (?:is )?full|missing tool|tool[^.;\n]*not found/i.test(text) ? 'environment' : 'work';
}
export function environmentRecovery(run) {
  if (!run?.automaticOrigin || run.state !== 'stuck' || run.repairLimit || classifyStuckCause(run.parkReason) !== 'environment') return null;
  const retry = run.environmentRetry;
  if (!retry || !Number.isFinite(retry.at) || !Number.isInteger(retry.attempts) || retry.attempts < 0 || retry.attempts > ENVIRONMENT_BACKOFF.length
    || retry.area !== run.area || !validations.has(retry.step) || !run.areas?.[run.area]?.steps?.includes(retry.step)
    || typeof retry.reason !== 'string' || classifyStuckCause(retry.reason) !== 'environment'
    || (retry.attempts < ENVIRONMENT_BACKOFF.length ? !Number.isFinite(retry.nextAt) || retry.nextAt < retry.at : retry.nextAt !== null)) return null;
  return retry;
}
export function environmentStatus(run) {
  const retry = environmentRecovery(run);
  if (!retry) return null;
  return retry.attempts >= ENVIRONMENT_BACKOFF.length
    ? `stuck (environment): ${retry.reason}; validation ${retry.step} failed after ${retry.attempts} retries`
    : `retrying after environment failure (attempt ${retry.attempts + 1} of ${ENVIRONMENT_BACKOFF.length}, next at ${new Date(retry.nextAt).toISOString()}): ${retry.reason}`;
}
export const environmentWakeTag = retry => `Environment validation wake for ${retry.area}:${retry.step} at ${new Date(retry.at).toISOString()} attempt ${retry.attempts + 1}.`;
const missingTool = reason => /missing tool\s*:?\s*([\w.-]+)|tool\s+([\w.-]+)\s+(?:is\s+)?not found/i.exec(reason ?? '');
const psi = text => {
  const value = /^some\s+.*?\bavg10=([\d.]+)(?:\s|$)/m.exec(text)?.[1];
  return value !== undefined && Number.isFinite(Number(value)) && Number(value) < 10;
};
export async function environmentHealthy({ env = process.env, reason = '' } = {}, ports = {}) {
  const readFile = ports.readFile ?? (path => readFileSync(path, 'utf8'));
  const readDir = ports.readDir ?? readdirSync;
  try {
    const count = (ports.cpuCount ?? (() => cpus().length))(), load = (ports.load ?? (() => loadavg()[0]))();
    if (!Number.isFinite(count) || count <= 0 || !Number.isFinite(load) || load < 0 || load / count >= 1) return false;
    const memory = await (ports.memory ?? (() => {
      if (process.platform !== 'linux') return { available: freemem(), total: totalmem() };
      const text = readFile('/proc/meminfo');
      return { available: Number(/^MemAvailable:\s+(\d+)/m.exec(text)?.[1]), total: Number(/^MemTotal:\s+(\d+)/m.exec(text)?.[1]) };
    }))();
    if (!Number.isFinite(memory.available) || !Number.isFinite(memory.total) || memory.total <= 0 || memory.available / memory.total < 0.1) return false;
    if ((ports.platform ?? process.platform) === 'linux' && (!psi(await readFile('/proc/pressure/io')) || !psi(await readFile('/proc/pressure/memory')))) return false;
    if (/missing tool|tool.*not found/i.test(reason)) {
      const match = missingTool(reason), tool = match?.[1] ?? match?.[2];
      if (!tool || !await (ports.toolPresent ?? (tool => (env.PATH ?? '').split(':').filter(Boolean).some(dir => { try { accessSync(join(dir, tool), constants.X_OK); return true; } catch { return false; } })))(tool)) return false;
    }
    if (ports.suiteAvailable) return await ports.suiteAvailable({ env }) === true;
    const root = env.PDD_SUITE_QUEUE ?? (env.PDD_VM_SUITE_LOCK ? `${env.PDD_VM_SUITE_LOCK}.queue` : `/tmp/pdd-full-suite-${process.getuid?.() ?? 'user'}`);
    if (!isAbsolute(root)) return false;
    let names;
    try { names = await readDir(root); } catch (error) { return error.code === 'ENOENT'; }
    let running = 0;
    for (const name of names.filter(name => /^ticket-.*\.json$/.test(name))) {
      const row = JSON.parse(await readFile(join(root, name)));
      if (!Number.isSafeInteger(row.ticket) || row.ticket <= 0 || !Number.isSafeInteger(row.pid) || row.pid <= 0 || !['waiting', 'running', 'finished'].includes(row.state)
        || typeof row.cwd !== 'string' || !Number.isFinite(row.queuedAt)
        || row.startedAt !== null && !Number.isFinite(row.startedAt) || row.finishedAt !== null && !Number.isFinite(row.finishedAt)) return false;
      if (row.state === 'waiting') return false;
      if (row.state === 'running') running++;
    }
    return running < 3;
  } catch { return false; }
}
