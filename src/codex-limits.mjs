// Generated from prompts/cli/codex-limits.prompt.md (sha256: c0d18fbb358f541b7220fe8cffefe72bb26683dff4d475fd80d2fdb9343767d4).
import { spawn } from 'node:child_process';
const unknown = () => ({ state: 'unknown', resetAt: null, usedPercent: null });
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
export function parseCodexLimits(reply) {
  const bucket = reply?.rateLimitsByLimitId?.codex ?? reply?.rateLimits;
  if (!object(bucket)) return unknown();
  const windows = [bucket.primary, bucket.secondary].filter(row => row != null);
  const reached = typeof bucket.rateLimitReachedType === 'string' && bucket.rateLimitReachedType.trim() !== '';
  if (!windows.length && !reached || windows.some(row => !object(row) || typeof row.usedPercent !== 'number'
    || !Number.isFinite(row.usedPercent) || row.usedPercent < 0 || row.resetsAt != null
    && (typeof row.resetsAt !== 'number' || !Number.isFinite(row.resetsAt) || row.resetsAt < 0 || row.resetsAt > 8.64e12))) return unknown();
  const blocked = windows.filter(row => row.usedPercent >= 100);
  const limited = blocked.length > 0 || reached;
  const resets = blocked.length ? blocked : reached ? windows : [];
  return { state: limited ? 'limited' : 'healthy',
    resetAt: resets.length && resets.every(row => row.resetsAt != null) ? Math.max(...resets.map(row => row.resetsAt * 1000)) : null,
    usedPercent: windows.length ? Math.max(...windows.map(row => row.usedPercent)) : null };
}
const HEALTH_CLIENT = { name: 'pdd_health', title: 'PDD health', version: '1' };
export async function readCodexRateLimitsReply({ command = 'codex', cwd, env = process.env, clientInfo = HEALTH_CLIENT } = {}, ports = {}) {
  const failed = reason => ({ ok: false, reason });
  return new Promise(resolve => {
    let child, done = false, buffer = '', size = 0, initialized = false, timer;
    const finish = (value, closed = false) => {
      if (done) return;
      done = true; clearTimeout(timer);
      if (!child || closed) { resolve(value); return; }
      const complete = () => { clearTimeout(kill); clearTimeout(cleanup); resolve(value); };
      const kill = setTimeout(() => {
        if (child.exitCode == null && child.signalCode == null) child.kill('SIGKILL');
      }, 500);
      const cleanup = setTimeout(() => {
        // Descendants can retain inherited pipes after the direct child exits.
        child.stdin.destroy(); child.stdout.destroy(); child.stderr.destroy();
        child.unref?.(); complete();
      }, 1_000);
      child.once('close', complete);
      child.stdin.end(); child.kill('SIGTERM');
    };
    const send = value => child.stdin.write(JSON.stringify(value) + '\n');
    timer = setTimeout(() => finish(failed('timeout')), 10_000);
    try {
      child = (ports.spawn ?? spawn)(command, ['app-server', '--listen', 'stdio://'], { cwd, env, stdio: ['pipe', 'pipe', 'pipe'], shell: false });
      child.on('error', () => finish(failed('spawn')));
      child.on('close', () => finish(failed('exit'), true));
      child.stdin.on('error', () => finish(failed('exit')));
      const data = chunk => {
        size += chunk.length;
        if (size > 1024 * 1024) { finish(failed('output')); return false; }
        return !done;
      };
      child.stderr.on('data', data);
      child.stdout.on('data', chunk => {
        if (!data(chunk)) return;
        buffer += chunk.toString();
        let end;
        while (!done && (end = buffer.indexOf('\n')) !== -1) {
          const line = buffer.slice(0, end); buffer = buffer.slice(end + 1);
          let row; try { row = JSON.parse(line); } catch { finish(failed('protocol')); return; }
          if (!object(row)) { finish(failed('protocol')); return; }
          if (row.id === 1 && !initialized) {
            if (row.error) { finish(failed('error')); return; }
            if (!object(row.result)) { finish(failed('protocol')); return; }
            initialized = true;
            send({ method: 'initialized' }); send({ method: 'account/rateLimits/read', id: 2 });
          } else if (row.id === 2 && initialized) finish(row.error ? failed('error') : { ok: true, reply: row.result });
        }
      });
      send({ method: 'initialize', id: 1, params: { clientInfo } });
    } catch { finish(failed('spawn')); }
  });
}
export async function readCodexLimits({ command = 'codex', cwd, env = process.env } = {}, ports = {}) {
  const read = await readCodexRateLimitsReply({ command, cwd, env }, ports);
  return read.ok ? parseCodexLimits(read.reply) : unknown();
}
