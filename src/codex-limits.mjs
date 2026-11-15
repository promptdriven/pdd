// Generated from prompts/cli/codex-limits.prompt.md (sha256: ac0b69b21808e53f1d3cfaeda407adaf8b6ad44a36106a8a133419abc2dfb1dc).
import { spawn } from 'node:child_process';
const unknown = () => ({ state: 'unknown', resetAt: null, usedPercent: null });
const unknownWindows = () => ({
  state: 'unknown',
  resetAt: null,
  usedPercent: null,
  five_hour_used_percent: null,
  five_hour_reset_at: null,
  weekly_used_percent: null,
  weekly_reset_at: null,
  limit_reached: false,
});
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const stopThreshold = (value, fallback = 97) => typeof value === 'number' && Number.isFinite(value) && value > 0 && value <= 100 ? value : fallback;
const validWindow = row => object(row) && typeof row.usedPercent === 'number'
  && Number.isFinite(row.usedPercent) && row.usedPercent >= 0
  && (row.resetsAt == null || (typeof row.resetsAt === 'number' && Number.isFinite(row.resetsAt) && row.resetsAt >= 0 && row.resetsAt <= 8.64e12));
const isoOfSeconds = sec => (typeof sec === 'number' && Number.isFinite(sec) && sec >= 0 && sec <= 8.64e12)
  ? new Date(sec * 1000).toISOString()
  : null;

function inspectCodexBucket(reply, weeklyStop) {
  const bucket = reply?.rateLimitsByLimitId?.codex ?? reply?.rateLimits;
  if (!object(bucket)) return null;
  const primaryMins = bucket.primary?.windowDurationMins;
  const primaryIsWeekly = (typeof primaryMins === 'number' && Number.isFinite(primaryMins))
    ? primaryMins >= 1440
    : (bucket.secondary == null && (String(bucket.planType ?? reply?.planType ?? '').toLowerCase() === 'pro'
      || bucket.credits?.hasCredits === true || reply?.credits?.hasCredits === true));
  const entries = [
    ['primary', bucket.primary, primaryIsWeekly ? weeklyStop : 100],
    ['secondary', bucket.secondary, weeklyStop],
  ].filter(([, row]) => row != null);
  const windows = entries.map(([, row]) => row);
  const reached = (typeof bucket.rateLimitReachedType === 'string' && bucket.rateLimitReachedType.trim() !== '')
    || bucket.spendControlReached === true || reply?.spendControlReached === true;
  if (!windows.length && !reached || windows.some(row => !validWindow(row))) return null;
  const blocked = entries.filter(([, row, limit]) => row.usedPercent >= limit).map(([, row]) => row);
  const limited = blocked.length > 0 || reached;
  const resets = blocked.length ? blocked : reached ? windows : [];
  const fiveHour = primaryIsWeekly ? null : (bucket.primary ?? null);
  const weekly = primaryIsWeekly ? (bucket.primary ?? null) : (bucket.secondary ?? null);
  return {
    state: limited ? 'limited' : 'healthy',
    resetAt: resets.length && resets.every(row => row.resetsAt != null) ? Math.max(...resets.map(row => row.resetsAt * 1000)) : null,
    usedPercent: windows.length ? Math.max(...windows.map(row => row.usedPercent)) : null,
    fiveHour,
    weekly,
    limited,
  };
}

export function parseCodexLimits(reply, { weeklyStopPercent = 97 } = {}) {
  const parsed = inspectCodexBucket(reply, stopThreshold(weeklyStopPercent, 97));
  if (!parsed) return unknown();
  return { state: parsed.state, resetAt: parsed.resetAt, usedPercent: parsed.usedPercent };
}

export function parseCodexUsageWindows(reply, { weeklyStopPercent = 100 } = {}) {
  const parsed = inspectCodexBucket(reply, stopThreshold(weeklyStopPercent, 100));
  if (!parsed) return unknownWindows();
  return {
    state: parsed.state,
    resetAt: parsed.resetAt,
    usedPercent: parsed.usedPercent,
    five_hour_used_percent: parsed.fiveHour ? parsed.fiveHour.usedPercent : null,
    five_hour_reset_at: parsed.fiveHour ? isoOfSeconds(parsed.fiveHour.resetsAt) : null,
    weekly_used_percent: parsed.weekly ? parsed.weekly.usedPercent : null,
    weekly_reset_at: parsed.weekly ? isoOfSeconds(parsed.weekly.resetsAt) : null,
    limit_reached: parsed.limited,
  };
}

function exchangeCodexRateLimits({ command = 'codex', cwd, env = process.env, timeoutMs = 10_000 }, ports, fallback, onResult) {
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
    const limitMs = typeof timeoutMs === 'number' && Number.isFinite(timeoutMs) && timeoutMs > 0 ? timeoutMs : 10_000;
    timer = setTimeout(() => finish(fallback()), limitMs);
    try {
      child = (ports.spawn ?? spawn)(command, ['app-server', '--listen', 'stdio://'], { cwd, env, stdio: ['pipe', 'pipe', 'pipe'], shell: false });
      child.on('error', () => finish(fallback()));
      child.on('close', () => finish(fallback(), true));
      child.stdin.on('error', () => finish(fallback()));
      const data = chunk => {
        size += chunk.length;
        if (size > 1024 * 1024) { finish(fallback()); return false; }
        return !done;
      };
      child.stderr.on('data', data);
      child.stdout.on('data', chunk => {
        if (!data(chunk)) return;
        buffer += chunk.toString();
        let end;
        while (!done && (end = buffer.indexOf('\n')) !== -1) {
          const line = buffer.slice(0, end); buffer = buffer.slice(end + 1);
          let row; try { row = JSON.parse(line); } catch { finish(fallback()); return; }
          if (!object(row)) { finish(fallback()); return; }
          if (row.id === 1 && !initialized) {
            if (row.error || !object(row.result)) { finish(fallback()); return; }
            initialized = true;
            send({ method: 'initialized' }); send({ method: 'account/rateLimits/read', id: 2 });
          } else if (row.id === 2 && initialized) finish(row.error ? fallback() : onResult(row.result));
        }
      });
      send({ method: 'initialize', id: 1, params: { clientInfo: { name: 'pdd_health', title: 'PDD health', version: '1' } } });
    } catch { finish(fallback()); }
  });
}

export async function readCodexLimits({ command = 'codex', cwd, env = process.env, weeklyStopPercent } = {}, ports = {}) {
  return exchangeCodexRateLimits({ command, cwd, env }, ports, unknown, result => parseCodexLimits(result, { weeklyStopPercent }));
}

export async function readCodexUsageWindows({ command = 'codex', cwd, env = process.env, weeklyStopPercent = 100, timeoutMs = 10_000 } = {}, ports = {}) {
  return exchangeCodexRateLimits({ command, cwd, env, timeoutMs }, ports, unknownWindows, result => parseCodexUsageWindows(result, { weeklyStopPercent }));
}
