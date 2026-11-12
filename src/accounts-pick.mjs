// Generated from prompts/cli/accounts-pick.prompt.md (sha256: 56e687e44427f9463bae28b062afc54ac732d4d5d5a1cd4422e9a9309dd9f329).
export const STALE_MS = 600000, DAY_MS = 86400000, BACK_SOON_MS = 7200000;
const HOUR_MS = 3600000, MINUTE_MS = 60000;
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const finite = value => typeof value === 'number' && Number.isFinite(value);
const own = (map, key) => object(map) && Object.hasOwn(map, key) ? map[key] : undefined;
const list = value => Array.isArray(value) ? value : [];
const loginsOf = value => list(value).filter(login => object(login) && typeof login.name === 'string');
const stopLine = value => finite(value) && value > 0 && value <= 100 ? value : 97;
const result = (reason, until = null) => ({ ready: reason === 'ready', reason, until });

// One window: absent (no limit), malformed, or { used, resetsAt } with resetsAt null when unknown.
function windowOf(value) {
  if (value === undefined || value === null) return { absent: true };
  if (!object(value) || !finite(value.usedPercent)) return { malformed: true };
  return { used: value.usedPercent, resetsAt: finite(value.resetsAt) ? value.resetsAt : null };
}

export function loginReadiness(login, usageRow, now) {
  if (login?.paused === true) return result('paused');
  if (!object(usageRow)) return result('stale');
  const limitedUntil = finite(usageRow.limitedUntil) && usageRow.limitedUntil > now ? usageRow.limitedUntil : null;
  const limitedOr = other => limitedUntil === null ? result(other) : result('limited', limitedUntil);
  const fresh = finite(usageRow.readAt) && now - usageRow.readAt <= STALE_MS;
  if (!fresh) return limitedOr('stale');
  if (['no-login', 'needs-sign-in', 'expired'].includes(usageRow.state)) return result(usageRow.state);
  const week = windowOf(usageRow.week), fiveHour = windowOf(usageRow.fiveHour);
  if (usageRow.state !== 'ok' || week.malformed || fiveHour.malformed) return limitedOr('unknown');
  const weekBlocked = !week.absent && week.used >= stopLine(login?.stop?.week);
  const fiveBlocked = !fiveHour.absent && fiveHour.used >= stopLine(login?.stop?.fiveHour);
  const blocked = [weekBlocked && week, fiveBlocked && fiveHour].filter(Boolean);
  if (blocked.some(row => row.resetsAt !== null && row.resetsAt <= now)) return limitedOr('stale');
  if (blocked.length) {
    const until = blocked.some(row => row.resetsAt === null) ? null
      : Math.max(...blocked.map(row => row.resetsAt), ...(limitedUntil === null ? [] : [limitedUntil]));
    return result(weekBlocked ? 'week' : 'five-hour', until);
  }
  return limitedOr('ready');
}

function readinessRows(logins, usage, now) {
  return loginsOf(logins).map(login => ({ login, readiness: loginReadiness(login, own(usage, login.name), now) }));
}

// The row with the smallest non-null until; the first in order wins a tie.
function soonest(rows) {
  let best = null;
  for (const row of rows) if (row.readiness.until !== null && (best === null || row.readiness.until < best.readiness.until)) best = row;
  return best;
}

export function pickLogin({ logins, usage, now, skip = [] } = {}) {
  const skipped = new Set(list(skip));
  const rows = readinessRows(logins, usage, now).filter(row => !skipped.has(row.login.name));
  const found = rows.find(row => row.readiness.ready);
  if (found) return { login: found.login, readiness: found.readiness };
  const earliest = soonest(rows);
  return { login: null, allOut: true, earliest: earliest && { name: earliest.login.name, at: earliest.readiness.until },
    rows: rows.map(({ login, readiness }) => ({ name: login.name, ...readiness })) };
}

export function poolSummary({ logins, usage, now } = {}) {
  const rows = readinessRows(logins, usage, now);
  const ready = rows.filter(row => row.readiness.ready);
  const free = soonest(rows.filter(row => !row.readiness.ready));
  return { ready: ready.length, total: rows.length, next: ready[0]?.login.name ?? null,
    nextFree: free && { name: free.login.name, at: free.readiness.until } };
}

function duration(ms) {
  const hours = Math.floor(ms / HOUR_MS);
  if (hours < 1) { const minutes = Math.max(1, Math.floor(ms / MINUTE_MS)); return `${minutes} minute${minutes === 1 ? '' : 's'}`; }
  const days = Math.floor(hours / 24), rest = hours % 24;
  return [days && `${days} day${days === 1 ? '' : 's'}`, rest && `${rest} hour${rest === 1 ? '' : 's'}`].filter(Boolean).join(' ');
}

function clock(now, timeZone) {
  const options = { hour: '2-digit', minute: '2-digit', hourCycle: 'h23', timeZoneName: 'shortGeneric' };
  let format;
  try { format = new Intl.DateTimeFormat('en-US', { ...options, timeZone }); }
  catch { format = new Intl.DateTimeFormat('en-US', options); }
  const parts = Object.fromEntries(format.formatToParts(new Date(now)).map(part => [part.type, part.value]));
  return `${parts.hour}:${parts.minute} ${parts.timeZoneName}`;
}

const count = (n, word) => `${n} ${word}${n === 1 ? '' : 's'}`;
const validLeft = left => Number.isSafeInteger(left) && left >= 1;

export function resetNoticeText({ actor, name, now, until, left, timeZone } = {}) {
  const parts = [];
  if (finite(until) && until > now) parts.push(`its week would reset in ${duration(until - now)}`);
  if (validLeft(left)) parts.push(`${count(left - 1, 'reset')} left`);
  return `${actor} used a reset on ${name} at ${clock(now, timeZone)}${parts.length ? `: ${parts.join('; ')}` : ''}`;
}

export function usedTodayFromLog(rows, now) {
  const names = [];
  for (const row of list(rows)) {
    if (!object(row) || row.action !== 'reset' || typeof row.login !== 'string') continue;
    const at = finite(row.at) ? row.at : typeof row.at === 'string' ? Date.parse(row.at) : NaN;
    if (Number.isFinite(at) && at > now - DAY_MS && !names.includes(row.login)) names.push(row.login);
  }
  return names;
}

export function resetDecision({ logins, usage, now, workWaiting, resets, usedToday, timeZone } = {}) {
  const decision = (action, reason, login = null, until = null, text = '') => ({ action, login, until, reason, text });
  if (!Number.isSafeInteger(workWaiting) || workWaiting < 1) return decision('none', 'no-work');
  const rows = readinessRows(logins, usage, now);
  for (const reason of ['ready', 'stale', 'unknown']) {
    const row = rows.find(item => item.readiness.reason === reason);
    if (row) return decision('none', reason === 'ready' ? 'quota' : reason, row.login);
  }
  const back = soonest(rows.filter(row => ['week', 'five-hour', 'limited'].includes(row.readiness.reason)));
  const wait = reason => decision('wait', reason, back?.login ?? null, back?.readiness.until ?? null);
  const entry = row => own(resets, row.login.name);
  const used = new Set(list(usedToday));
  const fiveHourFree = row => {
    const usageRow = own(usage, row.login.name), fiveHour = windowOf(object(usageRow) ? usageRow.fiveHour : undefined);
    return fiveHour.absent || !fiveHour.malformed && fiveHour.used < stopLine(row.login.stop?.fiveHour);
  };
  const filters = [
    ['not-allowed', row => row.login.reset === 'ask' || row.login.reset === 'auto'],
    ['no-resets', row => validLeft(entry(row)?.left)],
    ['used-today', row => !used.has(row.login.name)],
    ['not-weekly', row => row.readiness.reason === 'week'],
    ['week-soon', row => row.readiness.until !== null && row.readiness.until - now > DAY_MS],
    ['five-hour-busy', fiveHourFree],
  ];
  let candidates = rows;
  for (const [reason, keep] of filters) {
    candidates = candidates.filter(keep);
    if (!candidates.length) return wait(reason);
  }
  if (back && back.readiness.until - now <= BACK_SOON_MS) return wait('back-soon');
  const expiry = row => finite(entry(row).expiresAt) ? entry(row).expiresAt : null;
  const expiring = candidates.filter(row => expiry(row) !== null && expiry(row) <= row.readiness.until);
  const pool = expiring.length ? expiring : candidates;
  // Array order is the person's order; a strict comparison keeps the first on a tie.
  const better = (a, b) => expiring.length && expiry(a) !== expiry(b) ? expiry(a) < expiry(b) : a.readiness.until > b.readiness.until;
  const chosen = pool.reduce((best, row) => better(row, best) ? row : best);
  const { login, readiness: { until } } = chosen, left = entry(chosen).left;
  if (login.reset === 'auto') return decision('reset', expiring.length ? 'expiring' : 'furthest', login, until,
    resetNoticeText({ actor: 'Autopilot', name: login.name, now, until, left, timeZone }));
  return decision('ask', expiring.length ? 'expiring' : 'furthest', login, until,
    `Reset ${login.name} now? Its week resets in ${duration(until - now)}; ${count(left, 'reset')} left; ${workWaiting === 1 ? '1 issue waits' : `${workWaiting} issues wait`}. Run: pdd accounts reset ${login.name}`);
}
