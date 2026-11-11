// Generated from prompts/cli/autopilot-pool.prompt.md (sha256: 9f76e10db9c11ec8d880f42dfac84611c1b0084e770ac63dbbfc9abb1cf39469).
import * as nativeFs from 'node:fs';
import { createHash, randomUUID } from 'node:crypto';
import { dirname, join, resolve } from 'node:path';

// The Autopilot side of the login pool (#3252): a login per agent step, the sorting of a step's end, the all-out pause
// and the status lines. It never refreshes, signs in, spends a reset or credits, or opens an auth.json.
const MIN = 60_000, DAY = 86_400_000, MAX_FUTURE = 32 * DAY, MAX_DATE = 8.64e15;
const LIMIT_FALLBACK = 30 * MIN, SIGN_IN_HOLD = 60 * MIN, STALE_COPY_HOLD = 10 * MIN, UNKNOWN_WAKE = 60 * MIN, PAST_WAKE = 10 * MIN;
const VARIABLES = { codex: 'CODEX_HOME', claude: 'CLAUDE_CONFIG_DIR' };
const NAMES = { codex: 'Codex', claude: 'Claude' };
const MODULES = { store: './accounts-store.mjs', usage: './accounts-usage.mjs', pick: './accounts-pick.mjs' };
const MESSAGES = { limit: 'usage limit', credits: 'out of credits', 'needs-sign-in': 'sign-in ended', 'stale-copy': '401 on the login copy', capacity: 'service busy' };
const RECORD = 'autopilot-pool.json';

const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const nonblank = value => typeof value === 'string' && value.trim() !== '';
const oneLine = (text, max = 200) => String(text ?? '').replace(/\s+/g, ' ').trim().slice(0, max);
const samePath = (a, b) => nonblank(a) && nonblank(b) && resolve(a) === resolve(b);
const iso = ms => new Date(ms).toISOString();
const pct = window => Number.isFinite(window?.usedPercent) ? `${Math.round(window.usedPercent)}%` : '?';
const plural = (n, word) => `${n} login${n === 1 ? '' : 's'}${word}`;
// The usage cache may come as the file object ({version, rows}) or as the rows map keyed by login name.
// A safe reason from a pool file error: no file text (a JSON parse error quotes the file), no token-like words.
function safeReason(error) {
  if (error instanceof SyntaxError) return 'the file does not parse';
  return oneLine(String(error?.message ?? 'unknown error').replace(/(["'`])[^"'`]{41,}\1/g, '$1…$1')
    .replace(/\b(?:eyJ[\w-]+\.[\w.-]+|sk-[\w-]{8,}|gh[pousr]_\w+|Bearer\s+\S+)/g, '[redacted]'), 160);
}
const usageRows = value => object(value) && value.version === 1 && object(value.rows) ? value.rows : object(value) ? value : {};

// A port that is not given loads its module. Only a module that is not installed means "no pool"; a broken one throws.
async function modules(ports) {
  const out = {}, load = ports.importModule ?? (path => import(path));
  for (const [key, path] of Object.entries(MODULES)) {
    if (ports[key]) { out[key] = ports[key]; continue; }
    try { out[key] = await load(path); }
    catch (error) {
      // Node names the missing file first ("Cannot find module '/x/src/accounts-store.mjs' imported from ...").
      const missing = /Cannot find (?:module|package) '([^']+)'/.exec(String(error?.message))?.[1] ?? '';
      if (error?.code === 'ERR_MODULE_NOT_FOUND' && (missing === path || missing.endsWith(`/${path.slice(2)}`))) return null;
      throw error;
    }
  }
  return out;
}
const modulePorts = ports => ports.modulePorts ?? {};
async function providerLogins(m, pool, provider) {
  const rows = await m.store.orderedLogins(pool);
  return (Array.isArray(rows) ? rows : []).filter(login => object(login) && login.provider === provider && nonblank(login.name));
}

// ---- Time words -----------------------------------------------------------------------------------------
function clockParts(ms, timeZone) {
  const format = zone => new Intl.DateTimeFormat('en-US', { timeZone: zone, hourCycle: 'h23', year: 'numeric', month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit', timeZoneName: 'short' });
  let parts;
  try { parts = format(timeZone).formatToParts(ms); } catch { parts = format(undefined).formatToParts(ms); }
  return Object.fromEntries(parts.filter(part => part.type !== 'literal').map(part => [part.type, part.value]));
}
function timeWords(ms, now, timeZone) {
  if (!Number.isFinite(ms)) return 'an unknown time';
  const at = clockParts(ms, timeZone), today = Number.isFinite(now) ? clockParts(now, timeZone) : null;
  const clock = `${String(Number(at.hour) % 24).padStart(2, '0')}:${at.minute} ${at.timeZoneName}`;
  return today && today.year === at.year && today.month === at.month && today.day === at.day ? clock : `${at.month} ${at.day} ${clock}`;
}
// The epoch ms of a wall-clock time in a time zone (the machine's zone when none is given), or null.
function zonedTime(year, month, day, hour, minute, timeZone) {
  try {
    const format = new Intl.DateTimeFormat('en-US', { timeZone, hourCycle: 'h23', year: 'numeric', month: 'numeric', day: 'numeric', hour: 'numeric', minute: 'numeric' });
    const offset = ms => {
      const p = Object.fromEntries(format.formatToParts(ms).filter(part => part.type !== 'literal').map(part => [part.type, Number(part.value)]));
      return Date.UTC(p.year, p.month - 1, p.day, p.hour % 24, p.minute) - Math.floor(ms / MIN) * MIN;
    };
    const wall = Date.UTC(year, month, day, hour, minute);
    const first = wall - offset(wall);
    return wall - offset(first);
  } catch { return null; }
}
function todayIn(now, timeZone) {
  try {
    const p = Object.fromEntries(new Intl.DateTimeFormat('en-US', { timeZone, year: 'numeric', month: 'numeric', day: 'numeric' }).formatToParts(now).filter(part => part.type !== 'literal').map(part => [part.type, Number(part.value)]));
    return { year: p.year, month: p.month - 1, day: p.day };
  } catch { return null; }
}

// ---- The pool record: this module's own machine file (last login, all-out pause, pool error) -------------
async function recordFile(m, env) { return join((await m.store.poolPaths(env)).stateDir, RECORD); }
function readRecord(fs, file) {
  try { const value = JSON.parse(fs.readFileSync(file, 'utf8')); if (object(value) && value.version === 1 && object(value.providers)) return value; }
  catch { /* A missing or broken record reads as empty. */ }
  return { version: 1, providers: {} };
}
// Read again, change one provider's entry and write atomically. False when the write failed.
function updateRecord(fs, file, provider, change) {
  const record = readRecord(fs, file), before = object(record.providers[provider]) ? record.providers[provider] : {};
  record.providers[provider] = change({ ...before });
  try {
    fs.mkdirSync(dirname(file), { recursive: true, mode: 0o700 });
    const temp = `${file}.${process.pid}.${randomUUID().slice(0, 8)}.tmp`;
    fs.writeFileSync(temp, `${JSON.stringify(record)}\n`, { mode: 0o600 });
    fs.renameSync(temp, file);
    return true;
  } catch { return false; }
}
// The pool stamp: the pool's order and logins, and the size and change time of each Codex login file (stat only).
function poolStamp(fs, pool, logins, provider) {
  const files = logins.map(login => {
    if (provider !== 'codex') return [login.name, null, null];
    try { const stat = fs.statSync(join(login.home, 'auth.json')); return [login.name, stat.size, stat.mtimeMs]; } catch { return [login.name, null, null]; }
  });
  return createHash('sha256').update(JSON.stringify({ order: pool?.order ?? [], logins: pool?.logins ?? [], files })).digest('hex');
}

// ---- Lines ---------------------------------------------------------------------------------------------
function readiness(m, login, row, now) {
  try { const value = m.pick.loginReadiness(login, row, now); return object(value) ? value : { ready: false, reason: 'unknown', until: null }; }
  catch { return { ready: false, reason: 'unknown', until: null }; }
}
function poolWords(m, logins, rows, now, timeZone) {
  let summary = null;
  try { summary = m.pick.poolSummary({ logins, usage: rows, now }); } catch { /* The counts below still show. */ }
  const unread = logins.filter(login => login.paused !== true && (!object(rows[login.name]) || readiness(m, login, rows[login.name], now).reason === 'stale')).length;
  const free = summary?.nextFree;
  const next = object(free) && nonblank(free.name) && Number.isFinite(free.at) ? ` Next free: ${free.name} at ${timeWords(free.at, now, timeZone)}.` : '';
  return `Pool: ${summary?.ready ?? 0} of ${summary?.total ?? logins.length} ready${unread ? ` (${unread} not read in the last 10 minutes)` : ''}.${next}`;
}
async function pinnedResult(m, provider, variable, env, ports) {
  const home = env[variable];
  let login = null;
  if (m) try { login = (await providerLogins(m, await m.store.readPool({ env }, modulePorts(ports)), provider)).find(row => samePath(row.home, home)) ?? null; }
  catch { /* Naming the pinned login is best effort. */ }
  const who = login ? `pinned to ${provider} ${login.name}: ` : 'pinned: ';
  return { pinned: true, reason: 'env', login, line: `Agent login: ${who}${variable}=${home} is set for this Autopilot; pdd does not rotate it.` };
}
const noPool = line => ({ pinned: true, reason: 'no-pool', login: null, line });
const pauseAlert = line => ({ kind: 'usage-limit', text: line, tried: 'Autopilot started no new agent step. Running steps go on.',
  need: 'Add a login (pdd accounts add NAME), wait for the reset, or resume a paused login (pdd accounts resume NAME).' });
const pauseView = pause => ({ reason: pause.reason, since: Number.isFinite(pause.since) ? pause.since : null, wakeAt: Number.isFinite(pause.wakeAt) ? pause.wakeAt : null,
  line: String(pause.line ?? ''), alert: null, earliest: object(pause.earliest) ? pause.earliest : null });
const LIMIT_REASONS = new Set(['week', 'five-hour', 'limited']), SIGN_IN_REASONS = new Set(['needs-sign-in', 'expired', 'no-login']);
function outWords(m, logins, rows, now) {
  const count = { limit: 0, signIn: 0, paused: 0, unreadable: 0 };
  for (const login of logins) {
    if (login.paused === true) { count.paused++; continue; }
    const reason = readiness(m, login, rows[login.name], now).reason;
    if (LIMIT_REASONS.has(reason)) count.limit++;
    else if (SIGN_IN_REASONS.has(reason)) count.signIn++;
    else if (reason === 'paused') count.paused++;
    else count.unreadable++;
  }
  return [[count.limit, 'at a limit'], [count.signIn, count.signIn === 1 ? 'needs a sign-in' : 'need a sign-in'], [count.paused, 'paused'],
    [count.unreadable, 'not readable']].filter(([n]) => n > 0).map(([n, words]) => `${n} ${words}`).join(', ');
}

// ---- A step's login -------------------------------------------------------------------------------------
export async function stepLogin({ provider, env = {}, now, command = provider, skip = [] } = {}, ports = {}) {
  const variable = VARIABLES[provider], name = NAMES[provider];
  if (!variable) return noPool(`Agent login: ${provider} is not in the login pool; the step uses its own environment.`);
  const m = await modules(ports);
  if (nonblank(env[variable])) return pinnedResult(m, provider, variable, env, ports);
  if (!m) return noPool('Agent login: this pdd has no login pool; the step uses its own environment.');
  const fs = ports.fs ?? nativeFs, timeZone = ports.timeZone, mp = modulePorts(ports), file = await recordFile(m, env);
  let pool;
  try { pool = await m.store.readPool({ env }, mp); }
  catch (error) {
    const line = `Paused: Autopilot cannot read the login pool file (${safeReason(error)}). Fix it, then the next tick goes on; no step starts until then.`;
    let fresh = false, since = now;
    const saved = updateRecord(fs, file, provider, entry => {
      fresh = !object(entry.error); if (!fresh && Number.isFinite(entry.error.since)) since = entry.error.since;
      return { ...entry, error: { since, line } };
    });
    return { pause: { reason: 'pool-error', since, wakeAt: null, line, earliest: null,
      alert: fresh && saved ? { ...pauseAlert(line), need: 'Fix the login pool file; pdd accounts list shows the problem.' } : null } };
  }
  const logins = await providerLogins(m, pool, provider);
  if (!logins.length) return noPool(`Agent login: no ${provider} login in the pool; the step uses its own environment.`);
  const saved = readRecord(fs, file).providers[provider] ?? {}, stamp = poolStamp(fs, pool, logins, provider);
  let rows = {};
  try { rows = { ...usageRows(await m.usage.loadUsage({ env }, mp)) }; } catch { /* No cache: every login is read. */ }
  // A waiting tick: only local files, no usage read.
  if (object(saved.pause) && saved.pause.reason === 'all-out' && !shouldWake(saved.pause, { now, stamp, usage: rows }).wake) return { pause: pauseView(saved.pause) };
  // Read the logins in order, one at a time, up to the first ready one; a login with no row or a stale one is read.
  const skipped = new Set(Array.isArray(skip) ? skip : []);
  let read = false;
  for (const login of logins) {
    if (skipped.has(login.name) || login.paused === true) continue;
    let state = readiness(m, login, rows[login.name], now);
    if (!object(rows[login.name]) || state.reason === 'stale') {
      try { const row = await m.usage.readLoginUsage(login, { env, now, command }, mp); if (object(row)) { rows[login.name] = row; read = true; } }
      catch { /* A failed read keeps the old row. */ }
      state = readiness(m, login, rows[login.name], now);
    }
    if (state.ready) break;
  }
  if (read) try { await m.usage.saveUsage({ env }, rows, mp); } catch { /* The next pick reads again. */ }
  let picked = m.pick.pickLogin({ logins, usage: rows, now, skip: [...skipped] });
  // skip is a preference of one step: when only skipped logins are ready, the step takes one; it never makes a pause.
  if (!object(picked?.login) && skipped.size) picked = m.pick.pickLogin({ logins, usage: rows, now, skip: [] });
  if (object(picked?.login)) {
    const login = picked.login, row = rows[login.name];
    let ended = false;
    updateRecord(fs, file, provider, entry => {
      ended = object(entry.pause) || object(entry.error);
      const next = { ...entry, last: { name: login.name, at: now } }; delete next.pause; delete next.error; return next;
    });
    return { login, env: { [variable]: login.home },
      line: `Agent login: ${provider} ${login.name} (week ${pct(row?.week)}, 5h ${pct(row?.fiveHour)}). ${poolWords(m, logins, rows, now, timeZone)}`,
      logLine: `pdd-account: ${login.name} (local pool)`, recovered: ended ? `Autopilot has a ${name} login again: ${login.name}. The pause ended.` : null };
  }
  // All out: wake at the earliest reset, or check again in 60 minutes when no reset is known.
  const first = picked?.earliest, earliest = object(first) && nonblank(first.name) && Number.isFinite(first.at) ? { name: first.name, at: first.at } : null;
  // A reset time that is already past (the login is still out) is checked again after one tick, not on every tick.
  const wakeAt = !earliest ? now + UNKNOWN_WAKE : earliest.at > now ? earliest.at : now + PAST_WAKE;
  const resets = logins.filter(login => nonblank(login.reset) && login.reset !== 'never').map(login => login.name);
  const line = `Paused: no ${name} login has quota now (${outWords(m, logins, rows, now)}). `
    + (earliest ? `Earliest reset: ${earliest.name} at ${timeWords(earliest.at, now, timeZone)}.` : `Earliest reset: unknown; Autopilot checks again at ${timeWords(wakeAt, now, timeZone)}.`)
    + ` Add a login (pdd accounts add NAME) and the pause ends at the next tick. Resets: ${resets.length ? `on for ${resets.join(', ')} (setting ask or auto; the reset rule decides)` : 'off'}.`;
  let fresh = false, since = now;
  const written = updateRecord(fs, file, provider, entry => {
    fresh = !(object(entry.pause) && entry.pause.reason === 'all-out');
    if (!fresh && Number.isFinite(entry.pause.since)) since = entry.pause.since;
    const next = { ...entry, pause: { reason: 'all-out', since, wakeAt, checkedAt: now, stamp, line, earliest } }; delete next.error; return next;
  });
  return { pause: { reason: 'all-out', since, wakeAt, line, alert: fresh && written ? pauseAlert(line) : null, earliest } };
}

// ---- Waking a pause (pure) ------------------------------------------------------------------------------
export function shouldWake(pause, { now, stamp, usage } = {}) {
  if (!object(pause)) return { wake: true, reason: 'no-pause' };
  if (Number.isFinite(pause.wakeAt) && Number.isFinite(now) && now >= pause.wakeAt) return { wake: true, reason: 'time' };
  if (stamp !== pause.stamp) return { wake: true, reason: 'pool' };
  if (Number.isFinite(pause.checkedAt) && Object.values(usageRows(usage)).some(row => object(row) && Number.isFinite(row.readAt) && row.readAt > pause.checkedAt))
    return { wake: true, reason: 'read' };
  return { wake: false, reason: 'waiting' };
}

// ---- Sorting the end of a step (pure) -------------------------------------------------------------------
const KINDS = [
  ['limit', /usage_limit_(?:reached|exceeded)|\bhit your (?:(?:weekly|daily|monthly|5-hour|five-hour|session) )?(?:usage )?limit\b|\busage limit (?:reached|exceeded|has been reached)\b|\b(?:weekly|5-hour|five-hour) limit reached\b|\bclaude ai usage limit reached\b/i],
  ['credits', /credits_depleted|\bout of credits\b|\bcredit balance is too low\b|\binsufficient[_ ](?:credits?|quota|funds)\b|\bexceeded your current quota\b/i],
  ['needs-sign-in', /refresh_token_(?:expired|reused|invalidated|revoked)|\brefresh token (?:has expired|was already used|was revoked|is invalid)\b|\b(?:sign|log) ?in again\b|\bplease (?:run \/login|log ?in|sign ?in)\b|\bnot (?:logged|signed) in\b|\b(?:login|authentication) required\b|authentication_failed|\binvalid[_ ]api[_ ]key\b|\boauth token has expired\b/i],
  ['stale-copy', /\b(?:status|http|error|code)\W{0,3}401\b|\b401 unauthori[sz]ed\b|\bunauthori[sz]ed\b|\baccess token (?:expired|is invalid|was rejected)\b/i],
  ['capacity', /\b(?:at|over) capacity\b|\boverloaded\b|\b(?:status|http|error|code)\W{0,3}(?:429|5\d\d)\b|\b(?:429|5\d\d) (?:too many|internal|bad gateway|service|gateway|overloaded)|\btoo many requests\b|\binternal server error\b|\bbad gateway\b|\bservice unavailable\b|\bgateway time-?out\b|\bserver_error\b|\bstream disconnected\b|\bconnection (?:reset|refused)\b/i],
];
const TEST_DIAGNOSTIC = /\b(?:tests?|assert(?:ion)?s?|expected|fixtures?|specs?)\b/i;
const text = value => typeof value === 'string' && value.trim() ? value : null;
function kindOf(message) {
  for (const [kind, pattern] of KINDS) if (pattern.test(message)) return kind;
  return /\brate[ _-]?limit/i.test(message) && !/usage/i.test(message) ? 'capacity' : null;
}
function eventMessage(event) {
  if (event.type === 'error') return text(event.message) ?? text(event.error?.message) ?? text(event.error);
  if (event.type === 'turn.failed') return text(event.error?.message) ?? text(event.message) ?? text(event.error);
  if (event.type === 'result' && event.is_error === true) return text(event.result) ?? text(event.error?.message) ?? text(event.error);
  return null;
}
function eventHint(event) {
  const info = event.codex_error_info ?? event.error?.codex_error_info;
  if (event.error === 'rate_limit' || event.apiError === 'usage_limit_reached' || info === 'usage_limit_exceeded') return 'limit';
  return event.error === 'authentication_failed' ? 'needs-sign-in' : null;
}
const MONTHS = ['jan', 'feb', 'mar', 'apr', 'may', 'jun', 'jul', 'aug', 'sep', 'oct', 'nov', 'dec'];
const CODEX_AT = /\btry again at (?:([a-z]{3})[a-z]* (\d{1,2})(?:st|nd|rd|th)?,? (\d{4}),? )?(\d{1,2}):(\d{2}) ?([ap])\.?m\b/i;
const CLAUDE_AT = /\bresets (?:([a-z]{3})[a-z]* (\d{1,2})(?:st|nd|rd|th)?,? (?:at )?)?(\d{1,2})(?::(\d{2}))? ?([ap])m\b \(([\w+\-/]{1,40})\)/i;
const clock = (hour, half) => Number(hour) % 12 + (half.toLowerCase() === 'p' ? 12 : 0);
function untilOf({ message, json }, now, timeZone) {
  const both = `${message}\n${json ?? ''}`, valid = ms => Number.isFinite(ms) && ms > 0 && ms <= MAX_DATE && (!Number.isFinite(now) || ms <= now + MAX_FUTURE) ? ms : null;
  const epoch = digits => { const n = Number(digits); return n < 1e12 ? n * 1000 : n; };
  let match = /resets_?at\\?"?\s*[:=]\s*"?(\d{9,13})\b/i.exec(both);
  if (match) return valid(epoch(match[1]));
  match = /resets_in_seconds\\?"?\s*[:=]\s*"?(\d{1,9})\b/i.exec(both);
  if (match) return Number.isFinite(now) ? valid(now + Number(match[1]) * 1000) : null;
  match = /usage limit reached\|(\d{9,13})\b/i.exec(both);
  if (match) return valid(epoch(match[1]));
  match = CODEX_AT.exec(message);
  if (match) {
    const [, month, day, year, hour, minute, half] = match, h = Number(hour), mi = Number(minute);
    if (h < 1 || h > 12 || mi > 59) return null;
    if (month) { const index = MONTHS.indexOf(month.toLowerCase()); return index < 0 ? null : valid(zonedTime(Number(year), index, Number(day), clock(hour, half), mi, timeZone)); }
    const today = Number.isFinite(now) ? todayIn(now, timeZone) : null;
    return today ? valid(zonedTime(today.year, today.month, today.day, clock(hour, half), mi, timeZone)) : null;
  }
  match = CLAUDE_AT.exec(message);
  if (match) {
    const [, month, day, hour, minute = '0', half, zone] = match, h = Number(hour), mi = Number(minute);
    if (h < 1 || h > 12 || mi > 59 || !Number.isFinite(now)) return null;
    const today = todayIn(now, zone);
    if (!today) return null;
    // Claude names the next such time: a time of day before now is tomorrow.
    if (!month) {
      const at = zonedTime(today.year, today.month, today.day, clock(hour, half), mi, zone);
      return valid(at !== null && at < now ? zonedTime(today.year, today.month, today.day + 1, clock(hour, half), mi, zone) : at);
    }
    const index = MONTHS.indexOf(month.toLowerCase());
    if (index < 0) return null;
    const at = year => zonedTime(year, index, Number(day), clock(hour, half), mi, zone);
    const thisYear = at(today.year);
    return valid(thisYear !== null && thisYear < now - MAX_FUTURE ? at(today.year + 1) : thisYear);
  }
  return null;
}
export function classifyAgentEnd({ provider, output, exitCode, now, timeZone } = {}) {
  const all = String(output ?? ''), tail = all.length > 262144 ? all.slice(-262144) : all;
  const lines = tail.split(/\r?\n/).slice(-200), plainLines = [];
  let event = null, plain = 0;
  for (let i = lines.length - 1; i >= 0 && !event; i--) {
    const line = lines[i].trim();
    if (!line || line.startsWith('pdd-account:')) continue;
    if (line.startsWith('{')) {
      let row;
      try { row = JSON.parse(line); } catch { continue; }
      if (!object(row)) continue;
      // A success is newer than every error before it: the step did not end on them.
      if (row.type === 'turn.completed' || row.type === 'result' && row.is_error !== true) return { kind: 'other', until: null, message: null };
      const hint = eventHint(row), message = eventMessage(row);
      if (hint || message) event = { message: message ?? '', hint, json: line };
      continue;
    }
    // Only the agent's last plain lines (its own stderr), and never a line that reads like a test diagnostic.
    if (plain++ < 5 && !TEST_DIAGNOSTIC.test(line)) plainLines.push({ message: line, hint: null, json: null });
  }
  // The newest error event decides; with no error event, the newest plain line with a kind.
  const found = event ?? plainLines.find(row => kindOf(row.message));
  const kind = found ? found.hint ?? kindOf(found.message) : null;
  return kind ? { kind, until: kind === 'limit' || kind === 'credits' ? untilOf(found, now, timeZone) : null, message: MESSAGES[kind] }
    : { kind: 'other', until: null, message: null };
}

// ---- After a step ---------------------------------------------------------------------------------------
const ACCOUNT_KINDS = new Set(['limit', 'credits', 'needs-sign-in', 'stale-copy']);
export async function afterStep({ login, end, env = {}, now, command } = {}, ports = {}) {
  const kind = end?.kind, row = object(login) ? login : null, name = nonblank(row?.name) ? row.name : nonblank(login) ? login : null;
  if (kind === 'capacity') return { strike: false, line: `pdd-account: ${name ?? 'the pinned login'}: the AI service is busy (service busy); no login change.`, mark: null, alert: null };
  if (!ACCOUNT_KINDS.has(kind)) return { strike: true, line: null, mark: null, alert: null };
  if (!name) return { strike: false, line: `pdd-account: the pinned login ended with: ${MESSAGES[kind]}. pdd does not rotate a pinned login.`, mark: null, alert: null };
  const m = await modules(ports), timeZone = ports.timeZone, mp = modulePorts(ports);
  if (!m) return { strike: false, line: `pdd-account: ${name} ended with: ${MESSAGES[kind]} (the pool could not save this: this pdd has no login pool).`, mark: null, alert: null };
  let until = null, alert = null, failure = null;
  if (kind === 'limit' || kind === 'credits') {
    if (Number.isFinite(end.until) && end.until > now) until = end.until;
    else if (row) try {
      const fresh = await m.usage.readLoginUsage(row, { env, now, command }, mp);
      if (object(fresh)) {
        const state = readiness(m, row, fresh, now);
        if (!state.ready && Number.isFinite(state.until) && state.until > now) until = state.until;
        try { await m.usage.saveUsage({ env }, { ...usageRows(await m.usage.loadUsage({ env }, mp)), [name]: fresh }, mp); }
        catch (error) { failure = error; }
      }
    } catch { /* A failed read: the fallback below. */ }
    until ??= now + LIMIT_FALLBACK;
  } else if (kind === 'needs-sign-in') {
    until = now + SIGN_IN_HOLD;
    let before = null;
    try { before = usageRows(await m.usage.loadUsage({ env }, mp))[name]; } catch { /* No cache: a new event. */ }
    if (!(before?.limitReason === 'needs-sign-in' && Number.isFinite(before.limitedUntil) && before.limitedUntil > now))
      alert = { kind: 'usage-limit', text: `${NAMES[row?.provider] ?? 'Pool'} login ${name} needs a new sign-in. Autopilot skips it. Run: pdd accounts add ${name}`,
        tried: 'Autopilot uses the other logins of the pool.', need: 'Sign in to this login again.' };
  } else until = now + STALE_COPY_HOLD;
  let mark = null;
  try { await m.usage.markLimited({ env }, name, until, kind, mp); mark = { name, until, reason: kind }; } catch (error) { failure = error; }
  try { await m.store.appendLog({ env }, { at: iso(now), action: kind === 'needs-sign-in' ? 'needs-sign-in' : 'limited', login: name, detail: `${kind} until ${iso(until)}` }, mp); }
  catch (error) { failure ??= error; }
  const line = kind === 'needs-sign-in' ? `pdd-account: ${name} needs a new sign-in (${MESSAGES[kind]}). The next step takes the next login.`
    : kind === 'stale-copy' ? `pdd-account: ${name} got 401 on its login copy; it waits 10 minutes. The next step takes the next login.`
      : `pdd-account: ${name} limited until ${timeWords(until, now, timeZone)} (${MESSAGES[kind]}). The next step takes the next login.`;
  // An alert needs its saved mark: without it the next step would alert again.
  return { strike: false, line: failure ? `${line} (the pool could not save this: ${oneLine(failure.message, 120)})` : line, mark, alert: mark ? alert : null };
}

// ---- The start binding (#3230) --------------------------------------------------------------------------
export async function startBinding({ provider, env = {}, saved = null, pool = false } = {}, ports = {}) {
  const variable = VARIABLES[provider], savedPool = saved?.agentPool === provider, savedHome = nonblank(saved?.home) ? saved.home : null;
  if (!variable) return { agentPool: null, home: savedHome, line: `Agent login: ${provider} is not in the login pool.` };
  let count = 0, problem = null;
  const m = await modules(ports);
  if (m) try { count = (await providerLogins(m, await m.store.readPool({ env }, modulePorts(ports)), provider)).length; } catch (error) { problem = safeReason(error); }
  const was = savedPool ? `the ${provider} pool` : savedHome ? `${variable}=${savedHome}` : null;
  const poolLine = extra => `Agent login: the ${provider} pool (${plural(count, '')}); each step takes the first login with quota.${extra}`;
  const hint = count ? " Run pdd autopilot start --pool to rotate the pool's logins." : '';
  if (nonblank(env[variable])) {
    const home = env[variable], changed = savedPool || savedHome !== null && !samePath(savedHome, home);
    return { agentPool: null, home, line: `Agent login: pinned to ${variable}=${home}.${changed ? ` It was ${was}.` : ''}` };
  }
  if (pool && count) return { agentPool: provider, home: null, line: poolLine(savedHome !== null && !savedPool ? ` It was ${variable}=${savedHome}.` : '') };
  if (pool) return { agentPool: savedPool ? provider : null, home: savedPool ? null : savedHome,
    line: `Agent login: the ${provider} pool has no login (${problem ? `the pool file cannot be read: ${problem}` : 'pdd accounts add NAME'}); kept: ${was ?? 'no saved login'}.` };
  if (savedPool) return { agentPool: provider, home: null, line: `Agent login: the ${provider} pool (${plural(count, ', saved')}).` };
  if (savedHome !== null) return { agentPool: null, home: savedHome, line: `Agent login: pinned to ${variable}=${savedHome} (saved).${hint}` };
  if (saved === null && count) return { agentPool: provider, home: null, line: poolLine('') };
  return { agentPool: null, home: null, line: `Agent login: no login pool; steps use ${NAMES[provider]}'s own default folder.${hint}` };
}

// ---- Status lines (local files only) --------------------------------------------------------------------
export async function poolStatusLines({ provider, env = {}, now } = {}, ports = {}) {
  const variable = VARIABLES[provider];
  if (!variable) return [];
  const m = await modules(ports);
  if (nonblank(env[variable])) return [(await pinnedResult(m, provider, variable, env, ports)).line];
  if (!m) return [];
  const fs = ports.fs ?? nativeFs, timeZone = ports.timeZone, mp = modulePorts(ports);
  let pool;
  try { pool = await m.store.readPool({ env }, mp); } catch (error) { return [`Agent login: the login pool file cannot be read (${safeReason(error)}).`]; }
  const logins = await providerLogins(m, pool, provider);
  if (!logins.length) return [];
  const entry = readRecord(fs, await recordFile(m, env)).providers[provider] ?? {};
  let rows = {};
  try { rows = usageRows(await m.usage.loadUsage({ env }, mp)); } catch { /* No cache: no percentages. */ }
  const lines = [];
  if (object(entry.pause) && entry.pause.reason === 'all-out' && nonblank(entry.pause.line)) lines.push(entry.pause.line);
  else {
    const last = object(entry.last) && nonblank(entry.last.name) && Number.isFinite(entry.last.at) ? entry.last : null, row = last ? rows[last.name] : null;
    lines.push(`${last ? `Agent login: ${provider} ${last.name} (week ${pct(row?.week)}, 5h ${pct(row?.fiveHour)}) since ${timeWords(last.at, now, timeZone)}.` : `Agent login: ${provider} pool; no step used it yet.`} ${poolWords(m, logins, rows, now, timeZone)}`);
  }
  for (const login of logins) {
    const row = rows[login.name];
    if (readiness(m, login, row, now).reason === 'needs-sign-in' || row?.limitReason === 'needs-sign-in' && Number.isFinite(row.limitedUntil) && row.limitedUntil > now)
      lines.push(`${login.name} needs a sign-in: run pdd accounts add ${login.name}.`);
  }
  return lines;
}
