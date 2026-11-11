import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, rmSync, statSync, writeFileSync, mkdirSync, utimesSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { stepLogin, classifyAgentEnd, afterStep, startBinding, poolStatusLines, shouldWake } from '../src/autopilot-pool.mjs';

const MIN = 60_000, NOW = Date.UTC(2026, 10, 11, 14, 0);
// A fake token that must never show in a line, a log row or the pool record.
const SECRET = 'eyJfake.synthetic-access-token.never-print';

// Fakes of the store, usage and pick ports (DESIGN section 5 shapes). The pick rules here are a small stand-in.
function world(t, { logins = [], rows = {}, reads = {} } = {}) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-autopilot-pool-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const homes = Object.fromEntries(logins.map(login => [login.name, join(root, 'homes', login.name)]));
  for (const [name, home] of Object.entries(homes)) { mkdirSync(home, { recursive: true }); writeFileSync(join(home, 'auth.json'), JSON.stringify({ tokens: { access_token: SECRET } })); void name; }
  const pool = { version: 1, order: logins.map(login => login.name), logins: logins.map(login => ({ provider: 'codex', reset: 'never', stop: { week: 97, fiveHour: 97 }, paused: false, home: homes[login.name], ...login })), server: null };
  const cache = { ...rows }, calls = { reads: [], marks: [], logs: [], saves: 0, readPool: 0 };
  let poolError = null;
  const store = {
    poolPaths: () => ({ stateDir: join(root, 'state') }),
    readPool: () => { calls.readPool++; if (poolError) throw poolError; return structuredClone(pool); },
    orderedLogins: value => value.logins.map((login, index) => ({ ...login, position: index + 1 })),
    appendLog: (_input, row) => { calls.logs.push(row); },
  };
  const usage = {
    loadUsage: () => ({ version: 1, rows: structuredClone(cache) }),
    saveUsage: (_input, next) => { calls.saves++; for (const key of Object.keys(cache)) delete cache[key]; Object.assign(cache, structuredClone(next)); },
    readLoginUsage: (login, { now }) => { calls.reads.push(login.name); const row = reads[login.name]; return row ? { ...row, readAt: now } : { state: 'unknown', note: 'read failed', readAt: now }; },
    markLimited: (_input, name, until, reason) => { calls.marks.push({ name, until, reason }); cache[name] = { ...cache[name], limitedUntil: until, limitReason: reason }; },
  };
  const loginReadiness = (login, row, now) => {
    if (login.paused) return { ready: false, reason: 'paused', until: null };
    if (!row) return { ready: false, reason: 'stale', until: null };
    if (Number.isFinite(row.limitedUntil) && row.limitedUntil > now) return { ready: false, reason: row.limitReason === 'needs-sign-in' ? 'needs-sign-in' : 'limited', until: row.limitedUntil };
    if (now - row.readAt > 10 * MIN) return { ready: false, reason: 'stale', until: null };
    if (row.state === 'needs-sign-in') return { ready: false, reason: 'needs-sign-in', until: null };
    if (row.state !== 'ok') return { ready: false, reason: 'unknown', until: null };
    if (row.week?.usedPercent >= login.stop.week) return { ready: false, reason: 'week', until: row.week.resetsAt };
    if (row.fiveHour?.usedPercent >= login.stop.fiveHour) return { ready: false, reason: 'five-hour', until: row.fiveHour.resetsAt };
    return { ready: true, reason: 'ready', until: null };
  };
  const pick = {
    loginReadiness,
    pickLogin: ({ logins: list, usage: map, now, skip = [] }) => {
      const states = list.map(login => ({ login, readiness: loginReadiness(login, map[login.name], now) }));
      const found = states.find(row => row.readiness.ready && !skip.includes(row.login.name));
      if (found) return found;
      const timed = states.filter(row => Number.isFinite(row.readiness.until)).sort((a, b) => a.readiness.until - b.readiness.until)[0];
      return { login: null, allOut: true, earliest: timed ? { name: timed.login.name, at: timed.readiness.until } : null, rows: states };
    },
    poolSummary: ({ logins: list, usage: map, now }) => {
      const states = list.map(login => ({ login, readiness: loginReadiness(login, map[login.name], now) }));
      const timed = states.filter(row => !row.readiness.ready && Number.isFinite(row.readiness.until)).sort((a, b) => a.readiness.until - b.readiness.until)[0];
      return { ready: states.filter(row => row.readiness.ready).length, total: list.length, next: null, nextFree: timed ? { name: timed.login.name, at: timed.readiness.until } : null };
    },
  };
  const ports = { store, usage, pick, timeZone: 'UTC' };
  const recordFile = join(root, 'state', 'autopilot-pool.json');
  return { root, homes, pool, cache, calls, ports, recordFile, failPool: error => { poolError = error; }, addLogin: login => { const home = join(root, 'homes', login.name); mkdirSync(home, { recursive: true }); pool.logins.push({ provider: 'codex', reset: 'never', stop: { week: 97, fiveHour: 97 }, paused: false, home, ...login }); pool.order.push(login.name); return home; } };
}
const ok = (week, fiveHour, extra = {}) => ({ state: 'ok', plan: 'team', week: { usedPercent: week, resetsAt: NOW + 3 * 24 * 60 * MIN }, fiveHour: { usedPercent: fiveHour, resetsAt: NOW + 41 * MIN }, readAt: NOW - MIN, limitedUntil: null, limitReason: null, ...extra });
const noSecret = (value, label) => assert.equal(JSON.stringify(value).includes(SECRET) || JSON.stringify(value).includes('synthetic-access-token'), false, `${label} shows no token`);

test('P3 two logins, the first at its limit: the next step gets the second login, with no sign-in', async t => {
  const w = world(t, { logins: [{ name: 'cx1' }, { name: 'cx2' }], rows: { cx1: ok(98, 10), cx2: ok(63, 42) } });
  const step = await stepLogin({ provider: 'codex', env: { HOME: w.root, PATH: '/usr/bin' }, now: NOW }, w.ports);
  assert.equal(step.login.name, 'cx2');
  assert.deepEqual(step.env, { CODEX_HOME: w.homes.cx2 });
  assert.equal(step.line, 'Agent login: codex cx2 (week 63%, 5h 42%). Pool: 1 of 2 ready. Next free: cx1 at Nov 14 14:00 UTC.');
  assert.equal(step.logLine, 'pdd-account: cx2 (local pool)');
  assert.equal(step.recovered, null);
  assert.deepEqual(w.calls.reads, [], 'fresh rows need no usage read; nothing signs in or refreshes');
  assert.deepEqual(w.calls.marks, []);
  noSecret(step, 'the step result');
  const record = JSON.parse(readFileSync(w.recordFile, 'utf8'));
  assert.deepEqual(record, { version: 1, providers: { codex: { last: { name: 'cx2', at: NOW } } } });
  assert.equal(statSync(w.recordFile).mode & 0o777, 0o600);
  assert.equal(statSync(join(w.root, 'state')).mode & 0o777, 0o700);
});

test('P3 a pick reads stale logins in order and stops at the first ready one', async t => {
  const stale = { ...ok(10, 10), readAt: NOW - 30 * MIN };
  const w = world(t, { logins: [{ name: 'cx1' }, { name: 'cx2', paused: true }, { name: 'cx3' }, { name: 'cx4' }, { name: 'cx5' }],
    rows: { cx1: stale, cx3: stale, cx5: stale }, reads: { cx1: ok(100, 5), cx3: ok(20, 30), cx4: ok(1, 1), cx5: ok(1, 1) } });
  const step = await stepLogin({ provider: 'codex', env: {}, now: NOW }, w.ports);
  assert.equal(step.login.name, 'cx3');
  assert.deepEqual(w.calls.reads, ['cx1', 'cx3'], 'a paused login is never read; nothing after the first ready login is read');
  assert.equal(w.calls.saves, 1, 'the cache is saved once');
  assert.equal(w.cache.cx3.week.usedPercent, 20);
  assert.match(step.line, /^Agent login: codex cx3 \(week 20%, 5h 30%\)\. Pool: 1 of 5 ready \(2 not read in the last 10 minutes\)\./);
});

test('P3 a limit end: no strike, the login is marked limited, one log line names it', async t => {
  const w = world(t, { logins: [{ name: 'cx1' }, { name: 'cx2' }], rows: { cx1: ok(50, 50), cx2: ok(10, 10) } });
  const first = await stepLogin({ provider: 'codex', env: {}, now: NOW }, w.ports);
  assert.equal(first.login.name, 'cx1');
  // The end of a `codex exec --json` job log: tool output first (it never counts), then the agent's own failure.
  const log = [
    first.logLine,
    JSON.stringify({ type: 'thread.started', thread_id: 't1' }),
    JSON.stringify({ type: 'item.completed', item: { type: 'command_execution', aggregated_output: 'fixture: Claude AI usage limit reached|1700000000' } }),
    JSON.stringify({ type: 'error', message: `unexpected status 429 Too Many Requests: {"error":{"type":"usage_limit_reached","resets_at":${(NOW + 161 * MIN) / 1000},"token":"${SECRET}"}}` }),
    JSON.stringify({ type: 'turn.failed', error: { message: "You've hit your usage limit. Upgrade to Pro or try again at 4:41 PM." } }),
  ].join('\n');
  const end = classifyAgentEnd({ provider: 'codex', output: log, exitCode: 1, now: NOW, timeZone: 'UTC' });
  assert.deepEqual(end, { kind: 'limit', until: Date.UTC(2026, 10, 11, 16, 41), message: 'usage limit' }, 'the newest error decides; its reset words give the time');
  const after = await afterStep({ login: first.login, end, env: {}, now: NOW }, w.ports);
  assert.equal(after.strike, false, 'a limit end is never a strike of the issue (#3229)');
  assert.deepEqual(after.mark, { name: 'cx1', until: Date.UTC(2026, 10, 11, 16, 41), reason: 'limit' });
  assert.deepEqual(w.calls.marks, [{ name: 'cx1', until: Date.UTC(2026, 10, 11, 16, 41), reason: 'limit' }]);
  assert.deepEqual(w.calls.logs, [{ at: new Date(NOW).toISOString(), action: 'limited', login: 'cx1', detail: 'limit until 2026-11-11T16:41:00.000Z' }]);
  assert.equal(after.line, 'pdd-account: cx1 limited until 16:41 UTC (usage limit). The next step takes the next login.');
  assert.equal(after.alert, null);
  noSecret([end, after, w.calls.logs], 'the end, the after-step result and the log');
  // The next step starts on the next login.
  const next = await stepLogin({ provider: 'codex', env: {}, now: NOW + MIN }, w.ports);
  assert.equal(next.login.name, 'cx2');
});

test('P3 a limit end with no reset time reads the login once; a failed read waits 30 minutes', async t => {
  const w = world(t, { logins: [{ name: 'cx1' }], rows: { cx1: ok(50, 50) }, reads: { cx1: ok(40, 100) } });
  const login = { ...w.pool.logins[0] };
  const read = await afterStep({ login, end: { kind: 'limit', until: null }, env: {}, now: NOW }, w.ports);
  assert.deepEqual(w.calls.reads, ['cx1']);
  assert.equal(read.mark.until, NOW + 41 * MIN, 'the 5-hour window resets in 41 minutes');
  const v = world(t, { logins: [{ name: 'cx9' }], rows: {} });
  const fallback = await afterStep({ login: { ...v.pool.logins[0] }, end: { kind: 'credits', until: null }, env: {}, now: NOW }, v.ports);
  assert.deepEqual(fallback.mark, { name: 'cx9', until: NOW + 30 * MIN, reason: 'credits' });
  assert.equal(fallback.line, 'pdd-account: cx9 limited until 14:30 UTC (out of credits). The next step takes the next login.');
});

test('P3 all out: one pause with its wake time and one alert; a waiting tick reads nothing', async t => {
  const cx2 = ok(20, 100, { fiveHour: { usedPercent: 100, resetsAt: NOW + 160 * MIN } });
  const w = world(t, { logins: [{ name: 'cx1' }, { name: 'cx2' }, { name: 'cx3', paused: true }], rows: { cx1: ok(100, 10), cx2 }, reads: { cx1: ok(100, 10), cx2 } });
  const first = await stepLogin({ provider: 'codex', env: {}, now: NOW }, w.ports);
  assert.equal(first.login, undefined);
  assert.equal(first.pause.reason, 'all-out');
  assert.equal(first.pause.wakeAt, NOW + 160 * MIN, 'wake at the earliest reset');
  assert.deepEqual(first.pause.earliest, { name: 'cx2', at: NOW + 160 * MIN });
  assert.equal(first.pause.line, 'Paused: no Codex login has quota now (2 at a limit, 1 paused). Earliest reset: cx2 at 16:40 UTC. Add a login (pdd accounts add NAME) and the pause ends at the next tick. Resets: off.');
  assert.deepEqual(first.pause.alert, { kind: 'usage-limit', text: first.pause.line, tried: 'Autopilot started no new agent step. Running steps go on.',
    need: 'Add a login (pdd accounts add NAME), wait for the reset, or resume a paused login (pdd accounts resume NAME).' });
  const readsBefore = w.calls.reads.length;
  const second = await stepLogin({ provider: 'codex', env: {}, now: NOW + 10 * MIN }, w.ports);
  assert.equal(second.pause.alert, null, 'one alert per all-out event, not one per tick');
  assert.equal(second.pause.since, NOW);
  assert.equal(second.pause.line, first.pause.line);
  assert.equal(w.calls.reads.length, readsBefore, 'a waiting tick reads no usage');
  // At the wake time the pick runs again; still out, so the same event goes on with no new alert.
  const third = await stepLogin({ provider: 'codex', env: {}, now: NOW + 161 * MIN }, w.ports);
  assert.ok(w.calls.reads.length > readsBefore, 'a wake reads the stale logins');
  assert.equal(third.pause.alert, null);
  assert.equal(third.pause.since, NOW);
  assert.equal(third.pause.wakeAt, NOW + 171 * MIN, 'a past reset is checked again after one tick');
  const status = await poolStatusLines({ provider: 'codex', env: {}, now: NOW + 162 * MIN }, w.ports);
  assert.deepEqual(status, [third.pause.line]);
});

test('P3 a new login during the pause: the next tick wakes and takes it', async t => {
  const w = world(t, { logins: [{ name: 'cx1' }], rows: { cx1: ok(100, 10) } });
  const paused = await stepLogin({ provider: 'codex', env: {}, now: NOW }, w.ports);
  assert.equal(paused.pause.reason, 'all-out');
  const home = w.addLogin({ name: 'cx7' });
  w.cache.cx7 = ok(5, 5, { readAt: NOW + 4 * MIN });
  const woke = await stepLogin({ provider: 'codex', env: {}, now: NOW + 5 * MIN }, w.ports);
  assert.equal(woke.login.name, 'cx7');
  assert.deepEqual(woke.env, { CODEX_HOME: home });
  assert.equal(woke.recovered, 'Autopilot has a Codex login again: cx7. The pause ended.');
  assert.equal(JSON.parse(readFileSync(w.recordFile, 'utf8')).providers.codex.pause, undefined, 'the pause record is gone');
});

test('P3 a new sign-in or a fresh usage read wakes the pause; nothing else does', async t => {
  const w = world(t, { logins: [{ name: 'cx1' }], rows: { cx1: ok(100, 10) } });
  await stepLogin({ provider: 'codex', env: {}, now: NOW }, w.ports);
  const pause = JSON.parse(readFileSync(w.recordFile, 'utf8')).providers.codex.pause;
  assert.equal(pause.checkedAt, NOW);
  assert.match(pause.stamp, /^[0-9a-f]{64}$/);
  assert.deepEqual(shouldWake(pause, { now: NOW + MIN, stamp: pause.stamp, usage: { cx1: { readAt: NOW - MIN } } }), { wake: false, reason: 'waiting' });
  assert.deepEqual(shouldWake(pause, { now: NOW + MIN, stamp: pause.stamp, usage: { version: 1, rows: { cx1: { readAt: NOW + 30_000 } } } }), { wake: true, reason: 'read' });
  assert.deepEqual(shouldWake(pause, { now: pause.wakeAt, stamp: pause.stamp, usage: {} }), { wake: true, reason: 'time' });
  assert.deepEqual(shouldWake(null, { now: NOW }), { wake: true, reason: 'no-pause' });
  // A new sign-in rewrites the login file: its size and time change the stamp (the file is never opened).
  writeFileSync(join(w.homes.cx1, 'auth.json'), 'x'.repeat(10));
  utimesSync(join(w.homes.cx1, 'auth.json'), new Date(NOW + MIN), new Date(NOW + MIN));
  w.cache.cx1 = ok(10, 10, { readAt: NOW - 30 * MIN });
  const step = await stepLogin({ provider: 'codex', env: {}, now: NOW + 2 * MIN }, { ...w.ports, usage: { ...w.ports.usage, readLoginUsage: (login, { now }) => { w.calls.reads.push(login.name); return ok(10, 10, { readAt: now }); } } });
  assert.equal(step.login.name, 'cx1', 'the changed stamp wakes the pause and the read shows room');
});

test('P3 an explicit CODEX_HOME pins the step, and one line says so', async t => {
  const w = world(t, { logins: [{ name: 'cx5' }], rows: { cx5: ok(100, 100) } });
  const outside = await stepLogin({ provider: 'codex', env: { CODEX_HOME: '/srv/codex-manual' }, now: NOW }, w.ports);
  assert.deepEqual(outside, { pinned: true, reason: 'env', login: null, line: 'Agent login: pinned: CODEX_HOME=/srv/codex-manual is set for this Autopilot; pdd does not rotate it.' });
  const named = await stepLogin({ provider: 'codex', env: { CODEX_HOME: `${w.homes.cx5}/` }, now: NOW }, w.ports);
  assert.equal(named.login.name, 'cx5');
  assert.equal(named.line, `Agent login: pinned to codex cx5: CODEX_HOME=${w.homes.cx5}/ is set for this Autopilot; pdd does not rotate it.`);
  assert.deepEqual(w.calls.reads, [], 'a pin reads no usage');
  assert.deepEqual(await poolStatusLines({ provider: 'codex', env: { CODEX_HOME: '/srv/codex-manual' }, now: NOW }, w.ports), [outside.line]);
  // A limit end on a pin outside the pool: still no strike, nothing marked.
  assert.deepEqual(await afterStep({ login: null, end: { kind: 'limit', until: null }, now: NOW }, w.ports),
    { strike: false, line: 'pdd-account: the pinned login ended with: usage limit. pdd does not rotate a pinned login.', mark: null, alert: null });
});

test('P3 no pool login, an unsupported agent or a pdd without the pool keeps the old behavior', async t => {
  const w = world(t, { logins: [] });
  assert.deepEqual(await stepLogin({ provider: 'codex', env: {}, now: NOW }, w.ports),
    { pinned: true, reason: 'no-pool', login: null, line: 'Agent login: no codex login in the pool; the step uses its own environment.' });
  assert.equal((await stepLogin({ provider: 'gemini', env: {}, now: NOW }, w.ports)).reason, 'no-pool');
  assert.deepEqual(await poolStatusLines({ provider: 'codex', env: {}, now: NOW }, w.ports), []);
});

test('P3 a pool file that cannot be read holds new steps with one alert', async t => {
  const w = world(t, { logins: [{ name: 'cx1' }], rows: { cx1: ok(1, 1) }, reads: { cx1: ok(1, 1) } });
  w.failPool(new Error('accounts.json does not parse; pdd did not change it.'));
  const first = await stepLogin({ provider: 'codex', env: {}, now: NOW }, w.ports);
  assert.equal(first.pause.reason, 'pool-error');
  assert.equal(first.pause.wakeAt, null);
  assert.equal(first.pause.line, 'Paused: Autopilot cannot read the login pool file (accounts.json does not parse; pdd did not change it.). Fix it, then the next tick goes on; no step starts until then.');
  assert.equal(first.pause.alert.need, 'Fix the login pool file; pdd accounts list shows the problem.');
  const second = await stepLogin({ provider: 'codex', env: {}, now: NOW + 10 * MIN }, w.ports);
  assert.equal(second.pause.alert, null);
  assert.equal(second.pause.since, NOW);
  w.failPool(null);
  const back = await stepLogin({ provider: 'codex', env: {}, now: NOW + 20 * MIN }, w.ports);
  assert.equal(back.login.name, 'cx1');
  assert.equal(back.recovered, 'Autopilot has a Codex login again: cx1. The pause ended.');
});

test('P3 sorting a step end: account kinds, service kinds and work', () => {
  const codex = (...events) => events.map(event => JSON.stringify(event)).join('\n');
  const kind = (output, extra = {}) => classifyAgentEnd({ provider: 'codex', output, exitCode: 1, now: NOW, timeZone: 'UTC', ...extra });
  assert.deepEqual(kind(codex({ type: 'turn.failed', error: { message: 'You’ve hit your usage limit. More at https://example.test/limits or try again at Nov 13th, 2026 10:35 PM.' } })),
    { kind: 'limit', until: Date.UTC(2026, 10, 13, 22, 35), message: 'usage limit' });
  assert.equal(kind(codex({ type: 'turn.failed', error: { message: "You've hit your usage limit. Visit https://chatgpt.com/codex/settings/usage to purchase more credits or try again later." } })).kind, 'limit', 'a limit text that offers credits is a limit');
  assert.deepEqual(kind(codex({ type: 'error', message: 'Your workspace is out of credits.' })), { kind: 'credits', until: null, message: 'out of credits' });
  assert.equal(kind(codex({ type: 'error', message: 'workspace_member_credits_depleted' })).kind, 'credits');
  assert.deepEqual(kind(codex({ type: 'turn.failed', error: { message: 'Your access token could not be refreshed because your refresh token was already used. Please log out and sign in again.' } })),
    { kind: 'needs-sign-in', until: null, message: 'sign-in ended' });
  assert.equal(kind(codex({ type: 'error', message: 'refresh_token_invalidated' })).kind, 'needs-sign-in');
  assert.deepEqual(kind(codex({ type: 'error', message: 'unexpected status 401 Unauthorized: missing scope' })), { kind: 'stale-copy', until: null, message: '401 on the login copy' });
  assert.deepEqual(kind(codex({ type: 'turn.failed', error: { message: 'Selected model is at capacity. Please try a different model.' } })), { kind: 'capacity', until: null, message: 'service busy' });
  assert.equal(kind(codex({ type: 'error', message: 'stream error: unexpected status 503 Service Unavailable' })).kind, 'capacity');
  assert.equal(kind(codex({ type: 'error', message: 'Rate limit reached for requests per min' })).kind, 'capacity', 'a request rate limit is not a usage limit');
  // Structured times: seconds since the epoch, a relative wait, the old Claude form.
  assert.equal(kind(codex({ type: 'error', message: `{"error":{"type":"usage_limit_reached","resets_in_seconds":600}}` })).until, NOW + 10 * MIN);
  assert.equal(kind(codex({ type: 'error', message: `usage_limit_reached`, resets_at: NOW / 1000 + 60 })).until, NOW + MIN);
  assert.equal(kind(codex({ type: 'error', message: `usage_limit_reached resets_at=${NOW / 1000 + 400 * 24 * 3600}` })).until, null, 'a time more than 32 days ahead is no time');
  // Not account state: work, tool output, a later success, a test diagnostic, nothing.
  assert.deepEqual(kind(codex({ type: 'turn.failed', error: { message: 'apply_patch failed: context mismatch' } })), { kind: 'other', until: null, message: null });
  assert.equal(kind(codex({ type: 'item.completed', item: { type: 'command_execution', aggregated_output: "You've hit your usage limit." } })).kind, 'other', 'tool output never counts');
  assert.equal(kind(codex({ type: 'error', message: 'stream disconnected - retrying turn (1/5)' }, { type: 'turn.completed', usage: {} })).kind, 'other', 'a later success wins');
  assert.equal(kind('not ok 3 - expected "You have hit your usage limit" in the fixture').kind, 'other', 'a test diagnostic is never a limit');
  assert.equal(kind('').kind, 'other');
  const others = Array.from({ length: 10 }, (_, i) => codex({ type: 'error', message: `tool call ${i} failed` })).join('\n');
  assert.equal(kind(`${codex({ type: 'error', message: 'usage limit reached' })}\n${others}`).kind, 'other', 'only the 10 newest messages count');
  assert.equal(kind(`Your workspace is out of credits.\n${'x\n'.repeat(5)}`).kind, 'other', 'only the last 5 plain lines count');
  assert.equal(kind(`Your workspace is out of credits.\n${'x\n'.repeat(4)}`).kind, 'credits');
  assert.equal(kind(`${codex({ type: 'error', message: 'usage limit reached' })}\npdd-account: cx2 limited until 14:41 UTC (usage limit).`).kind, 'limit', 'the pool\'s own lines never count');
});

test('P3 sorting a Claude step end, with its reset words in their own time zone', () => {
  const claude = (...events) => events.map(event => JSON.stringify(event)).join('\n');
  const end = claude({ type: 'system', subtype: 'init' }, { type: 'result', subtype: 'success', is_error: true, result: "You've hit your limit · resets 3pm (America/Los_Angeles)" });
  assert.deepEqual(classifyAgentEnd({ provider: 'claude', output: end, exitCode: 1, now: NOW }), { kind: 'limit', until: Date.UTC(2026, 10, 11, 23, 0), message: 'usage limit' });
  const dated = claude({ type: 'result', is_error: true, result: '5-hour limit reached ∙ resets Jan 2 at 3:30pm (Europe/Berlin)' });
  assert.equal(classifyAgentEnd({ provider: 'claude', output: dated, exitCode: 1, now: Date.UTC(2026, 11, 30, 12, 0) }).until, Date.UTC(2027, 0, 2, 14, 30), 'a date with no year rolls into the next year');
  assert.equal(classifyAgentEnd({ provider: 'claude', output: claude({ type: 'result', is_error: true, result: 'Claude AI usage limit reached|1762891200' }), exitCode: 1, now: NOW }).until, 1762891200000);
  assert.equal(classifyAgentEnd({ provider: 'claude', output: claude({ type: 'assistant', error: 'rate_limit', message: { content: [] } }), exitCode: 1, now: NOW }).kind, 'limit');
  assert.equal(classifyAgentEnd({ provider: 'claude', output: claude({ type: 'result', is_error: true, result: 'Invalid API key · Please run /login' }), exitCode: 1, now: NOW }).kind, 'needs-sign-in');
  assert.equal(classifyAgentEnd({ provider: 'claude', output: claude({ type: 'result', is_error: false, result: 'done' }), exitCode: 0, now: NOW }).kind, 'other');
});

test('P3 after a step: capacity, sign-in and stale copies never strike; other ends follow the normal rules', async t => {
  const w = world(t, { logins: [{ name: 'cx3' }], rows: { cx3: ok(1, 1) } });
  const login = { ...w.pool.logins[0] };
  assert.deepEqual(await afterStep({ login, end: { kind: 'other', until: null }, now: NOW }, w.ports), { strike: true, line: null, mark: null, alert: null });
  assert.deepEqual(await afterStep({ login, end: { kind: 'capacity', until: null }, now: NOW }, w.ports),
    { strike: false, line: 'pdd-account: cx3: the AI service is busy (service busy); no login change.', mark: null, alert: null });
  assert.deepEqual(w.calls.marks, [], 'capacity changes no login');
  const sign = await afterStep({ login, end: { kind: 'needs-sign-in', until: null }, now: NOW }, w.ports);
  assert.equal(sign.strike, false);
  assert.deepEqual(sign.mark, { name: 'cx3', until: NOW + 60 * MIN, reason: 'needs-sign-in' });
  assert.deepEqual(sign.alert, { kind: 'usage-limit', text: 'Codex login cx3 needs a new sign-in. Autopilot skips it. Run: pdd accounts add cx3', tried: 'Autopilot uses the other logins of the pool.', need: 'Sign in to this login again.' });
  assert.equal(sign.line, 'pdd-account: cx3 needs a new sign-in (sign-in ended). The next step takes the next login.');
  const again = await afterStep({ login, end: { kind: 'needs-sign-in', until: null }, now: NOW + 5 * MIN }, w.ports);
  assert.equal(again.alert, null, 'one alert per sign-in event');
  assert.deepEqual(await poolStatusLines({ provider: 'codex', env: {}, now: NOW + 6 * MIN }, w.ports),
    ['Agent login: codex pool; no step used it yet. Pool: 0 of 1 ready. Next free: cx3 at 15:05 UTC.', 'cx3 needs a sign-in: run pdd accounts add cx3.']);
  const copy = await afterStep({ login: 'cx3', end: { kind: 'stale-copy', until: null }, now: NOW }, w.ports);
  assert.deepEqual(copy.mark, { name: 'cx3', until: NOW + 10 * MIN, reason: 'stale-copy' });
  assert.equal(copy.line, 'pdd-account: cx3 got 401 on its login copy; it waits 10 minutes. The next step takes the next login.');
  assert.deepEqual(w.calls.logs.map(row => row.action), ['needs-sign-in', 'needs-sign-in', 'limited']);
  // A mark that cannot be saved: still no strike, the line says why, and no alert.
  const broken = { ...w.ports, usage: { ...w.ports.usage, markLimited: () => { throw new Error('usage.json is locked'); } } };
  const failed = await afterStep({ login: { ...login, name: 'cx4' }, end: { kind: 'needs-sign-in', until: null }, now: NOW }, broken);
  assert.deepEqual([failed.strike, failed.mark, failed.alert], [false, null, null]);
  assert.match(failed.line, / \(the pool could not save this: usage\.json is locked\)$/);
});

test('P3 status lines name the last login and the pool, from local files only', async t => {
  const w = world(t, { logins: [{ name: 'cx1' }, { name: 'cx2' }, { name: 'cx3', reset: 'ask' }], rows: { cx1: ok(98, 10), cx2: ok(63, 42), cx3: { ...ok(5, 5), readAt: NOW - 60 * MIN } } });
  await stepLogin({ provider: 'codex', env: {}, now: NOW }, w.ports);
  const reads = w.calls.reads.length;
  assert.deepEqual(await poolStatusLines({ provider: 'codex', env: {}, now: NOW + 5 * MIN }, w.ports),
    ['Agent login: codex cx2 (week 63%, 5h 42%) since 14:00 UTC. Pool: 1 of 3 ready (1 not read in the last 10 minutes). Next free: cx1 at Nov 14 14:00 UTC.']);
  assert.equal(w.calls.reads.length, reads, 'status reads no usage');
  noSecret(readFileSync(w.recordFile, 'utf8'), 'the pool record');
});

test('P3 the start binding (#3230): a pool, not one fixed CODEX_HOME; old states keep working', async t => {
  const w = world(t, { logins: [{ name: 'cx1' }, { name: 'cx2' }] });
  const bind = input => startBinding({ provider: 'codex', ...input }, w.ports);
  assert.deepEqual(await bind({ env: {}, saved: null }), { agentPool: 'codex', home: null, line: 'Agent login: the codex pool (2 logins); each step takes the first login with quota.' }, 'a new state takes the pool');
  assert.deepEqual(await bind({ env: { CODEX_HOME: '/b' }, saved: { agentPool: null, home: '/a' } }), { agentPool: null, home: '/b', line: 'Agent login: pinned to CODEX_HOME=/b. It was CODEX_HOME=/a.' }, 'start with B after A: B, and one line says so');
  assert.deepEqual(await bind({ env: {}, saved: { agentPool: null, home: '/b' } }), { agentPool: null, home: '/b', line: "Agent login: pinned to CODEX_HOME=/b (saved). Run pdd autopilot start --pool to rotate the pool's logins." }, 'then a start with no variable keeps B');
  assert.deepEqual(await bind({ env: { CODEX_HOME: '/b' }, saved: { agentPool: null, home: '/b' } }), { agentPool: null, home: '/b', line: 'Agent login: pinned to CODEX_HOME=/b.' });
  assert.deepEqual(await bind({ env: {}, saved: { agentPool: null, home: '/b' }, pool: true }), { agentPool: 'codex', home: null, line: 'Agent login: the codex pool (2 logins); each step takes the first login with quota. It was CODEX_HOME=/b.' });
  assert.deepEqual(await bind({ env: {}, saved: { agentPool: 'codex', home: null } }), { agentPool: 'codex', home: null, line: 'Agent login: the codex pool (2 logins, saved).' });
  assert.deepEqual(await bind({ env: { CODEX_HOME: '/c' }, saved: { agentPool: 'codex', home: null } }), { agentPool: null, home: '/c', line: 'Agent login: pinned to CODEX_HOME=/c. It was the codex pool.' });
  assert.deepEqual(await bind({ env: {}, saved: { agentPool: null, home: null } }), { agentPool: null, home: null, line: "Agent login: no login pool; steps use Codex's own default folder. Run pdd autopilot start --pool to rotate the pool's logins." }, 'an old state with no saved folder keeps it');
  const empty = world(t, { logins: [] });
  assert.deepEqual(await startBinding({ provider: 'codex', env: {}, saved: { agentPool: null, home: '/a' }, pool: true }, empty.ports), { agentPool: null, home: '/a', line: 'Agent login: the codex pool has no login (pdd accounts add NAME); kept: CODEX_HOME=/a.' });
  assert.deepEqual(await startBinding({ provider: 'codex', env: {}, saved: null }, empty.ports), { agentPool: null, home: null, line: "Agent login: no login pool; steps use Codex's own default folder." });
});

test('P3 a pdd without the pool modules works as before the pool; a broken module is an error', async () => {
  const missing = { importModule: async path => { throw Object.assign(new Error(`Cannot find module '/pdd/src/${path.slice(2)}' imported from /pdd/src/autopilot-pool.mjs`), { code: 'ERR_MODULE_NOT_FOUND' }); } };
  assert.deepEqual(await stepLogin({ provider: 'codex', env: {}, now: NOW }, missing), { pinned: true, reason: 'no-pool', login: null, line: 'Agent login: this pdd has no login pool; the step uses its own environment.' });
  assert.deepEqual(await poolStatusLines({ provider: 'codex', env: {}, now: NOW }, missing), []);
  assert.deepEqual(await afterStep({ login: 'cx1', end: { kind: 'limit', until: null }, now: NOW }, missing),
    { strike: false, line: 'pdd-account: cx1 ended with: usage limit (the pool could not save this: this pdd has no login pool).', mark: null, alert: null });
  const broken = { importModule: async () => { throw new SyntaxError('Unexpected token'); } };
  await assert.rejects(stepLogin({ provider: 'codex', env: {}, now: NOW }, broken), /Unexpected token/);
});
