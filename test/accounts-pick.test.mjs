import test from 'node:test';
import assert from 'node:assert/strict';
import { loginReadiness, pickLogin, poolSummary, resetDecision, resetNoticeText, usedTodayFromLog } from '../src/accounts-pick.mjs';

// 14:05 PT on Nov 11, 2026 (PST, UTC-8).
const NOW = Date.UTC(2026, 10, 11, 22, 5), MIN = 60000, H = 60 * MIN, DAY = 24 * H;
const ZONE = 'America/Los_Angeles';
const login = (name, extra = {}) => ({ name, provider: 'codex', home: `/fake/${name}`, paused: false, reset: 'never', stop: { week: 97, fiveHour: 97 }, ...extra });
const win = (usedPercent, resetsAt) => ({ usedPercent, resetsAt });
const row = ({ week = win(30, NOW + 5 * DAY), fiveHour = win(10, NOW + 3 * H), readAt = NOW - MIN, state = 'ok', ...extra } = {}) =>
  ({ state, plan: 'team', week, fiveHour, accessExpiresAt: NOW + 9 * DAY, readAt, limitedUntil: null, limitReason: null, note: '', ...extra });
const deepFreeze = value => { if (value && typeof value === 'object') { Object.values(value).forEach(deepFreeze); Object.freeze(value); } return value; };
const weekOut = (resetIn, fiveHour = win(10, NOW + 3 * H)) => row({ week: win(100, NOW + resetIn), fiveHour });
const fiveOut = backIn => row({ week: win(40, NOW + 6 * DAY), fiveHour: win(100, NOW + backIn) });

test('readiness: a fresh row under both stop lines is ready; a paused login is never ready', () => {
  assert.deepEqual(loginReadiness(login('cx5'), row(), NOW), { ready: true, reason: 'ready', until: null });
  assert.deepEqual(loginReadiness(login('cx5', { paused: true }), row(), NOW), { ready: false, reason: 'paused', until: null });
  assert.deepEqual(loginReadiness(login('cx5'), row({ fiveHour: null }), NOW).reason, 'ready', 'a plan without a 5-hour window has no 5-hour limit');
});

test('readiness: a missing or old row is stale; a row read exactly 10 minutes ago is fresh', () => {
  assert.equal(loginReadiness(login('cx5'), undefined, NOW).reason, 'stale');
  assert.equal(loginReadiness(login('cx5'), null, NOW).reason, 'stale');
  assert.equal(loginReadiness(login('cx5'), row({ readAt: NOW - 10 * MIN - 1 }), NOW).reason, 'stale');
  assert.equal(loginReadiness(login('cx5'), row({ readAt: NOW - 10 * MIN }), NOW).reason, 'ready');
  assert.equal(loginReadiness(login('cx5'), row({ readAt: null }), NOW).reason, 'stale');
  assert.deepEqual(loginReadiness(login('cx5'), row({ readAt: NOW - H, limitedUntil: NOW + 2 * H }), NOW),
    { ready: false, reason: 'limited', until: NOW + 2 * H }, 'a limit that a step saw holds even on an old row');
});

test('readiness: states that need a person never come back by themselves; a bad row is unknown', () => {
  for (const state of ['no-login', 'needs-sign-in', 'expired'])
    assert.deepEqual(loginReadiness(login('cx5'), row({ state }), NOW), { ready: false, reason: state, until: null });
  assert.equal(loginReadiness(login('cx5'), row({ state: 'unknown' }), NOW).reason, 'unknown');
  assert.equal(loginReadiness(login('cx5'), row({ week: { usedPercent: '40' } }), NOW).reason, 'unknown');
  assert.deepEqual(loginReadiness(login('cx5'), row({ state: 'unknown', limitedUntil: NOW + H }), NOW), { ready: false, reason: 'limited', until: NOW + H });
});

test('readiness: a full local login whose access ended renews itself; an access copy whose access ended does not', () => {
  const ended = extra => row({ state: 'expired', week: null, fiveHour: null, accessExpiresAt: NOW - H, ...extra });
  assert.deepEqual(loginReadiness(login('cx5'), ended({ kind: 'full' }), NOW), { ready: true, reason: 'renews', until: null });
  assert.deepEqual(loginReadiness(login('work1'), ended({ kind: 'access' }), NOW), { ready: false, reason: 'expired', until: null });
  assert.deepEqual(loginReadiness(login('work1'), ended({ kind: null }), NOW), { ready: false, reason: 'expired', until: null });
  assert.deepEqual(loginReadiness(login('cx5'), ended({ kind: 'full', limitedUntil: NOW + 2 * H }), NOW), { ready: false, reason: 'limited', until: NOW + 2 * H });
  assert.equal(loginReadiness(login('cx5'), ended({ kind: 'full', readAt: NOW - H }), NOW).reason, 'stale', 'an old row is read again first');
  assert.equal(loginReadiness(login('cx5', { paused: true }), ended({ kind: 'full' }), NOW).reason, 'paused');
});

test('pick and summary: a login that renews itself is used and counted as ready', () => {
  const logins = [login('cx5'), login('cx6')];
  const usage = { cx5: weekOut(2 * DAY), cx6: row({ state: 'expired', kind: 'full', week: null, fiveHour: null }) };
  const picked = pickLogin({ logins, usage, now: NOW });
  assert.deepEqual([picked.login.name, picked.readiness], ['cx6', { ready: true, reason: 'renews', until: null }]);
  assert.deepEqual(poolSummary({ logins, usage, now: NOW }), { ready: 1, total: 2, next: 'cx6', nextFree: { name: 'cx5', at: NOW + 2 * DAY } });
});

test('readiness: a Claude login has no usage read; only a limit that a step saw stops it', () => {
  const claude = (extra = {}) => login('cl1', { provider: 'claude', home: '/fake/claude/cl1', ...extra });
  const unread = extra => ({ state: 'unknown', kind: null, plan: null, week: null, fiveHour: null, accessExpiresAt: null, readAt: null, limitedUntil: null, limitReason: null, note: '', ...extra });
  assert.deepEqual(loginReadiness(claude(), undefined, NOW), { ready: true, reason: 'ready', until: null });
  assert.deepEqual(loginReadiness(claude(), unread(), NOW), { ready: true, reason: 'ready', until: null });
  assert.deepEqual(loginReadiness(claude(), unread({ readAt: NOW - 5 * H }), NOW), { ready: true, reason: 'ready', until: null });
  assert.deepEqual(loginReadiness(claude(), unread({ limitedUntil: NOW + 3 * H, limitReason: 'limit' }), NOW), { ready: false, reason: 'limited', until: NOW + 3 * H });
  assert.deepEqual(loginReadiness(claude(), unread({ limitedUntil: NOW - 1 }), NOW), { ready: true, reason: 'ready', until: null });
  assert.deepEqual(loginReadiness(claude({ paused: true }), unread(), NOW), { ready: false, reason: 'paused', until: null });
  const logins = [claude(), login('cl2', { provider: 'claude' })];
  assert.equal(pickLogin({ logins, usage: { cl1: unread({ limitedUntil: NOW + H }) }, now: NOW }).login.name, 'cl2');
});

test('readiness: the stop lines of the login row decide week and five-hour limits', () => {
  assert.deepEqual(loginReadiness(login('cx5'), row({ week: win(97, NOW + 2 * DAY) }), NOW), { ready: false, reason: 'week', until: NOW + 2 * DAY });
  assert.equal(loginReadiness(login('cx5'), row({ week: win(96.9, NOW + 2 * DAY) }), NOW).reason, 'ready');
  assert.deepEqual(loginReadiness(login('cx5'), row({ fiveHour: win(100, NOW + 90 * MIN) }), NOW), { ready: false, reason: 'five-hour', until: NOW + 90 * MIN });
  assert.equal(loginReadiness(login('cx5', { stop: { week: 80, fiveHour: 97 } }), row({ week: win(85, NOW + DAY) }), NOW).reason, 'week');
  for (const bad of [0, 150, '80', null]) assert.equal(loginReadiness(login('cx5', { stop: { week: bad } }), row({ week: win(90, NOW + DAY) }), NOW).reason, 'ready', `stop ${bad} is 97`);
  for (const bad of [0, 150, '80', null]) assert.equal(loginReadiness(login('cx5', { stop: { week: bad } }), row({ week: win(98, NOW + DAY) }), NOW).reason, 'week', `stop ${bad} is 97`);
  assert.deepEqual(loginReadiness(login('cx5'), row({ week: win(100, NOW + DAY), fiveHour: win(100, NOW + 2 * DAY) }), NOW),
    { ready: false, reason: 'week', until: NOW + 2 * DAY }, 'both windows blocked: reason week, until the later reset');
  assert.deepEqual(loginReadiness(login('cx5'), row({ week: win(100, null) }), NOW), { ready: false, reason: 'week', until: null });
});

test('readiness: a blocked window whose reset time passed is stale, so the caller reads again', () => {
  assert.equal(loginReadiness(login('cx5'), row({ fiveHour: win(100, NOW - MIN) }), NOW).reason, 'stale');
  assert.equal(loginReadiness(login('cx5'), row({ fiveHour: win(100, NOW) }), NOW).reason, 'stale');
  assert.deepEqual(loginReadiness(login('cx5'), row({ limitedUntil: NOW + 4 * H }), NOW), { ready: false, reason: 'limited', until: NOW + 4 * H });
  assert.equal(loginReadiness(login('cx5'), row({ limitedUntil: NOW - 1 }), NOW).reason, 'ready', 'a past limit ends');
});

test('pick: the first ready login in order wins; paused and skipped logins are passed over', () => {
  const logins = deepFreeze([login('cx2', { paused: true }), login('cx5'), login('cx6'), login('work3')]);
  const usage = deepFreeze({ cx2: row(), cx5: weekOut(2 * DAY), cx6: row(), work3: row() });
  const picked = pickLogin({ logins, usage, now: NOW });
  assert.equal(picked.login, logins[2], 'the same login object comes back');
  assert.deepEqual(picked.readiness, { ready: true, reason: 'ready', until: null });
  assert.equal(pickLogin({ logins, usage, now: NOW, skip: ['cx6'] }).login.name, 'work3');
});

test('pick: all out gives the earliest return and one row per login', () => {
  const logins = [login('cx5'), login('cx6'), login('work3'), login('work1'), login('cx2', { paused: true })];
  const usage = { cx5: weekOut(2 * DAY), cx6: fiveOut(90 * MIN), work3: fiveOut(90 * MIN), work1: row({ state: 'expired' }), cx2: row() };
  assert.deepEqual(pickLogin({ logins, usage, now: NOW, skip: ['cx2'] }), {
    login: null, allOut: true, earliest: { name: 'cx6', at: NOW + 90 * MIN },
    rows: [
      { name: 'cx5', ready: false, reason: 'week', until: NOW + 2 * DAY },
      { name: 'cx6', ready: false, reason: 'five-hour', until: NOW + 90 * MIN },
      { name: 'work3', ready: false, reason: 'five-hour', until: NOW + 90 * MIN },
      { name: 'work1', ready: false, reason: 'expired', until: null },
    ] });
  assert.deepEqual(pickLogin({ logins: [login('work1')], usage, now: NOW }).earliest, null);
  assert.deepEqual(pickLogin({ logins: [], usage, now: NOW }), { login: null, allOut: true, earliest: null, rows: [] });
});

test('pick: usage uses own properties only, and a stale first login does not block a later ready one', () => {
  assert.equal(pickLogin({ logins: [login('constructor')], usage: {}, now: NOW }).rows[0].reason, 'stale');
  assert.equal(pickLogin({ logins: [login('cx5'), login('cx6')], usage: { cx5: row({ readAt: NOW - H }), cx6: row() }, now: NOW }).login.name, 'cx6');
  assert.equal(pickLogin({ logins: [null, { name: 3 }, login('cx6')], usage: { cx6: row() }, now: NOW }).login.name, 'cx6');
});

test('summary: the list example of the pool design comes out of fake rows', () => {
  const at1648 = Date.UTC(2026, 10, 12, 0, 48), at1328 = Date.UTC(2026, 10, 13, 23, 28);
  const logins = [login('cx5'), login('cx6'), login('work3'), login('work2'), login('cx2', { paused: true }), login('work1')];
  const usage = {
    cx5: row({ week: win(39, NOW + 6 * DAY), fiveHour: win(31, NOW + 4 * H) }),
    cx6: row({ week: win(16, NOW + 6 * DAY), fiveHour: win(100, at1648) }),
    work3: row({ week: win(100, at1328), fiveHour: null }),
    work2: row({ week: win(32, NOW + 5 * DAY), fiveHour: null }),
    cx2: row({ week: win(37, NOW + 6 * DAY), fiveHour: win(0, NOW + 5 * H) }),
    work1: row({ state: 'expired', week: null, fiveHour: null }),
  };
  assert.deepEqual(poolSummary({ logins, usage, now: NOW }), { ready: 2, total: 6, next: 'cx5', nextFree: { name: 'cx6', at: at1648 } });
  assert.deepEqual(poolSummary({ logins: [], usage, now: NOW }), { ready: 0, total: 0, next: null, nextFree: null });
});

// The reset rule, plan section 6. work3's week resets in 2 days 6 hours (and 3 minutes).
const WEEK_IN = 54 * H + 3 * MIN;
const decide = input => resetDecision({ now: NOW, workWaiting: 4, usedToday: [], timeZone: ZONE, ...input });

test('rule 1: no work waiting means no reset', () => {
  const input = { logins: [login('work3', { reset: 'auto' })], usage: { work3: weekOut(WEEK_IN) }, resets: { work3: { left: 3, expiresAt: null } } };
  assert.equal(decide(input).action, 'reset', 'the same pool with work uses a reset');
  for (const workWaiting of [0, -1, 1.5, '4', undefined])
    assert.deepEqual(decide({ ...input, workWaiting }), { action: 'none', login: null, until: null, reason: 'no-work', text: '' });
});

test('rule 2: another login with quota means no reset; an old or unknown row is read first', () => {
  const logins = [login('work3', { reset: 'auto' }), login('cx5')];
  const resets = { work3: { left: 3, expiresAt: null } };
  assert.deepEqual(decide({ logins, resets, usage: { work3: weekOut(WEEK_IN), cx5: row() } }), { action: 'none', login: logins[1], until: null, reason: 'quota', text: '' });
  assert.equal(decide({ logins, resets, usage: { work3: weekOut(WEEK_IN), cx5: row({ readAt: NOW - H }) } }).reason, 'stale');
  assert.equal(decide({ logins, resets, usage: { work3: weekOut(WEEK_IN), cx5: row({ state: 'unknown' }) } }).reason, 'unknown');
  assert.equal(decide({ logins, resets, usage: { work3: weekOut(WEEK_IN), cx5: row({ state: 'needs-sign-in' }) } }).action, 'reset', 'a login that needs a person is out');
  assert.deepEqual(decide({ logins, resets, usage: { work3: weekOut(WEEK_IN), cx5: row({ state: 'expired', kind: 'full' }) } }),
    { action: 'none', login: logins[1], until: null, reason: 'quota', text: '' }, 'a login that renews itself has quota');
  assert.equal(decide({ logins, resets, usage: { work3: weekOut(WEEK_IN), cx5: row({ state: 'expired', kind: 'access' }) } }).action, 'reset', 'an ended access copy is out');
});

test('rule 3: never a reset for a 5-hour limit', () => {
  const logins = [login('cx5', { reset: 'auto' }), login('cx6', { reset: 'ask' })];
  const decision = decide({ logins, usage: { cx5: fiveOut(4 * H), cx6: fiveOut(3 * H) }, resets: { cx5: { left: 3, expiresAt: null }, cx6: { left: 2, expiresAt: null } } });
  assert.deepEqual(decision, { action: 'wait', login: logins[1], until: NOW + 3 * H, reason: 'not-weekly', text: '' });
});

test('rule 3: no reset when the natural weekly reset is 24 hours away or less', () => {
  const logins = [login('work3', { reset: 'auto' })], resets = { work3: { left: 3, expiresAt: null } };
  assert.deepEqual(decide({ logins, resets, usage: { work3: weekOut(DAY) } }), { action: 'wait', login: logins[0], until: NOW + DAY, reason: 'week-soon', text: '' });
  assert.equal(decide({ logins, resets, usage: { work3: weekOut(DAY + MIN) } }).action, 'reset');
});

test('rule 4: among allowed logins the one whose natural reset is furthest away wins', () => {
  const logins = [login('work2', { reset: 'auto' }), login('work3', { reset: 'auto' }), login('work4', { reset: 'auto' }), login('work5')];
  const usage = { work2: weekOut(2 * DAY), work3: weekOut(4 * DAY), work4: weekOut(3 * DAY), work5: weekOut(6 * DAY) };
  const resets = { work2: { left: 1, expiresAt: null }, work3: { left: 1, expiresAt: null }, work4: { left: 1, expiresAt: null }, work5: { left: 5, expiresAt: null } };
  const decision = decide({ logins, usage, resets });
  assert.equal(decision.login, logins[1], 'work5 is further but its setting is never');
  assert.deepEqual([decision.action, decision.reason, decision.until], ['reset', 'furthest', NOW + 4 * DAY]);
  assert.equal(decide({ logins, usage: { ...usage, work4: weekOut(4 * DAY) }, resets }).login.name, 'work3', 'a tie keeps the person order');
});

test('rule 5: a reset that would expire unused is used first', () => {
  const logins = [login('work3', { reset: 'auto' }), login('work4', { reset: 'auto' })];
  const usage = { work3: weekOut(5 * DAY), work4: weekOut(2 * DAY) };
  const decision = decide({ logins, usage, resets: { work3: { left: 2, expiresAt: NOW + 6 * DAY }, work4: { left: 1, expiresAt: NOW + DAY } } });
  assert.deepEqual([decision.login.name, decision.reason], ['work4', 'expiring'], 'work4 loses its reset before its week resets');
  assert.equal(decide({ logins, usage, resets: { work3: { left: 2, expiresAt: null }, work4: { left: 1, expiresAt: NOW + 3 * DAY } } }).login.name, 'work3',
    'a reset that ends after the natural reset is not at risk, so rule 4 decides');
  assert.equal(decide({ logins, usage, resets: { work3: { left: 2, expiresAt: NOW + 4 * DAY }, work4: { left: 1, expiresAt: NOW + DAY + H } } }).login.name, 'work4',
    'of two expiring resets, the one that ends first goes first');
  assert.equal(decide({ logins, usage: { work3: weekOut(2 * DAY), work4: weekOut(5 * DAY) }, resets: { work3: { left: 2, expiresAt: NOW + 2 * DAY + H }, work4: { left: 1, expiresAt: NOW + 5 * DAY } } }).login.name, 'work4',
    'only work4 would expire unused (it ends at its natural reset); work3 ends sooner but after its natural reset');
  assert.equal(decide({ logins, usage, resets: { work3: { left: 2, expiresAt: null }, work4: { left: 1, expiresAt: NOW + 2 * DAY } } }).login.name, 'work4',
    'a reset that ends exactly at the natural reset would expire unused');
});

test('rule 6, mixed case: a 5-hour login back within 2 hours means wait', () => {
  const logins = [login('cx6'), login('work3', { reset: 'auto' })];
  const resets = { work3: { left: 3, expiresAt: null } };
  assert.deepEqual(decide({ logins, resets, usage: { cx6: fiveOut(2 * H), work3: weekOut(WEEK_IN) } }),
    { action: 'wait', login: logins[0], until: NOW + 2 * H, reason: 'back-soon', text: '' });
});

test('rule 6, mixed case: when the earliest return is more than 2 hours away, reset the allowed weekly login with the furthest reset', () => {
  const logins = [login('cx6'), login('work3', { reset: 'auto' }), login('work4', { reset: 'auto' })];
  const resets = { work3: { left: 3, expiresAt: null }, work4: { left: 3, expiresAt: null } };
  const decision = decide({ logins, resets, usage: { cx6: fiveOut(2 * H + MIN), work3: weekOut(WEEK_IN), work4: weekOut(2 * DAY) } });
  assert.deepEqual([decision.action, decision.login.name, decision.until], ['reset', 'work3', NOW + WEEK_IN]);
});

test('rule 6, mixed case: no reset when the weekly login\'s own 5-hour window is not free', () => {
  const logins = [login('cx6'), login('work3', { reset: 'auto' })];
  const usage = { cx6: fiveOut(4 * H), work3: weekOut(WEEK_IN, win(100, NOW + 3 * H)) };
  assert.deepEqual(decide({ logins, usage, resets: { work3: { left: 3, expiresAt: null } } }),
    { action: 'wait', login: logins[0], until: NOW + 4 * H, reason: 'five-hour-busy', text: '' }, 'pdd waits for cx6, which comes back first');
});

test('setting never never resets', () => {
  const logins = [login('work3'), login('work4', { reset: 'nope' }), login('work5', { reset: undefined })];
  const usage = { work3: weekOut(WEEK_IN), work4: weekOut(3 * DAY), work5: weekOut(4 * DAY) };
  const resets = { work3: { left: 3, expiresAt: null }, work4: { left: 3, expiresAt: null }, work5: { left: 3, expiresAt: null } };
  assert.deepEqual(decide({ logins, usage, resets }), { action: 'wait', login: logins[0], until: NOW + WEEK_IN, reason: 'not-allowed', text: '' });
});

test('no reset left, or a login limited by a step with an unknown window, gives no reset', () => {
  const logins = [login('work3', { reset: 'auto' })];
  for (const resets of [{}, { work3: { left: 0, expiresAt: null } }, { work3: { left: '3' } }, undefined])
    assert.equal(decide({ logins, resets, usage: { work3: weekOut(WEEK_IN) } }).reason, 'no-resets');
  const limited = row({ week: win(60, NOW + 5 * DAY), limitedUntil: NOW + 3 * DAY });
  assert.equal(decide({ logins, resets: { work3: { left: 3, expiresAt: null } }, usage: { work3: limited } }).reason, 'not-weekly');
});

test('ask gives the alert text of the plan', () => {
  const logins = [login('work3', { reset: 'ask' })];
  assert.deepEqual(decide({ logins, usage: { work3: weekOut(WEEK_IN) }, resets: { work3: { left: 3, expiresAt: null } } }), {
    action: 'ask', login: logins[0], until: NOW + WEEK_IN, reason: 'furthest',
    text: 'Reset work3 now? Its week resets in 2 days 6 hours; 3 resets left; 4 issues wait. Run: pdd accounts reset work3' });
  assert.equal(decide({ logins, workWaiting: 1, usage: { work3: weekOut(2 * DAY + 30 * MIN) }, resets: { work3: { left: 1, expiresAt: null } } }).text,
    'Reset work3 now? Its week resets in 2 days; 1 reset left; 1 issue waits. Run: pdd accounts reset work3');
});

test('auto gives the reset action and the owner notice of the plan', () => {
  const logins = deepFreeze([login('work3', { reset: 'auto' })]);
  const input = deepFreeze({ logins, usage: { work3: weekOut(WEEK_IN) }, resets: { work3: { left: 3, expiresAt: null } }, usedToday: [] });
  assert.deepEqual(decide(input), {
    action: 'reset', login: logins[0], until: NOW + WEEK_IN, reason: 'furthest',
    text: 'Autopilot used a reset on work3 at 14:05 PT: its week would reset in 2 days 6 hours; 2 resets left' });
});

test('a second reset on the same login the same day is refused', () => {
  const logins = [login('work3', { reset: 'auto' }), login('work4', { reset: 'auto' })];
  const usage = { work3: weekOut(WEEK_IN), work4: weekOut(2 * DAY) };
  const resets = { work3: { left: 3, expiresAt: null }, work4: { left: 3, expiresAt: null } };
  const log = [
    { at: new Date(NOW - 23 * H).toISOString(), action: 'reset', login: 'work3', detail: 'used by Autopilot' },
    { at: new Date(NOW - 25 * H).toISOString(), action: 'reset', login: 'work4', detail: 'used by Autopilot' },
    { at: new Date(NOW - H).toISOString(), action: 'pause', login: 'work4', detail: '' },
  ];
  const usedToday = usedTodayFromLog(log, NOW);
  assert.deepEqual(usedToday, ['work3']);
  assert.equal(decide({ logins, usage, resets, usedToday }).login.name, 'work4', 'work3 is skipped; work4 is the next best');
  assert.deepEqual(decide({ logins: [logins[0]], usage, resets, usedToday }), { action: 'wait', login: logins[0], until: NOW + WEEK_IN, reason: 'used-today', text: '' });
});

test('the day of the reset log is the last 24 hours, and a clock that runs ahead still counts', () => {
  const rows = [
    { at: NOW - DAY, action: 'reset', login: 'old' },
    { at: NOW - DAY + 1, action: 'reset', login: 'edge' },
    { at: new Date(NOW + H).toISOString(), action: 'reset', login: 'ahead' },
    { at: 'not a time', action: 'reset', login: 'bad' },
    { at: NOW, action: 'reset', login: 'edge' },
    null, { at: NOW, action: 'reset', login: 7 },
  ];
  assert.deepEqual(usedTodayFromLog(rows, NOW), ['edge', 'ahead']);
  assert.deepEqual(usedTodayFromLog(undefined, NOW), []);
});

test('the owner notice leaves out what is not known', () => {
  assert.equal(resetNoticeText({ actor: 'A person at a terminal', name: 'work3', now: NOW, until: NOW + 25 * H, left: 1, timeZone: ZONE }),
    'A person at a terminal used a reset on work3 at 14:05 PT: its week would reset in 1 day 1 hour; 0 resets left');
  assert.equal(resetNoticeText({ actor: 'You', name: 'work3', now: NOW, timeZone: ZONE }), 'You used a reset on work3 at 14:05 PT');
  assert.equal(resetNoticeText({ actor: 'You', name: 'work3', now: NOW, until: NOW + 59 * MIN, timeZone: ZONE }), 'You used a reset on work3 at 14:05 PT: its week would reset in 59 minutes');
  assert.equal(resetNoticeText({ actor: 'You', name: 'work3', now: NOW, until: NOW + 30 * 1000, left: 2, timeZone: ZONE }), 'You used a reset on work3 at 14:05 PT: its week would reset in 1 minute; 1 reset left');
  assert.match(resetNoticeText({ actor: 'You', name: 'work3', now: NOW, timeZone: 'Not/AZone' }), /^You used a reset on work3 at \d\d:\d\d \S/);
});
