import test from 'node:test';
import assert from 'node:assert/strict';
import { PassThrough } from 'node:stream';
import { runReset } from '../src/accounts-reset.mjs';

// 14:05 PT on Nov 11, 2026. Every port is a fake: no test reaches Codex.
const NOW = Date.UTC(2026, 10, 11, 22, 5), H = 3600000;
const WORK3 = Object.freeze({ name: 'work3', provider: 'codex', home: '/fake/work3', mode: 'local', paused: false, reset: 'ask', stop: { week: 97, fiveHour: 97 } });
const QUESTION = 'Reset work3 now? This uses one of its Codex resets. pdd cannot undo it.\nType work3 to confirm, or press Enter to stop: ';

function terminal(typed) {
  const stdin = new PassThrough(); stdin.isTTY = true;
  if (typed !== undefined) setImmediate(() => { if (typed === null) stdin.end(); else stdin.write(typed); });
  const written = [];
  return { stdin, stdout: { write: text => { written.push(text); return true; } }, written };
}

function fakes({ login = WORK3, log = [], usage = { state: 'ok', week: { usedPercent: 100, resetsAt: NOW + 54 * H + 3 * 60000 }, resets: { left: 3, expiresAt: null }, readAt: NOW - 60000 }, outcome = 'reset', ...more } = {}) {
  const calls = [];
  const record = (port, value) => (...args) => { calls.push([port, ...args]); return typeof value === 'function' ? value(...args) : value; };
  return { calls, ports: {
    now: () => NOW, timeZone: 'America/Los_Angeles',
    findLogin: record('findLogin', login), readLog: record('readLog', log), appendLog: record('appendLog', undefined),
    readUsage: record('readUsage', usage), forgetUsage: record('forgetUsage', undefined), notify: record('notify', undefined),
    consumeReset: record('consumeReset', () => typeof outcome === 'function' ? outcome() : { outcome }), ...more } };
}

const run = (input, ports) => runReset({ name: 'work3', env: {}, ...input }, ports);
const ports = calls => calls.map(([port]) => port);

test('a person at a terminal who types the name uses one reset; the log, the cache and the owner are told', async () => {
  const t = terminal('work3\n'), f = fakes();
  assert.deepEqual(await run(t, f.ports), { exitCode: 0, message: 'You used a reset on work3 at 14:05 PT: its week would reset in 2 days 6 hours; 2 resets left' });
  assert.deepEqual(t.written, [QUESTION]);
  assert.deepEqual(f.calls, [
    ['findLogin', 'work3'], ['readLog', 'work3'], ['readUsage', 'work3'], ['consumeReset', WORK3],
    ['appendLog', { at: '2026-11-11T22:05:00.000Z', action: 'reset', login: 'work3', detail: 'used by a person at a terminal' }],
    ['forgetUsage', 'work3'],
    ['notify', 'A person at a terminal used a reset on work3 at 14:05 PT: its week would reset in 2 days 6 hours; 2 resets left'],
  ]);
});

test('an agent or Autopilot is refused before anything is read or asked', async () => {
  for (const env of [{ CODEX_THREAD_ID: 'thread-1' }, { CLAUDECODE: '1' }, { PDD_AGENT_SESSION: '1' }, { PDD_AGENT: 'codex' }, { PDD_AUTOPILOT_CONTEXT: 'ctx' }]) {
    const t = terminal('work3\n'), f = fakes();
    assert.deepEqual(await run({ ...t, env }, f.ports), { exitCode: 2,
      message: 'pdd accounts reset runs only for a person at a terminal. It does not run under an agent or Autopilot. No reset was used.' }, JSON.stringify(env));
    assert.deepEqual([f.calls, t.written], [[], []]);
  }
});

test('without a terminal nothing is read or asked', async () => {
  const f = fakes(), stdin = new PassThrough(), written = [];
  assert.deepEqual(await run({ stdin, stdout: { write: text => written.push(text) } }, f.ports),
    { exitCode: 2, message: 'pdd accounts reset needs a person at a terminal to type the login name. No reset was used.' });
  assert.deepEqual([f.calls, written], [[], []]);
});

test('this version has no real reset call, so the default ports never spend a reset', async () => {
  const t = terminal('work3\n'), { consumeReset, ...rest } = fakes().ports;
  assert.equal(typeof consumeReset, 'function');
  assert.deepEqual(await run(t, rest), { exitCode: 2, message: 'This pdd has no Codex reset call yet. No reset was used.' });
  assert.deepEqual(t.written, []);
});

test('a login that may not be reset is refused before the question', async () => {
  const cases = [
    [{ name: 'Work3' }, {}, 2, 'Give a login name: pdd accounts reset NAME. No reset was used.'],
    [{ name: undefined }, {}, 2, 'Give a login name: pdd accounts reset NAME. No reset was used.'],
    [{}, { login: null }, 2, 'No login named work3 in this pool. See pdd accounts list. No reset was used.'],
    [{}, { findLogin: () => { throw Error('bad pool file'); } }, 1, 'Could not read the login pool. No reset was used.'],
    [{}, { login: { ...WORK3, provider: 'claude' } }, 2, 'work3 is a Claude login. Only Codex logins have resets. No reset was used.'],
    [{}, { login: { ...WORK3, mode: 'cloud' } }, 2, 'work3 is on the login server. This version resets only local logins. No reset was used.'],
    [{}, { login: { ...WORK3, reset: 'never' } }, 2, 'work3 has reset never. To allow resets, run: pdd accounts set work3 --reset ask. No reset was used.'],
    [{}, { login: { ...WORK3, reset: undefined } }, 2, 'work3 has reset never. To allow resets, run: pdd accounts set work3 --reset ask. No reset was used.'],
    [{}, { readLog: () => { throw Error('bad log'); } }, 1, 'Could not read the reset log of work3. No reset was used.'],
  ];
  for (const [input, options, exitCode, message] of cases) {
    const t = terminal('work3\n'), f = fakes(options);
    assert.deepEqual(await run({ ...t, ...input }, f.ports), { exitCode, message });
    assert.deepEqual(t.written, [], message);
    assert.equal(ports(f.calls).includes('consumeReset'), false, message);
  }
  const t = terminal('work3\n'), f = fakes({ login: { ...WORK3, reset: 'auto', mode: undefined } });
  assert.equal((await run(t, f.ports)).exitCode, 0, 'auto allows it, and a login without mode is local');
});

test('a second reset on the same login within 24 hours is refused', async () => {
  const log = [{ at: new Date(NOW - 23 * H).toISOString(), action: 'reset', login: 'work3', detail: 'used by Autopilot' }];
  const t = terminal('work3\n'), f = fakes({ log });
  assert.deepEqual(await run(t, f.ports), { exitCode: 2, message: 'work3 used a reset less than 24 hours ago. pdd allows one reset per login per day. No reset was used.' });
  assert.deepEqual([ports(f.calls), t.written], [['findLogin', 'readLog'], []]);
  const later = fakes({ log: [{ ...log[0], at: new Date(NOW - 25 * H).toISOString() }] });
  assert.equal((await run(terminal('work3\n'), later.ports)).exitCode, 0, 'after 24 hours it is allowed again');
});

test('a wrong name or an empty answer does not confirm', async () => {
  for (const typed of ['work4\n', '\n', 'WORK3\n', null]) {
    const t = terminal(typed), f = fakes();
    assert.deepEqual(await run(t, f.ports), { exitCode: 1, message: 'Not confirmed. No reset was used.' }, JSON.stringify(typed));
    assert.deepEqual([t.written, ports(f.calls)], [[QUESTION], ['findLogin', 'readLog']]);
  }
  assert.equal((await run(terminal('  work3 \r\n'), fakes().ports)).exitCode, 0, 'spaces around the typed name are trimmed');
});

test('a reset call that uses nothing writes nothing', async () => {
  const cases = [
    ['noCredit', 'work3 has no reset left. No reset was used.'],
    ['nothingToReset', 'work3 has no limit that a reset can clear now. No reset was used.'],
    ['failed', 'Could not reach Codex for work3. No reset was used.'],
  ];
  for (const [outcome, message] of cases) {
    const f = fakes({ outcome });
    assert.deepEqual(await run(terminal('work3\n'), f.ports), { exitCode: 1, message });
    assert.deepEqual(ports(f.calls), ['findLogin', 'readLog', 'readUsage', 'consumeReset']);
  }
});

test('an unclear reset call is logged as a reset, so it is not tried again the same day', async () => {
  const unclear = 'The reset of work3 did not finish clearly. It may have used a reset. Run pdd accounts list to see its usage.';
  for (const outcome of ['unclear', 'surprise', () => { throw Error('timeout'); }, () => undefined]) {
    const f = fakes({ outcome });
    assert.deepEqual(await run(terminal('work3\n'), f.ports), { exitCode: 1, message: unclear });
    assert.deepEqual(f.calls.slice(4), [['appendLog', { at: '2026-11-11T22:05:00.000Z', action: 'reset', login: 'work3', detail: 'outcome unclear' }], ['forgetUsage', 'work3']]);
    const again = fakes({ log: [f.calls[4][1]] });
    assert.equal((await run(terminal('work3\n'), again.ports)).exitCode, 2);
  }
});

test('alreadyRedeemed counts as a used reset; missing usage facts are left out of the notice', async () => {
  const f = fakes({ outcome: 'alreadyRedeemed', usage: null });
  assert.deepEqual(await run(terminal('work3\n'), f.ports), { exitCode: 0, message: 'You used a reset on work3 at 14:05 PT' });
  assert.deepEqual(f.calls.at(-1), ['notify', 'A person at a terminal used a reset on work3 at 14:05 PT']);
  const broken = fakes({ readUsage: () => { throw Error('cache'); } });
  assert.deepEqual(await run(terminal('work3\n'), broken.ports), { exitCode: 0, message: 'You used a reset on work3 at 14:05 PT' });
});

test('after a used reset, a failed log write is said, and failed cache or notice ports change nothing else', async () => {
  const f = fakes({ appendLog: () => { throw Error('disk'); }, forgetUsage: () => { throw Error('disk'); }, notify: () => { throw Error('net'); } });
  assert.deepEqual(await run(terminal('work3\n'), f.ports), { exitCode: 0,
    message: 'You used a reset on work3 at 14:05 PT: its week would reset in 2 days 6 hours; 2 resets left. The local log could not be written.' });
  const unclear = fakes({ outcome: 'unclear', appendLog: () => { throw Error('disk'); } });
  assert.equal((await run(terminal('work3\n'), unclear.ports)).message,
    'The reset of work3 did not finish clearly. It may have used a reset. Run pdd accounts list to see its usage. The local log could not be written.');
  const { notify, ...withoutNotify } = fakes().ports;
  assert.equal((await run(terminal('work3\n'), withoutNotify)).exitCode, 0, 'no notify port is fine');
});

test('a closed output before the question gives one line and spends nothing', async () => {
  const t = terminal('work3\n'), f = fakes();
  assert.deepEqual(await run({ ...t, stdout: { write: () => { throw Error('EPIPE'); } } }, f.ports), { exitCode: 1, message: 'pdd accounts reset failed. No reset was used.' });
  assert.equal(ports(f.calls).includes('consumeReset'), false);
});
