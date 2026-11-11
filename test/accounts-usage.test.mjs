import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { PassThrough } from 'node:stream';
import { existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, statSync, utimesSync, writeFileSync } from 'node:fs';
import * as fsp from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { setImmediate } from 'node:timers/promises';
import { loadUsage, markLimited, readAllUsage, readLoginUsage, saveUsage } from '../src/accounts-usage.mjs';

// Fake logins only. Every secret below is made up for this test.
const NOW = Date.UTC(2026, 10, 11, 23, 0, 0);
const S = seconds => Math.floor(NOW / 1000) + seconds;
const b64 = value => Buffer.from(JSON.stringify(value)).toString('base64url');
const jwt = payload => `${b64({ alg: 'none' })}.${b64(payload)}.fake-signature`;
const FAKE = { refresh: 'rt-fake-refresh-1234-secret', account: 'acct-fake-5678', email: 'fake.owner@example.test', apiKey: 'sk-fake-env-key-9999' };
const accessToken = exp => jwt({ exp, 'https://api.openai.com/auth': { chatgpt_account_id: FAKE.account } });
const ID_TOKEN = jwt({ email: FAKE.email });
const authFile = (exp, refresh = FAKE.refresh) => JSON.stringify({ auth_mode: 'chatgpt',
  tokens: { id_token: ID_TOKEN, access_token: accessToken(exp), refresh_token: refresh, account_id: FAKE.account }, last_refresh: '2026-11-10T00:00:00Z' });
const secrets = exp => [FAKE.refresh, FAKE.account, FAKE.email, FAKE.apiKey, ID_TOKEN, accessToken(exp)];
const DAY = 86_400;

function folder(t, prefix) {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}
function codexLogin(t, name, { exp = S(DAY), refresh = FAKE.refresh, file } = {}) {
  const home = folder(t, `pdd-usage-${name}-`);
  if (file !== null) writeFileSync(join(home, 'auth.json'), file ?? authFile(exp, refresh), { mode: 0o600 });
  return { name, provider: 'codex', home };
}
const windowRow = (usedPercent, mins, resetsAt) => ({ usedPercent, windowDurationMins: mins, resetsAt });
const teamReply = { accountId: FAKE.account, rateLimits: { planType: 'team', primary: windowRow(31, 300, S(3600)), secondary: windowRow(39, 10080, S(5 * DAY)),
  credits: { hasCredits: true, unlimited: false, balance: '17' } } };
const empty = { state: 'unknown', plan: null, week: null, fiveHour: null, accessExpiresAt: null, readAt: NOW, limitedUntil: null, limitReason: null, resets: null, note: '' };

// A fake `codex app-server`. It records each start and, at start, what the temp home holds.
function fakeCodex({ reply = teamReply, mode = 'ok', delay = 0 } = {}) {
  const starts = [];
  let active = 0, maxActive = 0;
  const spawn = (command, args, options) => {
    if (mode === 'throw') throw new Error('fake-private spawn failure');
    const home = options.env.CODEX_HOME;
    const files = Object.fromEntries(readdirSync(home).map(name => [name, readFileSync(join(home, name), 'utf8')]));
    const start = { command, args, cwd: options.cwd, env: options.env, files, methods: [], params: [] };
    starts.push(start);
    active++; maxActive = Math.max(maxActive, active);
    const child = new EventEmitter();
    child.stdin = new PassThrough(); child.stdout = new PassThrough(); child.stderr = new PassThrough();
    child.exitCode = null; child.signalCode = null;
    child.kill = () => { queueMicrotask(() => { active--; child.exitCode = 0; child.emit('close', 0); }); return true; };
    const write = value => child.stdout.write((typeof value === 'string' ? value : JSON.stringify(value)) + '\n');
    child.stdin.on('data', bytes => {
      for (const line of bytes.toString().trim().split('\n')) {
        const row = JSON.parse(line);
        start.methods.push(row.method); start.params.push(row.params);
        if (mode === 'silent') continue;
        const answer = () => {
          if (row.method === 'initialize') write({ id: 1, result: {} });
          if (row.method !== 'account/rateLimits/read') return;
          if (mode === 'error') write({ id: 2, error: { message: 'fake-private refused' } });
          else if (mode === 'garbage') write('fake-private not json');
          else if (mode === 'exit') { active--; child.emit('close', 1); }
          else write({ id: 2, result: reply });
        };
        delay ? setTimeout(answer, delay) : queueMicrotask(answer);
      }
    });
    return child;
  };
  return { spawn, starts, maxActive: () => maxActive };
}

test('a read gives week, 5-hour, plan and access end from an access-only home, and keeps no token, id or email', async t => {
  const cx5 = codexLogin(t, 'cx5');
  const base = folder(t, 'pdd-usage-tmp-');
  const codex = fakeCodex();
  const env = { PATH: '/fake/bin', HOME: '/fake/home', OPENAI_API_KEY: FAKE.apiKey, CODEX_API_KEY: FAKE.apiKey, CODEX_ACCESS_TOKEN: FAKE.apiKey, CODEX_HOME: cx5.home };
  const result = await readLoginUsage(cx5, { env, now: NOW, command: '/fake/codex' }, { spawn: codex.spawn, tmpdir: base });
  assert.deepEqual(result, { state: 'ok', plan: 'team', week: { usedPercent: 39, resetsAt: S(5 * DAY) * 1000 },
    fiveHour: { usedPercent: 31, resetsAt: S(3600) * 1000 }, accessExpiresAt: S(DAY) * 1000, readAt: NOW,
    limitedUntil: null, limitReason: null, resets: null, note: '' });
  assert.equal(codex.starts.length, 1);
  const [start] = codex.starts;
  assert.equal(start.command, '/fake/codex');
  assert.deepEqual(start.args, ['app-server', '--listen', 'stdio://']);
  assert.deepEqual(start.methods, ['initialize', 'initialized', 'account/rateLimits/read']);
  assert.deepEqual(start.params[0], { clientInfo: { name: 'pdd_accounts', title: 'PDD accounts', version: '1' } });
  assert.equal(start.cwd, start.env.CODEX_HOME);
  assert.notEqual(start.env.CODEX_HOME, cx5.home);
  assert.equal(start.env.CODEX_HOME.startsWith(join(base, 'pdd-codex-read-')), true);
  assert.deepEqual(Object.keys(start.env).sort(), ['CODEX_HOME', 'HOME', 'PATH']);
  assert.deepEqual(Object.keys(start.files).sort(), ['auth.json', 'config.toml']);
  assert.equal(JSON.parse(start.files['auth.json']).tokens.refresh_token, '');
  assert.equal(Object.values(start.files).join('\n').includes(FAKE.refresh), false, 'the temp home never has the refresh token');
  assert.equal(existsSync(start.env.CODEX_HOME), false, 'the temp home is removed');
  assert.deepEqual(readdirSync(base), []);
  const text = JSON.stringify(result);
  for (const secret of secrets(S(DAY))) assert.equal(text.includes(secret), false);
});

test('the codex bucket wins, and limits come from the read', async t => {
  const cases = [
    ['codex bucket', { rateLimits: { primary: windowRow(1, 300, S(60)) }, rateLimitsByLimitId: { codex: { primary: windowRow(100, 300, S(600)) } } },
      { fiveHour: { usedPercent: 100, resetsAt: S(600) * 1000 }, limitedUntil: S(600) * 1000, limitReason: 'limit' }],
    ['both full: the later reset', { rateLimits: { primary: windowRow(100, 300, S(600)), secondary: windowRow(100, 10080, S(DAY)) } },
      { limitedUntil: S(DAY) * 1000, limitReason: 'limit' }],
    ['full with unknown reset', { rateLimits: { primary: windowRow(100, 300, null), secondary: windowRow(20, 10080, S(DAY)) } },
      { fiveHour: { usedPercent: 100, resetsAt: null }, limitedUntil: null, limitReason: 'limit' }],
    ['credits depleted', { rateLimits: { primary: windowRow(40, 300, S(600)), secondary: windowRow(20, 10080, S(DAY)), rateLimitReachedType: 'workspace_member_credits_depleted' } },
      { limitedUntil: S(DAY) * 1000, limitReason: 'credits' }],
    ['usage limit reached', { rateLimits: { primary: windowRow(40, 300, S(600)), rateLimitReachedType: 'rate_limit_reached' } },
      { limitedUntil: S(600) * 1000, limitReason: 'limit' }],
    ['ordinary usage not allowed', { ordinaryUsageAllowed: false, rateLimits: { primary: windowRow(40, 300, S(600)) } },
      { limitedUntil: S(600) * 1000, limitReason: 'limit' }],
    ['weekly window only', { rateLimits: { planType: 'pro', primary: windowRow(32, 10080, S(DAY)), secondary: null } },
      { plan: 'pro', week: { usedPercent: 32, resetsAt: S(DAY) * 1000 }, fiveHour: null, limitedUntil: null, limitReason: null }],
    ['two windows of one length: the higher', { rateLimits: { primary: windowRow(10, 300, S(60)), secondary: windowRow(70, 300, S(90)) } },
      { fiveHour: { usedPercent: 70, resetsAt: S(90) * 1000 }, week: null }],
  ];
  for (const [label, reply, expected] of cases) {
    const result = await readLoginUsage(codexLogin(t, 'cx1'), { now: NOW }, { spawn: fakeCodex({ reply }).spawn });
    assert.equal(result.state, 'ok', label);
    for (const [key, value] of Object.entries(expected)) assert.deepEqual(result[key], value, `${label}: ${key}`);
  }
});

test('an access token that ends within 10 minutes is not read, and other logins without a usable token are not read', async t => {
  const codex = fakeCodex();
  const read = (login, now = NOW) => readLoginUsage(login, { now }, { spawn: codex.spawn });
  for (const exp of [S(-60), S(9 * 60), S(10 * 60)]) {
    assert.deepEqual(await read(codexLogin(t, 'cx2', { exp })),
      { ...empty, state: 'expired', accessExpiresAt: exp * 1000, note: 'access ended; this read never refreshes' });
  }
  assert.deepEqual(await read(codexLogin(t, 'cx3', { file: null })), { ...empty, state: 'no-login', note: 'no Codex login in this folder' });
  assert.deepEqual(await read(codexLogin(t, 'cx3', { file: '{bad' })), { ...empty, note: 'login file is unreadable' });
  assert.deepEqual(await read(codexLogin(t, 'cx3', { file: authFile(0).replace(/"access_token":"[^"]*"/, '"access_token":"opaque"') })),
    { ...empty, note: 'access end is unknown; not read' });
  assert.deepEqual(await read({ name: 'c1', provider: 'claude', home: '/fake/claude' }), { ...empty, note: 'usage read is only for codex logins' });
  assert.deepEqual(await read({ name: 'cx4', provider: 'codex', home: 'relative/cx4' }), { ...empty, note: 'login folder is not an absolute path' });
  assert.equal(codex.starts.length, 0);
  await read(codexLogin(t, 'cx2', { exp: S(10 * 60 + 1) }));
  assert.equal(codex.starts.length, 1, 'just past the margin is read');
});

test('a login file that changes to an ending token between the two reads is not read', async t => {
  const cx6 = codexLogin(t, 'cx6');
  const codex = fakeCodex();
  let opens = 0;
  const open = async (path, flags) => {
    if (path === join(cx6.home, 'auth.json') && ++opens === 2) writeFileSync(path, authFile(S(60)));
    return fsp.open(path, flags);
  };
  const result = await readLoginUsage(cx6, { now: NOW }, { spawn: codex.spawn, fs: { open } });
  assert.deepEqual(result, { ...empty, state: 'expired', accessExpiresAt: S(60) * 1000, note: 'access ended; this read never refreshes' });
  assert.equal(codex.starts.length, 0);
});

test('a bad reply or a failed read is unknown with a safe note, never a throw, and the temp home is removed', async t => {
  const base = folder(t, 'pdd-usage-tmp-');
  const cases = [
    [{ reply: null }, 'bad usage reply'], [{ reply: [] }, 'bad usage reply'], [{ reply: { rateLimits: 'x' } }, 'bad usage reply'],
    [{ reply: { rateLimits: { primary: { usedPercent: '5', windowDurationMins: 300 } } } }, 'bad usage reply'],
    [{ reply: { rateLimits: { primary: windowRow(-1, 300, null) } } }, 'bad usage reply'],
    [{ reply: { rateLimits: { primary: windowRow(5, 300, 9e12) } } }, 'bad usage reply'],
    [{ reply: { rateLimits: { primary: null, secondary: null } } }, 'no usage windows in reply'],
    [{ mode: 'throw' }, 'codex did not start'], [{ mode: 'exit' }, 'codex app-server ended early'],
    [{ mode: 'error' }, 'codex app-server refused the read'], [{ mode: 'garbage' }, 'bad reply from codex app-server'],
  ];
  for (const [options, note] of cases) {
    const result = await readLoginUsage(codexLogin(t, 'cx1'), { now: NOW }, { spawn: fakeCodex(options).spawn, tmpdir: base });
    assert.deepEqual(result, { ...empty, accessExpiresAt: S(DAY) * 1000, note }, note);
    assert.equal(JSON.stringify(result).includes('fake-private'), false);
    assert.deepEqual(readdirSync(base), [], `${note}: temp home removed`);
  }
  for (const bad of [null, 'cx1', []]) assert.deepEqual(await readLoginUsage(bad, { now: NOW }), { ...empty, note: 'usage read failed' });
});

test('a read that times out is unknown and its temp home is removed', async t => {
  const base = folder(t, 'pdd-usage-tmp-');
  const codex = fakeCodex({ mode: 'silent' });
  let started;
  const spawned = new Promise(resolve => { started = resolve; });
  const spawn = (...args) => { const child = codex.spawn(...args); started(); return child; };
  t.mock.timers.enable({ apis: ['setTimeout'] });
  const pending = readLoginUsage(codexLogin(t, 'cx1'), { now: NOW }, { spawn, tmpdir: base });
  await spawned;
  await setImmediate();
  t.mock.timers.tick(10_000);
  assert.deepEqual(await pending, { ...empty, accessExpiresAt: S(DAY) * 1000, note: 'usage read timed out' });
  assert.deepEqual(readdirSync(base), []);
});

test('a temp home that cannot be removed is named in the note', async t => {
  const base = folder(t, 'pdd-usage-tmp-');
  const result = await readLoginUsage(codexLogin(t, 'cx1'), { now: NOW },
    { spawn: fakeCodex().spawn, tmpdir: base, fs: { rm: async () => { throw new Error('busy'); } } });
  const [left] = readdirSync(base);
  assert.deepEqual(result, { ...empty, note: `temporary login folder not removed: ${join(base, left)}` });
});

test('a native fake codex program sees only an access-only home and the three read-only methods', async t => {
  const dir = folder(t, 'pdd-usage-native-');
  const out = join(dir, 'seen.json'), file = join(dir, 'codex');
  writeFileSync(file, `#!${process.execPath}
const fs = require('node:fs'), path = require('node:path'), readline = require('node:readline');
const home = process.env.CODEX_HOME, seen = { args: process.argv.slice(2), cwd: process.cwd(), methods: [] };
const auth = JSON.parse(fs.readFileSync(path.join(home, 'auth.json'), 'utf8'));
seen.refreshEmpty = auth.tokens.refresh_token === '';
seen.config = fs.readFileSync(path.join(home, 'config.toml'), 'utf8');
seen.apiKey = process.env.OPENAI_API_KEY ?? null;
readline.createInterface({ input: process.stdin }).on('line', text => {
  const row = JSON.parse(text); seen.methods.push(row.method);
  fs.writeFileSync(${JSON.stringify(out)}, JSON.stringify({ ...seen, home }));
  if (row.method === 'initialize') console.log(JSON.stringify({ id: 1, result: {} }));
  if (row.method === 'account/rateLimits/read') console.log(JSON.stringify({ id: 2, result: ${JSON.stringify(teamReply)} }));
});
`, { mode: 0o755 });
  const cx7 = codexLogin(t, 'cx7');
  const result = await readLoginUsage(cx7, { now: NOW, command: file, env: { PATH: process.env.PATH, HOME: dir, OPENAI_API_KEY: FAKE.apiKey } }, { tmpdir: dir });
  assert.equal(result.state, 'ok');
  assert.deepEqual(result.week, { usedPercent: 39, resetsAt: S(5 * DAY) * 1000 });
  const seen = JSON.parse(readFileSync(out, 'utf8'));
  assert.deepEqual(seen.args, ['app-server', '--listen', 'stdio://']);
  assert.deepEqual(seen.methods, ['initialize', 'initialized', 'account/rateLimits/read']);
  assert.equal(seen.refreshEmpty, true);
  assert.equal(seen.config, 'cli_auth_credentials_store = "file"\n');
  assert.equal(seen.apiKey, null);
  assert.equal(seen.cwd.endsWith(seen.home.split('/').pop()), true);
  assert.equal(existsSync(seen.home), false);
});

test('reading many logins runs at most 4 at a time, keeps input order and saves the cache without tokens', async t => {
  const state = folder(t, 'pdd-usage-state-');
  const env = { HOME: state, PATH: process.env.PATH };
  const logins = ['cx1', 'cx2', 'cx3', 'cx4', 'cx5', 'cx6'].map(name => codexLogin(t, name));
  const codex = fakeCodex({ delay: 20 });
  const rows = await readAllUsage(logins, { env, now: NOW }, { spawn: codex.spawn });
  assert.deepEqual(Object.keys(rows), ['cx1', 'cx2', 'cx3', 'cx4', 'cx5', 'cx6']);
  assert.equal(codex.starts.length, 6);
  assert.equal(codex.maxActive(), 4);
  for (const row of Object.values(rows)) assert.equal(row.state, 'ok');
  const file = join(state, '.local', 'state', 'pdd', 'accounts', 'usage.json');
  assert.equal(statSync(file).mode & 0o777, 0o600);
  assert.equal(statSync(join(state, '.local', 'state', 'pdd', 'accounts')).mode & 0o777, 0o700);
  const text = readFileSync(file, 'utf8');
  for (const secret of secrets(S(DAY))) assert.equal(text.includes(secret), false);
  assert.deepEqual(await loadUsage({ env }), rows);
  assert.deepEqual(readdirSync(join(state, '.local', 'state', 'pdd', 'accounts')), ['usage.json']);
});

test('reading many logins without save writes nothing; bad input throws before any read', async t => {
  const state = folder(t, 'pdd-usage-state-');
  const codex = fakeCodex();
  const rows = await readAllUsage([codexLogin(t, 'cx1')], { env: { HOME: state }, now: NOW, save: false }, { spawn: codex.spawn });
  assert.equal(rows.cx1.state, 'ok');
  assert.equal(existsSync(join(state, '.local')), false);
  for (const bad of [null, {}, [{ provider: 'codex' }], [{ name: '' }]])
    await assert.rejects(readAllUsage(bad, { env: { HOME: state } }, { spawn: codex.spawn }), { name: 'TypeError', message: 'logins must be an array of pool logins.' });
  assert.equal(codex.starts.length, 1);
});

test('the cache keeps the section 4 shape, keeps other names, drops foreign fields and uses XDG_STATE_HOME', async t => {
  const xdg = folder(t, 'pdd-usage-xdg-');
  const env = { HOME: '/nonexistent-home', XDG_STATE_HOME: xdg };
  const cx5 = { state: 'ok', plan: 'team', week: { usedPercent: 39, resetsAt: 1763412540000 }, fiveHour: { usedPercent: 31, resetsAt: 1762916000000 },
    accessExpiresAt: 1763764380000, readAt: 1762905000000, limitedUntil: null, limitReason: null, resets: null, note: '' };
  assert.deepEqual(await saveUsage({ env }, { cx5 }), { cx5 });
  const file = join(xdg, 'pdd', 'accounts', 'usage.json');
  assert.deepEqual(JSON.parse(readFileSync(file, 'utf8')), { version: 1, rows: { cx5 } });
  await saveUsage({ env }, { cx6: { ...cx5, access_token: 'fake-token-in-a-field', plan: 7, week: 'x', state: 'busy', note: null } });
  const rows = await loadUsage({ env });
  assert.deepEqual(rows.cx5, cx5);
  assert.deepEqual(rows.cx6, { ...cx5, state: 'unknown', plan: null, week: null, note: '' });
  assert.equal(readFileSync(file, 'utf8').includes('fake-token-in-a-field'), false);
  const relative = folder(t, 'pdd-usage-home-');
  await saveUsage({ env: { HOME: relative, XDG_STATE_HOME: 'relative/state' } }, { cx5 });
  assert.equal(existsSync(join(relative, '.local', 'state', 'pdd', 'accounts', 'usage.json')), true);
});

test('a bad or newer cache file loads as empty and the next save replaces it', async t => {
  const xdg = folder(t, 'pdd-usage-xdg-');
  const env = { XDG_STATE_HOME: xdg };
  const dir = join(xdg, 'pdd', 'accounts'), file = join(dir, 'usage.json');
  mkdirSync(dir, { recursive: true });
  for (const text of ['{bad', JSON.stringify({ version: 2, rows: {} }), JSON.stringify({ version: 1, rows: [] }), JSON.stringify({ version: 1, rows: { cx1: 'x' } })]) {
    writeFileSync(file, text);
    assert.deepEqual(await loadUsage({ env }), {});
  }
  writeFileSync(file, '{bad');
  await saveUsage({ env }, { cx1: { state: 'ok', readAt: NOW } });
  assert.equal(JSON.parse(readFileSync(file, 'utf8')).rows.cx1.state, 'ok');
  assert.deepEqual(await loadUsage({ env: { XDG_STATE_HOME: join(xdg, 'missing') } }), {});
});

test('a limit from a step stays until a good read; a failed read never clears it', async t => {
  const env = { XDG_STATE_HOME: folder(t, 'pdd-usage-xdg-') };
  const until = NOW + 3_600_000;
  assert.deepEqual(await markLimited({ env }, 'work3', until, 'limit'),
    { ...empty, readAt: null, limitedUntil: until, limitReason: 'limit', note: 'not read yet' });
  const failed = { ...empty, note: 'usage read timed out' };
  assert.deepEqual((await saveUsage({ env }, { work3: failed })).work3, { ...failed, limitedUntil: until, limitReason: 'limit' });
  const good = { ...empty, state: 'ok', week: { usedPercent: 40, resetsAt: null } };
  assert.deepEqual((await saveUsage({ env }, { work3: good })).work3, good);
  await markLimited({ env }, 'work3', null, 'credits');
  assert.equal((await saveUsage({ env }, { work3: { ...failed, readAt: NOW + 9e9 } })).work3.limitReason, 'credits', 'an unknown end stays');
  await markLimited({ env }, 'work3', NOW - 1, 'limit');
  assert.equal((await saveUsage({ env }, { work3: failed })).work3.limitReason, null, 'an ended limit is not kept');
  for (const args of [['', 1, 'limit'], ['work3', -1, 'limit'], ['work3', NaN, 'limit'], ['work3', 1, 'reset'], ['work3', undefined, 'limit']])
    await assert.rejects(markLimited({ env }, ...args), { name: 'TypeError' });
});

test('the cache lock: a stale lock is taken over; a held lock refuses after 100 tries and changes nothing', async t => {
  const xdg = folder(t, 'pdd-usage-xdg-');
  const env = { XDG_STATE_HOME: xdg };
  const dir = join(xdg, 'pdd', 'accounts'), lock = join(dir, 'usage.json.lock');
  await saveUsage({ env }, { cx1: { state: 'ok', readAt: NOW } });
  writeFileSync(lock, '');
  const old = new Date(Date.now() - 60_000);
  utimesSync(lock, old, old);
  await saveUsage({ env }, { cx2: { state: 'ok', readAt: NOW } });
  assert.equal(existsSync(lock), false);
  writeFileSync(lock, '');
  let sleeps = 0;
  const before = readFileSync(join(dir, 'usage.json'), 'utf8');
  await assert.rejects(markLimited({ env }, 'cx1', NOW, 'limit', { sleep: async () => { sleeps++; } }),
    { code: 'PDD_USAGE_LOCKED', message: 'The usage cache is locked by another pdd process.' });
  assert.equal(sleeps, 100);
  assert.equal(existsSync(lock), true, 'another process owns the lock');
  assert.equal(readFileSync(join(dir, 'usage.json'), 'utf8'), before);
});
