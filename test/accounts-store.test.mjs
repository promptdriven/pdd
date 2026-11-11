import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs/promises';
import { mkdtempSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { PoolError, appendLog, orderedLogins, poolPaths, readLog, readPool, updatePool } from '../src/accounts-store.mjs';

const freshHome = () => realpathSync(mkdtempSync(join(tmpdir(), 'pdd-accounts-store-')));
const mode = async path => (await fs.stat(path)).mode & 0o777;
const login = (name, extra = {}) => ({ name, provider: 'codex', home: `/synthetic/homes/${name}`, ...extra });
const addLogin = row => pool => ({ ...pool, logins: [...pool.logins, row] });

test('paths follow HOME, absolute XDG folders only, and refuse a missing home', () => {
  const home = freshHome();
  assert.deepEqual(poolPaths({ HOME: home }), {
    configDir: join(home, '.config', 'pdd'), stateDir: join(home, '.local', 'state', 'pdd', 'accounts'),
    poolFile: join(home, '.config', 'pdd', 'accounts.json'), logFile: join(home, '.local', 'state', 'pdd', 'accounts', 'log.jsonl'),
    usageFile: join(home, '.local', 'state', 'pdd', 'accounts', 'usage.json'), machineFile: join(home, '.config', 'pdd', 'machine.json') });
  const xdg = poolPaths({ HOME: home, XDG_CONFIG_HOME: '/synthetic/config', XDG_STATE_HOME: '/synthetic/state' });
  assert.equal(xdg.poolFile, '/synthetic/config/pdd/accounts.json');
  assert.equal(xdg.logFile, '/synthetic/state/pdd/accounts/log.jsonl');
  assert.equal(poolPaths({ HOME: home, XDG_CONFIG_HOME: 'relative' }).configDir, join(home, '.config', 'pdd'));
  assert.equal(poolPaths({ HOME: 'relative' }, { userInfo: () => ({ homedir: home }) }).configDir, join(home, '.config', 'pdd'));
  assert.throws(() => poolPaths({}, { userInfo: () => { throw Error('no account'); } }), error => error instanceof PoolError && error.code === 'no-home'
    && error.message === 'pdd accounts needs an absolute home folder; set HOME to an absolute path.');
});

test('a missing pool file reads as the empty pool and is not created', async () => {
  const env = { HOME: freshHome() };
  assert.deepEqual(await readPool({ env }), { version: 1, order: [], logins: [], server: null });
  await assert.rejects(fs.stat(poolPaths(env).configDir), { code: 'ENOENT' });
});

test('a change writes the version 1 file with defaults, mode 0600 in a new 0700 folder, and leaves no lock', async () => {
  const env = { HOME: freshHome() }, { configDir, poolFile } = poolPaths(env);
  const pool = await updatePool({ env }, addLogin(login('cx5', { addedAt: '2026-11-11T23:00:00.000Z' })));
  const expected = { version: 1, order: [], logins: [{ ...login('cx5'), addedAt: '2026-11-11T23:00:00.000Z',
    source: 'import', mode: 'local', paused: false, reset: 'never', stop: { week: 97, fiveHour: 97 } }], server: null };
  assert.deepEqual(pool, expected);
  const text = await fs.readFile(poolFile, 'utf8');
  assert.deepEqual(JSON.parse(text), expected);
  assert.equal(text, `${JSON.stringify(expected, null, 2)}\n`);
  assert.equal(await mode(poolFile), 0o600);
  assert.equal(await mode(configDir), 0o700);
  assert.deepEqual((await fs.readdir(configDir)).sort(), ['accounts.json']);
  assert.deepEqual(await readPool({ env }), expected);
});

test('unknown fields at the top and in rows stay on every write', async () => {
  const env = { HOME: freshHome() }, { configDir, poolFile } = poolPaths(env);
  await fs.mkdir(configDir, { recursive: true });
  await fs.writeFile(poolFile, JSON.stringify({ version: 1, order: ['cx5'], server: null, futureTop: { keep: true },
    logins: [{ ...login('cx5'), futureRow: [1, 2], stop: { week: 90, futurePart: 'x' } }] }));
  await updatePool({ env }, pool => ({ ...pool, logins: pool.logins.map(row => ({ ...row, paused: true })) }));
  const saved = JSON.parse(await fs.readFile(poolFile, 'utf8'));
  assert.deepEqual(saved.futureTop, { keep: true });
  assert.deepEqual(saved.logins[0].futureRow, [1, 2]);
  assert.deepEqual(saved.logins[0].stop, { week: 90, futurePart: 'x', fiveHour: 97 });
  assert.equal(saved.logins[0].paused, true);
});

test('a bad pool file is never overwritten and names the broken rule', async () => {
  const cases = [
    ['{"version": 1, "logins": [', 'it is not valid JSON'],
    [JSON.stringify({ version: 2, logins: [] }), 'its version is not 1'],
    [JSON.stringify({ version: 1, logins: [login('cx5'), login('cx5')] }), 'the name cx5 is used twice'],
    [JSON.stringify({ version: 1, logins: [login('Bad Name')] }), 'login 1 has no valid name'],
    [JSON.stringify({ version: 1, logins: [login('cx5', { reset: 'sometimes' })] }), 'cx5 has no valid reset setting'],
    [JSON.stringify({ version: 1, logins: [login('cx5', { home: 'relative/cx5' })] }), 'cx5 has no absolute home'],
    [JSON.stringify({ version: 1, logins: [login('cx5', { stop: { week: 0 } })] }), 'cx5 has a stop line outside 1 to 100'],
  ];
  for (const [text, problem] of cases) {
    const env = { HOME: freshHome() }, { configDir, poolFile } = poolPaths(env);
    await fs.mkdir(configDir, { recursive: true });
    await fs.writeFile(poolFile, text);
    const message = `The pool file ${poolFile} is not valid: ${problem}. pdd did not change it. Fix or move the file, then try again.`;
    await assert.rejects(readPool({ env }), error => error instanceof PoolError && error.code === 'invalid' && error.message === message);
    let called = false;
    await assert.rejects(updatePool({ env }, pool => { called = true; return pool; }), { code: 'invalid', message });
    assert.equal(called, false);
    assert.equal(await fs.readFile(poolFile, 'utf8'), text);
    assert.deepEqual(await fs.readdir(configDir), ['accounts.json'], 'no lock or temp file stays');
  }
});

test('a failed or invalid change writes nothing and releases the lock', async () => {
  const env = { HOME: freshHome() }, { poolFile } = poolPaths(env);
  await updatePool({ env }, addLogin(login('cx5')));
  const before = await fs.readFile(poolFile, 'utf8');
  await assert.rejects(updatePool({ env }, () => { throw new Error('synthetic change failure'); }), { message: 'synthetic change failure' });
  await assert.rejects(updatePool({ env }, addLogin(login('cx5'))), error => error.code === 'invalid-change'
    && error.message === 'pdd did not save the pool: the name cx5 is used twice.');
  assert.equal(await fs.readFile(poolFile, 'utf8'), before);
  assert.equal((await updatePool({ env }, addLogin(login('cx6')))).logins.length, 2);
});

test('a fresh lock makes a change wait and then refuse; a stale lock is removed', async () => {
  const env = { HOME: freshHome() }, { configDir, poolFile } = poolPaths(env), lock = `${poolFile}.lock`;
  await fs.mkdir(configDir, { recursive: true });
  await fs.writeFile(lock, '{"token":"other"}\n');
  let clock = Date.now(); const sleeps = [];
  const ports = { now: () => clock, sleep: async ms => { sleeps.push(ms); clock += ms; } };
  await assert.rejects(updatePool({ env }, addLogin(login('cx5')), ports), error => error.code === 'busy'
    && error.message === `Another pdd process is changing the pool (${lock}). Try again.`);
  assert.equal(sleeps.length, 100);
  assert.ok(sleeps.every(ms => ms === 50));
  assert.equal(await fs.readFile(lock, 'utf8'), '{"token":"other"}\n', 'the other process keeps its lock');
  await assert.rejects(fs.stat(poolFile), { code: 'ENOENT' });

  const old = new Date(Date.now() - 31_000);
  await fs.utimes(lock, old, old);
  const pool = await updatePool({ env }, addLogin(login('cx5')));
  assert.equal(pool.logins[0].name, 'cx5');
  await assert.rejects(fs.stat(lock), { code: 'ENOENT' });
});

test('a failed rename keeps the old pool file and removes the temp file', async () => {
  const env = { HOME: freshHome() }, { configDir, poolFile } = poolPaths(env);
  await updatePool({ env }, addLogin(login('cx5')));
  const before = await fs.readFile(poolFile, 'utf8');
  const failing = { ...fs, rename: async () => { throw Object.assign(new Error('synthetic rename failure'), { code: 'EIO' }); } };
  await assert.rejects(updatePool({ env }, addLogin(login('cx6')), { fs: failing }), { code: 'EIO' });
  assert.equal(await fs.readFile(poolFile, 'utf8'), before);
  assert.deepEqual(await fs.readdir(configDir), ['accounts.json']);
});

test('many changes at once lose none', async () => {
  const env = { HOME: freshHome() };
  const names = Array.from({ length: 20 }, (_, index) => `cx${index}`);
  await Promise.all(names.map(name => updatePool({ env }, addLogin(login(name)))));
  assert.deepEqual((await readPool({ env })).logins.map(row => row.name).sort(), [...names].sort());
});

test('effective order: named logins first, then the rest by addedAt, with 1-based positions', () => {
  const pool = { version: 1, order: ['work3', 'ghost', 'cx5', 'work3', 'owner/shared'], server: null, logins: [
    login('cx1', { addedAt: '2026-11-03T00:00:00.000Z' }), login('cx5', { paused: true }), login('nodate'),
    login('work3', { addedAt: '2026-11-01T00:00:00.000Z' }), login('cx2', { addedAt: '2026-11-02T00:00:00.000Z' }),
    login('tie', { addedAt: '2026-11-02T00:00:00.000Z' }) ] };
  const copy = structuredClone(pool);
  const rows = orderedLogins(pool);
  assert.deepEqual(rows.map(row => [row.position, row.name]), [[1, 'work3'], [2, 'cx5'], [3, 'cx2'], [4, 'tie'], [5, 'cx1'], [6, 'nodate']]);
  assert.equal(rows[1].paused, true);
  assert.deepEqual(pool, copy, 'the input does not change');
  assert.deepEqual(orderedLogins({ version: 1, order: [], logins: [], server: null }), []);
});

test('the local log keeps one safe line per change, 0600 in a 0700 folder', async () => {
  const env = { HOME: freshHome() }, { stateDir, logFile } = poolPaths(env);
  const now = Date.parse('2026-11-11T22:58:00.000Z');
  const first = await appendLog({ env }, { action: 'import', login: 'cx5', detail: 'folder /synthetic/cx5' }, { now: () => now });
  assert.deepEqual(first, { at: '2026-11-11T22:58:00.000Z', action: 'import', login: 'cx5', detail: 'folder /synthetic/cx5' });
  const jwt = 'eyJhbGciOiJub25lIn0.eyJleHAiOjF9.c2lnbmF0dXJl';
  const second = await appendLog({ env }, { at: '2026-11-11T23:00:00.000Z', action: 'set', login: 'cx6',
    detail: `owner person@example.com token ${jwt}\nnext line ${'x'.repeat(400)}` });
  assert.equal(second.detail.includes('person@example.com'), false);
  assert.equal(second.detail.includes(jwt), false);
  assert.match(second.detail, /^owner \[removed\] token \[removed\] next line x+$/);
  assert.equal(second.detail.length, 300);
  await appendLog({ env }, { action: 'order', login: null, detail: 'cx6 first' });
  await assert.rejects(appendLog({ env }, { action: 'Bad Action', login: 'cx5' }), { code: 'invalid-log' });
  await assert.rejects(appendLog({ env }, { action: 'set', login: 'Bad Name' }), { code: 'invalid-log' });
  assert.equal(await mode(logFile), 0o600);
  assert.equal(await mode(stateDir), 0o700);
  const text = await fs.readFile(logFile, 'utf8');
  assert.equal(text.split('\n').filter(Boolean).length, 3);
  assert.equal(text.includes('person@example.com') || text.includes(jwt), false);

  await fs.appendFile(logFile, 'not json\n[1]\n');
  assert.deepEqual((await readLog({ env })).map(row => row.action), ['import', 'set', 'order']);
  assert.deepEqual((await readLog({ env, name: 'cx5' })).map(row => row.detail), ['folder /synthetic/cx5']);
  assert.deepEqual((await readLog({ env, limit: 2 })).map(row => row.action), ['set', 'order']);
  assert.deepEqual(await readLog({ env: { HOME: freshHome() } }), []);
});

test('log lines from many appends at once do not mix', async () => {
  const env = { HOME: freshHome() };
  await Promise.all(Array.from({ length: 50 }, (_, index) => appendLog({ env }, { action: 'limit', login: `cx${index}`, detail: 'd'.repeat(250) })));
  const rows = await readLog({ env });
  assert.equal(rows.length, 50);
  assert.deepEqual(rows.map(row => row.login).sort(), Array.from({ length: 50 }, (_, index) => `cx${index}`).sort());
});
