import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, statSync, symlinkSync, writeFileSync, existsSync } from 'node:fs';
import * as fsp from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { codexLoginFacts, withAccessOnlyHome } from '../src/accounts-login.mjs';

// Fake logins only. Every secret below is made up for this test.
const b64 = value => Buffer.from(JSON.stringify(value)).toString('base64url');
const jwt = payload => `${b64({ alg: 'none', typ: 'JWT' })}.${b64(payload)}.fake-signature`;
const EXP = 1_800_000_000;
const FAKE = {
  access: jwt({ exp: EXP, 'https://api.openai.com/auth': { chatgpt_account_id: 'acct-fake-1111' } }),
  refresh: 'rt-fake-refresh-0000-secret',
  id: jwt({ email: 'fake.person@example.test', 'https://api.openai.com/auth': { chatgpt_account_id: 'acct-fake-1111' } }),
  account: 'acct-fake-1111',
  email: 'fake.person@example.test',
  apiKey: 'sk-fake-api-key-0000',
};
const login = (tokens = {}, extra = {}) => ({
  auth_mode: 'chatgpt', OPENAI_API_KEY: FAKE.apiKey,
  tokens: { id_token: FAKE.id, access_token: FAKE.access, refresh_token: FAKE.refresh, account_id: FAKE.account, ...tokens },
  last_refresh: '2026-11-10T12:00:00Z', ...extra,
});
const secrets = Object.values(FAKE);
const leaks = text => secrets.filter(secret => text.includes(secret));

function folder(t, prefix = 'pdd-login-') {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}
function home(t, content) {
  const dir = folder(t);
  if (content !== undefined) writeFileSync(join(dir, 'auth.json'), typeof content === 'string' ? content : JSON.stringify(content), { mode: 0o600 });
  return dir;
}

test('facts of a full login, an access-only copy and no login; never a token, id or email', async t => {
  const key = createHash('sha256').update(FAKE.account).digest('hex').slice(0, 16);
  const full = await codexLoginFacts(home(t, login()));
  assert.deepEqual(full, { state: 'full', accessExpiresAt: EXP * 1000, accountKey: key });
  assert.deepEqual(leaks(JSON.stringify(full)), []);
  assert.deepEqual(await codexLoginFacts(home(t, login({ refresh_token: '' }))), { state: 'access', accessExpiresAt: EXP * 1000, accountKey: key });
  assert.deepEqual(await codexLoginFacts(home(t)), { state: 'none', accessExpiresAt: null, accountKey: null });
  assert.deepEqual(await codexLoginFacts(join(home(t), 'missing-folder')), { state: 'none', accessExpiresAt: null, accountKey: null });
  assert.deepEqual(await codexLoginFacts(home(t, { OPENAI_API_KEY: FAKE.apiKey, tokens: null })), { state: 'none', accessExpiresAt: null, accountKey: null });
});

test('a broken, foreign or oversized login file is unreadable, never a throw', async t => {
  const unreadable = { state: 'unreadable', accessExpiresAt: null, accountKey: null };
  for (const content of ['{not json', '[]', 'null', JSON.stringify({ tokens: [] }),
    JSON.stringify(login({ access_token: '' })), JSON.stringify(login({ refresh_token: null })),
    JSON.stringify(login({}, { padding: 'x'.repeat(64 * 1024) }))])
    assert.deepEqual(await codexLoginFacts(home(t, content)), unreadable, content.slice(0, 40));
  const dir = home(t);
  mkdirSync(join(dir, 'auth.json'));
  assert.deepEqual(await codexLoginFacts(dir), unreadable);
  // Exactly 64 KiB is still read.
  const text = JSON.stringify(login());
  const exact = text.slice(0, -1) + ',"pad":"' + 'x'.repeat(64 * 1024 - text.length - 9) + '"}';
  assert.equal(Buffer.byteLength(exact), 64 * 1024);
  assert.equal((await codexLoginFacts(home(t, exact))).state, 'full');
});

test('access end and account key are null when the token or the id cannot give them', async t => {
  for (const access of ['opaque-token', jwt({ exp: '1800000000' }), jwt({ exp: -5 }), jwt({ exp: 9e12 }), jwt({})])
    assert.equal((await codexLoginFacts(home(t, login({ access_token: access })))).accessExpiresAt, null, access);
  assert.equal((await codexLoginFacts(home(t, login({ account_id: undefined })))).accountKey, null);
  assert.equal((await codexLoginFacts(home(t, login({ account_id: '' })))).accountKey, null);
});

test('a linked login file is followed; a relative or empty folder throws before any read', async t => {
  const target = home(t, login());
  const dir = home(t);
  symlinkSync(join(target, 'auth.json'), join(dir, 'auth.json'));
  assert.equal((await codexLoginFacts(dir)).state, 'full');
  let opened = 0;
  const ports = { fs: { open: async (...args) => { opened++; return fsp.open(...args); } } };
  for (const bad of ['relative/folder', '', null, undefined]) {
    await assert.rejects(codexLoginFacts(bad, ports), { name: 'TypeError', message: 'A login folder must be an absolute path.' });
    await assert.rejects(withAccessOnlyHome(bad, () => {}, ports), { name: 'TypeError' });
  }
  assert.equal(opened, 0);
});

test('the access-only home has no refresh token, only the needed fields, private modes, and is removed after success', async t => {
  const source = home(t, login({}, { unknown_secret: 'fake-other-secret' }));
  const before = readFileSync(join(source, 'auth.json'));
  const base = folder(t, 'pdd-login-base-');
  let seen;
  const value = await withAccessOnlyHome(source, (tempHome, facts) => {
    const names = readdirSync(tempHome).sort();
    const auth = JSON.parse(readFileSync(join(tempHome, 'auth.json'), 'utf8'));
    seen = { tempHome, facts, names, auth,
      config: readFileSync(join(tempHome, 'config.toml'), 'utf8'),
      modes: [statSync(tempHome).mode & 0o777, statSync(join(tempHome, 'auth.json')).mode & 0o777, statSync(join(tempHome, 'config.toml')).mode & 0o777],
      text: names.map(name => readFileSync(join(tempHome, name), 'utf8')).join('\n') };
    return 'fn-result';
  }, { tmpdir: base });
  assert.equal(value, 'fn-result');
  assert.equal(seen.tempHome.startsWith(join(base, 'pdd-codex-read-')), true);
  assert.deepEqual(seen.names, ['auth.json', 'config.toml']);
  assert.deepEqual(seen.modes, [0o700, 0o600, 0o600]);
  assert.equal(seen.config, 'cli_auth_credentials_store = "file"\n');
  assert.deepEqual(seen.auth, { auth_mode: 'chatgpt',
    tokens: { id_token: FAKE.id, access_token: FAKE.access, refresh_token: '', account_id: FAKE.account },
    last_refresh: '2026-11-10T12:00:00Z' });
  assert.equal(seen.text.includes(FAKE.refresh), false);
  assert.equal(seen.text.includes(FAKE.apiKey), false);
  assert.equal(seen.text.includes('fake-other-secret'), false);
  assert.deepEqual(seen.facts, await codexLoginFacts(source));
  assert.equal(existsSync(seen.tempHome), false);
  assert.deepEqual(readdirSync(base), []);
  assert.deepEqual(readFileSync(join(source, 'auth.json')), before, 'the login folder is never changed');
});

test('the access-only home is removed after a thrown or rejected callback, and the error passes through', async t => {
  const source = home(t, login());
  const base = folder(t, 'pdd-login-base-');
  for (const fn of [() => { throw new Error('sync failure'); }, async () => { throw new Error('async failure'); }]) {
    let tempHome;
    await assert.rejects(withAccessOnlyHome(source, temp => { tempHome = temp; return fn(); }, { tmpdir: base }), /failure/);
    assert.equal(existsSync(tempHome), false);
  }
  assert.deepEqual(readdirSync(base), []);
});

test('no usable login: no folder is made and the callback never runs', async t => {
  const base = folder(t, 'pdd-login-base-');
  let called = 0;
  for (const dir of [home(t), home(t, '{bad')])
    await assert.rejects(withAccessOnlyHome(dir, () => { called++; }, { tmpdir: base }),
      { code: 'PDD_NO_LOGIN', message: 'No readable Codex login in this folder.' });
  assert.equal(called, 0);
  assert.deepEqual(readdirSync(base), []);
});

test('a failed setup removes the folder; a failed removal wins and names the folder', async t => {
  const source = home(t, login());
  const base = folder(t, 'pdd-login-base-');
  let called = 0;
  await assert.rejects(withAccessOnlyHome(source, () => { called++; }, { tmpdir: base, fs: { writeFile: async () => { throw new Error('disk full'); } } }),
    { code: 'PDD_TEMP_HOME_FAILED', message: 'Could not make the temporary login folder.' });
  await assert.rejects(withAccessOnlyHome(source, () => { called++; }, { tmpdir: base, fs: { mkdtemp: async () => { throw new Error('no space'); } } }),
    { code: 'PDD_TEMP_HOME_FAILED' });
  assert.equal(called, 0);
  assert.deepEqual(readdirSync(base), []);
  let tempHome;
  const error = await withAccessOnlyHome(source, temp => { tempHome = temp; throw new Error('callback failure'); },
    { tmpdir: base, fs: { rm: async () => { throw new Error('busy'); } } }).catch(e => e);
  assert.equal(error.code, 'PDD_TEMP_HOME_LEFT');
  assert.equal(error.path, tempHome);
  assert.equal(error.message, `Could not remove the temporary login folder ${tempHome}.`);
  assert.deepEqual(leaks(error.message), []);
  rmSync(tempHome, { recursive: true, force: true });
});
