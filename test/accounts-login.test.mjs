import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, statSync, symlinkSync, writeFileSync, existsSync } from 'node:fs';
import * as fsp from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { codexLoginFacts, makeAccessOnly, readLoginForUpload, withAccessOnlyHome } from '../src/accounts-login.mjs';

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
  const started = Date.now();
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
  const { last_refresh: copiedAt, ...auth } = seen.auth;
  assert.deepEqual(auth, { auth_mode: 'chatgpt',
    tokens: { id_token: FAKE.id, access_token: FAKE.access, refresh_token: '', account_id: FAKE.account } });
  assert.equal(new Date(copiedAt).toISOString(), copiedAt, 'last_refresh is an ISO time');
  assert.ok(Date.parse(copiedAt) >= started && Date.parse(copiedAt) <= Date.now(), 'last_refresh is the time of the copy, not the source time');
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
  for (const [dir, state] of [[home(t), 'none'], [home(t, '{bad'), 'unreadable']])
    await assert.rejects(withAccessOnlyHome(dir, () => { called++; }, { tmpdir: base }),
      { code: 'PDD_NO_LOGIN', state, message: 'No readable Codex login in this folder.' });
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

test('a named pipe in place of the login file is unreadable at once, not a hang', { skip: process.platform === 'win32' }, async t => {
  const dir = home(t);
  execFileSync('mkfifo', [join(dir, 'auth.json')]);
  let timer;
  const result = await Promise.race([codexLoginFacts(dir), new Promise(resolve => { timer = setTimeout(() => resolve('hang'), 2_000); })]);
  clearTimeout(timer);
  assert.deepEqual(result, { state: 'unreadable', accessExpiresAt: null, accountKey: null });
});

const keyOf = text => createHash('sha256').update(text).digest('hex').slice(0, 16);
const AUTH = 'https://api.openai.com/auth';

test('Team members who share one account id get two keys; the user id follows the server claim order', async t => {
  const user = (claims, account = FAKE.account) => login({ account_id: account, id_token: jwt(claims) });
  const keyFor = async content => (await codexLoginFacts(home(t, content))).accountKey;
  const first = await keyFor(user({ [AUTH]: { chatgpt_user_id: 'user-fake-aaaa' } }));
  const second = await keyFor(user({ [AUTH]: { chatgpt_user_id: 'user-fake-bbbb' } }));
  assert.notEqual(first, second);
  assert.equal(first, keyOf(`${FAKE.account}\nuser-fake-aaaa`));
  assert.equal(await keyFor(user({ [AUTH]: { chatgpt_user_id: 'user-fake-aaaa', user_id: 'other' }, sub: 'sub-x' })), first, 'chatgpt_user_id wins');
  assert.equal(await keyFor(user({ [AUTH]: { chatgpt_user_id: '  ', user_id: 'user-fake-cccc' }, sub: 'sub-x' })), keyOf(`${FAKE.account}\nuser-fake-cccc`), 'then user_id');
  assert.equal(await keyFor(user({ [AUTH]: { chatgpt_user_id: 7 }, sub: ' sub-fake-dddd ' })), keyOf(`${FAKE.account}\nsub-fake-dddd`), 'then sub, trimmed');
  assert.equal(await keyFor(user({ [AUTH]: {} }, `  ${FAKE.account} `)), keyOf(FAKE.account), 'no user id: account id alone');
  assert.equal(await keyFor(login({ id_token: 'not-a-jwt' })), keyOf(FAKE.account));
  assert.equal(await keyFor(login({ id_token: undefined })), keyOf(FAKE.account));
  assert.equal(await keyFor(login({ account_id: '   ' })), null);
});

test('the upload read gives the exact login text, its hash and facts; no login is refused', async t => {
  const content = JSON.stringify(login(), null, 2) + '\n';
  const dir = home(t, content);
  const upload = await readLoginForUpload(dir);
  assert.deepEqual(Object.keys(upload).sort(), ['facts', 'sha256', 'text']);
  assert.equal(upload.text, content);
  assert.equal(upload.sha256, createHash('sha256').update(content).digest('hex'));
  assert.deepEqual(upload.facts, await codexLoginFacts(dir));
  for (const [dir2, state] of [[home(t), 'none'], [home(t, '{bad'), 'unreadable']])
    await assert.rejects(readLoginForUpload(dir2), { code: 'PDD_NO_LOGIN', state });
  await assert.rejects(readLoginForUpload('relative'), { name: 'TypeError' });
});

test('make access-only rewrites the file in place with an empty refresh token and keeps every other field', async t => {
  const original = login({}, { unknown_field: 'kept' });
  const dir = home(t, JSON.stringify(original));
  const { sha256 } = await readLoginForUpload(dir);
  assert.deepEqual(await makeAccessOnly(dir, sha256), { changed: true, reason: 'rewritten' });
  const after = JSON.parse(readFileSync(join(dir, 'auth.json'), 'utf8'));
  assert.deepEqual(after, { ...original, tokens: { ...original.tokens, refresh_token: '' } });
  assert.equal(statSync(join(dir, 'auth.json')).mode & 0o777, 0o600);
  assert.deepEqual(readdirSync(dir), ['auth.json'], 'no temporary file is left');
  assert.equal((await codexLoginFacts(dir)).state, 'access');
  const again = await readLoginForUpload(dir);
  assert.deepEqual(await makeAccessOnly(dir, again.sha256), { changed: false, reason: 'already-access' });
});

test('make access-only leaves the file alone when its bytes changed, it is a link, or there is no login', async t => {
  const dir = home(t, login());
  const { sha256 } = await readLoginForUpload(dir);
  const renewed = JSON.stringify(login({ refresh_token: 'rt-fake-renewed' }));
  writeFileSync(join(dir, 'auth.json'), renewed);
  assert.deepEqual(await makeAccessOnly(dir, sha256), { changed: false, reason: 'bytes-changed' });
  assert.equal(readFileSync(join(dir, 'auth.json'), 'utf8'), renewed);
  const target = home(t, login());
  const linked = home(t);
  symlinkSync(join(target, 'auth.json'), join(linked, 'auth.json'));
  const before = readFileSync(join(target, 'auth.json'), 'utf8');
  assert.deepEqual(await makeAccessOnly(linked, (await readLoginForUpload(linked)).sha256), { changed: false, reason: 'link' });
  assert.equal(readFileSync(join(target, 'auth.json'), 'utf8'), before);
  assert.deepEqual(await makeAccessOnly(home(t), sha256), { changed: false, reason: 'no-login' });
  let opened = 0;
  const ports = { fs: { open: async (...args) => { opened++; return fsp.open(...args); }, lstat: async (...args) => { opened++; return fsp.lstat(...args); } } };
  for (const bad of ['', 'ABC', sha256.toUpperCase(), null])
    await assert.rejects(makeAccessOnly(dir, bad, ports), { name: 'TypeError', message: 'expectedSha256 must be a SHA-256 hex digest.' });
  assert.equal(opened, 0);
});

test('a renewal between the check and the rename wins; a failed write leaves the file and no temporary file', async t => {
  const dir = home(t, login());
  const file = join(dir, 'auth.json');
  const { sha256 } = await readLoginForUpload(dir);
  const renewed = JSON.stringify(login({ refresh_token: 'rt-fake-renewed' }));
  let reads = 0;
  const open = async (path, flags, mode) => {
    if (path === file && ++reads === 2) writeFileSync(file, renewed);
    return fsp.open(path, flags, mode);
  };
  assert.deepEqual(await makeAccessOnly(dir, sha256, { fs: { open } }), { changed: false, reason: 'bytes-changed' });
  assert.equal(readFileSync(file, 'utf8'), renewed);
  assert.deepEqual(readdirSync(dir), ['auth.json']);
  const current = (await readLoginForUpload(dir)).sha256;
  for (const fs of [{ rename: async () => { throw new Error('disk'); } }, { open: async (path, flags, mode) => {
    if (flags === 'wx') throw new Error('disk'); return fsp.open(path, flags, mode);
  } }]) {
    await assert.rejects(makeAccessOnly(dir, current, { fs }), { code: 'PDD_ACCESS_ONLY_FAILED', message: 'Could not make the login file access-only.' });
    assert.equal(readFileSync(file, 'utf8'), renewed);
    assert.deepEqual(readdirSync(dir), ['auth.json']);
  }
});
