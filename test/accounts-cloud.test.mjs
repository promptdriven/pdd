// Tests for src/accounts-cloud.mjs against the in-process fake login server. Fake gh tokens and fake logins only.
import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, existsSync, lstatSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { cloudCopy, cloudList, cloudUrl, runCloudAccounts, writeCopyHome, LOCAL_MODE_TEXT } from '../src/accounts-cloud.mjs';
import { fakeLogin, startFakeAccountsServer } from './helpers/fake-accounts-server.mjs';

const LOCAL = 'This needs the PDD login server. It is not set up on this machine.';
const AUTH_401 = 'The PDD login server did not accept your GitHub login (HTTP 401). Run gh auth login, then run the command again.';
// ali's token has no gh token shape, so only the exact-value redaction can hide it.
const AHMED = { token: 'gho_FAKEahmed00000000000000000000000001', login: 'ahmed', id: 101 };
const ALI = { token: 'fake-gh-token-ali-7f3a9c', login: 'ali', id: 102 };
const MEHTAB = { token: 'fake-gh-token-mehtab-51d0e2', login: 'mehtab', id: 103 };
const NOW = Date.parse('2026-11-11T22:58:00Z');
const EXP = Date.parse('2026-11-21T22:33:00Z') / 1000;
const TZ = 'America/Los_Angeles';
const mode = path => statSync(path).mode & 0o777;
const homesOf = home => join(home, '.local', 'state', 'pdd', 'accounts', 'homes');

const ghAs = (user, calls = []) => args => {
  calls.push(args.join(' '));
  if (args[0] === 'auth' && args[1] === 'token') return { status: 0, stdout: `${user.token}\n`, stderr: '' };
  if (args[0] === 'api' && args[1] === 'user') return { status: 0, stdout: `${user.login} ${user.id}\n`, stderr: '' };
  return { status: 1, stdout: '', stderr: 'unknown' };
};
function person(user, fake, extra = {}) {
  const home = mkdtempSync(join(process.env.HOME, `${user.login}-`)), calls = [];
  return { home, calls, input: { env: { HOME: home, PATH: '/usr/bin:/bin', PDD_ACCOUNTS_URL: fake?.url ?? 'https://pool.example' } },
    ports: { gh: ghAs(user, calls), timeZone: TZ, hostname: () => 'test-mac.local', ...extra } };
}
async function server(t, options = {}) {
  const fake = await startFakeAccountsServer({ users: [AHMED, ALI, MEHTAB], now: () => NOW, ...options });
  t.after(fake.close);
  return fake;
}
// No file under the folder holds any of the values.
function scan(dir, values) {
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const path = join(dir, entry.name);
    if (entry.isDirectory()) scan(path, values);
    else if (entry.isFile()) { const text = readFileSync(path, 'utf8'); for (const value of values) assert.ok(!text.includes(value), `${path} holds a secret`); }
  }
}

test('cloudUrl: the environment wins, then the pool file; only HTTPS or loopback HTTP passes', () => {
  assert.equal(cloudUrl({}, null), null);
  assert.equal(cloudUrl({}, undefined), null);
  assert.equal(cloudUrl({}, { version: 1, server: null }), null);
  assert.equal(cloudUrl({ PDD_ACCOUNTS_URL: '' }, { server: null }), null);
  assert.equal(cloudUrl({}, { server: { url: 'https://pool.example' } }), 'https://pool.example/');
  assert.equal(cloudUrl({ PDD_ACCOUNTS_URL: 'https://env.example/pool' }, { server: { url: 'https://pool.example' } }), 'https://env.example/pool/');
  assert.equal(cloudUrl({ PDD_ACCOUNTS_URL: 'http://127.0.0.1:9' }), 'http://127.0.0.1:9/');
  assert.equal(cloudUrl({ PDD_ACCOUNTS_URL: 'http://localhost:9/x/' }), 'http://localhost:9/x/');
  const envText = 'PDD_ACCOUNTS_URL must be an HTTPS address, for example https://accounts.example.';
  for (const bad of ['http://pool.example', 'https://u:p@pool.example', 'https://pool.example/?a=1', 'https://pool.example/?', 'https://pool.example/#x', 'ftp://pool.example', 'not a url', ' '])
    assert.throws(() => cloudUrl({ PDD_ACCOUNTS_URL: bad }, null), { message: envText, exitCode: 2 }, bad);
  const poolText = 'The server address in accounts.json must be an HTTPS address, for example https://accounts.example.';
  for (const server of [{ url: 'http://pool.example' }, {}, { url: 7 }, 'https://pool.example'])
    assert.throws(() => cloudUrl({}, { server }), { message: poolText, exitCode: 2 }, JSON.stringify(server));
});

test('local mode: every server action says so with exit 2, before gh, the names or the network', async () => {
  assert.equal(LOCAL_MODE_TEXT, LOCAL);
  const calls = [], home = mkdtempSync(join(process.env.HOME, 'local-'));
  const ports = { gh: args => { calls.push(args); return { status: 0, stdout: 'x' }; }, fetch: async () => { calls.push('fetch'); throw new Error('no'); } };
  for (const action of ['share', 'unshare', 'accept', 'leave', 'group-create', 'log', 'upload']) {
    assert.deepEqual(await runCloudAccounts(action, { env: { HOME: home }, pool: { version: 1, logins: [], server: null }, name: 'Not A Name' }, ports), { exitCode: 2, message: LOCAL }, action);
    assert.deepEqual(await runCloudAccounts(action, { env: { HOME: home }, name: 'x' }, { ...ports, readPool: () => ({ version: 1, server: null }) }), { exitCode: 2, message: LOCAL }, action);
  }
  // No pool given and no port: the store module (or no pool file in this fake home) means no server.
  assert.deepEqual(await runCloudAccounts('share', { env: { HOME: home }, name: 'x' }, ports), { exitCode: 2, message: LOCAL });
  assert.deepEqual(await cloudList({ env: { HOME: home }, pool: null }, ports), { ok: false, code: 'local', exitCode: 2, message: LOCAL });
  assert.deepEqual(await cloudCopy({ env: { HOME: home }, pool: null }, ports), { ok: false, code: 'local', exitCode: 2, message: LOCAL });
  assert.deepEqual(calls, []);
  // A pool file that the store can not read stops with its line; a bad pool address stops too.
  assert.deepEqual(await runCloudAccounts('share', { env: { HOME: home }, name: 'x' }, { ...ports, readPool: () => { throw new Error('accounts.json does not parse. pdd did not change it.'); } }),
    { exitCode: 2, message: 'accounts.json does not parse. pdd did not change it.' });
  assert.equal((await runCloudAccounts('share', { env: { HOME: home }, pool: { server: { url: 'http://x.example' } }, name: 'x' }, ports)).exitCode, 2);
  assert.deepEqual(calls, []);
});

test('share, accept and copy: an invite is not used before accept, own logins come first, the run home is access-only', async t => {
  const fake = await server(t);
  fake.addLogin({ owner: 'ahmed', name: 'shared-200', auth: fakeLogin({ refresh: 'rt-shared-200-secret', access: 'at-shared-200', exp: EXP }) });
  const aliOwn = fake.addLogin({ owner: 'ali', name: 'ali-own', auth: fakeLogin({ refresh: 'rt-ali-own-secret', exp: EXP }) });
  const ahmed = person(AHMED, fake), ali = person(ALI, fake);

  assert.deepEqual(await runCloudAccounts('share', { ...ahmed.input, name: 'shared-200', with: ['ali, Mehtab', 'ALI'] }, ahmed.ports),
    { exitCode: 0, message: 'Shared shared-200 with ali, Mehtab. Each person accepts it with: pdd accounts accept shared-200' });
  assert.deepEqual(fake.requests.at(-1).body, { with: ['ali', 'Mehtab'] });

  const before = await cloudList(ali.input, ali.ports);
  assert.equal(before.ok, true);
  assert.deepEqual(before.me, { login: 'ali', id: '102' });
  assert.deepEqual(before.logins.map(row => row.display), ['ali-own']);
  assert.deepEqual(before.inviteLines, ['ahmed shares shared-200 with you. Accept it with: pdd accounts accept shared-200']);
  const pending = await cloudCopy({ ...ali.input, skip: [aliOwn] }, ali.ports);
  assert.equal(pending.code, 'all_out');
  assert.equal(pending.exitCode, 1);
  assert.equal(fake.counts.copies, 0, 'the invite gave no copy');

  assert.deepEqual(await runCloudAccounts('accept', { ...ali.input, name: 'shared-200' }, ali.ports),
    { exitCode: 0, message: 'You accepted ahmed/shared-200. Your steps use it after your own logins.' });
  const after = await cloudList(ali.input, ali.ports);
  assert.deepEqual(after.logins.map(row => [row.display, row.kind, row.shared]), [['ali-own', 'cloud login', false], ['ahmed/shared-200', 'shared by ahmed', true]]);
  assert.deepEqual(after.order, ['ali-own', 'ahmed/shared-200']);
  assert.deepEqual(after.inviteLines, []);
  assert.equal(after.logins[1].accessExpiresAt, EXP * 1000);

  const first = await cloudCopy(ali.input, ali.ports);
  assert.equal(first.name, 'ali-own');
  assert.equal(first.home, join(homesOf(ali.home), 'ali-own'));
  const copy = await cloudCopy({ ...ali.input, skip: [aliOwn] }, ali.ports);
  assert.equal(copy.ok, true);
  assert.equal(copy.name, 'ahmed/shared-200');
  assert.equal(copy.home, join(homesOf(ali.home), '@ahmed', 'shared-200'));
  assert.equal(copy.expiresAt, EXP * 1000);
  assert.match(copy.copyId, /^c_/);
  assert.equal(Object.hasOwn(copy, 'auth'), false);
  assert.deepEqual(fake.requests.at(-1).body, { provider: 'codex', skip: [aliOwn] });
  const written = JSON.parse(readFileSync(join(copy.home, 'auth.json'), 'utf8'));
  assert.equal(written.tokens.refresh_token, '');
  assert.equal(JSON.parse(Buffer.from(written.tokens.access_token.split('.')[1], 'base64url')).sub, 'at-shared-200');
  assert.equal(readFileSync(join(copy.home, 'config.toml'), 'utf8'), 'cli_auth_credentials_store = "file"\n');
  assert.equal(mode(join(copy.home, 'auth.json')), 0o600);
  assert.equal(mode(join(copy.home, 'config.toml')), 0o600);
  for (const folder of [homesOf(ali.home), join(homesOf(ali.home), '@ahmed'), copy.home]) assert.equal(mode(folder), 0o700);
  assert.ok(existsSync(join(copy.home, '.pdd-copy-home')));
  assert.doesNotMatch(JSON.stringify([before, after, first, copy]), /rt-|at-shared-200|fake-gh-token/);
  scan(ali.home, [ALI.token, 'rt-shared-200-secret', 'rt-ali-own-secret']);

  // Each request names this machine; machine.json is made once (0600) and used again.
  const mine = fake.requests.filter(row => row.user === 'ali');
  const machine = JSON.parse(readFileSync(join(ali.home, '.config', 'pdd', 'machine.json'), 'utf8'));
  assert.match(machine.id, /^m_[0-9a-f]{16}$/);
  assert.equal(machine.name, 'test-mac');
  assert.equal(mode(join(ali.home, '.config', 'pdd', 'machine.json')), 0o600);
  assert.ok(mine.every(row => row.machine === machine.id && row.machineName === 'test-mac' && row.bearer && /^pdd\/\d/.test(row.userAgent)));
  assert.ok(mine.every(row => row.contentType === (row.body === undefined ? null : 'application/json')));
  // gh: one token read per call, and "who am I" once per token.
  assert.equal(ali.calls.filter(line => line.startsWith('api user')).length, 1);
});

test('leave and unshare: no new copies, and the owner hears until when an old copy works', async t => {
  const fake = await server(t);
  fake.addLogin({ owner: 'ahmed', name: 'shared-200', auth: fakeLogin({ refresh: 'rt-x', exp: EXP }) });
  const ahmed = person(AHMED, fake), ali = person(ALI, fake);
  await runCloudAccounts('share', { ...ahmed.input, name: 'shared-200', with: 'ali' }, ahmed.ports);
  await runCloudAccounts('accept', { ...ali.input, name: 'shared-200' }, ali.ports);
  assert.equal((await cloudCopy(ali.input, ali.ports)).name, 'ahmed/shared-200');
  assert.deepEqual(await runCloudAccounts('leave', { ...ali.input, name: 'ahmed/shared-200' }, ali.ports),
    { exitCode: 0, message: 'You left ahmed/shared-200. You get no new copies of it.' });
  assert.equal((await cloudCopy(ali.input, ali.ports)).code, 'all_out');
  assert.deepEqual(await runCloudAccounts('leave', { ...ali.input, name: 'shared-200' }, ali.ports),
    { exitCode: 1, message: 'You have no shared login named shared-200. Run pdd accounts list.' });

  await runCloudAccounts('share', { ...ahmed.input, name: 'shared-200', with: 'ali' }, ahmed.ports);
  await runCloudAccounts('accept', { ...ali.input, name: 'shared-200' }, ali.ports);
  assert.deepEqual(await runCloudAccounts('unshare', { ...ahmed.input, name: 'shared-200', with: 'ali' }, ahmed.ports),
    { exitCode: 0, message: 'ali gets no new copies of shared-200. A copy that is already on a machine works until its access ends (Nov 21 14:33 PST).' });
  const list = await cloudList(ali.input, ali.ports);
  assert.deepEqual([list.logins, list.invites], [[], []]);
  assert.deepEqual(await runCloudAccounts('unshare', { ...ahmed.input, name: 'shared-200' }, ahmed.ports),
    { exitCode: 2, message: 'Name the people to stop sharing with: --with USER,...' });
  // Only the owner shares: ali can not share ahmed's login.
  assert.deepEqual(await runCloudAccounts('share', { ...ali.input, name: 'ahmed/shared-200', with: 'mehtab' }, ali.ports),
    { exitCode: 1, message: 'You have no login named ahmed/shared-200 on the PDD login server. Run pdd accounts list.' });
});

test('groups: --github follows a GitHub team, --with names people, and each member accepts once', async t => {
  const fake = await server(t, { github: { 'promptdriven/eng': ['Mehtab'] } });
  fake.addLogin({ owner: 'ahmed', name: 'team-1', auth: fakeLogin({ refresh: 'rt-team', exp: EXP }) });
  const ahmed = person(AHMED, fake), ali = person(ALI, fake), mehtab = person(MEHTAB, fake);
  assert.deepEqual(await runCloudAccounts('group-create', { ...ahmed.input, name: 'eng', github: 'promptdriven/eng' }, ahmed.ports),
    { exitCode: 0, message: 'Made group eng. It follows GitHub team promptdriven/eng. Each member accepts it once.' });
  assert.deepEqual(fake.requests.at(-1).body, { name: 'eng', github: 'promptdriven/eng' });
  assert.deepEqual(await runCloudAccounts('share', { ...ahmed.input, name: 'team-1', group: 'eng' }, ahmed.ports),
    { exitCode: 0, message: 'Shared team-1 with group eng. Each member accepts it once.' });
  assert.deepEqual(fake.requests.at(-1).body, { with: [], group: 'eng' });
  assert.deepEqual((await cloudList(mehtab.input, mehtab.ports)).inviteLines, ['ahmed shares team-1 with you (group eng). Accept it with: pdd accounts accept team-1']);
  assert.deepEqual((await cloudList(ali.input, ali.ports)).inviteLines, [], 'ali is not in the team');
  assert.equal((await cloudCopy(mehtab.input, mehtab.ports)).code, 'all_out');
  assert.equal((await runCloudAccounts('accept', { ...mehtab.input, name: 'team-1' }, mehtab.ports)).exitCode, 0);
  const copy = await cloudCopy(mehtab.input, mehtab.ports);
  assert.equal(copy.name, 'ahmed/team-1');
  assert.equal(JSON.parse(readFileSync(join(copy.home, 'auth.json'), 'utf8')).tokens.refresh_token, '');

  assert.deepEqual(await runCloudAccounts('group-create', { ...ahmed.input, name: 'friends', with: 'ali,mehtab' }, ahmed.ports),
    { exitCode: 0, message: 'Made group friends with ali, mehtab. Each member accepts it once.' });
  assert.deepEqual(fake.requests.at(-1).body, { name: 'friends', with: ['ali', 'mehtab'] });
  assert.deepEqual(await runCloudAccounts('group-create', { ...ahmed.input, name: 'org', github: 'promptdriven' }, ahmed.ports),
    { exitCode: 0, message: 'Made group org. It follows GitHub org promptdriven. Each member accepts it once.' });
  const count = fake.requests.length;
  for (const input of [{ name: 'x', with: 'ali', github: 'promptdriven' }, { name: 'x' }])
    assert.deepEqual(await runCloudAccounts('group-create', { ...ahmed.input, ...input }, ahmed.ports), { exitCode: 2, message: 'Use one of --with USER,... or --github ORG[/TEAM].' });
  assert.deepEqual(await runCloudAccounts('group-create', { ...ahmed.input, name: 'x', github: 'promptdriven/e ng' }, ahmed.ports),
    { exitCode: 2, message: 'promptdriven/e ng is not a GitHub org or ORG/TEAM.' });
  assert.equal((await runCloudAccounts('group-create', { ...ahmed.input, name: 'Bad', with: 'ali' }, ahmed.ports)).exitCode, 2);
  assert.equal(fake.requests.length, count, 'bad input sends nothing');
  assert.deepEqual(await runCloudAccounts('group-create', { ...ahmed.input, name: 'friends', with: 'ali' }, ahmed.ports),
    { exitCode: 1, message: 'You already have a group named friends.' });
});

test('log: the owner sees the server audit table or JSON; others get no log', async t => {
  const fake = await server(t);
  fake.addLogin({ owner: 'ahmed', name: 'shared-200', auth: fakeLogin({ refresh: 'rt-log', exp: EXP }) });
  fake.addLogin({ owner: 'ahmed', name: 'quiet', auth: fakeLogin({ refresh: 'rt-quiet', exp: EXP }) });
  const ahmed = person(AHMED, fake), ali = person(ALI, fake);
  await runCloudAccounts('share', { ...ahmed.input, name: 'shared-200', with: 'ali' }, ahmed.ports);
  await runCloudAccounts('accept', { ...ali.input, name: 'shared-200' }, ali.ports);
  await cloudCopy(ali.input, ali.ports);
  assert.deepEqual(await runCloudAccounts('log', { ...ahmed.input, name: 'shared-200' }, ahmed.ports), { exitCode: 0, message: [
    'Server log for shared-200 (newest last). Times in PST.',
    '',
    'TIME          ACTION  LOGIN       BY     MACHINE   DETAIL',
    'Nov 11 14:58  share   shared-200  ahmed  test-mac  with ali',
    'Nov 11 14:58  accept  shared-200  ali    test-mac  -',
    'Nov 11 14:58  copy    shared-200  ali    test-mac  -'].join('\n') });
  const json = JSON.parse((await runCloudAccounts('log', { ...ahmed.input, name: 'shared-200', json: true }, ahmed.ports)).message);
  assert.deepEqual(json.rows.map(row => Object.keys(row)), Array(3).fill(['at', 'action', 'login', 'actor', 'machine', 'detail']));
  assert.deepEqual(json.rows.map(row => row.action), ['share', 'accept', 'copy']);
  assert.match((await runCloudAccounts('log', ahmed.input, ahmed.ports)).message, /^Server log for your logins \(newest last\)/);
  assert.deepEqual(await runCloudAccounts('log', { ...ahmed.input, name: 'quiet' }, ahmed.ports), { exitCode: 0, message: 'No server log rows for quiet.' });
  assert.deepEqual(await runCloudAccounts('log', { ...ali.input, name: 'shared-200' }, ali.ports),
    { exitCode: 1, message: 'You have no login named shared-200 on the PDD login server. Run pdd accounts list.' });
});

test('sign-in: no gh, no gh login, no GitHub user and a 401 each say what to run, with exit 5', async t => {
  const fake = await server(t);
  const stranger = { token: 'fake-gh-token-unknown-0001', login: 'stranger', id: 999 };
  const who = person(stranger, fake);
  assert.deepEqual(await runCloudAccounts('accept', { ...who.input, name: 'x' }, who.ports), { exitCode: 5, message: AUTH_401 });
  assert.deepEqual(await cloudCopy(who.input, who.ports), { ok: false, code: 'sign-in', exitCode: 5, message: AUTH_401 });
  const count = fake.requests.length;
  const gh = reply => args => (args[0] === 'auth' ? reply : { status: 1, stdout: '' });
  assert.deepEqual(await runCloudAccounts('accept', { ...who.input, name: 'x' }, { ...who.ports, gh: gh({ status: null, error: { code: 'ENOENT' } }) }),
    { exitCode: 5, message: 'Install the GitHub CLI, then run gh auth login.' });
  assert.deepEqual(await runCloudAccounts('accept', { ...who.input, name: 'x' }, { ...who.ports, gh: gh({ status: 1, stdout: '', stderr: 'not logged in' }) }),
    { exitCode: 5, message: 'Run gh auth login.' });
  assert.deepEqual(await runCloudAccounts('accept', { ...who.input, name: 'x' }, { ...who.ports, gh: gh({ status: 0, stdout: '  \n' }) }),
    { exitCode: 5, message: 'Run gh auth login.' });
  assert.deepEqual(await runCloudAccounts('share', { ...who.input, name: 'x', with: 'ali' }, { ...who.ports, gh: gh({ status: 0, stdout: 'fake-gh-token-x\n' }) }),
    { exitCode: 5, message: 'pdd could not read your GitHub login (gh api user). Run gh auth status.' });
  assert.equal(fake.requests.length, count, 'a sign-in problem sends nothing');
});

test('server errors: the message is the server line as safe text and never shows the gh token', async t => {
  const fake = await server(t);
  const ali = person(ALI, fake), outputs = [];
  const run = async () => { const out = await runCloudAccounts('accept', { ...ali.input, name: 'x' }, ali.ports); outputs.push(out); return out; };
  fake.failNext({ status: 500, body: { error: { code: 'unavailable', message: `boom ${ALI.token} Authorization: Bearer ${ALI.token}` } } });
  let out = await run();
  assert.equal(out.exitCode, 3);
  assert.match(out.message, /^boom \[secret\]/);
  fake.failNext({ status: 400, body: { error: { code: 'invalid', message: `bad\n\u001b[31m${ALI.token}\u0007 for x` } } });
  out = await run();
  assert.equal(out.exitCode, 1);
  assert.equal(out.message, 'bad [31m[secret] for x');
  fake.failNext({ status: 403, body: { error: { code: 'forbidden', message: `ghp_${'A'.repeat(36)} is not yours` } } });
  assert.deepEqual(await run(), { exitCode: 1, message: '[redacted] is not yours' });
  fake.failNext({ status: 418, raw: `teapot ${ALI.token}` });
  assert.deepEqual(await run(), { exitCode: 1, message: 'The PDD login server refused this (HTTP 418, no code).' });
  fake.failNext({ status: 503, raw: 'down' });
  assert.deepEqual(await run(), { exitCode: 3, message: 'The PDD login server is not available now (HTTP 503). Try again later.' });
  fake.failNext({ status: 200, raw: `not json ${ALI.token}` });
  assert.deepEqual(await run(), { exitCode: 3, message: 'The PDD login server sent a reply that pdd can not read (HTTP 200). Nothing was saved.' });
  fake.failNext({ status: 200, body: { logins: [{ id: '../x', name: 'x', owner: { login: 'ahmed' } }], invites: [], order: [], groups: [] } });
  assert.equal((await run()).exitCode, 3);
  fake.failNext({ status: 200, body: { logins: [], invites: [], order: [], groups: [], big: 'x'.repeat(1024 * 1024) } });
  assert.equal((await run()).exitCode, 3, 'a reply over 1 MiB is not read');
  assert.ok(outputs.every(row => !row.message.includes(ALI.token)), JSON.stringify(outputs));
  scan(ali.home, [ALI.token]);
});

test('copy desk: a copy that can renew itself is refused and nothing is saved; all out names the next free login', async t => {
  const fake = await server(t);
  const own = fake.addLogin({ owner: 'ali', name: 'ali-own', auth: fakeLogin({ refresh: 'rt-must-not-land', exp: EXP }) });
  const ali = person(ALI, fake);
  fake.options.copyWithRefresh = true;
  assert.deepEqual(await cloudCopy(ali.input, ali.ports), { ok: false, code: 'unsafe_copy', exitCode: 1,
    message: 'The login server sent a copy of ali-own that can renew itself. pdd did not save it. Tell the server owner.' });
  assert.equal(existsSync(join(homesOf(ali.home), 'ali-own', 'auth.json')), false);
  scan(ali.home, ['rt-must-not-land', ALI.token]);
  fake.options.copyWithRefresh = false;

  fake.setUsage(own, { limitedUntil: Date.parse('2026-11-12T00:48:00Z') });
  const out = await cloudCopy(ali.input, ali.ports);
  assert.deepEqual(out, { ok: false, code: 'all_out', exitCode: 1, message: 'No login on the PDD login server has quota now. Next free: ali-own at Nov 11 16:48 PST.',
    earliest: { id: own, name: 'ali-own', at: Date.parse('2026-11-12T00:48:00Z') } });
  fake.failNext({ status: 409, body: { error: { code: 'all_out', message: 'none' }, earliest: { id: 'l_gone', at: '2026-11-12T00:48:00Z' } } });
  assert.deepEqual((await cloudCopy(ali.input, ali.ports)).earliest, { id: 'l_gone', name: null, at: Date.parse('2026-11-12T00:48:00Z') });
  fake.failNext({ status: 200, body: { login: { id: own, name: 'ali-own', owner: { login: 'ali', id: 102 } }, auth: 7 } });
  assert.equal((await cloudCopy(ali.input, ali.ports)).code, 'bad_reply');
  assert.deepEqual(await cloudCopy({ ...ali.input, provider: 'claude' }, ali.ports), { ok: false, code: 'input', exitCode: 2,
    message: 'Claude logins stay on this machine. The PDD login server does not hold them.' });
  assert.equal((await cloudCopy({ ...ali.input, skip: ['../x'] }, ali.ports)).exitCode, 2);
  assert.equal((await cloudCopy({ ...ali.input, pin: 'a b' }, ali.ports)).exitCode, 2);
  fake.setUsage(own, { limitedUntil: null });
  assert.equal((await cloudCopy({ ...ali.input, pin: own }, ali.ports)).name, 'ali-own');
  assert.deepEqual(fake.requests.at(-1).body, { provider: 'codex', pin: own });
});

test('writeCopyHome: checks the copy first, writes only into its own folders, never through a link', () => {
  const home = mkdtempSync(join(process.env.HOME, 'homes-')), env = { HOME: home }, homes = homesOf(home);
  const copy = (refresh = '', extra = {}) => JSON.stringify({ tokens: { id_token: 'i', access_token: 'fake-access', refresh_token: refresh, account_id: 'a' }, ...extra });
  const bad = { ok: false, code: 'bad_copy', exitCode: 1, message: 'The login server sent a copy of cx5 that pdd can not read. pdd did not save it.' };
  for (const auth of [undefined, 'not json', '[]', '{}', '{"tokens":{"access_token":"","refresh_token":""}}', '{"tokens":{"access_token":"a"}}',
    '{"tokens":{"access_token":"a","refresh_token":null}}', copy('', { pad: 'x'.repeat(64 * 1024) })])
    assert.deepEqual(writeCopyHome({ env, name: 'cx5', auth }), bad, String(auth).slice(0, 60));
  const unsafe = { ok: false, code: 'unsafe_copy', exitCode: 1, message: 'The login server sent a copy of cx5 that can renew itself. pdd did not save it. Tell the server owner.' };
  assert.deepEqual(writeCopyHome({ env, name: 'cx5', auth: copy('rt-live') }), unsafe);
  assert.deepEqual(writeCopyHome({ env, name: 'cx5', auth: copy('', { spare: [{ refresh_token: 'rt-hidden' }] }) }), unsafe);
  assert.deepEqual(writeCopyHome({ env, name: 'cx5', auth: copy({ value: 'x' }) }), unsafe);
  assert.equal(existsSync(homes), false, 'a refused copy touches no file');
  for (const name of ['../x', 'Cx5', 'a/b/c', '', '@x/cx5', 'ahmed/../x'])
    assert.equal(writeCopyHome({ env, name, auth: copy() }).code, 'input', name);

  // A duplicate key can not hide a refresh token: pdd writes the parsed object.
  const sneaky = '{"tokens":{"access_token":"fake-access","refresh_token":"rt-dup-hidden","refresh_token":""}}';
  const done = writeCopyHome({ env, name: 'cx5', auth: sneaky });
  assert.deepEqual(done, { ok: true, home: join(homes, 'cx5') });
  assert.doesNotMatch(readFileSync(join(done.home, 'auth.json'), 'utf8'), /rt-dup-hidden/);
  assert.equal(mode(join(done.home, 'auth.json')), 0o600);
  // Codex's own config lines stay when the file store line is there; another store is replaced.
  writeFileSync(join(done.home, 'config.toml'), 'cli_auth_credentials_store = "file"\n\n[projects."/x"]\ntrust_level = "trusted"\n');
  assert.equal(writeCopyHome({ env, name: 'cx5', auth: copy() }).ok, true);
  assert.match(readFileSync(join(done.home, 'config.toml'), 'utf8'), /trust_level/);
  writeFileSync(join(done.home, 'config.toml'), 'cli_auth_credentials_store = "keyring"\n');
  assert.equal(writeCopyHome({ env, name: 'cx5', auth: copy() }).ok, true);
  assert.equal(readFileSync(join(done.home, 'config.toml'), 'utf8'), 'cli_auth_credentials_store = "file"\n');
  assert.deepEqual(readdirSync(done.home).sort(), ['.pdd-copy-home', 'auth.json', 'config.toml'], 'no temp file stays');

  // A link named auth.json is replaced, never followed.
  const outside = join(home, 'outside-auth.json');
  writeFileSync(outside, 'keep me');
  const linked = join(homes, 'cx6');
  mkdirSync(linked, { mode: 0o700 });
  writeFileSync(join(linked, '.pdd-copy-home'), 'pdd copy home v1\n');
  symlinkSync(outside, join(linked, 'auth.json'));
  assert.equal(writeCopyHome({ env, name: 'cx6', auth: copy() }).ok, true);
  assert.equal(readFileSync(outside, 'utf8'), 'keep me');
  assert.equal(lstatSync(join(linked, 'auth.json')).isSymbolicLink(), false);

  // A folder that pdd did not make, or a linked folder, gets nothing.
  const foreign = join(homes, 'cx7');
  mkdirSync(foreign);
  writeFileSync(join(foreign, 'auth.json'), 'a person put this here');
  assert.deepEqual(writeCopyHome({ env, name: 'cx7', auth: copy() }), { ok: false, code: 'not_copy_home', exitCode: 1,
    message: '~/.local/state/pdd/accounts/homes/cx7 is not a folder that pdd made for copies. pdd did not write there.' });
  assert.equal(readFileSync(join(foreign, 'auth.json'), 'utf8'), 'a person put this here');
  const target = mkdtempSync(join(home, 'target-'));
  symlinkSync(target, join(homes, 'cx8'));
  assert.equal(writeCopyHome({ env, name: 'cx8', auth: copy() }).code, 'not_copy_home');
  assert.deepEqual(readdirSync(target), []);
  // An empty folder is taken; a shared name goes under @owner in lower case.
  mkdirSync(join(homes, 'cx9'));
  assert.equal(writeCopyHome({ env, name: 'cx9', auth: copy() }).ok, true);
  assert.deepEqual(writeCopyHome({ env, name: 'Ahmed/shared-200', auth: copy() }), { ok: true, home: join(homes, '@ahmed', 'shared-200') });
  // pdd sets its own folder back to 0700 before it writes.
  chmodSync(join(homes, 'cx9'), 0o755);
  assert.equal(writeCopyHome({ env, name: 'cx9', auth: copy() }).ok, true);
  assert.equal(mode(join(homes, 'cx9')), 0o700);
  // A file error is one line with its code, and no temp file stays.
  const broken = join(homes, 'cx10');
  mkdirSync(broken);
  writeFileSync(join(broken, '.pdd-copy-home'), 'pdd copy home v1\n');
  mkdirSync(join(broken, 'auth.json'));
  const failed = writeCopyHome({ env, name: 'cx10', auth: copy() });
  assert.equal(failed.code, 'home_error');
  assert.match(failed.message, /^pdd could not write the copy of cx10 \([A-Z]+\)\.$/);
  assert.deepEqual(readdirSync(broken).sort(), ['.pdd-copy-home', 'auth.json', 'config.toml']);
});

test('network: no redirect is followed, a lost connection and a timeout are one line with exit 3', async () => {
  const ali = person(ALI, null), seen = [];
  const run = fetch => runCloudAccounts('accept', { ...ali.input, name: 'x' }, { ...ali.ports, fetch, timeoutMs: 50 });
  assert.deepEqual(await run(async (url, init) => { seen.push([String(url), init.redirect, init.headers.Authorization === `Bearer ${ALI.token}`]);
    return new Response(null, { status: 302, headers: { location: 'https://elsewhere.example/' } }); }),
  { exitCode: 3, message: 'The PDD login server at pool.example sent a redirect. pdd does not follow it with your GitHub login. Check PDD_ACCOUNTS_URL.' });
  assert.deepEqual(seen, [['https://pool.example/v1/accounts', 'manual', true]]);
  assert.deepEqual(await run(async () => { throw new TypeError('fetch failed', { cause: { code: 'ECONNREFUSED' } }); }),
    { exitCode: 3, message: 'pdd could not reach the PDD login server at pool.example (the connection was refused). Check your network and PDD_ACCOUNTS_URL.' });
  assert.deepEqual(await run((url, init) => new Promise((_, reject) => init.signal.addEventListener('abort', () => reject(Object.assign(new Error('aborted'), { name: 'AbortError' }))))),
    { exitCode: 3, message: 'pdd could not reach the PDD login server at pool.example (no answer in time). Check your network and PDD_ACCOUNTS_URL.' });
});

test('the default gh is the first gh on PATH that is not a PDD Try launcher; requests go below a base path', async t => {
  const fake = await server(t);
  fake.addUser({ token: 'fake-gh-token-path-0001', login: 'ahmed', id: 101 });
  fake.addLogin({ owner: 'ahmed', name: 'cx5', auth: fakeLogin({ refresh: 'rt-path', exp: EXP }) });
  const home = mkdtempSync(join(process.env.HOME, 'path-')), launcher = join(home, 'launcher'), bin = join(home, 'bin'), empty = join(home, 'empty');
  for (const dir of [launcher, bin, empty]) mkdirSync(dir);
  writeFileSync(join(launcher, 'gh'), '#!/bin/sh\n# PDD Try launcher v1\necho wrong-token\n', { mode: 0o755 });
  writeFileSync(join(bin, 'gh'), '#!/bin/sh\nif [ "$1" = auth ]; then echo fake-gh-token-path-0001; exit 0; fi\nif [ "$1" = api ]; then echo "ahmed 101"; exit 0; fi\nexit 1\n', { mode: 0o755 });
  const env = { HOME: home, PATH: `${launcher}:${bin}:/usr/bin:/bin`, PDD_ACCOUNTS_URL: `${fake.url}pool` };
  assert.deepEqual(await runCloudAccounts('share', { env, name: 'cx5', with: 'ali' }, { timeZone: TZ }),
    { exitCode: 0, message: 'Shared cx5 with ali. Each person accepts it with: pdd accounts accept cx5' });
  assert.ok(fake.requests.slice(-2).every(row => row.prefix === '/pool' && row.user === 'ahmed'));
  assert.deepEqual(await runCloudAccounts('share', { env: { ...env, PATH: empty }, name: 'cx5', with: 'ali' }, {}),
    { exitCode: 5, message: 'Install the GitHub CLI, then run gh auth login.' });
});

test('input: bad names, bad user lists and unknown actions stop with exit 2 and send nothing', async t => {
  const fake = await server(t);
  const ali = person(ALI, fake);
  const cases = [
    ['share', { name: 'Bad Name', with: 'x' }, 'Bad Name is not a login name. Use lower-case letters, digits, dots, dashes or underscores (at most 32), or OWNER/NAME.'],
    ['share', { name: 'cx5', with: 'ok,not a user!' }, 'not a user! is not a GitHub user name.'],
    ['share', { name: 'cx5', with: ' , ' }, 'Name the people to share with: --with USER,...'],
    ['share', { name: 'cx5', with: [7] }, 'The --with list must name GitHub users.'],
    ['share', { name: 'cx5', group: 'Bad' }, 'Bad is not a group name.'],
    ['accept', { name: 'a/b/c' }, 'a/b/c is not a login name. Use lower-case letters, digits, dots, dashes or underscores (at most 32), or OWNER/NAME.'],
    ['log', { name: '../x' }, '../x is not a login name. Use lower-case letters, digits, dots, dashes or underscores (at most 32), or OWNER/NAME.'],
    ['upload', { name: 'cx5', provider: 'codex', home: '/x' }, 'pdd accounts upload is not ready yet. Use --local.'],
    ['remove', { name: 'cx5' }, 'Unknown pdd accounts server action: remove.'],
  ];
  for (const [action, input, message] of cases) assert.deepEqual(await runCloudAccounts(action, { ...ali.input, ...input }, ali.ports), { exitCode: 2, message }, action);
  assert.deepEqual(fake.requests, []);
  assert.deepEqual(ali.calls, []);
});

test('accept: two invites with one name need OWNER/NAME; a bad machine.json is never overwritten', async t => {
  const fake = await server(t);
  fake.addLogin({ owner: 'ahmed', name: 'shared', auth: fakeLogin({ refresh: 'rt-a', exp: EXP }) });
  fake.addLogin({ owner: 'mehtab', name: 'shared', auth: fakeLogin({ refresh: 'rt-m', exp: EXP }) });
  const ahmed = person(AHMED, fake), mehtab = person(MEHTAB, fake), ali = person(ALI, fake);
  await runCloudAccounts('share', { ...ahmed.input, name: 'shared', with: 'ali' }, ahmed.ports);
  await runCloudAccounts('share', { ...mehtab.input, name: 'shared', with: 'ali' }, mehtab.ports);
  mkdirSync(join(ali.home, '.config', 'pdd'), { recursive: true });
  writeFileSync(join(ali.home, '.config', 'pdd', 'machine.json'), '{bad');
  assert.deepEqual((await cloudList(ali.input, ali.ports)).inviteLines, [
    'ahmed shares shared with you. Accept it with: pdd accounts accept ahmed/shared',
    'mehtab shares shared with you. Accept it with: pdd accounts accept mehtab/shared']);
  assert.deepEqual(await runCloudAccounts('accept', { ...ali.input, name: 'shared' }, ali.ports),
    { exitCode: 2, message: 'Two people share a login named shared with you. Use OWNER/NAME: ahmed/shared, mehtab/shared.' });
  assert.deepEqual(await runCloudAccounts('accept', { ...ali.input, name: 'mehtab/shared' }, ali.ports),
    { exitCode: 0, message: 'You accepted mehtab/shared. Your steps use it after your own logins.' });
  assert.deepEqual(await runCloudAccounts('accept', { ...ali.input, name: 'nobody' }, ali.ports), { exitCode: 1, message: 'No invite for nobody. Run pdd accounts list.' });
  assert.equal(readFileSync(join(ali.home, '.config', 'pdd', 'machine.json'), 'utf8'), '{bad');
  assert.ok(fake.requests.filter(row => row.user === 'ali').every(row => /^m_[0-9a-f]{16}$/.test(row.machine)));
});
