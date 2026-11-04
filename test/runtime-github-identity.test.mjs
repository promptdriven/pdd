import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, statSync, unlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { runCheck } from '../src/runtime-client.mjs';
import { listRuntimeJobs } from '../src/runtime-slots.mjs';
import { fakeRuntime, harbor, portsFor, TOKEN } from './runtime-fake.mjs';

const CALL = '1b3b9253-8488-4c3a-a138-168d97db262a';
const OTHER_TOKEN = 'gho_OTHER_synthetic_identity_token';
const digest = value => createHash('sha256').update(value).digest('hex');
const cachePath = setup => join(setup.state, 'github-identity.json');
const readCache = setup => JSON.parse(readFileSync(cachePath(setup), 'utf8'));
const denied = { status: 401, json: { error: { code: 'auth-invalid', message: 'Sign in again.' } } };
const limited = { status: 1, stderr: 'gh: API rate limit exceeded (HTTP 403)' };
const envFor = (setup, fake) => ({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
const receipt = (entry, f) => ({ status: 200, json: f.job(CALL, 'call', 'passed', { program_result: { stdout: 'saved\n', stderr: '', exit_code: 0 } }, 2) });

async function read(setup, fake, { token = TOKEN, user = 'octo 4242\n', extra = {} } = {}) {
  const calls = [];
  const { ports } = portsFor(envFor(setup, fake), { gh: args => {
    calls.push(args);
    return args[0] === 'auth' ? { status: 0, stdout: token } : typeof user === 'string' ? { status: 0, stdout: user } : user;
  }, ...extra });
  const code = await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true, '--json': true } }, ports);
  return { code, calls, out: ports.stdout.text, err: ports.stderr.text,
    lookups: calls.filter(args => args[0] === 'api' && args[1] === 'user').length };
}

test('2914: saved-batch reads reuse identity with no GitHub API call, while reading the token locally', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const first = portsFor(envFor(setup, fake));
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, first.ports), 0);
  const batch = JSON.parse(first.ports.stdout.text).batch;
  assert.equal(first.clock.gh.filter(args => args[0] === 'api').length, 1);
  const posts = fake.posts.length;
  for (let i = 0; i < 2; i++) {
    const next = portsFor(envFor(setup, fake), { gh: args => {
      assert.deepEqual(args, ['auth', 'token'], 'saved reads must not contact GitHub');
      return { status: 0, stdout: TOKEN };
    } });
    assert.equal(await runCheck({ cwd: setup.repo, options: { '--read': batch, '--json': true } }, next.ports), 0, next.ports.stderr.text);
  }
  assert.equal(fake.posts.length, posts, 'saved terminal reads send no new work');
});

test('2914: identity persists across Node processes with only login, ID, time and token SHA-256', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt), log = join(setup.sandbox, 'gh-calls.jsonl');
  const script = `
    import { appendFileSync } from 'node:fs';
    import { runCheck } from ${JSON.stringify(new URL('../src/runtime-client.mjs', import.meta.url).href)};
    const code = await runCheck({cwd: ${JSON.stringify(setup.repo)}, words: [${JSON.stringify(CALL)}], options: {'--read': true, '--json': true}}, {
      env: ${JSON.stringify(envFor(setup, fake))}, interactive: false,
      gh(args) { appendFileSync(${JSON.stringify(log)}, JSON.stringify(args)+'\\n'); return {status: 0, stdout: args[0] === 'auth' ? ${JSON.stringify(TOKEN)} : 'octo 4242'}; }
    });
    process.exitCode = code;
  `;
  for (let i = 0; i < 2; i++) await promisify(execFile)(process.execPath, ['--input-type=module', '-e', script]);
  const calls = readFileSync(log, 'utf8').trim().split('\n').map(line => JSON.parse(line));
  assert.equal(calls.filter(args => args[0] === 'auth').length, 2);
  assert.equal(calls.filter(args => args[0] === 'api').length, 1);
  const cached = readCache(setup);
  assert.deepEqual(Object.keys(cached).sort(), ['checked_at', 'login', 'token_sha256', 'user_id']);
  assert.equal(cached.login, 'octo'); assert.equal(cached.user_id, '4242');
  assert.equal(cached.token_sha256, digest(TOKEN)); assert.ok(Number.isFinite(Date.parse(cached.checked_at)));
  assert.equal(statSync(cachePath(setup)).mode & 0o777, 0o600);
  assert.ok(!readFileSync(cachePath(setup), 'utf8').includes(TOKEN));
});

test('2914: matching identity has no expiry and is shared across repositories on this machine', async t => {
  const setup = harbor(t), second = harbor(t), fake = await fakeRuntime(t, receipt);
  assert.equal((await read(setup, fake)).code, 0);
  const cached = readCache(setup); cached.checked_at = '2001-01-01T00:00:00Z';
  writeFileSync(cachePath(setup), JSON.stringify(cached));
  second.state = setup.state;
  const result = await read(second, fake, { user: limited });
  assert.equal(result.code, 0, result.err); assert.equal(result.lookups, 0);
});

test('2914: a changed token does one lookup, replaces identity, and preserves saved-batch owner checks', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const first = portsFor(envFor(setup, fake));
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, first.ports), 0);
  const batch = JSON.parse(first.ports.stdout.text).batch;
  const next = portsFor(envFor(setup, fake), { gh: args => ({ status: 0, stdout: args[0] === 'auth' ? OTHER_TOKEN : 'another 8080' }) });
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--read': batch } }, next.ports), 5);
  assert.match(next.ports.stderr.text, /These runs belong to octo/);
  const changed = readCache(setup);
  assert.equal(changed.login, 'another'); assert.equal(changed.user_id, '8080'); assert.equal(changed.token_sha256, digest(OTHER_TOKEN));
  const again = await read(setup, await fakeRuntime(t, receipt), { token: OTHER_TOKEN, user: limited });
  assert.equal(again.code, 0, again.err); assert.equal(again.lookups, 0);
});

test('2914: a rate-limited lookup never falls back to another token or an absent identity', async t => {
  for (const warm of [false, true]) {
    const setup = harbor(t), fake = await fakeRuntime(t, receipt);
    if (warm) assert.equal((await read(setup, fake)).code, 0);
    const before = fake.gets.length;
    const result = await read(setup, fake, { token: OTHER_TOKEN, user: limited });
    assert.equal(result.code, 5); assert.equal(result.lookups, 1); assert.equal(fake.gets.length, before);
    assert.match(result.err, /rate limit exceeded/);
  }
});

test('2914: HTTP 401 refreshes GitHub identity and retries the same read once', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt);
  assert.equal((await read(setup, fake)).code, 0);
  let attempts = 0;
  const retry = await fakeRuntime(t, (entry, f) => ++attempts === 1 ? denied : receipt(entry, f));
  const result = await read(setup, retry);
  assert.equal(result.code, 0, result.err); assert.equal(result.lookups, 1);
  assert.deepEqual(retry.gets.map(entry => entry.url), [`/v1/runs/${CALL}`, `/v1/runs/${CALL}`]);
  assert.equal(result.calls.filter(args => args[0] === 'auth').length, 1);
});

test('2914: a second HTTP 401 ends recovery and leaves no cached identity', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt);
  assert.equal((await read(setup, fake)).code, 0);
  const retry = await fakeRuntime(t, () => denied), result = await read(setup, retry);
  assert.equal(result.code, 3, result.err); assert.equal(result.lookups, 1); assert.equal(retry.gets.length, 2);
  assert.match(result.out + result.err, /Run gh auth login/);
  assert.equal(existsSync(cachePath(setup)), false);
  assert.equal((await read(setup, fake)).lookups, 1, 'a later command must look up identity again');
});

test('2914: rate limiting during fresh lookup uses the matching identity with a warning', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt);
  assert.equal((await read(setup, fake)).code, 0);
  let attempts = 0;
  const retry = await fakeRuntime(t, (entry, f) => ++attempts === 1 ? denied : receipt(entry, f));
  const result = await read(setup, retry, { user: limited });
  assert.equal(result.code, 0, result.err); assert.equal(result.lookups, 1); assert.equal(retry.gets.length, 2);
  assert.match(result.err, /Warning:.*GitHub.*rate limit.*cached/i);
  assert.ok(!(result.out + result.err + readFileSync(cachePath(setup), 'utf8')).includes(TOKEN));
});

test('2914: non-auth server errors neither refresh identity nor retry the request', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt);
  assert.equal((await read(setup, fake)).code, 0);
  for (const status of [403, 429, 500]) {
    const other = await fakeRuntime(t, () => ({ status, json: { error: { code: 'other', message: 'unavailable' } } }));
    const result = await read(setup, other);
    assert.equal(result.lookups, 0); assert.equal(other.gets.length, 1); assert.equal(readCache(setup).login, 'octo');
  }
});

test('2914: corrupt or unwritable identity cache still permits a successful lookup', async t => {
  for (const kind of ['corrupt', 'unwritable']) {
    const setup = harbor(t), fake = await fakeRuntime(t, receipt);
    mkdirSync(setup.state);
    if (kind === 'corrupt') writeFileSync(cachePath(setup), '{'); else mkdirSync(cachePath(setup));
    const result = await read(setup, fake);
    assert.equal(result.code, 0, result.err); assert.equal(result.lookups, 1);
  }
});

test('2914: cached identity never bypasses a missing local GitHub token', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt);
  assert.equal((await read(setup, fake)).code, 0);
  const before = fake.gets.length, result = await read(setup, fake, { token: '' });
  assert.equal(result.code, 5); assert.equal(result.lookups, 0); assert.equal(fake.gets.length, before);
  assert.match(result.err, /Run gh auth login/);
});

test('2914: parallel requests each retry their own initial HTTP 401 once', async t => {
  const setup = harbor(t), attempts = new Map();
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'check') {
      const id = entry.request.requestId, count = (attempts.get(id) ?? 0) + 1;
      attempts.set(id, count);
      if (count === 1) return denied;
    }
    return f.normal(entry);
  });
  const { ports } = portsFor(envFor(setup, fake));
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--json': true } }, ports), 0, ports.stderr.text + ports.stdout.text);
  assert.deepEqual([...attempts.values()], [2, 2]);
});

test('2914: hidden request reads retain support outside Git and reuse the external identity', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => ({ status: 200, json: f.check(CALL, 'passed') }));
  const calls = [];
  for (let i = 0; i < 2; i++) {
    const { ports, clock } = portsFor(envFor(setup, fake));
    assert.equal(await runCheck({ cwd: setup.sandbox, options: { '--request': CALL, '--json': true } }, ports), 0, ports.stderr.text);
    calls.push(...clock.gh);
  }
  assert.equal(calls.filter(args => args[0] === 'auth').length, 2);
  assert.equal(calls.filter(args => args[0] === 'api').length, 1);
  assert.equal(fake.gets.length, 2);
});

test('2914: hidden request reads retain in-repo state overrides without caching in the repo', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt);
  const state = join(setup.repo, 'runtime-state');
  const { ports, clock } = portsFor({ ...envFor(setup, fake), PDD_STATE_DIR: state });
  const checkFake = await fakeRuntime(t, (entry, f) => ({ status: 200, json: f.check(CALL, 'passed') }));
  ports.env.PDD_RUNTIME_URL = checkFake.origin;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--request': CALL } }, ports), 0, ports.stderr.text);
  assert.equal(clock.gh.length, 2); assert.equal(checkFake.gets.length, 1); assert.equal(existsSync(state), false);
});

for (const user of ['renamed 4242', 'octo 7777']) test(`2914 repair: refreshed owner ${user} cannot retry or rewrite a saved batch`, async t => {
  const setup = harbor(t); let reading = false;
  const fake = await fakeRuntime(t, (entry, f) => reading ? denied : f.normal(entry));
  const first = portsFor(envFor(setup, fake));
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, first.ports), 0);
  const batch = JSON.parse(first.ports.stdout.text).batch, folder = join(setup.state, 'batches', batch);
  const file = join(folder, 'batch.json'), before = readFileSync(file, 'utf8'), saved = JSON.parse(before);
  unlinkSync(join(folder, `${saved.rows[0].request_ids.at(-1)}.json`));
  reading = true;
  const next = portsFor(envFor(setup, fake), { gh: args => ({ status: 0, stdout: args[0] === 'auth' ? TOKEN : user }) });
  const gets = fake.gets.length;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--read': batch, '--json': true } }, next.ports), 5);
  assert.match(next.ports.stderr.text, /These runs belong to octo/);
  assert.equal(fake.gets.length - gets, 1, 'owner mismatch must stop before the retry');
  assert.equal(readFileSync(file, 'utf8'), before, 'saved owner and rows remain unchanged');
  assert.equal(existsSync(cachePath(setup)), false);
});

test('2914 repair: a revoked-token refresh follows normal 401 JSON, row and slot cleanup', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.command === 'check' ? denied : f.normal(entry));
  let lookups = 0, restored = false;
  const make = () => portsFor(envFor(setup, fake), { gh: args => args[0] === 'auth' ? { status: 0, stdout: TOKEN }
    : ++lookups === 1 || restored ? { status: 0, stdout: 'octo 4242' } : { status: 1, stderr: 'gh: Bad credentials (HTTP 401)' } }).ports;
  const ports = make();
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, ports), 5);
  const result = JSON.parse(ports.stdout.text), row = result.rows[0];
  assert.equal(row.state, 'not_run'); assert.match(row.reason.message, /Run gh auth login/);
  const saved = JSON.parse(readFileSync(join(setup.state, 'batches', result.batch, 'batch.json')));
  assert.equal(saved.rows[0].state, 'not_run'); assert.equal(existsSync(cachePath(setup)), false);
  assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.length, 0);
  assert.equal(fake.posts.filter(entry => entry.command === 'check').length, 1);
  assert.equal(fake.gets.length, 0);
  restored = true;
  const later = make();
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--read': result.batch, '--json': true } }, later), 5);
  assert.equal(fake.gets.length, 0, 'a later read cannot poll a run that was never created');
});
