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

async function invoke(setup, fake, { token = TOKEN, user = 'octo 4242\n', extra = {} } = {}, sending = false) {
  const calls = [];
  const { ports } = portsFor(envFor(setup, fake), { gh: args => {
    calls.push(args);
    return args[0] === 'auth' ? { status: 0, stdout: token } : typeof user === 'string' ? { status: 0, stdout: user } : user;
  }, ...extra });
  const code = await runCheck({ cwd: setup.repo, words: sending ? ['place-order'] : [CALL], options: { ...(!sending ? { '--read': true } : {}), '--json': true } }, ports);
  return { code, calls, out: ports.stdout.text, err: ports.stderr.text,
    lookups: calls.filter(args => args[0] === 'api' && args[1] === 'user').length };
}
const read = (setup, fake, options) => invoke(setup, fake, options);
const send = (setup, fake, options) => invoke(setup, fake, options, true);

test('2914: saved-batch reads look up the current owner even with a matching-token cache', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const first = portsFor(envFor(setup, fake));
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, first.ports), 0);
  const batch = JSON.parse(first.ports.stdout.text).batch;
  assert.equal(first.clock.gh.filter(args => args[0] === 'api').length, 1);
  const posts = fake.posts.length;
  for (let i = 0; i < 2; i++) {
    const next = portsFor(envFor(setup, fake));
    assert.equal(await runCheck({ cwd: setup.repo, options: { '--read': batch, '--json': true } }, next.ports), 0, next.ports.stderr.text);
    assert.equal(next.clock.gh.filter(args => args[0] === 'api').length, 1);
  }
  assert.equal(fake.posts.length, posts, 'saved terminal reads send no new work');
});

test('2914: identity persists across Node processes with only login, ID, time and token SHA-256', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry)), log = join(setup.sandbox, 'gh-calls.jsonl');
  const script = `
    import { appendFileSync } from 'node:fs';
    import { runCheck } from ${JSON.stringify(new URL('../src/runtime-client.mjs', import.meta.url).href)};
    const code = await runCheck({cwd: ${JSON.stringify(setup.repo)}, words: ['place-order'], options: {'--json': true}}, {
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

test('2914: plain sends share matching identity across repositories without an expiry', async t => {
  const setup = harbor(t), second = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  assert.equal((await send(setup, fake)).code, 0);
  const cached = readCache(setup); cached.checked_at = '2001-01-01T00:00:00Z';
  writeFileSync(cachePath(setup), JSON.stringify(cached));
  second.state = setup.state;
  const result = await send(second, fake, { user: limited });
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
  assert.equal(again.code, 5, again.err); assert.equal(again.lookups, 1);
  assert.match(again.err, /Wait for the GitHub rate limit to reset/);
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
  assert.equal(result.code, 0, result.err); assert.equal(result.lookups, 2);
  assert.deepEqual(retry.gets.map(entry => entry.url), [`/v1/runs/${CALL}`, `/v1/runs/${CALL}`]);
  assert.equal(result.calls.filter(args => args[0] === 'auth').length, 1);
});

test('2914: a second HTTP 401 ends recovery and leaves no cached identity', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt);
  assert.equal((await read(setup, fake)).code, 0);
  const retry = await fakeRuntime(t, () => denied), result = await read(setup, retry);
  assert.equal(result.code, 3, result.err); assert.equal(result.lookups, 2); assert.equal(retry.gets.length, 2);
  assert.match(result.out + result.err, /Run gh auth login/);
  assert.equal(existsSync(cachePath(setup)), false);
  assert.equal((await read(setup, fake)).lookups, 1, 'a later command must look up identity again');
});

test('2914: a rate-limited owner lookup never trusts a matching cache without a reported reset', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt);
  assert.equal((await read(setup, fake)).code, 0);
  const gets = fake.gets.length, result = await read(setup, fake, { user: limited });
  assert.equal(result.code, 5); assert.equal(result.lookups, 1); assert.equal(fake.gets.length, gets);
  assert.match(result.err, /Wait for the GitHub rate limit to reset/);
  assert.ok(!(result.out + result.err + readFileSync(cachePath(setup), 'utf8')).includes(TOKEN));
});

test('2914: non-auth server errors neither refresh identity nor retry the request', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt);
  assert.equal((await read(setup, fake)).code, 0);
  for (const status of [403, 429, 500]) {
    const other = await fakeRuntime(t, () => ({ status, json: { error: { code: 'other', message: 'unavailable' } } }));
    const result = await read(setup, other);
    assert.equal(result.lookups, 1); assert.equal(other.gets.length, 1); assert.equal(readCache(setup).login, 'octo');
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

test('2914: hidden request reads retain support outside Git and resolve identity freshly', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => ({ status: 200, json: f.check(CALL, 'passed') }));
  const calls = [];
  for (let i = 0; i < 2; i++) {
    const { ports, clock } = portsFor(envFor(setup, fake));
    assert.equal(await runCheck({ cwd: setup.sandbox, options: { '--request': CALL, '--json': true } }, ports), 0, ports.stderr.text);
    calls.push(...clock.gh);
  }
  assert.equal(calls.filter(args => args[0] === 'auth').length, 2);
  assert.equal(calls.filter(args => args[0] === 'api').length, 2);
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
  let lookups = 0;
  const next = portsFor(envFor(setup, fake), { gh: args => ({ status: 0, stdout: args[0] === 'auth' ? TOKEN : ++lookups === 1 ? 'octo 4242' : user }) });
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

for (const mode of ['--read', '--retry']) for (const user of ['renamed 4242', 'mallory 777']) {
  test(`2914 decision b: ${mode} refuses same-token owner ${user} before any request`, async t => {
    const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
    const first = portsFor(envFor(setup, fake));
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, first.ports), 0);
    const batch = JSON.parse(first.ports.stdout.text).batch, file = join(setup.state, 'batches', batch, 'batch.json');
    const before = readFileSync(file, 'utf8'), gets = fake.gets.length, posts = fake.posts.length;
    const calls = [];
    const next = portsFor(envFor(setup, fake), { gh: args => {
      calls.push(args); return { status: 0, stdout: args[0] === 'auth' ? TOKEN : user };
    } });
    assert.equal(await runCheck({ cwd: setup.repo, options: { [mode]: batch, '--json': true } }, next.ports), 5);
    assert.match(next.ports.stderr.text, /These runs belong to octo/);
    assert.equal(calls.filter(args => args[0] === 'api').length, 1);
    assert.equal(fake.gets.length, gets); assert.equal(fake.posts.length, posts);
    assert.equal(readFileSync(file, 'utf8'), before, 'same-token account changes cannot rewrite saved ownership');
  });
}

for (const user of ['octo 4242', 'renamed 4242']) test(`2914 decision b: saved read waits for reset then verifies ${user}`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const first = portsFor(envFor(setup, fake));
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, first.ports), 0);
  const batch = JSON.parse(first.ports.stdout.text).batch, file = join(setup.state, 'batches', batch, 'batch.json');
  const before = readFileSync(file, 'utf8'), gets = fake.gets.length, posts = fake.posts.length;
  const next = portsFor(envFor(setup, fake)), reset = next.clock.now + 120000, sleeps = [];
  let lookups = 0;
  next.ports.gh = args => {
    if (args[0] === 'auth') return { status: 0, stdout: TOKEN };
    assert.equal(args[1], 'user'); lookups++;
    if (lookups === 1) return { ...limited, stdout: `HTTP/2.0 403\r\nx-ratelimit-reset: ${reset / 1000}\r\n\r\n` };
    assert.equal(next.clock.now, reset, 'no lookup before the reset');
    return { status: 0, stdout: `HTTP/2.0 200\r\nx-ratelimit-remaining: 4999\r\n\r\n${user}\n` };
  };
  next.ports.sleep = async ms => { sleeps.push(ms); next.clock.now += ms; };
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--read': batch, '--json': true } }, next.ports), user.startsWith('octo') ? 0 : 5);
  assert.equal(lookups, 2); assert.deepEqual(sleeps, [60000, 60000]);
  assert.match(next.ports.stderr.text, /waiting until.*fresh owner lookup/);
  assert.equal(fake.gets.length, gets); assert.equal(fake.posts.length, posts);
  if (!user.startsWith('octo')) {
    assert.match(next.ports.stderr.text, /These runs belong to octo/);
    assert.equal(readFileSync(file, 'utf8'), before);
  }
});

test('2914 decision b: reset wait respects the saved-read deadline without accepting cached ownership', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const first = portsFor(envFor(setup, fake));
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, first.ports), 0);
  const batch = JSON.parse(first.ports.stdout.text).batch, gets = fake.gets.length;
  const next = portsFor(envFor(setup, fake)), start = next.clock.now;
  let lookups = 0;
  next.ports.gh = args => args[0] === 'auth' ? { status: 0, stdout: TOKEN } : (lookups++, {
    ...limited, stdout: `HTTP/2.0 403\r\nx-ratelimit-reset: ${(start + 120000) / 1000}\r\n\r\n`,
  });
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--read': batch, '--json': true, '--timeout': 1 } }, next.ports), 3);
  assert.equal(lookups, 1); assert.equal(next.clock.now - start, 60000); assert.equal(fake.gets.length, gets);
  assert.match(next.ports.stderr.text, /Read the saved result again after the rate limit resets/);
});

test('2914 decision b: missing response headers use rate-limit metadata before retrying lookup', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt), next = portsFor(envFor(setup, fake));
  const reset = next.clock.now + 2000; let lookups = 0, metadata = 0;
  next.ports.gh = args => {
    if (args[0] === 'auth') return { status: 0, stdout: TOKEN };
    if (args[1] === 'rate_limit') { metadata++; return { status: 0, stdout: String(reset / 1000) }; }
    if (++lookups === 1) return limited;
    assert.equal(next.clock.now, reset); return { status: 0, stdout: 'octo 4242' };
  };
  assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true, '--json': true } }, next.ports), 0);
  assert.equal(lookups, 2); assert.equal(metadata, 1); assert.equal(fake.gets.length, 1);
});

test('2914 decision b: interruption ends reset waiting without any owner request', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt), next = portsFor(envFor(setup, fake));
  const reset = next.clock.now + 120000; let lookups = 0;
  next.ports.gh = args => args[0] === 'auth' ? { status: 0, stdout: TOKEN } : (lookups++, {
    ...limited, stdout: `HTTP/2.0 403\r\nx-ratelimit-reset: ${reset / 1000}\r\n\r\n`,
  });
  next.ports.sleep = async () => { next.clock.interrupt(); };
  assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true } }, next.ports), 3);
  assert.equal(lookups, 1); assert.equal(fake.gets.length, 0);
});

test('2914 decision b: a UUID read respects its timeout while waiting for GitHub', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt), next = portsFor(envFor(setup, fake));
  const start = next.clock.now; let lookups = 0;
  next.ports.gh = args => args[0] === 'auth' ? { status: 0, stdout: TOKEN } : (lookups++, {
    ...limited, stdout: 'HTTP/2.0 403\r\nretry-after: 10\r\n\r\n',
  });
  assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true, '--timeout': 0.001 } }, next.ports), 3);
  assert.equal(next.clock.now - start, 60); assert.equal(lookups, 1); assert.equal(fake.gets.length, 0);
});

test('2914 decision b: a read waits for both Retry-After and the later core reset', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt), next = portsFor(envFor(setup, fake));
  const reset = next.clock.now + 10000; let lookups = 0;
  next.ports.gh = args => {
    if (args[0] === 'auth') return { status: 0, stdout: TOKEN };
    if (++lookups === 1) return { ...limited, stdout: `HTTP/2.0 403\r\nretry-after: 1\r\nx-ratelimit-reset: ${reset / 1000}\r\n\r\n` };
    assert.equal(next.clock.now, reset); return { status: 0, stdout: 'octo 4242' };
  };
  assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true } }, next.ports), 0);
  assert.equal(lookups, 2); assert.equal(fake.gets.length, 1);
});

for (const status of [403, 429]) test(`2914 decision b: HTTP ${status} limit headers need no rate-limit wording`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt), next = portsFor(envFor(setup, fake));
  const start = next.clock.now; let lookups = 0;
  next.ports.gh = args => {
    if (args[0] === 'auth') return { status: 0, stdout: TOKEN };
    if (++lookups === 1) return { status: 1, stderr: `gh: HTTP ${status}`, stdout: `HTTP/2 ${status}\r\nretry-after: 2\r\n${status === 403 ? 'x-ratelimit-remaining: 0\r\n' : ''}\r\n` };
    assert.equal(next.clock.now - start, 2000); return { status: 0, stdout: 'octo 4242' };
  };
  assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true } }, next.ports), 0);
  assert.equal(lookups, 2); assert.equal(fake.gets.length, 1);
});

for (const status of [401, 403]) test(`2914: an ordinary HTTP ${status} lookup is not retried as a rate limit`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, receipt), next = portsFor(envFor(setup, fake));
  let lookups = 0;
  next.ports.gh = args => args[0] === 'auth' ? { status: 0, stdout: TOKEN } : (lookups++, {
    status: 1, stdout: `HTTP/2 ${status}\r\nx-ratelimit-remaining: ${status === 401 ? 0 : 4999}\r\nretry-after: 10\r\n\r\n`, stderr: status === 401 ? 'gh: Bad credentials (HTTP 401)' : 'gh: Forbidden',
  });
  next.ports.sleep = async () => assert.fail('ordinary forbidden responses do not wait for a reset');
  assert.equal(await runCheck({ cwd: setup.repo, words: [CALL], options: { '--read': true } }, next.ports), 5);
  assert.equal(lookups, 1); assert.equal(fake.gets.length, 0);
});
