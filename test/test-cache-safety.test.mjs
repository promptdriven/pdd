import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import * as disk from 'node:fs';
import assert from 'node:assert/strict';
import { cpSync, existsSync, mkdirSync, utimesSync, chmodSync, readFileSync, renameSync, symlinkSync, unlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

async function fixture(t) {
  const env = harbor(t);
  let mode = 'passed', incomplete = false, delay = null;
  const fake = await fakeRuntime(t, async entry => {
    if (entry.command === 'lint') return { status: 200, json: fake.lint(entry.request.requestId) };
    if (delay && entry.method === 'POST') await delay;
    const answer = fake.check(entry.request?.requestId ?? entry.url.split('/').at(-1), mode);
    if (incomplete) answer.usage.accounting_complete = false;
    return { status: 200, json: answer };
  });
  const makePorts = () => portsFor({ HOME: env.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: env.state }).ports;
  const invoke = async (options = {}, words = [], extra = {}) => {
    const ports = makePorts(), before = fake.posts.filter(row => row.command === 'check').length;
    const code = await runCheck({ cwd: env.repo, words, options: { '--json': true, ...options }, cache: true }, { ...ports, ...extra });
    return { code, json: ports.stdout.text ? JSON.parse(ports.stdout.text) : null, sent: fake.posts.filter(row => row.command === 'check').length - before };
  };
  const first = await invoke(); assert.equal(first.code, 0);
  assert.ok(existsSync(join(env.repo, '.pdd/cache/test/stories.json')), 'completed pass writes local Story cache');
  assert.ok(existsSync(join(env.repo, '.pdd/cache/test/lastfailed.json')), 'last-failed state uses the designated cache file');
  return { ...env, fake, invoke, makePorts, path: join(env.repo, '.pdd/cache/test/stories.json'),
    mode(value) { mode = value; }, incomplete(value) { incomplete = value; }, delay(value) { delay = value; } };
}
const cacheWarnings = result => result.json.warnings.filter(warning => /cache/i.test(warning));
const change = ctx => {
  const path = join(ctx.repo, 'tests/place-order.json'), original = readFileSync(path, 'utf8'), doc = JSON.parse(original);
  doc.initial_world.changed = true; writeFileSync(path, JSON.stringify(doc));
  return () => writeFileSync(path, original);
};

test('cache clear repairs malformed regular metadata and persists its new pass', async t => {
  const ctx = await fixture(t); writeFileSync(ctx.path, '{truncated');
  const result = await ctx.invoke({ '--cache-clear': true });
  assert.equal(result.sent, 2); assert.equal(result.code, 0);
  assert.equal(cacheWarnings(result).length, 1, 'damaged metadata warns once even during clear');
  assert.ok(result.json.rows.every(row => !row.cached));
  const repeated = await ctx.invoke();
  assert.equal(repeated.sent, 0, 'safe clear persists a usable new cache');
  assert.equal(cacheWarnings(repeated).length, 0);
});

test('cache refuses symlinked ancestor and unsafe clear without changing external data', async t => {
  const ctx = await fixture(t), dir = join(ctx.repo, '.pdd'), outside = join(ctx.sandbox, 'external-pdd');
  renameSync(dir, outside); symlinkSync(outside, dir);
  const before = readFileSync(join(outside, 'cache/test/stories.json'), 'utf8');
  for (const options of [{}, { '--cache-clear': true }]) {
    const result = await ctx.invoke(options); assert.equal(result.sent, 2); assert.equal(cacheWarnings(result).length, 1);
    assert.equal(readFileSync(join(outside, 'cache/test/stories.json'), 'utf8'), before);
  }
});

test('cache refuses symlinked Git exclude without changing its target', async t => {
  const ctx = await fixture(t), exclude = join(ctx.repo, '.git/info/exclude'), outside = join(ctx.sandbox, 'external-exclude');
  const original = readFileSync(exclude, 'utf8'); writeFileSync(outside, original); unlinkSync(exclude); symlinkSync(outside, exclude);
  const result = await ctx.invoke(); assert.equal(result.sent, 2); assert.equal(cacheWarnings(result).length, 1);
  assert.equal(readFileSync(outside, 'utf8'), original);
});

test('unwritable cache fails open once and never claims reuse', async t => {
  const ctx = await fixture(t), dir = join(ctx.repo, '.pdd/cache/test');
  const restore = change(ctx); ctx.mode('failed');
  chmodSync(dir, 0o500);
  try {
    const result = await ctx.invoke(); assert.equal(result.sent, 2); assert.equal(result.code, 1); assert.equal(cacheWarnings(result).length, 1);
    assert.ok(result.json.rows.every(row => !row.cached));
  } finally { chmodSync(dir, 0o700); }
  restore(); ctx.mode('passed');
  assert.equal((await ctx.invoke()).sent, 2, 'restored permissions and old source cannot resurrect earlier passes');
  assert.equal((await ctx.invoke()).sent, 0, 'a reliable fresh generation can be reused');
});

test('oversized and injected cache evidence fail open once', async t => {
  const ctx = await fixture(t), original = readFileSync(ctx.path, 'utf8');
  const injected = JSON.parse(original); const story = Object.values(injected.stories)[0];
  Object.values(story.pass.rows)[0].test = 'tests/forged.json';
  for (const text of [' '.repeat(2 * 1024 * 1024 + 1), JSON.stringify(injected)]) {
    writeFileSync(ctx.path, text);
    const result = await ctx.invoke(); assert.equal(result.sent, 2); assert.equal(cacheWarnings(result).length, 1);
    assert.ok(result.json.rows.every(row => !row.cached));
  }
});

test('passed result with unavailable accounting cannot restore an older pass', async t => {
  const ctx = await fixture(t), restore = change(ctx);
  ctx.incomplete(true); const attempt = await ctx.invoke({}, ['place-order']); assert.equal(attempt.sent, 1);
  assert.equal(attempt.json.rows[0].calls, 'unknown');
  ctx.incomplete(false); restore(); assert.equal((await ctx.invoke({}, ['place-order'])).sent, 1);
});

test('local refusal invalidates an older pass before returning without dispatch', async t => {
  const ctx = await fixture(t), path = join(ctx.repo, 'tests/place-order.json'), original = readFileSync(path, 'utf8');
  const doc = JSON.parse(original); delete doc.steps; writeFileSync(path, JSON.stringify(doc));
  const refused = await ctx.invoke({}, ['place-order']); assert.equal(refused.code, 4); assert.equal(refused.sent, 0);
  writeFileSync(path, original); assert.equal((await ctx.invoke({}, ['place-order'])).sent, 1);
});

test('earlier concurrent pass cannot overwrite a later failed attempt', async t => {
  const ctx = await fixture(t), restore = change(ctx);
  let release;
  const gate = new Promise(resolve => { release = resolve; });
  ctx.delay(gate);
  const before = ctx.fake.posts.filter(row => row.command === 'check').length;
  const earlier = ctx.invoke({}, ['place-order']);
  // Yield until the first command has invalidated the prior pass and dispatched.
  const deadline = Date.now() + 15000;
  while (ctx.fake.posts.filter(row => row.command === 'check').length === before) {
    assert.ok(Date.now() < deadline, 'first check dispatches');
    await new Promise(resolve => setTimeout(resolve, 10));
  }
  ctx.delay(null); ctx.mode('failed');
  const later = await ctx.invoke({}, ['place-order']); assert.equal(later.code, 1);
  ctx.mode('passed'); release(); assert.equal((await earlier).code, 0);
  const selected = await ctx.invoke({ '--lf': true });
  assert.equal(selected.sent, 1, 'the later failed Story remains selected');
  restore();
});

// Review regressions seed only a completed pass: each reaches its own contract assertion on alpha.
test('tracked cache cannot hide failing checks', async t => {
  const ctx = await fixture(t);
  const tracked = spawnSync('git', ['add', '-f', '.pdd/cache/test/stories.json'], { cwd: ctx.repo, encoding: 'utf8' });
  assert.equal(tracked.status, 0, tracked.stderr);
  const committed = spawnSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-qm', 'tracked cache'], { cwd: ctx.repo, encoding: 'utf8' });
  assert.equal(committed.status, 0, committed.stderr);
  ctx.mode('failed');
  const result = await ctx.invoke();
  assert.equal(result.sent, 2, 'Git-tracked prior evidence never skips failing checks');
  assert.equal(result.code, 1); assert.equal(cacheWarnings(result).length, 1);
});

test('copied cache with fresh external state cannot hide failing checks', async t => {
  const ctx = await fixture(t), copied = join(ctx.sandbox, 'copied');
  cpSync(ctx.repo, copied, { recursive: true });
  ctx.mode('failed');
  const ports = ctx.makePorts(); ports.env = { ...ports.env, PDD_STATE_DIR: join(ctx.sandbox, 'fresh-state') };
  const before = ctx.fake.posts.filter(row => row.command === 'check').length;
  const code = await runCheck({ cwd: copied, words: [], options: { '--json': true }, cache: true }, ports);
  assert.equal(ctx.fake.posts.filter(row => row.command === 'check').length - before, 2, 'copy has no local binding');
  assert.equal(code, 1);
});

for (const noVerdict of ['sign-in', 'unknown', 'interrupt', 'timeout']) test(`last failure survives ${noVerdict} then --lf retries it`, async t => {
  const ctx = await fixture(t); change(ctx); ctx.mode('failed');
  assert.equal((await ctx.invoke({}, ['place-order'])).code, 1);
  if (noVerdict === 'sign-in') {
    const attempt = await ctx.invoke({ '--lf': true }, [], { gh: () => ({ status: 1, stdout: '', stderr: 'not signed in' }) });
    assert.notEqual(attempt.code, 0);
  } else if (noVerdict === 'unknown') {
    ctx.mode('unknown'); assert.notEqual((await ctx.invoke({ '--lf': true })).code, 0);
  } else {
    ctx.mode('running'); const ports = ctx.makePorts();
    const extra = { ...ports, sleep: async ms => { if (noVerdict === 'interrupt') interrupt(); else now += ms; }, now: () => now,
      onInterrupt: handler => { interrupt = handler; return () => {}; } };
    let interrupt = () => {}, now = Date.parse('2026-10-27T16:27:47Z');
    assert.notEqual((await ctx.invoke({ '--lf': true, '--timeout': '0.001' }, [], extra)).code, 0);
  }
  ctx.mode('passed'); const retried = await ctx.invoke({ '--lf': true });
  assert.equal(retried.sent, 1, 'a no-verdict attempt never clears the last failure');
  assert.equal(retried.json.rows.length, 1);
  assert.equal((await ctx.invoke({ '--lf': true })).sent, 0, 'confirmed pass clears failure');
});

for (const clear of [false, true]) test(`dead-owner cache lock recovers${clear ? ' during clear' : ''}`, async t => {
  const ctx = await fixture(t), lock = join(ctx.repo, '.pdd/cache/test/transaction.lock');
  mkdirSync(lock); writeFileSync(join(lock, 'owner.json'), JSON.stringify({ pid: 2147483647 }));
  utimesSync(lock, new Date(0), new Date(0));
  const result = await ctx.invoke(clear ? { '--cache-clear': true } : {});
  assert.equal(result.sent, clear ? 2 : 0, 'dead owner does not permanently disable reuse');
  assert.equal(cacheWarnings(result).length, 1);
  assert.match(cacheWarnings(result)[0], /recover.*(?:stale|dead).*cache.*lock/i);
  assert.doesNotMatch(cacheWarnings(result)[0], /not reused|running all|run all/i, 'recovery must not falsely deny eligible reuse');
  assert.equal(existsSync(lock), false, 'stale lock is removed after transaction');
  assert.equal((await ctx.invoke()).sent, 0);
});

test('external state accepts symlinked ancestors and refuses final symlink', async t => {
  const ctx = await fixture(t), ancestor = join(ctx.sandbox, 'ancestor');
  symlinkSync(ctx.sandbox, ancestor);
  const base = ctx.makePorts().env;
  const result = await ctx.invoke({}, [], { env: { ...base, PDD_STATE_DIR: join(ancestor, 'state') } });
  assert.equal(result.sent, 0, 'realpath of trusted state root accepts symlinked ancestors');
  const final = join(ctx.sandbox, 'final-state'); symlinkSync(ctx.state, final);
  const refused = await ctx.invoke({}, [], { env: { ...base, PDD_STATE_DIR: final } });
  assert.ok(refused.code !== 0 || refused.sent === 2, 'final symlink never authorizes reuse');
});

test('damaged regular cache heals after completed run and warning names clear', async t => {
  const ctx = await fixture(t); writeFileSync(ctx.path, '{broken');
  const result = await ctx.invoke(); assert.equal(result.sent, 2);
  assert.equal(cacheWarnings(result).length, 1); assert.match(cacheWarnings(result)[0], /pdd test --cache-clear/);
  const repeated = await ctx.invoke(); assert.equal(repeated.sent, 0, 'completed check repairs regular metadata');
  assert.equal(cacheWarnings(repeated).length, 0);
});

test('fingerprint includes local package and engine identity and pass keeps observed engine', async t => {
  const ctx = await fixture(t); change(ctx); const keys = [];
  await ctx.invoke({}, [], { cacheHash: bytes => { keys.push(JSON.parse(bytes.toString())); return createHash('sha256').update(bytes).digest('hex'); } });
  const fingerprint = keys.find(value => value.footprint && value.raw);
  assert.ok(fingerprint, 'fingerprint goes through injected hashing port');
  assert.equal(fingerprint.pdd_version, JSON.parse(readFileSync(new URL('../package.json', import.meta.url))).version);
  const engine = readFileSync(new URL('../src/runtime-client.mjs', import.meta.url), 'utf8').match(/const ENGINE_SHA = '([^']+)'/)[1];
  assert.equal(fingerprint.engine_sha, engine);
  const records = JSON.parse(readFileSync(ctx.path, 'utf8')).stories;
  assert.ok(Object.values(records).every(row => row.pass?.engine_sha === engine), 'pass retains observed server engine');
});

// AC6: a dead-owner recovery must still protect a live successor owner.
test('stale lock recovery preserves a successor live owner', async t => {
  const ctx = await fixture(t);
  const lock = join(ctx.repo, '.pdd/cache/test/transaction.lock');
  const ownerPath = join(lock, 'owner.json');
  mkdirSync(lock);
  writeFileSync(ownerPath, JSON.stringify({ pid: 2147483647 }));
  let successorAcquired = false, removedSuccessor = false, ownAcquired = false;
  const cacheFiles = {
    nonce: randomUUID, lstat: disk.lstatSync, write: disk.writeFileSync,
    list: disk.readdirSync, rename: disk.renameSync, rmdir: disk.rmdirSync,
    exclude(root) { return join(root, '.git/info/exclude'); },
    mkdir(path, ...args) {
      const result = disk.mkdirSync(path, ...args);
      if (path === lock) ownAcquired = true;
      return result;
    },
    read(path, ...args) {
      const result = disk.readFileSync(path, ...args);
      if (path === ownerPath && !successorAcquired) {
        // A second stale contender recovers and acquires while our read returns
        // the earlier dead-owner bytes. This invocation has not acquired yet.
        successorAcquired = true;
        disk.writeFileSync(ownerPath, JSON.stringify({ pid: process.pid }));
      }
      return result;
    },
    unlink(path) {
      if (path === ownerPath && successorAcquired && !ownAcquired &&
          disk.existsSync(path) && JSON.parse(disk.readFileSync(path)).pid === process.pid) {
        removedSuccessor = true;
      }
      return disk.unlinkSync(path);
    }
  };
  await ctx.invoke({}, [], { cacheFiles });
  assert.equal(successorAcquired, true, 'the recovery race must be exercised');
  assert.equal(removedSuccessor, false, 'stale contender must never unlink successor live owner');
  assert.ok(existsSync(ownerPath), 'the live successor retains its lock');
});

// AC6: interrupted cache transactions recover, while live owners remain protected.
// These on-disk claims model a process stopped before or after ticket publication.
for (const published of [false, true]) test(`dead ${published ? 'published' : 'pending'} cache claim recovers`, async t => {
  const ctx = await fixture(t);
  const claim = join(ctx.repo, '.pdd/cache/test/transaction-claims', `2147483647.${randomUUID()}`);
  mkdirSync(claim, { recursive: true });
  writeFileSync(join(claim, published ? 'ticket.json' : 'ticket.tmp'), '1');
  const result = await ctx.invoke();
  assert.equal(result.code, 0);
  assert.equal(result.sent, 0, 'dead claim recovery preserves valid unchanged passes');
  assert.equal(cacheWarnings(result).length, 1, 'dead claim recovery warns once');
  assert.equal(existsSync(claim), false, 'abandoned transaction claim is reclaimed');
  const repeat = await ctx.invoke();
  assert.equal(repeat.sent, 0);
  assert.equal(cacheWarnings(repeat).length, 0, 'recovered claim does not warn again');
});

test('live pending cache claim fails open within a bound and recovers after release', async t => {
  const ctx = await fixture(t);
  const claim = join(ctx.repo, '.pdd/cache/test/transaction-claims', `${process.pid}.${randomUUID()}`);
  mkdirSync(claim, { recursive: true });
  writeFileSync(join(claim, 'ticket.tmp'), '1');
  const before = readFileSync(ctx.path, 'utf8');
  let waits = 0;
  ctx.mode('failed');
  const result = await ctx.invoke({}, [], { sleep: async () => {
    assert.ok(++waits <= 100, 'cache contention has a bounded wait');
  } });
  assert.equal(result.sent, 2, 'a live pending owner cannot authorize reuse');
  assert.equal(result.code, 1, 'cache contention still reports interpreter failures');
  assert.ok(result.json.rows.every(row => !row.cached));
  assert.equal(cacheWarnings(result).length, 1);
  assert.equal(readFileSync(ctx.path, 'utf8'), before, 'contended transaction never changes cached evidence');
  assert.ok(existsSync(claim), 'live choosing owner retains its claim');
  assert.equal(readFileSync(join(claim, 'ticket.tmp'), 'utf8'), '1');
  assert.equal(existsSync(join(claim, 'ticket.json')), false, 'another process never publishes for the live owner');
  disk.rmSync(claim, { recursive: true });
  ctx.mode('passed');
  const recovered = await ctx.invoke();
  assert.equal(recovered.code, 0);
  assert.equal(recovered.sent, 2, 'contention invalidation prevents resurrecting the earlier passes');
  assert.equal(cacheWarnings(recovered).length, 0);
  assert.equal((await ctx.invoke()).sent, 0, 'completed uncontended checks restore reuse');
});

// A partial pass cannot confirm a complete Story pass or clear its known failure.
test('partial sibling pass retains last failure until the whole Story passes', async t => {
  const env = harbor(t, repo => {
    cpSync(join(repo, 'tests/place-order.json'), join(repo, 'tests/place-order-extra.json'));
  });
  let mode = 'passed';
  const fake = await fakeRuntime(t, entry => ({ status: 200, json: entry.command === 'lint'
    ? fake.lint(entry.request.requestId)
    : fake.check(entry.request?.requestId ?? entry.url.split('/').at(-1), mode) }));
  const invoke = async (words = [], options = {}) => {
    const { ports } = portsFor({ HOME: env.home, PDD_STATE_DIR: env.state, PDD_RUNTIME_URL: fake.origin });
    const code = await runCheck({ cwd: env.repo, words, options: { '--json': true, ...options }, cache: true }, ports);
    return { code, json: JSON.parse(ports.stdout.text) };
  };
  assert.equal((await invoke()).code, 0);
  assert.ok(existsSync(join(env.repo, '.pdd/cache/test/stories.json')), 'completed pass writes local Story cache');
  mode = 'failed';
  const failed = await invoke([], { '--cache-clear': true });
  assert.equal(failed.code, 1);
  assert.deepEqual(failed.json.rows.map(row => row.test).sort(),
    ['tests/place-order-extra.json', 'tests/place-order.json', 'tests/unknown-item.json']);
  assert.ok(failed.json.rows.every(row => row.state === 'failed'));
  mode = 'passed';
  const partial = await invoke(['tests/place-order.json']);
  assert.equal(partial.code, 0);
  assert.deepEqual(partial.json.rows.map(row => row.test), ['tests/place-order.json']);
  assert.equal(partial.json.rows[0].state, 'passed');
  // Keep another failed Story so --lf's empty-history fallback cannot hide a loss.
  mode = 'failed';
  const retained = await invoke([], { '--lf': true });
  assert.deepEqual(retained.json.rows.map(row => row.test).sort(),
    ['tests/place-order-extra.json', 'tests/place-order.json', 'tests/unknown-item.json'],
    '--lf retains every sibling of the previously failed Story after only a partial pass');
  assert.equal(retained.code, 1);
  mode = 'passed';
  const complete = await invoke(['user_stories/place-order.md']);
  assert.equal(complete.code, 0);
  assert.deepEqual(complete.json.rows.map(row => row.test).sort(),
    ['tests/place-order-extra.json', 'tests/place-order.json']);
  assert.ok(complete.json.rows.every(row => row.state === 'passed'));
  mode = 'failed';
  const remaining = await invoke([], { '--lf': true });
  assert.equal(remaining.code, 1);
  assert.deepEqual(remaining.json.rows.map(row => row.test), ['tests/unknown-item.json'],
    'a complete Story pass clears only that Story from last-failed selection');
});
