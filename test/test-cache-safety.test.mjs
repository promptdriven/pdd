import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, readFileSync, renameSync, symlinkSync, unlinkSync, writeFileSync } from 'node:fs';
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
  assert.equal((await invoke()).sent, 0, 'complete unchanged passes reuse before safety checks');
  return { ...env, fake, invoke, makePorts, path: join(env.repo, '.pdd/test-cache/stories.json'),
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
  assert.equal((await ctx.invoke()).sent, 0);
});

test('cache refuses symlinked ancestor and unsafe clear without changing external data', async t => {
  const ctx = await fixture(t), dir = join(ctx.repo, '.pdd'), outside = join(ctx.sandbox, 'external-pdd');
  renameSync(dir, outside); symlinkSync(outside, dir);
  const before = readFileSync(join(outside, 'test-cache/stories.json'), 'utf8');
  for (const options of [{}, { '--cache-clear': true }]) {
    const result = await ctx.invoke(options); assert.equal(result.sent, 2); assert.equal(cacheWarnings(result).length, 1);
    assert.equal(readFileSync(join(outside, 'test-cache/stories.json'), 'utf8'), before);
  }
});

test('cache refuses symlinked Git exclude without changing its target', async t => {
  const ctx = await fixture(t), exclude = join(ctx.repo, '.git/info/exclude'), outside = join(ctx.sandbox, 'external-exclude');
  const original = readFileSync(exclude, 'utf8'); writeFileSync(outside, original); unlinkSync(exclude); symlinkSync(outside, exclude);
  const result = await ctx.invoke(); assert.equal(result.sent, 2); assert.equal(cacheWarnings(result).length, 1);
  assert.equal(readFileSync(outside, 'utf8'), original);
});

test('unwritable cache fails open once and never claims reuse', async t => {
  const ctx = await fixture(t), dir = join(ctx.repo, '.pdd/test-cache');
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
