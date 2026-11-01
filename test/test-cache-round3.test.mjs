import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, writeFileSync, readdirSync, statSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';
import { interfaceBlocks, proseSha256 } from '../src/runtime-preflight.mjs';

const read = path => { assert.ok(existsSync(path), 'required fixture or cache metadata exists'); return JSON.parse(readFileSync(path, 'utf8')); };
const write = (path, value) => writeFileSync(path, JSON.stringify(value, null, 2) + '\n');
const min = 60000;
const A = { engine_sha: 'a'.repeat(40), requested_model: 'synthetic-model-A' };
const B = { engine_sha: 'b'.repeat(40), requested_model: 'synthetic-model-A' };

async function setup(t, edit) {
  const fixture = harbor(t, repo => {
    writeFileSync(join(repo, 'user_stories/independent.md'), readFileSync(join(repo, 'user_stories/place-order.md')));
    writeFileSync(join(repo, 'prompts/independent.prompt.md'), readFileSync(join(repo, 'prompts/place_order.prompt.md')));
    const doc = read(join(repo, 'tests/place-order.json')); doc.story_path = 'user_stories/independent.md';
    for (const step of doc.steps) step.entry_path = 'prompts/independent.prompt.md';
    write(join(repo, 'tests/independent.json'), doc); edit?.(repo);
  });
  const state = { identity: { ...A }, running: false, reply: null, pick: null };
  const fake = await fakeRuntime(t, entry => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    if (entry.command === 'lint') return { status: 200, json: fake.lint(id, ['prompts/place_order.prompt.md', 'prompts/independent.prompt.md'].map(path => ({ path, state: 'approved', admission_state: 'approved', interface: { calls: [] } }))) };
    const custom = state.reply?.(id, entry, fake); if (custom) return custom;
    const identity = state.pick?.(id) ?? state.identity;
    if (state.running) {
      const job = fake.check(id, 'running'); job.engine_sha = identity.engine_sha; job.usage.requested_model = identity.requested_model;
      return { status: entry.method === 'POST' ? 202 : 200, json: job };
    }
    const job = fake.check(id); job.engine_sha = identity.engine_sha;
    job.usage.requested_model = identity.requested_model;
    job.result.report.evaluation.requested_model = identity.requested_model;
    return { status: 200, json: job };
  });
  const env = { HOME: fixture.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: fixture.state };
  const { ports, clock } = portsFor(env);
  const invokeWith = async (p, words = [], options = {}) => {
    p.stdout.text = ''; p.stderr.text = '';
    const before = fake.posts.filter(x => x.command === 'check').length;
    const code = await runCheck({ words, options: { '--json': true, ...options }, cwd: fixture.repo, cache: true }, p);
    return { code, sent: fake.posts.filter(x => x.command === 'check').length - before, json: options['--json'] === false ? null : JSON.parse(p.stdout.text), stderr: p.stderr.text };
  };
  const invoke = (words, options) => invokeWith(ports, words, options);
  const readBatch = async (name, p = ports) => { p.stdout.text = ''; p.stderr.text = ''; return runCheck({ words: [name], options: { '--read': true, '--json': true }, cwd: fixture.repo, cache: true }, p); };
  return { ...fixture, fake, ports, clock, env, invoke, invokeWith, readBatch, state };
}
function bump(ctx, file) { const path = join(ctx.repo, file), doc = read(path); doc.initial_world.changed = (doc.initial_world.changed ?? 0) + 1; write(path, doc); }
function findBatch(dir, name) {
  for (const entry of readdirSync(dir)) {
    const path = join(dir, entry);
    if (entry === name && existsSync(join(path, 'batch.json'))) return join(path, 'batch.json');
    if (statSync(path).isDirectory()) { const found = findBatch(path, name); if (found) return found; }
  }
  return null;
}

const interleavings = [
  { name: 'overlap and older writer', run: async ctx => {
  assert.equal((await ctx.invoke()).sent, 3);
  bump(ctx, 'tests/independent.json'); bump(ctx, 'tests/place-order.json');
  const p = portsFor(ctx.env); p.ports.interactive = true; p.clock.now = ctx.clock.now + 1000;
  const q = portsFor(ctx.env); q.clock.now = ctx.clock.now + 60000;
  let released = false; const held = new Set(); let phase = 'p';
  ctx.state.reply = (id, entry, fake) => {
    if (entry.method === 'POST') { if (phase === 'p') held.add(id); }
    const hold = held.has(id);
    if (hold && !released) { const job = fake.check(id, 'running'); job.engine_sha = A.engine_sha; job.usage.requested_model = A.requested_model; return { status: entry.method === 'POST' ? 202 : 200, json: job }; }
    const identity = hold ? A : B;
    const job = fake.check(id); job.engine_sha = identity.engine_sha; job.usage.requested_model = identity.requested_model; job.result.report.evaluation.requested_model = identity.requested_model;
    return { status: 200, json: job };
  };
  const pRun = ctx.invokeWith(p.ports, ['independent']);
  while (!held.size) await new Promise(done => setTimeout(done, 5));
  phase = 'q';
  const qRes = await ctx.invokeWith(q.ports, ['place-order']);
  released = true;
  const pRes = await pRun;
  ctx.state.reply = null; ctx.state.identity = { ...B }; ctx.clock.now = q.clock.now + 60000;
  const u = await ctx.invoke(['unknown-item']);
  assert.equal(u.sent, 1, 'pdd saw build b in Q; the old build-a pass must not be reused');
  } },
  { name: 'read that resends', run: async ctx => {
  assert.equal((await ctx.invoke()).sent, 3);
  bump(ctx, 'tests/independent.json'); bump(ctx, 'tests/place-order.json');
  ctx.state.running = true;
  const x = await ctx.invoke(['independent', 'place-order']);
  assert.equal(x.code, 3); assert.equal(x.sent, 2);
  ctx.state.running = false;
  const saved = read(findBatch(ctx.env.PDD_STATE_DIR, x.json.batch) ?? findBatch(ctx.home, x.json.batch));
  const ids = Object.fromEntries(saved.rows.map(r => [r.test, r.request_ids.at(-1)]));
  ctx.clock.now += 10 * min; ctx.state.identity = { ...B }; bump(ctx, 'tests/unknown-item.json');
  const y = await ctx.invoke(['unknown-item']);
  ctx.clock.now += 10 * min;
  ctx.state.reply = (id, entry, fake) => {
    if (id === ids['tests/independent.json']) { const job = fake.check(id); job.engine_sha = A.engine_sha; job.usage.requested_model = A.requested_model; job.result.report.evaluation.requested_model = A.requested_model; return { status: 200, json: job }; }
    if (id === ids['tests/place-order.json']) { const job = fake.job(id, 'check', 'unknown', { exitCode: 1, refusals: [{ code: 'service-restarted', message: 'restarted' }], report: { refusal: { code: 'service-restarted' } } }); job.engine_sha = A.engine_sha; job.usage.requested_model = A.requested_model; return { status: 200, json: job }; }
    const job = fake.check(id, 'queued'); delete job.engine_sha; delete job.usage.requested_model; return { status: entry.method === 'POST' ? 202 : 200, json: job };
  };
  const before = ctx.fake.posts.filter(p => p.command === 'check').length;
  const code = await ctx.readBatch(x.json.batch);
  ctx.state.reply = null;
  const named = await ctx.invoke(['independent']);
  assert.equal(named.sent, 1, 'Y saw build b after X started; X\'s build-a pass must not be reused');
  } },
  { name: 'clean repeat', run: async ctx => {
    assert.equal((await ctx.invoke()).sent, 3);
    assert.equal((await ctx.invoke(['unknown-item'])).sent, 0);
  } },
  { name: 'late read', run: async ctx => {
    ctx.state.running = true; const first = await ctx.invoke(['independent']); assert.equal(first.code, 3);
    ctx.state.running = false; ctx.clock.now += 10 * min;
    assert.equal((await ctx.invoke(['place-order', 'unknown-item'])).sent, 2);
    ctx.state.identity = { ...B }; ctx.clock.now += 10 * min;
    assert.equal(await ctx.readBatch(first.json.batch), 0);
    assert.equal((await ctx.invoke(['place-order'])).sent, 1, 'never skip after a read wrote the record');
  } },
  { name: 'mixed builds', run: async ctx => {
    assert.equal((await ctx.invoke()).sent, 3); bump(ctx, 'tests/independent.json'); bump(ctx, 'tests/place-order.json');
    const ids = []; ctx.state.pick = id => { if (!ids.includes(id)) ids.push(id); return ids.indexOf(id) === 0 ? B : A; };
    assert.equal((await ctx.invoke(['independent', 'place-order'])).sent, 2); ctx.state.pick = null;
    assert.equal((await ctx.invoke(['unknown-item'])).sent, 1, 'never skip after mixed observations');
  } },
  { name: 'partial identity', run: async ctx => {
    assert.equal((await ctx.invoke()).sent, 3); bump(ctx, 'tests/independent.json');
    ctx.state.reply = (id, entry, fake) => { const job = fake.check(id); delete job.engine_sha; return { status: 200, json: job }; };
    assert.equal((await ctx.invoke(['independent'])).sent, 1); ctx.state.reply = null;
    assert.equal((await ctx.invoke(['unknown-item'])).sent, 1, 'never skip after a partial identity');
  } },
  { name: 'old writer record', run: async ctx => {
    assert.equal((await ctx.invoke()).sent, 3);
    const file = join(ctx.repo, '.pdd/cache/test/stories.json'), doc = read(file);
    doc.latest_identity.clean = false; write(file, doc);
    assert.equal((await ctx.invoke(['unknown-item'])).sent, 1, 'never skip when the writer was not clean');
  } },
  { name: 'unknown writer', run: async ctx => {
    assert.equal((await ctx.invoke()).sent, 3);
    const file = join(ctx.repo, '.pdd/cache/test/stories.json'), doc = read(file);
    delete doc.latest_identity.clean; delete doc.latest_identity.written_at; write(file, doc);
    assert.equal((await ctx.invoke(['unknown-item'])).sent, 1, 'legacy or unknown writers cannot authorize reuse');
  } },
];
test('TEST-CACHE-R3 interleaving table: never skip on doubt', async t => {
  for (const row of interleavings) await t.test(row.name, async t => row.run(await setup(t)));
});
function editClock(repo) {
  const file = join(repo, 'prompts/place_order.prompt.md'); let text = readFileSync(file, 'utf8');
  const block = interfaceBlocks(text)[0], doc = JSON.parse(block[1]); doc.status = 'draft';
  const schema = { type: 'object', properties: {}, required: [], additionalProperties: false };
  doc.resources = [{ name: 'clock', kind: 'port', access: 'read', operations: [{ name: 'now', access: 'read', arguments_schema: schema, result_schema: schema }] }];
  text = text.slice(0, block.indices[1][0]) + JSON.stringify(doc) + text.slice(block.indices[1][1]);
  text = text.replace(/"prose_sha256"\s*:\s*"[^"]*"/, '"prose_sha256":"' + proseSha256(text) + '"'); writeFileSync(file, text);
}
test('TEST-CACHE-R3 only ISO date-time strings fix the clock', async t => {
  const ctx = await setup(t, editClock), selected = ['tests/place-order.json'];
  for (const value of ['real 2026', 'now 1', '1', '2026-10-31', '2026-10-31T12:00:00Z', '2026-10-31T12:00:00+01:00']) {
    const file = join(ctx.repo, 'tests/place-order.json'), doc = read(file); doc.initial_world.clock = { now: value }; write(file, doc);
    assert.equal((await ctx.invoke(selected)).sent, 1);
    const repeat = await ctx.invoke(selected), iso = value.includes('T');
    assert.equal(repeat.sent, iso ? 0 : 1);
    if (!iso) assert.equal(repeat.json.rows[0].cache_reason, 'runs every time: uses the real clock');
  }
});
for (const part of ['engine', 'model']) test(`TEST-CACHE-R3 multiple stored ${part} values remain doubt with a false flag`, async t => {
  const ctx = await setup(t); assert.equal((await ctx.invoke()).sent, 3);
  const file = join(ctx.repo, '.pdd/cache/test/stories.json'), doc = read(file);
  if (part === 'engine') Object.assign(doc.latest_identity, { engine_sha: null, engine_shas: [A.engine_sha, B.engine_sha], conflict: false });
  else Object.assign(doc.latest_identity, { models: [A.requested_model, 'synthetic-model-B'], conflict: false });
  write(file, doc);
  assert.equal((await ctx.invoke()).sent, 3, 'stored multiple values can never authorize a skip');
});
