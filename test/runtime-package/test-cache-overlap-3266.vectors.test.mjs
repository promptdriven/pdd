import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, writeFileSync, readdirSync, statSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../../src/runtime-seam.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';
import { interfaceBlocks, proseSha256 } from '../../src/runtime-seam.mjs';

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
  const state = { identity: { ...A }, running: false, reply: null, pick: null, onCheckPost: null };
  const fake = await fakeRuntime(t, entry => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    if (entry.command === 'lint') return { status: 200, json: fake.lint(id, ['prompts/place_order.prompt.md', 'prompts/independent.prompt.md'].map(path => ({ path, state: 'approved', admission_state: 'approved', interface: { calls: [] } }))) };
    if (entry.method === 'POST' && entry.command === 'check') state.onCheckPost?.(entry);
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
  const invokeWith = async (p, words = [], options = {}, cache = true) => {
    p.stdout.text = ''; p.stderr.text = '';
    const before = fake.posts.filter(x => x.command === 'check').length;
    const code = await runCheck({ words, options: { '--json': true, ...options }, cwd: fixture.repo, cache }, p);
    if (p === ports) clock.now += 1;
    return { code, sent: fake.posts.filter(x => x.command === 'check').length - before, json: options['--json'] === false ? null : JSON.parse(p.stdout.text), stderr: p.stderr.text };
  };
  const invoke = (words, options) => invokeWith(ports, words, options);
  const readBatch = async (name, p = ports, options = {}) => { p.stdout.text = ''; p.stderr.text = ''; return runCheck({ words: [name], options: { '--read': true, '--json': true, ...options }, cwd: fixture.repo, cache: true }, p); };
  return { ...fixture, fake, ports, clock, env, invoke, invokeWith, readBatch, state };
}
function actorPorts(ctx, extra = {}) {
  return portsFor({ ...ctx.env }, extra);
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

const wait = () => new Promise(done => setTimeout(done, 5));
const vectors = read(new URL('./fixtures/native-cases/cache-overlap-3266-cases.json', import.meta.url));
for (const vector of vectors.cases) test(`issue 3266 replay: ${vector.name}`, async t => {
  const ctx = await setup(t); assert.equal((await ctx.invoke()).sent, 3);
  const names = ['independent', 'place-order', 'unknown-item'];
  for (const name of names.slice(0, vector.identities.length)) bump(ctx, `tests/${name}.json`);
  const held = new Map(), released = new Set(); let current = 0;
  const identities = { A, engine: { ...A, engine_sha: 'b'.repeat(40) }, model: { ...A, requested_model: 'synthetic-model-B' } };
  ctx.state.reply = (id, entry, fake) => {
    if (entry.method === 'POST' && !held.has(id)) held.set(id, current);
    const index = held.get(id), identity = identities[vector.identities[index]] ?? A;
    const running = !released.has(index), value = fake.check(id, running ? 'running' : 'passed');
    value.engine_sha = identity.engine_sha; value.usage.requested_model = identity.requested_model;
    if (value.result?.report?.evaluation) value.result.report.evaluation.requested_model = identity.requested_model;
    return { status: running && entry.method === 'POST' ? 202 : 200, json: value };
  };
  const pending = [];
  try {
    for (let i = 0; i < vector.identities.length; i++) {
      current = i; const actor = actorPorts(ctx); actor.ports.interactive = true; actor.clock.now = ctx.clock.now + (i + 1) * 1000;
      pending.push(ctx.invokeWith(actor.ports, [names[i]]));
      for (let n = 0; held.size <= i && n < 2000; n++) await wait();
      assert.equal(held.size, i + 1, 'each run reaches its check before completion');
      if (vector.enterAfter === i - 1 && i + 1 < vector.identities.length) { released.add(vector.enterAfter); assert.equal((await pending[vector.enterAfter]).code, 0); }
    }
    for (const i of vector.order) { released.add(i); assert.equal((await pending[i]).code, 0); }
  } finally { for (let i = 0; i < pending.length; i++) released.add(i); await Promise.allSettled(pending); ctx.state.reply = null; }
  const latest = read(join(ctx.repo, '.pdd/cache/test/stories.json')).latest_identity;
  assert.equal(latest.clean, vector.clean, 'overlap identity is clean only when complete observations agree');
  assert.deepEqual(latest.in_progress, []);
});
