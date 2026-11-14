import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../../src/runtime-seam.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';
import { interfaceBlocks, proseSha256, captureSource } from '../../src/runtime-seam.mjs';
function appendProse(file, extra) { let text = readFileSync(file, 'utf8').replace('## Dependencies\n\nNone.\n', '## Dependencies\n' + extra); const block = interfaceBlocks(text)[0]; const doc = JSON.parse(block[1]); doc.status = 'draft'; text = text.slice(0, block.indices[1][0]) + JSON.stringify(doc) + text.slice(block.indices[1][1]); text = text.replace(/"prose_sha256"\s*:\s*"[^"]*"/, '"prose_sha256":"' + proseSha256(text) + '"'); writeFileSync(file, text); }

const read = path => { assert.ok(existsSync(path), 'required fixture or cache metadata exists'); return JSON.parse(readFileSync(path, 'utf8')); };
const write = (path, value) => writeFileSync(path, JSON.stringify(value, null, 2) + '\n');
const day = 86400000;

async function setup(t, edit) {
  const fixture = harbor(t, repo => {
    writeFileSync(join(repo, 'user_stories/independent.md'), readFileSync(join(repo, 'user_stories/place-order.md')));
    writeFileSync(join(repo, 'prompts/independent.prompt.md'), readFileSync(join(repo, 'prompts/place_order.prompt.md')));
    const doc = read(join(repo, 'tests/place-order.json')); doc.story_path = 'user_stories/independent.md';
    for (const step of doc.steps) step.entry_path = 'prompts/independent.prompt.md';
    write(join(repo, 'tests/independent.json'), doc); edit?.(repo);
  });
  const state = { identity: { engine_sha: 'a'.repeat(40), requested_model: 'synthetic-model-A' }, running: false };
  const fake = await fakeRuntime(t, entry => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    if (entry.command === 'lint') return { status: 200, json: fake.lint(id, ['prompts/place_order.prompt.md', 'prompts/independent.prompt.md', 'prompts/style.prompt.md'].map(path => ({ path, state: 'approved', admission_state: 'approved', interface: { calls: [] } }))) };
    if (state.running) {
      const job = fake.check(id, 'running'); job.engine_sha = state.identity.engine_sha; job.usage.requested_model = state.identity.requested_model;
      return { status: entry.method === 'POST' ? 202 : 200, json: job };
    }
    const job = fake.check(id); job.engine_sha = state.identity.engine_sha;
    job.usage.requested_model = state.identity.requested_model;
    job.result.report.evaluation.requested_model = state.identity.requested_model;
    state.edit?.(job, entry);
    return { status: 200, json: job };
  });
  const { ports, clock } = portsFor({ HOME: fixture.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: fixture.state });
  const invoke = async (words = [], options = {}) => {
    ports.stdout.text = ''; ports.stderr.text = '';
    const before = fake.posts.filter(x => x.command === 'check').length;
    const code = await runCheck({ words, options: { '--json': true, ...options }, cwd: fixture.repo, cache: true }, ports);
    clock.now += 1; // Separate successive synthetic invocations without changing their sample time.
    return { code, sent: fake.posts.filter(x => x.command === 'check').length - before, json: options['--json'] === false ? null : JSON.parse(ports.stdout.text), stderr: ports.stderr.text, stdout: ports.stdout.text };
  };
  return { ...fixture, fake, ports, clock, invoke, state };
}
function changeIndependent(ctx) {
  const path = join(ctx.repo, 'tests/independent.json'), doc = read(path); doc.initial_world.changed = true; write(path, doc);
}

// Every fixture and expectation below is synthetic; no hosted interpreter is used.
function editPrompt(repo, mutate) {
  const path = join(repo, 'prompts/place_order.prompt.md');
  let text = readFileSync(path, 'utf8'), block = interfaceBlocks(text)[0], doc = JSON.parse(block[1]);
  mutate(doc); doc.status = 'draft';
  text = text.slice(0, block.indices[1][0]) + JSON.stringify(doc) + text.slice(block.indices[1][1]);
  text = text.replace(/"prose_sha256"\s*:\s*"[^"]*"/, '"prose_sha256":"' + proseSha256(text) + '"');
  writeFileSync(path, text);
}
function resource(kind) {
  const schema = { type: 'object', properties: {}, required: [], additionalProperties: false };
  return { name: 'gcloud', kind, access: 'write', operations: [{ name: 'call', access: 'write', arguments_schema: schema, result_schema: schema }] };
}
const selected = ['tests/place-order.json'];
const fakeReason = 'runs every time: uses an AI-played fake (gcloud)';
async function successful(ctx, words = [], options = {}) {
  const result = await ctx.invoke(words, options); assert.equal(result.code, 0, result.stderr); return result;
}

test('TEST-CACHE-R2 late read identity conflict invalidates a newer batch pass', async t => {
  const ctx = await setup(t); ctx.state.running = true;
  const original = await ctx.invoke(['independent'], { '--timeout': 1 }); assert.equal(original.code, 3); assert.equal(original.sent, 1);
  ctx.state.running = false; ctx.clock.now += 10 * 60000;
  assert.equal((await successful(ctx, ['place-order', 'unknown-item'])).sent, 2);
  ctx.state.identity.engine_sha = 'b'.repeat(40); ctx.clock.now += 10 * 60000;
  assert.equal(await runCheck({ words: [original.json.batch], options: { '--read': true, '--json': true }, cwd: ctx.repo, cache: true }, ctx.ports), 0);
  const afterRead = read(join(ctx.repo, '.pdd/cache/test/stories.json'));
  const repeat = await successful(ctx, ['place-order']);
  assert.equal(repeat.sent, 1, 'a disagreeing late read must invalidate previously stored identities');
  assert.equal(repeat.json.rows[0].cache_reason, 'runs again: cache identity is unverified');
  assert.equal(afterRead.latest_identity.conflict, true);
  assert.equal((await successful(ctx, ['place-order'])).sent, 0, 'a clean run resolves the conflict');
});
test('TEST-CACHE-R2 mixed builds cannot let the last observation authorize reuse', async t => {
  const ctx = await setup(t); assert.equal((await successful(ctx)).sent, 3); changeIndependent(ctx);
  const file = join(ctx.repo, 'tests/place-order.json'), doc = read(file); doc.initial_world.changed = true; write(file, doc);
  const ids = [];
  ctx.state.edit = job => { if (!ids.includes(job.requestId)) ids.push(job.requestId); job.engine_sha = (ids.indexOf(job.requestId) === 0 ? 'b' : 'a').repeat(40); };
  assert.equal((await successful(ctx, ['independent', 'place-order'])).sent, 2);
  ctx.state.edit = null;
  const mixed = read(join(ctx.repo, '.pdd/cache/test/stories.json'));
  const next = await successful(ctx, ['unknown-item']);
  assert.equal(next.sent, 1, 'mixed identities match no pass regardless of last answer');
  assert.equal(next.json.rows[0].cache_reason, 'runs again: cache identity is unverified');
  assert.equal(mixed.latest_identity.conflict, true);
  assert.equal((await successful(ctx, ['unknown-item'])).sent, 0, 'a clean run makes reuse eligible again');
});
test('TEST-CACHE-R2 unparseable fixed-clock labels use the real clock', async t => {
  const ctx = await setup(t, repo => {
    editPrompt(repo, doc => { doc.resources = [{ ...resource('port'), name: 'clock', operations: [{ ...resource('port').operations[0], name: 'now' }] }]; });
  });
  for (const value of ['now', 'real', 'not-a-date']) {
    const file = join(ctx.repo, 'tests/place-order.json'), doc = read(file); doc.initial_world.clock = { now: value }; write(file, doc);
    assert.equal((await successful(ctx, selected)).sent, 1);
    const repeat = await successful(ctx, selected);
    assert.equal(repeat.sent, 1); assert.equal(repeat.json.rows[0].cache_reason, 'runs every time: uses the real clock');
  }
});
test('TEST-CACHE-R2 normal long-running invocation keeps its batch start as passed_at', async t => {
  const ctx = await setup(t); ctx.ports.interactive = true; ctx.state.running = true;
  const started = ctx.clock.now;
  ctx.ports.sleep = async () => { ctx.clock.now += 45 * 60000; ctx.state.running = false; await new Promise(done => setImmediate(done)); };
  assert.equal((await successful(ctx, ['independent'])).sent, 1);
  assert.ok(ctx.clock.now >= started + 45 * 60000, 'synthetic wait separates start from completion');
  const pass = read(join(ctx.repo, '.pdd/cache/test/stories.json')).stories['user_stories/independent.md'].pass;
  assert.equal(pass.passed_at, new Date(started).toISOString(), 'normal completion must not refresh the sample timestamp');
});
test('TEST-CACHE-R2 one additional check uses a singular send notice', async t => {
  const ctx = await setup(t); assert.equal((await successful(ctx)).sent, 3); changeIndependent(ctx);
  ctx.state.identity.engine_sha = 'b'.repeat(40);
  const result = await successful(ctx, ['independent', 'place-order']);
  assert.equal(result.sent, 2); assert.equal(result.stderr.split('\n').filter(line => /^Sent 1 check at /.test(line)).length, 2);
  assert.doesNotMatch(result.stderr, /Sending 1 more checks:/);
});
test('TEST-CACHE-R2 unavailable footprint explains this run and permits later reuse', async t => {
  const ctx = await setup(t);
  ctx.ports.captureSource = (...args) => { const capture = captureSource(...args); capture.stories = []; return capture; };
  const missing = await successful(ctx, selected);
  assert.equal(missing.sent, 1); assert.equal(missing.json.rows[0].cache_reason, 'runs again: resource declarations unavailable');
  delete ctx.ports.captureSource;
  assert.equal((await successful(ctx, selected)).sent, 1);
  assert.equal((await successful(ctx, selected)).sent, 0, 'complete evidence allows later reuse');
});
