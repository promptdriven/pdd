import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { interfaceBlocks, proseSha256 } from '../src/runtime-preflight.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// Synthetic requirements from the approved design: no hosted interpreter or model.
const read = path => JSON.parse(readFileSync(path, 'utf8'));
const write = (path, value) => writeFileSync(path, JSON.stringify(value, null, 2) + '\n');
const day = 86400000;
function editPrompt(repo, mutate, path = 'prompts/place_order.prompt.md') {
  const file = join(repo, path), text = readFileSync(file, 'utf8'), block = interfaceBlocks(text)[0];
  const doc = JSON.parse(block[1]); mutate(doc); doc.status = 'draft';
  let changed = text.slice(0, block.indices[1][0]) + JSON.stringify(doc) + text.slice(block.indices[1][1]);
  if (doc.resources?.length) changed = changed.replace('There are no external resources, operating-system commands, or persistent state.', 'The declared resources are supplied through injected fake boundaries.');
  changed = changed.replace(/"prose_sha256"\s*:\s*"[^"]*"/, '"prose_sha256":"' + proseSha256(changed) + '"');
  writeFileSync(file, changed);
}
function resource(kind, name = 'gcloud', operations = ['call']) {
  const schema = { type: 'object', properties: {}, required: [], additionalProperties: false };
  return { name, kind, access: 'write', operations: operations.map(name => ({ name, access: 'write', arguments_schema: schema, result_schema: schema })) };
}
async function setup(t, edit) {
  const fixture = harbor(t, repo => {
    writeFileSync(join(repo, 'user_stories/independent.md'), readFileSync(join(repo, 'user_stories/place-order.md')));
    writeFileSync(join(repo, 'prompts/independent.prompt.md'), readFileSync(join(repo, 'prompts/place_order.prompt.md')));
    const doc = read(join(repo, 'tests/place-order.json')); doc.story_path = 'user_stories/independent.md';
    for (const step of doc.steps) step.entry_path = 'prompts/independent.prompt.md';
    write(join(repo, 'tests/independent.json'), doc); edit?.(repo);
  });
  let identity = { engine_sha: 'a'.repeat(40), requested_model: 'synthetic-model-A' };
  let answerEdit = x => x;
  const fake = await fakeRuntime(t, entry => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    if (entry.command === 'lint') return { status: 200, json: fake.lint(id, ['prompts/place_order.prompt.md', 'prompts/independent.prompt.md'].map(path => ({ path, state: 'approved', admission_state: 'approved', interface: { calls: [] } }))) };
    const job = fake.check(id); job.engine_sha = identity.engine_sha;
    job.usage.requested_model = identity.requested_model;
    job.result.report.evaluation.requested_model = identity.requested_model;
    return { status: 200, json: answerEdit(job, entry) };
  });
  const { ports, clock } = portsFor({ HOME: fixture.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: fixture.state });
  const invoke = async (words = [], options = {}) => {
    ports.stdout.text = ''; ports.stderr.text = '';
    const before = fake.posts.filter(x => x.command === 'check').length;
    const code = await runCheck({ words, options: { '--json': true, ...options }, cwd: fixture.repo, cache: true }, ports);
    assert.equal(code, 0, ports.stderr.text);
    return { sent: fake.posts.filter(x => x.command === 'check').length - before, json: JSON.parse(ports.stdout.text), text: ports.stdout.text + ports.stderr.text };
  };
  return { ...fixture, ports, clock, invoke, identity: x => { identity = x; }, answerEdit: fn => { answerEdit = fn; } };
}
async function prime(ctx) { assert.equal((await ctx.invoke()).sent, 3); }
function changeIndependent(ctx) {
  const path = join(ctx.repo, 'tests/independent.json'), doc = read(path); doc.initial_world.changed = true; write(path, doc);
}

for (const delta of [1, 0, -1]) test(`TEST-CACHE-V3 seven-day boundary ${delta}`, async t => {
  const ctx = await setup(t); await prime(ctx);
  ctx.clock.now += 7 * day + delta;
  const result = await ctx.invoke();
  assert.equal(result.sent, delta > 0 ? 3 : 0, 'seven days inclusive, older evidence reruns');
  if (delta <= 0) { ctx.clock.now += 2; assert.equal((await ctx.invoke()).sent, 3, 'boundary pass expires rather than refreshing on reuse'); }
});
for (const ci of ['', '0', 'true']) test(`TEST-CACHE-V3 CI present ${JSON.stringify(ci)}`, async t => {
  const ctx = await setup(t); await prime(ctx); ctx.ports.env.CI = ci;
  assert.equal((await ctx.invoke(['independent'])).sent, 1, 'CI presence runs selected scope');
});
for (const missing of ['engine', 'model', 'unknown-model', 'conflicting-model']) test(`TEST-CACHE-V3 missing identity ${missing}`, async t => {
  const ctx = await setup(t);
  ctx.answerEdit(job => {
    if (missing === 'engine') delete job.engine_sha;
    else if (missing === 'model') { delete job.usage.requested_model; delete job.result.report.evaluation.requested_model; }
    else if (missing === 'unknown-model') { job.usage.requested_model = 'unknown'; job.result.report.evaluation.requested_model = 'unknown'; }
    else job.result.report.evaluation.requested_model = 'conflicting-model';
    return job;
  });
  await prime(ctx); assert.equal((await ctx.invoke()).sent, 3, 'unknown or inconsistent identity cannot authorize reuse');
});
for (const part of ['engine', 'model']) test(`TEST-CACHE-V3 same-run ${part} change redispatches skipped Stories`, async t => {
  const ctx = await setup(t); await prime(ctx); changeIndependent(ctx);
  ctx.identity({ engine_sha: (part === 'engine' ? 'b' : 'a').repeat(40), requested_model: part === 'model' ? 'synthetic-model-B' : 'synthetic-model-A' });
  const result = await ctx.invoke();
  assert.equal(result.sent, 3, 'new answer identity reruns both skipped Stories in the same command');
  assert.equal(result.json.rows.length, 3); assert.ok(result.json.rows.every(row => !row.cached));
  assert.match(result.text, /runs again: interpreter build or model changed/);
  assert.ok(result.json.rows.filter(row => row.test !== 'tests/independent.json').every(row => row.cache_reason === 'runs again: interpreter build or model changed'));
  assert.equal((await ctx.invoke()).sent, 0, 'new consistent identity is reusable');
});

for (const kind of ['http', 'command', 'model', 'port']) test(`TEST-CACHE-V3 ${kind} default always runs`, async t => {
  const ctx = await setup(t, repo => editPrompt(repo, doc => { doc.resources = [resource(kind)]; }));
  await prime(ctx); const result = await ctx.invoke();
  assert.equal(result.sent, 2, 'only Stories reaching the AI-played resource rerun');
  assert.match(result.text, /runs every time: uses an AI-played fake \(gcloud\)/);
  assert.ok(result.json.rows.filter(row => row.test !== 'tests/independent.json').every(row => row.cache_reason === 'runs every time: uses an AI-played fake (gcloud)'));
});
for (const action of ['fixture.lookup', 'port.write', 'collection.get', 'blob.read', 'sql.execute']) test(`TEST-CACHE-V3 complete deterministic ${action} then unbound operation`, async t => {
  const ctx = await setup(t, repo => {
    editPrompt(repo, doc => { doc.resources = [resource('port')]; });
    const path = join(repo, 'tests/place-order.json'), doc = read(path);
    doc.simulation = { 'gcloud.call': action === 'fixture.lookup' ? { action, cases: [{ call_index: 1, args: {}, result: {} }] } : { action, result_template: {}, world_pointer: '/store' } };
    write(path, doc);
  });
  assert.equal((await ctx.invoke(['tests/place-order.json'])).sent, 1);
  // Determinism is per test: fixing one Story cannot bless another reaching the resource.
  const result = await ctx.invoke(); assert.equal(result.sent, 2);
  const repeat = await ctx.invoke(); assert.equal(repeat.sent, 1, 'unbound Story still runs; deterministic Story reuses');
  assert.match(repeat.text, /runs every time: uses an AI-played fake \(gcloud\)/);
});
for (const fixed of [undefined, 0, '2026-10-31T12:00:00Z']) test(`TEST-CACHE-V3 clock fixed ${JSON.stringify(fixed)}`, async t => {
  const ctx = await setup(t, repo => {
    editPrompt(repo, doc => { doc.resources = [resource('port', 'clock', ['now'])]; });
    if (fixed !== undefined) {
      const path = join(repo, 'tests/place-order.json'), doc = read(path); doc.initial_world.clock = { now: fixed }; write(path, doc);
    }
  });
  await prime(ctx); const result = await ctx.invoke();
  assert.equal(result.sent, fixed === undefined ? 2 : 1, 'a fixed clock permits only its own Story to reuse');
  assert.match(result.text, /runs every time: uses the real clock/);
});
for (const action of ['http.prompt', 'port.prompt']) test(`TEST-CACHE-V3 level-three ${action}`, async t => {
  const ctx = await setup(t, repo => {
    editPrompt(repo, doc => { doc.resources = [resource('port')]; });
    const path = join(repo, 'tests/place-order.json'), doc = read(path); doc.simulation = { 'gcloud.call': { action, target: 'prompts/independent.prompt.md' } }; write(path, doc);
  });
  await prime(ctx); const result = await ctx.invoke(); assert.equal(result.sent, 2);
  assert.match(result.text, /runs every time: uses an AI-played fake \(gcloud\)/);
});
test('TEST-CACHE-V3 reached fake prompt always runs', async t => {
  const ctx = await setup(t, repo => {
    mkdirSync(join(repo, 'prompts/fakes'));
    writeFileSync(join(repo, 'prompts/fakes/gcloud.prompt.md'), readFileSync(join(repo, 'prompts/independent.prompt.md')));
    editPrompt(repo, doc => { doc.calls = [{ operation: 'fake', target: 'prompts/fakes/gcloud.prompt.md', target_operation: 'place_order', max_calls: 1 }]; });
  });
  await prime(ctx); const result = await ctx.invoke(); assert.equal(result.sent, 2);
  assert.match(result.text, /runs every time: uses an AI-played fake \(gcloud\)/);
});

for (const fixed of [0, '2026-10-31T12:00:00Z']) test(`TEST-CACHE-V3 all clocks fixed ${JSON.stringify(fixed)} expire`, async t => {
  const ctx = await setup(t, repo => {
    editPrompt(repo, doc => { doc.resources = [resource('port', 'clock', ['now'])]; });
    for (const name of ['place-order', 'unknown-item']) {
      const path = join(repo, `tests/${name}.json`), doc = read(path); doc.initial_world.clock = { now: fixed }; write(path, doc);
    }
  });
  await prime(ctx); assert.equal((await ctx.invoke()).sent, 0, 'fixed now, including zero, permits reuse');
  ctx.clock.now += 7 * day + 1; assert.equal((await ctx.invoke()).sent, 3, 'fixed resources do not waive age guard');
});
for (const action of ['fixture.lookup', 'port.write']) test(`TEST-CACHE-V3 all operations deterministic ${action} expire`, async t => {
  const ctx = await setup(t, repo => {
    editPrompt(repo, doc => { doc.resources = [resource('port')]; });
    for (const name of ['place-order', 'unknown-item']) {
      const path = join(repo, `tests/${name}.json`), doc = read(path);
      doc.simulation = { 'gcloud.call': action === 'fixture.lookup' ? { action, cases: [{ call_index: 1, args: {}, result: {} }] } : { action, result_template: {} } }; write(path, doc);
    }
  });
  await prime(ctx); assert.equal((await ctx.invoke()).sent, 0, 'fully deterministic supplied replies permit reuse');
  ctx.clock.now += 7 * day + 1; assert.equal((await ctx.invoke()).sent, 3);
});
test('TEST-CACHE-V3 conflicting sibling identities never authorize a complete pass', async t => {
  const ctx = await setup(t, repo => {
    const doc = read(join(repo, 'tests/place-order.json')); write(join(repo, 'tests/place-order-extra.json'), doc);
  });
  let answer = 0;
  ctx.answerEdit(job => { job.engine_sha = (++answer % 2 ? 'a' : 'b').repeat(40); return job; });
  assert.equal((await ctx.invoke(['place-order'])).sent, 2);
  assert.equal((await ctx.invoke(['place-order'])).sent, 2, 'mixed interpreter identities cannot combine into one reusable Story');
});
