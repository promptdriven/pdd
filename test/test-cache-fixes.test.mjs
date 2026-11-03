import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';
import { interfaceBlocks, proseSha256, captureSource } from '../src/runtime-preflight.mjs';
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
for (const readMode of ['batch', 'uuid']) test(`TEST-CACHE-FIX late ${readMode} read retains original sample age`, async t => {
  const ctx = await setup(t); ctx.state.running = true;
  const started = ctx.clock.now, first = await ctx.invoke(['independent'], { '--timeout': 1 });
  assert.equal(first.code, 3); assert.equal(first.sent, 1);
  ctx.state.running = false; ctx.clock.now += 9 * day;
  const id = readMode === 'batch' ? first.json.batch : ctx.fake.posts.find(x => x.command === 'check').request.requestId;
  const result = await runCheck({ words: [id], options: { '--read': true, '--json': true }, cwd: ctx.repo, cache: true }, ctx.ports);
  assert.equal(result, 0, ctx.ports.stderr.text);
  // Day fifteen is six days after the read, but fifteen days after the sample.
  ctx.clock.now += 6 * day;
  const later = await successful(ctx, ['independent']);
  assert.equal(later.sent, 1, 'a late read must not refresh old sample evidence');
  assert.equal(later.json.rows[0].cache_reason, 'runs again: saved pass is older than seven days');
  assert.ok(started < ctx.clock.now - 7 * day);
});
for (const scenario of ['unknown-kind', 'unknown-action', 'store-prompt', 'missing-sources']) test(`TEST-CACHE-FIX wrong skip ${scenario}`, async t => {
  const ctx = await setup(t, repo => {
    if (scenario === 'unknown-kind') editPrompt(repo, doc => { doc.resources = [resource('future-store')]; });
    if (['unknown-action', 'store-prompt'].includes(scenario)) {
      editPrompt(repo, doc => { doc.resources = [resource('key-value')]; });
      const path = join(repo, 'tests/place-order.json'), doc = read(path);
      doc.simulation = { 'gcloud.call': { action: scenario === 'store-prompt' ? 'service.prompt' : 'collection.query', target: 'prompts/independent.prompt.md' } }; write(path, doc);
    }
  });
  if (scenario === 'missing-sources') ctx.ports.captureSource = (...args) => { const capture = captureSource(...args); delete capture.sources; return capture; };
  assert.equal((await successful(ctx, selected)).sent, 1);
  const again = await successful(ctx, selected);
  assert.equal(again.sent, 1, 'uncertain declarations cannot authorize a skip');
  assert.equal(again.json.rows[0].cache_reason, scenario === 'missing-sources' ? 'runs again: resource declarations unavailable' : fakeReason);
});
for (const action of ['collection.get-or-null', 'collection.merge', 'compute']) test(`TEST-CACHE-FIX documented deterministic ${action}`, async t => {
  const ctx = await setup(t, repo => {
    editPrompt(repo, doc => { doc.resources = [resource('port')]; });
    const path = join(repo, 'tests/place-order.json'), doc = read(path);
    doc.simulation = { 'gcloud.call': { action, world_pointer: '/store', result_template: {} } }; write(path, doc);
  });
  assert.equal((await successful(ctx, selected)).sent, 1);
  assert.equal((await successful(ctx, selected)).sent, 0);
});
test('TEST-CACHE-FIX sibling-only reached prompt does not poison selected test', async t => {
  const ctx = await setup(t, repo => {
    const doc = read(join(repo, 'tests/place-order.json'));
    for (const step of doc.steps) step.entry_path = 'prompts/independent.prompt.md';
    write(join(repo, 'tests/place-order.second.json'), doc);
  });
  assert.equal((await successful(ctx)).sent, 4);
  assert.equal((await successful(ctx, selected)).sent, 0);
});
test('TEST-CACHE-FIX plain prompt dependency without interface declares no resources', async t => {
  const ctx = await setup(t, repo => {
    writeFileSync(join(repo, 'prompts/style.prompt.md'), '# Writing style\nUse clear words.\n');
    appendProse(join(repo, 'prompts/place_order.prompt.md'), '- [Style](style.prompt.md), required runtime context.\n');
  });
  assert.equal((await successful(ctx, selected)).sent, 1);
  assert.equal((await successful(ctx, selected)).sent, 0);
});
for (const part of ['engine', 'model']) test(`TEST-CACHE-FIX partial conflicting ${part} blocks complete passes`, async t => {
  const ctx = await setup(t); let seen = 0;
  ctx.state.edit = job => {
    if (++seen !== 3) return;
    if (part === 'engine') { job.engine_sha = 'b'.repeat(40); delete job.usage.requested_model; delete job.result.report.evaluation.requested_model; }
    else { delete job.engine_sha; job.usage.requested_model = 'synthetic-model-B'; job.result.report.evaluation.requested_model = 'synthetic-model-B'; }
  };
  assert.equal((await successful(ctx)).sent, 3); ctx.state.edit = null;
  assert.equal((await successful(ctx)).sent, 3, 'partial identity conflict invalidates otherwise complete passes');
});
test('TEST-CACHE-FIX latest observed identity guards reuse across runs', async t => {
  const ctx = await setup(t); assert.equal((await successful(ctx)).sent, 3);
  ctx.state.identity.engine_sha = 'b'.repeat(40); changeIndependent(ctx);
  assert.equal((await successful(ctx, ['independent'])).sent, 1);
  const cache = read(join(ctx.repo, '.pdd/cache/test/stories.json'));
  assert.ok(cache.latest_identity, 'latest observed identity must be persisted');
  assert.equal(cache.latest_identity.engine_sha, 'b'.repeat(40));
  assert.ok(Number.isFinite(Date.parse(cache.latest_identity.observed_at)));
  const again = await successful(ctx);
  assert.equal(again.sent, 2, 'latest known build invalidates old build passes even without new selected source changes');
  assert.ok(again.json.rows.filter(row => row.test !== 'tests/independent.json').every(row => row.cache_reason === 'runs again: interpreter build or model changed'));
});
for (const stop of ['timeout', 'interrupt']) test(`TEST-CACHE-FIX identity rerun after ${stop} is not sent`, async t => {
  const ctx = await setup(t); assert.equal((await successful(ctx)).sent, 3);
  changeIndependent(ctx); ctx.state.identity.engine_sha = 'b'.repeat(40); ctx.state.running = true;
  if (stop === 'interrupt') ctx.ports.sleep = async ms => { ctx.clock.now += ms; ctx.clock.interrupt(); };
  const result = await ctx.invoke([], { '--json': false, ...(stop === 'timeout' ? { '--timeout': 1 } : {}) });
  assert.equal(result.code, 3); assert.equal(result.sent, 1);
  assert.equal((result.stderr.match(/Lint passed\./g) ?? []).length, 1, 'no second lint/send claim without dispatch');
  assert.doesNotMatch(result.stderr, /Sending 2 more/);
  assert.match(result.stdout, stop === 'timeout' ? /not sent: time limit reached/ : /not sent: interrupted/);
  assert.doesNotMatch(result.stdout, /Held locally|busy \(not run\)/);
  if (stop === 'timeout') assert.match(result.stderr, /Still running\. Read the results later with: pdd test --read /);
});
test('TEST-CACHE-FIX active second phase reports additional dispatch truthfully', async t => {
  const ctx = await setup(t); assert.equal((await successful(ctx)).sent, 3); changeIndependent(ctx);
  ctx.state.identity.engine_sha = 'b'.repeat(40);
  const result = await successful(ctx);
  assert.equal(result.sent, 3); assert.match(result.stderr, /Sending 2 more checks: interpreter build or model changed/);
  assert.equal((result.stderr.match(/Lint passed\./g) ?? []).length, 1);
});
for (const shape of ['legacy', 'future']) test(`TEST-CACHE-FIX ${shape} pass cannot authorize reuse`, async t => {
  const ctx = await setup(t); assert.equal((await successful(ctx, ['independent'])).sent, 1);
  const path = join(ctx.repo, '.pdd/cache/test/stories.json'), cache = read(path);
  const pass = cache.stories['user_stories/independent.md'].pass;
  if (shape === 'legacy') delete pass.requested_model;
  else pass.passed_at = new Date(ctx.clock.now + day).toISOString();
  write(path, cache);
  assert.equal((await successful(ctx, ['independent'])).sent, 1);
});
test('TEST-CACHE-FIX step prompt override beats deterministic store binding', async t => {
  const ctx = await setup(t, repo => {
    editPrompt(repo, doc => { doc.resources = [resource('key-value')]; });
    const path = join(repo, 'tests/place-order.json'), doc = read(path);
    doc.simulation = { 'gcloud.call': { action: 'fixture.lookup', cases: [{ call_index: 1, args: {}, result: {} }] } };
    doc.steps[0].simulation_overrides = { 'gcloud.call': { action: 'http.prompt', target: 'prompts/independent.prompt.md' } }; write(path, doc);
  });
  assert.equal((await successful(ctx, selected)).sent, 1);
  const repeat = await successful(ctx, selected);
  assert.equal(repeat.sent, 1); assert.equal(repeat.json.rows[0].cache_reason, fakeReason);
});
for (const value of [null, '', '   ']) test(`TEST-CACHE-FIX invalid fixed clock ${JSON.stringify(value)}`, async t => {
  const ctx = await setup(t, repo => {
    editPrompt(repo, doc => { doc.resources = [{ ...resource('port'), name: 'clock', operations: [{ ...resource('port').operations[0], name: 'now' }] }]; });
    const path = join(repo, 'tests/place-order.json'), doc = read(path); doc.initial_world.clock = { now: value }; write(path, doc);
  });
  assert.equal((await successful(ctx, selected)).sent, 1);
  const repeat = await successful(ctx, selected);
  assert.equal(repeat.sent, 1); assert.equal(repeat.json.rows[0].cache_reason, 'runs every time: uses the real clock');
});
for (const part of ['engine', 'model']) test(`TEST-CACHE-FIX partial observations preserve latest known ${part}`, async t => {
  const ctx = await setup(t); assert.equal((await successful(ctx)).sent, 3); changeIndependent(ctx);
  ctx.state.edit = job => {
    if (part === 'engine') { job.engine_sha = 'b'.repeat(40); delete job.usage.requested_model; delete job.result.report.evaluation.requested_model; }
    else { delete job.engine_sha; job.usage.requested_model = 'synthetic-model-B'; job.result.report.evaluation.requested_model = 'synthetic-model-B'; }
  };
  assert.equal((await successful(ctx, ['independent'])).sent, 1);
  ctx.state.edit = job => {
    if (part === 'engine') delete job.engine_sha;
    else { delete job.usage.requested_model; delete job.result.report.evaluation.requested_model; }
  };
  assert.equal((await successful(ctx, ['independent'])).sent, 1);
  const latest = read(join(ctx.repo, '.pdd/cache/test/stories.json')).latest_identity;
  ctx.state.edit = null;
  const repeat = await successful(ctx);
  assert.equal(repeat.sent, 3, 'later omission cannot erase a known conflicting build/model and authorize old passes');
  assert.ok(latest, 'known partial identity is persisted');
  assert.equal(latest.conflict, true, 'partial observations leave doubt instead of merging identities');
});
