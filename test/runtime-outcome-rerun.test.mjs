import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-seam.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// The per-test lint gate also guards the Story cache's second phase: after the interpreter build or model
// changes, provisionally reused Stories run again with this invocation's lint, test by test.
// Setup as in test/test-cache-round2.test.mjs; every fixture and expectation is synthetic.
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


test('OUTCOME a rerun after an interpreter change sends only tests that pass their own lint', async t => {
  const ctx = await setup(t);
  const first = await ctx.invoke();
  assert.equal(first.code, 0, first.stderr); assert.equal(first.sent, 3);
  changeIndependent(ctx);
  ctx.state.identity.engine_sha = 'b'.repeat(40);
  const lint = ctx.fake.lint;
  ctx.fake.lint = (...args) => {
    const answer = lint(...args);
    answer.result.report.lint.tests = answer.result.report.lint.tests.map(item => item.path === 'tests/place-order.json' ? { ...item, verdict: 'refused' } : item);
    return answer;
  };
  const result = await ctx.invoke(['independent', 'place-order']);
  assert.deepEqual(ctx.fake.posts.filter(post => post.command === 'check').slice(first.sent).map(post => post.request.scenario), ['tests/independent.json'],
    'the rerun does not send a test that its lint refused');
  const row = result.json.rows.find(item => item.test === 'tests/place-order.json');
  assert.equal(row.state, 'refused'); assert.equal(row.calls, 0);
  assert.equal(result.code, 4, result.stderr);
});
