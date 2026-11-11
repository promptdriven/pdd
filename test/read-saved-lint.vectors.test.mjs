import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-seam.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { harbor, fakeRuntime, portsFor, storyTest } from './runtime-fake.mjs';

// Replay the approved native draft inventory at its real public boundary.
// Real Git/capture/state and loopback transport; no Interpreter verdict is claimed.
const inventory = JSON.parse(readFileSync(new URL('./runtime/read-saved-lint-cases.json', import.meta.url)));
const standalone = inventory.standalone_read_invariants;
async function setup(t, vector, { extraStory = false } = {}) {
  const h = harbor(t, repo => { if (extraStory) storyTest(repo, 'unselected'); });
  let finished = vector.given.original_lint === 'passed; exit 0';
  const f = await fakeRuntime(t, (entry, f) => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    if (entry.command === 'check') return { status: 200, json: f.check(id) };
    if (!finished) return { status: entry.method === 'POST' ? 202 : 200, json: f.job(id, 'lint', 'running') };
    const answer = f.lint(id);
    if (vector.given.diagnostic) {
      answer.result.report.lint.tests[0].verdict = 'refused';
      answer.result.problems = [vector.given.diagnostic];
    }
    return { status: 200, json: answer };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  const invoke = async argv => {
    const p = portsFor(env), plan = parseArgv(argv);
    const code = await runCheck({ cwd: h.repo, words: plan.operands, options: plan.options }, p.ports);
    // Check the expected command outcome before decoding its JSON output.
    return { code, ...p, get json() {
      return plan.options['--json'] ? JSON.parse(p.ports.stdout.text) : null;
    } };
  };
  const isCheck = vector.given.intent === 'explicit normal Check';
  const seed = await invoke(isCheck ? ['test', 'place-order', '--max-calls', '6', '--timeout', '1', '--json']
    : ['lint', 'place-order', '--timeout', '1', '--json']);
  assert.equal(seed.code, finished ? 0 : 3, 'seed the specified original history');
  finished = true;
  const batch = readdirSync(join(h.state, 'batches'), { withFileTypes: true }).find(entry => entry.isDirectory()).name;
  const saved = () => JSON.parse(readFileSync(join(h.state, 'batches', batch, 'batch.json')));
  return { h, f, batch, seed, saved, invoke };
}

function assertRead(r, result, vector, before) {
  const expected = vector.expected, output = result.ports.stdout.text;
  assert.equal(result.code, expected.exit_code, 'saved lint uses its confirmed outcome exit');
  if (expected.row_state) assert.equal(result.json.rows[0].state, expected.row_state, 'saved lint preserves the selected outcome');
  if (expected.summary_line) {
    assert.ok(result.json ? result.json.summary_line === expected.summary_line : output.split('\n').includes(expected.summary_line),
      'saved lint retains the lint summary');
  }
  if (expected.diagnostic_preserved) {
    assert.ok(output.includes(vector.given.diagnostic.code), 'keep the refusal code');
    assert.ok(output.includes(vector.given.diagnostic.message), 'keep the canonical diagnostic message');
  }
  const posts = r.f.posts.slice(before), checks = posts.filter(entry => entry.command === 'check');
  assert.equal(posts.filter(entry => entry.command === 'lint').length, expected.new_lint_posts ?? standalone.new_lint_posts);
  assert.equal(checks.length, expected.new_check_posts ?? standalone.new_check_posts);
  const summary = JSON.parse(readFileSync(join(r.h.state, 'batches', r.batch, 'summary.json')));
  if (expected.summary_line) assert.equal(summary.summary_line, expected.summary_line, 'save the same lint summary in either output mode');
  if (expected.apply_standalone_read_invariants) {
    for (const forbidden of standalone.forbidden_text) assert.ok(!(output + result.ports.stderr.text).includes(forbidden));
    assert.ok(r.saved().rows.every(row => !row.request_ids.length), 'standalone lint never allocates a paid request');
    if (expected.exit_code === 0) {
      assert.equal(r.saved().rows[0].state, 'passed');
      assert.notEqual(r.saved().rows[0].note?.code, standalone.passing_forbidden.reason_code);
    }
  } else {
    assert.equal(checks[0].request.max_calls, expected.check_max_calls);
    assert.deepEqual(checks.map(entry => entry.request.scenario), expected.selected_tests);
    assert.equal(checks[0].request.source_sha256, r.f.posts[0].request.source_sha256);
    assert.ok(checks[0].tar.equals(r.f.posts[0].tar), 'continuation retains original source multipart');
  }
  assert.ok(output.endsWith('\n'));
  assert.equal(r.f.posts.filter(entry => entry.command === 'lint').length, 1, 'only the original lint POST');
}

for (const vector of inventory.cases) test(`SAVED-LINT vector: ${vector.id}`, async t => {
  const r = await setup(t, vector, { extraStory: true }), before = r.f.posts.length;
  const argv = ['test', '--read', r.batch, ...(vector.action.output === 'json' ? ['--json'] : [])];
  const result = await r.invoke(argv);
  assertRead(r, result, vector, before);
  const reads = r.f.gets.length, posts = r.f.posts.length;
  const again = await r.invoke(argv);
  if (vector.expected.apply_standalone_read_invariants) assertRead(r, again, vector, posts);
  assert.equal(again.code, vector.expected.exit_code);
  if (vector.expected.summary_line) assert.ok(again.json ? again.json.summary_line === vector.expected.summary_line
    : again.ports.stdout.text.split('\n').includes(vector.expected.summary_line));
  assert.equal(r.f.posts.length, posts, 'a repeated terminal read sends nothing');
  assert.equal(r.f.gets.length, reads, 'a repeated terminal read uses the saved answer');
});

for (const id of ['pending-first-pass-json', 'already-passed-text']) test(`SAVED-LINT latest batch: ${id}`, async t => {
  const vector = inventory.cases.find(item => item.id === id), r = await setup(t, vector);
  const before = r.f.posts.length;
  const result = await r.invoke(['test', '--read', ...(vector.action.output === 'json' ? ['--json'] : [])]);
  assertRead(r, result, vector, before);
});

for (const reply of ['running', 'wrong-id']) test(`SAVED-LINT unresolved control: ${reply}`, async t => {
  const vector = inventory.cases.find(item => item.id === 'pending-first-pass-json'), r = await setup(t, vector);
  const terminal = r.f.lint;
  r.f.lint = id => reply === 'running' ? r.f.job(id, 'lint', 'running') : terminal('00000000-0000-4000-8000-000000000000');
  const posts = r.f.posts.length;
  const result = await r.invoke(['test', '--read', r.batch, '--timeout', '1', '--json']);
  assert.equal(result.code, 3, 'unresolved lint remains pending/unknown');
  assert.equal(result.json.rows[0].state, 'not run');
  assert.equal(result.json.rows[0].calls, 0);
  assert.equal(r.f.posts.length, posts, 'unresolved lint cannot send a lint or Check');
  assert.ok(r.saved().rows.every(row => !row.request_ids.length));
});
