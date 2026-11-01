import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { exitCodeFor, projectAnswer, renderText, summaryLine } from '../src/runtime-output.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const TEST = 'tests/place-order.json';
const refusal = { code: 'admission-stopped', message: 'Admission stopped before this test.', fix: 'Correct the admission input.' };
const running = { steps_done: 2, steps_total: 5, step: 3, calls_settled: 4, calls_open: 1 };
const progressText = 'running · step 3 of 5 · 4 AI calls so far · 1 in flight';
function lintAnswer(f, id, shape) {
  const answer = f.lint(id);
  answer.result.report.lint = { complete: true, tests: [{ path: TEST, verdict: 'passed' }] };
  switch (shape) {
    case 'refused':
      answer.state = answer.result.report.verdict = 'refused';
      answer.result.report.refusal = refusal; answer.result.refusals = [refusal];
      answer.result.report.lint = { complete: false, tests: [] }; break;
    case 'raw-refusal':
      answer.result.report.refusal = refusal;
      answer.result.report.lint = { complete: false, tests: [] }; break;
    case 'incomplete': answer.result.report.lint.complete = false; break;
    case 'missing-verdict': answer.result.report.lint.tests = []; break;
    case 'empty': return f.job(id, 'lint', 'passed', {});
    case 'no-prompts': delete answer.result.report.program.prompts;
      answer.result.report.lint = { complete: false, tests: [] }; break;
    case 'unrelated': case 'unrelated-no-verdict':
      answer.state = answer.result.report.verdict = 'refused';
      answer.result.refusals = [{ code: 'unrelated-input', message: 'An unselected test has invalid input.', file: 'tests/other.json' }];
      answer.result.problems = [{ code: 'unrelated-input', file: 'tests/other.json', message: 'An unselected test has invalid input.', severity: 'error' }];
      if (shape === 'unrelated-no-verdict') answer.result.report.lint.tests = [];
  }
  return answer;
}
async function setup(t, shape, { pending = false, check = 'passed', progress } = {}) {
  const h = harbor(t);
  let done = !pending;
  const f = await fakeRuntime(t, (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.command === 'lint' || f.posts.some(p => p.command === 'lint' && p.request.requestId === id))
      return { status: 200, json: done ? lintAnswer(f, id, shape) : f.job(id, 'lint', 'running') };
    let answer = f.check(id, check);
    if (check === 'running') { answer.progress = progress; answer.usage.calls = 'unknown'; }
    if (check === 'pool') {
      const pool = { code: 'pool-copy-unavailable', message: 'No model login is available.', details: { retryable: true } };
      answer = f.job(id, 'check', 'refused', { refusals: [pool], report: { dispatch: 'not_started', refusal: pool } });
    }
    return { status: 200, json: answer };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  const command = async (options = {}, words = ['place-order']) => {
    const p = portsFor(env);
    const code = await runCheck({ cwd: h.repo, words, options }, p.ports);
    return { code, ...p, out: p.ports.stdout.text, err: p.ports.stderr.text, json: options['--json'] && p.ports.stdout.text ? JSON.parse(p.ports.stdout.text) : null };
  };
  return { h, f, command, finish() { done = true; } };
}

for (const [shape, code, state] of [
  ['passed', 0, 'passed'], ['refused', 4, 'refused'], ['raw-refusal', 4, 'refused'],
  ['incomplete', 3, 'unknown'], ['missing-verdict', 3, 'unknown'], ['empty', 3, 'unknown'],
  ['no-prompts', 3, 'unknown'], ['unrelated', 0, 'passed'], ['unrelated-no-verdict', 4, 'refused'],
]) test(`OUTCOME explicit lint: ${shape}`, async t => {
  const r = await setup(t, shape);
  let result;
  await assert.doesNotReject(async () => { result = await r.command({ '--lint': true, '--json': true }); }, 'a malformed program must yield an outcome without throwing');
  assert.equal(result.code, code, result.err);
  assert.equal(result.json.lint_state, state);
  assert.equal(result.json.rows[0]?.state, state, 'selected row must be present, including unknown');
  assert.equal(r.f.posts.filter(p => p.command === 'check').length, 0);
  if (state !== 'passed') assert.doesNotMatch(result.json.summary_line, /1 of 1 tests pass/);
  if (shape === 'refused' || shape === 'raw-refusal') assert.match(JSON.stringify(result.json), /admission-stopped/);
  if (shape === 'incomplete') assert.match(JSON.stringify(result.json), /lint did not finish/);
  if (shape === 'unrelated') assert.ok(result.json.problems.some(p => p.code === 'unrelated-input'));
  assert.doesNotMatch(result.err, /internal error|not iterable/i);
});

for (const shape of ['refused', 'raw-refusal', 'incomplete', 'empty', 'missing-verdict', 'unrelated-no-verdict'])
  test(`OUTCOME new checks stop at ${shape} lint`, async t => {
    const r = await setup(t, shape);
    const result = await r.command({ '--json': true });
    assert.equal(r.f.posts.filter(p => p.command === 'check').length, 0, 'no paid POST');
    assert.equal(result.json.rows[0].calls, 0);
    assert.doesNotMatch(result.err, /Lint passed/);
    assert.ok([3, 4].includes(result.code));
  });

for (const retry of [false, true]) for (const shape of ['refused', 'incomplete', 'unrelated', 'unrelated-no-verdict'])
  test(`OUTCOME ${retry ? 'retry' : 'continuation'} gate: ${shape}`, async t => {
    const r = await setup(t, shape, { pending: true });
    const first = await r.command({ '--json': true });
    assert.equal(first.code, 3);
    r.finish();
    const result = await r.command({ '--json': true, [retry ? '--retry' : '--read']: first.json.batch }, []);
    assert.equal(r.f.posts.filter(p => p.command === 'check').length, shape === 'unrelated' ? 1 : 0);
    if (shape === 'unrelated') { assert.equal(result.code, 0, result.err); assert.match(result.out + result.err, /unrelated-input/); }
  });

for (const shape of ['refused', 'incomplete', 'unrelated-no-verdict']) test(`OUTCOME a new Try uses the same lint gate: ${shape}`, async t => {
  const r = await setup(t, shape);
  const p = portsFor({ HOME: r.h.home, PDD_STATE_DIR: r.h.state, PDD_RUNTIME_URL: r.f.origin }, { openUrl: async () => true });
  const code = await runTry({ cwd: r.h.repo, words: ['place-order'], options: { '--no-open': true } }, p.ports);
  assert.equal(r.f.posts.filter(post => post.command === 'try').length, 0, 'no Try setup is sent');
  assert.equal(code, shape === 'incomplete' ? 3 : 4);
  assert.doesNotMatch(p.ports.stdout.text + p.ports.stderr.text, /Lint passed/);
});

test('OUTCOME retry rechecks saved per-test lint evidence', async t => {
  const r = await setup(t, 'passed');
  const first = await r.command({ '--json': true });
  const folder = join(r.h.state, 'batches', first.json.batch), path = join(folder, 'batch.json');
  const saved = JSON.parse(readFileSync(path)), lintId = saved.lint.request_ids.at(-1);
  const answer = lintAnswer(r.f, lintId, 'incomplete');
  writeFileSync(join(folder, `${lintId}.json`), JSON.stringify(answer));
  Object.assign(saved.rows[0], { request_ids: [], state: 'not_run', phase: 'lint', calls: 0, can_retry: true, eligible: true });
  writeFileSync(path, JSON.stringify(saved));
  const count = r.f.posts.filter(p => p.command === 'check').length;
  await r.command({ '--retry': first.json.batch, '--json': true }, []);
  assert.equal(r.f.posts.filter(p => p.command === 'check').length, count, 'incomplete saved evidence cannot authorize a paid retry');
});

test('OUTCOME empty results cannot succeed or imply criterion passes', () => {
  assert.equal(exitCodeFor([]), 3);
  assert.match(summaryLine([{ state: 'passed', story: 'one', criteria_total: 3 }]), /0 of 3 criteria/);
});

test('OUTCOME retryable unstarted pool answer is not run in every output', async t => {
  const r = await setup(t, 'passed', { check: 'pool' });
  const result = await r.command({ '--json': true });
  assert.equal(result.code, 5);
  assert.equal(result.json.rows[0].state, 'not_run');
  assert.match(JSON.stringify(result.json), /No model login is available/);
  assert.doesNotMatch(result.json.summary_line, /✗|refused/);
  const text = renderText({ rows: result.json.rows, exitCode: 5 });
  assert.match(text, /NOT RUN/); assert.doesNotMatch(text, /REFUSED|✗/);
});

test('OUTCOME supplied progress reaches table, summary, stderr and saved reads', async t => {
  const r = await setup(t, 'passed', { check: 'running', progress: running });
  const result = await r.command({ '--json': true });
  assert.equal(result.code, 3);
  assert.deepEqual(result.json.rows[0].progress, running);
  assert.match(result.json.summary_line, /running · step 3 of 5 · 4 AI calls so far · 1 in flight/);
  assert.ok(result.err.includes(progressText), result.err);
  assert.ok(renderText({ rows: result.json.rows, exitCode: 3 }).includes(progressText));
  const next = await r.command({ '--read': result.json.batch, '--json': true }, []);
  assert.deepEqual(next.json.rows[0].progress, running);
});

test('OUTCOME partial progress never invents a call or step number', async t => {
  const r = await setup(t, 'passed', { check: 'running', progress: { step: 'prepare' } });
  const result = await r.command({ '--json': true });
  assert.match(result.json.summary_line, /running · prepare/);
  assert.doesNotMatch(result.err, /0 AI calls so far|step \d+ of/);
});

test('OUTCOME projection preserves queued and failed evidence', () => {
  assert.equal(projectAnswer({ command: 'check', state: 'queued', queue: { ahead: 2 } }).state, 'queued');
  assert.equal(exitCodeFor([{ state: 'failed' }]), 1);
  assert.equal(exitCodeFor([{ state: 'refused' }]), 4);
  assert.equal(exitCodeFor([{ state: 'running' }]), 3);
});
