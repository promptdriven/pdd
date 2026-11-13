import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runTry } from '../../src/runtime-seam.mjs';
import { exitCodeFor, projectAnswer, renderText, summaryLine } from '../../src/runtime-seam.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const TEST = 'tests/place-order.json';
const refusal = { code: 'admission-stopped', message: 'Admission stopped before this test.', fix: 'Correct the admission input.' };
const running = { steps_done: 2, steps_total: 5, step: 3, calls_settled: 4, calls_open: 1 };
const progressText = 'sent (timeout-flag) · step 3 of 5 · 4 AI calls so far · 1 not yet settled';
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
    // The lint ended before this test: the server marks it not-checked.
    case 'incomplete': answer.result.report.lint = { complete: false, tests: [{ path: TEST, verdict: 'not-checked' }] }; break;
    // The lint ended before another test; this test has its own pass.
    case 'incomplete-own-pass': answer.result.report.lint = { complete: false, tests: [{ path: TEST, verdict: 'passed' }, { path: 'tests/other.json', verdict: 'not-checked' }] }; break;
    // The status view's public list (result.tests, problems_complete) with no report.lint.
    case 'public-tests': delete answer.result.report.lint; Object.assign(answer.result, { tests: [{ path: TEST, verdict: 'passed', problems: 0 }], problems_complete: true }); break;
    // A raw refusal of the selected test with no message text.
    case 'bare-refusal': answer.state = 'refused'; answer.result.report.lint = { complete: true, tests: [] };
      answer.result.refusals = [{ code: 'interface-missing', file: TEST, reason: 'The test names a prompt with no Runtime interface.' }]; break;
    case 'missing-verdict': answer.result.report.lint.tests = []; break;
    case 'both': answer.result.report.lint.tests.push({ path: 'tests/unknown-item.json', verdict: 'passed' }); break;
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
    // A retryable refusal before dispatch, declared on the record (login queue) or in its details (pool copy).
    if (check === 'pool' || check === 'login-queue') {
      const refusal = check === 'pool' ? { code: 'pool-copy-unavailable', message: 'No model login is available.', details: { retryable: true } }
        : { code: 'login-queue-timeout', message: 'Waited too long for a model login.', retryable: true };
      answer = f.job(id, 'check', 'refused', { refusals: [refusal], report: { dispatch: 'not_started', refusal } });
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

// An ended lint without a pass for the test is final: not run, exit 5 (exit 3 means "read again").
for (const [shape, code, state] of [
  ['passed', 0, 'passed'], ['refused', 4, 'refused'], ['raw-refusal', 4, 'refused'], ['bare-refusal', 4, 'refused'],
  ['incomplete', 5, 'not run'], ['missing-verdict', 5, 'not run'], ['empty', 5, 'not run'], ['no-prompts', 5, 'not run'],
  ['incomplete-own-pass', 0, 'passed'], ['public-tests', 0, 'passed'], ['unrelated', 0, 'passed'], ['unrelated-no-verdict', 4, 'refused'],
]) test(`OUTCOME explicit lint: ${shape}`, async t => {
  const r = await setup(t, shape);
  let result;
  await assert.doesNotReject(async () => { result = await r.command({ '--lint': true, '--json': true }); }, 'a malformed program must yield an outcome without throwing');
  assert.equal(result.code, code, result.err);
  assert.equal(result.json.lint_state, state);
  assert.equal(result.json.rows[0]?.state, state, 'selected row must be present, including unknown');
  assert.equal(r.f.posts.filter(p => p.command === 'check').length, 0);
  if (state !== 'passed') assert.doesNotMatch(result.json.summary_line, /1 of 1 tests pass/);
  if (shape === 'refused' || shape === 'raw-refusal') assert.match(JSON.stringify(result.json), /admission-stopped[\s\S]*Admission stopped before this test\./);
  if (shape === 'incomplete') assert.match(JSON.stringify(result.json.rows[0].reason), /lint did not finish/);
  if (shape === 'missing-verdict') assert.match(JSON.stringify(result.json.rows[0].reason), /lint gave no verdict for this test/);
  if (shape === 'unrelated') assert.ok(result.json.problems.some(p => p.code === 'unrelated-input'));
  assert.doesNotMatch(result.err, /internal error|not iterable/i);
});

for (const shape of ['refused', 'raw-refusal', 'bare-refusal', 'incomplete', 'empty', 'missing-verdict', 'unrelated-no-verdict'])
  test(`OUTCOME new checks stop at ${shape} lint`, async t => {
    const r = await setup(t, shape);
    const result = await r.command({ '--json': true });
    assert.equal(r.f.posts.filter(p => p.command === 'check').length, 0, 'no paid POST');
    assert.equal(result.json.rows[0].calls, 0);
    assert.doesNotMatch(result.err, /Lint passed/);
    assert.equal(result.code, result.json.rows[0].state === 'refused' ? 4 : 5, 'an ended lint is final');
  });

test('OUTCOME a test with its own pass is sent although the lint did not finish for another test', async t => {
  const r = await setup(t, 'incomplete-own-pass');
  const result = await r.command({ '--json': true });
  assert.deepEqual(r.f.posts.filter(p => p.command === 'check').map(p => p.request.scenario), [TEST]);
  assert.equal(result.code, 0, result.err);
});

for (const retry of [false, true]) for (const shape of ['refused', 'incomplete', 'unrelated', 'unrelated-no-verdict'])
  test(`OUTCOME ${retry ? 'retry' : 'continuation'} gate: ${shape}`, async t => {
    const r = await setup(t, shape, { pending: true });
    const first = await r.command({ '--json': true, '--timeout': 1 });
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
  // An ended lint without a pass for the test is final for a Try too: not run, exit 5, with the reason.
  assert.equal(code, shape === 'incomplete' ? 5 : 4);
  if (shape === 'incomplete') assert.match(p.ports.stderr.text, /No lint pass for this test \(lint did not finish\), so pdd made no Try link\./);
  assert.doesNotMatch(p.ports.stdout.text + p.ports.stderr.text, /Lint passed|again later/);
});

// Scope, not ignore: one test without a lint pass never stops a test that has one.
for (const pending of [false, true]) test(`OUTCOME ${pending ? 'continuation' : 'new checks'}: a test without a verdict is not sent; a passing one is`, async t => {
  const r = await setup(t, 'passed', { pending });
  const first = await r.command({ '--json': true, ...(pending ? { '--timeout': 1 } : {}) }, ['place-order', 'unknown-item']);
  r.finish();
  const result = pending ? await r.command({ '--json': true, '--read': first.json.batch }, []) : first;
  assert.deepEqual(r.f.posts.filter(post => post.command === 'check').map(post => post.request.scenario), [TEST]);
  assert.deepEqual(result.json.rows.map(row => row.state), ['passed', 'not run']);
  assert.equal(result.json.rows[1].calls, 0);
  assert.match(result.json.rows[1].reason.message, /No lint pass for this test \(lint gave no verdict for this test\)/);
  assert.equal(result.code, 5, 'an ended lint without a verdict is final');
  if (pending) {
    const again = await r.command({ '--json': true, '--read': first.json.batch }, []);
    assert.equal(again.code, 5); assert.equal(r.f.posts.filter(post => post.command === 'check').length, 1);
  }
});

// --retry: a busy, unstarted check is sent again only when its saved lint gives it a pass of its own.
for (const saved of ['passed', 'not-checked']) test(`OUTCOME retry gate on a busy unstarted check: saved verdict ${saved}`, async t => {
  const h = harbor(t);
  let busy = true, now;
  const f = await fakeRuntime(t, (e, f) => e.command === 'check' && busy ? { status: 503, headers: { 'retry-after': '300' },
    json: { dispatch: 'not_started', provider_calls: 0, accounting_complete: true,
      usage: { calls: 0, known_calls: 0, unknown_calls: 0, provider_calls: 0, accounting_complete: true },
      error: { code: 'check-queue-full', details: { retryable: true, retry_after: 300 } } } } : f.normal(e));
  const run = async options => {
    const p = portsFor({ HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin });
    if (now) p.clock.now = now;
    const code = await runCheck({ cwd: h.repo, words: options['--retry'] ? [] : ['place-order'], options }, p.ports);
    now = p.clock.now;
    return { code, err: p.ports.stderr.text, json: p.ports.stdout.text.startsWith('{') ? JSON.parse(p.ports.stdout.text) : null };
  };
  const first = await run({ '--json': true, '--timeout': 1 });
  assert.equal(first.code, 5); assert.equal(first.json.rows[0].can_retry, true);
  const folder = join(h.state, 'batches', first.json.batch), lintId = JSON.parse(readFileSync(join(folder, 'batch.json'))).lint.request_ids.at(-1);
  const answer = JSON.parse(readFileSync(join(folder, `${lintId}.json`)));
  answer.result.report.lint = { complete: saved === 'passed', tests: [{ path: TEST, verdict: saved }] };
  writeFileSync(join(folder, `${lintId}.json`), JSON.stringify(answer));
  busy = false; now += 400_000;
  const sent = f.posts.filter(p => p.command === 'check').length;
  const retry = await run({ '--retry': first.json.batch, '--json': true });
  assert.equal(f.posts.filter(p => p.command === 'check').length - sent, saved === 'passed' ? 1 : 0, retry.err);
  assert.equal(retry.code, saved === 'passed' ? 0 : 2, retry.err);
});

test('OUTCOME empty results cannot succeed or imply criterion passes', () => {
  assert.equal(exitCodeFor([]), 3);
  // A passed row without per-criterion results says so; it never counts its criteria either way.
  const line = summaryLine([{ state: 'passed', story: 'one', criteria_total: 3 }]);
  assert.match(line, /: ✓ passed · criteria details not reported · /);
  assert.doesNotMatch(line, /\d+ of 3 criteria/);
  assert.equal(
    summaryLine([{ state: 'passed', story: 'one', criteria_total: 3 }], 'one'),
    'Prompt tests (one): ✓ passed · criteria details not reported · 0/0 checks · 0 AI calls'
  );
  const mixed = summaryLine([{ state: 'passed', story: 'one', criteria_total: 3 }, { state: 'passed', story: 'one', criteria_total: 2, criteria: { passed: 2, total: 2 } }]);
  assert.match(mixed, /: ✓ 2 of 2 criteria · criteria details not reported · /);
  // A row that is not passed and has no criterion_results counts its test's criteria (criteria_total, or 0 when absent), with 0 passed.
  assert.equal(
    summaryLine([{ state: 'refused', story: 'place-order', criteria_total: 3 }], 'place-order'),
    'Prompt tests (place-order): no verdict · 0 of 3 criteria · 0/0 checks · 1 refused (admission-refused) · 0 AI calls'
  );
  assert.equal(
    summaryLine([{ state: 'running', phase: 'server', story: 'place-order', criteria_total: 3 }], 'place-order'),
    'Prompt tests (place-order): running · 0 of 3 criteria · 0/0 checks · 1 sent (awaiting-server-verdict) · 0 AI calls + 1 unknown'
  );
  assert.equal(
    summaryLine([
      { state: 'passed', story: 'one', criteria: { passed: 1, total: 1 }, checks: { passed: 1, total: 1 }, phase: 'server', calls: 1 },
      { state: 'refused', story: 'two', criteria_total: 3 }
    ]),
    'Prompt tests: no verdict · 1 of 4 criteria · 1/1 checks · 1 refused (admission-refused) · 1 AI call'
  );
  for (const [state, suffix] of [
    ['not_run', 'no verdict · 0 of 3 criteria · 0/0 checks · 1 not run (no-server-verdict) · 0 AI calls'],
    ['unknown', 'no verdict · 0 of 3 criteria · 0/0 checks · 1 partial (no-server-verdict) · 0 AI calls'],
    ['failed', '✗ 0 of 3 criteria · 0/0 checks · 1 failed (check-failed) · 0 AI calls']
  ]) {
    assert.equal(summaryLine([{ state, story: 'place-order', criteria_total: 3 }], 'place-order'), `Prompt tests (place-order): ${suffix}`);
  }
});

test('OUTCOME formal check: summaryLine criterion counting across row states and criteria shapes', () => {
  const states = ['passed', 'failed', 'refused', 'not_run', 'unknown', 'queued', 'running'];
  const criteriaShapes = [undefined, { passed: 0, total: 2 }, { passed: 2, total: 2 }];
  const totals = [undefined, 0, 3];
  const companions = [
    null,
    { state: 'passed', story: 'two', criteria: { passed: 1, total: 1 }, criteria_total: 1 },
    { state: 'passed', story: 'two', criteria_total: 4 },
    { state: 'refused', story: 'two', criteria_total: 4 },
    { state: 'running', phase: 'server', story: 'two', criteria_total: 2 }
  ];
  let checked = 0;
  for (const state of states) {
    for (const criteria of criteriaShapes) {
      for (const criteria_total of totals) {
        for (const companion of companions) {
          const first = {
            state,
            story: 'one',
            ...(state === 'running' ? { phase: 'server' } : {}),
            ...(criteria ? { criteria } : {}),
            ...(criteria_total !== undefined ? { criteria_total } : {})
          };
          const rows = companion ? [first, companion] : [first];
          const unreported = row => row.state === 'passed' && !row.criteria;
          const countedRows = rows.filter(row => !unreported(row));
          const notReported = rows.some(unreported);
          const expectedPassed = countedRows.reduce((sum, row) => sum + (row.criteria ? row.criteria.passed : 0), 0);
          const expectedTotal = countedRows.reduce((sum, row) => sum + (row.criteria ? row.criteria.total : (row.criteria_total ?? 0)), 0);
          const expectedFragment = countedRows.length === 0 && notReported
            ? 'passed · criteria details not reported'
            : `${expectedPassed} of ${expectedTotal} ${expectedTotal === 1 ? 'criterion' : 'criteria'}${notReported ? ' · criteria details not reported' : ''}`;
          const actual = summaryLine(rows);
          assert.ok(
            actual.includes(` ${expectedFragment} · `),
            `rows=${JSON.stringify(rows)} expected fragment "${expectedFragment}" in "${actual}"`
          );
          checked += 1;
        }
      }
    }
  }
  assert.equal(checked, 315);
});

for (const [check, code, said] of [['pool', 'pool-copy-unavailable', /No model login is available/], ['login-queue', 'login-queue-timeout', /Waited too long for a model login/]])
test(`OUTCOME a retryable refusal before dispatch is not run in every output, whatever its code: ${code}`, async t => {
  const r = await setup(t, 'passed', { check });
  const result = await r.command({ '--json': true });
  assert.equal(result.code, 5);
  assert.equal(result.json.rows[0].state, 'not run');
  assert.equal(result.json.rows[0].reason?.code, 'server-busy');
  assert.ok(result.json.rows[0].refusals.some(item => item.code === code), 'retain the server code');
  assert.match(JSON.stringify(result.json), said);
  assert.equal(result.json.rows[0].reason.message, check === 'pool' ? 'No model login is available.' : 'Waited too long for a model login.');
  assert.equal(result.json.rows[0].refusals[0].code, code);
  assert.equal(result.json.rows[0].calls, 0);
  assert.ok(result.json.rows[0].request_id);
  assert.ok(result.json.rows[0].report_url);
  const read = await r.command({ '--read': true }, [result.json.batch]);
  assert.match(read.out, /Not run: PDD stayed busy, so your check did not start\. Nothing was charged\. Try again in a few minutes: pdd test place-order/);
  assert.doesNotMatch(read.out, /interpreter|slot|pool|model|login|account|Why:|Next:/i);
  assert.equal(r.f.posts.filter(post => post.command === 'check').length, 1);
  assert.doesNotMatch(result.json.summary_line, /✗|refused/);
  const text = renderText({ rows: result.json.rows, exitCode: 5 });
  assert.match(text, /NOT RUN/); assert.doesNotMatch(text, /REFUSED|✗/);
});

test('OUTCOME supplied progress reaches table, summary, stderr and saved reads', async t => {
  const r = await setup(t, 'passed', { check: 'running', progress: running });
  const result = await r.command({ '--json': true, '--timeout': 1 });
  assert.equal(result.code, 3);
  assert.deepEqual(result.json.rows[0].progress, running);
  assert.match(result.json.summary_line, /sent \(timeout-flag\) · step 3 of 5 · 4 AI calls so far · 1 not yet settled/);
  assert.match(result.err, /sent \(awaiting-server-verdict\).*step 3 of 5/);
  assert.ok(renderText({ rows: result.json.rows, exitCode: 3 }).includes(progressText));
  const next = await r.command({ '--read': result.json.batch, '--json': true, '--timeout': 1 }, []);
  assert.deepEqual(next.json.rows[0].progress, running);
});

test('OUTCOME several running tests share one progress part', async t => {
  const r = await setup(t, 'both', { check: 'running', progress: running });
  const result = await r.command({ '--json': true, '--timeout': 1 }, ['place-order', 'unknown-item']);
  assert.match(result.json.summary_line, /sent \(awaiting-server-verdict\) · 8 AI calls so far · 2 not yet settled · 2 sent \(timeout-flag\)$/);
  assert.equal(result.json.summary_line.split('step 3 of 5').length, 1, 'no per-row step in a shared line');
  assert.ok(result.err.split('\n').filter(line => line.startsWith('Still running:')).every(line => line.split(' · sent (awaiting-server-verdict)').length === 2), result.err);
});

test('OUTCOME partial progress never invents a call or step number', async t => {
  const r = await setup(t, 'passed', { check: 'running', progress: { step: 'prepare' } });
  const result = await r.command({ '--json': true, '--timeout': 1 });
  assert.match(result.json.summary_line, /sent \(timeout-flag\) · prepare/);
  assert.doesNotMatch(result.err, /0 AI calls so far|step \d+ of/);
});

test('OUTCOME projection preserves queued and failed evidence', () => {
  assert.equal(projectAnswer({ command: 'check', state: 'queued', queue: { ahead: 2 } }).state, 'queued');
  assert.equal(exitCodeFor([{ state: 'failed' }]), 1);
  assert.equal(exitCodeFor([{ state: 'refused' }]), 4);
  assert.equal(exitCodeFor([{ state: 'running' }]), 3);
});
