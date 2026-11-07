import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { jsonRow, summaryLine, renderText } from '../src/runtime-output.mjs';
import { outcomeFor } from '../src/runtime-outcome.mjs';
import { readRunResults, resultLines } from '../src/workflow-results.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const cases = JSON.parse(readFileSync(new URL('./fixtures/named-check-states/results.json', import.meta.url)));
const row = input => ({ story: 'place-order', title: 'Order', test: 'tests/place-order.json', request_ids: [], refusals: [], warnings: [], phase: 'server', ...input });
const envFor = (h, f) => ({ HOME: h.home, PDD_STATE_DIR: h.state, ...(f ? { PDD_RUNTIME_URL: f.origin } : {}) });
const savedBatch = (h, batch) => JSON.parse(readFileSync(join(h.state, 'batches', batch, 'batch.json')));

test('named states: fixtures give one state and a reason on every non-pass surface', () => {
  const rows = cases.map(c => row(c.input));
  assert.deepEqual(rows.map(jsonRow).map(r => [r.state, r.reason?.code ?? null]), cases.map(c => [c.state, c.code]));
  for (const [i, c] of cases.entries()) {
    const r = jsonRow(rows[i]);
    if (c.code) {
      assert.ok(r.reason.message.length);
      const text = renderText({ rows: [rows[i]], warnings: [], exitCode: 3, now: 0 });
      assert.ok(text.includes(c.state), c.state);
      assert.ok(text.includes(c.code), c.code);
      assert.ok(summaryLine([rows[i]]).includes(c.code), c.code);
    } else assert.equal(r.reason, null);
  }
});

test('named states: local lint reports partial in JSON and text with no authentication', async t => {
  const h = harbor(t);
  for (const json of [true, false]) {
    const p = portsFor(envFor(h));
    const code = await runCheck({ cwd: h.repo, options: { '--lint': true, '--local': true, ...(json ? { '--json': true } : {}) } }, p.ports);
    assert.equal(code, 0);
    assert.equal(p.clock.gh.length, 0);
    if (json) {
      const r = JSON.parse(p.ports.stdout.text);
      assert.equal(r.state, 'partial'); assert.equal(r.lint_state, 'partial');
      assert.equal(r.reason.code, 'local-only');
    } else {
      assert.match(p.ports.stdout.text, /partial/); assert.match(p.ports.stdout.text, /local-only/);
      assert.match(p.ports.stdout.text, /SVG/); assert.match(p.ports.stdout.text, /prompts.*not checked/);
    }
  }
});

test('named states: Sent is absent until an admitted Check POST returns', async t => {
  const h = harbor(t); let p, early = false, checks = 0, dispatch;
  const f = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint') return { status: 200, json: f.lint(e.request.requestId) };
    if (e.command === 'check') { checks++; early ||= /\bSent\b/.test(p.ports.stderr.text); dispatch = savedBatch(h, readdirSync(join(h.state, 'batches'))[0]).rows[0]; return { status: 200, json: f.check(e.request.requestId) }; }
    return f.normal(e);
  });
  p = portsFor(envFor(h, f));
  assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--json': true } }, p.ports), 0);
  assert.equal(checks, 1); assert.equal(dispatch.state, 'partial'); assert.equal(dispatch.reason.code, 'dispatch-uncertain'); assert.equal(early, false, 'Sent must follow actual admission and dispatch');
  assert.match(p.ports.stderr.text, /\bSent 1 check\b/);
});

test('named states: --timeout starts after free lint and survives JSON, batch and evidence', async t => {
  const h = harbor(t); let p;
  const f = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint') { p.clock.now += 80_000; return { status: 200, json: f.lint(e.request.requestId) }; }
    return { status: 202, json: f.check(e.request?.requestId ?? e.url.split('/').at(-1), 'running') };
  });
  const env = envFor(h, f); p = portsFor(env);
  assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--json': true, '--timeout': 1 } }, p.ports), 3);
  assert.equal(f.posts.filter(e => e.command === 'check').length, 1, 'free lint cannot consume the paid Check timeout');
  const r = JSON.parse(p.ports.stdout.text), saved = savedBatch(h, r.batch);
  assert.match(renderText({ rows: r.rows, exitCode: 3, timeoutMin: 1 }), /--timeout/);
  for (const value of [r.rows[0], saved.rows[0]]) {
    assert.equal(value.state, 'sent'); assert.equal(value.reason.code, 'timeout-flag');
    assert.match(value.reason.message, /--timeout/);
  }
  const evidence = resultLines(readRunResults({ root: h.repo }, { env, capture: () => ({ sha256: saved.source_sha256 }) })).join('\n');
  assert.match(evidence, /sent/); assert.match(evidence, /timeout-flag/);
  const read = portsFor(env);
  await runCheck({ cwd: h.repo, options: { '--read': r.batch, '--json': true, '--timeout': 1 } }, read.ports);
  assert.equal(f.posts.filter(e => e.command === 'check').length, 1, 'reading the canonical saved state must not resend');
  assert.equal(JSON.parse(read.ports.stdout.text).rows[0].reason.code, 'timeout-flag');
});

test('named states: standalone lint timeout names --timeout in its result', async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => ({ status: 202, json: f.job(e.request?.requestId ?? e.url.split('/').at(-1), 'lint', 'running') }));
  const p = portsFor(envFor(h, f));
  assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--lint': true, '--json': true, '--timeout': 1 } }, p.ports), 3, p.ports.stderr.text + p.ports.stdout.text);
  assert.ok(p.ports.stdout.text.trim(), 'a timed-out lint must still return JSON rows');
  const r = JSON.parse(p.ports.stdout.text);
  assert.equal(r.rows.length, 1); assert.equal(r.rows[0].reason.code, 'timeout-flag');
  assert.match(r.rows[0].reason.message, /--timeout/);
});

test('named states: a partial lint cannot admit paid checks and retains a reason', async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => {
    assert.equal(e.command, 'lint', 'partial lint must block a paid Check');
    const answer = f.lint(e.request.requestId);
    for (const item of answer.result.report.lint.tests) item.verdict = 'partial';
    return { status: 200, json: answer };
  });
  const p = portsFor(envFor(h, f));
  assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--json': true } }, p.ports), 5);
  const r = JSON.parse(p.ports.stdout.text);
  assert.equal(r.rows[0].state, 'not run'); assert.equal(r.rows[0].reason.code, 'no-server-verdict');
  assert.equal(savedBatch(h, r.batch).lint.state, 'not run', 'a raw job pass cannot claim a full selected lint pass');
  assert.equal(f.posts.filter(e => e.command === 'check').length, 0);
  assert.doesNotMatch(r.summary_line, /✓/);
});

test('named states: an ended lint without selected verdict carries deadline or no-server-verdict', () => {
  const answer = complete => ({ command: 'lint', state: 'passed', result: { report: { lint: { complete, tests: [] } } } });
  assert.deepEqual([false, true].map(complete => outcomeFor(answer(complete), { test: 'tests/place-order.json' }).code), ['deadline', 'no-server-verdict']);
});

test('named states: a partial saved lint is visible but cannot provide workflow pass evidence', async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => ({ status: 200, json: f.lint(e.request.requestId) }));
  const env = envFor(h, f), p = portsFor(env);
  assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--lint': true, '--json': true } }, p.ports), 0);
  const r = JSON.parse(p.ports.stdout.text), saved = savedBatch(h, r.batch);
  saved.rows[0] = { ...saved.rows[0], state: 'partial', reason: { code: 'local-only', message: 'SVG only' }, note: null };
  const { writeFileSync } = await import('node:fs');
  writeFileSync(join(h.state, 'batches', r.batch, 'batch.json'), JSON.stringify(saved));
  const result = readRunResults({ root: h.repo }, { env })[0];
  const { usableResult } = await import('../src/workflow-results.mjs');
  assert.equal(usableResult(result), false, 'partial lint must not supply workflow or Autopilot pass evidence');
  assert.equal(result.states[0].reason.code, 'local-only');
  const evidence = resultLines([result]).join('\n');
  assert.match(evidence, /partial/); assert.match(evidence, /local-only/);
  assert.doesNotMatch(evidence, /✓|1 of 1/);
});

test('named states: native CLI local lint returns a partial JSON result', async t => {
  const h = harbor(t);
  const { spawnSync } = await import('node:child_process');
  const { fileURLToPath } = await import('node:url');
  const cli = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));
  const r = spawnSync(process.execPath, [cli, 'lint', '--local', '--json'], { cwd: h.repo, env: { ...process.env, ...envFor(h) }, encoding: 'utf8', timeout: 30_000 });
  assert.equal(r.status, 0, r.stderr);
  const output = JSON.parse(r.stdout);
  assert.equal(output.state, 'partial'); assert.equal(output.reason.code, 'local-only');
});

test('named states: saved pass evidence names its state without a summary file', async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => ({ status: 200, json: f.lint(e.request.requestId) }));
  const env = envFor(h, f), p = portsFor(env);
  assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--lint': true, '--json': true } }, p.ports), 0);
  const r = JSON.parse(p.ports.stdout.text);
  const { unlinkSync } = await import('node:fs');
  unlinkSync(join(h.state, 'batches', r.batch, 'summary.json'));
  const evidence = resultLines(readRunResults({ root: h.repo }, { env })).join('\n');
  assert.match(evidence, /tests\/place-order.json: passed\b/);
});

test('named states: lint exception JSON uses a named state and reason', async t => {
  const h = harbor(t);
  const { PreflightError } = await import('../src/runtime-preflight.mjs');
  const p = portsFor(envFor(h), { captureSource() { throw new PreflightError(4, 'capture unavailable'); } });
  assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--lint': true, '--json': true } }, p.ports), 4);
  const r = JSON.parse(p.ports.stdout.text);
  assert.equal(r.lint_state, 'not run'); assert.equal(r.state, 'not run');
  assert.equal(r.reason.code, 'no-server-verdict');
});

test('named states: a retryable not-started receipt cannot print Sent with a failed job label', async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint') return { status: 200, json: f.lint(e.request.requestId) };
    const refusal = { code: 'login-queue-timeout', retryable: true, message: 'Capacity unavailable' };
    return { status: 200, json: f.job(e.request.requestId, 'check', 'failed', { refusals: [refusal], report: { dispatch: 'not_started' } }) };
  });
  const p = portsFor(envFor(h, f));
  assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--json': true } }, p.ports), 5);
  assert.doesNotMatch(p.ports.stderr.text, /\bSent\b/);
  const r = JSON.parse(p.ports.stdout.text);
  assert.equal(r.rows[0].state, 'not run'); assert.equal(r.rows[0].reason.code, 'server-busy');
});
