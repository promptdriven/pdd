import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-seam.mjs';
import { projectAnswer, renderJson, renderText, exitCodeFor } from '../src/runtime-seam.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

// Expected text comes from the approved display contract for issue 2622.
const internal = /interpreter|slot|pool|model|login|account/i;
const queueOne = '⏳ PDD is busy right now. Your check is in line (1 ahead of you) and starts by itself. You are not charged while you wait.';
const queueFive = '⏳ PDD is busy right now. Your check is in line (5 ahead of you) and starts by itself. You are not charged while you wait.';
const queueNext = '⏳ PDD is busy right now. Your check is next in line and starts by itself. You are not charged while you wait.';
const untimed = 'Not run: PDD stayed busy, so your check did not start. Nothing was charged. Try again in a few minutes';
const timed = duration => `Not run: PDD stayed busy for ${duration}, so your check did not start. Nothing was charged. Try again in a few minutes`;
const busyLines = text => text.split('\n').filter(line => line.startsWith('Not run:'));
function answer(seconds, extra = {}) {
  const refusal = { code: 'login-queue-timeout', message: 'No model login in the account pool.', retryable: true, max_wait_seconds: seconds };
  return { id: 'receipt', command: 'check', state: 'refused', usage: { calls: 0, seconds: 999 },
    report_url: 'https://runtime.example/r/receipt',
    result: { refusals: [refusal], why: 'The model login pool stayed busy.', next_step: 'Repair the account login.',
      report: { dispatch: 'not_started', refusal, samples: [], provider_calls: 0 } }, ...extra };
}
function projected(receipt, story = 'place-order') {
  return { story, title: 'Order', test: 'tests/place-order.json', phase: 'server', request_ids: [receipt.id],
    ...projectAnswer(receipt, { origin: 'https://runtime.example' }) };
}
for (const [seconds, duration] of [[600, '10 minutes'], [60, '1 minute'], [90, '90 seconds'], [1, '1 second']]) {
  test(`BUSY terminal duration ${seconds} uses the refusal deadline only`, () => {
    const row = projected(answer(seconds));
    const text = renderText({ rows: [row], exitCode: exitCodeFor([row]) });
    assert.deepEqual(busyLines(text), [`${timed(duration)}: pdd test place-order`]);
    assert.doesNotMatch(text, internal);
    assert.match(text, /https:\/\/runtime.example\/r\/receipt/);
    assert.equal(exitCodeFor([row]), 5);
    const json = renderJson({ repo: 'repo', rows: [row], exitCode: 5 }).rows[0];
    assert.equal(json.reason.code, 'server-busy');
    assert.equal(json.reason.message, 'No model login in the account pool.');
    assert.equal(json.why, 'The model login pool stayed busy.');
    assert.equal(json.next_step, 'Repair the account login.');
    assert.equal(json.request_id, 'receipt');
    assert.equal(json.report_url, 'https://runtime.example/r/receipt');
    assert.equal(json.calls, 0);
    assert.equal(Object.hasOwn(json, 'busy_display'), false);
  });
}
for (const seconds of [undefined, null, -1, 0, 1.5, NaN, Infinity, '600', Number.MAX_SAFE_INTEGER + 1]) {
  test(`BUSY invalid duration ${String(seconds)} omits duration`, () => {
    const text = renderText({ rows: [projected(answer(seconds))], exitCode: 5 });
    assert.deepEqual(busyLines(text), [`${untimed}: pdd test place-order`]);
    assert.doesNotMatch(text, internal);
  });
}
for (const story of [undefined, null, '', ' ', '-']) for (const seconds of [600, undefined]) {
  test(`BUSY unknown Story ${String(story)} duration ${seconds} has no command`, () => {
    const row = projected(answer(seconds)); row.story = story; row.report_url = null;
    const text = renderText({ rows: [row], exitCode: 5 });
    assert.deepEqual(busyLines(text), [`${seconds ? timed('10 minutes') : untimed}.`]);
    assert.doesNotMatch(busyLines(text).join('\n'), /pdd test|<story>/);
  });
}
test('BUSY each row gets its own safely quoted Story command', () => {
  const rows = [projected(answer(60), 'first'), projected(answer(90), "second story's choice")];
  assert.deepEqual(busyLines(renderText({ rows, exitCode: 5 })), [
    `${timed('1 minute')}: pdd test first`, `${timed('90 seconds')}: pdd test 'second story'\\''s choice'`,
  ]);
});
test('BUSY report-only refusal uses the selected refusal deadline', () => {
  const receipt = answer(600); delete receipt.result.refusals;
  assert.deepEqual(busyLines(renderText({ rows: [projected(receipt)], exitCode: 5 })), [`${timed('10 minutes')}: pdd test place-order`]);
});

async function command(h, f, options = {}, words = ['place-order']) {
  const p = portsFor({ HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin });
  const code = await runCheck({ cwd: h.repo, words, options }, p.ports);
  return { code, out: p.ports.stdout.text, err: p.ports.stderr.text };
}
for (const [ahead, expected] of [[0, queueNext], [1, queueOne], [5, queueFive],
  [undefined, null], [-1, null], [1.5, null], [Infinity, null], [Number.MAX_SAFE_INTEGER + 1, null]]) {
  test(`BUSY accepted ahead-only queue ${String(ahead)} preserves one POST and same-ID reads`, async t => {
    const h = harbor(t);
    const f = await fakeRuntime(t, (e, f) => {
      if (e.command === 'check') return { status: 202, json: { ...f.check(e.request.requestId, 'queued'), queue: { ahead } } };
      return f.normal(e);
    });
    const result = await command(h, f);
    const lines = result.err.split('\n').filter(line => line.startsWith('⏳'));
    assert.deepEqual(lines, expected ? [expected] : []);
    assert.doesNotMatch(lines.join('\n'), internal);
    assert.equal(result.code, 0);
    const posts = f.posts.filter(post => post.command === 'check');
    assert.equal(posts.length, 1);
    assert.deepEqual(f.gets.map(get => get.url), [`/v1/runs/${posts[0].request.requestId}`]);
  });
}
test('BUSY queue suppresses unchanged progress per request and shows changed counts', async t => {
  const h = harbor(t); let reads = 0;
  const f = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint') return f.normal(e);
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.method === 'POST' || ++reads <= 3) return { status: 200, json: { ...f.check(id, 'queued'), queue: { ahead: reads < 2 ? 5 : reads === 2 ? 1 : 0 } } };
    return { status: 200, json: f.check(id) };
  });
  const result = await command(h, f);
  assert.deepEqual(result.err.split('\n').filter(line => line.startsWith('⏳')), [queueFive, queueOne, queueNext]);
  assert.equal(result.code, 0);
  assert.equal(f.posts.filter(post => post.command === 'check').length, 1);
  assert.equal(new Set(f.gets.map(get => get.url)).size, 1);
});
test('BUSY immediate, batch read and bare request read agree without new POSTs or changed receipts', async t => {
  const h = harbor(t); let receipt;
  const f = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint') return f.normal(e);
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    receipt ??= { ...answer(600), id, requestId: id, report_url: `${f.origin}/r/receipt` };
    return { status: 200, json: receipt };
  });
  const first = await command(h, f, { '--json': true });
  const json = JSON.parse(first.out), row = json.rows[0], batch = json.batch;
  assert.equal(first.code, 5);
  assert.equal(row.reason.code, 'server-busy');
  const saved = JSON.parse(readFileSync(join(h.state, 'batches', batch, `${row.request_id}.json`), 'utf8'));
  assert.deepEqual(saved, receipt);
  const read = await command(h, f, { '--read': true }, [batch]);
  assert.deepEqual(busyLines(read.out), [`${timed('10 minutes')}: pdd test place-order`]);
  const bare = await command(h, f, { '--read': true }, [row.request_id]);
  assert.deepEqual(busyLines(bare.out), [`${timed('10 minutes')}.`]);
  assert.equal(read.code, 5); assert.equal(bare.code, 5);
  assert.equal(f.posts.filter(post => post.command === 'check').length, 1);
  assert.ok(f.gets.every(get => get.url === `/v1/runs/${row.request_id}`));
});
for (const calls of [2, 'unknown']) test(`BUSY text does not alter reported usage ${calls}`, () => {
  const receipt = answer(600, { usage: { calls, seconds: 10 } });
  const row = projected(receipt);
  assert.equal(row.calls, calls);
  assert.equal(renderJson({ repo: 'repo', rows: [row], exitCode: 5 }).rows[0].calls, calls);
});
test('BUSY evaluated checks keep their evidence and ordinary successful checks keep their verdict', () => {
  const receipt = answer(600);
  receipt.state = 'passed'; receipt.result.refusals = []; receipt.result.report = { samples: [{ steps: [{ checks: [{ passed: true }] }] }] };
  const row = projected(receipt);
  assert.equal(row.state, 'passed'); assert.deepEqual(row.checks, { passed: 1, total: 1 });
  assert.deepEqual(busyLines(renderText({ rows: [row], exitCode: 0 })), []);
});
test('BUSY local unsent work retains its unsent explanation and makes no queue promise', () => {
  const row = { story: 'place-order', title: 'Order', test: 'tests/place-order.json', state: 'not_run', phase: 'local',
    busy: true, request_ids: [], calls: 0, note: { code: 'check-busy', message: 'Held locally; this check was not sent. Retry this batch later.' } };
  const text = renderText({ rows: [row], exitCode: 5 });
  assert.match(text, /Held locally; this check was not sent/);
  assert.deepEqual(busyLines(text), []);
  assert.doesNotMatch(text, /in line|starts by itself|Nothing was charged/);
});
test('BUSY interruption keeps the submitted-request explanation', () => {
  const row = projected(answer(600)); row.busy = true;
  row.note = { code: 'check-busy', message: 'Stopped. Submitted request receipt. Read its saved result.' };
  const text = renderText({ rows: [row], exitCode: 3, interrupted: true });
  assert.match(text, /Stopped\. Submitted request receipt/);
  assert.deepEqual(busyLines(text), []);
});
