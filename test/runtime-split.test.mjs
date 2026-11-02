import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { appendFileSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { captureSource } from '../src/runtime-preflight.mjs';
import { fakeRuntime, harbor, portsFor, sha } from './runtime-fake.mjs';

// Split large test runs: the fixture's two Stories each fit an upload alone, but not together under a small limit.
const A = 'tests/place-order.json', B = 'tests/unknown-item.json';
const measure = (root, tests) => { const capture = captureSource(root, { tests, appMap: null }); return { bytes: capture.tar.length, files: capture.files.length }; };
const listing = tar => spawnSync('tar', ['-tf', '-'], { input: tar, encoding: 'utf8' }).stdout.split('\n').filter(Boolean);
const lints = f => f.posts.filter(post => post.command === 'lint');
const checks = f => f.posts.filter(post => post.command === 'check');
function twoPartLimit(h) {
  const a = measure(h.repo, [A]), b = measure(h.repo, [B]), both = measure(h.repo, [A, B]);
  const limits = { bytes: 10_485_760, files: Math.max(a.files, b.files) };
  assert.ok(both.files > limits.files, 'fixture: the two Stories together need more files than either alone');
  return limits;
}
async function run(h, f, options, { words = ['place-order', 'unknown-item'], limits, clock } = {}) {
  const p = portsFor({ HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin }, limits ? { uploadLimits: limits } : {});
  if (clock?.now) p.clock.now = clock.now;
  const code = await runCheck({ cwd: h.repo, words: options['--read'] || options['--retry'] ? [] : words, options }, p.ports);
  if (clock) clock.now = p.clock.now;
  const out = p.ports.stdout.text;
  return { code, out, err: p.ports.stderr.text, json: options['--json'] && out.startsWith('{') ? JSON.parse(out) : null };
}

test('SPLIT sends Stories that do not fit one upload in parts, with one result', async t => {
  const h = harbor(t), limits = twoPartLimit(h);
  const f = await fakeRuntime(t, (e, f) => f.normal(e));
  const result = await run(h, f, { '--json': true }, { limits });
  assert.equal(lints(f).length, 2, 'one lint for each part');
  assert.deepEqual(lints(f).map(post => listing(post.tar).filter(path => path.startsWith('tests/'))), [[A], [B]], 'a Story is never split; each part has its own archive');
  for (const post of checks(f)) {
    const part = lints(f).find(lint => listing(lint.tar).includes(post.request.scenario));
    assert.equal(post.request.source_sha256, part?.request.source_sha256, 'a check sends its own part archive');
    assert.equal(sha(post.tar), post.request.source_sha256);
  }
  assert.equal(checks(f).length, 2);
  assert.equal(result.code, 0, result.err);
  assert.deepEqual(result.json.rows.map(row => row.state), ['passed', 'passed']);
  assert.equal(result.json.parts?.length, 2);
  assert.deepEqual(result.json.parts?.map(part => part.tests), [[A], [B]]);
  assert.equal(result.json.source_sha256, null, 'no single archive hash for a run in parts');
  assert.match(result.err, /Sent in 2 parts: 1 and 1 tests \(/);
  assert.equal(result.json.summary_line.split('Prompt tests').length, 2, 'one overall summary line');
});

test('SPLIT refuses only a Story too large to send alone, with its path, size and the limit', async t => {
  const h = harbor(t, repo => appendFileSync(join(repo, 'user_stories/place-order.md'), `\n${'Large background text. '.repeat(3000)}\n`));
  const a = measure(h.repo, [A]), b = measure(h.repo, [B]);
  const limits = { bytes: b.bytes + 1, files: 10_000 };
  assert.ok(a.bytes > limits.bytes, 'fixture: place-order alone is larger than the limit');
  const f = await fakeRuntime(t, (e, f) => f.normal(e));
  const result = await run(h, f, { '--json': true }, { limits });
  assert.deepEqual(checks(f).map(post => post.request.scenario), [B], 'the other Story is still sent');
  assert.ok(lints(f).every(post => !listing(post.tar).includes(A)), 'the large Story is never uploaded');
  const row = result.json.rows.find(item => item.test === A);
  assert.equal(row.state, 'refused'); assert.equal(row.calls, 0);
  assert.equal(row.refusals[0]?.code, 'upload-too-large');
  assert.match(row.refusals[0]?.message ?? '', /^tests\/place-order\.json: its files need \d+ KB \(\d+ files\) to send; the limit is \d+ KB and 10000 files\.$/);
  assert.equal(result.code, 4);
});

for (const progress of [true, false]) test(`SPLIT lints again the Stories a lint did not reach (${progress ? 'the next round gives a verdict' : 'no new verdict'})`, async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => {
    if (e.command !== 'lint') return f.normal(e);
    const answer = f.lint(e.request.requestId), first = lints(f).length === 1;
    if (first || !progress) answer.result.report.lint = { complete: false, tests: listing(e.tar).filter(path => path.startsWith('tests/'))
      .map(path => ({ path, verdict: path === B ? 'not-checked' : 'passed' })) };
    return { status: 200, json: answer };
  });
  const result = await run(h, f, { '--json': true });
  assert.equal(lints(f).length, 2, 'one more lint, then stop when nothing changes');
  assert.deepEqual(listing(lints(f)[1].tar).filter(path => path.startsWith('tests/')), [B], 'only the Story without a verdict is linted again');
  const sentB = checks(f).find(post => post.request.scenario === B);
  if (progress) {
    assert.equal(sentB?.request.source_sha256, lints(f)[1].request.source_sha256, 'the check uses the archive of the part that linted it');
    assert.equal(result.code, 0, result.err);
  } else {
    assert.equal(sentB, undefined);
    const row = result.json.rows.find(item => item.test === B);
    assert.equal(row.state, 'not_run'); assert.match(JSON.stringify(row.reason), /lint did not finish/);
    assert.equal(result.code, 5);
  }
  assert.equal(checks(f).filter(post => post.request.scenario === A).length, 1, 'a test with its own pass is never held back');
});

test('SPLIT pdd lint on many Stories lints each part and gives one result', async t => {
  const h = harbor(t), limits = twoPartLimit(h);
  const f = await fakeRuntime(t, (e, f) => f.normal(e));
  const result = await run(h, f, { '--lint': true, '--json': true }, { limits });
  assert.equal(lints(f).length, 2);
  assert.deepEqual(result.json.rows.map(row => [row.test, row.state]), [[A, 'passed'], [B, 'passed']]);
  assert.equal(result.json.lint_state, 'passed'); assert.equal(result.code, 0, result.err);
  assert.match(result.err, /Linted in 2 parts: 1 and 1 tests/);
  assert.equal(checks(f).length, 0);
});

test('SPLIT --read and --retry use each row part', async t => {
  const h = harbor(t), limits = twoPartLimit(h), clock = {};
  let busy = true;
  const f = await fakeRuntime(t, (e, f) => e.command === 'check' && e.request.scenario === B && busy
    ? { status: 503, headers: { 'retry-after': '300' }, json: { dispatch: 'not_started', error: { code: 'check-queue-full', details: { retryable: true, retry_after: 300 } } } }
    : f.normal(e));
  const first = await run(h, f, { '--json': true }, { limits, clock });
  assert.equal(first.code, 5, first.err);
  assert.equal(first.json.parts?.length, 2);
  const read = await run(h, f, { '--read': first.json.batch, '--json': true }, { limits, clock });
  assert.deepEqual(read.json.rows.map(row => row.test), [A, B]);
  assert.equal(read.json.parts?.length, 2);
  busy = false; clock.now += 400_000;
  const partB = first.json.parts?.find(part => part.tests.includes(B));
  const retry = await run(h, f, { '--retry': first.json.batch, '--json': true }, { limits, clock });
  const resent = checks(f).filter(post => post.request.scenario === B).at(-1);
  assert.equal(resent.request.source_sha256, partB?.source_sha256, 'a check sent again uses its own part archive');
  assert.equal(retry.code, 0, retry.err);
});

test('SPLIT a batch saved before parts existed reads as one part', async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => f.normal(e));
  const first = await run(h, f, { '--json': true });
  const path = join(h.state, 'batches', first.json.batch, 'batch.json'), saved = JSON.parse(readFileSync(path));
  if (saved.version === 2) {
    const [part] = saved.parts;
    Object.assign(saved, { version: 1, source_sha256: part.source_sha256, files: part.files, bytes: part.bytes, lint: part.lint });
    delete saved.parts; for (const row of saved.rows) delete row.part;
    writeFileSync(path, JSON.stringify(saved));
  }
  const read = await run(h, f, { '--read': first.json.batch, '--json': true });
  assert.equal(read.code, 0, read.err);
  assert.equal(read.json.parts?.length, 1);
  assert.equal(read.json.parts?.[0].source_sha256, read.json.source_sha256);
});
