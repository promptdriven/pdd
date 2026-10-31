import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

function capacity(f, id, { calls = 0, code = 'check-queue-timeout', dispatch = 'not_started', checks = [], state = 'refused' } = {}) {
  const refusal = { code, message: 'No checks ran.', reason: 'The queue is full.', fix: 'Fix what it names.', details: { retryable: true, retry_after: 5 } };
  return f.job(id, 'check', state, { refusals: [refusal], report: { dispatch, provider_calls: calls, refusal,
    samples: checks.length ? [{ steps: [{ checks }] }] : [] } }, calls);
}
async function run(setup, fake, words = ['place-order'], options = { '--json': true }, extra = {}) {
  const { ports, clock } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, extra);
  if (setup.clockNow) clock.now = setup.clockNow;
  const code = await runCheck({ words, options, cwd: setup.repo }, ports);
  setup.clockNow = clock.now;
  return { code, clock, out: ports.stdout.text, err: ports.stderr.text, json: options['--json'] && ports.stdout.text ? JSON.parse(ports.stdout.text) : null };
}
const checkPosts = fake => fake.posts.filter(p => p.command === 'check');
const saved = (setup, batch) => JSON.parse(readFileSync(join(setup.state, 'batches', batch, 'batch.json'), 'utf8'));

test('CAPACITY1: confirmed zero-execution capacity is retried until the wait ends, then busy, never a test failure', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => e.command === 'check' ? { status: 200, json: capacity(f, e.request.requestId) } : f.normal(e));
  const result = await run(setup, fake);
  assert.equal(result.code, 5, result.err + result.out);
  assert.ok(checkPosts(fake).length > 3);
  assert.equal(new Set(checkPosts(fake).map(p => p.request.requestId)).size, checkPosts(fake).length);
  assert.equal(result.json.rows[0].state, 'not_run');
  assert.equal(result.json.rows[0].busy, true); assert.equal(result.json.rows[0].can_retry, true);
  assert.equal(result.json.rows[0].calls, 0); assert.equal(result.json.rows[0].checks, null);
  assert.match(result.json.summary_line, /: busy/); assert.doesNotMatch(result.out + result.err, /Fix what|fix the test|✗/);
  assert.match(result.err, /Server busy/); assert.match(result.err, /pdd check --retry/);
  assert.equal(saved(setup, result.json.batch).rows[0].request_ids.length, checkPosts(fake).length);
  const before = fake.posts.length;
  const read = await run(setup, fake, [result.json.batch], { '--read': true, '--json': true });
  assert.equal(read.code, 5); assert.equal(read.json.rows[0].busy, true); assert.equal(fake.posts.length, before);
});

test('CAPACITY2: 17 tests use four configured active slots, adapt to a one-worker queue, and preserve all IDs', async t => {
  const setup = harbor(t, repo => {
    const file = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(file));
    rmSync(file); rmSync(join(repo, 'tests/unknown-item.json'));
    for (let i = 0; i < 17; i++) writeFileSync(join(repo, `tests/order-${i}.json`), JSON.stringify(doc));
  });
  let now = 0, active = null, peak = 0;
  const jobs = new Map();
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check') {
      const id = e.request.requestId;
      jobs.set(id, { at: now, started: !active }); if (!active) active = id;
      peak = Math.max(peak, [...jobs.values()].filter(j => !j.ended).length);
      return { status: 202, json: f.check(id, 'queued') };
    }
    if (e.method === 'GET') {
      const id = e.url.split('/').at(-1), job = jobs.get(id);
      if (job.started && now - job.at >= 35_000) { job.ended = true; active = null; return { status: 200, json: f.check(id) }; }
      if (!job.started && now - job.at >= 20_000) { job.ended = true; return { status: 200, json: capacity(f, id) }; }
      return { status: 200, json: f.check(id, job.started ? 'running' : 'queued') };
    }
    return f.normal(e);
  });
  const start = Date.parse('2026-10-27T16:27:47Z');
  const result = await run(setup, fake, [], { '--json': true, '--timeout': '15' }, {
    env: { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state, PDD_MAX_JOBS: '4' },
    now: () => start + now, sleep: async ms => { now += ms; }
  });
  assert.equal(result.code, 0, result.err + result.out); assert.equal(result.json.rows.length, 17);
  assert.equal(peak, 4); assert.equal(checkPosts(fake).length, 20);
  assert.ok(result.json.rows.every(r => r.state === 'passed'));
  assert.equal(new Set(checkPosts(fake).map(p => p.request.requestId)).size, checkPosts(fake).length);
  assert.ok(fake.posts.every(p => p.tar.equals(fake.posts[0].tar)));
  assert.match(result.err, /Still running:/);
});

test('CAPACITY3: admission backpressure honors Retry-After before a fresh ID', async t => {
  const setup = harbor(t); let now = 0, firstAt;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check' && checkPosts(f).length === 1) { firstAt = now; return { status: 503, headers: { 'retry-after': '7' }, json: {
      dispatch: 'not_started', job_created: false, error: { code: 'check-queue-full', details: { retryable: true, retry_after: 2 } } } }; }
    if (e.command === 'check') assert.ok(now - firstAt >= 7000);
    return f.normal(e);
  });
  const result = await run(setup, fake, undefined, undefined, { now: () => 1793118467000 + now, sleep: async ms => { now += ms; } });
  assert.equal(result.code, 0, result.out + result.err); assert.equal(checkPosts(fake).length, 2);
});

test('CAPACITY4: execution, missing accounting, invalid source, wrong dispatch and unknown never authorize retry', async t => {
  for (const opts of [{ calls: 1 }, { calls: 'unknown' }, { code: 'invalid-source' }, { dispatch: 'unknown' }, { state: 'unknown' },
    { checks: [{ criterion_id: 'AC1', passed: true }] }]) {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (e, f) => e.command === 'check' ? { status: 200, json: capacity(f, e.request.requestId, opts) } : f.normal(e));
    const result = await run(setup, fake);
    assert.equal(checkPosts(fake).length, 1, JSON.stringify(opts)); assert.notEqual(result.code, 0);
    assert.notEqual(result.json.rows[0].can_retry, true, JSON.stringify(opts));
  }
});

test('CAPACITY5: lost POST is read with its ID before confirmed capacity permits one new ID', async t => {
  const setup = harbor(t); let reads = 0;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check' && checkPosts(f).length === 1) return { destroy: true };
    if (e.method === 'GET' && e.url.endsWith(checkPosts(f)[0].request.requestId)) {
      reads++; return { status: 200, json: reads === 1 ? f.check(e.url.split('/').at(-1), 'running') : capacity(f, e.url.split('/').at(-1)) };
    }
    return f.normal(e);
  });
  const result = await run(setup, fake);
  assert.equal(result.code, 0, result.out + result.err); assert.equal(reads, 2); assert.equal(checkPosts(fake).length, 2);
});

test('CAPACITY6: explicit recovery retries only busy rows, keeps passes/caps/history, and refuses changed source', async t => {
  const setup = harbor(t); let recover = false;
  const fake = await fakeRuntime(t, (e, f) => e.command === 'check' && e.request.scenario.endsWith('place-order.json') && !recover
    ? { status: 200, json: capacity(f, e.request.requestId) } : f.normal(e));
  const first = await run(setup, fake, [], { '--json': true, '--max-calls': '9' });
  assert.equal(first.code, 5); recover = true;
  const old = saved(setup, first.json.batch), before = fake.posts.length;
  const recovered = await run(setup, fake, [], { '--retry': first.json.batch, '--json': true });
  assert.equal(recovered.code, 0, recovered.out + recovered.err);
  assert.equal(fake.posts.length, before + 1); assert.equal(checkPosts(fake).at(-1).request.max_calls, 9);
  const after = saved(setup, first.json.batch);
  assert.equal(after.created_at, old.created_at);
  assert.deepEqual(after.rows.find(r => r.test.endsWith('unknown-item.json')).request_ids, old.rows.find(r => r.test.endsWith('unknown-item.json')).request_ids);
  assert.equal(after.rows.find(r => r.test.endsWith('place-order.json')).request_ids.length, old.rows.find(r => r.test.endsWith('place-order.json')).request_ids.length + 1);
  assert.deepEqual(parseArgv(['check', '--retry', first.json.batch]).options['--retry'], first.json.batch);

  recover = false;
  const second = await run(setup, fake);
  writeFileSync(join(setup.repo, 'user_stories/place-order.md'), readFileSync(join(setup.repo, 'user_stories/place-order.md'), 'utf8') + '\nChanged source.\n');
  const count = fake.posts.length;
  const stale = await run(setup, fake, [], { '--retry': second.json.batch, '--json': true });
  assert.equal(stale.code, 2, stale.err); assert.match(stale.err, /source.*changed|source.*match/i); assert.equal(fake.posts.length, count);
});

test('CAPACITY7: a lost retry clears eligibility; a later recovery only reads that unknown ID', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check') return checkPosts(f).length === 1 ? { status: 200, json: capacity(f, e.request.requestId) } : { destroy: true };
    if (e.method === 'GET') return { status: 404, json: { error: { code: 'not-found' } } };
    return f.normal(e);
  });
  const first = await run(setup, fake);
  assert.equal(first.code, 3); assert.equal(checkPosts(fake).length, 2); assert.equal(first.json.rows[0].can_retry, false);
  const retry = await run(setup, fake, [], { '--retry': first.json.batch, '--json': true });
  assert.equal(retry.code, 3); assert.equal(checkPosts(fake).length, 2);
});

test('CAPACITY8: deadline and interruption never bypass backoff or send another ID', async t => {
  for (const interrupt of [false, true]) {
    const setup = harbor(t); let made;
    const fake = await fakeRuntime(t, (e, f) => {
      if (e.command !== 'check') return f.normal(e);
      const json = capacity(f, e.request.requestId); json.result.report.refusal.details.retry_after = 300;
      return { status: 200, json };
    });
    made = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
    if (interrupt) made.ports.sleep = async ms => { made.clock.now += ms; made.clock.interrupt(); };
    const code = await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: setup.repo }, made.ports);
    assert.equal(code, interrupt ? 3 : 5); assert.equal(checkPosts(fake).length, 1);
    assert.equal(JSON.parse(made.ports.stdout.text).rows[0].calls, 0);
  }
});

test('CAPACITY9: explicit recovery preserves a running job and a completed job while retrying capacity', async t => {
  const setup = harbor(t, repo => writeFileSync(join(repo, 'tests/running.json'), readFileSync(join(repo, 'tests/place-order.json'))));
  let recover = false;
  const runningIds = new Set();
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check' && e.request.scenario.endsWith('running.json')) runningIds.add(e.request.requestId);
    if (e.command === 'check' && e.request.scenario.endsWith('place-order.json') && !recover)
      return { status: 200, json: capacity(f, e.request.requestId) };
    if (e.method === 'GET' && runningIds.has(e.url.split('/').at(-1))) return { status: 200, json: f.check(e.url.split('/').at(-1), 'running') };
    return f.normal(e);
  });
  const first = await run(setup, fake, []); assert.equal(first.code, 3);
  const original = saved(setup, first.json.batch), posts = fake.posts.length; recover = true;
  const retry = await run(setup, fake, [], { '--retry': first.json.batch, '--json': true });
  assert.equal(retry.code, 3); assert.equal(fake.posts.length, posts + 1);
  for (const path of ['tests/running.json', 'tests/unknown-item.json']) assert.deepEqual(saved(setup, first.json.batch).rows.find(r => r.test === path).request_ids,
    original.rows.find(r => r.test === path).request_ids);
});

test('CAPACITY10: unknown dispatched jobs still occupy four configured slots; held rows stay unposted', async t => {
  const setup = harbor(t, repo => {
    const bytes = readFileSync(join(repo, 'tests/place-order.json'));
    for (let i = 0; i < 8; i++) writeFileSync(join(repo, `tests/extra-${i}.json`), bytes);
  });
  const fake = await fakeRuntime(t, (e, f) => e.method === 'GET' ? { status: 200, json: { ...f.check(e.url.split('/').at(-1)), requestId: 'wrong' } } : f.normal(e));
  const result = await run(setup, fake, [], undefined, {
    env: { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state, PDD_MAX_JOBS: '4' }
  });
  assert.equal(result.code, 3); assert.equal(checkPosts(fake).length, 4);
  assert.equal(result.json.rows.filter(r => r.state === 'unknown').length, 4);
  assert.equal(result.json.rows.filter(r => r.state === 'not_run' && r.calls === 0 && !r.request_id).length, 6);
});

test('CAPACITY11: explicit recovery honors saved admission Retry-After across invocations', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => e.command === 'check' ? { status: 503, headers: { 'retry-after': '300' }, json: {
    dispatch: 'not_started', error: { code: 'check-queue-full', details: { retryable: true, retry_after: 300 } } } } : f.normal(e));
  const first = await run(setup, fake); assert.equal(first.code, 5); assert.equal(checkPosts(fake).length, 1);
  const next = await run(setup, fake, [], { '--retry': first.json.batch, '--json': true });
  assert.equal(next.code, 5); assert.equal(checkPosts(fake).length, 1);
  assert.equal(next.json.rows[0].can_retry, true); assert.equal(next.json.rows[0].calls, 0);
  assert.equal(fake.gets.length, 0);
});
