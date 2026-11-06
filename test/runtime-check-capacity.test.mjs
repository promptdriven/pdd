import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync, readdirSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { fakeRuntime, harbor, ordinaryCapabilities, portsFor, storyTest } from './runtime-fake.mjs';

const ENGINE = 'eae2202a68d00ab762fcbbf1eba0d8607a132a15';

async function memoryRuntime(setup, handlers = {}, extraPorts = {}) {
  const fake = { posts: [], checkPosts: [], gets: [], capacities: 0, origin: 'https://runtime.invalid' };
  const decode = async form => {
    const request = JSON.parse(await form.get('request').text());
    const tar = Buffer.from(await form.get('source').arrayBuffer());
    return { request, tar };
  };
  const sourcesFrom = tar => {
    const listing = spawnSync('tar', ['-tf', '-'], { input: tar, encoding: 'utf8' });
    assert.equal(listing.status, 0, listing.stderr);
    return listing.stdout.split('\n').filter(Boolean).map(path => {
      const file = spawnSync('tar', ['-xOf', '-', path], { input: tar });
      assert.equal(file.status, 0, file.stderr.toString());
      return { path, bytes: file.stdout };
    });
  };
  const job = (id, command, state, result, calls = 0) => ({ requestId: id, id, command, state, engine_sha: ENGINE,
    result, usage: { calls, model: 'unknown', requested_model: calls ? 'gpt-6.1-sol' : 'unknown', seconds: 0 },
    report_url: `https://runtime.invalid/r/${id}` });
  fake.job = job;
  const fetch = async (input, init = {}) => {
    const url = new URL(input), method = init.method ?? 'GET';
    if (url.pathname === '/v1/capacity') {
      fake.capacities++;
      return Response.json({ error: { code: 'not-found' } }, { status: 404 });
    }
    if (method === 'POST' && url.pathname === '/v1/lint') {
      const { request, tar } = await decode(init.body), sources = sourcesFrom(tar);
      fake.posts.push({ command: 'lint', request });
      const paths = sources.filter(source => { try { return JSON.parse(source.bytes).schema_version === 'prompt-runtime.program-scenario.v1'; } catch { return false; } }).map(source => source.path);
      const tests = paths.map(path => ({ path, verdict: 'passed' }));
      const capabilities = paths.map(path => ({ path, report: ordinaryCapabilities(sources, path) }));
      const result = { exitCode: 0, refusals: [], capabilities, capabilities_complete: true,
        report: { verdict: 'passed', lint: { complete: true, tests }, program: { prompts: [{ path: 'prompts/place_order.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } }] } } };
      return Response.json(job(request.requestId, 'lint', 'passed', result));
    }
    if (method === 'POST' && url.pathname === '/v1/check') {
      const { request } = await decode(init.body);
      fake.posts.push({ command: 'check', request }); fake.checkPosts.push(request);
      const reply = handlers.check ? await handlers.check(request, fake) : { status: 200, json: job(request.requestId, 'check', 'passed', { exitCode: 0, report: { samples: [] } }, 1) };
      return new Response(JSON.stringify(reply.json), { status: reply.status, headers: { 'content-type': 'application/json', ...(reply.headers ?? {}) } });
    }
    if (method === 'GET' && url.pathname.startsWith('/v1/runs/')) {
      const id = url.pathname.split('/').at(-1); fake.gets.push(id);
      const reply = handlers.get ? await handlers.get(id, fake) : { status: 404, json: { error: { code: 'not-found' } } };
      return new Response(JSON.stringify(reply.json ?? {}), { status: reply.status, headers: { 'content-type': 'application/json', ...(reply.headers ?? {}) } });
    }
    assert.fail(`unexpected in-memory request: ${method} ${url.pathname}`);
  };
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };
  const made = portsFor(env, { fetch, ...extraPorts });
  return { fake, ...made };
}

function dispatchClaims(setup, batch) {
  const folder = join(setup.state, 'batches', batch);
  try { return readdirSync(folder).filter(name => name.endsWith('.dispatch.json')); } catch { return []; }
}
function dispatchClaimIds(setup, batch) {
  const folder = join(setup.state, 'batches', batch);
  return dispatchClaims(setup, batch).map(name => {
    try { return JSON.parse(readFileSync(join(folder, name), 'utf8')).id; } catch { return null; }
  }).filter(Boolean);
}

async function runMemory(setup, fake, made, words = ['place-order'], options = { '--json': true }) {
  const code = await runCheck({ words, options, cwd: setup.repo }, made.ports);
  setup.clockNow = made.clock.now;
  const out = made.ports.stdout.text;
  return { code, clock: made.clock, out, err: made.ports.stderr.text, json: options['--json'] && out ? JSON.parse(out) : null };
}
async function invokeMemory(setup, fake, fetch, words, options, cache = false) {
  const { ports, clock } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, { fetch });
  if (setup.clockNow) clock.now = setup.clockNow;
  const code = await runCheck({ words, options, cwd: setup.repo, cache }, ports);
  setup.clockNow = clock.now;
  const out = ports.stdout.text;
  return { code, clock, out, err: ports.stderr.text, json: options['--json'] && out ? JSON.parse(out) : null };
}

function capacity(f, id, { calls = 0, code = 'check-queue-timeout', dispatch = 'not_started', checks = [], state = 'refused' } = {}) {
  const refusal = { code, message: 'No checks ran.', reason: 'The queue is full.', fix: 'Fix what it names.', details: { retryable: true, retry_after: 5 } };
  const answer = f.job(id, 'check', state, { refusals: [refusal], report: { dispatch, provider_calls: calls, accounting_complete: true, refusal,
    samples: checks.length ? [{ steps: [{ checks }] }] : [] } }, calls);
  answer.accounting_complete = true;
  Object.assign(answer.usage, { known_calls: calls, unknown_calls: 0, accounting_complete: true });
  return answer;
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

test('CAPACITY direct 429: unknown usage never allocates another ID, claim or Check POST', async t => {
  const setup = harbor(t);
  const { fake, ...made } = await memoryRuntime(setup, { check: request => ({ status: 429, json: {
    dispatch: 'not_started', provider_calls: 0, accounting_complete: true,
    usage: { calls: 0, known_calls: 0, unknown_calls: 1, accounting_complete: true },
    error: { code: 'server-full', message: 'Queue full.', details: { retryable: true, retry_after: 1 } }, requestId: request.requestId,
  } }) });
  const result = await runMemory(setup, fake, made, ['place-order'], { '--json': true, '--timeout': 1 });
  assert.ok(result.json, result.err + result.out);
  const observed = { posts: fake.checkPosts.length, ids: new Set(fake.checkPosts.map(item => item.requestId)).size,
    claims: dispatchClaims(setup, result.json.batch).length, allocated_check_uuids: dispatchClaimIds(setup, result.json.batch).length, state: result.json.rows[0].state,
    calls: result.json.rows[0].calls, busy: result.json.rows[0].busy, can_retry: result.json.rows[0].can_retry };
  assert.deepEqual(observed, { posts: 1, ids: 1, claims: 1, allocated_check_uuids: 1, state: 'unknown', calls: 'unknown', busy: false, can_retry: false });
  assert.match(result.json.rows[0].next_step ?? '', /--read/);
  const read = await invokeMemory(setup, fake, made.ports.fetch, [result.json.batch], { '--read': true, '--json': true });
  assert.equal(fake.checkPosts.length, 1); assert.equal(dispatchClaimIds(setup, result.json.batch).length, 1);
  assert.ok(fake.gets.includes(result.json.rows[0].request_id)); assert.equal(read.json.rows[0].state, 'unknown');
});

test('CAPACITY terminal contradiction stays unknown through saved read and explicit retry', async t => {
  const setup = harbor(t);
  const { fake, ...made } = await memoryRuntime(setup, { check: request => {
    const refusal = { code: 'server-full', message: 'Queue full.', details: { retryable: true, retry_after: 1 } };
    const answer = fake.job(request.requestId, 'check', 'refused', { refusals: [refusal], report: {
      dispatch: 'not_started', provider_calls: 0, accounting_complete: true, refusal, samples: [] } }, 0);
    answer.accounting_complete = false;
    Object.assign(answer.usage, { known_calls: 0, unknown_calls: 0, accounting_complete: true });
    return { status: 200, json: answer };
  } });
  const initial = await runMemory(setup, fake, made, ['place-order'], { '--json': true, '--timeout': 1 });
  const row = initial.json.rows[0], batch = initial.json.batch;
  assert.equal(row.state, 'unknown'); assert.equal(row.calls, 'unknown');
  assert.equal(row.known_calls, 0); assert.equal(row.unknown_calls, 1); assert.equal(row.accounting_complete, false);
  assert.equal(row.busy, false); assert.equal(row.can_retry, false);
  assert.match(row.next_step ?? '', /--read/);
  assert.equal(fake.checkPosts.length, 1); assert.equal(dispatchClaimIds(setup, batch).length, 1);

  const read = await invokeMemory(setup, fake, made.ports.fetch, [batch], { '--read': true, '--json': true });
  assert.equal(fake.checkPosts.length, 1); assert.equal(dispatchClaimIds(setup, batch).length, 1);
  assert.ok(fake.gets.includes(row.request_id));
  assert.equal(read.json.rows[0].state, 'unknown'); assert.equal(read.json.rows[0].busy, false);
  setup.clockNow += 90_100;
  const retry = await invokeMemory(setup, fake, made.ports.fetch, [], { '--retry': batch, '--json': true, '--timeout': 1 });
  assert.equal(fake.checkPosts.length, 1); assert.equal(dispatchClaimIds(setup, batch).length, 1);
  assert.equal(retry.json.rows[0].calls, 'unknown'); assert.equal(retry.json.rows[0].can_retry, false);
  const text = await invokeMemory(setup, fake, made.ports.fetch, [batch], { '--read': true });
  assert.match(text.out, /unknown/i); assert.match(text.out, /pdd test --read/);
  assert.doesNotMatch(text.out + text.err, /You are not charged|No checks ran/);
  assert.equal(fake.checkPosts.length, 1);
});

test('CAPACITY missing, malformed or conflicting accounting surfaces fail closed', async t => {
  const mutations = [
    ['missing provider proof', reply => { delete reply.provider_calls; delete reply.report.provider_calls; }],
    ['missing calls', reply => { delete reply.usage.calls; }],
    ['malformed provider count', reply => { reply.report.provider_calls = '0'; }],
    ['conflicting provider counts', reply => { reply.report.provider_calls = 1; }],
    ['conflicting completion flags', reply => { reply.report.accounting_complete = false; }],
    ['conflicting dispatch flags', reply => { reply.report.dispatch = 'started'; }],
    ['wrong response ID', reply => { reply.requestId = '00000000-0000-4000-8000-000000000000'; }],
    ['claimed job creation', reply => { reply.job_created = true; }],
    ['evaluated checks', reply => { reply.report.samples = [{ steps: [{ checks: [{}] }] }]; }],
  ];
  for (const [name, mutate] of mutations) await t.test(name, async sub => {
    const setup = harbor(sub);
    const { fake, ...made } = await memoryRuntime(setup, { check: request => {
      const reply = { dispatch: 'not_started', provider_calls: 0, accounting_complete: true,
        usage: { calls: 0, known_calls: 0, unknown_calls: 0, accounting_complete: true },
        report: { dispatch: 'not_started', provider_calls: 0, accounting_complete: true },
        error: { code: 'server-full', details: { retryable: true, retry_after: 1 } }, requestId: request.requestId };
      mutate(reply);
      return { status: 429, json: reply };
    } });
    const result = await runMemory(setup, fake, made, ['place-order'], { '--json': true, '--timeout': 1 });
    const row = result.json.rows[0];
    assert.deepEqual({ posts: fake.checkPosts.length, ids: new Set(fake.checkPosts.map(item => item.requestId)).size,
      claims: dispatchClaimIds(setup, result.json.batch).length, state: row.state, calls: row.calls,
      unknown_calls: row.unknown_calls, busy: row.busy, can_retry: row.can_retry },
    { posts: 1, ids: 1, claims: 1, state: 'unknown', calls: 'unknown', unknown_calls: 1, busy: false, can_retry: false });
  });
});

test('CAPACITY complete zero remains retryable beyond three attempts; saved read sends no Check', async t => {
  const setup = harbor(t);
  const { fake, ...made } = await memoryRuntime(setup, { check: request => ({ status: 429, json: {
    dispatch: 'not_started', provider_calls: 0, accounting_complete: true,
    usage: { calls: 0, known_calls: 0, unknown_calls: 0, accounting_complete: true },
    error: { code: 'server-full', message: 'Queue full.', details: { retryable: true, retry_after: 1 } }, requestId: request.requestId,
  } }) });
  const initial = await runMemory(setup, fake, made, ['place-order'], { '--json': true, '--timeout': 1 });
  assert.ok(fake.checkPosts.length > 3);
  const before = { posts: fake.checkPosts.length, claims: dispatchClaimIds(setup, initial.json.batch).length };
  const read = await invokeMemory(setup, fake, made.ports.fetch, [initial.json.batch], { '--read': true, '--json': true });
  assert.deepEqual({ posts: fake.checkPosts.length, claims: dispatchClaimIds(setup, initial.json.batch).length }, before);
  assert.equal(read.json.rows[0].busy, true); assert.equal(read.json.rows[0].calls, 0);
  setup.clockNow += 90_100;
  const retry = await invokeMemory(setup, fake, made.ports.fetch, [], { '--retry': initial.json.batch, '--json': true, '--timeout': 1 });
  assert.ok(fake.checkPosts.length > before.posts, retry.err + retry.out);
  assert.ok(dispatchClaimIds(setup, initial.json.batch).length > before.claims);
});

test('RESTART accounting aggregates original and replacement in JSON, text and cache', async t => {
  const setup = harbor(t); let check = 0, originalId;
  const { fake, ...made } = await memoryRuntime(setup, {
    check: request => {
      check++;
      if (check === 1) {
        originalId = request.requestId;
        const refusal = { code: 'service-restarted', message: 'The runtime restarted.' };
        const answer = fake.job(originalId, 'check', 'unknown', { refusals: [refusal], report: { refusal, samples: [] } }, 2);
        answer.accounting_complete = false;
        Object.assign(answer.usage, { known_calls: 2, unknown_calls: 1, accounting_complete: false });
        answer.result.report.accounting_complete = false;
        return { status: 200, json: answer };
      }
      const answer = fake.job(request.requestId, 'check', 'passed', { exitCode: 0, report: { samples: [], accounting_complete: true } }, 3);
      answer.accounting_complete = true;
      Object.assign(answer.usage, { known_calls: 3, unknown_calls: 0, accounting_complete: true });
      return { status: 200, json: answer };
    },
    get: id => ({ status: 200, json: fake.job(id, 'check', 'passed', { exitCode: 0, report: { samples: [], accounting_complete: true } }, 2) }),
  });
  const initial = await runMemory(setup, fake, made, ['place-order'], { '--json': true, '--timeout': 1, '--cache-clear': true });
  const row = initial.json.rows[0], batch = initial.json.batch, replacementId = row.request_id;
  assert.deepEqual({ posts: fake.checkPosts.length, ids: new Set(fake.checkPosts.map(item => item.requestId)).size,
    claims: dispatchClaimIds(setup, batch).length }, { posts: 2, ids: 2, claims: 2 });
  assert.equal(row.calls, 'unknown'); assert.equal(row.known_calls, 5); assert.equal(row.unknown_calls, 1); assert.equal(row.accounting_complete, false);
  assert.match(initial.json.summary_line, /5 AI calls \+ 1 unknown/);
  const cachePath = join(setup.repo, '.pdd/cache/test/stories.json');
  const cache = JSON.parse(readFileSync(cachePath, 'utf8')).stories['user_stories/place-order.md'];
  assert.notEqual(cache.outcome, 'passed'); assert.equal(cache.pass, undefined);
  const original = JSON.parse(readFileSync(join(setup.state, 'batches', batch, `${originalId}.json`), 'utf8'));
  assert.equal(original.usage.unknown_calls, 1);

  await invokeMemory(setup, fake, made.ports.fetch, [originalId], { '--read': true });
  const observations = JSON.parse(readFileSync(join(setup.state, 'batches', batch, `${originalId}.observations.json`), 'utf8'));
  assert.ok(observations.some(item => item.usage.unknown_calls === 1));
  assert.equal(fake.checkPosts.length, 2);
  const text = await invokeMemory(setup, fake, made.ports.fetch, [batch], { '--read': true });
  assert.match(text.out, /5 AI calls \+ 1 unknown/);
  assert.equal(fake.checkPosts.length, 2);

  const later = await invokeMemory(setup, fake, made.ports.fetch, ['place-order'], { '--json': true }, true);
  assert.equal(later.json.rows[0].cached, undefined);
  assert.equal(fake.checkPosts.length, 3);
  assert.notEqual(replacementId, originalId);
});

test('RESTART recognizes report refusal and keeps one replacement with the original call ceiling', async t => {
  const setup = harbor(t); let check = 0;
  const { fake, ...made } = await memoryRuntime(setup, { check: request => {
    check++;
    if (check === 1 || check === 2) {
      const refusal = { code: 'service-restarted' };
      const answer = fake.job(request.requestId, 'check', 'unknown', { report: { refusal, samples: [] } }, check === 1 ? 2 : 1);
      Object.assign(answer, { accounting_complete: false });
      Object.assign(answer.usage, { known_calls: answer.usage.calls, unknown_calls: 1, accounting_complete: false });
      answer.result.report.accounting_complete = false;
      return { status: 200, json: answer };
    }
    assert.fail('one structured replacement must not produce a third Check POST');
  } });
  const result = await runMemory(setup, fake, made, ['place-order'], { '--json': true, '--timeout': 1, '--max-calls': '7' });
  assert.equal(fake.checkPosts.length, 2);
  assert.equal(new Set(fake.checkPosts.map(request => request.requestId)).size, 2);
  assert.ok(fake.checkPosts.every(request => request.max_calls === 7));
  assert.equal(dispatchClaimIds(setup, result.json.batch).length, 2);
  assert.equal(result.json.rows[0].calls, 'unknown');
});

test('CAPACITY1: confirmed zero-execution capacity is retried until the wait ends, then busy, never a test failure', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => e.command === 'check' ? { status: 200, json: capacity(f, e.request.requestId) } : f.normal(e));
  const result = await run(setup, fake, ['place-order'], { '--json': true, '--timeout': 1 });
  assert.equal(result.code, 5, result.err + result.out);
  assert.ok(checkPosts(fake).length > 3);
  assert.equal(new Set(checkPosts(fake).map(p => p.request.requestId)).size, checkPosts(fake).length);
  assert.equal(result.json.rows[0].state, 'not_run');
  assert.equal(result.json.rows[0].busy, true); assert.equal(result.json.rows[0].can_retry, true);
  assert.equal(result.json.rows[0].calls, 0); assert.equal(result.json.rows[0].checks, null);
  assert.match(result.json.summary_line, /: busy/); assert.doesNotMatch(result.out + result.err, /Fix what|fix the test|✗/);
  assert.ok(result.err.split('\n').includes('⏳ PDD is busy right now. 1 of your checks is waiting to start. You are not charged while you wait.')); assert.match(result.err, /pdd test --retry/);
  assert.equal(saved(setup, result.json.batch).rows[0].request_ids.length, checkPosts(fake).length);
  const before = fake.posts.length;
  const read = await run(setup, fake, [result.json.batch], { '--read': true, '--json': true });
  assert.equal(read.code, 5); assert.equal(read.json.rows[0].busy, true); assert.equal(fake.posts.length, before);
});

for (const [count, words, message] of [
  [1, ['place-order'], '⏳ PDD is busy right now. 1 of your checks is waiting to start. You are not charged while you wait.'],
  [2, [], '⏳ PDD is busy right now. 2 of your checks are waiting to start. You are not charged while you wait.'],
]) test(`CAPACITY local wait: ${count} held check${count === 1 ? '' : 's'} has exact progress and zero-call recovery`, async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command !== 'check') return f.normal(entry);
    const json = capacity(f, entry.request.requestId);
    json.result.report.refusal.details.retry_after = 300;
    return { status: 200, json };
  });
  const result = await run(setup, fake, words, { '--json': true, '--timeout': 1 });
  assert.equal(result.code, 5, result.err + result.out);
  assert.ok(result.err.split('\n').includes(message), result.err);
  assert.doesNotMatch(result.err, /checks are waiting locally|Your check is in line|Your check is next in line/);
  assert.equal(checkPosts(fake).length, count);
  assert.equal(fake.gets.length, 0);
  assert.equal(result.json.rows.length, count);
  for (const row of result.json.rows) {
    assert.equal(row.state, 'not_run');
    assert.equal(row.calls, 0);
    assert.equal(row.busy, true);
    assert.equal(row.can_retry, true);
  }
  assert.ok(saved(setup, result.json.batch).rows.every(row => row.request_ids.length === 1));
});

test('CAPACITY2: 17 tests use four configured active slots, adapt to a one-worker queue, and preserve all IDs', async t => {
  const setup = harbor(t, repo => {
    const file = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(file));
    rmSync(file); rmSync(join(repo, 'tests/unknown-item.json'));
    for (let i = 0; i < 17; i++) storyTest(repo, `order-${i}`);
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
  const first = await run(setup, fake, [], { '--json': true, '--max-calls': '9', '--timeout': 1 });
  assert.equal(first.code, 5); recover = true;
  const old = saved(setup, first.json.batch), before = fake.posts.length;
  const recovered = await run(setup, fake, [], { '--retry': first.json.batch, '--json': true });
  assert.equal(recovered.code, 0, recovered.out + recovered.err);
  assert.equal(fake.posts.length, before + 1); assert.equal(checkPosts(fake).at(-1).request.max_calls, 9);
  const after = saved(setup, first.json.batch);
  assert.equal(after.created_at, old.created_at);
  assert.deepEqual(after.rows.find(r => r.test.endsWith('unknown-item.json')).request_ids, old.rows.find(r => r.test.endsWith('unknown-item.json')).request_ids);
  assert.equal(after.rows.find(r => r.test.endsWith('place-order.json')).request_ids.length, old.rows.find(r => r.test.endsWith('place-order.json')).request_ids.length + 1);
  assert.deepEqual(parseArgv(['test', '--retry', first.json.batch]).options['--retry'], first.json.batch);

  recover = false;
  const second = await run(setup, fake, ['place-order'], { '--json': true, '--timeout': 1 });
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
  const first = await run(setup, fake, ['place-order'], { '--json': true, '--timeout': 1 });
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
    const code = await runCheck({ words: ['place-order'], options: { '--json': true, ...(interrupt ? {} : { '--timeout': 1 }) }, cwd: setup.repo }, made.ports);
    assert.equal(code, interrupt ? 3 : 5); assert.equal(checkPosts(fake).length, 1);
    assert.equal(JSON.parse(made.ports.stdout.text).rows[0].calls, 0);
  }
});

test('CAPACITY9: explicit recovery preserves a running job and a completed job while retrying capacity', async t => {
  const setup = harbor(t, repo => storyTest(repo, 'running'));
  let recover = false;
  const runningIds = new Set();
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check' && e.request.scenario.endsWith('running.json')) runningIds.add(e.request.requestId);
    if (e.command === 'check' && e.request.scenario.endsWith('place-order.json') && !recover)
      return { status: 200, json: capacity(f, e.request.requestId) };
    if (e.method === 'GET' && runningIds.has(e.url.split('/').at(-1))) return { status: 200, json: f.check(e.url.split('/').at(-1), 'running') };
    return f.normal(e);
  });
  const first = await run(setup, fake, [], { '--json': true, '--timeout': 1 }); assert.equal(first.code, 3);
  const original = saved(setup, first.json.batch), posts = fake.posts.length; recover = true;
  const retry = await run(setup, fake, [], { '--retry': first.json.batch, '--json': true });
  assert.equal(retry.code, 3); assert.equal(fake.posts.length, posts + 1);
  for (const path of ['tests/running.json', 'tests/unknown-item.json']) assert.deepEqual(saved(setup, first.json.batch).rows.find(r => r.test === path).request_ids,
    original.rows.find(r => r.test === path).request_ids);
});

test('CAPACITY10: unknown dispatched jobs still occupy four configured slots; held rows stay unposted', async t => {
  const setup = harbor(t, repo => {
    for (let i = 0; i < 8; i++) storyTest(repo, `extra-${i}`);
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
  const first = await run(setup, fake, ['place-order'], { '--json': true, '--timeout': 1 }); assert.equal(first.code, 5); assert.equal(checkPosts(fake).length, 1);
  const next = await run(setup, fake, [], { '--retry': first.json.batch, '--json': true });
  assert.equal(next.code, 5); assert.equal(checkPosts(fake).length, 1);
  assert.equal(next.json.rows[0].can_retry, true); assert.equal(next.json.rows[0].calls, 0);
  assert.equal(fake.gets.length, 0);
});
