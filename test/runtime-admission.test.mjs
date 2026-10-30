import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { listRuntimeJobs } from '../src/runtime-slots.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const checkPosts = fake => fake.posts.filter(e => e.command === 'check');
const makePorts = (setup, fake, extra) => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, extra);
const saved = (setup, batch) => JSON.parse(readFileSync(join(setup.state, 'batches', batch, 'batch.json')));
const restart = (f, id, calls = 'unknown') => f.job(id, 'check', 'unknown', { why: 'The result is unknown.', refusals: [{ code: 'service-restarted', message: 'The service restarted.' }] }, calls);

for (const kind of ['check', 'lint', 'try']) test(`admission: ${kind} succeeds after four confirmed unstarted refusals`, async t => {
  const setup = harbor(t), times = []; let made;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === kind) {
      times.push(made.clock.now);
      if (times.length <= 4) return { status: kind === 'lint' ? 503 : 429, headers: { 'retry-after': '7' }, json: {
        dispatch: 'not_started', error: { code: kind === 'lint' ? 'lint-queue-full' : 'server-full', details: { retryable: true, retry_after: 7 } },
      } };
    }
    if (e.command === 'try') return { status: 200, json: f.tryJob(e.request.requestId) };
    if (e.url.endsWith('/tests')) return { status: 200, json: { tests: [] } };
    if (e.url.endsWith('/approvals')) return { status: 200, json: { approvals: [] } };
    return f.normal(e);
  });
  made = makePorts(setup, fake);
  const code = kind === 'try' ? await runTry({ words: ['place-order'], cwd: setup.repo, options: { '--no-open': true, '--no-wait': true } }, made.ports)
    : await runCheck({ words: ['place-order'], cwd: setup.repo, options: { '--json': true, ...(kind === 'lint' ? { '--lint': true } : {}) } }, made.ports);
  assert.equal(code, 0, made.ports.stdout.text + made.ports.stderr.text); assert.equal(times.length, 5);
  for (let i = 1; i < times.length; i++) assert.ok(times[i] - times[i - 1] >= 7000);
  assert.equal(new Set(fake.posts.filter(e => e.command === kind).map(e => e.request.requestId)).size, 5);
  assert.ok(fake.posts.every(e => e.tar.equals(fake.posts[0].tar)));
  assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.length, 0);
  if (kind === 'try') {
    const repoState = JSON.parse(readFileSync(join(setup.state, 'repos', readdirSync(join(setup.state, 'repos'))[0])));
    assert.equal(repoState.tries['tests/place-order.json'].request_ids.length, 5);
  }
});

test('admission: runtime queue progress keeps the accepted ID and JSON output', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => e.command === 'check' ? { status: 202, json: { ...f.check(e.request.requestId, 'queued'), queue: { ahead: 5, slots_in_use: 8, slots: 8 } } } : f.normal(e));
  const { ports } = makePorts(setup, fake);
  const code = await runCheck({ words: ['place-order'], cwd: setup.repo, options: { '--json': true } }, ports);
  assert.equal(code, 0); assert.equal(checkPosts(fake).length, 1); assert.equal(JSON.parse(ports.stdout.text).rows[0].state, 'passed');
  assert.match(ports.stderr.text, /5 ahead.*8 of 8/);
});

test('maintenance: authenticated capacity window waits, rechecks and submits only afterward', async t => {
  const setup = harbor(t); let made, first = true, until; const reads = [];
  const fake = await fakeRuntime(t, (e, f) => { if (e.method === 'POST') assert.ok(made.clock.now >= until); return f.normal(e); });
  made = makePorts(setup, fake); until = made.clock.now + 7000;
  fake.capacity = e => { reads.push(e); return { status: 200, json: { maintenance: first ? (first = false, { until: new Date(until).toISOString(), reason: 'deploy' }) : null } }; };
  assert.equal(await runCheck({ words: ['place-order'], cwd: setup.repo, options: { '--json': true } }, made.ports), 0);
  assert.ok(reads.length >= 2); assert.ok(reads.every(e => e.headers.authorization?.startsWith('Bearer ')));
  assert.match(made.ports.stderr.text, /maintenance.*deploy/); assert.equal(checkPosts(fake).length, 1);
});

for (const kind of ['check', 'lint', 'try']) test(`maintenance: ${kind} handles direct 503 after capacity 404`, async t => {
  const setup = harbor(t); let count = 0, made, at;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === kind && ++count === 1) {
      at = made.clock.now;
      return { status: 503, headers: { 'retry-after': '7' }, json: { dispatch: 'not_started', error: { code: 'maintenance', details: { until: new Date(at + 9000).toISOString(), reason: 'deploy' } } } };
    }
    if (e.command === kind) assert.ok(made.clock.now >= at + 9000);
    if (e.command === 'try') return { status: 200, json: f.tryJob(e.request.requestId) };
    if (e.url.endsWith('/tests')) return { status: 200, json: { tests: [] } };
    if (e.url.endsWith('/approvals')) return { status: 200, json: { approvals: [] } };
    return f.normal(e);
  });
  made = makePorts(setup, fake);
  const code = kind === 'try' ? await runTry({ words: ['place-order'], cwd: setup.repo, options: { '--no-open': true, '--no-wait': true } }, made.ports)
    : await runCheck({ words: ['place-order'], cwd: setup.repo, options: { '--json': true, ...(kind === 'lint' ? { '--lint': true } : {}) } }, made.ports);
  assert.equal(code, 0, made.ports.stderr.text + made.ports.stdout.text); assert.equal(count, 2); assert.match(made.ports.stderr.text, /maintenance.*deploy/);
});

for (const interrupt of [false, true]) test(`maintenance: ${interrupt ? 'interrupt' : 'deadline'} sends no POST and leaves no ticket`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, () => { assert.fail('maintenance sent a job'); });
  const made = makePorts(setup, fake);
  fake.capacity = () => ({ status: 200, json: { maintenance: { until: new Date(made.clock.now + 600_000).toISOString(), reason: 'deploy' } } });
  if (interrupt) made.ports.sleep = async ms => { made.clock.now += ms; made.clock.interrupt(); };
  assert.equal(await runCheck({ words: ['place-order'], cwd: setup.repo, options: { '--json': true } }, made.ports), interrupt ? 3 : 5);
  assert.equal(fake.posts.length, 0); assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.length, 0);
  assert.equal(JSON.parse(made.ports.stdout.text).rows[0].calls, 0);
});

for (const reply of [
  { status: 401, json: { error: { code: 'auth-required' } } },
  { status: 403, json: { error: { code: 'not-invited' } } },
  { status: 503, json: { error: { code: 'cloud-unavailable' } } },
]) test(`capacity: gate ${reply.json.error.code} sends no job`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, () => { assert.fail('capacity gate sent a job'); }); fake.capacity = () => reply;
  const { ports } = makePorts(setup, fake);
  assert.equal(await runCheck({ words: ['place-order'], cwd: setup.repo, options: { '--json': true } }, ports), 5);
  assert.equal(fake.posts.length, 0); assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.length, 0);
});

test('restart: one structured restart receipt replaces once, retaining source, caps, receipts and cumulative known calls', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => e.command === 'check' ? { status: 200, json: checkPosts(f).length === 1 ? restart(f, e.request.requestId, 2) : f.check(e.request.requestId) } : f.normal(e));
  const { ports } = makePorts(setup, fake);
  assert.equal(await runCheck({ words: ['place-order'], cwd: setup.repo, options: { '--json': true, '--max-calls': '9' } }, ports), 0, ports.stderr.text + ports.stdout.text);
  const report = JSON.parse(ports.stdout.text), batch = saved(setup, report.batch);
  assert.equal(checkPosts(fake).length, 2); assert.equal(batch.rows[0].request_ids.length, 2); assert.equal(report.rows[0].calls, 3);
  assert.ok(checkPosts(fake).every(e => e.request.max_calls === 9 && e.request.source_sha256 === batch.source_sha256));
  for (const id of batch.rows[0].request_ids) assert.ok(JSON.parse(readFileSync(join(setup.state, 'batches', report.batch, `${id}.json`))));
  assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.length, 0);
});

test('restart: unknown accounting remains unknown and a second restarted attempt never replaces again', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => e.command === 'check' ? { status: 200, json: restart(f, e.request.requestId) } : f.normal(e));
  const first = makePorts(setup, fake);
  assert.equal(await runCheck({ words: ['place-order'], cwd: setup.repo, options: { '--json': true } }, first.ports), 3);
  const report = JSON.parse(first.ports.stdout.text); assert.equal(report.rows[0].calls, 'unknown'); assert.equal(checkPosts(fake).length, 2);
  for (const options of [{ '--read': true, '--json': true }, { '--retry': report.batch, '--json': true }]) {
    const next = makePorts(setup, fake); next.clock.now = first.clock.now;
    assert.equal(await runCheck({ words: options['--read'] ? [report.batch] : [], cwd: setup.repo, options }, next.ports), 3);
    assert.equal(checkPosts(fake).length, 2); assert.equal(JSON.parse(next.ports.stdout.text).rows[0].calls, 'unknown');
  }
});

test('restart: overlapping saved readers share one durable replacement allowance', async t => {
  const setup = harbor(t); let resume = false;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check') return { status: 202, json: resume ? f.check(e.request.requestId) : f.check(e.request.requestId, 'running') };
    if (e.method === 'GET' && checkPosts(f).length && e.url.endsWith(checkPosts(f)[0].request.requestId)) return { status: 200, json: resume ? restart(f, checkPosts(f)[0].request.requestId) : f.check(checkPosts(f)[0].request.requestId, 'running') };
    return f.normal(e);
  });
  const first = makePorts(setup, fake); assert.equal(await runCheck({ words: ['place-order'], cwd: setup.repo, options: { '--json': true } }, first.ports), 3);
  const batch = JSON.parse(first.ports.stdout.text).batch; resume = true;
  const readers = [makePorts(setup, fake), makePorts(setup, fake)]; for (const made of readers) made.clock.now = first.clock.now;
  await Promise.all(readers.map(made => runCheck({ words: [batch], cwd: setup.repo, options: { '--read': true, '--json': true } }, made.ports)));
  assert.equal(checkPosts(fake).length, 2); assert.equal(saved(setup, batch).rows[0].request_ids.length, 2);
  const again = makePorts(setup, fake); await runCheck({ words: [batch], cwd: setup.repo, options: { '--read': true, '--json': true } }, again.ports);
  assert.equal(checkPosts(fake).length, 2);
});

test('restart: changed source and display-only restart wording authorize no replacement', async t => {
  for (const changed of [false, true]) {
    const setup = harbor(t); let resume = false;
    const fake = await fakeRuntime(t, (e, f) => {
      if (e.command === 'check') return { status: 202, json: f.check(e.request.requestId, 'running') };
      if (e.method === 'GET' && checkPosts(f).length) {
        const id = e.url.split('/').at(-1);
        return { status: 200, json: resume ? changed ? restart(f, id) : f.job(id, 'check', 'unknown', { why: 'service-restarted' }, 'unknown') : f.check(id, 'running') };
      }
      return f.normal(e);
    });
    const made = makePorts(setup, fake); assert.equal(await runCheck({ words: ['place-order'], cwd: setup.repo, options: { '--json': true } }, made.ports), 3);
    const batch = JSON.parse(made.ports.stdout.text).batch; resume = true;
    if (changed) writeFileSync(join(setup.repo, 'user_stories/place-order.md'), readFileSync(join(setup.repo, 'user_stories/place-order.md')) + '\nChanged source.\n');
    const next = makePorts(setup, fake); await runCheck({ words: [batch], cwd: setup.repo, options: { '--read': true, '--json': true } }, next.ports);
    assert.equal(checkPosts(fake).length, 1);
  }
});

test('leases: a later live reader releases terminal check/lint reservations without requiring producer death', async t => {
  for (const kind of ['check', 'lint']) {
    const setup = harbor(t); let resume = false;
    const fake = await fakeRuntime(t, (e, f) => {
      if (e.command === kind) return { status: 202, json: f.job(e.request.requestId, kind, 'running') };
      if (e.method === 'GET') {
        const id = e.url.split('/').at(-1);
        return { status: 200, json: resume ? kind === 'lint' ? f.lint(id) : f.check(id) : f.job(id, kind, 'running') };
      }
      return f.normal(e);
    });
    const first = makePorts(setup, fake);
    assert.equal(await runCheck({ words: ['place-order'], cwd: setup.repo, options: { '--json': true, ...(kind === 'lint' ? { '--lint': true } : {}) } }, first.ports), 3);
    assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.length, 1);
    resume = true; const next = makePorts(setup, fake);
    await runCheck({ words: [JSON.parse(first.ports.stdout.text).batch], cwd: setup.repo, options: { '--read': true, '--json': true } }, next.ports);
    assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.length, 0);
  }
});

test('admission: remote lint, Check and Try setup in different repos share the default four slots', { timeout: 180_000 }, async t => {
  const setups = Array.from({ length: 5 }, () => harbor(t)); let active = 0, peak = 0;
  const jobs = new Map(), completed = new Set(), pending = [];
  let release;
  const terminalReplies = new Promise(done => { release = done; });
  const fake = await fakeRuntime(t, async (e, f) => {
    if (e.command) {
      assert.equal(jobs.has(e.request.requestId), false, 'each command posts one unique request');
      active++; peak = Math.max(peak, active); assert.ok(active <= 4, 'default capacity is never exceeded');
      jobs.set(e.request.requestId, e.command);
      return { status: 202, json: f.job(e.request.requestId, e.command, 'queued') };
    }
    if (e.url.endsWith('/tests')) return { status: 200, json: { tests: [] } };
    if (e.url.endsWith('/approvals')) return { status: 200, json: { approvals: [] } };
    const id = e.url.split('/').at(-1), kind = jobs.get(id); assert.ok(kind);
    await terminalReplies;
    if (!completed.has(id)) { completed.add(id); active--; }
    assert.ok(active >= 0 && active <= 4);
    return { status: 200, json: kind === 'lint' ? f.lint(id) : kind === 'try' ? f.tryJob(id) : f.check(id) };
  });
  const start = i => {
    const setup = setups[i];
    const made = makePorts({ ...setup, state: setups[0].state }, fake, { now: Date.now, sleep: ms => new Promise(done => setTimeout(done, ms)), pollMs: 20 });
    return i < 2 ? runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, made.ports)
      : runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true, ...(i === 2 ? { '--lint': true } : {}) } }, made.ports);
  };
  const waitFor = async predicate => {
    const deadline = Date.now() + 60_000;
    while (!await predicate()) {
      assert.ok(Date.now() < deadline, 'capacity barrier watchdog expired');
      await new Promise(done => setTimeout(done, 20));
    }
  };
  try {
    // Terminal replies stay closed while the first four callers fill capacity.
    pending.push(...Array.from({ length: 4 }, (_, i) => start(i)));
    await waitFor(() => active === 4);
    pending.push(start(4));
    let snapshot;
    await waitFor(async () => {
      snapshot = (await listRuntimeJobs({ stateDir: setups[0].state, origin: fake.origin })).jobs;
      return snapshot.some(row => row.state === 'waiting');
    });
    assert.equal(active, 4); assert.equal(fake.posts.length, 4, 'the fifth caller waits without a POST');
    assert.equal(snapshot.filter(row => row.state === 'active').length, 4);
    assert.deepEqual(snapshot.filter(row => row.state === 'active').flatMap(row => row.request_ids).sort(), [...jobs.keys()].sort());
    assert.deepEqual(snapshot.filter(row => row.state === 'waiting').map(row => row.request_ids), [[]]);
    release();
    assert.deepEqual(await Promise.all(pending), [0, 0, 0, 0, 0]);
    assert.equal(active, 0); assert.equal(peak, 4); assert.equal(completed.size, 9); assert.equal(jobs.size, 9);
    assert.deepEqual([...jobs.values()].sort(), ['check', 'check', 'lint', 'lint', 'lint', 'lint', 'lint', 'try', 'try']);
    assert.equal(fake.posts.length, 9);
    assert.equal((await listRuntimeJobs({ stateDir: setups[0].state, origin: fake.origin })).jobs.length, 0);
  } finally { release(); await Promise.allSettled(pending); }
});

test('admission: invalid PDD_MAX_JOBS warns and keeps a usable default', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => f.normal(e));
  const made = makePorts(setup, fake); made.ports.env.PDD_MAX_JOBS = '0';
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, made.ports), 0);
  assert.match(made.ports.stderr.text, /PDD_MAX_JOBS.*4/);
});

test('admission: contended registration cannot POST after cancellation or deadline', async t => {
  for (const interrupt of [false, true]) {
    const setup = harbor(t), fake = await fakeRuntime(t, () => { assert.fail('blocked registration posted'); });
    const made = makePorts(setup, fake); const records = new Map(), refreshed = new Map(); let claims = 0;
    made.ports.slotFiles = {
      listRecords: () => ({ jobs: [...records.values()].filter(row => row.state) }),
      exclusiveCreate: (path, row) => {
        if (path.endsWith('/claim.json') && ++claims > 1) return false;
        if (records.has(path)) return false; records.set(path, row); refreshed.set(path, made.clock.now); return true;
      },
      writeAtomic: (path, row) => { records.set(path, row); refreshed.set(path, made.clock.now); }, unlink: path => records.delete(path),
      modifiedAt: path => records.has(path) ? refreshed.get(path) : null,
      touch: path => { if (!records.has(path)) return false; refreshed.set(path, made.clock.now); return true; },
    };
    made.ports.sleep = async () => { if (interrupt) made.clock.interrupt(); else made.clock.now += 90_000; };
    const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, made.ports);
    assert.equal(code, interrupt ? 3 : 5); assert.equal(fake.posts.length, 0);
    assert.equal([...records.values()].filter(row => row.state).length, 0);
  }
});

test('leases: dead-owner runtime reads require exact ID and command before reclaiming', async t => {
  const { mkdirSync } = await import('node:fs');
  for (const wrong of ['id', 'command', 'unknown', 'missing']) {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (e, f) => {
      if (e.method !== 'GET') assert.fail('uncertain dead lease permitted a POST');
      const id = e.url.split('/').at(-1);
      return wrong === 'missing' ? { status: 404, json: {} } : { status: 200, json: wrong === 'command' ? f.lint(id)
        : wrong === 'unknown' ? f.job(id, 'check', 'unknown', { why: 'The result is unknown.' }, 'unknown') : { ...f.check(id), requestId: 'wrong' } };
    });
    const made = makePorts(setup, fake); made.ports.env.PDD_MAX_JOBS = '1';
    const directory = join(setup.state, 'slots', encodeURIComponent(new URL(fake.origin).host)); mkdirSync(directory, { recursive: true });
    writeFileSync(join(directory, 'old.json'), JSON.stringify({ id: 'old', state: 'active', pid: 2147483647, kind: 'check', started_at: made.clock.now, request_ids: ['old-run'] }));
    made.ports.sleep = async ms => { made.clock.now += 90_000; };
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, made.ports), 5);
    assert.equal(fake.posts.length, 0); assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs[0].id, 'old');
  }
});

for (const invalid of ['positive', 'unknown', 'incomplete', 'checks']) test(`admission: contradictory direct ${invalid} accounting cannot authorize another attempt`, async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check') return { status: 503, json: { dispatch: 'not_started', error: { code: 'check-queue-full', details: { retryable: true } },
      ...(invalid === 'positive' ? { usage: { calls: 1 } } : invalid === 'unknown' ? { usage: { calls: 'unknown' } } : invalid === 'incomplete' ? { usage: { calls: 0, accounting_complete: false } }
        : { result: { report: { samples: [{ steps: [{ checks: [{ passed: true }] }] }] } } }) } };
    if (e.method === 'GET') return { status: 404, json: {} };
    return f.normal(e);
  });
  const { ports } = makePorts(setup, fake);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, ports), 3);
  assert.equal(checkPosts(fake).length, 1); assert.ok(fake.gets.length); assert.equal(JSON.parse(ports.stdout.text).rows[0].can_retry, false);
});

test('admission: HTTP Retry-After overrides lint error details', async t => {
  const setup = harbor(t); let made, at;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint' && f.posts.length === 1) { at = made.clock.now; return { status: 503, headers: { 'retry-after': '7' }, json: { error: { code: 'lint-queue-full', details: { retryable: true, retry_after: 1 } } } }; }
    if (e.command === 'lint') assert.ok(made.clock.now - at >= 7000);
    return f.normal(e);
  });
  made = makePorts(setup, fake); assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true, '--json': true } }, made.ports), 0);
});

for (const priorCalls of [2, 'unknown']) test(`restart: capacity attempts retain cumulative ${priorCalls} usage through timeout`, async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check') return checkPosts(f).length === 1 ? { status: 200, json: restart(f, e.request.requestId, priorCalls) }
      : { status: 503, headers: { 'retry-after': '7' }, json: { dispatch: 'not_started', error: { code: 'check-queue-full', details: { retryable: true } } } };
    return f.normal(e);
  });
  const { ports } = makePorts(setup, fake);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, ports), 5);
  assert.ok(checkPosts(fake).length > 3); assert.equal(JSON.parse(ports.stdout.text).rows[0].calls, priorCalls);
});

test('restart: a passed replacement counts confirmed admission attempts as zero calls', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check') return checkPosts(f).length === 1 ? { status: 200, json: restart(f, e.request.requestId, 2) }
      : checkPosts(f).length === 2 ? { status: 503, headers: { 'retry-after': '1' }, json: { dispatch: 'not_started', error: { code: 'check-queue-full', details: { retryable: true } } } }
        : { status: 200, json: f.check(e.request.requestId) };
    return f.normal(e);
  });
  const { ports } = makePorts(setup, fake);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, ports), 0);
  assert.equal(checkPosts(fake).length, 3); assert.equal(JSON.parse(ports.stdout.text).rows[0].calls, 3);
});

for (const kind of ['check', 'lint', 'try']) for (const providerCalls of ['unknown', null]) test(`admission: ${kind} cannot retry explicit provider accounting ${providerCalls}`, async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === kind) return { status: 503, json: { dispatch: 'not_started', error: { code: kind === 'lint' ? 'lint-queue-full' : 'check-queue-full', details: { retryable: true } }, result: { report: { provider_calls: providerCalls } } } };
    if (e.method === 'GET') return { status: 404, json: {} };
    return f.normal(e);
  });
  const { ports } = makePorts(setup, fake);
  const code = kind === 'try' ? await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, ports)
    : await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true, ...(kind === 'lint' ? { '--lint': true } : {}) } }, ports);
  assert.equal(code, 3); assert.equal(fake.posts.filter(e => e.command === kind).length, 1);
});

for (const providerCalls of ['unknown', null]) test(`admission: terminal check capacity cannot override provider accounting ${providerCalls}`, async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => e.command === 'check' ? { status: 200, json: f.job(e.request.requestId, 'check', 'refused', {
    refusals: [{ code: 'check-queue-timeout' }], report: { dispatch: 'not_started', provider_calls: providerCalls },
  }, 0) } : f.normal(e));
  const { ports } = makePorts(setup, fake);
  assert.notEqual(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, ports), 0);
  assert.equal(checkPosts(fake).length, 1); assert.equal(JSON.parse(ports.stdout.text).rows[0].can_retry, false);
});
