import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { existsSync, readFileSync, writeFileSync, mkdirSync, statSync } from 'node:fs';
import { join } from 'node:path';
import * as client from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor, temp } from './runtime-fake.mjs';

const read = file => JSON.parse(readFileSync(file, 'utf8'));
const deferred = () => { let resolve; const promise = new Promise(done => { resolve = done; }); return { promise, resolve }; };
const pause = ms => new Promise(done => setTimeout(done, ms));
const checks = fake => fake.posts.filter(p => p.command === 'check');
async function fixture(t) {
  const setup = harbor(t); let delay = false;
  const fake = await fakeRuntime(t, async (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.command === 'lint') return { status: 200, json: f.lint(id) };
    if (delay) await pause(40);
    const answer = f.check(id); answer.usage.calls = 4;
    return { status: 200, json: answer };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
  async function run(options = {}, words = [], extra = {}) {
    const { ports, clock } = portsFor(env, extra);
    const code = await client.runCheck({ cwd: setup.repo, words, options: { '--json': true, ...options } }, ports);
    return { code, out: ports.stdout.text, err: ports.stderr.text, json: ports.stdout.text ? JSON.parse(ports.stdout.text) : null, clock };
  }
  const first = await run({}, ['place-order']); assert.equal(first.code, 0);
  const batch = first.json.batch, folder = join(setup.state, 'batches', batch), file = join(folder, 'batch.json');
  const saved = read(file);
  Object.assign(saved.rows[0], { phase: 'local', state: 'not_run', request_ids: [], eligible: true, can_retry: true, busy: true, retry_at: null });
  writeFileSync(file, JSON.stringify(saved)); delay = true;
  return { setup, env, fake, run, batch, folder, file };
}
function passed(r) {
  assert.equal(r.code, 0, r.err + r.out);
  assert.equal(r.json.rows[0].state, 'passed');
  assert.equal(r.json.rows[0].calls, 4);
}

test('2675: two same-process retries send one check and keep its receipt and accounting', async t => {
  const r = await fixture(t), before = checks(r.fake).length;
  const results = await Promise.all([r.run({ '--retry': r.batch }), r.run({ '--retry': r.batch })]);
  assert.equal(checks(r.fake).length - before, 1, 'only one held check may be sent');
  results.forEach(passed);
  const ids = read(r.file).rows[0].request_ids;
  assert.deepEqual(ids, [checks(r.fake).at(-1).request.requestId]);
  assert.equal(read(join(r.folder, `${ids[0]}.json`)).usage.calls, 4);
  const later = await r.run({ '--read': true }, [r.batch]); passed(later);
  assert.deepEqual(read(r.file).rows[0].request_ids, ids);
});

function worker(r, options, words = []) {
  const source = `import {runCheck} from ${JSON.stringify(new URL('../src/runtime-client.mjs', import.meta.url).href)};
    import {portsFor} from ${JSON.stringify(new URL('./runtime-fake.mjs', import.meta.url).href)};
    const {ports}=portsFor(${JSON.stringify(r.env)}); console.error('START');
    const code=await runCheck(${JSON.stringify({ cwd: r.setup.repo, words, options: { '--json': true, ...options } })},ports); process.exitCode=code;`;
  const child = spawn(process.execPath, ['--input-type=module', '-e', source], { stdio: ['ignore', 'pipe', 'pipe'] });
  let out = '', err = ''; const started = deferred();
  child.stdout.on('data', chunk => { out += chunk; });
  child.stderr.on('data', chunk => { err += chunk; if (err.includes('START')) started.resolve(); });
  const done = new Promise((resolve, reject) => { child.on('error', reject); child.on('close', code => resolve({ code, out, err, json: out ? JSON.parse(out) : null })); });
  return { child, started: started.promise, done };
}

test('2675: separate processes serialize retry admission and the waiting process reloads', async t => {
  const r = await fixture(t), before = checks(r.fake).length;
  const a = worker(r, { '--retry': r.batch }), b = worker(r, { '--retry': r.batch });
  t.after(() => { a.child.kill(); b.child.kill(); });
  await Promise.all([a.started, b.started]);
  const results = await Promise.all([a.done, b.done]);
  assert.equal(checks(r.fake).length - before, 1, 'an in-memory lock is insufficient');
  results.forEach(passed);
  assert.equal(results[0].json.rows[0].request_id, results[1].json.rows[0].request_id);
  assert.deepEqual(read(r.file).rows[0].request_ids, [results[0].json.rows[0].request_id]);
});

test('2675: a batch read holds ownership across its refresh and cannot overwrite a retry', async t => {
  const setup = harbor(t); const entered = deferred(), resume = deferred(); let gate = false;
  const fake = await fakeRuntime(t, async (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.command === 'lint') return { status: 200, json: f.lint(id) };
    if (gate && e.method === 'GET') { entered.resolve(); await resume.promise; }
    return { status: 200, json: f.check(id) };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
  async function run(options = {}, words = []) { const { ports } = portsFor(env); const code = await client.runCheck({ cwd: setup.repo, words, options: { '--json': true, ...options } }, ports); return { code, out: ports.stdout.text, err: ports.stderr.text }; }
  const first = JSON.parse((await run()).out), folder = join(setup.state, 'batches', first.batch), file = join(folder, 'batch.json');
  const saved = read(file), old = saved.rows[0].request_ids[0];
  writeFileSync(join(folder, `${old}.json`), JSON.stringify(fake.check(old, 'running')));
  Object.assign(saved.rows[1], { state: 'not_run', phase: 'local', request_ids: [], eligible: true, busy: true, can_retry: true, retry_at: null });
  writeFileSync(file, JSON.stringify(saved)); gate = true;
  const reading = run({ '--read': true }, [first.batch]); await entered.promise;
  const before = checks(fake).length, retrying = run({ '--retry': first.batch });
  await pause(80);
  const postsWhileReadOwns = checks(fake).length - before;
  resume.resolve(); await Promise.all([reading, retrying]);
  assert.equal(postsWhileReadOwns, 0, 'retry cannot decide against a snapshot being refreshed');
  assert.equal(checks(fake).length - before, 1);
  assert.deepEqual(read(file).rows[1].request_ids, [checks(fake).at(-1).request.requestId]);
});

test('2675: acquisition is a runtime-faked boundary and releases after source refusal or exception', async t => {
  const r = await fixture(t); let acquired = 0, released = 0;
  const extra = { acquireBatchLock: async folder => { assert.equal(folder, r.folder); acquired++; return () => { released++; }; } };
  const story = join(r.setup.repo, 'user_stories/place-order.md'), original = readFileSync(story);
  writeFileSync(story, 'changed');
  const refusal = await r.run({ '--retry': r.batch }, [], extra);
  assert.equal(refusal.code, 2); assert.equal(acquired, 1); assert.equal(released, 1);
  writeFileSync(story, original);
  await assert.rejects(r.run({ '--retry': r.batch }, [], { ...extra, gh: () => { throw new Error('injected auth failure'); } }), /injected auth failure/);
  assert.equal(acquired, 2); assert.equal(released, 2);
});

test('2675: an interrupted ownership wait leaves batch and summary untouched and sends nothing', async t => {
  const r = await fixture(t), batch = readFileSync(r.file), summaryPath = join(r.folder, 'summary.json'), summary = readFileSync(summaryPath);
  let stop, calls = 0; const before = r.fake.posts.length;
  const result = await r.run({ '--retry': r.batch }, [], {
    onInterrupt: handler => { stop = handler; return () => {}; },
    acquireBatchLock: async (folder, { signal, timeoutMs }) => { calls++; assert.equal(folder, r.folder); assert.ok(timeoutMs <= 30000); stop(); assert.equal(signal.aborted, true); throw Object.assign(new Error('interrupted'), { code: 'BATCH_LOCK_INTERRUPTED' }); }
  });
  assert.equal(calls, 1); assert.equal(result.code, 3); assert.match(result.err, /wait|stop|interrupt/i);
  assert.equal(r.fake.posts.length, before); assert.deepEqual(readFileSync(r.file), batch); assert.deepEqual(readFileSync(summaryPath), summary);
});

for (const kind of ['live', 'dead', 'malformed', 'guard']) test(`2675: native lock handles ${kind} owners without unsafe age expiry`, async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function', 'native lock boundary must exist');
  const folder = temp(t), lock = join(folder, 'batch.lock'), guard = join(folder, 'batch.lock.claim');
  let deadPid;
  if (kind === 'dead') { const child = spawn(process.execPath, ['-e', '']); deadPid = child.pid; await new Promise(done => child.on('close', done)); }
  writeFileSync(kind === 'guard' ? guard : lock, kind === 'malformed' ? 'not a pid' : String(kind === 'dead' ? deadPid : process.pid));
  if (kind === 'dead') {
    const release = await client.acquireRuntimeBatchLock(folder, { timeoutMs: 10 });
    assert.equal(readFileSync(lock, 'utf8'), String(process.pid)); assert.equal(statSync(lock).mode & 0o777, 0o600);
    release(); release(); assert.equal(existsSync(lock), false);
  } else {
    const bytes = readFileSync(kind === 'guard' ? guard : lock);
    await assert.rejects(client.acquireRuntimeBatchLock(folder, { timeoutMs: 5 }), error => error.code === 'BATCH_LOCK_BUSY');
    assert.deepEqual(readFileSync(kind === 'guard' ? guard : lock), bytes);
  }
});

test('2675: native lock permits independent batches and interrupted wait cannot release the owner', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const folder = temp(t), other = join(folder, 'other'); mkdirSync(other);
  const release = await client.acquireRuntimeBatchLock(folder), releaseOther = await client.acquireRuntimeBatchLock(other);
  const controller = new AbortController(); const waiting = client.acquireRuntimeBatchLock(folder, { signal: controller.signal }); controller.abort();
  await assert.rejects(waiting, error => error.code === 'BATCH_LOCK_INTERRUPTED');
  assert.equal(readFileSync(join(folder, 'batch.lock'), 'utf8'), String(process.pid));
  releaseOther(); release();
  const again = await client.acquireRuntimeBatchLock(folder); again();
});
