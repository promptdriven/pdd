import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { existsSync, readFileSync, writeFileSync, mkdirSync, statSync } from 'node:fs';
import { join } from 'node:path';
import { hostname } from 'node:os';
import * as client from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor, temp } from './runtime-fake.mjs';

const read = file => JSON.parse(readFileSync(file, 'utf8'));
const deferred = () => { let resolve; const promise = new Promise(done => { resolve = done; }); return { promise, resolve }; };
const pause = ms => new Promise(done => setTimeout(done, ms));
const checks = fake => fake.posts.filter(p => p.command === 'check');
async function fixture(t) {
  const setup = harbor(t); let delay = false, held = null;
  const fake = await fakeRuntime(t, async (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.command === 'lint') return { status: 200, json: f.lint(id) };
    if (held && e.command === 'check') { const current = held; held = null; current.entered.resolve(); await current.resume.promise; }
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
  return { setup, env, fake, run, batch, folder, file, holdCheck: () => { const current = { entered: deferred(), resume: deferred() }; held = current; return current; } };
}
function passed(r) {
  assert.equal(r.code, 0, r.err + r.out);
  assert.equal(r.json.rows[0].state, 'passed');
  assert.equal(r.json.rows[0].calls, 4);
}

test('2675: two same-process retries send one check and keep its receipt and accounting', async t => {
  const r = await fixture(t), before = checks(r.fake).length;
  const gate = r.holdCheck(), first = r.run({ '--retry': r.batch }); await gate.entered.promise;
  const second = await r.run({ '--retry': r.batch }); gate.resume.resolve();
  const results = [await first, second];
  assert.equal(results[0].clock.uuids, 1); assert.equal(second.clock.uuids, 0, 'live competitor allocates no request ID');
  assert.equal(checks(r.fake).length - before, 1, 'only one held check may be sent');
  assert.equal(results.filter(r => r.code === 0).length, 1);
  passed(results.find(r => r.code === 0));
  const busy = results.find(r => r.code !== 0); assert.equal(busy.code, 2); assert.match(busy.err, /pdd check --read/);
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
    const code=await runCheck(${JSON.stringify({ cwd: r.setup.repo, words, options: { '--json': true, ...options } })},ports); process.stdout.write(ports.stdout.text); process.stderr.write(ports.stderr.text); process.exitCode=code;`;
  const child = spawn(process.execPath, ['--input-type=module', '-e', source], { stdio: ['ignore', 'pipe', 'pipe'] });
  let out = '', err = ''; const started = deferred();
  child.stdout.on('data', chunk => { out += chunk; });
  child.stderr.on('data', chunk => { err += chunk; if (err.includes('START')) started.resolve(); });
  const done = new Promise((resolve, reject) => { child.on('error', reject); child.on('close', code => resolve({ code, out, err, json: out ? JSON.parse(out) : null })); });
  return { child, started: started.promise, done };
}

test('2675: separate processes admit one retry and refuse the live competitor', async t => {
  const r = await fixture(t), before = checks(r.fake).length;
  const gate = r.holdCheck(), a = worker(r, { '--retry': r.batch }); await gate.entered.promise;
  const b = worker(r, { '--retry': r.batch });
  t.after(() => { a.child.kill(); b.child.kill(); gate.resume.resolve(); });
  await Promise.all([a.started, b.started]);
  const second = await b.done; gate.resume.resolve();
  const results = [await a.done, second];
  assert.equal(checks(r.fake).length - before, 1, 'an in-memory lock is insufficient');
  assert.equal(results.filter(r => r.code === 0).length, 1);
  passed(results.find(r => r.code === 0));
  const busy = results.find(r => r.code !== 0); assert.equal(busy.code, 2); assert.match(busy.err, /pdd check --read/);
  assert.deepEqual(read(r.file).rows[0].request_ids, [results.find(r => r.code === 0).json.rows[0].request_id]);
});

test('2675: a batch read holds ownership across its refresh and cannot overwrite a retry', async t => {
  const setup = harbor(t); const entered = deferred(), resume = deferred(); let gate = false;
  const fake = await fakeRuntime(t, async (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.command === 'lint') return { status: 200, json: f.lint(id) };
    if (gate && e.method === 'GET') { gate = false; entered.resolve(); await resume.promise; }
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
  assert.equal(checks(fake).length - before, 0, 'competing retry is refused while batch read owns it');
  const result = await run({ '--retry': first.batch }); assert.equal(result.code, 0);
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

for (const kind of ['live', 'dead', 'foreign', 'malformed']) test(`2675: native lock handles ${kind} owners without unsafe age expiry`, async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function', 'native lock boundary must exist');
  const folder = temp(t), lock = join(folder, 'batch.lock'), guard = join(folder, 'batch.lock.claim');
  let deadPid;
  if (kind === 'dead' || kind === 'foreign') { const child = spawn(process.execPath, ['-e', '']); deadPid = child.pid; await new Promise(done => child.on('close', done)); }
  writeFileSync(kind === 'guard' ? guard : lock, kind === 'malformed' ? 'not a pid' : JSON.stringify({ pid: kind === 'dead' || kind === 'foreign' ? deadPid : process.pid, host: kind === 'foreign' ? 'another-host' : hostname(), started_at: '2026-10-01T00:00:00.000Z' }));
  if (kind === 'dead') {
    const warnings = []; const release = await client.acquireRuntimeBatchLock(folder, { onWarning: line => warnings.push(line) });
    assert.equal(warnings.length, 1); assert.match(warnings[0], /recover|dead|abandon/i);
    assert.equal(read(lock).pid, process.pid); assert.equal(read(lock).host, hostname()); assert.ok(Date.parse(read(lock).started_at)); assert.equal(statSync(lock).mode & 0o777, 0o600);
    release(); release(); assert.equal(existsSync(lock), false);
  } else {
    const bytes = readFileSync(kind === 'guard' ? guard : lock);
    await assert.rejects(client.acquireRuntimeBatchLock(folder, {}), error => error.code === 'BATCH_LOCK_BUSY');
    assert.deepEqual(readFileSync(kind === 'guard' ? guard : lock), bytes);
  }
});

test('2675: native lock permits independent batches and a refusal cannot release the owner', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const folder = temp(t), other = join(folder, 'other'); mkdirSync(other);
  const release = await client.acquireRuntimeBatchLock(folder), releaseOther = await client.acquireRuntimeBatchLock(other);
  await assert.rejects(client.acquireRuntimeBatchLock(folder), error => error.code === 'BATCH_LOCK_BUSY');
  assert.equal(read(join(folder, 'batch.lock')).pid, process.pid);
  releaseOther(); release();
  const again = await client.acquireRuntimeBatchLock(folder); again();
});


test('2675: ownership refusal, sends nothing and preserves saved data', async t => {
  const r = await fixture(t), batch = readFileSync(r.file), summary = readFileSync(join(r.folder, 'summary.json'));
  const before = r.fake.posts.length; let attempts = 0;
  const result = await r.run({ '--retry': r.batch, '--timeout': '0.0001' }, [], {
    acquireBatchLock: async folder => { attempts++; assert.equal(folder, r.folder); throw Object.assign(new Error('busy'), { code: 'BATCH_LOCK_BUSY' }); }
  });
  assert.equal(attempts, 1); assert.equal(result.code, 2); assert.match(result.err, /another command|using batch/i); assert.match(result.err, new RegExp(`pdd check --read ${r.batch}`));
  assert.equal(r.fake.posts.length, before); assert.deepEqual(readFileSync(r.file), batch); assert.deepEqual(readFileSync(join(r.folder, 'summary.json')), summary);
});

test('2675: UUID receipt read bypasses batch ownership and leaves its projection unchanged', async t => {
  const r = await fixture(t), id = checks(r.fake)[0].request.requestId, bytes = readFileSync(r.file);
  let calls = 0;
  const result = await r.run({ '--read': true }, [id], { acquireBatchLock: async () => { calls++; throw new Error('must not lock UUID read'); } });
  assert.equal(calls, 0); passed(result); assert.deepEqual(readFileSync(r.file), bytes);
});


test('2675: a process killed after dispatch leaves its ID recoverable without another POST', async t => {
  const setup = harbor(t), posted = deferred(), resume = deferred(); let gate = false;
  const fake = await fakeRuntime(t, async (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.command === 'lint') return { status: 200, json: f.lint(id) };
    if (gate && e.command === 'check') { gate = false; posted.resolve(id); await resume.promise; }
    const answer = f.check(id); answer.usage.calls = 4;
    return { status: 200, json: answer };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
  const { ports } = portsFor(env);
  await client.runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, ports);
  const batch = JSON.parse(ports.stdout.text).batch, folder = join(setup.state, 'batches', batch), file = join(folder, 'batch.json'), saved = read(file);
  Object.assign(saved.rows[0], { phase: 'local', state: 'not_run', request_ids: [], eligible: true, can_retry: true, busy: true, retry_at: null }); writeFileSync(file, JSON.stringify(saved));
  gate = true; const before = checks(fake).length;
  const owner = worker({ setup, env }, { '--retry': batch }); t.after(() => { owner.child.kill('SIGKILL'); resume.resolve(); });
  const id = await posted.promise;
  assert.deepEqual(read(file).rows[0].request_ids, [id], 'ID is durable before dispatch');
  owner.child.kill('SIGKILL'); await owner.done; resume.resolve();
  const recovered = worker({ setup, env }, { '--retry': batch }); t.after(() => recovered.child.kill());
  const result = await recovered.done; passed(result);
  assert.equal(checks(fake).length - before, 1, 'dead owner recovery reads its submitted ID');
  assert.deepEqual(read(file).rows[0].request_ids, [id]);
  assert.ok(fake.gets.some(e => e.url.endsWith(id)));
  assert.equal(existsSync(join(folder, 'batch.lock')), false);
});

test('2675: native live-owner refusal leaves persisted data and the live owner intact', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const r = await fixture(t), bytes = readFileSync(r.file), summary = readFileSync(join(r.folder, 'summary.json')), before = r.fake.posts.length;
  const release = await client.acquireRuntimeBatchLock(r.folder); t.after(release);
  const result = await r.run({ '--retry': r.batch, '--timeout': '0.0001' });
  assert.equal(result.code, 2); assert.match(result.err, /pdd check --read/);
  assert.equal(read(join(r.folder, 'batch.lock')).pid, process.pid);
  assert.deepEqual(readFileSync(r.file), bytes); assert.deepEqual(readFileSync(join(r.folder, 'summary.json')), summary); assert.equal(r.fake.posts.length, before);
  release();
});


test('2675: an abandoned recovery guard is recoverable and a live recovery guard is respected', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const child = spawn(process.execPath, ['-e', '']); const dead = child.pid; await new Promise(done => child.on('close', done));
  for (const live of [true, false]) {
    const folder = temp(t), lock = join(folder, 'batch.lock'), guard = `${lock}.recover.${dead}`;
    const metadata = pid => JSON.stringify({ pid, host: hostname(), started_at: '2026-10-01T00:00:00.000Z' });
    writeFileSync(lock, metadata(dead)); writeFileSync(guard, metadata(live ? process.pid : dead));
    if (live) { await assert.rejects(client.acquireRuntimeBatchLock(folder), error => error.code === 'BATCH_LOCK_BUSY'); assert.equal(read(lock).pid, dead); assert.equal(read(guard).pid, process.pid); }
    else { let warnings = 0; const release = await client.acquireRuntimeBatchLock(folder, { onWarning: () => { warnings++; } }); assert.equal(warnings, 1); assert.equal(existsSync(guard), false); release(); assert.equal(existsSync(lock), false); }
  }
});

test('2675: a warning sink failure releases recovered ownership before propagating', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const folder = temp(t), child = spawn(process.execPath, ['-e', '']), dead = child.pid; await new Promise(done => child.on('close', done));
  writeFileSync(join(folder, 'batch.lock'), JSON.stringify({ pid: dead, host: hostname(), started_at: '2026-10-01T00:00:00.000Z' }));
  await assert.rejects(client.acquireRuntimeBatchLock(folder, { onWarning: () => { throw new Error('sink failed'); } }), /sink failed/);
  assert.equal(existsSync(join(folder, 'batch.lock')), false);
});


test('2675: real batch ownership is removed after an exception and Ctrl-C', async t => {
  const r = await fixture(t);
  await assert.rejects(r.run({ '--retry': r.batch }, [], { gh: () => { throw new Error('auth probe failed'); } }), /auth probe failed/);
  assert.equal(existsSync(join(r.folder, 'batch.lock')), false, 'auth failure releases the native lock');
  let stop; const gate = r.holdCheck(), before = checks(r.fake).length;
  const running = r.run({ '--retry': r.batch }, [], { onInterrupt: handler => { stop = handler; return () => {}; } });
  await gate.entered.promise; stop(); gate.resume.resolve();
  const result = await running; assert.equal(result.code, 3);
  assert.equal(existsSync(join(r.folder, 'batch.lock')), false, 'Ctrl-C releases the native lock');
  assert.equal(checks(r.fake).length - before, 1); assert.equal(read(r.file).rows[0].request_ids.length, 1);
  passed(await r.run({ '--read': true }, [r.batch]));
  assert.equal(checks(r.fake).length - before, 1);
});
