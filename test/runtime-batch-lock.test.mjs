import nodeTest from 'node:test';
const test = (name, body) => nodeTest(name, { timeout: 15_000 }, body);
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import fs, { existsSync, readFileSync, writeFileSync, mkdirSync, statSync, renameSync, readdirSync } from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { join } from 'node:path';
import { hostname } from 'node:os';
import * as client from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor, temp } from './runtime-fake.mjs';

const read = file => JSON.parse(readFileSync(file, 'utf8'));
const deferred = () => { let resolve; const promise = new Promise(done => { resolve = done; }); return { promise, resolve }; };
async function bounded(promise, label = 'gate', ms = 5000) {
  let timer;
  try { return await Promise.race([promise, new Promise((_, reject) => { timer = setTimeout(() => reject(new Error(`Timed out waiting for ${label}`)), ms); })]); }
  finally { clearTimeout(timer); }
}
const pause = ms => new Promise(done => setTimeout(done, ms));
const checks = fake => fake.posts.filter(p => p.command === 'check');
async function fixture(t) {
  const setup = harbor(t); let delay = false, held = null;
  const fake = await fakeRuntime(t, async (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (held && e.command === held.command) { const current = held; held = null; current.entered.resolve(); await bounded(current.resume.promise, 'held check release'); }
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
  const holdCommand = command => { const current = { command, entered: deferred(), resume: deferred() }; held = current; t.after(() => current.resume.resolve()); return current; };
  return { setup, env, fake, run, batch, folder, file, holdCommand, holdCheck: () => holdCommand('check') };
}
function passed(r) {
  assert.equal(r.code, 0, r.err + r.out);
  assert.equal(r.json.rows[0].state, 'passed');
  assert.equal(r.json.rows[0].calls, 4);
}

test('2675: two same-process retries send one check and keep its receipt and accounting', async t => {
  const r = await fixture(t), before = checks(r.fake).length;
  const gate = r.holdCheck(), first = r.run({ '--retry': r.batch }); await bounded(gate.entered.promise, 'owner POST');
  const second = await r.run({ '--retry': r.batch }); gate.resume.resolve();
  const results = [await bounded(first, 'first retry'), second];
  assert.equal(results[0].clock.uuids, 1); assert.equal(second.clock.uuids, 0, 'live competitor allocates no request ID');
  assert.equal(checks(r.fake).length - before, 1, 'only one held check may be sent');
  assert.equal(results.filter(r => r.code === 0).length, 1);
  passed(results.find(r => r.code === 0));
  const busy = results.find(r => r.code !== 0); assert.equal(busy.code, 3); assert.match(busy.err, /pdd check --read/);
  const ids = read(r.file).rows[0].request_ids;
  assert.deepEqual(ids, [checks(r.fake).at(-1).request.requestId]);
  assert.equal(read(join(r.folder, `${ids[0]}.json`)).usage.calls, 4);
  const later = await r.run({ '--read': true }, [r.batch]); passed(later);
  assert.deepEqual(read(r.file).rows[0].request_ids, ids);
});

function worker(t, r, options, words = []) {
  const source = `import {runCheck} from ${JSON.stringify(new URL('../src/runtime-client.mjs', import.meta.url).href)};
    import {portsFor} from ${JSON.stringify(new URL('./runtime-fake.mjs', import.meta.url).href)};
    const {ports}=portsFor(${JSON.stringify(r.env)}); console.error('START');
    const code=await runCheck(${JSON.stringify({ cwd: r.setup.repo, words, options: { '--json': true, ...options } })},ports); process.stdout.write(ports.stdout.text); process.stderr.write(ports.stderr.text); process.exitCode=code;`;
  const child = spawn(process.execPath, ['--input-type=module', '-e', source], { stdio: ['ignore', 'pipe', 'pipe'] });
  t.after(() => child.kill('SIGKILL'));
  let out = '', err = ''; const started = deferred();
  child.stdout.on('data', chunk => { out += chunk; });
  child.stderr.on('data', chunk => { err += chunk; if (err.includes('START')) started.resolve(); });
  const done = new Promise((resolve, reject) => { child.on('error', reject); child.on('close', code => resolve({ code, out, err, json: out ? JSON.parse(out) : null })); });
  return { child, started: started.promise, done };
}

test('2675: separate processes admit one retry and refuse the live competitor', async t => {
  const r = await fixture(t), before = checks(r.fake).length;
  const gate = r.holdCheck(), a = worker(t, r, { '--retry': r.batch }); await bounded(gate.entered.promise, 'owner POST');
  const b = worker(t, r, { '--retry': r.batch });
  t.after(() => { a.child.kill(); b.child.kill(); gate.resume.resolve(); });
  await bounded(Promise.all([a.started, b.started]), 'workers ready');
  const second = await bounded(b.done, 'competing worker exit'); gate.resume.resolve();
  const results = [await bounded(a.done, 'first worker exit'), second];
  assert.equal(checks(r.fake).length - before, 1, 'an in-memory lock is insufficient');
  assert.equal(results.filter(r => r.code === 0).length, 1);
  passed(results.find(r => r.code === 0));
  const busy = results.find(r => r.code !== 0); assert.equal(busy.code, 3); assert.match(busy.err, /pdd check --read/);
  assert.deepEqual(read(r.file).rows[0].request_ids, [results.find(r => r.code === 0).json.rows[0].request_id]);
});

test('2675: a batch read holds ownership across its refresh and cannot overwrite a retry', async t => {
  const setup = harbor(t); const entered = deferred(), resume = deferred(); t.after(() => resume.resolve()); let gate = false;
  const fake = await fakeRuntime(t, async (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.command === 'lint') return { status: 200, json: f.lint(id) };
    if (gate && e.method === 'GET') { gate = false; entered.resolve(); await bounded(resume.promise, 'read release'); }
    return { status: 200, json: f.check(id) };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
  async function run(options = {}, words = []) { const { ports } = portsFor(env); const code = await client.runCheck({ cwd: setup.repo, words, options: { '--json': true, ...options } }, ports); return { code, out: ports.stdout.text, err: ports.stderr.text }; }
  const first = JSON.parse((await run()).out), folder = join(setup.state, 'batches', first.batch), file = join(folder, 'batch.json');
  const saved = read(file), old = saved.rows[0].request_ids[0];
  writeFileSync(join(folder, `${old}.json`), JSON.stringify(fake.check(old, 'running')));
  Object.assign(saved.rows[1], { state: 'not_run', phase: 'local', request_ids: [], eligible: true, busy: true, can_retry: true, retry_at: null });
  writeFileSync(file, JSON.stringify(saved)); gate = true;
  const reading = run({ '--read': true }, [first.batch]); await bounded(entered.promise, 'read entry');
  const before = checks(fake).length, retrying = run({ '--retry': first.batch });
  await pause(80);
  const postsWhileReadOwns = checks(fake).length - before;
  resume.resolve(); await bounded(Promise.all([reading, retrying]), 'read and retry');
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
  const folder = temp(t), lock = join(folder, 'batch.lock');
  let deadPid;
  if (kind === 'dead' || kind === 'foreign') { const child = spawn(process.execPath, ['-e', '']); deadPid = child.pid; await bounded(new Promise(done => child.on('close', done)), 'child exit'); }
  writeFileSync(lock, kind === 'malformed' ? 'not a pid' : JSON.stringify({ pid: kind === 'dead' || kind === 'foreign' ? deadPid : process.pid, host: kind === 'foreign' ? 'another-host' : hostname(), started_at: '2026-10-01T00:00:00.000Z' }));
  if (kind === 'dead') {
    const warnings = []; const release = await client.acquireRuntimeBatchLock(folder, { onWarning: line => warnings.push(line) });
    assert.equal(warnings.length, 1); assert.match(warnings[0], /recover|dead|abandon/i);
    assert.equal(read(lock).pid, process.pid); assert.equal(read(lock).host, hostname()); assert.ok(Date.parse(read(lock).started_at)); assert.equal(statSync(lock).mode & 0o777, 0o600);
    release(); release(); assert.equal(existsSync(lock), false);
  } else {
    const bytes = readFileSync(lock);
    await assert.rejects(client.acquireRuntimeBatchLock(folder, {}), error => error.code === (kind === 'live' ? 'BATCH_LOCK_BUSY' : 'BATCH_LOCK_INVALID'));
    assert.deepEqual(readFileSync(lock), bytes);
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
  const result = await r.run({ '--retry': r.batch }, [], {
    acquireBatchLock: async folder => { attempts++; assert.equal(folder, r.folder); throw Object.assign(new Error('busy'), { code: 'BATCH_LOCK_BUSY' }); }
  });
  assert.equal(attempts, 1); assert.equal(result.code, 3); assert.match(result.err, /another command|using batch/i); assert.match(result.err, new RegExp(`pdd check --read ${r.batch}`));
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
    if (gate && e.command === 'check') { gate = false; posted.resolve(id); await bounded(resume.promise, 'read release'); }
    const answer = f.check(id); answer.usage.calls = 4;
    return { status: 200, json: answer };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
  const { ports } = portsFor(env);
  await client.runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, ports);
  const batch = JSON.parse(ports.stdout.text).batch, folder = join(setup.state, 'batches', batch), file = join(folder, 'batch.json'), saved = read(file);
  Object.assign(saved.rows[0], { phase: 'local', state: 'not_run', request_ids: [], eligible: true, can_retry: true, busy: true, retry_at: null }); writeFileSync(file, JSON.stringify(saved));
  gate = true; const before = checks(fake).length;
  const owner = worker(t, { setup, env }, { '--retry': batch }); t.after(() => { owner.child.kill('SIGKILL'); resume.resolve(); });
  const id = await bounded(posted.promise, 'dispatch');
  assert.deepEqual(read(file).rows[0].request_ids, [id], 'ID is durable before dispatch');
  owner.child.kill('SIGKILL'); await bounded(owner.done, 'killed worker exit'); resume.resolve();
  const recovered = worker(t, { setup, env }, { '--retry': batch }); t.after(() => recovered.child.kill());
  const result = await bounded(recovered.done, 'recovery worker exit'); passed(result);
  assert.equal(checks(fake).length - before, 1, 'dead owner recovery reads its submitted ID');
  assert.deepEqual(read(file).rows[0].request_ids, [id]);
  assert.ok(fake.gets.some(e => e.url.endsWith(id)));
  assert.equal(existsSync(join(folder, 'batch.lock')), false);
});

test('2675: native live-owner refusal leaves persisted data and the live owner intact', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const r = await fixture(t), bytes = readFileSync(r.file), summary = readFileSync(join(r.folder, 'summary.json')), before = r.fake.posts.length;
  const release = await client.acquireRuntimeBatchLock(r.folder); t.after(release);
  const result = await r.run({ '--retry': r.batch });
  assert.equal(result.code, 3); assert.match(result.err, /pdd check --read/);
  const metadata = read(join(r.folder, 'batch.lock'));
  assert.equal(metadata.pid, process.pid); assert.ok(result.err.includes(String(metadata.pid))); assert.ok(result.err.includes(metadata.started_at));
  assert.deepEqual(readFileSync(r.file), bytes); assert.deepEqual(readFileSync(join(r.folder, 'summary.json')), summary); assert.equal(r.fake.posts.length, before);
  release();
});


test('2675: an abandoned recovery guard is recoverable and a live recovery guard is respected', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const child = spawn(process.execPath, ['-e', '']); const dead = child.pid; await bounded(new Promise(done => child.on('close', done)), 'child exit');
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
  const folder = temp(t), child = spawn(process.execPath, ['-e', '']), dead = child.pid; await bounded(new Promise(done => child.on('close', done)), 'child exit');
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
  await bounded(gate.entered.promise, 'owner POST'); stop(); gate.resume.resolve();
  const result = await bounded(running, 'interrupted retry'); assert.equal(result.code, 3);
  assert.equal(existsSync(join(r.folder, 'batch.lock')), false, 'Ctrl-C releases the native lock');
  assert.equal(checks(r.fake).length - before, 1); assert.equal(read(r.file).rows[0].request_ids.length, 1);
  passed(await r.run({ '--read': true }, [r.batch]));
  assert.equal(checks(r.fake).length - before, 1);
});


test('2675: releasing a replaced lock never removes the replacement owner', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const folder = temp(t), lock = join(folder, 'batch.lock'), held = join(folder, 'original-owner');
  const release = await client.acquireRuntimeBatchLock(folder);
  renameSync(lock, held);
  const replacement = JSON.stringify({ pid: process.pid, host: hostname(), started_at: '2026-10-02T00:00:00.000Z' });
  writeFileSync(lock, replacement); release(); release();
  assert.equal(readFileSync(lock, 'utf8'), replacement);
});

function mockFs(t, name, wrap) {
  const original = fs[name];
  t.mock.method(fs, name, wrap(original)); syncBuiltinESMExports();
  t.after(() => { t.mock.restoreAll(); syncBuiltinESMExports(); });
}
const metadata = pid => ({ pid, host: hostname(), started_at: '2026-10-01T00:00:00.000Z' });
async function deadProcess(t) {
  const child = spawn(process.execPath, ['-e', '']); t.after(() => child.kill('SIGKILL'));
  await bounded(new Promise((resolve, reject) => { child.on('error', reject); child.on('close', resolve); }), 'dead child');
  return child.pid;
}

test('2675 review: takeover rechecks record contents when the same inode names a new live owner', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const folder = temp(t), lock = join(folder, 'batch.lock'), dead = await deadProcess(t);
  writeFileSync(lock, JSON.stringify(metadata(dead))); const before = statSync(lock, { bigint: true });
  const replacement = metadata(process.pid), kill = process.kill; let changed = false;
  t.mock.method(process, 'kill', (pid, signal) => {
    if (pid === dead && !changed) { changed = true; writeFileSync(lock, JSON.stringify(replacement)); throw Object.assign(new Error('dead'), { code: 'ESRCH' }); }
    return kill(pid, signal);
  });
  await assert.rejects(client.acquireRuntimeBatchLock(folder), error => error.code === 'BATCH_LOCK_BUSY');
  assert.equal(changed, true); assert.equal(statSync(lock, { bigint: true }).ino, before.ino);
  assert.deepEqual(read(lock), replacement, 'a new record must survive even when its file identity matches');
});

test('2675 review: release preserves a changed record on the original inode', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const folder = temp(t), lock = join(folder, 'batch.lock'), release = await client.acquireRuntimeBatchLock(folder);
  const replacement = { ...read(lock), started_at: '2026-10-02T00:00:00.000Z' };
  writeFileSync(lock, JSON.stringify(replacement)); release();
  assert.deepEqual(read(lock), replacement);
});

test('2675 review: release preserves identical contents on a replacement inode', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const folder = temp(t), lock = join(folder, 'batch.lock'), release = await client.acquireRuntimeBatchLock(folder);
  const bytes = readFileSync(lock); renameSync(lock, join(folder, 'original')); writeFileSync(lock, bytes); release();
  assert.deepEqual(readFileSync(lock), bytes);
});

test('2675 review: only a complete fsynced record is published by an exclusive hard link', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const folder = temp(t), lock = join(folder, 'batch.lock'); let links = 0, synced = false;
  mockFs(t, 'fsyncSync', original => fd => { synced = true; return original(fd); });
  mockFs(t, 'linkSync', original => (source, target) => {
    assert.equal(target, lock); assert.notEqual(source, target); assert.equal(existsSync(target), false); assert.equal(synced, true);
    const record = read(source); assert.equal(record.pid, process.pid); assert.equal(record.host, hostname()); assert.ok(Date.parse(record.started_at));
    assert.equal(statSync(source).mode & 0o777, 0o600); links++;
    return original(source, target);
  });
  const release = await client.acquireRuntimeBatchLock(folder); assert.equal(links, 1); assert.deepEqual(readdirSync(folder), ['batch.lock']);
  release(); assert.deepEqual(readdirSync(folder), []);
});

test('2675 review: failed publication removes its temporary record and exposes no empty lock', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const folder = temp(t), lock = join(folder, 'batch.lock');
  mockFs(t, 'linkSync', () => (source, target) => {
    assert.equal(target, lock); assert.ok(read(source).pid); assert.equal(existsSync(lock), false);
    throw Object.assign(new Error('disk full'), { code: 'ENOSPC' });
  });
  await assert.rejects(client.acquireRuntimeBatchLock(folder), error => error.code === 'ENOSPC');
  assert.deepEqual(readdirSync(folder), []);
});

test('2675 review: EPERM means the owner remains alive', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const folder = temp(t), lock = join(folder, 'batch.lock'); writeFileSync(lock, JSON.stringify(metadata(1)));
  let nativeStatus = 'alive'; try { process.kill(1, 0); } catch (error) { nativeStatus = error.code; }
  t.diagnostic(`native kill(1, 0): ${nativeStatus}; uid=${process.getuid?.()}`);
  assert.ok(['alive', 'EPERM'].includes(nativeStatus));
  await assert.rejects(client.acquireRuntimeBatchLock(folder), error => error.code === 'BATCH_LOCK_BUSY');
  // The deterministic port-level error also covers privileged CI runners.
  const kill = process.kill; t.mock.method(process, 'kill', (pid, signal) => {
    if (pid === 1) throw Object.assign(new Error('permission denied'), { code: 'EPERM' });
    return kill(pid, signal);
  });
  await assert.rejects(client.acquireRuntimeBatchLock(folder), error => error.code === 'BATCH_LOCK_BUSY'); assert.equal(read(lock).pid, 1);
});

test('2675 review: unverifiable locks give conditional file recovery advice without effects', async t => {
  const r = await fixture(t), lock = join(r.folder, 'batch.lock');
  for (const kind of ['empty', 'directory', 'foreign', 'invalid-pid']) {
    fs.rmSync(lock, { recursive: true, force: true });
    if (kind === 'directory') mkdirSync(lock);
    else writeFileSync(lock, kind === 'empty' ? '' : JSON.stringify({ ...metadata(kind === 'invalid-pid' ? 9007199254740991 : process.pid), host: kind === 'foreign' ? 'old-host' : hostname() }));
    const before = readFileSync(r.file), summary = readFileSync(join(r.folder, 'summary.json')), posts = r.fake.posts.length, gets = r.fake.gets.length;
    const result = await r.run({ '--retry': r.batch });
    assert.equal(result.code, 2); assert.ok(result.err.includes(lock)); assert.match(result.err, /delete.*only if no pdd command is running.*host/i); assert.match(result.err, /run.*command again/i);
    assert.equal(r.fake.posts.length, posts); assert.equal(r.fake.gets.length, gets); assert.deepEqual(readFileSync(r.file), before); assert.deepEqual(readFileSync(join(r.folder, 'summary.json')), summary);
  }
});

test('2675 review: ownership lasts through final batch and summary publication', async t => {
  const r = await fixture(t); let atRelease, releases = 0;
  const result = await r.run({ '--retry': r.batch }, [], { acquireBatchLock: async () => () => {
    releases++; atRelease = { batch: readFileSync(r.file), summary: readFileSync(join(r.folder, 'summary.json')) };
  } });
  passed(result); assert.equal(releases, 1); assert.deepEqual(atRelease.batch, readFileSync(r.file)); assert.deepEqual(atRelease.summary, readFileSync(join(r.folder, 'summary.json')));
  const summary = JSON.parse(atRelease.summary); assert.equal(summary.rows[0].request_id, result.json.rows[0].request_id); assert.equal(summary.rows[0].calls, 4);
});

test('2675 review: missing batches retain their file-problem line and never acquire ownership', async t => {
  const r = await fixture(t), missing = '20260101-000000-zzzz'; let acquisitions = 0;
  for (const options of [{ '--read': true }, { '--retry': missing }]) {
    const result = await r.run(options, options['--read'] ? [missing] : [], { acquireBatchLock: async () => { acquisitions++; throw new Error('unexpected lock'); } });
    assert.equal(result.code, 2); assert.ok(result.err.includes(`No saved batch ${missing}.`)); assert.equal(result.clock.gh.length, 0);
  }
  assert.equal(acquisitions, 0); assert.equal(existsSync(join(r.setup.state, 'batches', missing)), false);
});

test('2675 review: generic acquisition errors use the documented line', async t => {
  const r = await fixture(t);
  const result = await r.run({ '--retry': r.batch }, [], { acquireBatchLock: async () => { throw Object.assign(new Error('readonly'), { code: 'EROFS' }); } });
  assert.equal(result.code, 2); assert.ok(result.err.includes(`Could not lock batch ${r.batch} (EROFS). Nothing was sent.`));
});

test('2675 review: cleanup failure warns without replacing success or the original error', async t => {
  const r = await fixture(t), extra = { acquireBatchLock: async () => () => { throw Object.assign(new Error('cleanup failure'), { code: 'EACCES' }); } };
  const result = await r.run({ '--retry': r.batch }, [], extra); passed(result); assert.match(result.err, /warning.*release.*EACCES/i);
  const original = new Error('original auth failure');
  await assert.rejects(r.run({ '--retry': r.batch }, [], { ...extra, gh: () => { throw original; } }), error => error === original);
});

test('2675 review: native release errors warn and do not escape', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  const folder = temp(t), lock = join(folder, 'batch.lock'), warnings = [];
  const release = await client.acquireRuntimeBatchLock(folder, { onWarning: text => warnings.push(text) });
  mockFs(t, 'unlinkSync', original => path => { if (path === lock) throw Object.assign(new Error('readonly'), { code: 'EROFS' }); return original(path); });
  assert.doesNotThrow(release); assert.equal(warnings.length, 1); assert.match(warnings[0], /release.*EROFS/i); assert.ok(warnings[0].includes(lock));
});

async function createRace(t, folder, count = 5) {
  const url = new URL('../src/runtime-client.mjs', import.meta.url).href;
  const source = `import {acquireRuntimeBatchLock} from ${JSON.stringify(url)};
    process.send({ready:true}); process.once('message', async () => {
      let release; try { release=await acquireRuntimeBatchLock(${JSON.stringify(folder)}); process.send({won:true}); }
      catch(error) { process.send({won:false,code:error.code}); }
      process.once('message', () => { release?.(); process.disconnect(); });
    });`;
  const children = Array.from({ length: count }, () => {
    const child = spawn(process.execPath, ['--input-type=module', '-e', source], { stdio: ['ignore', 'pipe', 'pipe', 'ipc'] });
    t.after(() => child.kill('SIGKILL'));
    const ready = deferred(), answer = deferred(); let stderr = '';
    child.stderr.on('data', value => { stderr += value; });
    child.on('message', message => { if (message.ready) ready.resolve(); else answer.resolve(message); });
    const done = new Promise((resolve, reject) => { child.on('error', reject); child.on('close', code => code === 0 ? resolve() : reject(new Error(`race worker ${code}: ${stderr}`))); });
    return { child, ready: ready.promise, answer: answer.promise, done };
  });
  await bounded(Promise.all(children.map(c => c.ready)), 'race workers ready'); children.forEach(c => c.child.send('go'));
  const results = await bounded(Promise.all(children.map(c => c.answer)), 'race results');
  children.forEach(c => c.child.send('finish')); await bounded(Promise.all(children.map(c => c.done)), 'race workers done');
  return results;
}

test('2675 review: bounded multi-process publication and dead-owner takeover each have one winner', async t => {
  assert.equal(typeof client.acquireRuntimeBatchLock, 'function');
  for (const stale of [false, true]) {
    const folder = temp(t); if (stale) writeFileSync(join(folder, 'batch.lock'), JSON.stringify(metadata(await deadProcess(t))));
    const results = await createRace(t, folder); assert.equal(results.filter(r => r.won).length, 1, JSON.stringify(results));
    assert.ok(results.filter(r => !r.won).every(r => r.code === 'BATCH_LOCK_BUSY')); assert.deepEqual(readdirSync(folder), []);
  }
});

for (const mode of ['check', 'lint']) test(`2675 review: a new ${mode} owns its batch through the whole run`, async t => {
  const r = await fixture(t), gate = r.holdCommand(mode), options = mode === 'lint' ? { '--lint': true } : {};
  const running = r.run(options, ['place-order']); let before, observed, result, owner, batch, finished;
  try {
    await bounded(gate.entered.promise, `${mode} dispatch`);
    const id = r.fake.posts.at(-1).request.requestId;
    batch = readdirSync(join(r.setup.state, 'batches')).find(name => {
      const saved = read(join(r.setup.state, 'batches', name, 'batch.json'));
      return saved.lint.request_ids.includes(id) || saved.rows.some(row => row.request_ids.includes(id));
    });
    assert.ok(batch); const file = join(r.setup.state, 'batches', batch, 'batch.json');
    before = { bytes: readFileSync(file), gets: r.fake.gets.length, posts: r.fake.posts.length };
    result = await r.run({ '--read': true }, [batch]);
    observed = { bytes: readFileSync(file), gets: r.fake.gets.length, posts: r.fake.posts.length };
    owner = read(join(r.setup.state, 'batches', batch, 'batch.lock'));
  } finally { gate.resume.resolve(); finished = await bounded(running, `${mode} completion`); }
  assert.equal(result.code, 3); assert.deepEqual(observed, before);
  assert.ok(result.err.includes(String(owner.pid))); assert.ok(result.err.includes(owner.started_at));
  assert.equal(finished.code, 0); assert.equal(existsSync(join(r.setup.state, 'batches', batch, 'batch.lock')), false);
});
