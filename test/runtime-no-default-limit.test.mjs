import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, mkdirSync, readFileSync, writeFileSync, statSync, rmSync } from 'node:fs';
import { spawn } from 'node:child_process';
import { join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { acquireRuntimeSlot, recordRuntimeRequest, releaseRuntimeSlot, listRuntimeJobs } from '../src/runtime-slots.mjs';
import { fakeRuntime, harbor, portsFor, root } from './runtime-fake.mjs';

const pause = ms => new Promise(done => setTimeout(done, ms));
async function waitFor(predicate) {
  const end = Date.now() + 10000;
  while (!await predicate() && Date.now() < end) await pause(10);
  return !!await predicate();
}
function selected(t, count) {
  return harbor(t, repo => {
    const source = readFileSync(join(repo, 'tests/place-order.json'));
    rmSync(join(repo, 'tests/unknown-item.json'));
    for (let i = 1; i < count; i++) writeFileSync(join(repo, `tests/place-order-${i}.json`), source);
  });
}
const make = (setup, fake, extra = {}) => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, extra);
const check = (setup, ports, options = {}) => runCheck({ cwd: setup.repo, words: [], options: { '--json': true, ...options } }, ports);
const checks = fake => fake.posts.filter(row => row.command === 'check');
function seed(setup, origin, now) {
  const directory = join(setup.state, 'slots', encodeURIComponent(new URL(origin).host));
  mkdirSync(directory, { recursive: true });
  const rows = Array.from({ length: 4 }, (_, i) => ({ id: `foreign-${i}`, state: 'active', pid: process.pid, kind: 'check', started_at: now, request_ids: [`uncertain-${i}`] }));
  rows.push({ id: 'older-waiter', state: 'waiting', pid: process.pid, kind: 'lint', started_at: now - 1, request_ids: [] });
  for (const row of rows) writeFileSync(join(directory, `${row.id}.json`), JSON.stringify(row));
  return { directory, rows };
}

for (const raw of [undefined, '0']) test(`2704: seven selected checks dispatch before completion (${raw ?? 'unset'})`, async t => {
  const setup = selected(t, 7); let release;
  const barrier = new Promise(done => { release = done; });
  const fake = await fakeRuntime(t, async (entry, f) => {
    if (entry.command === 'check') return { status: 202, json: f.check(entry.request.requestId, 'queued') };
    if (entry.method === 'GET') { await barrier; return { status: 200, json: f.check(entry.url.split('/').at(-1)) }; }
    return f.normal(entry);
  });
  const made = make(setup, fake, { now: Date.now, sleep: pause, pollMs: 10 });
  if (raw !== undefined) made.ports.env.PDD_MAX_JOBS = raw;
  const running = check(setup, made.ports);
  let sent, snapshot;
  try {
    sent = await waitFor(() => checks(fake).length === 7);
    snapshot = (await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs;
  } finally { release(); await running; }
  assert.equal(sent, true, 'all seven POSTs must precede any terminal reply');
  assert.equal(snapshot.filter(row => row.state === 'active').length, 7);
  assert.deepEqual(snapshot.flatMap(row => row.request_ids).sort(), checks(fake).map(row => row.request.requestId).sort());
  assert.equal(new Set(checks(fake).map(row => row.request.scenario)).size, 7);
  assert.doesNotMatch(made.ports.stderr.text, /Waiting for a local slot/);
  assert.equal(made.ports.stderr.text.split('\n').filter(line => /Warning:.*PDD_MAX_JOBS/.test(line)).length, raw === undefined ? 0 : 1);
  assert.equal(JSON.parse(made.ports.stdout.text).exit_code, 0);
});

for (const raw of ['', '-1', '1.5', 'garbage', ' 2', '02', '9007199254740992']) test(`2704: invalid ${JSON.stringify(raw)} warns once and means no cap`, async t => {
  const setup = selected(t, 1), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const made = make(setup, fake); made.ports.env.PDD_MAX_JOBS = raw;
  assert.equal(await check(setup, made.ports), 0);
  const warnings = made.ports.stderr.text.split('\n').filter(line => /Warning:.*PDD_MAX_JOBS/.test(line));
  assert.equal(warnings.length, 1); assert.match(warnings[0], /no (?:local )?(?:cap|limit)/i);
});

for (const kind of ['lint', 'try']) test(`2704: ${kind} has no local wait behind active leases and FIFO tickets`, async t => {
  const setup = selected(t, 1); let made, seeded;
  const fake = await fakeRuntime(t, async (entry, f) => {
    if (entry.command) {
      const jobs = (await listRuntimeJobs({ stateDir: setup.state, origin: f.origin })).jobs;
      assert.ok(jobs.some(row => row.request_ids.includes(entry.request.requestId)), 'durably register before POST');
    }
    if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    return f.normal(entry);
  });
  made = make(setup, fake); seeded = seed(setup, fake.origin, made.clock.now);
  const code = kind === 'lint' ? await check(setup, made.ports, { '--lint': true })
    : await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, made.ports);
  assert.equal(code, 0, made.ports.stderr.text);
  assert.equal(fake.posts.filter(entry => entry.command === kind).length, 1);
  assert.doesNotMatch(made.ports.stderr.text, /Waiting for a local slot/);
  assert.deepEqual((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.sort((a,b) => a.id.localeCompare(b.id)), seeded.rows.sort((a,b) => a.id.localeCompare(b.id)));
});

for (const limit of [undefined, Infinity]) test(`2704: ${String(limit)} slot limit preserves records without FIFO or occupancy wait`, async t => {
  const setup = selected(t, 1), origin = 'http://localhost:453';
  const seeded = seed(setup, origin, Date.now()); let sleeps = 0, probes = 0; const lines = [];
  const reservation = await acquireRuntimeSlot({ stateDir: setup.state, origin, kind: 'check', ...(limit === undefined ? {} : { limit }), deadline: Date.now() + 100 }, {
    say: line => lines.push(line), sleep: async () => { sleeps++; await pause(10); }, readRun: async () => { probes++; return 'unknown'; },
  });
  try {
    assert.ok(reservation, 'no-cap admission bypasses older waiting tickets');
    assert.equal(sleeps, 0); assert.equal(probes, 0); assert.deepEqual(lines, []);
    assert.equal(statSync(join(reservation.directory, `${reservation.id}.json`)).mode & 0o777, 0o600);
    await recordRuntimeRequest(reservation, 'a'); await recordRuntimeRequest(reservation, 'a'); await recordRuntimeRequest(reservation, 'b');
    await releaseRuntimeSlot(reservation, { ended: false });
    assert.deepEqual((await listRuntimeJobs({ stateDir: setup.state, origin })).jobs.find(row => row.id === reservation.id).request_ids, ['a', 'b']);
  } finally { if (reservation) await releaseRuntimeSlot(reservation, { ended: true }); }
  assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin })).jobs.length, seeded.rows.length);
});

// The first accepted check stays open while a peer reports busy. Window=1 must
// hold the retry and the third scenario until that accepted check has ended.
test('2704: busy keeps Retry-After, window one, new ID and accepted-check identity', async t => {
  const setup = selected(t, 3); let made, busyAt, acceptedId, polls = 0;
  const attempts = new Map(), times = [];
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'check') {
      const scenario = entry.request.scenario, count = (attempts.get(scenario) ?? 0) + 1;
      attempts.set(scenario, count); times.push(made.clock.now);
      if (checks(f).length === 1) { acceptedId = entry.request.requestId; return { status: 202, json: f.check(acceptedId, 'queued') }; }
      if (checks(f).length === 2) { busyAt = made.clock.now; return { status: 429, headers: { 'retry-after': '7' }, json: { dispatch: 'not_started', error: { code: 'server-full', details: { retryable: true } } } }; }
      assert.ok(polls >= 3, 'busy window one holds all later sends behind the accepted check');
      assert.ok(made.clock.now - busyAt >= 10000, 'minimum wait and Retry-After are retained');
      return { status: 200, json: f.check(entry.request.requestId) };
    }
    if (entry.method === 'GET' && entry.url.endsWith(acceptedId)) return { status: 200, json: f.check(acceptedId, ++polls < 3 ? 'running' : 'passed') };
    return f.normal(entry);
  });
  made = make(setup, fake); made.ports.env.PDD_MAX_JOBS = '2'; made.ports.pollMs = 10000;
  assert.equal(await check(setup, made.ports), 0, made.ports.stderr.text);
  assert.deepEqual([...attempts.values()].sort(), [1, 1, 2]);
  const posts = checks(fake); assert.equal(new Set(posts.map(entry => entry.request.requestId)).size, 4);
  const batch = JSON.parse(made.ports.stdout.text).batch;
  const saved = JSON.parse(readFileSync(join(setup.state, 'batches', batch, 'batch.json')));
  assert.equal(saved.rows.flatMap(row => row.request_ids).length, 4);
  assert.ok(readFileSync(join(setup.state, 'batches', batch, `${posts[1].request.requestId}.admission.json`)));
});

// Two real commands share one cap, rather than only sharing in-process ports.
test('2704: cap two is shared across two real CLI processes', { timeout: 40000 }, async t => {
  const setup = selected(t, 3), second = selected(t, 3); let active = 0, peak = 0, release;
  const completed = new Set(), kinds = new Map(), barrier = new Promise(done => { release = done; });
  const fake = await fakeRuntime(t, async (entry, f) => {
    if (entry.command === 'lint') return f.normal(entry);
    if (entry.command === 'check') { active++; peak = Math.max(peak, active); kinds.set(entry.request.requestId, entry.command); return { status: 202, json: f.check(entry.request.requestId, 'queued') }; }
    const id = entry.url.split('/').at(-1); await barrier;
    if (!completed.has(id)) { completed.add(id); active--; }
    return { status: 200, json: f.check(id) };
  });
  const gh = join(setup.sandbox, 'gh'); writeFileSync(gh, '#!/bin/sh\nif [ "$1" = auth ]; then echo fixture-token; else echo "octo 4242"; fi\n'); chmodSync(gh, 0o700);
  const children = [], pending = [setup, second].map(current => new Promise((done, fail) => {
    const child = spawn(process.execPath, [join(root, 'bin/pdd.mjs'), 'check', '--json'], { cwd: current.repo, env: { ...process.env, HOME: setup.home, PATH: `${setup.sandbox}:${process.env.PATH}`, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, PDD_MAX_JOBS: '2' }, stdio: ['ignore', 'pipe', 'pipe'] });
    children.push(child); let out = '', err = ''; child.stdout.on('data', b => out += b); child.stderr.on('data', b => err += b); child.on('error', fail); child.on('close', code => done({ code, out, err }));
  }));
  t.after(() => children.forEach(child => { if (child.exitCode === null) child.kill('SIGKILL'); }));
  let filled, queued, snapshot;
  try {
    filled = await waitFor(() => checks(fake).length >= 2);
    queued = await waitFor(async () => (await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.some(row => row.state === 'waiting'));
    snapshot = (await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs;
  } finally { release(); }
  const results = await Promise.all(pending);
  assert.equal(filled, true); assert.equal(queued, true); assert.equal(new Set(snapshot.map(row => row.pid)).size, 2); assert.equal(snapshot.filter(row => row.state === 'active').length, 2);
  assert.equal(peak, 2); assert.equal(checks(fake).length, 6); assert.equal(kinds.size, 6);
  for (const result of results) assert.equal(result.code, 0, result.out + result.err);
  assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.length, 0);
});
