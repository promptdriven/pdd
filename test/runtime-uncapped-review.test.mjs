import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { acquireRuntimeSlot, releaseRuntimeSlot, listRuntimeJobs } from '../src/runtime-slots.mjs';
import { fakeRuntime, harbor, portsFor, sha } from './runtime-fake.mjs';

function selected(t, count) {
  return harbor(t, repo => {
    const source = readFileSync(join(repo, 'tests/place-order.json'));
    rmSync(join(repo, 'tests/unknown-item.json'));
    for (let i = 1; i < count; i++) writeFileSync(join(repo, `tests/place-order-${i}.json`), source);
  });
}

// These are the actual filesystem/process/clock dependencies of public admission.
// No fake port supplies an admission or reclamation decision.
function localWorld() {
  const now = 2_000_000_000_000, directory = '/fixture/slots/localhost%3A453';
  const records = new Map(), times = new Map(); let claimHook = () => {};
  const add = (id, state, pid, age, request_ids, refreshAge = 0) => {
    const path = join(directory, `${id}.json`);
    records.set(path, { id, state, pid, kind: 'check', started_at: now - age, request_ids }); times.set(path, now - refreshAge);
  };
  const files = {
    listRecords: () => ({ jobs: [...records.values()].filter(r => r.state).map(r => structuredClone(r)) }),
    exclusiveCreate: (path, row) => {
      if (path.endsWith('/claim.json') && claimHook() === false) return false;
      if (records.has(path)) return false;
      records.set(path, structuredClone(row)); times.set(path, now); return true;
    },
    writeAtomic: (path, row) => { records.set(path, structuredClone(row)); times.set(path, now); },
    modifiedAt: path => times.get(path) ?? null, touch: path => records.has(path),
    unlink: path => { records.delete(path); times.delete(path); },
  };
  const ports = { files, now: () => now, pid: 7, isAlive: pid => pid !== 99, randomUUID: () => 'own',
    timers: { setInterval: () => 1, clearInterval: () => {} }, onInterrupt: () => () => {},
    sleep: () => assert.fail('uncapped admission must not wait or retry contention'),
    readRun: () => assert.fail('passive cleanup must not probe runtime jobs'),
    say: () => assert.fail('uncapped admission must not show a local wait') };
  return { now, directory, records, times, add, ports, claimHook: hook => { claimHook = hook; },
    options: { stateDir: '/fixture', origin: 'http://localhost:453', kind: 'check', limit: Infinity } };
}

test('2704 S1: uncapped admission passively reclaims only eligible expired owners', async () => {
  const w = localWorld();
  w.add('dead-waiter', 'waiting', 99, 1, []);
  w.add('stale-waiter', 'waiting', 8, 60_000, [], 60_000);
  w.add('dead-unsent', 'active', 99, 1, []);
  w.add('stale-unsent', 'active', 8, 60_000, [], 60_000);
  w.add('dead-aged', 'active', 99, 1_800_000, ['old-unknown']);
  w.add('stale-aged', 'active', 8, 1_800_000, ['old-running'], 60_000);
  w.add('live-aged', 'active', 8, 7_200_000, ['live-paid']);
  w.add('dead-recent', 'active', 99, 1_799_999, ['recent-unknown']);
  w.add('stale-recent', 'active', 8, 60_000, ['recent-running'], 60_000);
  w.add('live-waiter', 'waiting', 8, 1, []);
  const retained = ['dead-recent', 'live-aged', 'live-waiter', 'stale-recent'];
  const before = [...w.records.values()].filter(r => retained.includes(r.id));
  const reservation = await acquireRuntimeSlot(w.options, w.ports);
  assert.ok(reservation);
  await releaseRuntimeSlot(reservation, { ended: true }, w.ports);
  const { jobs } = await listRuntimeJobs(w.options, w.ports);
  assert.deepEqual(jobs.map(r => r.id).sort(), retained);
  assert.deepEqual(jobs.sort((a,b) => a.id.localeCompare(b.id)), before.sort((a,b) => a.id.localeCompare(b.id)), 'retain every uncertain ID and owner field');
});

for (const changed of ['snapshot', 'heartbeat']) test(`2704 S1: passive cleanup preserves a ${changed} changed before exclusion`, async () => {
  const w = localWorld(); let guarded = false;
  w.add('changed', 'active', changed === 'heartbeat' ? 8 : 99, 1_800_000, ['original'], 60_000);
  const path = join(w.directory, 'changed.json');
  w.claimHook(() => {
    if (guarded) return;
    guarded = true;
    if (changed === 'snapshot') w.records.get(path).request_ids.push('new-paid-request');
    else w.times.set(path, w.now);
  });
  const reservation = await acquireRuntimeSlot(w.options, w.ports);
  assert.ok(reservation);
  await releaseRuntimeSlot(reservation, { ended: true }, w.ports);
  assert.equal(guarded, true, 'synchronize the competing update with cleanup exclusion');
  assert.ok(w.records.has(path), 'a stale cleanup snapshot must not erase new evidence');
  assert.deepEqual(w.records.get(path).request_ids, changed === 'snapshot' ? ['original', 'new-paid-request'] : ['original']);
});

test('2704 S1: contested passive cleanup cannot delay uncapped admission', async () => {
  const w = localWorld(); w.add('dead-aged', 'active', 99, 1_800_000, ['unknown']);
  w.claimHook(() => false);
  const reservation = await acquireRuntimeSlot(w.options, w.ports);
  assert.ok(reservation);
  await releaseRuntimeSlot(reservation, { ended: true }, w.ports);
  assert.deepEqual([...w.records.values()].map(r => r.id), ['dead-aged']);
});

test('2704 S2: one immutable source Blob serves lint and all selected check uploads', async t => {
  const setup = selected(t, 7), sources = [], requests = [];
  // Observe the multipart boundary before FormData wraps Blob in a File.
  const OriginalFormData = globalThis.FormData;
  globalThis.FormData = class extends OriginalFormData {
    set(name, value, filename) {
      if (name === 'source') sources.push(value);
      if (name === 'request') requests.push(value);
      return super.set(name, value, filename);
    }
  };
  t.after(() => { globalThis.FormData = OriginalFormData; });
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const made = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--json': true } }, made.ports), 0);
  assert.equal(fake.posts.length, 8); assert.equal(sources.length, 8);
  assert.equal(new Set(sources).size, 1, 'multipart uploads must share the immutable packed source rather than copy it per request');
  assert.equal(new Set(requests).size, 8, 'request metadata remains independent');
  assert.equal(sources[0].type, 'application/x-tar');
  const bytes = Buffer.from(await sources[0].arrayBuffer());
  for (const post of fake.posts) { assert.deepEqual(post.tar, bytes); assert.equal(post.request.source_sha256, sha(bytes)); }
  assert.equal(new Set(fake.posts.map(p => p.request.requestId)).size, 8);
});

test('2704 S3: uncapped busy drops dispatch to one while accepted work runs', async t => {
  const setup = selected(t, 3); let made, acceptedId, polls = 0;
  const first = new Set(), retries = [], busyAt = [];
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'check') {
      const scenario = entry.request.scenario;
      if (!first.has(scenario)) {
        first.add(scenario);
        if (first.size === 1) { acceptedId = entry.request.requestId; return { status: 202, json: f.check(acceptedId, 'queued') }; }
        busyAt.push(made.clock.now);
        return { status: 429, headers: { 'retry-after': '7' }, json: { dispatch: 'not_started', error: { code: 'server-full', details: { retryable: true } } } };
      }
      retries.push({ scenario, at: made.clock.now });
      return { status: 202, json: f.check(entry.request.requestId, 'queued') };
    }
    if (entry.method === 'GET') { polls++; return { status: 200, json: f.check(entry.url.split('/').at(-1), 'running') }; }
    return f.normal(entry);
  });
  made = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }); made.ports.pollMs = 10000;
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--json': true } }, made.ports), 3);
  assert.equal(first.size, 3); assert.equal(busyAt.length, 2); assert.ok(polls > 0);
  assert.deepEqual(retries, [], 'window one must hold every busy retry behind still-running accepted work');
  assert.equal(fake.posts.filter(p => p.request.requestId === acceptedId).length, 1);
  assert.equal(fake.posts.filter(p => p.command === 'check').length, 3);
});
