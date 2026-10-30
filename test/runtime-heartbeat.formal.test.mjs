import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, statSync, utimesSync, unlinkSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { acquireRuntimeSlot, recordRuntimeRequest, releaseRuntimeSlot } from '../src/runtime-slots.mjs';

// Source333: runtime-local-queue Rules to check and runtime-slots owner freshness.
// Enumerate native-file heartbeat boundaries, separately from the existing
// injected-files recovery model. No implementation predicates form the oracle.
const ages = [59_999, 60_000, 60_001];
const replacements = [
  ['id', row => ({ ...row, id: 'successor' })],
  ['pid', row => ({ ...row, pid: row.pid + 1 })],
  ['state', row => ({ ...row, state: 'waiting' })],
  ['kind', row => ({ ...row, kind: 'lint' })],
  ['started_at', row => ({ ...row, started_at: row.started_at - 1 })],
  ['request append', row => ({ ...row, request_ids: [...row.request_ids, 'third'] })],
  ['request removal', row => ({ ...row, request_ids: row.request_ids.slice(1) })],
  ['request reorder', row => ({ ...row, request_ids: [...row.request_ids].reverse() })],
];

function world() {
  const stateDir = mkdtempSync(join(tmpdir(), 'pdd-heartbeat-formal-'));
  const origin = 'https://heartbeat-formal.invalid:9443';
  const directory = join(stateDir, 'slots', encodeURIComponent(new URL(origin).host));
  mkdirSync(directory, { recursive: true });
  const intervals = new Set(), subscriptions = new Set();
  let now = 2_000_000;
  const ports = {
    now: () => now, randomUUID: () => 'original', random: () => 0,
    isAlive: () => true, interrupted: () => false,
    onInterrupt: fn => { subscriptions.add(fn); return () => subscriptions.delete(fn); },
    timers: {
      setInterval: (fn, ms) => { const handle = { fn, ms }; intervals.add(handle); return handle; },
      clearInterval: handle => intervals.delete(handle),
    },
    sleep: async () => { throw new Error('Unexpected wait in bounded world'); },
  };
  return {
    stateDir, origin, directory, ports, intervals, subscriptions,
    file: join(directory, 'original.json'),
    setNow: value => { now = value; },
    advance: ms => { now += ms; },
    acquire: extra => acquireRuntimeSlot({ stateDir, origin, kind: 'check', limit: 1, ...extra }, ports),
    async pulse() {
      for (const { fn } of [...intervals]) fn();
      await new Promise(done => setImmediate(done));
    },
    dispose: () => rmSync(stateDir, { recursive: true, force: true }),
  };
}

function put(path, row, refreshedAt) {
  writeFileSync(path, `${JSON.stringify(row)}\n`, { mode: 0o600 });
  utimesSync(path, new Date(refreshedAt), new Date(refreshedAt));
}
const read = path => JSON.parse(readFileSync(path, 'utf8'));

test('bounded native heartbeat cannot refresh any substituted identity: 24 worlds', async () => {
  for (const [field, replace] of replacements) for (const age of ages) {
    const w = world();
    let lease;
    try {
      lease = await w.acquire();
      assert.ok(lease);
      await recordRuntimeRequest(lease, 'first', w.ports);
      await recordRuntimeRequest(lease, 'second', w.ports);
      const replacement = replace(read(w.file));
      put(w.file, replacement, w.ports.now() - age);
      const before = readFileSync(w.file, 'utf8'), modified = statSync(w.file).mtimeMs;
      await w.pulse();
      assert.equal(statSync(w.file).mtimeMs, modified, `${field}/${age}: another record cannot gain freshness`);
      assert.equal(readFileSync(w.file, 'utf8'), before, `${field}/${age}: heartbeat cannot rewrite a successor`);
      assert.equal(w.intervals.size, 0, `${field}/${age}: lost ownership stops refreshes`);
      await releaseRuntimeSlot(lease, { ended: false }, w.ports);
      lease = null;
      assert.equal(readFileSync(w.file, 'utf8'), before);
      assert.equal(w.subscriptions.size, 0);
    } finally {
      if (lease) await releaseRuntimeSlot(lease, { ended: false }, w.ports);
      w.dispose();
    }
  }
});

test('bounded waiting replacements keep ordinary freshness after a pulse: 18 worlds', async () => {
  const waitingChanges = replacements.filter(([name]) => ['pid', 'kind', 'started_at'].includes(name));
  for (const [field, replace] of waitingChanges) for (const age of ages) for (const pulse of [false, true]) {
    const w = world(), label = `${field}/${age}/pulse=${pulse}`;
    const holder = join(w.directory, 'holder.json');
    put(holder, { id: 'holder', state: 'active', pid: process.pid, kind: 'check', started_at: w.ports.now(), request_ids: [] }, w.ports.now());
    let replacement, original, slept = false, lease;
    w.ports.sleep = async () => {
      if (slept) { w.setNow(2_120_000); return; }
      slept = true;
      original = read(w.file);
      replacement = replace(original);
      put(w.file, replacement, w.ports.now() - age);
      const modified = statSync(w.file).mtimeMs;
      if (pulse) await w.pulse();
      assert.equal(statSync(w.file).mtimeMs, modified, `${label}: a heartbeat cannot protect the replacement`);
      assert.deepEqual(read(w.file), replacement);
      unlinkSync(holder);
    };
    try {
      lease = await w.acquire({ deadline: 2_120_000 });
      // The owner prompt fixes the boundary at >=60s, independently of pulse.
      if (age >= 60_000) {
        assert.equal(lease?.id, 'original', `${label}: expired foreign waiting owner must not strand acquisition`);
        assert.deepEqual(read(w.file), { ...original, state: 'active' }, `${label}: restore the original identity`);
      } else {
        assert.equal(lease, null, `${label}: a fresh foreign owner retains its ticket`);
        assert.deepEqual(read(w.file), replacement, `${label}: no overwrite or cleanup of successor`);
      }
      await releaseRuntimeSlot(lease, { ended: true }, w.ports);
      lease = null;
      assert.equal(w.intervals.size, 0);
      assert.equal(w.subscriptions.size, 0);
    } finally {
      if (lease) await releaseRuntimeSlot(lease, { ended: true }, w.ports);
      w.dispose();
    }
  }
});

test('legitimate waiting promotion and request updates retain refresh; ended:false retains unknown paid lease', async () => {
  const w = world(), holder = join(w.directory, 'holder.json');
  put(holder, { id: 'holder', state: 'active', pid: process.pid, kind: 'check', started_at: w.ports.now(), request_ids: [] }, w.ports.now());
  let original, lease;
  w.ports.sleep = async () => {
    original = read(w.file);
    w.advance(5_000);
    await w.pulse();
    assert.deepEqual(read(w.file), original);
    assert.equal(statSync(w.file).mtimeMs, w.ports.now(), 'a legitimate waiting ticket stays fresh');
    unlinkSync(holder);
  };
  try {
    lease = await w.acquire();
    assert.ok(lease);
    assert.deepEqual(read(w.file), { ...original, state: 'active', started_at: w.ports.now() });
    for (const request of [null, 'first', 'second', 'first']) {
      if (request !== null) assert.equal(await recordRuntimeRequest(lease, request, w.ports), true);
      w.advance(5_000);
      await w.pulse();
      assert.equal(statSync(w.file).mtimeMs, w.ports.now(), `owned update ${request} keeps refreshing`);
      assert.equal(w.intervals.size, 1);
    }
    assert.deepEqual(read(w.file).request_ids, ['first', 'second']);
    await releaseRuntimeSlot(lease, { ended: false }, w.ports);
    const retained = readFileSync(w.file, 'utf8'), modified = statSync(w.file).mtimeMs;
    assert.equal(w.intervals.size, 0);
    assert.equal(w.subscriptions.size, 0);
    w.advance(60_000);
    await w.pulse();
    assert.equal(statSync(w.file).mtimeMs, modified, 'return with uncertain work cannot pretend to remain alive');
    const observed = [];
    w.ports.randomUUID = () => 'competitor';
    w.ports.readRun = async id => { observed.push(id); return 'unknown'; };
    const deadline = w.ports.now() + 1_000;
    w.ports.sleep = async () => w.setNow(deadline);
    assert.equal(await w.acquire({ deadline }), null, 'stale owner does not establish completion of paid work');
    assert.deepEqual(observed, ['first', 'second']);
    assert.equal(readFileSync(w.file, 'utf8'), retained, 'unknown younger-than-30-minute paid work retains its exact lease');
    assert.equal(w.intervals.size, 0);
    assert.equal(w.subscriptions.size, 0);
  } finally {
    if (lease) await releaseRuntimeSlot(lease, { ended: true }, w.ports);
    w.dispose();
  }
});
