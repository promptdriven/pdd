import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync } from 'node:fs';
import { randomUUID } from 'node:crypto';
import { join } from 'node:path';
import { acquireRuntimeSlot, releaseRuntimeSlot, listRuntimeJobs } from '../src/runtime-slots.mjs';
import { fakeRuntime, temp } from './runtime-fake.mjs';

const flush = () => new Promise(done => setImmediate(done));
const paid = { id: 'dead', state: 'active', pid: 2147483647, kind: 'check', started_at: 0, request_ids: ['paid'] };

test('long-native-observer-deadline: default timers preserve a 30-day wait through one shared 150ms GET', async t => {
  let began;
  const started = new Promise(done => { began = done; });
  const fake = await fakeRuntime(t, async entry => {
    assert.equal(entry.method, 'GET'); assert.equal(entry.url, '/v1/runs/paid');
    began(); await new Promise(done => setTimeout(done, 150));
    return { status: 200, json: { state: 'ended' } };
  });
  const stateDir = temp(t), directory = join(stateDir, 'slots', encodeURIComponent(new URL(fake.origin).host));
  mkdirSync(directory, { recursive: true });
  writeFileSync(join(directory, 'dead.json'), JSON.stringify({ ...paid, started_at: Date.now() }));
  const signals = ['SIGINT', 'SIGHUP', 'SIGTERM'], listeners = signals.map(signal => process.listenerCount(signal)), warnings = [];
  const warning = value => { if (value.name === 'TimeoutOverflowWarning') warnings.push(value.message); };
  process.on('warning', warning); t.after(() => process.off('warning', warning));
  const options = { stateDir, origin: fake.origin, kind: 'lint', limit: 1 };
  const first = acquireRuntimeSlot({ ...options, deadline: Date.now() + 2000 }, {
    readRun: async id => (await (await fetch(`${fake.origin}/v1/runs/${id}`)).json()).state,
  }).then(async reservation => {
    if (reservation) await releaseRuntimeSlot(reservation, { ended: true });
    return reservation;
  });
  await started;
  let settled = false;
  const second = acquireRuntimeSlot({ ...options, deadline: Date.now() + 2_592_000_000 }, {
    readRun: () => assert.fail('a borrower must reuse the initiating GET'),
  }).then(reservation => { settled = true; return reservation; });
  await new Promise(done => setTimeout(done, 30));
  const early = settled, leaseBeforeEnd = (await listRuntimeJobs(options)).jobs.find(row => row.id === 'dead');
  const firstReservation = await first, secondReservation = await second;
  if (secondReservation) await releaseRuntimeSlot(secondReservation, { ended: true });
  assert.equal(early, false, 'the far deadline must not become a 1ms expiry');
  assert.deepEqual(leaseBeforeEnd?.request_ids, ['paid']);
  assert.ok(firstReservation); assert.ok(secondReservation);
  assert.equal(fake.gets.length, 1); assert.equal(fake.posts.length + fake.jsonPosts.length, 0);
  assert.deepEqual(warnings, []);
  assert.deepEqual((await listRuntimeJobs(options)).jobs, []);
  assert.deepEqual(signals.map(signal => process.listenerCount(signal)), listeners);
});

// Advance repeating timers at their actual due times, including timers created
// or cleared inside callbacks. A callback does not stand in for elapsed time.
function clockWorld() {
  let now = 0, sequence = 0;
  const origin = `https://${randomUUID()}.example`, directory = join('/virtual', 'slots', new URL(origin).host);
  const records = new Map([[join(directory, 'dead.json'), structuredClone(paid)]]), refreshed = new Map();
  const intervals = new Set(), delays = [];
  const files = {
    listRecords: () => ({ jobs: [...records.values()].filter(row => row.state).map(row => structuredClone(row)) }),
    exclusiveCreate: (path, row) => { if (records.has(path)) return false; records.set(path, structuredClone(row)); refreshed.set(path, now); return true; },
    writeAtomic: (path, row) => { records.set(path, structuredClone(row)); refreshed.set(path, now); },
    unlink: path => { records.delete(path); refreshed.delete(path); },
    modifiedAt: path => records.has(path) ? refreshed.get(path) ?? 0 : null,
    touch: path => { if (!records.has(path)) return false; refreshed.set(path, now); return true; },
  };
  const timers = {
    setInterval: (fn, ms) => { delays.push(ms); const timer = { fn, ms, next: now + ms }; intervals.add(timer); return timer; },
    clearInterval: timer => intervals.delete(timer),
  };
  const caller = () => {
    const listeners = new Set();
    return { listeners, signal: () => { for (const fn of [...listeners]) fn(); }, ports: {
      files, timers, now: () => now, pid: 123, isAlive: pid => pid !== paid.pid, randomUUID: () => `ticket-${++sequence}`, random: () => 0,
      onInterrupt: fn => { listeners.add(fn); return () => listeners.delete(fn); },
      sleep: async () => assert.fail('pending probe observers must not reach queue backoff'),
    } };
  };
  return { records, intervals, delays, caller, options: { stateDir: '/virtual', origin, kind: 'lint', limit: 1 },
    advance: async target => {
      for (;;) {
        const next = [...intervals].filter(timer => timer.next <= target).sort((a, b) => a.next - b.next)[0];
        if (!next) break;
        now = next.next; next.next += next.ms; next.fn(); await flush();
      }
      now = target; await flush();
    },
  };
}

for (const mode of ['deadline', 'long-interrupt', 'null-interrupt']) test(`long-native-observer-deadline: faithful clock ${mode} preserves shared read and cleans timers/subscriptions`, async () => {
  const w = clockWorld(), creator = w.caller(), borrower = w.caller();
  let complete, reads = 0, settled = false;
  creator.ports.readRun = async () => { reads++; return new Promise(done => { complete = done; }); };
  borrower.ports.readRun = () => assert.fail('duplicate read');
  const first = acquireRuntimeSlot(w.options, creator.ports); await flush();
  const deadline = mode === 'null-interrupt' ? null : mode === 'deadline' ? 130_001 : 2_592_000_000;
  const second = acquireRuntimeSlot({ ...w.options, deadline }, borrower.ports).then(value => { settled = true; return value; });
  await flush();
  const observerDelays = () => w.delays.filter(ms => ms !== 5000);
  try {
    for (const at of [59_999, 60_000, 119_999, 120_000, 130_000]) {
      await w.advance(at);
      assert.equal(settled, false, `observer ended before its absolute deadline at ${at}`);
      assert.equal(reads, 1);
      assert.deepEqual(w.records.get(join('/virtual', 'slots', new URL(w.options.origin).host, 'dead.json')), paid);
    }
    if (mode === 'deadline') {
      assert.deepEqual(observerDelays(), [60_000, 60_000, 10_001]);
      await w.advance(130_001);
    } else {
      if (deadline === null) assert.deepEqual(observerDelays(), []);
      else assert.ok(observerDelays().every(ms => ms > 0 && ms <= 60_000));
      borrower.signal(); await flush();
    }
    assert.equal(settled, true); assert.equal(await second, null);
    assert.equal(borrower.listeners.size, 0);
    assert.equal(w.intervals.size, 1, 'only the initiating caller heartbeat remains');
    assert.equal(creator.listeners.size, 1); assert.equal(reads, 1);
  } finally {
    borrower.signal(); creator.signal(); complete('running');
    assert.equal(await first, null); assert.equal(await second, null);
  }
  assert.equal(w.intervals.size, 0); assert.equal(creator.listeners.size + borrower.listeners.size, 0);
  assert.deepEqual([...w.records.values()], [paid]); assert.equal(reads, 1);
});
