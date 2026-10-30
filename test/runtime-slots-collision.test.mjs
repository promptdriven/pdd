import test from 'node:test';
import assert from 'node:assert/strict';
import { join } from 'node:path';
import { acquireRuntimeSlot, releaseRuntimeSlot } from '../src/runtime-slots.mjs';

// The approved ownership rule protects only this acquisition's original ticket.
// Reusing its path does not exempt a different owner from ordinary freshness.
function collisionWorld(change, { age = 0, dead = false, state = 'waiting' } = {}) {
  const stateDir = '/virtual/collision', origin = 'https://collision.example';
  const directory = join(stateDir, 'slots', 'collision.example');
  const path = id => join(directory, `${id}.json`);
  const data = new Map(), modified = new Map(), timers = new Set(), listeners = new Set(), creates = [], reads = [];
  let now = 100_000, sleeps = 0, original, collision;
  const seed = (record, at = now) => { data.set(path(record.id), structuredClone(record)); modified.set(path(record.id), at); };
  seed({ id: 'holder', state: 'active', pid: 42, kind: 'check', started_at: now, request_ids: [] });
  const files = {
    listRecords: () => ({ jobs: [...data.values()].filter(row => row.state).map(row => structuredClone(row)) }),
    exclusiveCreate: (file, record) => {
      creates.push(structuredClone(record));
      if (data.has(file)) return false;
      data.set(file, structuredClone(record)); modified.set(file, now); return true;
    },
    writeAtomic: (file, record) => { data.set(file, structuredClone(record)); modified.set(file, now); },
    modifiedAt: file => modified.get(file) ?? null,
    touch: file => { if (!data.has(file)) return false; modified.set(file, now); return true; },
    unlink: file => { data.delete(file); modified.delete(file); },
  };
  const ports = {
    files, pid: 43, randomUUID: () => 'original', now: () => now, random: () => 0,
    isAlive: pid => !dead || pid !== 99,
    readRun: async id => { reads.push(id); return 'unknown'; },
    onInterrupt: fn => { listeners.add(fn); return () => listeners.delete(fn); },
    timers: { setInterval: fn => { timers.add(fn); return fn; }, clearInterval: fn => timers.delete(fn) },
    sleep: async () => {
      if (sleeps++ === 0) {
        original = structuredClone(data.get(path('original')));
        files.unlink(path('original')); files.unlink(path('holder'));
        now = 200_000;
        collision = { ...original, state, ...change };
        seed(collision, now - age);
      } else now = 1_000_000;
    },
  };
  return { ports, data, timers, listeners, creates, reads, path,
    options: { stateDir, origin, kind: 'check', limit: 1, deadline: 1_000_000 },
    original: () => original, collision: () => collision };
}

const reclaimable = [
  { name: 'different dead PID with a fresh file', change: { pid: 99 }, options: { dead: true } },
  { name: 'different PID at exactly 60 seconds', change: { pid: 99 }, options: { age: 60_000 } },
  { name: 'same PID and kind but different start at exactly 60 seconds', change: { started_at: 99_999 }, options: { age: 60_000 } },
  { name: 'same PID and start but different kind after 60 seconds', change: { kind: 'lint' }, options: { age: 60_001 } },
];
for (const { name, change, options } of reclaimable) test(`same-ID waiting collision: reclaim ${name} and restore original ticket`, async () => {
  const w = collisionWorld(change, options);
  const lease = await acquireRuntimeSlot(w.options, w.ports);
  try {
    assert.equal(lease?.id, 'original', 'a different expired waiting owner cannot strand a pending wait with free capacity');
    assert.deepEqual(w.creates.filter(row => row.state === 'waiting'), [w.original(), w.original()], 'exclusive restoration keeps the original ID, PID, kind and start time');
    assert.equal(w.data.get(w.path('original'))?.state, 'active');
    assert.deepEqual(w.reads, [], 'an abandoned waiting owner requires no paid-job probe');
  } finally {
    if (lease) await releaseRuntimeSlot(lease, { ended: true }, w.ports);
  }
  assert.equal(w.data.size, 0); assert.equal(w.timers.size, 0); assert.equal(w.listeners.size, 0);
});

const protectedCollisions = [
  { name: 'fresh different PID', change: { pid: 99 } },
  { name: 'same PID with different start just below expiry', change: { started_at: 99_999 }, options: { age: 59_999 } },
  { name: 'fresh different kind', change: { kind: 'try' } },
  { name: 'fresh active paid successor', change: { pid: 99, request_ids: ['paid-fresh-collision'] }, options: { state: 'active' } },
  { name: 'dead active paid successor with unknown evidence', change: { pid: 99, request_ids: ['paid-dead-collision'] }, options: { dead: true, age: 60_000, state: 'active' } },
];
for (const { name, change, options } of protectedCollisions) test(`same-ID collision: preserve ${name}`, async () => {
  const w = collisionWorld(change, options);
  const lease = await acquireRuntimeSlot(w.options, w.ports);
  try {
    assert.equal(lease, null, 'an occupied identity cannot be overwritten or mistaken for the original ticket');
    assert.deepEqual(w.data.get(w.path('original')), w.collision(), 'the successor survives admission and deadline cleanup');
    assert.equal(w.creates.filter(row => row.state === 'waiting').length, 1, 'no duplicate or replacement waiting ticket');
    assert.deepEqual(w.reads, options?.dead ? ['paid-dead-collision'] : []);
  } finally {
    if (lease) await releaseRuntimeSlot(lease, { ended: true }, w.ports);
  }
  assert.equal(w.timers.size, 0); assert.equal(w.listeners.size, 0);
});
