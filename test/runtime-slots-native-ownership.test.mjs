import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, readdirSync, statSync, unlinkSync, utimesSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { acquireRuntimeSlot, recordRuntimeRequest, releaseRuntimeSlot } from '../src/runtime-slots.mjs';
import { temp } from './runtime-fake.mjs';

const flush = () => new Promise(done => setImmediate(done));
function manualTimers() {
  const active = new Set();
  return {
    active,
    setInterval(fn) { const timer = { fn }; active.add(timer); return timer; },
    clearInterval(timer) { active.delete(timer); },
    async tick() { for (const { fn } of [...active]) fn(); await flush(); },
  };
}

// Native files with injected clock/timers reproduce the ownership boundary
// without waiting for a real heartbeat or racing a filesystem timestamp tick.
for (const field of ['started_at', 'state', 'kind', 'request_ids']) {
  for (const heartbeat of [false, true]) test(`native heartbeat respects same-ID/PID successor ${field}, heartbeat=${heartbeat}`, async t => {
    const stateDir = join(temp(t), 'state'), origin = 'https://native-ownership.example';
    const directory = join(stateDir, 'slots', 'native-ownership.example'), file = join(directory, 'original.json');
    mkdirSync(directory, { recursive: true });
    let now = Date.now(), rounds = 0;
    const deadline = now + 120_000, timers = manualTimers();
    const holder = join(directory, 'holder.json');
    writeFileSync(holder, JSON.stringify({ id: 'holder', pid: process.pid, state: 'active', kind: 'check', started_at: now, request_ids: [] }));
    let successor, original, before, after;
    const ports = {
      randomUUID: () => 'original', now: () => now, timers,
      sleep: async () => {
        if (rounds++ > 0) { now = deadline; return; }
        original = JSON.parse(readFileSync(file));
        const changed = { started_at: original.started_at - 1, state: 'active', kind: 'lint', request_ids: ['successor-paid'] };
        successor = { ...original, [field]: changed[field] };
        writeFileSync(file, JSON.stringify(successor));
        const stale = new Date(now - 60_001); utimesSync(file, stale, stale);
        before = statSync(file).mtimeMs;
        if (heartbeat) await timers.tick();
        after = statSync(file).mtimeMs;
        assert.deepEqual(JSON.parse(readFileSync(file)), successor, 'heartbeat never rewrites the successor');
        unlinkSync(holder);
      },
    };
    let reservation;
    try {
      reservation = await acquireRuntimeSlot({ stateDir, origin, kind: 'check', limit: 1, deadline }, ports);
      assert.equal(after, before, 'old owner must not refresh any changed ownership field');
      if (field === 'state') {
        assert.equal(reservation, null, 'an active successor cannot be treated as this acquisition\'s waiting ticket');
        assert.deepEqual(JSON.parse(readFileSync(file)), successor, 'cleanup preserves the foreign active successor');
      } else {
        assert.equal(reservation?.id, 'original', 'expired foreign waiter stays reclaimable and free capacity is acquired');
        assert.equal(JSON.parse(readFileSync(file)).started_at, original.started_at, 'restoration retains original ordering');
      }
    } finally {
      if (reservation) await releaseRuntimeSlot(reservation, { ended: true }, ports);
    }
    assert.equal(timers.active.size, 0, 'refresh work ends with this owner');
  });
}

test('native ownership follows promotion and request writes across native ports, then ends with an uncertain lease', async t => {
  const stateDir = join(temp(t), 'state'), origin = 'https://native-writes.example';
  let now = Date.now(); const timers = manualTimers(), ports = { now: () => now, timers };
  const reservation = await acquireRuntimeSlot({ stateDir, origin, kind: 'check', limit: 1 }, ports);
  const file = join(reservation.directory, `${reservation.id}.json`);
  try {
    now += 5000; await timers.tick();
    assert.ok(Math.abs(statSync(file).mtimeMs - now) < 1, 'waiting-to-active promotion advances the owned snapshot');
    assert.equal(await recordRuntimeRequest(reservation, 'paid-one', ports), true);
    assert.equal(await recordRuntimeRequest(reservation, 'paid-two', ports), true);
    assert.equal(await recordRuntimeRequest(reservation, 'paid-one', ports), true);
    now += 5000; await timers.tick();
    assert.ok(Math.abs(statSync(file).mtimeMs - now) < 1, 'request registration through another native port keeps the original heartbeat valid');
    assert.deepEqual(JSON.parse(readFileSync(file)).request_ids, ['paid-one', 'paid-two']);
    assert.deepEqual(readdirSync(reservation.directory), [`${reservation.id}.json`], 'claim choosing/number transitions complete and clean up');
  } finally {
    await releaseRuntimeSlot(reservation, { ended: false }, ports);
  }
  assert.equal(timers.active.size, 0);
  const before = statSync(file).mtimeMs;
  now += 5000; await timers.tick();
  assert.equal(statSync(file).mtimeMs, before, 'uncertain paid lease remains without live ownership');
  assert.deepEqual(JSON.parse(readFileSync(file)).request_ids, ['paid-one', 'paid-two']);
});
