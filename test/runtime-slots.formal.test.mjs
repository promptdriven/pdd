import test from 'node:test';
import assert from 'node:assert/strict';
import { acquireRuntimeSlot } from '../src/runtime-slots.mjs';

// Story oracle: a live occupied lease cannot be reclaimed. A sole waiter gets a
// reservation exactly when the occupied count is less than the requested limit.
test('bounded local admission: limits 1..3 and occupied counts 0..4', async () => {
  for (let limit = 1; limit <= 3; limit++) for (let occupied = 0; occupied <= 4; occupied++) {
    const records = new Map(Array.from({ length: occupied }, (_, i) => [`/state/slots/host/busy-${i}.json`, {
      id: `busy-${i}`, state: 'active', pid: 42, kind: 'check', started_at: 0, request_ids: [`r-${i}`],
    }]));
    let now = 0;
    const ports = { pid: 43, now: () => now, randomUUID: () => 'waiter', isAlive: () => true, sleep: async ms => now += ms,
      files: {
        listRecords: async () => ({ jobs: [...records.values()].filter(row => row.state) }),
        exclusiveCreate: async (path, row) => { if (records.has(path)) return false; records.set(path, row); return true; },
        writeAtomic: async (path, row) => records.set(path, row), unlink: async path => records.delete(path),
        modifiedAt: async path => records.has(path) ? 0 : null, touch: async path => records.has(path),
      } };
    const lease = await acquireRuntimeSlot({ stateDir: '/state', origin: 'https://host', limit, kind: 'try', deadline: 1 }, ports);
    assert.equal(!!lease, occupied < limit, `limit=${limit}, occupied=${occupied}`);
    assert.equal([...records.values()].filter(row => row.state === 'active').length, occupied + (occupied < limit ? 1 : 0));
    assert.equal([...records.values()].filter(row => row.state === 'waiting').length, 0);
  }
});
