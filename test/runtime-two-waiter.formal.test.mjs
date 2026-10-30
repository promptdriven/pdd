import test from 'node:test';
import assert from 'node:assert/strict';
import { randomUUID } from 'node:crypto';
import { join } from 'node:path';
import { acquireRuntimeSlot, recordRuntimeRequest, releaseRuntimeSlot } from '../src/runtime-slots.mjs';

// Independent oracle: user_stories/runtime-local-queue.md and
// runtime-capacity-wait.md, Rules to check; runtime-slots.prompt.md owns the
// exact freshness, identity, ordering and paid-lease rules. No observed output
// supplies an expected result. Every member of each finite product below runs.
// These declared file/clock/timer ports model controlled event-loop schedules,
// not all native filesystem, signal or OS process interleavings.
const ages = [59_999, 60_000, 60_001];
const bits = [false, true];
const flush = () => new Promise(done => setImmediate(done));
const clone = value => structuredClone(value);
const record = (id, extra = {}) => ({ id, state: 'active', pid: 41, kind: 'check', started_at: 100_000, request_ids: ['uncertain'], ...extra });

function world(reverse = false) {
  const stateDir = '/formal/two-waiter', origin = `https://${randomUUID()}.example`;
  const directory = join(stateDir, 'slots', new URL(origin).host);
  const data = new Map(), modified = new Map(), timers = new Set(), listeners = new Set();
  const w = { now: 100_000, data, modified, timers, listeners, creates: [], claims: [], reads: [], writes: [] };
  w.path = id => join(directory, `${id}.json`);
  w.seed = (row, at = w.now) => { data.set(w.path(row.id), clone(row)); modified.set(w.path(row.id), at); };
  w.files = {
    listRecords() { const jobs = [...data.values()].filter(row => row.state).map(clone); return { jobs: reverse ? jobs.reverse() : jobs }; },
    exclusiveCreate(path, row) {
      w.beforeCreate?.(path, row);
      w.creates.push({ path, row: clone(row), occupied: data.has(path) });
      if (data.has(path)) return false;
      data.set(path, clone(row)); modified.set(path, w.now); return true;
    },
    writeAtomic(path, row) { w.writes.push({ path, row: clone(row) }); data.set(path, clone(row)); modified.set(path, w.now); },
    unlink(path) { data.delete(path); modified.delete(path); },
    modifiedAt: path => modified.get(path) ?? null,
    touch(path) { if (!data.has(path)) return false; modified.set(path, w.now); return true; },
  };
  w.options = { stateDir, origin, limit: 1, kind: 'check' };
  w.ports = id => ({
    files: { ...w.files, exclusiveCreate(path, row) { if (path.endsWith('/claim.json')) w.claims.push(id); return w.files.exclusiveCreate(path, row); } },
    now: () => w.now, pid: id === 'a' ? 42 : 43, randomUUID: () => id, random: () => 0, isAlive: () => true,
    sleep: async ms => { w.now += ms; },
    readRun: async id => { w.reads.push(id); return 'unknown'; },
    onInterrupt(fn) { listeners.add(fn); return () => listeners.delete(fn); },
    timers: {
      setInterval(fn, ms) { const timer = { fn, ms }; timers.add(timer); return timer; },
      clearInterval(timer) { timers.delete(timer); },
    },
  });
  w.pulse = async () => { for (const timer of [...timers]) timer.fn(); await flush(); };
  w.interrupt = () => { for (const fn of [...listeners]) fn(); };
  w.waitingCreates = id => w.creates.filter(entry => entry.row.state === 'waiting' && entry.row.id === id);
  w.clean = () => { assert.equal(timers.size, 0); assert.equal(listeners.size, 0); assert.equal(data.has(join(directory, 'claim.json')), false); };
  return w;
}

// A scheduled caller stops only at its real public sleep boundary. A generous
// wall-clock watchdog detects a broken harness/stall; elapsed speed is no oracle.
async function settle(predicate) {
  const watchdog = Date.now() + 30_000;
  while (!predicate() && Date.now() < watchdog) await flush();
  assert.ok(predicate(), 'scheduled caller reaches sleep or public completion');
}
async function start(w, id, startedAt) {
  const ports = w.ports(id), c = { ports, turns: 0, done: false, wake: null };
  ports.sleep = () => { c.turns++; return new Promise(done => c.wake = done); };
  w.now = startedAt;
  c.pending = acquireRuntimeSlot({ ...w.options, deadline: 300_000 }, ports).then(lease => { c.done = true; c.lease = lease; return lease; });
  await settle(() => c.turns || c.done);
  c.step = async () => {
    assert.equal(c.done, false, 'only an ongoing acquisition is resumed');
    const turn = c.turns, wake = c.wake; c.wake = null; wake();
    await settle(() => c.turns > turn || c.done);
  };
  return c;
}

test('formal pending recovery: ages 59999..60001 x loss masks 1..3 x absent heartbeat 0..1 (18 worlds)', async () => {
  for (const age of ages) for (const mask of [1, 2, 3]) for (const heartbeat of bits) {
    const w = world(), ports = w.ports('a'), original = record('a', { state: 'waiting', pid: 42, request_ids: [] });
    w.seed(record('holder')); let sleeps = 0;
    ports.sleep = async () => {
      sleeps++;
      assert.deepEqual(w.data.get(w.path('a')), original, `recovery keeps original identity/time: ${age}/${mask}/${heartbeat}/${sleeps}`);
      if (sleeps === 1) {
        w.now += age;
        w.seed(record('abandoned', { state: 'waiting', started_at: 1, request_ids: [] }), w.now - age);
        w.seed(record('later', { state: 'waiting', started_at: w.now + 1, request_ids: [] }));
      }
      if (sleeps === 2) {
        assert.equal(w.data.has(w.path('abandoned')), age < 60_000, 'other owners retain the exact expiry boundary');
        assert.deepEqual(w.data.get(w.path('holder')), record('holder'), 'ticket loss supplies no paid completion evidence');
      }
      if (sleeps <= 2 && mask & (1 << (sleeps - 1))) {
        w.files.unlink(w.path('a'));
        if (heartbeat) { await w.pulse(); assert.equal(w.data.has(w.path('a')), false, 'heartbeat itself never recreates'); }
      }
      if (sleeps === 3) {
        w.now += 5000; await w.pulse();
        assert.equal(w.modified.get(w.path('a')), w.now, 'restored waiting refresh lifecycle is active');
        w.files.unlink(w.path('holder')); w.files.unlink(w.path('abandoned'));
      }
      assert.ok(sleeps <= 3, 'restored head progresses to next free slot');
    };
    const lease = await acquireRuntimeSlot({ ...w.options, deadline: 250_000 }, ports);
    assert.equal(lease?.id, 'a'); assert.equal(sleeps, 3);
    assert.equal(w.waitingCreates('a').length, 1 + Number(!!(mask & 1)) + Number(!!(mask & 2)));
    assert.ok(w.waitingCreates('a').every(entry => !entry.occupied && JSON.stringify(entry.row) === JSON.stringify(original)));
    await releaseRuntimeSlot(lease, { ended: true }, ports);
    assert.deepEqual([...w.data.values()].map(row => row.id), ['later']); w.clean();
  }
});

test('formal two waiter schedules: 3 ages x 3 time orders x 2 create orders x 2 resume orders x 2 listings x 2 loss patterns (144 worlds)', { timeout: 120_000 }, async () => {
  for (const age of ages) for (const delta of [-1, 0, 1]) for (const createReverse of bits)
    for (const resumeReverse of bits) for (const listingReverse of bits) for (const externalLoss of bits) {
      const w = world(listingReverse), initial = { a: 100_000, b: 100_000 + delta }, callers = {};
      w.seed(record('holder'));
      for (const id of createReverse ? ['b', 'a'] : ['a', 'b']) callers[id] = await start(w, id, initial[id]);
      const originals = Object.fromEntries(['a', 'b'].map(id => [id, clone(w.data.get(w.path(id)))]));
      w.now = 160_002; w.modified.set(w.path('holder'), w.now);
      for (const id of ['a', 'b']) w.modified.set(w.path(id), w.now - age);
      if (externalLoss) { for (const id of ['a', 'b']) w.files.unlink(w.path(id)); await w.pulse(); }
      const first = resumeReverse ? 'b' : 'a', second = first === 'a' ? 'b' : 'a';
      await callers[first].step(); await callers[second].step(); await callers[first].step();
      for (const id of ['a', 'b']) assert.deepEqual(w.data.get(w.path(id)), originals[id], 'both ongoing waits preserve original ticket and start');
      const head = delta < 0 ? 'b' : 'a', tail = head === 'a' ? 'b' : 'a';
      w.files.unlink(w.path('holder'));
      const claims = w.claims.length; await callers[tail].step();
      assert.equal(w.claims.length, claims, 'later ticket does not compete, including an ID tie');
      assert.equal(callers[tail].done, false);
      await callers[head].step(); assert.equal((await callers[head].pending)?.id, head);
      await callers[tail].step(); assert.equal(callers[tail].done, false);
      assert.equal([...w.data.values()].filter(row => row.state === 'active').length, 1, 'limit one excludes second waiter');
      await releaseRuntimeSlot(callers[head].lease, { ended: true }, callers[head].ports);
      await callers[tail].step(); assert.equal((await callers[tail].pending)?.id, tail);
      await releaseRuntimeSlot(callers[tail].lease, { ended: true }, callers[tail].ports);
      await w.pulse(); assert.equal(w.data.size, 0, 'ended waits cannot be restored by retained timer callbacks'); w.clean();
    }
});

test('formal stops: 3 owner ages x 2 absent heartbeat patterns x interrupt/deadline (12 worlds)', async () => {
  for (const age of ages) for (const heartbeat of bits) for (const stop of ['interrupt', 'deadline']) {
    const w = world(), paid = record('paid'); w.seed(paid); w.now += age;
    const ports = w.ports('a'); let sleeps = 0;
    ports.sleep = async () => {
      sleeps++; w.files.unlink(w.path('a'));
      if (heartbeat) await w.pulse();
      if (stop === 'interrupt') w.interrupt(); else w.now = 250_000;
    };
    assert.equal(await acquireRuntimeSlot({ ...w.options, deadline: 250_000 }, ports), null);
    await w.pulse();
    assert.equal(sleeps, 1); assert.equal(w.waitingCreates('a').length, 1, 'ended wait never attempts restoration');
    assert.deepEqual([...w.data.values()], [paid]);
    assert.equal(w.reads.length, age < 60_000 ? 0 : 1); assert.equal(w.writes.length, 0, 'no admission or request recording after stop'); w.clean();
  }
});

test('formal exclusive restoration: 3 ages x 2 collision states x 2 heartbeat patterns (12 worlds)', async () => {
  for (const age of ages) for (const state of ['waiting', 'active']) for (const heartbeat of bits) {
    const w = world(), ports = w.ports('a'); w.seed(record('holder'));
    const collision = record('a', { state, pid: 99, started_at: 99_000, request_ids: state === 'active' ? ['other-paid'] : [] });
    let sleeps = 0, collided = false;
    w.beforeCreate = (path, row) => {
      if (row.state === 'waiting' && w.waitingCreates('a').length && !collided) { collided = true; w.seed(collision); }
    };
    ports.sleep = async () => {
      if (++sleeps === 1) { w.now += age; w.files.unlink(w.path('a')); if (heartbeat) await w.pulse(); }
      else w.now = 250_000;
    };
    assert.equal(await acquireRuntimeSlot({ ...w.options, deadline: 250_000 }, ports), null);
    assert.equal(collided, true); assert.deepEqual(w.data.get(w.path('a')), collision, 'exclusive recovery and cleanup preserve the successor');
    assert.equal(w.waitingCreates('a').filter(entry => entry.occupied).length, 1); assert.equal(w.writes.length, 0); w.clean();
  }
});

test('formal acquired/ended reservations: both release outcomes x deletion before/after release (4 worlds)', async () => {
  for (const ended of bits) for (const deleteBefore of bits) {
    const w = world(), ports = w.ports('a'), lease = await acquireRuntimeSlot(w.options, ports);
    assert.equal(await recordRuntimeRequest(lease, 'paid-unknown', ports), true);
    assert.equal(await recordRuntimeRequest(lease, 'paid-unknown', ports), true);
    const paid = clone(w.data.get(w.path('a'))); assert.deepEqual(paid.request_ids, ['paid-unknown']);
    if (deleteBefore) { w.files.unlink(w.path('a')); await w.pulse(); assert.equal(w.data.size, 0, 'active heartbeat never recreates'); }
    await releaseRuntimeSlot(lease, { ended }, ports);
    assert.equal(w.data.has(w.path('a')), !ended && !deleteBefore, 'uncertain release retains the exact paid lease');
    if (!ended && !deleteBefore) assert.deepEqual(w.data.get(w.path('a')), paid);
    w.files.unlink(w.path('a')); await w.pulse();
    assert.equal(w.data.size, 0); assert.equal(w.waitingCreates('a').length, 1); w.clean();
  }
});

test('formal paid uncertainty: 5 freshness/lease boundary ages x unknown/running/read-failure (15 worlds)', async () => {
  for (const age of [...ages, 1_799_999, 1_800_000]) for (const evidence of ['unknown', 'running', 'read-failure']) {
    const w = world(), paid = record('paid'), ports = w.ports('a'); w.seed(paid); w.now += age;
    ports.readRun = async id => { w.reads.push(id); if (evidence === 'read-failure') throw Error('synthetic unavailable evidence'); return evidence; };
    const lease = await acquireRuntimeSlot({ ...w.options, deadline: w.now + 1 }, ports);
    assert.equal(!!lease, age >= 1_800_000, 'uncertain evidence cannot free an unexpired paid lease');
    assert.equal(w.reads.length, age < 60_000 || age >= 1_800_000 ? 0 : 1);
    if (age < 1_800_000) assert.deepEqual([...w.data.values()], [paid]);
    else await releaseRuntimeSlot(lease, { ended: true }, ports);
    assert.ok(w.reads.every(id => id === 'uncertain'), 'recovery reads preserve the original request identity'); w.clean();
  }
});
