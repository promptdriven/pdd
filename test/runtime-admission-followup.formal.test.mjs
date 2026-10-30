import test from 'node:test';
import assert from 'node:assert/strict';
import { randomUUID } from 'node:crypto';
import { join } from 'node:path';
import { acquireRuntimeSlot, releaseRuntimeSlot } from '../src/runtime-slots.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor, TOKEN } from './runtime-fake.mjs';

// Oracles come from the approved local-queue/capacity-wait Rules to check and
// their owner prompts, not from a captured implementation result. Every integer
// in each inclusive range below is executed; other integers are outside scope.
const integers = (first, last) => Array.from({ length: last - first + 1 }, (_, i) => first + i);
const flush = () => new Promise(done => setImmediate(done));
const deferred = () => { let resolve; const promise = new Promise(done => resolve = done); return { promise, resolve }; };
async function until(predicate) {
  const end = Date.now() + 30_000;
  while (!predicate() && Date.now() < end) await flush();
  assert.ok(predicate(), 'the controlled public-boundary event must occur');
}
function clockTimers(clock) {
  const active = new Set(), delays = [];
  return { active, delays, port: {
    setInterval(fn, ms) { const timer = { fn, ms, due: clock.now + ms }; active.add(timer); delays.push(ms); return timer; },
    clearInterval(timer) { active.delete(timer); },
  },
  // Model an event loop resuming after suspension: elapsed wall time advances
  // before overdue callbacks run, and each overdue interval is serviced once.
  async resume(at) {
    clock.now = at;
    for (const timer of [...active]) if (active.has(timer) && timer.due <= at) {
      timer.due = at + timer.ms; timer.fn();
    }
    await flush();
  } };
}
function memory(clock) {
  const records = new Map(), modified = new Map();
  const files = {
    listRecords: () => ({ jobs: [...records.values()].filter(row => row.state).map(row => structuredClone(row)) }),
    exclusiveCreate(path, row) { if (records.has(path)) return false; records.set(path, structuredClone(row)); modified.set(path, clock.now); return true; },
    writeAtomic(path, row) { records.set(path, structuredClone(row)); modified.set(path, clock.now); },
    unlink(path) { records.delete(path); modified.delete(path); },
    modifiedAt: path => modified.get(path) ?? null,
    touch(path) { if (!records.has(path)) return false; modified.set(path, clock.now); return true; },
  };
  return { records, modified, files };
}
const warnings = made => (made.ports.stderr.text.match(/Warning: runtime capacity/g) ?? []).length;
function caller(setup, origin, clock, extra = {}, owner = 'formal 4242') {
  const made = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: origin }, {
    now: () => clock.now,
    sleep: async ms => { assert.ok(ms > 0); clock.now += ms; await flush(); },
    gh: args => args[0] === 'auth' ? { status: 0, stdout: `${TOKEN}\n` } : { status: 0, stdout: `${owner}\n` },
    ...extra,
  });
  const subscriptions = new Set(), subscribe = made.ports.onInterrupt;
  made.ports.onInterrupt = fn => { subscriptions.add(fn); const off = subscribe(fn); return () => { subscriptions.delete(fn); off(); }; };
  made.subscriptions = subscriptions;
  return made;
}
const invoke = (setup, made, milliseconds = 2_592_000_000) => runCheck({ cwd: setup.repo, words: ['place-order'],
  options: { '--lint': true, '--json': true, '--timeout': milliseconds / 60_000 } }, made.ports);

test('formal ticket identity/order: every own jump and other-owner age in 59998..60002 ms (25 worlds)', async () => {
  for (const jump of integers(59_998, 60_002)) for (const otherAge of integers(59_998, 60_002)) {
    const clock = { now: 100_000 }, mem = memory(clock), timers = clockTimers(clock);
    const origin = `https://${randomUUID()}.example`, directory = join('/formal', 'slots', new URL(origin).host);
    const path = id => join(directory, `${id}.json`);
    const paid = { id: 'paid', state: 'active', pid: 41, kind: 'check', started_at: clock.now, request_ids: ['uncertain'] };
    mem.records.set(path('paid'), structuredClone(paid)); mem.modified.set(path('paid'), clock.now);
    let sleeps = 0, reads = 0;
    const ports = { files: mem.files, timers: timers.port, now: () => clock.now, pid: 42,
      isAlive: () => true, randomUUID: () => 'mine', random: () => 0, onInterrupt: () => () => {},
      readRun: async id => { assert.equal(id, 'uncertain'); reads++; return 'unknown'; },
      sleep: async () => {
        sleeps++;
        assert.deepEqual(mem.records.get(path('mine')), { id: 'mine', state: 'waiting', pid: 42, kind: 'check', started_at: 100_000, request_ids: [] }, `jump=${jump}, age=${otherAge}`);
        if (sleeps === 1) {
          clock.now += jump;
          for (const [id, started] of [['abandoned', 1], ['later', clock.now]]) {
            mem.records.set(path(id), { ...paid, id, state: 'waiting', started_at: started, request_ids: [] });
            mem.modified.set(path(id), id === 'abandoned' ? clock.now - otherAge : clock.now);
          }
        } else {
          assert.equal(sleeps, 2, 'the original ticket takes the next available slot');
          assert.equal(mem.records.has(path('abandoned')), otherAge < 60_000, 'only another expired owner is reclaimed');
          assert.deepEqual(mem.records.get(path('paid')), paid, 'unknown paid work cannot become free capacity');
          const liveOrder = [...mem.records.values()].filter(row => row.state === 'waiting' && row.id !== 'abandoned').sort((a, b) => a.started_at - b.started_at).map(row => row.id);
          assert.deepEqual(liveOrder, ['mine', 'later']);
          // The environment now confirms the occupied work ended and removes
          // the still-fresh earlier waiter, making the next slot available.
          mem.files.unlink(path('paid')); mem.files.unlink(path('abandoned'));
        }
      },
    };
    const lease = await acquireRuntimeSlot({ stateDir: '/formal', origin, kind: 'check', limit: 1, deadline: 200_000 }, ports);
    assert.equal(lease?.id, 'mine'); assert.equal(sleeps, 2);
    assert.equal(reads, jump >= 60_000 ? 1 : 0);
    await releaseRuntimeSlot(lease, { ended: true }, ports);
    assert.deepEqual([...mem.records.values()].map(row => row.id), ['later']); assert.equal(timers.active.size, 0);
  }
});

test('formal unclear capacity: six failures x every completion age 9998..10002 ms (30 worlds)', { timeout: 120_000 }, async t => {
  const a = harbor(t), b = harbor(t), fake = await fakeRuntime(t, (entry, runtime) => runtime.normal(entry));
  for (const failure of ['html', '405', '500', 'body-read', 'timeout', 'unreachable']) for (const age of integers(9998, 10002)) {
    const clock = { now: 0 }, gate = deferred(); let reads = 0, posts = 0;
    const transport = async (url, init) => {
      if (new URL(url).pathname !== '/v1/capacity') { posts++; return fetch(url, init); }
      reads++;
      if (reads === 1) {
        await gate.promise;
        if (failure === 'body-read') return { text: async () => { throw Error('finite body-read failure'); } };
        if (failure === 'timeout') throw Object.assign(Error('finite timeout'), { name: 'AbortError' });
        if (failure === 'unreachable') throw Object.assign(Error('finite unreachable read'), { cause: { code: 'ECONNREFUSED' } });
        return new Response(failure === 'html' ? '<html>proxy</html>' : '{}', { status: failure === 'html' ? 200 : Number(failure) });
      }
      return Response.json({ maintenance: reads === 2 ? { until: new Date(clock.now + 3).toISOString(), reason: 'formal TTL maintenance' } : null });
    };
    const owner = `formal-${failure}-${age} 4242`, timers = clockTimers(clock);
    const make = setup => caller(setup, fake.origin, clock, { fetch: transport, timers: timers.port }, owner);
    const first = make(a), second = make(b), p = invoke(a, first), q = invoke(b, second);
    await until(() => reads === 1 && timers.delays.filter(ms => ms !== 5000).length === 2);
    assert.equal(posts, 0); clock.now = 1000; gate.resolve();
    assert.deepEqual(await Promise.all([p, q]), [0, 0]);
    assert.equal(reads, 1, 'simultaneous observers share the pending failure');
    assert.equal(warnings(first), 1); assert.equal(warnings(second), 1);
    clock.now = 1000 + age;
    const later = make(a); assert.equal(await invoke(a, later), 0);
    assert.equal(reads, age < 10_000 ? 1 : 3, `failure=${failure}, completion age=${age}`);
    assert.equal(warnings(later), age < 10_000 ? 1 : 0);
    if (age >= 10_000) assert.match(later.ports.stderr.text, /formal TTL maintenance/);
    assert.equal(posts, 3, 'each ordinary lint is submitted once'); assert.equal(timers.active.size, 0);
    assert.equal(first.subscriptions.size + second.subscriptions.size + later.subscriptions.size, 0);
  }
});

test('formal cache isolation: all 2 authenticated owners x 3 exact origins, then all six reused', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (entry, runtime) => runtime.normal(entry)), other = await fakeRuntime(t, (entry, runtime) => runtime.normal(entry));
  const clock = { now: 0 }; let reads = 0;
  const transport = (url, init) => {
    if (new URL(url).pathname !== '/v1/capacity') return fetch(String(url).replace('localhost', '127.0.0.1'), init);
    reads++; return Promise.resolve(new Response('<html>unclear</html>', { status: 200 }));
  };
  const origins = [fake.origin, other.origin, fake.origin.replace('127.0.0.1', 'localhost')];
  for (let pass = 0; pass < 2; pass++) for (const owner of ['owner-a 4242', 'owner-b 4243']) for (const origin of origins) {
    const made = caller(setup, origin, clock, { fetch: transport }, owner);
    assert.equal(await invoke(setup, made), 0); assert.equal(warnings(made), 1);
    assert.equal(made.subscriptions.size, 0);
    if (pass === 1) assert.equal(reads, 6, 'a cache hit cannot cross an owner or exact origin');
  }
  assert.equal(reads, 6);
});

test('formal observers: every deadline 2147483646..2147483648 x first observer 0..1 x last ending (18 worlds)', { timeout: 120_000 }, async t => {
  const a = harbor(t), b = harbor(t), fake = await fakeRuntime(t, (entry, runtime) => runtime.normal(entry));
  for (const deadline of integers(2_147_483_646, 2_147_483_648)) for (const firstEnd of [0, 1]) for (const ending of ['interrupt', 'deadline', 'complete']) {
    // The public option is minutes and may represent a fractional millisecond.
    // Native epoch clocks/records use integer milliseconds: enumerate the last
    // integer clock tick before that value, then the first tick at/after it.
    const firstExpiredTick = Math.ceil((deadline / 60_000) * 60_000);
    const clock = { now: 0 }, timers = clockTimers(clock), release = deferred(); let reads = 0, posts = 0, sharedSignal, transportEnded = false;
    const transport = async (url, init) => {
      if (new URL(url).pathname !== '/v1/capacity') { posts++; return fetch(url, init); }
      reads++;
      if (reads > 1) return Response.json({ maintenance: null });
      sharedSignal = init.signal;
      try {
        await Promise.race([release.promise, new Promise((done, reject) => init.signal.addEventListener('abort', () => reject(Object.assign(Error('observer cancellation'), { name: 'AbortError' })), { once: true }))]);
        return Response.json({ maintenance: null });
      } finally { transportEnded = true; }
    };
    const owner = `observer-${deadline}-${firstEnd}-${ending} 4242`;
    const made = [a, b].map(setup => caller(setup, fake.origin, clock, { fetch: transport, timers: timers.port }, owner));
    const done = [false, false], pending = [invoke(a, made[0], deadline).finally(() => done[0] = true)];
    await until(() => reads === 1);
    pending.push(invoke(b, made[1], deadline).finally(() => done[1] = true));
    await until(() => timers.delays.filter(ms => ms !== 5000).length === 2);
    try {
      assert.deepEqual(done, [false, false]); assert.equal(reads, 1); assert.equal(posts, 0);
      made[firstEnd].clock.interrupt(); await until(() => done[firstEnd]);
      assert.equal(await pending[firstEnd], 5); assert.equal(sharedSignal.aborted, false, 'another observer still owns use of the pending read');
      const last = 1 - firstEnd;
      // Completion needs ordinary transport budget for the subsequent lint;
      // only the still-pending branches exercise the final integer clock tick.
      await timers.resume(ending === 'complete' ? 60_000 : firstExpiredTick - 1);
      assert.equal(done[last], false, 'native timer boundary must not shorten the absolute deadline');
      assert.ok(timers.delays.every(ms => ms > 0 && ms <= 60_000), 'every scheduled observer/heartbeat interval fits the safe positive range');
      assert.equal(timers.delays.at(-1), ending === 'complete' ? 60_000 : 1, 'the remaining observer wait is preserved');
      assert.equal(reads, 1); assert.equal(posts, 0);
      if (ending === 'interrupt') made[last].clock.interrupt();
      else if (ending === 'deadline') await timers.resume(firstExpiredTick);
      else release.resolve();
      assert.equal(await pending[last], ending === 'complete' ? 0 : 5);
      assert.equal(sharedSignal.aborted, ending !== 'complete', 'only an unfinished read without another observer is cancelled');
      await until(() => transportEnded);
      assert.equal(posts, ending === 'complete' ? 1 : 0); assert.equal(warnings(made[0]) + warnings(made[1]), 0);
      assert.equal(timers.active.size, 0); assert.equal(made[0].subscriptions.size + made[1].subscriptions.size, 0);
      const next = caller(a, fake.origin, clock, { fetch: transport, timers: timers.port }, owner);
      assert.equal(await invoke(a, next), 0);
      assert.equal(reads, ending === 'complete' ? 1 : 2, 'a completed shared outcome survives, but cancellation is never cached as unclear');
      assert.equal(warnings(next), 0); assert.equal(timers.active.size, 0);
    } finally {
      made[0].clock.interrupt(); made[1].clock.interrupt(); release.resolve(); await Promise.all(pending);
    }
  }
});
