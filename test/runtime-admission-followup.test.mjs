import test from 'node:test';
import assert from 'node:assert/strict';
import { randomUUID } from 'node:crypto';
import { join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { acquireRuntimeSlot, releaseRuntimeSlot } from '../src/runtime-slots.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

const flush = () => new Promise(done => setImmediate(done));
const deferred = () => { let resolve; const promise = new Promise(done => resolve = done); return { promise, resolve }; };
async function until(predicate) {
  let expired = false;
  const timer = setTimeout(() => expired = true, 30_000);
  try {
    while (!predicate() && !expired) await flush();
    assert.equal(!!predicate(), true, 'causal boundary was not reached');
  } finally { clearTimeout(timer); }
}
function memory(clock) {
  const records = new Map(), times = new Map();
  return { records, times, files: {
    listRecords: () => ({ jobs: [...records.values()].filter(row => row.state).map(row => structuredClone(row)) }),
    exclusiveCreate: (path, row) => { if (records.has(path)) return false; records.set(path, structuredClone(row)); times.set(path, clock.now); return true; },
    writeAtomic: (path, row) => { records.set(path, structuredClone(row)); times.set(path, clock.now); },
    unlink: path => { records.delete(path); times.delete(path); },
    modifiedAt: path => times.get(path) ?? null,
    touch: path => { if (!records.has(path)) return false; times.set(path, clock.now); return true; },
  } };
}
function timers(clock) {
  const active = new Set(), delays = [];
  return { active, delays, port: {
    setInterval: (fn, ms) => { delays.push(ms); const timer = { fn, ms, next: clock.now + ms }; active.add(timer); return timer; },
    clearInterval: timer => active.delete(timer),
  }, advance: async target => {
    for (;;) {
      const timer = [...active].filter(t => t.next <= target).sort((a,b) => a.next-b.next)[0];
      if (!timer) break;
      clock.now = timer.next; timer.next += timer.ms; timer.fn(); await flush();
    }
    clock.now = target; await flush();
  } };
}
const make = (setup, fake, extra = {}) => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, extra);
const invoke = (setup, made, kind = 'lint', options = {}) => kind === 'try'
  ? runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true, ...options } }, made.ports)
  : runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true, ...(kind === 'lint' ? { '--lint': true } : {}), ...options } }, made.ports);
const warningCount = made => (made.ports.stderr.text.match(/Warning: interpreter capacity/g) ?? []).length;

test('FOLLOWUP own waiting ticket survives a 61000ms clock jump before heartbeat, preserving order and paid leases', async () => {
  const clock = { now: 100_000 }, mem = memory(clock), timer = timers(clock);
  const origin = `https://${randomUUID()}.example`, directory = join('/virtual', 'slots', new URL(origin).host);
  const path = id => join(directory, `${id}.json`);
  const paid = { id: 'held', state: 'active', pid: 42, kind: 'check', started_at: clock.now, request_ids: ['uncertain-paid'] };
  mem.records.set(path('held'), paid); mem.times.set(path('held'), clock.now);
  mem.records.set(path('abandoned'), { ...paid, id: 'abandoned', state: 'waiting', started_at: 1, request_ids: [] }); mem.times.set(path('abandoned'), 0);
  let sleeps = 0, reads = 0;
  const ports = { files: mem.files, now: () => clock.now, pid: 43, isAlive: () => true, timers: timer.port,
    randomUUID: () => 'mine', random: () => 0, onInterrupt: () => () => {},
    readRun: async id => { assert.equal(id, 'uncertain-paid'); reads++; return 'unknown'; },
    sleep: async () => {
      sleeps++;
      const mine = mem.records.get(path('mine'));
      assert.equal(mine?.id, 'mine', 'ongoing acquisition must never reclaim its own ticket');
      assert.equal(mine.started_at, 100_000); assert.equal(mem.records.has(path('abandoned')), false);
      if (sleeps === 1) {
        clock.now += 61_000;
        mem.records.set(path('later'), { ...mine, id: 'later', pid: 44, started_at: clock.now }); mem.times.set(path('later'), clock.now);
      } else {
        assert.deepEqual(mem.records.get(path('held')), paid, 'clock jump supplies no paid completion evidence');
        assert.deepEqual([...mem.records.values()].filter(r => r.state === 'waiting').sort((a,b) => a.started_at-b.started_at).map(r => r.id), ['mine', 'later']);
        mem.records.delete(path('held')); mem.times.delete(path('held'));
      }
    },
  };
  const lease = await acquireRuntimeSlot({ stateDir: '/virtual', origin, limit: 1, kind: 'check', deadline: 200_000 }, ports);
  assert.equal(lease?.id, 'mine'); assert.equal(sleeps, 2); assert.equal(reads, 1);
  await releaseRuntimeSlot(lease, { ended: true }, ports); assert.equal(timer.active.size, 0);
  assert.deepEqual([...mem.records.values()].map(r => r.id), ['later']);
});

for (const kind of ['check', 'lint', 'try']) for (const boundary of ['admitted', 'recording']) test(`FOLLOWUP interrupt ${kind} at ${boundary}: stopped-before-sending, no new POST, cleanup`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e,f) => e.command === 'try' ? { status: 200, json: f.tryJob(e.request.requestId) } : f.normal(e));
  const made = make(setup, fake), mem = memory(made.clock); made.ports.slotFiles = mem.files;
  const directory = join(setup.state, 'slots', encodeURIComponent(new URL(fake.origin).host));
  const prior = { id: 'earlier-uncertain', state: 'active', pid: 99, kind: 'check', started_at: made.clock.now, request_ids: ['original-paid-id'] };
  const priorPath = join(directory, `${prior.id}.json`); mem.records.set(priorPath, structuredClone(prior)); mem.times.set(priorPath, made.clock.now);
  made.ports.isAlive = () => true;
  made.ports.env.PDD_MAX_JOBS = '4';
  const targetKind = kind === 'lint' ? 'lint' : kind;
  let interrupted = false, targetPath, beforePosts;
  const write = mem.files.writeAtomic;
  mem.files.writeAtomic = (path, row) => {
    write(path, row);
    if (row.kind !== targetKind || interrupted || (boundary === 'admitted' ? row.state !== 'active' || row.request_ids.length : !row.request_ids.length)) return;
    interrupted = true; targetPath = path; beforePosts = fake.posts.length; made.clock.interrupt();
  };
  const code = await invoke(setup, made, kind);
  assert.equal(interrupted, true); assert.equal(code, kind === 'check' ? 3 : kind === 'lint' ? 5 : 3);
  assert.equal(fake.posts.length, beforePosts, 'the synchronized signal forbids the next POST');
  assert.match(made.ports.stdout.text + made.ports.stderr.text, /Stopped before sending\./);
  assert.equal(mem.records.has(targetPath), false); assert.deepEqual([...mem.records.values()].filter(r => r.state), [prior], 'earlier uncertain dispatch keeps its lease and exact IDs');
  assert.equal(warningCount(made), 0);
});

for (const outcome of ['html', '405', '500', 'read-failure', 'timeout', 'unreachable']) test(`FOLLOWUP unclear ${outcome} coalesces and caches until completion+10s; refresh discovers maintenance`, async t => {
  const a = harbor(t), b = harbor(t), fake = await fakeRuntime(t, (e,f) => {
    if (maintenance) assert.ok(clock.now >= maintenanceEnd, 'refresh must hold submissions until maintenance clears');
    return f.normal(e);
  });
  const clock = { now: 100_000 }, release = deferred(); let reads = 0, maintenance = false, maintenanceEnd;
  const fetchPort = async (url, init) => {
    if (new URL(url).pathname !== '/v1/capacity') return fetch(url, init);
    reads++;
    if (reads === 1) {
      await release.promise;
      if (outcome === 'timeout') throw Object.assign(Error('transport timeout'), { name: 'AbortError' });
      if (outcome === 'unreachable') throw Object.assign(Error('no route'), { cause: { code: 'ECONNREFUSED' } });
      if (outcome === 'read-failure') return { text: async () => { throw Error('read failed'); } };
      return new Response(outcome === 'html' ? '<html>proxy</html>' : '{}', { status: outcome === 'html' ? 200 : Number(outcome) });
    }
    return Response.json({ maintenance: clock.now < maintenanceEnd ? { until: new Date(maintenanceEnd).toISOString(), reason: 'TTL maintenance' } : null });
  };
  const caller = setup => make(setup, fake, { fetch: fetchPort, now: () => clock.now, sleep: async ms => { clock.now += ms; await flush(); } });
  const first = caller(a), second = caller(b), p = invoke(a, first), q = invoke(b, second);
  await until(() => reads === 1); clock.now = 110_000; release.resolve();
  assert.deepEqual(await Promise.all([p,q]), [0,0]); assert.equal(reads, 1);
  assert.equal(warningCount(first), 1); assert.equal(warningCount(second), 1);
  clock.now = 119_999; const cached = caller(a); assert.equal(await invoke(a, cached), 0); assert.equal(reads, 1); assert.equal(warningCount(cached), 1);
  clock.now = 120_000; maintenance = true; maintenanceEnd = 127_000;
  const fresh = caller(a); assert.equal(await invoke(a, fresh), 0); assert.equal(reads, 3); assert.equal(clock.now, maintenanceEnd);
  assert.match(fresh.ports.stderr.text, /TTL maintenance/); assert.equal(warningCount(fresh), 0);
});

for (const mode of ['complete', 'deadline', 'interrupt', 'initiator-interrupt']) test(`FOLLOWUP capacity observer ${mode}: positive bounded chunks, independent shared GET and cleanup`, async t => {
  const a = harbor(t), b = harbor(t), fake = await fakeRuntime(t, (e,f) => f.normal(e));
  const release = deferred(); let reads = 0, sharedSignal;
  const clock = { now: 0 }, timer = timers(clock), options = { '--timeout': 43_200 };
  const transport = async (url, init) => {
    if (new URL(url).pathname !== '/v1/capacity') return fetch(url, init);
    reads++; sharedSignal = init.signal; await release.promise; return Response.json({ maintenance: null });
  };
  const caller = setup => make(setup, fake, { timers: timer.port, now: () => clock.now, fetch: transport });
  const first = caller(a), second = caller(b); let firstDone = false, secondDone = false;
  const p = invoke(a, first, 'lint', options).finally(() => firstDone = true);
  await until(() => reads === 1);
  const q = invoke(b, second, 'lint', mode === 'deadline' ? { '--timeout': 130_001 / 60_000 } : options).finally(() => secondDone = true);
  await until(() => timer.delays.filter(ms => ms !== 5000).length >= 2 || firstDone || secondDone);
  try {
    assert.equal(secondDone, false, 'far-future observer must not overflow into immediate expiry');
    const observerDelays = () => timer.delays.filter(ms => ms !== 5000);
    assert.ok(observerDelays().length >= 2, 'both observers schedule independent deadline timers');
    for (const at of [60_000, 120_000, 130_000]) { await timer.advance(at); assert.equal(secondDone, false); assert.equal(firstDone, false); }
    assert.ok(observerDelays().every(ms => ms > 0 && ms <= 60_000));
    if (mode === 'deadline') await timer.advance(130_001);
    else if (mode === 'interrupt') second.clock.interrupt();
    else if (mode === 'initiator-interrupt') first.clock.interrupt();
    if (mode !== 'complete') {
      await until(() => mode === 'initiator-interrupt' ? firstDone : secondDone);
      assert.equal(sharedSignal.aborted, false, 'one observer ending must not abort the shared transport');
      assert.equal(mode === 'initiator-interrupt' ? secondDone : firstDone, false);
      assert.equal(fake.posts.length, 0); assert.equal(reads, 1);
      assert.equal(warningCount(first) + warningCount(second), 0, 'ending an observer is not an unclear reply');
    }
    release.resolve();
    const result = await Promise.all([p,q]);
    assert.deepEqual(result, mode === 'complete' ? [0,0] : mode === 'initiator-interrupt' ? [5,0] : [0,5]);
    assert.equal(reads, 1); assert.equal(fake.posts.length, mode === 'complete' ? 2 : 1);
    assert.equal(warningCount(first) + warningCount(second), 0); assert.equal(timer.active.size, 0);
    const cached = caller(a); assert.equal(await invoke(a, cached), 0); assert.equal(reads, 1);
  } finally { clock.now = 2_592_000_001; release.resolve(); await Promise.all([p,q]); }
});

test('FOLLOWUP cached unclear outcomes isolate authenticated owner and exact origin including port', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e,f) => f.normal(e));
  let reads = 0;
  const fetchPort = async (url, init) => {
    if (new URL(url).pathname !== '/v1/capacity') return fetch(url, init);
    reads++; return new Response('<html>unclear</html>', { status: 200 });
  };
  const a = make(setup, fake, { fetch: fetchPort }); assert.equal(await invoke(setup, a, 'check'), 0); assert.equal(reads, 1); assert.equal(warningCount(a), 1);
  const same = make(setup, fake, { fetch: fetchPort }); assert.equal(await invoke(setup, same), 0); assert.equal(reads, 1); assert.equal(warningCount(same), 1);
  const owner = make(setup, fake, { fetch: fetchPort, gh: args => args[0] === 'auth' ? { status: 0, stdout: 'other-token' } : { status: 0, stdout: 'other 55' } });
  assert.equal(await invoke(setup, owner), 0); assert.equal(reads, 2); assert.equal(warningCount(owner), 1);
  const port = await fakeRuntime(t, (e,f) => f.normal(e)), elsewhere = make(setup, port, { fetch: fetchPort });
  assert.equal(await invoke(setup, elsewhere), 0); assert.equal(reads, 3);
  const host = make(setup, fake, { fetch: (url, init) => fetchPort(new URL(String(url).replace('localhost', '127.0.0.1')), init) });
  host.ports.env.PDD_RUNTIME_URL = fake.origin.replace('127.0.0.1', 'localhost');
  assert.equal(await invoke(setup, host), 0); assert.equal(reads, 4);
  assert.equal(warningCount(elsewhere), 1); assert.equal(warningCount(host), 1);
});


test('FOLLOWUP sole interrupted capacity observer cancels unshared transport and does not cache cancellation as unclear', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e,f) => f.normal(e));
  const clock = { now: 0 }, timer = timers(clock); let reads = 0, transportSignal, transportEnded = false;
  const transport = async (url, init) => {
    if (new URL(url).pathname !== '/v1/capacity') return fetch(url, init);
    reads++;
    if (reads > 1) return Response.json({ maintenance: null });
    transportSignal = init.signal;
    try {
      return await new Promise((done, reject) => init.signal.addEventListener('abort', () => reject(Object.assign(Error('aborted'), { name: 'AbortError' })), { once: true }));
    } finally { transportEnded = true; }
  };
  const made = make(setup, fake, { now: () => clock.now, timers: timer.port, fetch: transport });
  const subscriptions = new Set(), subscribe = made.ports.onInterrupt;
  made.ports.onInterrupt = handler => { subscriptions.add(handler); const off = subscribe(handler); return () => { subscriptions.delete(handler); off(); }; };
  const pending = invoke(setup, made);
  await until(() => transportSignal); made.clock.interrupt();
  assert.equal(await pending, 5); await until(() => transportEnded);
  assert.equal(transportSignal.aborted, true); assert.equal(fake.posts.length, 0); assert.equal(warningCount(made), 0);
  assert.match(made.ports.stderr.text, /Stopped before sending\./); assert.equal(timer.active.size, 0); assert.equal(subscriptions.size, 0);
  const next = make(setup, fake, { now: () => clock.now, fetch: transport });
  assert.equal(await invoke(setup, next), 0); assert.equal(reads, 2); assert.equal(warningCount(next), 0);
});
