import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, statSync, utimesSync, unlinkSync, existsSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { acquireRuntimeSlot, recordRuntimeRequest, releaseRuntimeSlot } from '../src/runtime-slots.mjs';

// Independent oracle: Source0088 runtime-local-slots Rules to check and its
// runtime-slots owner prompt, including the approved ownership follow-up.
// Every member of each finite product runs against native temporary files.
// Manual timer/interrupt ports delimit schedules; this is no universal proof
// of filesystem interleavings, process signals, crash consistency or GC.
const changes = [
  ['combined same-ID/PID', row => ({ ...row, kind: 'try', started_at: row.started_at - 1, request_ids: ['foreign-paid'] })],
  ['id', row => ({ ...row, id: 'foreign' })],
  ['pid', row => ({ ...row, pid: row.pid + 1 })],
  ['state', row => ({ ...row, state: 'waiting' })],
  ['kind', row => ({ ...row, kind: 'lint' })],
  ['started_at', row => ({ ...row, started_at: row.started_at - 1 })],
  ['request append', row => ({ ...row, request_ids: [...row.request_ids, 'foreign-paid'] })],
  ['request removal', row => ({ ...row, request_ids: row.request_ids.slice(1) })],
  ['request order', row => ({ ...row, request_ids: [...row.request_ids].reverse() })],
];
const bits = [false, true];
const flush = () => new Promise(done => setImmediate(done));
const read = path => JSON.parse(readFileSync(path, 'utf8'));
function put(path, row, now) {
  writeFileSync(path, `${JSON.stringify(row)}\n`, { mode: 0o600 });
  utimesSync(path, new Date(now), new Date(now));
}
function observed(path) { return { bytes: readFileSync(path, 'utf8'), modified: statSync(path).mtimeMs }; }
function unchanged(path, before, label) {
  assert.equal(existsSync(path), true, `${label}: foreign file must remain present`);
  assert.deepEqual(observed(path), before, label);
}
async function finiteFailure(action, label) {
  await assert.rejects(action, error => error.code === 'local-state-unavailable'
    && !error.message.includes('\n') && error.message.length < 1000, label);
}
// An invalid native row (the changed id no longer matches its filename) may
// report the existing read error during cleanup; that still must preserve it.
async function cleanup(lease, ports) {
  try { await releaseRuntimeSlot(lease, { ended: true }, ports); }
  catch (error) { assert.equal(error.code, 'local-state-unavailable'); }
}
function world() {
  const stateDir = mkdtempSync(join(tmpdir(), 'pdd-reservation-formal-'));
  // Probe caching is intentionally process-wide, so independent worlds also
  // need distinct exact origins rather than borrowing another world's read.
  const origin = `https://${stateDir.split('/').at(-1)}.invalid:9443`;
  const directory = join(stateDir, 'slots', encodeURIComponent(new URL(origin).host));
  mkdirSync(directory, { recursive: true });
  let now = 3_000_000, identity = 'original';
  const intervals = new Set(), listeners = new Set();
  const w = { stateDir, origin, directory, intervals, listeners };
  const ports = {
    now: () => now, randomUUID: () => identity, random: () => 0,
    isAlive: () => true, interrupted: () => false,
    onInterrupt: fn => { listeners.add(fn); return () => listeners.delete(fn); },
    timers: {
      setInterval(fn, ms) { const handle = { fn, ms }; intervals.add(handle); w.onInterval?.(); return handle; },
      clearInterval: handle => intervals.delete(handle),
    },
    sleep: async () => { throw Error('Unexpected wait in finite ownership world'); },
  };
  Object.assign(w, {
    ports, file: join(directory, 'original.json'),
    options: { stateDir, origin, kind: 'check', limit: 1 },
    advance: ms => { now += ms; }, setNow: value => { now = value; },
    setIdentity: value => { identity = value; },
    acquire: extra => acquireRuntimeSlot({ ...w.options, ...extra }, ports),
    async pulse() { for (const { fn } of [...intervals]) fn(); await flush(); },
    async interrupt() { for (const fn of [...listeners]) fn(); await flush(); },
    clean() { assert.equal(intervals.size, 0, 'all owner timers stop'); assert.equal(listeners.size, 0, 'all owner listeners stop'); },
    dispose: () => rmSync(stateDir, { recursive: true, force: true }),
  });
  return w;
}

test('formal known predecessor: 9 field changes x 3 operations x 2 exact-reference histories (54 worlds)', async () => {
  for (const [field, replace] of changes) for (const operation of ['append', 'duplicate', 'release']) for (const stopped of bits) {
    const w = world(), label = `${field}/${operation}/stopped=${stopped}`;
    let lease;
    try {
      lease = await w.acquire();
      assert.ok(lease);
      for (const id of ['paid-one', 'paid-two']) assert.equal(await recordRuntimeRequest(lease, id, { ...w.ports }), true);
      if (stopped) { await releaseRuntimeSlot(lease, { ended: false }, w.ports); w.clean(); }
      put(w.file, replace(read(w.file)), w.ports.now() - 17_000);
      const before = observed(w.file);
      if (operation === 'release') await cleanup(lease, w.ports);
      else await finiteFailure(() => recordRuntimeRequest(lease, operation === 'append' ? 'new-paid' : 'paid-one', { ...w.ports }), label);
      unchanged(w.file, before, `${label}: no write/delete/freshness adoption`);
      w.advance(5_000); await w.pulse();
      unchanged(w.file, before, `${label}: no later heartbeat adoption`);
      await releaseRuntimeSlot(lease, { ended: false }, w.ports);
      await cleanup(lease, w.ports);
      unchanged(w.file, before, `${label}: cleanup retains foreign predecessor`);
      w.clean();
    } finally { if (lease) await releaseRuntimeSlot(lease, { ended: false }, w.ports); w.dispose(); }
  }
});

test('formal valid updates: 6 request sequences x immediate/waiting promotion (12 worlds)', async () => {
  const sequences = [[], ['a'], ['a', 'a'], ['a', 'b'], ['b', 'a', 'b'], ['c', 'a', 'c', 'b', 'a']];
  for (const sequence of sequences) for (const waiting of bits) {
    const w = world(); let lease, ticket;
    const holder = join(w.directory, 'holder.json');
    try {
      if (waiting) {
        put(holder, { id: 'holder', state: 'active', pid: process.pid, kind: 'check', started_at: w.ports.now(), request_ids: [] }, w.ports.now());
        w.ports.sleep = async () => {
          assert.equal(ticket, undefined, 'only one scheduled wait is needed');
          ticket = read(w.file); w.advance(5_000); await w.pulse();
          assert.equal(statSync(w.file).mtimeMs, w.ports.now(), 'owned waiting ticket refreshes');
          unlinkSync(holder);
        };
      }
      lease = await w.acquire();
      assert.deepEqual(Object.keys(lease).sort(), ['directory', 'id']);
      if (waiting) assert.deepEqual(read(w.file), { ...ticket, state: 'active', started_at: w.ports.now() });
      const expected = [];
      for (const id of sequence) {
        // Each call resolves a separate native file adapter. A plain copied
        // reference still respects the live path owner's known predecessor.
        assert.equal(await recordRuntimeRequest({ ...lease }, id, { ...w.ports }), true);
        if (!expected.includes(id)) expected.push(id);
        assert.deepEqual(read(w.file).request_ids, expected);
        w.advance(5_000); await w.pulse();
        assert.equal(statSync(w.file).mtimeMs, w.ports.now(), 'legitimate cross-port write advances the live heartbeat');
        assert.equal(w.intervals.size, 1);
      }
      await releaseRuntimeSlot(lease, { ended: false }, w.ports); w.clean();
      const before = observed(w.file); w.advance(60_000); await w.pulse(); unchanged(w.file, before, 'stopped owner stays stopped');
      if (expected.length) {
        const reads = [], deadline = w.ports.now() + 100;
        w.setIdentity('competitor');
        w.ports.readRun = async id => { reads.push(id); return 'unknown'; };
        w.ports.sleep = async () => w.setNow(deadline);
        assert.equal(await w.acquire({ deadline }), null, 'unknown paid lease stays occupied');
        assert.deepEqual(reads, expected); unchanged(w.file, before, 'expiry cannot establish completion'); w.clean();
      }
      await cleanup(lease, w.ports); assert.equal(existsSync(w.file), false, 'same returned reference still releases its own ended lease');
    } finally { if (lease) await releaseRuntimeSlot(lease, { ended: false }, w.ports); w.dispose(); }
  }
});

test('formal newer path owner: live/stopped old reference x append/duplicate/release (6 worlds)', async () => {
  for (const stopped of bits) for (const operation of ['append', 'duplicate', 'release']) {
    const w = world(); let old, newer;
    try {
      old = await w.acquire(); await recordRuntimeRequest(old, 'old-paid', w.ports);
      if (stopped) await releaseRuntimeSlot(old, { ended: false }, w.ports);
      unlinkSync(w.file); w.advance(1);
      newer = await w.acquire(); await recordRuntimeRequest(newer, 'new-paid', w.ports);
      const before = observed(w.file);
      if (operation === 'release') await cleanup(old, w.ports);
      else await finiteFailure(() => recordRuntimeRequest(old, operation === 'append' ? 'old-extra' : 'new-paid', w.ports), `${stopped}/${operation}`);
      unchanged(w.file, before, 'old exact reference cannot adopt/delete newer owner');
      w.advance(5_000); await w.pulse();
      assert.equal(statSync(w.file).mtimeMs, w.ports.now(), 'old cleanup cannot stop newer owner refresh');
      assert.deepEqual(read(w.file).request_ids, ['new-paid']);
      assert.equal(w.intervals.size, 1);
      await cleanup(newer, w.ports); await releaseRuntimeSlot(old, { ended: false }, w.ports); w.clean();
    } finally {
      if (old) await releaseRuntimeSlot(old, { ended: false }, w.ports);
      if (newer) await releaseRuntimeSlot(newer, { ended: false }, w.ports);
      w.dispose();
    }
  }
});

test('formal legacy reference: 3 request orders x both release outcomes (6 worlds)', async () => {
  for (const sequence of [['a', 'a'], ['a', 'b', 'a'], ['b', 'a', 'b']]) for (const ended of bits) {
    const w = world(), legacy = { id: 'original', directory: w.directory };
    try {
      put(w.file, { id: legacy.id, state: 'active', pid: process.pid, kind: 'try', started_at: w.ports.now(), request_ids: [] }, w.ports.now());
      const expected = [];
      for (const id of sequence) {
        assert.equal(await recordRuntimeRequest(legacy, id, { ...w.ports }), true, 'no local acquisition is required');
        if (!expected.includes(id)) expected.push(id);
        assert.deepEqual(read(w.file).request_ids, expected);
      }
      const before = observed(w.file); await releaseRuntimeSlot(legacy, { ended }, w.ports);
      if (ended) assert.equal(existsSync(w.file), false); else unchanged(w.file, before, 'unknown legacy paid lease retained');
      w.clean();
    } finally { w.dispose(); }
  }
});

test('formal foreign interrupt cleanup: live/stopped heartbeat at common handler boundary (2 worlds)', async () => {
  // The injected subscription is the declared common signal cleanup boundary;
  // separate child-process tests establish actual OS signal delivery.
  for (const pulseFirst of bits) {
    const w = world(); let lease;
    try {
      lease = await w.acquire(); await recordRuntimeRequest(lease, 'paid-one', w.ports);
      put(w.file, { ...read(w.file), kind: 'try' }, w.ports.now() - 17_000);
      const before = observed(w.file);
      if (pulseFirst) await w.pulse();
      await w.interrupt(); await releaseRuntimeSlot(lease, { ended: false }, w.ports);
      unchanged(w.file, before, `pulse first=${pulseFirst}: no foreign cleanup/refresh`); w.clean();
    } finally { if (lease) await releaseRuntimeSlot(lease, { ended: false }, w.ports); w.dispose(); }
  }
});

test('formal held claim identity: 4 claim field changes x admission/registration (8 worlds)', async () => {
  const claimChanges = [
    ['id', row => ({ ...row, id: `${row.id}-foreign` })],
    ['pid', row => ({ ...row, pid: row.pid + 1 })],
    ['number', row => ({ ...row, number: row.number + 1 })],
    ['choosing', row => ({ ...row, choosing: true })],
  ];
  for (const [field, replace] of claimChanges) for (const operation of ['admission', 'registration']) {
    const w = world(); let lease, foreignPath, before;
    try {
      if (operation === 'registration') { lease = await w.acquire(); await recordRuntimeRequest(lease, 'paid-one', w.ports); }
      const activeBefore = operation === 'registration' ? observed(w.file) : null;
      w.onInterval = () => {
        const claims = readdirSync(w.directory).filter(name => /^\.claim-.*\.lock$/.test(name));
        if (!claims.length || foreignPath) return;
        assert.equal(claims.length, 1);
        foreignPath = join(w.directory, claims[0]);
        put(foreignPath, replace(read(foreignPath)), w.ports.now()); before = observed(foreignPath);
      };
      if (operation === 'registration') {
        const result = await recordRuntimeRequest(lease, 'new-paid', { ...w.ports, deadline: w.ports.now() + 100 });
        assert.equal(result, false, `${field}: lost claim cannot authorize registration`);
        unchanged(w.file, activeBefore, 'lost claim cannot append a request');
      } else {
        const deadline = w.ports.now() + 100;
        w.ports.sleep = async () => w.setNow(deadline);
        lease = await w.acquire({ deadline });
        assert.equal(lease, null, `${field}: lost claim cannot authorize promotion`);
        assert.equal(existsSync(w.file), false, 'ended own waiting ticket cleans up');
      }
      assert.ok(foreignPath, 'replacement occurs at the held native claim boundary');
      unchanged(foreignPath, before, 'old claim cleanup preserves foreign identity');
      if (lease) await releaseRuntimeSlot(lease, { ended: false }, w.ports);
      w.clean();
    } finally { if (lease) await releaseRuntimeSlot(lease, { ended: false }, w.ports); w.dispose(); }
  }
});
