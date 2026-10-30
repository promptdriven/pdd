import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, readdirSync, statSync, unlinkSync, utimesSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { acquireRuntimeSlot, recordRuntimeRequest, releaseRuntimeSlot } from '../src/runtime-slots.mjs';
import { temp } from './runtime-fake.mjs';

const flush = () => new Promise(done => setImmediate(done));
function world(t) {
  const stateDir = join(temp(t), 'state'), origin = 'https://registration-ownership.example';
  const timers = new Set(), listeners = new Set();
  const w = { now: Date.now(), timers, listeners, options: { stateDir, origin, kind: 'check', limit: 1 } };
  w.ports = {
    now: () => w.now,
    onInterrupt: handler => { listeners.add(handler); return () => listeners.delete(handler); },
    timers: { setInterval: fn => { const timer = { fn }; timers.add(timer); return timer; }, clearInterval: timer => timers.delete(timer) },
  };
  w.acquire = () => acquireRuntimeSlot(w.options, w.ports);
  w.file = reservation => join(reservation.directory, `${reservation.id}.json`);
  w.read = reservation => JSON.parse(readFileSync(w.file(reservation), 'utf8'));
  w.replace = (reservation, changes) => {
    const replacement = { ...w.read(reservation), ...changes }, file = w.file(reservation);
    writeFileSync(file, `${JSON.stringify(replacement)}\n`);
    const old = new Date(w.now - 60_001); utimesSync(file, old, old);
    return { replacement, bytes: readFileSync(file, 'utf8'), modified: statSync(file).mtimeMs };
  };
  w.tick = async () => { w.now += 5000; for (const { fn } of [...timers]) fn(); await flush(); };
  w.signal = async () => { for (const handler of [...listeners]) handler(); await flush(); };
  w.assertPreserved = (reservation, before) => {
    assert.equal(existsSync(w.file(reservation)), true, 'foreign replacement stays present');
    assert.equal(readFileSync(w.file(reservation), 'utf8'), before.bytes, 'foreign bytes remain unchanged');
    assert.equal(statSync(w.file(reservation)).mtimeMs, before.modified, 'foreign record is never refreshed');
  };
  return w;
}

const replacements = {
  kind: row => ({ kind: 'lint' }),
  started_at: row => ({ started_at: row.started_at - 1 }),
  request_ids: row => ({ request_ids: ['foreign-paid'] }),
  request_order: row => ({ request_ids: [...row.request_ids].reverse() }),
  pid: row => ({ pid: row.pid + 1 }),
  state: row => ({ state: 'waiting' }),
  combined: row => ({ kind: 'lint', started_at: row.started_at - 1, request_ids: ['foreign-paid'] }),
  duplicate: row => ({ request_ids: ['foreign-paid', 'paid-one'] }),
};

for (const [name, changes] of Object.entries(replacements)) test(`registration rejects changed owned predecessor: ${name}`, async t => {
  const w = world(t), reservation = await w.acquire();
  try {
    await recordRuntimeRequest(reservation, 'paid-one', w.ports);
    await recordRuntimeRequest(reservation, 'paid-two', w.ports);
    const before = w.replace(reservation, changes(w.read(reservation)));
    await assert.rejects(recordRuntimeRequest(reservation, name === 'duplicate' ? 'paid-one' : 'old-owner-request', w.ports), error => {
      assert.equal(error.code, 'local-state-unavailable');
      assert.equal(error.message.includes('\n'), false, 'ownership error stays finite');
      return true;
    });
    assert.equal(w.timers.size, 0, 'ownership mismatch stops only the old pulse');
    await w.tick(); w.assertPreserved(reservation, before);
    await releaseRuntimeSlot(reservation, { ended: true }, w.ports);
    w.assertPreserved(reservation, before);
    assert.deepEqual(readdirSync(reservation.directory), [`${reservation.id}.json`], 'claim cleanup completes');
    assert.equal(w.listeners.size, 0);
  } finally { await releaseRuntimeSlot(reservation, { ended: false }, w.ports); }
});

for (const afterStopped of [false, true]) test(`ended true preserves a foreign successor, prior ended false=${afterStopped}`, async t => {
  const w = world(t), reservation = await w.acquire();
  await recordRuntimeRequest(reservation, 'paid-unknown', w.ports);
  if (afterStopped) await releaseRuntimeSlot(reservation, { ended: false }, w.ports);
  const before = w.replace(reservation, { kind: 'try', request_ids: ['other-paid'] });
  await releaseRuntimeSlot(reservation, { ended: true }, w.ports);
  await w.tick(); w.assertPreserved(reservation, before);
  assert.equal(w.timers.size, 0); assert.equal(w.listeners.size, 0);
});

test('old exact reservation cannot adopt or stop a newer owner at the same path', async t => {
  const w = world(t); w.ports.randomUUID = () => 'reused-id';
  const old = await w.acquire();
  await recordRuntimeRequest(old, 'old-paid', w.ports);
  await releaseRuntimeSlot(old, { ended: false }, w.ports);
  unlinkSync(w.file(old)); w.now++;
  const current = await w.acquire();
  try {
    const before = w.read(current);
    await assert.rejects(recordRuntimeRequest(old, 'must-not-adopt', w.ports), { code: 'local-state-unavailable' });
    await releaseRuntimeSlot(old, { ended: true }, w.ports);
    assert.deepEqual(w.read(current), before);
    assert.equal(w.timers.size, 1, 'newer owner keeps its pulse');
    assert.equal(await recordRuntimeRequest(current, 'new-paid', w.ports), true);
    await w.tick();
    assert.equal(statSync(w.file(current)).mtimeMs, w.now, 'newer owner retains native heartbeat identity');
  } finally { await releaseRuntimeSlot(current, { ended: true }, w.ports); }
  assert.equal(w.listeners.size, 0);
});

test('unsent interruption preserves a replaced active reservation', async t => {
  const w = world(t), reservation = await w.acquire();
  const before = w.replace(reservation, { kind: 'lint', request_ids: ['foreign-paid'] });
  await w.signal(); await w.tick(); w.assertPreserved(reservation, before);
  await releaseRuntimeSlot(reservation, { ended: true }, w.ports);
  w.assertPreserved(reservation, before);
  assert.equal(w.timers.size, 0); assert.equal(w.listeners.size, 0);
});

test('valid cross-port append, deduplication and promotion retain ownership; unknown paid lease survives', async t => {
  const w = world(t), reservation = await w.acquire();
  await w.tick(); assert.equal(statSync(w.file(reservation)).mtimeMs, w.now, 'promoted reservation refreshes');
  for (const id of ['paid-one', 'paid-two', 'paid-one']) assert.equal(await recordRuntimeRequest({ ...reservation }, id, w.ports), true);
  assert.deepEqual(w.read(reservation).request_ids, ['paid-one', 'paid-two']);
  await w.tick(); assert.equal(statSync(w.file(reservation)).mtimeMs, w.now, 'separately resolved native ports advance the live owner');
  assert.deepEqual(readdirSync(reservation.directory), [`${reservation.id}.json`], 'claim choosing/number transitions clean up');
  await releaseRuntimeSlot(reservation, { ended: false }, w.ports);
  const before = { bytes: readFileSync(w.file(reservation), 'utf8'), modified: statSync(w.file(reservation)).mtimeMs };
  await w.tick(); w.assertPreserved(reservation, before);
  assert.equal(w.timers.size, 0); assert.equal(w.listeners.size, 0);
  await releaseRuntimeSlot(reservation, { ended: true }, w.ports);
  assert.equal(existsSync(w.file(reservation)), false, 'known unchanged stopped reservation remains releasable');
});

test('legacy saved reservation without a known owner still appends, deduplicates and releases', async t => {
  const w = world(t), directory = join(w.options.stateDir, 'slots', 'registration-ownership.example');
  mkdirSync(directory, { recursive: true });
  const reservation = { id: 'legacy', directory }, row = { id: 'legacy', pid: process.pid, state: 'active', kind: 'try', started_at: w.now, request_ids: ['earlier'] };
  writeFileSync(w.file(reservation), JSON.stringify(row));
  for (const id of ['new', 'new', 'last']) assert.equal(await recordRuntimeRequest(reservation, id, w.ports), true);
  assert.deepEqual(w.read(reservation).request_ids, ['earlier', 'new', 'last']);
  await releaseRuntimeSlot(reservation, { ended: false }, w.ports);
  assert.equal(existsSync(w.file(reservation)), true);
  await releaseRuntimeSlot(reservation, { ended: true }, w.ports);
  assert.equal(existsSync(w.file(reservation)), false); assert.equal(w.listeners.size, 0);
});

for (const signal of [false, true]) for (const operation of ['admission', 'registration']) test(`changed native claim cannot authorize ${operation}; signal=${signal}`, async t => {
  const w = world(t), directory = join(w.options.stateDir, 'slots', 'registration-ownership.example');
  let replace = operation === 'admission', claimFile, claimBytes, claimTime;
  const subscribe = w.ports.onInterrupt;
  w.ports.onInterrupt = handler => {
    const off = subscribe(handler);
    const claim = existsSync(directory) && readdirSync(directory).find(name => name.endsWith('.lock'));
    if (replace && claim && !claimFile) {
      claimFile = join(directory, claim);
      const foreign = { ...JSON.parse(readFileSync(claimFile, 'utf8')), id: 'foreign-claim' };
      claimBytes = `${JSON.stringify(foreign)}\n`; writeFileSync(claimFile, claimBytes);
      claimTime = statSync(claimFile).mtimeMs;
      if (signal) handler();
    }
    return off;
  };
  w.ports.sleep = async () => { w.now += 100; };
  let reservation;
  try {
    if (operation === 'admission') {
      const result = await acquireRuntimeSlot({ ...w.options, deadline: w.now + 50 }, w.ports);
      reservation = result;
      assert.equal(result, null, 'foreign claim cannot authorize promotion');
    } else {
      reservation = await w.acquire(); replace = true;
      const before = w.read(reservation);
      assert.equal(await recordRuntimeRequest(reservation, 'must-not-register', w.ports), false, 'lost claim cannot authorize registration');
      assert.deepEqual(w.read(reservation), before);
    }
    assert.ok(claimFile, 'replacement occurs after native claim publication');
    assert.equal(existsSync(claimFile), true, 'foreign claim stays present after old cleanup');
    assert.equal(readFileSync(claimFile, 'utf8'), claimBytes, 'old claim cleanup preserves successor bytes');
    assert.equal(statSync(claimFile).mtimeMs, claimTime, 'old claim never refreshes successor');
  } finally { if (reservation) await releaseRuntimeSlot(reservation, { ended: true }, w.ports); }
  assert.equal(w.timers.size, 0); assert.equal(w.listeners.size, 0);
});

test('native claim fencing still reclaims an expired other claim', async t => {
  const w = world(t), directory = join(w.options.stateDir, 'slots', 'registration-ownership.example');
  mkdirSync(directory, { recursive: true });
  const abandoned = join(directory, '.claim-abandoned.lock');
  writeFileSync(abandoned, JSON.stringify({ id: 'abandoned', pid: 999, choosing: false, number: 1 }));
  w.ports.isAlive = pid => pid !== 999;
  const reservation = await w.acquire();
  assert.ok(reservation); assert.equal(existsSync(abandoned), false);
  await releaseRuntimeSlot(reservation, { ended: true }, w.ports);
  assert.deepEqual(readdirSync(directory), []);
});
