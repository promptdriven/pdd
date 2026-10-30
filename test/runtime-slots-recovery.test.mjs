import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { mkdirSync, readFileSync, readdirSync, unlinkSync, utimesSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { randomUUID } from 'node:crypto';
import { acquireRuntimeSlot, listRuntimeJobs, recordRuntimeRequest, releaseRuntimeSlot } from '../src/runtime-slots.mjs';
import { temp } from './runtime-fake.mjs';

const flush = () => new Promise(done => setImmediate(done));
const row = (id, extra = {}) => ({ id, state: 'active', pid: 42, kind: 'check', started_at: 100, request_ids: ['paid'], ...extra });
function world() {
  const stateDir = '/virtual/recovery', origin = `https://${randomUUID()}.example`, directory = join(stateDir, 'slots', new URL(origin).host);
  const data = new Map(), modified = new Map(), timers = new Set(), listeners = new Set();
  const w = { now: 100, data, modified, timers, creates: [], touches: [], directory, options: { stateDir, origin, kind: 'check', limit: 1 } };
  w.path = id => join(directory, `${id}.json`);
  w.seed = (record, at = w.now) => { data.set(w.path(record.id), structuredClone(record)); modified.set(w.path(record.id), at); };
  w.files = {
    listRecords: () => ({ jobs: [...data.values()].filter(r => r.state).map(r => structuredClone(r)) }),
    exclusiveCreate: (path, record) => { w.creates.push(structuredClone(record)); if (data.has(path)) return false; data.set(path, structuredClone(record)); modified.set(path, w.now); return true; },
    writeAtomic: (path, record) => { data.set(path, structuredClone(record)); modified.set(path, w.now); },
    modifiedAt: path => modified.get(path) ?? null,
    touch: path => { if (!data.has(path)) return false; modified.set(path, w.now); w.touches.push(path); return true; },
    unlink: path => { data.delete(path); modified.delete(path); },
  };
  w.ports = { files: w.files, now: () => w.now, pid: 43, randomUUID: () => 'original', isAlive: () => true, random: () => 0,
    onInterrupt: fn => { listeners.add(fn); return () => listeners.delete(fn); },
    timers: { setInterval: (fn, ms) => { const t = { fn, ms }; timers.add(t); return t; }, clearInterval: t => timers.delete(t) },
    sleep: async ms => { w.now += ms; },
  };
  w.signal = () => { for (const fn of [...listeners]) fn(); };
  w.tick = async () => { w.now += 5000; for (const { fn } of [...timers]) fn(); await flush(); };
  return w;
}

for (const loss of ['before-inspection', 'before-heartbeat']) test(`pending recovery: ${loss} keeps original identity and resumes refresh`, async () => {
  const w = world(); w.seed(row('holder'));
  let round = 0, original;
  w.ports.sleep = async () => {
    if (round++ === 0) {
      original = structuredClone(w.data.get(w.path('original')));
      w.files.unlink(w.path('original'));
      if (loss === 'before-heartbeat') { await w.tick(); assert.equal(w.timers.size, 0, 'absent heartbeat stops rather than resurrects'); }
    } else {
      assert.deepEqual(w.data.get(w.path('original')), original, 'still-pending wait restores its exact original ticket');
      const before = w.touches.length; await w.tick();
      assert.ok(w.touches.length > before, 'restored wait refreshes again');
      w.files.unlink(w.path('holder'));
    }
  };
  const reservation = await acquireRuntimeSlot({ ...w.options, deadline: 20_000 }, w.ports);
  assert.equal(reservation?.id, 'original');
  assert.equal(w.creates.filter(r => r.state === 'waiting').length, 2, 'one original plus one exclusive restoration');
  await releaseRuntimeSlot(reservation, { ended: true }, w.ports);
  assert.equal(w.data.size, 0); assert.equal(w.timers.size, 0);
});

test('pending recovery: disappearance during inspection is repaired before competing', async () => {
  const w = world(), list = w.files.listRecords; let removed = false;
  w.files.listRecords = () => { if (!removed) { removed = true; w.files.unlink(w.path('original')); } return list(); };
  const lease = await acquireRuntimeSlot({ ...w.options, deadline: 101 }, w.ports);
  assert.equal(lease?.id, 'original', 'missing at first inspection must progress without a timeout');
  await releaseRuntimeSlot(lease, { ended: true }, w.ports); assert.equal(w.timers.size, 0);
});

for (const reason of ['interrupt', 'interrupt-after-heartbeat', 'deadline']) test(`pending recovery: ${reason} wins and preserves another unknown paid lease`, async () => {
  const w = world(); w.seed(row('holder', { started_at: 0 }), -60_000);
  let reads = 0, sleeps = 0; w.ports.readRun = async () => { reads++; return 'unknown'; };
  w.ports.sleep = async () => {
    sleeps++; w.files.unlink(w.path('original'));
    if (reason === 'interrupt-after-heartbeat') await w.tick();
    if (reason.startsWith('interrupt')) w.signal(); else w.now = 200;
  };
  assert.equal(await acquireRuntimeSlot({ ...w.options, deadline: reason === 'interrupt-after-heartbeat' ? 20_000 : 200 }, w.ports), null);
  assert.equal(sleeps, 1, 'interruption is observed even after a missing-file heartbeat stopped');
  assert.equal(w.creates.filter(r => r.state === 'waiting').length, 1, 'no restoration after waiting ends');
  assert.deepEqual([...w.data.values()], [row('holder', { started_at: 0 })]); assert.equal(reads, 1); assert.equal(w.timers.size, 0);
});

for (const state of ['waiting', 'active']) test(`pending recovery: exclusive restoration never overwrites an existing ${state} collision`, async () => {
  const w = world(); w.seed(row('holder'));
  const collision = row('original', { state, pid: 99, started_at: 50, request_ids: state === 'active' ? ['other-paid'] : [] });
  const create = w.files.exclusiveCreate; let collided = false;
  w.files.exclusiveCreate = (path, record) => {
    if (record.state === 'waiting' && w.creates.some(r => r.state === 'waiting') && !collided) { collided = true; w.seed(collision); }
    return create(path, record);
  };
  let round = 0;
  w.ports.sleep = async () => { if (round++ === 0) w.files.unlink(w.path('original')); else w.now = 200; };
  assert.equal(await acquireRuntimeSlot({ ...w.options, deadline: 200 }, w.ports), null);
  assert.equal(collided, true, 'recovery attempts exclusive creation');
  assert.deepEqual(w.data.get(w.path('original')), collision, 'collision survives without replacement or cleanup deletion');
  assert.equal(w.timers.size, 0);
});

test('recovery never resurrects an acquired reservation', async () => {
  const w = world(), lease = await acquireRuntimeSlot(w.options, w.ports);
  await recordRuntimeRequest(lease, 'paid', w.ports);
  w.files.unlink(w.path(lease.id)); await w.tick();
  assert.equal(w.data.size, 0); assert.equal(w.timers.size, 0);
  await releaseRuntimeSlot(lease, { ended: false }, w.ports);
  assert.equal(w.creates.filter(r => r.state === 'waiting').length, 1);
});

// IPC barriers put each process at a known waiting turn. The holder is released
// only after both original tickets are restored. Heartbeats are suspended at
// each barrier to model a sleeping event loop without a five-second race.
for (const equalTimes of [false, true]) test(`native two live waiters recover mutual expiry with ${equalTimes ? 'equal-time ID' : 'distinct-time'} FIFO`, { timeout: 180_000 }, async t => {
  const stateDir = join(temp(t), 'state'), origin = 'https://recovery.example', directory = join(stateDir, 'slots', 'recovery.example');
  mkdirSync(directory, { recursive: true });
  const base = Date.now();
  writeFileSync(join(directory, 'holder.json'), JSON.stringify(row('holder', { pid: process.pid, started_at: base, request_ids: [] })));
  const start = (id, startedAt) => {
    const source = `const m=await import(${JSON.stringify(new URL('../src/runtime-slots.mjs', import.meta.url).href)});let initial=true, suspended=false;
const wait=()=>new Promise(done=>process.once('message',done));
const r=await m.acquireRuntimeSlot({stateDir:${JSON.stringify(stateDir)},origin:${JSON.stringify(origin)},kind:'check',limit:1,deadline:Date.now()+120000},{randomUUID:()=>${JSON.stringify(id)},now:()=>initial?${startedAt}:Date.now(),timers:{setInterval:(fn,ms)=>setInterval(()=>{if(!suspended)fn();},ms),clearInterval},sleep:async()=>{initial=false;suspended=true;process.send({type:'waiting'});await wait();suspended=false;}});
process.send({type:r?'acquired':'timeout',id:r?.id});if(r){await wait();await m.releaseRuntimeSlot(r,{ended:true});}process.send({type:'released'});process.disconnect();`;
    const p = spawn(process.execPath, ['--input-type=module', '-e', source], { stdio: ['ignore', 'pipe', 'pipe', 'ipc'] });
    let stderr = ''; p.stderr.on('data', b => stderr += b);
    const queue = [], readers = [];
    p.on('message', msg => readers.length ? readers.shift()(msg) : queue.push(msg));
    const next = () => queue.length ? Promise.resolve(queue.shift()) : new Promise(done => readers.push(done));
    const closed = new Promise(done => p.on('close', code => done({ code, stderr })));
    const watchdog = setTimeout(() => p.kill('SIGKILL'), 150_000);
    t.after(() => { clearTimeout(watchdog); if (p.exitCode === null) p.kill('SIGKILL'); });
    return { p, next, closed, send: () => p.send('continue') };
  };
  const b = start('b-original', base), c = start('c-original', base + (equalTimes ? 0 : 1));
  assert.equal((await b.next()).type, 'waiting'); assert.equal((await c.next()).type, 'waiting');
  const originalB = JSON.parse(readFileSync(join(directory, 'b-original.json'))), originalC = JSON.parse(readFileSync(join(directory, 'c-original.json')));
  for (const id of ['b-original', 'c-original']) utimesSync(join(directory, `${id}.json`), new Date(base - 120_000), new Date(base - 120_000));
  b.send(); assert.equal((await b.next()).type, 'waiting');
  assert.equal(readdirSync(directory).includes('c-original.json'), false, 'first live waiter reclaims stale-looking peer');
  c.send(); assert.equal((await c.next()).type, 'waiting');
  const afterC = (await listRuntimeJobs({ stateDir, origin })).jobs;
  assert.deepEqual(afterC.find(r => r.id === 'c-original'), originalC, 'second live waiter restores original identity');
  b.send(); assert.equal((await b.next()).type, 'waiting');
  assert.deepEqual(JSON.parse(readFileSync(join(directory, 'b-original.json'))), originalB);
  assert.deepEqual(JSON.parse(readFileSync(join(directory, 'c-original.json'))), originalC);
  unlinkSync(join(directory, 'holder.json'));
  b.send(); assert.deepEqual(await b.next(), { type: 'acquired', id: 'b-original' });
  c.send(); assert.equal((await c.next()).type, 'waiting');
  assert.equal((await listRuntimeJobs({ stateDir, origin })).jobs.filter(r => r.state === 'active').length, 1, 'one active while second waits');
  b.send(); assert.equal((await b.next()).type, 'released'); assert.equal((await b.closed).code, 0);
  c.send(); assert.deepEqual(await c.next(), { type: 'acquired', id: 'c-original' });
  c.send(); assert.equal((await c.next()).type, 'released'); assert.equal((await c.closed).code, 0);
  assert.deepEqual(readdirSync(directory), [], 'no ticket, claim or refresh artifact after release');
});
