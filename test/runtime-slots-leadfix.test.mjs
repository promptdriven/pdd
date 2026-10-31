import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync, utimesSync, readdirSync, unlinkSync } from 'node:fs';
import { spawn } from 'node:child_process';
import { join } from 'node:path';
import { randomUUID } from 'node:crypto';
import { acquireRuntimeSlot, recordRuntimeRequest, releaseRuntimeSlot, listRuntimeJobs } from '../src/runtime-slots.mjs';
import { temp } from './runtime-fake.mjs';

const row = (id, extra = {}) => ({ id, state: 'active', kind: 'check', pid: 42, started_at: 0, request_ids: [id], ...extra });
const flush = () => new Promise(done => setImmediate(done));
function world() {
  const origin = `https://${randomUUID()}.example`, stateDir = '/virtual/state';
  const directory = join(stateDir, 'slots', new URL(origin).host), data = new Map(), times = new Map(), listeners = new Set(), intervals = new Set();
  const w = { now: 0, claims: 0, touches: [], sleeps: [], origin, directory, data, times, intervals, held: false };
  const path = id => join(directory, `${id}.json`);
  w.seed = (record, time = w.now) => { data.set(path(record.id), structuredClone(record)); times.set(path(record.id), time); };
  const files = {
    listRecords: () => ({ jobs: [...data.values()].filter(item => item.state).map(item => structuredClone(item)) }),
    exclusiveCreate: (file, record) => {
      if (file.endsWith('claim.json')) { w.claims++; if (w.rejectClaim || w.held) return false; w.held = true; }
      if (data.has(file)) return false; data.set(file, structuredClone(record)); times.set(file, w.now); return true;
    },
    writeAtomic: (file, record) => { data.set(file, structuredClone(record)); times.set(file, w.now); },
    unlink: file => { if (file.endsWith('claim.json')) w.held = false; times.delete(file); data.delete(file); },
    modifiedAt: file => times.get(file) ?? null,
    touch: file => { if (!data.has(file)) return false; times.set(file, w.now); w.touches.push(file); return true; },
  };
  w.ports = { files, now: () => w.now, pid: 43, randomUUID, isAlive: () => true, random: () => 0,
    sleep: async ms => { w.sleeps.push(ms); w.now += ms; },
    onInterrupt: handler => { listeners.add(handler); return () => listeners.delete(handler); },
    timers: { setInterval: (fn, ms) => { const timer = { fn, ms }; intervals.add(timer); return timer; }, clearInterval: timer => intervals.delete(timer) },
  };
  w.options = { stateDir, origin, kind: 'check', limit: 1 };
  w.signal = () => { for (const fn of [...listeners]) fn(); };
  w.tick = async () => { w.now += 5000; for (const timer of [...intervals]) { assert.equal(timer.ms, 5000); timer.fn(); } await flush(); };
  return w;
}

test('heartbeat-live-owner: waiting, active and held claim refresh on the timer; ownership end stops refresh', async () => {
  const w = world(); w.seed(row('occupied'));
  let wake; w.ports.sleep = () => new Promise(done => wake = done);
  const pending = acquireRuntimeSlot(w.options, w.ports); await flush();
  for (let i = 0; i < 13; i++) await w.tick();
  const waiting = [...w.data.values()].find(item => item.state === 'waiting');
  assert.equal(w.times.get(join(w.directory, `${waiting.id}.json`)), 65_000);
  w.signal(); wake(); assert.equal(await pending, null); assert.equal(w.intervals.size, 0);
  assert.deepEqual([...w.data.values()].map(item => item.id), ['occupied']);

  const active = world(), lease = await acquireRuntimeSlot(active.options, active.ports);
  for (let i = 0; i < 13; i++) await active.tick();
  assert.equal(active.times.get(join(active.directory, `${lease.id}.json`)), 65_000);
  assert.deepEqual(Object.keys((await listRuntimeJobs(active.options, active.ports)).jobs[0]).sort(), ['id', 'state', 'pid', 'kind', 'started_at', 'request_ids'].sort());
  const realList = active.ports.files.listRecords; let unblock;
  active.ports.files.listRecords = async () => { await new Promise(done => unblock = done); return realList(); };
  const recording = recordRuntimeRequest(lease, 'paid', active.ports); await flush();
  for (let i = 0; i < 13; i++) await active.tick();
  assert.equal(active.times.get(join(active.directory, 'claim.json')), 130_000);
  unblock(); assert.equal(await recording, true);
  active.ports.files.listRecords = realList;
  await releaseRuntimeSlot(lease, { ended: false }, active.ports);
  assert.equal(active.intervals.size, 0); const touched = active.touches.length; await active.tick(); assert.equal(active.touches.length, touched);
  assert.equal(active.data.get(join(active.directory, `${lease.id}.json`)).request_ids[0], 'paid');
  await releaseRuntimeSlot(lease, { ended: true }, active.ports);
  assert.equal(active.data.size, 0);
});

test('heartbeat does not recreate a removed owned file', async () => {
  const w = world(), lease = await acquireRuntimeSlot(w.options, w.ports);
  await w.ports.files.unlink(join(w.directory, `${lease.id}.json`)); await w.tick();
  assert.equal(w.data.size, 0); assert.equal(w.intervals.size, 0);
  await releaseRuntimeSlot(lease, { ended: true }, w.ports);
});

test('reused-pid-active and legacy-freshness: exact owner expiry preserves paid leases and fixed 30-minute boundary', async () => {
  for (const age of [59_999, 60_000, 1_799_999, 1_800_000]) for (const answer of ['running', 'unknown', 'throw', 'ended', 'unsent']) {
    const w = world(); w.now = age; w.seed(row('old', { request_ids: answer === 'unsent' ? [] : ['old'] }), 0);
    let reads = 0; w.ports.readRun = async () => { reads++; if (answer === 'throw') throw Error('read failed'); return answer; };
    const found = await acquireRuntimeSlot({ ...w.options, deadline: age + 1 }, w.ports);
    const allowed = age >= 60_000 && (answer === 'ended' || answer === 'unsent' || age >= 1_800_000);
    assert.equal(!!found, allowed, `${age}/${answer}`);
    assert.equal(w.data.has(join(w.directory, 'old.json')), !allowed);
    if (age < 60_000 || age >= 1_800_000 || answer === 'unsent') assert.equal(reads, 0);
    if (found) await releaseRuntimeSlot(found, { ended: true }, w.ports);
  }
});

test('reused-pid-waiter-and-claim: native legacy mtime reaches expiry at exactly 60000, preserving a fresh claim', async t => {
  for (const kind of ['waiting', 'claim']) for (const age of [59_999, 60_000]) {
    const stateDir = join(temp(t), 'state'), directory = join(stateDir, 'slots', 'host'), file = join(directory, kind === 'claim' ? '.claim-old.lock' : 'old.json');
    mkdirSync(directory, { recursive: true });
    writeFileSync(file, JSON.stringify(kind === 'claim' ? { id: 'old', pid: process.pid, choosing: false, number: 1 } : row('old', { state: 'waiting', pid: process.pid, request_ids: [] })));
    utimesSync(file, new Date(0), new Date(0)); let now = age;
    const found = await acquireRuntimeSlot({ stateDir, origin: 'https://host', kind: 'check', limit: 1, deadline: age + 1 }, { now: () => now, sleep: async ms => now += ms, random: () => 0 });
    assert.equal(!!found, age === 60_000, `${kind}/${age}`);
    assert.equal(readdirSync(directory).includes(file.split('/').at(-1)), age === 59_999);
    if (found) await releaseRuntimeSlot(found, { ended: true });
  }
});

test('probe-outside-lock: a blocked probe permits another admitted job to record while it waits', async () => {
  const w = world(); w.now = 60_000; w.seed(row('dead', { pid: 99 }), 0); w.seed(row('admitted', { pid: 43 }), w.now);
  let finish; w.ports.readRun = async () => { assert.equal(w.held, false); await new Promise(done => finish = done); return 'running'; };
  const pending = acquireRuntimeSlot({ ...w.options, deadline: w.now + 100 }, w.ports); await flush();
  assert.equal(await recordRuntimeRequest({ id: 'admitted', directory: w.directory }, 'new-request', w.ports), true);
  assert.deepEqual(w.data.get(join(w.directory, 'admitted.json')).request_ids, ['admitted', 'new-request']);
  finish(); assert.equal(await pending, null);
});

test('dead-job-probe-cache: 15-second observations cache running, unknown and errors and isolate origin, command and request', async () => {
  for (const result of ['running', 'unknown', 'error']) {
    const w = world(); w.ports.isAlive = pid => pid !== 42; w.seed(row('old')); let reads = 0;
    w.ports.readRun = async () => { assert.equal(w.held, false); reads++; if (result === 'error') throw Error('offline'); return result; };
    for (const now of [0, 100, 14_999, 15_000]) {
      w.now = now; assert.equal(await acquireRuntimeSlot({ ...w.options, deadline: now + 1 }, w.ports), null);
      assert.equal(reads, now < 15_000 ? 1 : 2);
    }
    w.data.get(join(w.directory, 'old.json')).kind = 'lint';
    await acquireRuntimeSlot({ ...w.options, deadline: w.now + 1 }, w.ports); assert.equal(reads, 3);
    w.data.get(join(w.directory, 'old.json')).request_ids = ['other'];
    await acquireRuntimeSlot({ ...w.options, deadline: w.now + 1 }, w.ports); assert.equal(reads, 4);
    const other = { ...w.options, origin: w.origin.replace('https:', 'http:') };
    await acquireRuntimeSlot({ ...other, deadline: w.now + 1 }, w.ports); assert.equal(reads, 5);
  }
});

for (const change of ['refresh', 'append', 'replace']) test(`probe-snapshot-race: ${change} invalidates the ended snapshot`, async () => {
  const w = world(); w.now = 60_000; w.seed(row('old'), 0);
  w.ports.readRun = async () => {
    assert.equal(w.held, false);
    const record = w.data.get(join(w.directory, 'old.json'));
    if (change === 'refresh') w.times.set(join(w.directory, 'old.json'), w.now);
    if (change === 'append') record.request_ids.push('new-paid-job');
    if (change === 'replace') { record.pid = 88; record.started_at = w.now; record.request_ids = ['successor']; }
    return 'ended';
  };
  assert.equal(await acquireRuntimeSlot({ ...w.options, deadline: w.now + 1 }, w.ports), null);
  assert.ok(w.data.has(join(w.directory, 'old.json')));
  if (change === 'append') assert.deepEqual(w.data.get(join(w.directory, 'old.json')).request_ids, ['old', 'new-paid-job']);
});

test('head-only-jitter: followers never claim; head retains identity and positive bounded jitter clips to deadline', async () => {
  const follower = world(); follower.now = 1; follower.seed(row('head', { state: 'waiting', request_ids: [] }));
  follower.ports.randomUUID = () => 'follower'; let original;
  follower.ports.sleep = async ms => { const ticket = follower.data.get(join(follower.directory, 'follower.json')); original ??= structuredClone(ticket); assert.deepEqual(ticket, original); follower.sleeps.push(ms); follower.now += ms; };
  assert.equal(await acquireRuntimeSlot({ ...follower.options, deadline: 50 }, follower.ports), null);
  assert.equal(follower.claims, 0);
  const head = world(); head.rejectClaim = true; head.ports.randomUUID = () => 'same-ticket'; let n = 0;
  head.ports.random = () => n++ % 2 ? 0.999999 : 0;
  assert.equal(await acquireRuntimeSlot({ ...head.options, deadline: 50 }, head.ports), null);
  assert.ok(head.claims > 2); assert.ok(new Set(head.sleeps).size > 1);
  assert.ok(head.sleeps.every(ms => ms > 0 && ms <= 8)); assert.equal(head.now, 50);
  assert.ok(follower.sleeps[0] > head.sleeps[0]); assert.equal(head.data.size, 0);
});

for (const signal of ['SIGINT', 'SIGHUP', 'SIGTERM']) for (const phase of ['waiting', 'claim', 'paid']) test(`signals-retain-paid-lease: child ${signal} during ${phase}`, async t => {
  const stateDir = join(temp(t), 'state');
  const source = `import {mkdirSync,readFileSync,readdirSync,writeFileSync,unlinkSync,statSync,utimesSync} from 'node:fs'; import {join} from 'node:path';
const m=await import(${JSON.stringify(new URL('../src/runtime-slots.mjs', import.meta.url).href)}); const dir=${JSON.stringify(join(stateDir, 'slots', 'host'))};mkdirSync(dir,{recursive:true});let pause=false,announce=false;
const files={listRecords:async()=>{if(announce){announce=false;process.stdout.write('ready\\n');}if(pause){pause=false;const keep=setInterval(()=>{},1000);await new Promise(done=>{process.once(${JSON.stringify(signal)},done);process.stdout.write('ready\\n');});clearInterval(keep);}return {jobs:readdirSync(dir).filter(n=>n.endsWith('.json')&&n!=='claim.json').map(n=>JSON.parse(readFileSync(join(dir,n))))};},exclusiveCreate:(p,r)=>{try{writeFileSync(p,JSON.stringify(r),{flag:'wx'});return true;}catch(e){if(e.code==='EEXIST')return false;throw e;}},writeAtomic:(p,r)=>writeFileSync(p,JSON.stringify(r)),unlink:p=>{try{unlinkSync(p);}catch(e){if(e.code!=='ENOENT')throw e;}},modifiedAt:p=>{try{return statSync(p).mtimeMs;}catch{return null;}},touch:p=>{try{utimesSync(p,new Date(),new Date());return true;}catch{return false;}}};
const opts={stateDir:${JSON.stringify(stateDir)},origin:'https://host',kind:'check',limit:1};
if(${JSON.stringify(phase)}==='waiting'){writeFileSync(join(dir,'busy.json'),JSON.stringify({id:'busy',state:'active',kind:'check',pid:process.pid,started_at:Date.now(),request_ids:['other']}));announce=true;await m.acquireRuntimeSlot(opts,{files});}
else {const r=await m.acquireRuntimeSlot(opts,{files});if(${JSON.stringify(phase)}==='claim'){pause=true;await m.recordRuntimeRequest(r,'must-not-record',{files});}else{await m.recordRuntimeRequest(r,'uncertain-paid',{files});process.stdout.write('ready\\n');const keep=setInterval(()=>{},1000);await new Promise(done=>process.once(${JSON.stringify(signal)},done));clearInterval(keep);await m.releaseRuntimeSlot(r,{ended:false},{files});}}`;
  const p = spawn(process.execPath, ['--input-type=module', '-e', source], { stdio: ['ignore', 'pipe', 'pipe'] }); let stderr = '';
  p.stderr.on('data', bytes => stderr += bytes); let sent = false;
  const watchdog = setTimeout(() => { stderr += 'signal cleanup watchdog expired'; p.kill('SIGKILL'); }, 30_000);
  t.after(() => { clearTimeout(watchdog); if (p.exitCode === null) p.kill('SIGKILL'); });
  const exited = new Promise((done, fail) => { p.on('error', fail); p.on('close', code => { clearTimeout(watchdog); done(code); }); });
  p.stdout.on('data', bytes => { if (!sent && String(bytes).includes('ready')) { sent = true; p.kill(signal); } });
  assert.equal(await exited, 0, stderr); assert.equal(sent, true);
  const directory = join(stateDir, 'slots', 'host'); assert.equal(readdirSync(directory).includes('claim.json'), false);
  const jobs = (await listRuntimeJobs({ stateDir, origin: 'https://host' })).jobs;
  if (phase === 'paid') assert.deepEqual(jobs.map(item => item.request_ids), [['uncertain-paid']]);
  else assert.deepEqual(jobs.map(item => item.id), phase === 'waiting' ? ['busy'] : []);
});


test('a removed native claim fences a paused registration and cannot unlink its successor', async t => {
  const stateDir = join(temp(t), 'state'), origin = 'https://host';
  let intervals = 0; const timers = { setInterval: () => { intervals++; return intervals; }, clearInterval: () => {} };
  const lease = await acquireRuntimeSlot({ stateDir, origin, kind: 'check', limit: 1 }, { timers });
  const directory = lease.directory, successor = join(directory, '.claim-successor.lock');
  let now = Date.now();
  timers.setInterval = () => {
    queueMicrotask(() => {
      for (const name of readdirSync(directory).filter(name => name.startsWith('.claim-'))) unlinkSync(join(directory, name));
      writeFileSync(successor, JSON.stringify({ id: 'successor', pid: process.pid, choosing: false, number: 1 }));
    });
    return ++intervals;
  };
  assert.equal(await recordRuntimeRequest(lease, 'must-not-register', { timers, now: () => now, deadline: now + 10, sleep: async ms => now += ms }), false);
  assert.deepEqual((await listRuntimeJobs({ stateDir, origin })).jobs[0].request_ids, []);
  assert.ok(readdirSync(directory).includes('.claim-successor.lock'));
  await releaseRuntimeSlot(lease, { ended: true });
});


test('pending dead-owner probes coalesce even when the request takes more than 15 seconds', async () => {
  const w = world(); w.ports.isAlive = pid => pid !== 42; w.seed(row('old')); let reads = 0, complete;
  w.ports.readRun = async () => { reads++; await new Promise(done => complete = done); return 'running'; };
  const first = acquireRuntimeSlot({ ...w.options, deadline: 30_000 }, w.ports); await flush();
  w.now = 20_000;
  const second = acquireRuntimeSlot({ ...w.options, deadline: 30_000 }, w.ports); await flush();
  assert.equal(reads, 1); complete(); await Promise.all([first, second]);
  assert.equal(reads, 1);
  w.now = 34_999; await acquireRuntimeSlot({ ...w.options, deadline: 35_000 }, w.ports); assert.equal(reads, 1);
});
