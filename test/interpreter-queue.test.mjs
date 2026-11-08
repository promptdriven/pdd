import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { acquireInterpreterSlot, markInterpreterDispatch, observeInterpreterRequest, readInterpreterProgress } from '../src/interpreter-queue.mjs';
import { temp } from './runtime-fake.mjs';

function fixture(t, limit = '2') {
  const root = temp(t), env = { PDD_INTERPRETER_QUEUE: root, PDD_INTERPRETER_CONCURRENCY: limit };
  const f = { root, env, now: 1000, messages: [] };
  f.ports = { now: () => f.now, alive: () => true, say: s => f.messages.push(s),
    sleep: async ms => { f.now += ms; await new Promise(done => setImmediate(done)); } };
  f.acquire = (id, extra = {}) => acquireInterpreterSlot({ cwd: '/work/one', origin: 'http://localhost:1234', requestId: id, kind: 'check', env, ...extra }, f.ports);
  f.finish = (id, extra = {}) => observeInterpreterRequest({ env, origin: 'http://localhost:1234', requestId: id, outcome: 'verdict', terminal: true, ...extra }, f.ports);
  f.progress = (cwd = '/work/one', since = 0) => readInterpreterProgress({ cwd, since, env }, f.ports);
  return f;
}

test('machine queue defaults to two shared lint/check requests across origins and worktrees', async t => {
  const f = fixture(t); delete f.env.PDD_INTERPRETER_CONCURRENCY;
  await f.acquire('a');
  await f.acquire('b', { kind: 'lint', cwd: '/work/two', origin: 'http://localhost:4321' });
  const third = await f.acquire('c', { deadline: f.now + 1000 });
  assert.equal(third, null);
  assert.equal(f.progress('/work/two').requests[0].activeAtStart, 2);
  assert.ok(f.messages.some(s => /position 1\)/.test(s)));
  assert.equal(f.progress().requests.at(-1).outcome, 'not_sent');
});

test('FIFO position includes equal-clock waiters and releases in ticket order', async t => {
  const f = fixture(t, '1'); await f.acquire('a');
  let polls = 0, observed;
  f.ports.sleep = async () => {
    if (++polls === 2) { observed = f.progress(); await f.finish('a'); }
    if (polls >= 4 && f.progress().requests.find(row => row.requestId === 'b')?.state === 'running') await f.finish('b');
    await new Promise(done => setImmediate(done));
  };
  const [b, c] = await Promise.all([f.acquire('b'), f.acquire('c', { deadline: f.now + 1000 })]);
  // Finish b from its first waiting successor's sleep.
  assert.ok(b); assert.ok(c); assert.equal(observed.position, 1);
  assert.ok(b.ticket < c.ticket);
});

test('waiting intervals pause once, survive restart and exclude execution', async t => {
  const f = fixture(t, '1'); await f.acquire('a', { cwd: '/work/blocker' });
  f.ports.sleep = async ms => { f.now += ms; if (f.now === 2000) await f.finish('a'); };
  await f.acquire('b');
  f.now = 4000;
  const restarted = readInterpreterProgress({ cwd: '/work/one', since: 1500, env: f.env }, { now: () => 4000 });
  assert.equal(restarted.pausedMs, 500);
  assert.equal(restarted.requests[0].startedAt, 2000);
});

test('busy halves capacity, holds it for a minute, then verdicts recover it to the limit', async t => {
  const f = fixture(t, '4'); await f.acquire('a');
  await f.finish('a', { outcome: 'busy', waitMs: 1000 });
  let cap = JSON.parse(readFileSync(join(f.root, 'capacity.json')));
  assert.equal(cap.limit, 2);
  f.now += 1000; await f.acquire('b'); await f.finish('b');
  assert.equal(JSON.parse(readFileSync(join(f.root, 'capacity.json'))).limit, 2);
  f.now += 60_000;
  for (const id of ['c', 'd', 'e']) { await f.acquire(id); await f.finish(id); }
  cap = JSON.parse(readFileSync(join(f.root, 'capacity.json')));
  assert.equal(cap.limit, 4);
});

test('busy pause also applies when the reduced capacity still has room', async t => {
  const f = fixture(t, '4'); await f.acquire('a'); await f.finish('a', { outcome: 'busy', waitMs: 2000 });
  assert.equal(await f.acquire('b', { deadline: f.now + 1000 }), null);
  assert.ok(f.progress().requests[1].startedAt === null);
});

test('a live uncertain request retains its slot until same-ID completion', async t => {
  const f = fixture(t, '1'), slot = await f.acquire('paid'); await markInterpreterDispatch(slot, f.ports);
  await f.finish('paid', { outcome: 'unknown', terminal: false });
  assert.equal(f.progress().state, 'running');
  assert.equal(await f.acquire('later', { deadline: f.now + 500 }), null);
  await f.finish('paid');
  assert.ok(await f.acquire('next'));
  assert.equal(f.progress().requests[0].dispatched, true);
});

test('ledger stores request start/end and load, repeated reads do not change the terminal row', async t => {
  const f = fixture(t), slot = await f.acquire('a'); await markInterpreterDispatch(slot, f.ports);
  await f.acquire('b'); f.now += 500;
  await f.finish('a', { outcome: 'refused' });
  const before = f.progress().requests[0]; f.now += 1000; await f.finish('a');
  assert.deepEqual(f.progress().requests[0], before);
  assert.equal(before.activeAtStart, 1); assert.equal(before.activeAtEnd, 2);
  assert.equal(before.startedAt, 1000); assert.equal(before.endedAt, 1500);
  assert.equal(before.outcome, 'refused');
});

test('unreadable records fail closed and status does not rewrite evidence', async t => {
  const f = fixture(t); writeFileSync(join(f.root, 'ticket-broken.json'), '{');
  const names = readdirSync(f.root);
  assert.equal(f.progress().state, 'unavailable');
  assert.deepEqual(readdirSync(f.root), names);
  await assert.rejects(f.acquire('a'), { code: 'local-state-unavailable' });
});

test('status leaves a dead waiter unchanged and admission persists its release', async t => {
  const f = fixture(t, '1'); await f.acquire('a');
  const row = f.progress().requests[0]; row.state = 'waiting'; row.startedAt = null; row.pid = 123456;
  writeFileSync(join(f.root, 'ticket-1.json'), JSON.stringify(row));
  f.ports.alive = pid => pid !== 123456;
  assert.equal(f.progress().state, 'finished');
  assert.equal(JSON.parse(readFileSync(join(f.root, 'ticket-1.json'))).state, 'waiting');
  assert.ok(await f.acquire('b'));
  const reclaimed = JSON.parse(readFileSync(join(f.root, 'ticket-1.json')));
  assert.equal(reclaimed.state, 'finished');
  assert.equal(reclaimed.releaseReason, 'owner-dead');
  assert.equal(reclaimed.outcome, 'not_sent');
});

test('interruption removes only unsent waiting ownership', async t => {
  const f = fixture(t, '1'); await f.acquire('a'); let interrupted = false;
  f.ports.interrupted = () => interrupted;
  f.ports.sleep = async () => { interrupted = true; };
  assert.equal(await f.acquire('b'), null);
  assert.equal(f.progress().requests[0].state, 'running');
  assert.equal(f.progress().requests[1].state, 'finished');
});

test('native processes share admission and preserve a queued child until a slot is released', async t => {
  const { spawn } = await import('node:child_process');
  const root = temp(t), env = { ...process.env, PDD_INTERPRETER_QUEUE: root, PDD_INTERPRETER_CONCURRENCY: '1' };
  const moduleUrl = new URL('../src/interpreter-queue.mjs', import.meta.url).href;
  const source = `
    import { acquireInterpreterSlot, observeInterpreterRequest } from ${JSON.stringify(moduleUrl)};
    const requestId = 'child-' + process.pid;
    const slot = await acquireInterpreterSlot({cwd:process.cwd(),origin:'http://localhost:1',requestId,kind:'lint'}, {say:s=>console.log(s)});
    console.log('ADMITTED:' + slot.ticket);
    await new Promise(done=>process.stdin.once('data',done));
    await observeInterpreterRequest({origin:'http://localhost:1',requestId,outcome:'verdict',terminal:true});
  `;
  const child = () => {
    const p = spawn(process.execPath, ['--input-type=module', '-e', source], { env, stdio: ['pipe', 'pipe', 'pipe'] });
    const output = { text: '', error: '' };
    p.stdout.on('data', bytes => { output.text += bytes; }); p.stderr.on('data', bytes => { output.error += bytes; });
    const closed = new Promise(done => p.once('close', code => done(code)));
    t.after(() => { if (p.exitCode === null) p.kill('SIGTERM'); });
    return { p, output, closed };
  };
  const waitFor = async predicate => { for (let i = 0; i < 400; i++) { if (predicate()) return; await new Promise(done => setTimeout(done, 10)); } assert.fail('native queue child did not reach its state'); };
  const first = child(); await waitFor(() => first.output.text.includes('ADMITTED:'));
  const second = child(); await waitFor(() => /position 1/.test(second.output.text));
  assert.ok(!second.output.text.includes('ADMITTED:'));
  first.p.stdin.end('done'); assert.equal(await first.closed, 0, first.output.error);
  await waitFor(() => second.output.text.includes('ADMITTED:'));
  second.p.stdin.end('done'); assert.equal(await second.closed, 0, second.output.error);
  const rows = readInterpreterProgress({ cwd: process.cwd(), env }).requests;
  assert.equal(rows.length, 2); assert.ok(rows.every(row => row.activeAtStart === 1 && row.state === 'finished'));
  assert.notEqual(rows[0].pid, rows[1].pid);
});

test('a dead admitted owner with durable unsent proof does not leak machine capacity', async t => {
  const f = fixture(t, '1'); await f.acquire('unsent');
  const file = join(f.root, 'ticket-1.json'), row = JSON.parse(readFileSync(file));
  row.pid = 123456; writeFileSync(file, JSON.stringify(row));
  f.ports.alive = pid => pid !== 123456;
  assert.ok(await f.acquire('next', { deadline: f.now + 500 }));
  assert.equal(f.progress().requests[0].outcome, 'not_sent');
  assert.equal(f.progress().requests[1].activeAtStart, 1);
});

for (const dispatched of [false, true]) test(`admission records dead holder release with dispatched=${dispatched} and never replays it`, async t => {
  const f = fixture(t, '1'), slot = await f.acquire('dead');
  if (dispatched) await markInterpreterDispatch(slot, f.ports);
  const file = join(f.root, 'ticket-1.json'), row = JSON.parse(readFileSync(file));
  row.pid = 123456; writeFileSync(file, JSON.stringify(row));
  f.ports.alive = pid => pid !== row.pid;
  f.now += 500;
  assert.ok(await f.acquire('next', { deadline: f.now + 500 }), 'dead-holder-capacity');
  const released = JSON.parse(readFileSync(file));
  assert.equal(released.state, 'finished');
  assert.equal(released.releaseReason, 'owner-dead');
  assert.equal(released.dispatched, dispatched);
  assert.equal(released.outcome, dispatched ? 'unknown' : 'not_sent');
  assert.equal(released.endedAt, 1500);
  assert.equal(released.activeAtStart, 1); assert.equal(released.activeAtEnd, 1);
  assert.equal(f.progress().requests[1].activeAtStart, 1);
  await assert.rejects(f.acquire('dead'), { code: 'local-state-unavailable' });
  assert.deepEqual(JSON.parse(readFileSync(file)), released);
  await f.finish('dead');
  const recovered = JSON.parse(readFileSync(file));
  assert.deepEqual(recovered, { ...released, outcome: dispatched ? 'verdict' : 'not_sent' });
  assert.equal(f.progress().requests[1].state, 'running');
  await f.finish('dead', { outcome: 'refused' });
  assert.deepEqual(JSON.parse(readFileSync(file)), recovered);
});

test('each waiting admission pass reclaims a holder that dies after registration', async t => {
  const f = fixture(t, '1'), slot = await f.acquire('holder');
  await markInterpreterDispatch(slot, f.ports);
  const file = join(f.root, 'ticket-1.json'), row = JSON.parse(readFileSync(file));
  row.pid = 123456; writeFileSync(file, JSON.stringify(row));
  let alive = true, waits = 0;
  f.ports.alive = pid => pid !== row.pid || alive;
  f.ports.sleep = async ms => { waits++; f.now += ms; alive = false; };
  assert.ok(await f.acquire('next', { deadline: f.now + 1000 }), 'dead-holder-during-wait');
  assert.equal(waits, 1);
  assert.equal(JSON.parse(readFileSync(file)).releaseReason, 'owner-dead');
});
