import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { captureSource } from '../src/runtime-preflight.mjs';
import { listRuntimeJobs } from '../src/runtime-slots.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const make = (setup, fake, extra = {}) => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, extra);
const check = (setup, ports, extra = {}) => runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true, ...extra } }, ports);
const startTry = (setup, ports, extra = {}) => runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true, ...extra } }, ports);
const response = reply => new Response(reply.text ?? JSON.stringify(reply.json), { status: reply.status, headers: reply.headers });
const gates = [
  { status: 401, json: { error: { code: 'auth-required' } } },
  { status: 403, json: { error: { code: 'not-invited' } } },
  { status: 403, json: { error: { code: 'no-cloud-access' } } },
  { status: 426, json: { error: { code: 'update-required' } } },
  { status: 503, json: { error: { code: 'cloud-unavailable' } } },
  { status: 503, text: 'The runtime opens soon.' },
];
const maintenanceCount = ports => (ports.stderr.text.match(/The runtime is in maintenance/g) ?? []).length;

for (const via of ['capacity', 'admission']) for (const interrupted of [true, false]) test(`far-until-${via}: bounded positive chunks, rechecks and one notice (${interrupted ? 'interrupt' : 'deadline'})`, async t => {
  const setup = harbor(t); let made, capacityReads = 0;
  const details = { until: new Date(2_592_000_000).toISOString(), reason: 'long synthetic window' };
  const fake = await fakeRuntime(t, (e, f) => {
    if (via === 'admission' && e.command === 'lint') return { status: 503, headers: { 'retry-after': '7' }, json: { dispatch: 'not_started', error: { code: 'maintenance', details } } };
    assert.fail(`unexpected submission ${e.url}`);
  });
  made = make(setup, fake, { interactive: true }); made.clock.now = 0;
  fake.capacity = () => { capacityReads++; return via === 'capacity' ? { status: 200, json: { maintenance: details } } : { status: 404, json: {} }; };
  const sleeps = [];
  made.ports.sleep = async ms => { assert.ok(ms > 0 && ms <= 60_000); sleeps.push(ms); made.clock.now += ms; if (interrupted && sleeps.length === 2) made.clock.interrupt(); };
  assert.equal(await check(setup, made.ports, interrupted ? {} : { '--timeout': '2' }), interrupted ? 3 : 5);
  assert.equal(made.clock.now, 120_000); assert.equal(sleeps.length, 2); assert.ok(capacityReads >= 2); assert.equal(maintenanceCount(made.ports), 1);
  assert.equal(fake.posts.length, via === 'admission' ? 1 : 0);
  const report = JSON.parse(made.ports.stdout.text); assert.equal(report.rows[0].calls, 0);
  assert.match(report.rows[0].reason.message, /maintenance/); assert.doesNotMatch(made.ports.stdout.text, /after 0 lint attempts/);
  if (via === 'admission') {
    const id = fake.posts[0].request.requestId;
    const raw = JSON.parse(readFileSync(join(setup.state, 'batches', report.batch, `${id}.admission.json`)));
    assert.equal(raw.error.details.until, details.until); assert.equal(report.rows[0].request_id, null);
  }
});

for (const failure of ['html', '405', '500', 'timeout', 'unreachable']) for (const kind of ['check', 'try']) test(`unrecognized-capacity-fail-open: ${failure} then ordinary ${kind}, one warning`, async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => e.command === 'try' ? { status: 200, json: f.tryJob(e.request.requestId) } : f.normal(e));
  let reads = 0;
  const made = make(setup, fake, { fetch: async (url, init) => {
    if (new URL(url).pathname !== '/v1/capacity') return fetch(url, init);
    reads++; if (failure === 'timeout') throw Object.assign(Error('timed out'), { name: 'AbortError' });
    if (failure === 'unreachable') throw Object.assign(Error('unreachable'), { cause: { code: 'ECONNREFUSED' } });
    return response(failure === 'html' ? { status: 200, text: '<html>proxy</html>' } : { status: Number(failure), json: {} });
  } });
  assert.equal(await (kind === 'try' ? startTry(setup, made.ports) : check(setup, made.ports)), 0, made.ports.stderr.text);
  assert.equal((made.ports.stderr.text.match(/Warning: runtime capacity/g) ?? []).length, 1);
  assert.ok(reads >= 2, 'an unrecognized reply must not be cached as clear');
  assert.equal(fake.posts.filter(e => e.command === 'lint').length, 1); assert.equal(fake.posts.filter(e => e.command === kind).length, 1);
  if (kind === 'check') assert.equal(JSON.parse(made.ports.stdout.text).rows[0].state, 'passed');
});

for (const gate of gates) for (const before of [true, false]) test(`${before ? 'capacity-gates-before-fail-open' : 'fail-open-keeps-admission-gates'}: ${gate.json?.error.code ?? 'opens-soon'}`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, () => gate), made = make(setup, fake);
  made.ports.fetch = (url, init) => new URL(url).pathname === '/v1/capacity' ? Promise.resolve(response(before ? gate : { status: 500, json: {} })) : fetch(url, init);
  assert.equal(await check(setup, made.ports), 5);
  assert.equal(fake.posts.length, before ? 0 : 1); assert.equal(fake.gets.length, 0);
  assert.equal((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs.length, 0);
});

test('fail-open-keeps-admission-gates: uncertain POST stays on its saved ID', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => e.command === 'check' ? { destroy: true } : e.method === 'GET' ? { status: 404, json: {} } : f.normal(e));
  const made = make(setup, fake, { fetch: (url, init) => new URL(url).pathname === '/v1/capacity' ? Promise.resolve(response({ status: 500, json: {} })) : fetch(url, init) });
  assert.equal(await check(setup, made.ports), 3); const posts = fake.posts.filter(e => e.command === 'check'); assert.equal(posts.length, 1);
  assert.ok(fake.gets.length > 0); assert.ok(fake.gets.every(e => e.url.endsWith(posts[0].request.requestId)));
});

for (const maintenance of [null, { until: 'bad' }, { until: new Date(0).toISOString() }]) test(`unclear-and-past-until: ${JSON.stringify(maintenance)} permits ordinary admission`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => f.normal(e)); fake.capacity = () => ({ status: 200, json: { maintenance } });
  const made = make(setup, fake); assert.equal(await check(setup, made.ports), 0); assert.equal(maintenanceCount(made.ports), 0);
});

test('fail-open-then-maintenance: a failed advisory read cannot conceal the next window', async t => {
  const setup = harbor(t); let made, reads = 0, end;
  const fake = await fakeRuntime(t, (e, f) => { if (e.command === 'check') assert.ok(made.clock.now >= end); return f.normal(e); });
  made = make(setup, fake); end = made.clock.now + 7000;
  fake.capacity = () => ++reads === 1 ? { status: 500, json: {} } : { status: 200, json: { maintenance: made.clock.now < end ? { until: new Date(end).toISOString(), reason: 'new window' } : null } };
  assert.equal(await check(setup, made.ports), 0);
  assert.equal((made.ports.stderr.text.match(/Warning: runtime capacity/g) ?? []).length, 1); assert.equal(maintenanceCount(made.ports), 1); assert.equal(reads, 3);
});

for (const kind of ['check', 'lint', 'try']) for (const reason of ['local slot', 'maintenance']) for (const interrupted of [false, true]) test(`wait-end-cause: ${kind} ${reason} ${interrupted ? 'interruption' : 'deadline'} before first lint POST`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, () => { assert.fail('wait sent a job'); }), made = make(setup, fake);
  if (reason === 'local slot') {
    made.ports.env.PDD_MAX_JOBS = '1'; const directory = join(setup.state, 'slots', encodeURIComponent(new URL(fake.origin).host)); mkdirSync(directory, { recursive: true });
    writeFileSync(join(directory, 'busy.json'), JSON.stringify({ id: 'busy', state: 'active', pid: process.pid, kind: 'check', started_at: made.clock.now, request_ids: ['other'] }));
  } else fake.capacity = () => ({ status: 200, json: { maintenance: { until: new Date(made.clock.now + 600_000).toISOString(), reason: 'test window' } } });
  made.ports.sleep = async ms => { made.clock.now += interrupted ? ms : 90_000; if (interrupted) made.clock.interrupt(); };
  const code = await (kind === 'try' ? startTry(setup, made.ports) : check(setup, made.ports, kind === 'lint' ? { '--lint': true } : {}));
  assert.equal(code, interrupted && kind === 'check' ? 3 : 5); assert.equal(fake.posts.length, 0);
  const output = made.ports.stdout.text + made.ports.stderr.text; assert.match(output, new RegExp(reason)); assert.doesNotMatch(output, /after 0 lint attempts/);
  if (kind !== 'try') { const out = JSON.parse(made.ports.stdout.text); if (kind === 'check') assert.equal(out.rows[0].calls, 0); else assert.match(out.summary_line, /0 AI calls/); }
});

function memorySlots(made, origin) {
  const records = new Map(), refreshed = new Map(), directory = join(made.ports.env.PDD_STATE_DIR, 'slots', encodeURIComponent(new URL(origin).host));
  return { records, directory, files: {
    listRecords: () => ({ jobs: [...records.values()].filter(row => row.state).map(row => structuredClone(row)) }),
    exclusiveCreate: (path, record) => { if (records.has(path)) return false; records.set(path, structuredClone(record)); refreshed.set(path, made.clock.now); return true; },
    writeAtomic: (path, record) => { records.set(path, structuredClone(record)); refreshed.set(path, made.clock.now); }, unlink: path => records.delete(path),
    modifiedAt: path => records.has(path) ? refreshed.get(path) ?? null : null,
    touch: path => { if (!records.has(path)) return false; refreshed.set(path, made.clock.now); return true; },
  } };
}

test('lint-probe-deadline: Try dead-owner GET at 89950 is bounded by 50ms and no second GET or POST follows', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, () => { assert.fail('late lint posted'); }), made = make(setup, fake), start = made.clock.now;
  const mem = memorySlots(made, fake.origin); const realList = mem.files.listRecords; let moved = false, reads = 0, elapsed;
  for (const id of ['dead-a', 'dead-b']) mem.records.set(join(mem.directory, `${id}.json`), { id, state: 'active', pid: 99, kind: 'check', started_at: start, request_ids: [id] });
  mem.files.listRecords = () => { if (!moved) { moved = true; made.clock.now = start + 89_950; } return realList(); };
  made.ports.slotFiles = mem.files; made.ports.isAlive = pid => pid !== 99; made.ports.env.PDD_MAX_JOBS = '1';
  made.ports.fetch = async (url, init) => {
    if (new URL(url).pathname.startsWith('/v1/runs/')) {
      reads++; const at = performance.now();
      return new Promise((done, reject) => init.signal.addEventListener('abort', () => { elapsed = performance.now() - at; made.clock.now = start + 90_000; reject(Object.assign(Error('aborted'), { name: 'AbortError' })); }, { once: true }));
    }
    return fetch(url, init);
  };
  assert.equal(await startTry(setup, made.ports), 5); assert.equal(reads, 1); assert.ok(elapsed < 500, `${elapsed}ms exceeds phase GET bound`);
  assert.equal(made.clock.now, start + 90_000); assert.equal(fake.posts.length, 0); assert.equal([...mem.records.values()].filter(row => row.state).length, 2);
});

for (const interrupted of [false, true]) test(`lint-record-deadline: contended Try registration ends at 90000 (${interrupted ? 'interrupt' : 'deadline'})`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, () => { assert.fail('registration posted'); }), made = make(setup, fake), start = made.clock.now;
  const mem = memorySlots(made, fake.origin), create = mem.files.exclusiveCreate; let claims = 0;
  mem.files.exclusiveCreate = (path, row) => path.endsWith('claim.json') && ++claims > 1 ? false : create(path, row);
  made.ports.slotFiles = mem.files;
  made.ports.sleep = async () => { made.clock.now = start + 90_000; if (interrupted) made.clock.interrupt(); };
  assert.equal(await startTry(setup, made.ports), 5); assert.equal(made.clock.now, start + 90_000); assert.equal(fake.posts.length, 0);
  assert.equal([...mem.records.values()].filter(row => row.state).length, 0);
  assert.doesNotMatch(made.ports.stdout.text + made.ports.stderr.text, /after 0 lint attempts/);
});

test('capacity-cache: exact 10-second expiry reuses clear observations across public commands', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => f.normal(e)); let reads = 0;
  fake.capacity = () => { reads++; return { status: 200, json: { maintenance: null } }; };
  for (const [at, expected] of [[0, 1], [9999, 1], [10000, 2]]) {
    const made = make(setup, fake); made.clock.now = at;
    assert.equal(await check(setup, made.ports, { '--lint': true }), 0); assert.equal(reads, expected);
  }
});

test('capacity-cache-scope: concurrent reads coalesce, owner and exact origin isolate, refreshed maintenance pauses', async t => {
  const setup = harbor(t), second = harbor(t), fake = await fakeRuntime(t, (e, f) => f.normal(e)); let reads = 0, release;
  fake.capacity = async () => { reads++; await new Promise(done => release = done); return { status: 200, json: { maintenance: null } }; };
  const a = make(setup, fake), b = make(second, fake);
  const pending = Promise.all([check(setup, a.ports, { '--lint': true }), check(second, b.ports, { '--lint': true })]);
  while (!release) await new Promise(done => setImmediate(done)); release(); assert.deepEqual(await pending, [0, 0]); assert.equal(reads, 1);
  fake.capacity = () => { reads++; return { status: 200, json: { maintenance: null } }; };
  const other = make(setup, fake, { gh: args => args[0] === 'auth' ? { status: 0, stdout: 'different-token' } : { status: 0, stdout: 'another 555' } });
  assert.equal(await check(setup, other.ports, { '--lint': true }), 0); assert.equal(reads, 2);
  const anotherOrigin = await fakeRuntime(t, (e, f) => f.normal(e)); let otherReads = 0;
  anotherOrigin.capacity = () => { otherReads++; return { status: 200, json: { maintenance: null } }; };
  assert.equal(await check(setup, make(setup, anotherOrigin).ports, { '--lint': true }), 0); assert.equal(otherReads, 1);
  const later = make(setup, fake); later.clock.now += 10_000; const until = later.clock.now + 7000;
  fake.capacity = () => { reads++; return { status: 200, json: { maintenance: later.clock.now < until ? { until: new Date(until).toISOString(), reason: 'fresh maintenance' } : null } }; };
  assert.equal(await check(setup, later.ports, { '--lint': true }), 0); assert.equal(later.clock.now, until); assert.equal(maintenanceCount(later.ports), 1);
  assert.doesNotMatch(later.ports.stdout.text, /different-token|capacityCache/);
});

test('reuse-recovery-capture: a waiting replacement packs once despite repeated scheduler ticks', async t => {
  const setup = harbor(t); let captures = 0, checks = 0, made;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check') {
      checks++;
      if (checks === 1) return { status: 200, json: f.job(e.request.requestId, 'check', 'unknown', { refusals: [{ code: 'service-restarted' }] }, 2) };
      return { status: 200, json: f.check(e.request.requestId) };
    }
    return f.normal(e);
  });
  made = make(setup, fake, { captureSource: (...args) => { captures++; return captureSource(...args); } });
  let maintenanceReads = 0;
  fake.capacity = () => {
    if (checks === 1 && maintenanceReads++ < 3) return { status: 200, json: { maintenance: { until: new Date(made.clock.now + 20_000).toISOString(), reason: 'replacement waits' } } };
    return { status: 200, json: { maintenance: null } };
  };
  // Force refresh for replacement by expiring the normal clear observation.
  const fetchReal = made.ports.fetch ?? fetch;
  made.ports.fetch = async (url, init) => { const reply = await fetchReal(url, init); if (new URL(url).pathname === '/v1/check' && checks === 1) made.clock.now += 10_000; return reply; };
  assert.equal(await check(setup, made.ports, { '--max-calls': '9' }), 0);
  assert.equal(captures, 2); assert.equal(checks, 2); assert.ok(maintenanceReads >= 3);
  const posts = fake.posts.filter(e => e.command === 'check'); assert.ok(posts.every(e => e.request.max_calls === 9 && e.request.source_sha256 === posts[0].request.source_sha256));
});

test('later-recovery-revalidates: a new invocation recaptures changed source before allocating a replacement', async t => {
  const setup = harbor(t); let restart = false, captures = 0;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check') return { status: 202, json: f.check(e.request.requestId, 'running') };
    if (e.method === 'GET') return { status: 200, json: restart ? f.job(e.url.split('/').at(-1), 'check', 'unknown', { refusals: [{ code: 'service-restarted' }] }, 1) : f.check(e.url.split('/').at(-1), 'running') };
    return f.normal(e);
  });
  const first = make(setup, fake); assert.equal(await check(setup, first.ports), 3); const batch = JSON.parse(first.ports.stdout.text).batch;
  restart = true; writeFileSync(join(setup.repo, 'user_stories/place-order.md'), readFileSync(join(setup.repo, 'user_stories/place-order.md'), 'utf8') + '\nChanged after prior wait.\n');
  const later = make(setup, fake, { captureSource: (...args) => { captures++; return captureSource(...args); } }); later.clock.now = first.clock.now;
  assert.equal(await runCheck({ cwd: setup.repo, words: [batch], options: { '--read': true, '--json': true } }, later.ports), 3);
  assert.equal(captures, 1); assert.equal(fake.posts.filter(e => e.command === 'check').length, 1);
  assert.match(later.ports.stderr.text, /saved source changed/i);
});


test('command return stops heartbeat timers without freeing an uncertain paid lease', async t => {
  const setup = harbor(t), intervals = new Set();
  const fake = await fakeRuntime(t, (e, f) => e.command === 'check' || e.method === 'GET'
    ? { status: 202, json: f.check(e.request?.requestId ?? e.url.split('/').at(-1), 'running') } : f.normal(e));
  const made = make(setup, fake, { timers: { setInterval: fn => { intervals.add(fn); return fn; }, clearInterval: fn => intervals.delete(fn) } });
  assert.equal(await check(setup, made.ports), 3);
  assert.equal(intervals.size, 0);
  const jobs = (await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs;
  assert.equal(jobs.length, 1); assert.deepEqual(jobs[0].request_ids, [fake.posts.find(e => e.command === 'check').request.requestId]);
});
