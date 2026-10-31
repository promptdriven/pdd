import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync, readdirSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor, TOKEN } from './runtime-fake.mjs';

const vectors = JSON.parse(readFileSync(new URL('./runtime-admission/runtime-busy-upload-wait.json', import.meta.url)));
const read = path => JSON.parse(readFileSync(path));
const posts = f => f.posts.filter(e => e.command === 'check');
const full = (running = 4, limit = 4) => ({ status: 200, json: { maintenance: null, slots: { check: { running, limit, waiting: 0 } } } });
const absent = () => ({ status: 404, json: { error: { code: 'not-found' } } });
const busy = (f, id) => f.job(id, 'check', 'refused', { refusals: [{ code: 'check-queue-timeout', details: { retryable: true, retry_after: 1 } }], report: { dispatch: 'not_started', provider_calls: 0, samples: [] } }, 0);
const pass = (f, id) => { const answer = f.check(id); answer.usage.calls = 4; return answer; };
async function fixture(t, { capacity = absent, answer, interruptAt = Infinity } = {}) {
  const setup = harbor(t), times = [], receipts = new Map(), sleeps = [], observations = [];
  let made, start, stopAt = interruptAt, seededClaims = 0;
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint') return { status: 200, json: f.lint(e.request.requestId) };
    if (e.command === 'check') times.push(made.clock.now - start);
    const reply = answer ? answer(e, f, times.length) : { status: 200, headers: { 'retry-after': '1' }, json: busy(f, e.request?.requestId ?? e.url.split('/').at(-1)) };
    if (e.command === 'check' && reply.json) receipts.set(e.request.requestId, structuredClone(reply.json));
    return reply;
  });
  made = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }); start = made.clock.now;
  const folder = () => { const root = join(setup.state, 'batches'); return existsSync(root) ? readdirSync(root).map(name => join(root, name)).find(path => existsSync(join(path, 'batch.json'))) : null; };
  const waitingOnly = () => {
    const path = folder();
    if (path && posts(fake).length) assert.equal(readdirSync(path).filter(name => name.endsWith('.dispatch.json')).length, posts(fake).length - seededClaims, 'waiting creates no dispatch claim');
  };
  fake.capacity = e => {
    assert.equal(e.headers.authorization, `Bearer ${TOKEN}`);
    const slots = join(setup.state, 'slots', encodeURIComponent(new URL(fake.origin).host));
    if (existsSync(slots)) assert.equal(readdirSync(slots).some(name => /^\.claim-.*\.lock$/.test(name)), false, 'capacity GET is outside local claim');
    observations.push(made.clock.now - start); waitingOnly();
    return capacity(made.clock.now - start, posts(fake).length);
  };
  async function run(options = {}, extra = {}) {
    const commandAt = made.clock.now;
    const next = portsFor(made.ports.env, { now: () => made.clock.now, onInterrupt: made.ports.onInterrupt,
      sleep: async ms => { waitingOnly(); sleeps.push(ms); const step = Math.min(ms, Math.max(0, start + stopAt - made.clock.now)); made.clock.now += step;
        if (made.clock.now >= start + stopAt) made.clock.interrupt(); await new Promise(done => setImmediate(done)); }, ...extra });
    const code = await runCheck({ cwd: setup.repo, words: options['--read'] ? [options['--read']] : options['--retry'] ? [] : ['place-order'], options: { '--json': true, ...options } }, next.ports);
    const json = next.ports.stdout.text ? JSON.parse(next.ports.stdout.text) : null;
    return { code, json, err: next.ports.stderr.text, folder: json?.batch ? join(setup.state, 'batches', json.batch) : folder(), elapsed: made.clock.now - commandAt };
  }
  return { setup, fake, made, start, times, sleeps, observations, receipts, run, resetSeedClaims: () => { seededClaims = posts(fake).length; }, setInterrupt: at => { stopAt = at; }, setTime: at => { made.clock.now = start + at; } };
}
function history(r, result) {
  const actual = posts(r.fake), ids = actual.map(e => e.request.requestId), saved = read(join(result.folder, 'batch.json'));
  assert.equal(new Set(ids).size, ids.length); assert.deepEqual(saved.rows[0].request_ids, ids);
  assert.ok(actual.every(e => e.tar.equals(actual[0].tar) && e.request.source_sha256 === actual[0].request.source_sha256 && e.request.max_calls === actual[0].request.max_calls));
  for (const [id, receipt] of r.receipts) assert.deepEqual(read(join(result.folder, `${id}.json`)), receipt);
  assert.ok(r.sleeps.every(ms => ms > 0 && ms <= 60_000));
  return saved;
}
function spaced(r) { for (let i = 1; i < r.times.length; i++) assert.ok(r.times[i] - r.times[i - 1] >= 10_000, 'busy uploads are at least 10 seconds apart'); }
function completed(result) { assert.equal(result.code, 0, result.err); assert.equal(result.json.rows[0].state, 'passed'); assert.equal(result.json.rows[0].calls, 4); }

for (const vector of vectors.cases) test(`BUSY-WAIT ${vector.id}`, async t => {
  if (vector.id === 'fallback-upload-rate' || vector.id === 'four-busy-then-pass') {
    const success = vector.id === 'four-busy-then-pass';
    const r = await fixture(t, { answer: (e, f, count) => success && count === 5 ? { status: 200, json: pass(f, e.request.requestId) }
      : { status: 200, headers: { 'retry-after': '1' }, json: busy(f, e.request.requestId) } });
    const result = await r.run();
    if (success) { completed(result); assert.equal(r.times.length, 5); assert.ok(r.times[4] >= 40_000); }
    else { assert.ok(r.times.length > 3 && r.times.length <= 10, `90s upload bound: ${r.times.length}`); assert.equal(result.code, 5); assert.equal(result.json.rows[0].calls, 0); assert.equal(result.json.rows[0].busy, true); assert.equal(r.made.clock.now - r.start, 90_000); }
    spaced(r); assert.ok(r.times.every(at => at < 90_000)); history(r, result); return;
  }
  if (['longer-advice', 'full-then-free', 'full-hold-bound', 'zero-limit-full'].includes(vector.id)) {
    const expected = vector.id === 'longer-advice' ? 75_000 : vector.id === 'full-then-free' ? 30_000 : 60_000;
    const r = await fixture(t, { capacity: at => vector.id === 'zero-limit-full' ? full(0, 0) : full(at >= 30_000 && vector.id === 'full-then-free' ? 3 : 4),
      answer: (e, f, count) => count === 1 ? { status: 200, headers: { 'retry-after': vector.id === 'longer-advice' ? '75' : '1' }, json: busy(f, e.request.requestId) } : { status: 200, json: pass(f, e.request.requestId) } });
    const result = await r.run(); completed(result); assert.equal(r.times.length, 2); assert.ok(r.times[1] >= expected, `next upload >= ${expected}, got ${r.times[1]}`);
    assert.ok(r.times[1] < (vector.id === 'full-then-free' ? 60_000 : 90_000)); history(r, result);
    if (vector.id === 'full-then-free') await t.test('capacity-refills-during-local-wait', async t => {
      let competitor, path, released = false;
      const local = await fixture(t, { capacity: at => {
        if (at === 30_000 && !competitor) {
          path = join(local.setup.state, 'slots', encodeURIComponent(new URL(local.fake.origin).host), 'competing-paid.json');
          competitor = { id: 'competing-paid', state: 'active', pid: process.pid, kind: 'check', started_at: local.made.clock.now, request_ids: ['uncertain-other'] };
          writeFileSync(path, JSON.stringify(competitor), { mode: 0o600 });
        }
        return full(at === 30_000 ? 3 : 4);
      }, answer: (e, f, count) => ({ status: 200, headers: { 'retry-after': '1' }, json: count === 1 ? busy(f, e.request.requestId) : pass(f, e.request.requestId) }) });
      local.made.ports.env.PDD_MAX_JOBS = '1';
      const result = await local.run({}, { sleep: async ms => {
        local.sleeps.push(ms); local.made.clock.now += ms;
        if (competitor && !released && local.made.clock.now - local.start >= 45_000) {
          assert.deepEqual(read(path), competitor, 'local waiting preserves the competing uncertain paid lease');
          rmSync(path); released = true;
        }
        await new Promise(done => setImmediate(done));
      } });
      completed(result); assert.equal(released, true); assert.equal(local.times.length, 2);
      assert.ok(local.times[1] >= 60_000 && local.times[1] < 90_000, 'full occupancy after local wait still holds the upload'); history(local, result);
    });
    return;
  }
  if (vector.id === 'absent-unusable-occupancy') {
    for (const kind of ['404', 'absent', 'malformed', 'unclear']) await t.test(kind, async t => {
      const r = await fixture(t, { capacity: () => kind === '404' ? absent() : kind === 'absent' ? { status: 200, json: { maintenance: null } } : kind === 'malformed' ? full('bad', -1) : { status: 503, json: { error: { code: 'unrecognized' } } },
        answer: (e, f, n) => ({ status: 200, headers: { 'retry-after': '1' }, json: n === 1 ? busy(f, e.request.requestId) : pass(f, e.request.requestId) }) });
      const result = await r.run(); completed(result); assert.equal(r.times.length, 2); assert.ok(r.times[1] >= 10_000 && r.times[1] < 60_000); history(r, result);
      assert.ok((result.err.match(/Warning: interpreter capacity could not be read/g) ?? []).length <= 1);
    }); return;
  }
  if (vector.id === 'short-deadline') {
    for (const [end, usable] of [[9000, false], [45_000, true]]) await t.test(`${end}ms`, async t => {
      const r = await fixture(t, { capacity: () => usable ? full() : absent() });
      const result = await r.run({ '--timeout': String(end / 60_000) });
      assert.equal(result.code, 5); assert.equal(r.times.length, 1); assert.equal(result.json.rows[0].calls, 0); history(r, result);
    }); return;
  }
  if (vector.id === 'interrupt-capacity-wait' || vector.id === 'maintenance-precedence') {
    const interrupt = vector.id === 'interrupt-capacity-wait';
    const r = await fixture(t, { capacity: (_, count) => !interrupt && count ? { status: 200, json: { ...full().json, maintenance: { until: new Date(r.start + 120_000).toISOString(), reason: 'Scheduled work' } } } : full(), interruptAt: interrupt ? 15_000 : Infinity });
    const result = await r.run(); assert.equal(result.code, interrupt ? 3 : 5); assert.equal(r.times.length, 1); assert.equal(result.json.rows[0].calls, 0); history(r, result);
    if (interrupt) { assert.equal(r.made.clock.now - r.start, 15_000); assert.match(result.err + JSON.stringify(result.json), /Stopped\./); assert.doesNotMatch(result.err + JSON.stringify(result.json), /Stopped before sending|wait ended|until the timeout/); }
    else { assert.equal(r.made.clock.now - r.start, 90_000); assert.match(result.err, /maintenance|Scheduled work/i); } return;
  }
  if (vector.id === 'access-precedence') {
    for (const [status, code, message] of [[401, 'unauthorized', /gh auth login/], [403, 'no-cloud-access', /access yet/], [403, 'not-invited', /invite list/], [503, 'cloud-unavailable', /confirm your access/], [426, 'update-required', /update pdd/]]) await t.test(code, async t => {
      const r = await fixture(t, { capacity: (_, count) => count ? { status, json: { error: { code } } } : full() });
      const result = await r.run(); assert.equal(result.code, 5); assert.equal(r.times.length, 1); assert.match(result.err, message); history(r, result);
    }); return;
  }
  if (vector.id === 'saved-retry-times') {
    for (const kind of ['full', 'unsupported', '75seconds']) await t.test(kind, async t => {
      const minimum = kind === '75seconds' ? 75_000 : 10_000;
      const r = await fixture(t, { capacity: () => kind === 'unsupported' ? absent() : full(), interruptAt: 5000,
        answer: (e, f, count) => ({ status: 200, headers: { 'retry-after': kind === '75seconds' ? '75' : '1' }, json: count === 1 ? busy(f, e.request.requestId) : pass(f, e.request.requestId) }) });
      const first = await r.run({}, { pollMs: 5000 }); assert.equal(first.code, 3); assert.equal(r.times.length, 1); const saved = history(r, first), before = structuredClone(saved.rows[0]);
      assert.equal(before.retry_at, r.start + minimum); assert.equal(before.capacity_until, r.start + 60_000);
      r.setInterrupt(Infinity); r.setTime(7000); const later = await r.run({ '--read': first.json.batch }); assert.equal(r.times.length, 1);
      const afterRead = read(join(first.folder, 'batch.json')); assert.equal(afterRead.rows[0].retry_at, before.retry_at); assert.equal(afterRead.rows[0].capacity_until, before.capacity_until);
      r.setTime(kind === 'unsupported' ? 8000 : 20_000); const result = await r.run({ '--retry': first.json.batch }); completed(result); assert.equal(r.times.length, 2);
      assert.ok(r.times[1] >= (kind === 'full' ? 60_000 : minimum)); assert.ok(r.times[1] < (kind === 'full' ? 80_000 : minimum + 10_000)); history(r, result);
      assert.equal(afterRead.source_sha256, saved.source_sha256); assert.equal(later.json.rows[0].can_retry, true);
    }); return;
  }
  if (vector.id === 'legacy-busy-timing-anchor') {
    for (const [longer, advice] of [[false, 1], [false, 75], [false, 300], [true, 1]]) await t.test(longer ? 'later-saved-delay' : `short-saved-delay-advice-${advice}`, async t => {
      const r = await fixture(t, { capacity: () => full(), interruptAt: 5000,
        answer: (e, f, count) => { const id = e.request?.requestId ?? e.url.split('/').at(-1), json = count === 1 ? busy(f, id) : pass(f, id);
          if (count === 1) json.result.refusals[0].details.retry_after = advice;
          return { status: 200, headers: { 'retry-after': '300' }, json }; } });
      const first = await r.run({}, { pollMs: 5000 }); assert.equal(r.times.length, 1);
      const path = join(first.folder, 'batch.json'), saved = read(path), row = saved.rows[0];
      row.retry_at = r.start + (longer ? 95_000 : 1000); row.sent_at = r.start - 100_000;
      delete row.busy_observed_at; delete row.capacity_until; delete row.busy_request_id;
      writeFileSync(path, JSON.stringify(saved)); r.setInterrupt(Infinity); r.setTime(20_000);
      const rawBefore = readFileSync(path), id = row.request_ids[0];
      const uuidRead = await r.run({ '--read': id });
      assert.equal(uuidRead.json.rows[0].request_id, id);
      assert.ok(r.fake.gets.some(entry => entry.url === `/v1/runs/${id}`), 'UUID read uses the original owner run');
      assert.equal(read(join(first.folder, `${id}.json`)).id, id);
      assert.deepEqual(readFileSync(path), rawBefore, 'UUID read never repairs batch metadata');
      const observed = await r.run({ '--read': first.json.batch }); assert.equal(r.times.length, 1); assert.equal(observed.json.rows[0].calls, 0);
      const anchored = read(path).rows[0]; assert.equal(anchored.retry_at, r.start + (longer ? 95_000 : 30_000)); assert.equal(anchored.capacity_until, r.start + 80_000);
      r.setTime(40_000); await r.run({ '--read': first.json.batch });
      assert.equal(read(path).rows[0].retry_at, anchored.retry_at); assert.equal(read(path).rows[0].capacity_until, anchored.capacity_until);
      const result = await r.run({ '--retry': first.json.batch }); completed(result); assert.equal(r.times.length, 2);
      assert.ok(r.times[1] >= (longer ? 95_000 : 80_000)); assert.ok(r.times[1] < (longer ? 105_000 : 100_000)); history(r, result);
    });
    await t.test('never-posted-held-control', async t => {
      const r = await fixture(t, { capacity: () => full(), answer: (e, f) => ({ status: 200, json: pass(f, e.request.requestId) }) });
      const initial = await r.run(), path = join(initial.folder, 'batch.json'), saved = read(path);
      Object.assign(saved.rows[0], { request_ids: [], phase: 'local', state: 'not_run', calls: 0, busy: false, can_retry: true, eligible: true, retry_at: null });
      delete saved.rows[0].busy_observed_at; delete saved.rows[0].capacity_until; delete saved.rows[0].busy_request_id;
      for (const name of readdirSync(initial.folder).filter(name => name.endsWith('.dispatch.json'))) rmSync(join(initial.folder, name));
      r.resetSeedClaims();
      writeFileSync(path, JSON.stringify(saved)); r.setTime(40_000);
      const result = await r.run({ '--retry': initial.json.batch }); completed(result); assert.equal(r.times.length, 2); assert.equal(r.times[1], 40_000, 'held first send has no busy cooldown');
    }); return;
  }
  if (vector.id === 'unknown-is-not-busy') {
    for (const kind of ['lost', 'wrong-id', 'wrong-command', 'unknown-calls', 'positive-calls', 'evaluated', 'incomplete', 'expired']) await t.test(kind, async t => {
      const r = await fixture(t, { capacity: () => full(0), answer: (e, f) => {
        if (e.method === 'GET') return { status: 410, json: { error: { code: 'expired' } } };
        if (kind === 'lost' || kind === 'expired') return { destroy: true };
        const answer = busy(f, e.request.requestId);
        if (kind === 'wrong-id') answer.id = 'wrong'; if (kind === 'wrong-command') answer.command = 'lint';
        if (kind === 'unknown-calls') answer.usage.calls = 'unknown'; if (kind === 'positive-calls') answer.usage.calls = 2;
        if (kind === 'evaluated') answer.result.report.samples = [{ steps: [{ checks: [{ passed: true, criterion_id: 'AC1' }] }] }];
        if (kind === 'incomplete') answer.result.report.accounting_complete = false;
        return { status: 200, json: answer };
      } });
      const initial = await r.run(); assert.equal(r.times.length, 1); assert.equal(initial.json.rows[0].can_retry, false);
      for (const options of [{ '--read': initial.json.batch }, { '--retry': initial.json.batch }]) { const result = await r.run(options); assert.equal(r.times.length, 1); assert.equal(result.json.rows[0].can_retry, false); }
      assert.ok(r.fake.gets.every(e => e.url.endsWith(posts(r.fake)[0].request.requestId)));
    }); return;
  }
  assert.fail(`Unmapped approved case: ${vector.id}`);
});
