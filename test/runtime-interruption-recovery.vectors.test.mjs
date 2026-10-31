import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor, TOKEN } from './runtime-fake.mjs';

const vectors = JSON.parse(readFileSync(new URL('./runtime-admission/runtime-interruption-recovery.json', import.meta.url)));
const read = path => JSON.parse(readFileSync(path));
const write = (path, value) => writeFileSync(path, JSON.stringify(value));
const checkPosts = fake => fake.posts.filter(e => e.command === 'check');
const checks = Array.from({ length: 17 }, (_, i) => ({ criterion_id: `AC${i % 4 + 1}`, target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: 900, passed: true }));
const capacity = (f, id) => f.job(id, 'check', 'refused', { outcome: 'Inconclusive', why: 'No verdict. Queue full.', next_step: 'STALE RETRY',
  refusals: [{ code: 'check-queue-timeout', details: { retryable: true, retry_after: 1 } }],
  report: { dispatch: 'not_started', provider_calls: 0, samples: [] } }, 0);
const passed = (f, id) => { const answer = f.check(id, 'passed', checks); answer.usage.calls = 4; return answer; };
async function fixture(t, answer) {
  const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => e.command === 'lint' ? { status: 200, json: f.lint(e.request.requestId) } : answer(e, f));
  const made = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  async function run(options = {}, extra = {}) {
    const next = portsFor(made.ports.env, { now: () => made.clock.now, sleep: made.ports.sleep, ...extra });
    const code = await runCheck({ cwd: setup.repo, words: options['--read'] ? [] : Object.keys(options).length ? [] : ['place-order'], options: { '--json': true, ...options } }, next.ports);
    const json = next.ports.stdout.text ? JSON.parse(next.ports.stdout.text) : null;
    return { code, json, err: next.ports.stderr.text, clock: next.clock, folder: json?.batch && join(setup.state, 'batches', json.batch) };
  }
  return { setup, fake, made, run };
}
function complete(result) {
  assert.equal(result.code, 0, result.err);
  const row = result.json.rows[0];
  assert.equal(row.state, 'passed'); assert.equal(row.calls, 4);
  assert.deepEqual(row.checks, { passed: 17, total: 17 }); assert.deepEqual(row.criteria, { passed: 4, total: 4 });
  assert.doesNotMatch(JSON.stringify(row), /Stopped before sending/);
}
function retained(result, fake, count) {
  const ids = checkPosts(fake).map(e => e.request.requestId);
  assert.equal(ids.length, count); assert.equal(new Set(ids).size, count);
  assert.deepEqual(read(join(result.folder, 'batch.json')).rows[0].request_ids, ids);
  for (const id of ids.slice(0, -1)) {
    assert.deepEqual(read(join(result.folder, `${id}.json`)), capacity(fake, id));
  }
  return ids;
}

for (const vector of vectors.cases) test(`RECONCILE ${vector.id}`, async t => {
  if (vector.id === 'fresh-interruption-with-claim-adoption') {
    const r = await fixture(t, (e, f) => ({ status: 200, json: passed(f, e.request?.requestId ?? e.url.split('/').at(-1)) }));
    const records = new Map(), times = new Map(); let target, interrupted = false;
    const directory = join(r.setup.state, 'slots', encodeURIComponent(new URL(r.fake.origin).host));
    const prior = { id: 'earlier-uncertain', state: 'active', pid: 99, kind: 'check', started_at: r.made.clock.now, request_ids: ['original-paid-id'] };
    records.set(join(directory, `${prior.id}.json`), prior); times.set(join(directory, `${prior.id}.json`), r.made.clock.now);
    const set = (path, value) => { records.set(path, structuredClone(value)); times.set(path, r.made.clock.now); };
    const slotFiles = {
      listRecords: () => ({ jobs: [...records.values()].filter(row => row.state).map(row => structuredClone(row)) }),
      exclusiveCreate: (path, row) => { if (records.has(path)) return false; set(path, row); return true; },
      writeAtomic: (path, row) => { set(path, row); if (!interrupted && row.kind === 'check' && row.request_ids.length) { interrupted = true; target = path; r.made.clock.interrupt(); } },
      unlink: path => { records.delete(path); times.delete(path); }, modifiedAt: path => times.get(path) ?? null,
      touch: path => { if (!records.has(path)) return false; times.set(path, r.made.clock.now); return true; },
    };
    // Use the live invocation's signal subscription; private batch/claim files remain real.
    const result = await r.run({}, { slotFiles, isAlive: () => true, onInterrupt: r.made.ports.onInterrupt });
    assert.equal(interrupted, true); assert.equal(result.code, 3);
    assert.equal(checkPosts(r.fake).length, 0);
    const saved = read(join(result.folder, 'batch.json')), row = result.json.rows[0];
    const claim = read(join(result.folder, readdirSync(result.folder).find(name => name.endsWith('.dispatch.json'))));
    assert.deepEqual(saved.rows[0].request_ids, [claim.id]); assert.equal(row.request_id, claim.id);
    assert.equal(row.calls, 'unknown'); assert.equal(row.busy, false); assert.equal(row.can_retry, false);
    assert.equal(records.has(target), false); assert.deepEqual([...records.values()].filter(row => row.state), [prior]);
    assert.equal(row.reason.message, 'Stopped before sending.');
    return;
  }
  if (vector.id === 'older-ambiguous-save' || vector.id === 'later-verified-receipt') {
    for (const cache of vector.id === 'older-ambiguous-save' ? ['missing', 'unreadable', 'wrong-id'] : ['verified']) await t.test(cache, async t => {
      let recovering = false;
      const r = await fixture(t, (e, f) => recovering && cache !== 'verified'
        ? { status: 410, json: { error: { code: 'expired' } } }
        : { status: 200, json: passed(f, e.request?.requestId ?? e.url.split('/').at(-1)) });
      const initial = await r.run(), file = join(initial.folder, 'batch.json'), saved = read(file), id = saved.rows[0].request_ids[0];
      Object.assign(saved.rows[0], { request_ids: [], phase: 'local', state: 'not_run', calls: 0, note: { message: 'Stopped before sending.' }, why: 'STALE RETRY', next_step: 'STALE RETRY', busy: true, can_retry: true });
      write(file, saved); const raw = join(initial.folder, `${id}.json`);
      if (cache === 'missing') rmSync(raw);
      if (cache === 'unreadable') writeFileSync(raw, '{broken');
      if (cache === 'wrong-id') { const answer = read(raw); answer.id = 'wrong-id'; write(raw, answer); }
      recovering = true; const posts = r.fake.posts.length;
      for (const options of [{ '--read': initial.json.batch }, { '--retry': initial.json.batch }]) {
        const result = await r.run(options);
        assert.equal(r.fake.posts.length, posts); assert.equal(result.clock.uuids, 0);
        assert.deepEqual(read(file).rows[0].request_ids, [id]);
        if (cache === 'verified') { complete(result); assert.deepEqual(read(raw), passed(r.fake, id)); }
        else {
          assert.equal(result.code, 3); const row = result.json.rows[0];
          assert.equal(row.request_id, id); assert.equal(row.calls, 'unknown'); assert.equal(row.busy, false); assert.equal(row.can_retry, false);
          assert.doesNotMatch(JSON.stringify(row), /Stopped before sending|STALE RETRY/);
          assert.ok(r.fake.gets.every(e => e.url.endsWith(id)));
        }
      }
    });
    return;
  }
  if (vector.id === 'same-process-retries-with-bookkeeping') {
    let hold = false, entered, resume;
    const boundary = new Promise(done => entered = done), release = new Promise(done => resume = done); t.after(() => resume());
    const r = await fixture(t, async (e, f) => { if (hold && e.command === 'check') { entered(); await release; } return { status: 200, json: passed(f, e.request?.requestId ?? e.url.split('/').at(-1)) }; });
    const first = await r.run(), file = join(first.folder, 'batch.json'), saved = read(file);
    for (const name of readdirSync(first.folder).filter(name => name.endsWith('.dispatch.json'))) rmSync(join(first.folder, name));
    Object.assign(saved.rows[0], { request_ids: [], phase: 'local', state: 'not_run', busy: true, can_retry: true, eligible: true, retry_at: null }); write(file, saved);
    hold = true; const before = checkPosts(r.fake).length, owner = r.run({ '--retry': first.json.batch }); await boundary;
    const bytes = readFileSync(file), summary = readFileSync(join(first.folder, 'summary.json')), traffic = [r.fake.gets.length, r.fake.posts.length];
    const contender = await r.run({ '--retry': first.json.batch });
    assert.equal(contender.code, 3); assert.equal(contender.clock.uuids, 0); assert.match(contender.err, /pdd test --read/);
    assert.deepEqual([r.fake.gets.length, r.fake.posts.length], traffic); assert.deepEqual(readFileSync(file), bytes); assert.deepEqual(readFileSync(join(first.folder, 'summary.json')), summary);
    resume(); const result = await owner; complete(result);
    assert.equal(checkPosts(r.fake).length - before, 1);
    const id = checkPosts(r.fake).at(-1).request.requestId;
    assert.deepEqual(read(file).rows[0].request_ids, [id]); assert.deepEqual(read(join(first.folder, `${id}.json`)), passed(r.fake, id));
    assert.equal(read(join(first.folder, 'summary.json')).rows[0].calls, 4);
    complete(await r.run({ '--read': first.json.batch })); assert.equal(checkPosts(r.fake).length - before, 1);
    return;
  }
  let posts = 0, lastAt, stop; const postTimes = [];
  const r = await fixture(t, (e, f) => {
    if (e.method === 'GET') return { status: 410, json: { error: { code: 'expired' } } };
    posts++; lastAt = r.made.clock.now; postTimes.push(lastAt);
    if (vector.id === 'more-than-three-busy-attempts' && posts === 5) return { status: 200, json: passed(f, e.request.requestId) };
    if (posts === 2 && vector.id === 'busy-then-lost') return { destroy: true };
    if (posts === 2 && vector.id === 'busy-then-fresh-refusal') return { status: 422, json: { error: { code: 'source-too-large', message: 'Source too large.', reason: `NEW REASON ${TOKEN} /srv/private/reason`, fix: `NEW FIX ${TOKEN} /srv/private/fix`, hint: `NEW HINT ${TOKEN} /srv/private/hint`, cause: 'test' } } };
    return { status: 200, headers: { 'retry-after': '1' }, json: capacity(f, e.request.requestId) };
  });
  const start = r.made.clock.now, sleeps = [];
  const result = await r.run({}, { onInterrupt: handler => { stop = handler; return () => {}; }, sleep: async ms => {
    sleeps.push(ms); r.made.clock.now += ms;
    if (vector.id === 'busy-interruption' && posts >= 4) stop();
  } });
  for (let index = 1; index < postTimes.length; index++) assert.ok(postTimes[index] - postTimes[index - 1] >= 10_000, 'Check busy minimum backoff');
  const ids = retained(result, r.fake, posts), row = result.json.rows[0];
  assert.doesNotMatch(JSON.stringify(result.json), /STALE RETRY/);
  if (vector.id === 'more-than-three-busy-attempts') { assert.equal(posts, 5); assert.ok(lastAt - start >= 40_000); complete(result); }
  else if (vector.id === 'busy-caller-deadline') {
    assert.ok(posts > 3 && posts <= 10); assert.equal(result.code, 5); assert.equal(row.state, 'not_run'); assert.equal(row.calls, 0); assert.equal(row.busy, true);
    assert.equal(r.made.clock.now - start, 90_000); assert.match(row.reason.message, /busy|No checks ran/i);
  } else if (vector.id === 'busy-interruption') {
    assert.ok(posts > 3); assert.equal(result.code, 3); assert.ok(r.made.clock.now - start < 90_000);
    assert.match(result.err + JSON.stringify(result.json), /Stopped\./); assert.doesNotMatch(result.err + JSON.stringify(result.json), /Stopped before sending|wait ended|until the timeout/);
  } else {
    assert.equal(posts, 2); assert.equal(result.code, vector.id === 'busy-then-lost' ? 3 : 4);
    assert.equal(row.busy, false); assert.equal(row.can_retry, false); assert.equal(row.next_step, null);
    if (vector.id === 'busy-then-lost') assert.equal(row.calls, 'unknown');
    else {
      const refusal = row.refusals[0]; assert.equal(refusal.code, 'source-too-large');
      for (const key of ['reason', 'fix', 'hint']) assert.match(refusal[key], /NEW .*\[secret\] <server path>/);
      assert.equal(refusal.cause, 'test'); assert.doesNotMatch(JSON.stringify(result.json), /gho_TESTTOKEN|\/srv\/private/);
    }
  }
  const count = [r.fake.posts.length, result.clock.uuids], gets = r.fake.gets.length;
  const later = await r.run({ '--read': result.json.batch });
  assert.equal(r.fake.posts.length, count[0]); assert.equal(later.clock.uuids, 0); assert.deepEqual(read(join(result.folder, 'batch.json')).rows[0].request_ids, ids);
  assert.doesNotMatch(JSON.stringify(later.json), /STALE RETRY/);
  if (vector.id === 'busy-then-fresh-refusal') { assert.equal(later.code, 4); assert.equal(r.fake.gets.length, gets); }
  if (vector.id === 'busy-then-lost') { assert.equal(later.code, 3); assert.ok(r.fake.gets.every(e => e.url.endsWith(ids[1]))); assert.match(JSON.stringify(later.json), /expired/i); }
  assert.ok(sleeps.every(ms => ms > 0 && ms <= 90_000));
});
