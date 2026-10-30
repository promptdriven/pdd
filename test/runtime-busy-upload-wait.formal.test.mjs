import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor, TOKEN } from './runtime-fake.mjs';

// Independent oracle: approved runtime-busy-upload-wait Story, Rules to check,
// and the person's legacy-timing decision. This finite public-boundary check
// covers 4 advice values x 7 occupancy worlds, plus delayed answers, stopping,
// persisted timing and replay authority. It is not an unbounded/concurrency or
// live Runtime proof. Expectations were recorded before implementation review.
const ORIGIN = Date.parse('2026-10-27T16:27:47Z');
const checks = fake => fake.posts.filter(entry => entry.command === 'check');
const load = path => JSON.parse(readFileSync(path, 'utf8'));
const occupancy = (running = 4, limit = 4) => ({ status: 200,
  json: { maintenance: null, slots: { check: { running, limit, waiting: 0 } } } });
const unsupported = () => ({ status: 404, json: { error: { code: 'not-found' } } });
const modes = ['404', 'absent', 'malformed', 'full', 'zero', 'free', 'free-later'];
function observation(mode, elapsed) {
  if (mode === '404') return unsupported();
  if (mode === 'absent') return { status: 200, json: { maintenance: null } };
  if (mode === 'malformed') return occupancy('unknown', -1);
  if (mode === 'zero') return occupancy(0, 0);
  return occupancy(mode === 'free' || (mode === 'free-later' && elapsed >= 30_000) ? 3 : 4);
}
function earliest(advice, mode, answerAt = 0) {
  const minimum = answerAt + Math.max(10_000, advice * 1000);
  const release = ['full', 'zero'].includes(mode) ? answerAt + 60_000
    : mode === 'free-later' ? Math.min(30_000, answerAt + 60_000) : answerAt;
  return Math.max(minimum, release);
}
function refused(fake, id, advice) {
  const refusal = { code: 'check-queue-timeout', details: { retryable: true, retry_after: advice } };
  return fake.job(id, 'check', 'refused', { refusals: [refusal], report: {
    dispatch: 'not_started', provider_calls: 0, samples: [], refusal,
  } }, 0);
}

async function world(t, { advice = 1, mode = '404', delay = 0, repeat = false, capacity, receipt } = {}) {
  const setup = harbor(t), traffic = [], answers = new Map(), capacityTimes = [];
  let clock, interruptAt = Infinity, firstAnswerAt;
  const fake = await fakeRuntime(t, (entry, server) => {
    if (entry.command === 'lint') return { status: 200, json: server.lint(entry.request.requestId) };
    if (entry.command !== 'check') {
      const answer = answers.get(entry.url.split('/').at(-1));
      return answer ? { status: 200, json: answer } : { status: 410, json: { error: { code: 'expired' } } };
    }
    const index = traffic.push(clock.now - ORIGIN);
    if (index === 1) { clock.now += delay; firstAnswerAt = clock.now - ORIGIN; }
    let json = index === 1 || repeat ? refused(server, entry.request.requestId, advice) : server.check(entry.request.requestId);
    if (receipt) json = receipt(json, entry, server);
    if (json === null) return { destroy: true };
    answers.set(entry.request.requestId, structuredClone(json));
    return { status: 200, headers: { 'retry-after': String(advice) }, json };
  });
  const base = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  clock = base.clock; clock.now = ORIGIN;
  const statePath = batch => join(setup.state, 'batches', batch, 'batch.json');
  function waitingEffects() {
    const batches = join(setup.state, 'batches');
    if (!existsSync(batches)) return;
    for (const batch of readdirSync(batches)) {
      const folder = join(batches, batch);
      assert.ok(readdirSync(folder).filter(name => name.endsWith('.dispatch.json')).length <= checks(fake).length,
        'waiting cannot create an unposted dispatch claim');
      if (traffic.length && existsSync(join(folder, 'batch.json'))) {
        const ids = load(join(folder, 'batch.json')).rows.flatMap(row => row.request_ids ?? []);
        assert.ok(ids.length <= checks(fake).length, 'waiting cannot allocate a new Check attempt identity');
      }
    }
  }
  fake.capacity = entry => {
    assert.equal(entry.headers.authorization, `Bearer ${TOKEN}`);
    const slots = join(setup.state, 'slots', encodeURIComponent(new URL(fake.origin).host));
    if (existsSync(slots)) assert.ok(!readdirSync(slots).some(name => /^\.claim-.*\.lock$/.test(name)),
      'capacity observations cannot hold a local claim lock');
    waitingEffects(); capacityTimes.push(clock.now - ORIGIN);
    return capacity ? capacity(clock.now - ORIGIN, traffic.length) : observation(mode, clock.now - ORIGIN);
  };
  async function invoke(options = {}) {
    const made = portsFor(base.ports.env, { now: () => clock.now, onInterrupt: base.ports.onInterrupt,
      sleep: async ms => {
        assert.ok(ms > 0 && ms <= 60_000, 'bounded positive wait'); waitingEffects();
        clock.now = Math.min(clock.now + ms, ORIGIN + interruptAt);
        if (clock.now >= ORIGIN + interruptAt) clock.interrupt();
        await new Promise(resolve => setImmediate(resolve));
      } });
    const words = options['--retry'] ? [] : options['--read'] ? [options['--read']] : ['place-order'];
    const parsed = { '--json': true, ...(!options['--read'] && !options['--retry'] ? { '--max-calls': '9' } : {}), ...options };
    if (parsed['--read']) parsed['--read'] = true;
    const code = await runCheck({ cwd: setup.repo, words, options: parsed }, made.ports);
    return { code, json: made.ports.stdout.text ? JSON.parse(made.ports.stdout.text) : null, err: made.ports.stderr.text };
  }
  function history(result) {
    // Access refusals retain their stderr/exit behavior and may have no JSON.
    // Inspect the durable batch rather than requiring a new output contract.
    const batches = readdirSync(join(setup.state, 'batches')).filter(name => existsSync(statePath(name)));
    assert.equal(batches.length, 1, 'the fixture creates exactly one durable batch');
    const batchName = result.json?.batch ?? batches[0];
    const sent = checks(fake), ids = sent.map(entry => entry.request.requestId), batch = load(statePath(batchName));
    assert.equal(new Set(ids).size, ids.length, 'only actual attempts get distinct dispatch identities');
    assert.deepEqual(batch.rows[0].request_ids, ids, 'retain every posted identity');
    for (const entry of sent) {
      assert.equal(entry.request.max_calls, 9);
      assert.equal(entry.request.source_sha256, batch.source_sha256);
      assert.ok(entry.tar.equals(sent[0].tar), 'retry keeps exact captured source');
    }
    for (const [id, answer] of answers) assert.deepEqual(load(join(setup.state, 'batches', batchName, `${id}.json`)), answer);
    return batch;
  }
  return { setup, fake, traffic, capacityTimes, invoke, history, statePath,
    elapsed: () => clock.now - ORIGIN, answerAt: () => firstAnswerAt,
    time: elapsed => { clock.now = ORIGIN + elapsed; }, interrupt: elapsed => { interruptAt = elapsed; } };
}

test('formal busy uploads: every advice/occupancy pair obeys independent timing and traffic oracle (28 worlds)', async t => {
  let count = 0;
  for (const advice of [1, 10, 30, 75]) for (const mode of modes) await t.test(`${advice}s ${mode}`, async t => {
    const w = await world(t, { advice, mode });
    const result = await w.invoke();
    assert.equal(result.code, 0, result.err); assert.equal(result.json.rows[0].state, 'passed');
    assert.equal(w.traffic.length, 2, 'one refused upload and one successful upload');
    const bound = earliest(advice, mode);
    assert.ok(w.traffic[1] >= bound, `next upload ${w.traffic[1]} must be >= ${bound}`);
    assert.ok(w.traffic[1] < (mode === 'free-later' && advice <= 30 ? 60_000 : 90_000),
      'permissive gates admit within the approved finite caller wait');
    assert.equal(result.json.rows[0].calls, 1); w.history(result); count++;
  });
  assert.equal(count, 28);
});

for (const mode of ['404', 'full']) test(`formal busy answer time, not POST start, anchors ${mode} wait`, async t => {
  const w = await world(t, { mode, delay: 7000 });
  const result = await w.invoke();
  assert.equal(result.code, 0, result.err); assert.equal(w.answerAt(), 7000);
  assert.equal(w.traffic.length, 2);
  const bound = earliest(1, mode, 7000);
  assert.ok(w.traffic[1] >= bound, `answer-relative lower bound ${bound}, got ${w.traffic[1]}`);
  assert.ok(w.traffic[1] < 90_000); w.history(result);
});

test('formal finite 90s busy stream has no three-attempt ceiling and no upload churn', async t => {
  const w = await world(t, { repeat: true });
  const result = await w.invoke();
  assert.equal(result.code, 5); assert.equal(result.json.rows[0].calls, 0);
  assert.ok(w.traffic.length > 3 && w.traffic.length <= 10, `90s uploads: ${w.traffic.length}`);
  for (let i = 1; i < w.traffic.length; i++) assert.ok(w.traffic[i] - w.traffic[i - 1] >= 10_000);
  assert.ok(w.traffic.every(at => at < 90_000)); assert.equal(w.elapsed(), 90_000); w.history(result);
});

for (const [advice, mode, end] of [[1, '404', 9000], [1, 'full', 45_000], [75, 'full', 70_000]])
  test(`formal caller deadline ${end} wins over ${advice}s/${mode}`, async t => {
    const w = await world(t, { advice, mode });
    const result = await w.invoke({ '--timeout': String(end / 60_000) });
    assert.equal(result.code, 5); assert.equal(w.traffic.length, 1); assert.equal(result.json.rows[0].calls, 0);
    assert.equal(w.elapsed(), end); w.history(result);
  });

test('formal interruption before capacity release sends no replacement', async t => {
  const w = await world(t, { mode: 'full' }); w.interrupt(15_000);
  const result = await w.invoke();
  assert.equal(result.code, 3); assert.equal(w.traffic.length, 1); assert.equal(w.elapsed(), 15_000);
  assert.match(result.err + JSON.stringify(result.json), /Stopped\./);
  assert.doesNotMatch(result.err + JSON.stringify(result.json), /Stopped before sending|wait ended/); w.history(result);
});

test('formal maintenance wins over capacity hold expiry', async t => {
  const w = await world(t, { capacity: (_, posted) => !posted ? occupancy() : { status: 200, json: {
    ...occupancy().json, maintenance: { until: new Date(ORIGIN + 120_000).toISOString(), reason: 'maintenance' },
  } } });
  const result = await w.invoke();
  assert.equal(result.code, 5); assert.equal(w.traffic.length, 1); assert.equal(w.elapsed(), 90_000); w.history(result);
});

for (const [status, code] of [[401, 'unauthorized'], [403, 'no-cloud-access'], [403, 'not-invited'], [503, 'cloud-unavailable'], [426, 'update-required']])
  test(`formal access stop ${code} wins over capacity release`, async t => {
    const w = await world(t, { capacity: (_, posted) => !posted ? occupancy() : { status, json: { error: { code } } } });
    const result = await w.invoke();
    assert.equal(result.code, 5); assert.equal(w.traffic.length, 1); w.history(result);
  });

for (const [advice, mode, retryAt] of [[1, '404', 8000], [1, 'full', 20_000], [75, 'full', 20_000]])
  test(`formal saved new bounds survive read and retry: ${advice}s ${mode}`, async t => {
    const w = await world(t, { advice, mode }); w.interrupt(5000);
    const first = await w.invoke(); assert.equal(first.code, 3); const before = w.history(first);
    const minimum = ORIGIN + Math.max(10_000, advice * 1000), hold = ORIGIN + 60_000;
    assert.equal(before.rows[0].retry_at, minimum); assert.equal(before.rows[0].capacity_until, hold);
    w.interrupt(Infinity); w.time(7000);
    const read = await w.invoke({ '--read': first.json.batch }); assert.equal(w.traffic.length, 1);
    const persisted = load(w.statePath(first.json.batch));
    assert.equal(persisted.rows[0].retry_at, minimum); assert.equal(persisted.rows[0].capacity_until, hold);
    assert.deepEqual(persisted.rows[0].request_ids, before.rows[0].request_ids);
    assert.equal(persisted.source_sha256, before.source_sha256); assert.equal(read.json.rows[0].calls, 0);
    w.time(retryAt); const result = await w.invoke({ '--retry': first.json.batch });
    assert.equal(result.code, 0, result.err); assert.equal(w.traffic.length, 2);
    const bound = earliest(advice, mode);
    const end = mode === '404' ? 60_000 : advice === 75 ? 90_000 : 80_000;
    assert.ok(w.traffic[1] >= bound && w.traffic[1] < end, 'saved bounds do not restart'); w.history(result);
  });

for (const advice of [1, 75, 300]) for (const savedDelay of [1000, 95_000])
  test(`formal legacy proof is anchored once: old advice ${advice}s, saved delay ${savedDelay}`, async t => {
  const w = await world(t, { mode: 'full', advice }); w.interrupt(5000);
  const first = await w.invoke(); assert.equal(w.traffic.length, 1);
  const path = w.statePath(first.json.batch), old = load(path), row = old.rows[0];
  row.sent_at = ORIGIN - 100_000; row.retry_at = ORIGIN + savedDelay;
  delete row.busy_observed_at; delete row.capacity_until; delete row.busy_request_id;
  writeFileSync(path, JSON.stringify(old)); w.interrupt(Infinity); w.time(20_000);
  const unchanged = readFileSync(path); await w.invoke({ '--read': row.request_ids[0] });
  assert.deepEqual(readFileSync(path), unchanged, 'UUID-only read cannot rewrite batch metadata');
  await w.invoke({ '--read': first.json.batch });
  const anchored = load(path).rows[0], minimum = ORIGIN + Math.max(30_000, savedDelay), hold = ORIGIN + 80_000;
  assert.equal(anchored.retry_at, minimum); assert.equal(anchored.capacity_until, hold); assert.equal(w.traffic.length, 1);
  w.time(40_000); await w.invoke({ '--read': first.json.batch });
  assert.equal(load(path).rows[0].retry_at, minimum); assert.equal(load(path).rows[0].capacity_until, hold);
  const result = await w.invoke({ '--retry': first.json.batch });
  assert.equal(result.code, 0, result.err); assert.equal(w.traffic.length, 2);
  const bound = Math.max(80_000, savedDelay);
  assert.ok(w.traffic[1] >= bound && w.traffic[1] < (savedDelay === 1000 ? 100_000 : 120_000),
    'legacy anchors survive subsequent observations'); w.history(result);
});

for (const kind of ['lost', 'wrong-id', 'wrong-command', 'paid', 'unknown-calls', 'evaluated', 'incomplete'])
  test(`formal elapsed/free capacity grants no replay authority to ${kind}`, async t => {
    const w = await world(t, { mode: 'free', receipt: answer => {
      if (kind === 'lost') return null;
      if (kind === 'wrong-id') { answer.id = 'wrong'; answer.requestId = 'wrong'; }
      if (kind === 'wrong-command') answer.command = 'lint';
      if (kind === 'paid') answer.usage.calls = 2;
      if (kind === 'unknown-calls') answer.usage.calls = 'unknown';
      if (kind === 'evaluated') answer.result.report.samples = [{ steps: [{ checks: [{ criterion_id: 'AC1', passed: true }] }] }];
      if (kind === 'incomplete') answer.result.report.accounting_complete = false;
      return answer;
    } });
    const first = await w.invoke(); assert.equal(w.traffic.length, 1); assert.notEqual(first.json.rows[0].can_retry, true);
    w.time(120_000);
    for (const options of [{ '--read': first.json.batch }, { '--retry': first.json.batch }]) {
      await w.invoke(options); assert.equal(w.traffic.length, 1, 'no fresh upload without authoritative busy proof');
    }
    const id = checks(w.fake)[0].request.requestId;
    assert.ok(w.fake.gets.every(entry => entry.url.endsWith(id)), 'uncertain attempts are read only by their original identity');
  });

test('formal source mismatch cannot use saved busy timing as dispatch authority', async t => {
  const w = await world(t); w.interrupt(5000);
  const first = await w.invoke(); assert.equal(w.traffic.length, 1);
  const story = join(w.setup.repo, 'user_stories/place-order.md');
  writeFileSync(story, readFileSync(story, 'utf8') + '\nChanged selected source.\n');
  w.interrupt(Infinity); w.time(120_000);
  const result = await w.invoke({ '--retry': first.json.batch });
  assert.equal(result.code, 2); assert.equal(w.traffic.length, 1); assert.match(result.err, /source.*changed|source.*match/i);
});
