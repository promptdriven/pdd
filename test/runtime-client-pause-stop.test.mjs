import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { listRuntimeJobs } from '../src/runtime-slots.mjs';
import { fakeRuntime, harbor, portsFor, filesUnder } from './runtime-fake.mjs';

const pauseReply = (kind, maintenance) => ({ status: 503, headers: { 'retry-after': '7' }, json: {
  dispatch: 'not_started', job_created: false, usage: { calls: 0 }, accounting_complete: true,
  error: { code: maintenance ? 'maintenance' : `${kind}-queue-full`, details: maintenance ? { reason: 'synthetic pause' } : { retryable: true, retry_after: 7 } },
} });
const receipts = setup => filesUnder(setup.state).filter(path => path.endsWith('.json')).map(path => ({ path, raw: readFileSync(path, 'utf8') }));
const make = (setup, fake) => portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
const savedBatch = (setup, batch) => JSON.parse(readFileSync(join(setup.state, 'batches', batch, 'batch.json')));

for (const stage of ['check', 'explicit-lint', 'try-lint', 'try-setup']) for (const maintenance of [false, true]) test(`post-POST stop: ${stage} ${maintenance ? 'maintenance' : 'busy'} reports sent, confirmed-unstarted truth`, async t => {
  const setup = harbor(t); let paused = false, made;
  const kind = stage.endsWith('lint') ? 'lint' : stage === 'try-setup' ? 'try' : 'check';
  const refusal = pauseReply(kind, maintenance);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === kind) { paused = true; return refusal; }
    return f.normal(entry);
  });
  made = make(setup, fake);
  made.ports.sleep = async ms => { made.clock.now += ms; assert.equal(paused, true); made.clock.interrupt(); };
  const code = stage.startsWith('try')
    ? await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true, '--no-wait': true } }, made.ports)
    : await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true, ...(stage === 'explicit-lint' ? { '--lint': true } : {}) } }, made.ports);
  assert.equal(code, stage === 'explicit-lint' || stage === 'try-lint' ? 5 : 3);
  assert.equal(fake.posts.filter(p => p.command === kind).length, 1, 'interruption must not retry the confirmed refusal');
  const submitted = fake.posts.find(p => p.command === kind).request.requestId;
  const output = made.ports.stdout.text + made.ports.stderr.text;
  assert.match(output, /Stopped\./, 'interruption wins over timeout/capacity wording');
  assert.doesNotMatch(output, /Stopped before sending\.|Nothing new was sent\.|wait ended|stayed busy until/);
  assert.ok(output.includes(submitted), 'identify the submission whose unstarted result was confirmed');
  assert.match(output, /submitted/i); assert.match(output, /not start|unstarted|no (?:checks|work) ran/i);
  if (!stage.startsWith('try')) assert.equal(JSON.parse(made.ports.stdout.text).exit_code, code, 'stdout remains one valid JSON report');
  const raw = receipts(setup).find(r => r.path.endsWith(`${submitted}.admission.json`));
  assert.deepEqual(JSON.parse(raw.raw), refusal.json, 'raw admission evidence is retained unchanged');
  assert.deepEqual((await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs, [], 'confirmed unsent jobs leave no paid lease');
});

for (const stage of ['check', 'explicit-lint']) test(`post-POST stop: ${stage} terminal queue refusal keeps receipt and zero usage`, async t => {
  const setup = harbor(t); let paused = false, made, receipt;
  const kind = stage === 'check' ? 'check' : 'lint';
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === kind) {
      paused = true;
      const refusal = { code: `${kind}-queue-timeout`, message: 'No work started.', details: { retryable: true, retry_after: 7 } };
      receipt = f.job(e.request.requestId, kind, 'refused', { refusals: [refusal], report: { dispatch: 'not_started', provider_calls: 0, refusal, samples: [] } }, 0);
      return { status: 200, json: receipt };
    }
    return f.normal(e);
  });
  made = make(setup, fake); made.ports.sleep = async ms => { made.clock.now += ms; assert.ok(paused); made.clock.interrupt(); };
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true, ...(stage === 'explicit-lint' ? { '--lint': true } : {}) } }, made.ports), stage === 'check' ? 3 : 5);
  assert.match(made.ports.stdout.text + made.ports.stderr.text, /Stopped\./);
  assert.equal(fake.posts.filter(e => e.command === kind).length, 1);
  assert.deepEqual(JSON.parse(receipts(setup).find(r => r.path.endsWith(`${receipt.id}.json`)).raw), receipt);
});

for (const earlier of ['confirmed', 'unknown']) test(`post-POST stop preserves earlier ${earlier} evidence, accounting and recovery`, async t => {
  const setup = harbor(t, repo => writeFileSync(join(repo, 'tests/earlier.json'), readFileSync(join(repo, 'tests/place-order.json'))));
  let made, checks = 0, paused = false; const answers = new Map();
  const fake = await fakeRuntime(t, (e, f) => {
    if (e.command === 'check') {
      checks++;
      if (e.request.scenario.endsWith('earlier.json')) {
        if (earlier === 'unknown') return { destroy: true };
        const answer = f.check(e.request.requestId); answers.set(answer.id, answer); return { status: 200, json: answer };
      }
      if (e.request.scenario.endsWith('place-order.json')) { paused = true; return pauseReply('check', false); }
      return { status: 200, json: f.check(e.request.requestId) };
    }
    if (e.method === 'GET') return { status: 404, json: { error: { code: 'not-found' } } };
    return f.normal(e);
  });
  made = make(setup, fake);
  made.ports.sleep = async ms => {
    made.clock.now += ms; await new Promise(done => setImmediate(done));
    const saved = receipts(setup).find(r => r.path.endsWith('/batch.json'));
    const previous = saved && JSON.parse(saved.raw).rows.find(r => r.test === 'tests/earlier.json');
    if (paused && receipts(setup).some(r => r.path.endsWith('.admission.json'))
      && previous?.state === (earlier === 'confirmed' ? 'passed' : 'unknown')) made.clock.interrupt();
  };
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--json': true } }, made.ports), 3);
  const report = JSON.parse(made.ports.stdout.text), previous = report.rows.find(r => r.test === 'tests/earlier.json'), current = report.rows.find(r => r.test === 'tests/place-order.json');
  assert.equal(previous.state, earlier === 'confirmed' ? 'passed' : 'unknown');
  assert.equal(previous.calls, earlier === 'confirmed' ? 1 : 'unknown');
  assert.match(current.reason.message, /^Stopped\./);
  const before = savedBatch(setup, report.batch), earlierSaved = before.rows.find(r => r.test === 'tests/earlier.json');
  assert.equal(earlierSaved.request_ids.length, 1);
  for (const [id, answer] of answers) assert.deepEqual(JSON.parse(readFileSync(join(setup.state, 'batches', report.batch, `${id}.json`))), answer);
  const leases = (await listRuntimeJobs({ stateDir: setup.state, origin: fake.origin })).jobs;
  assert.deepEqual(leases.flatMap(r => r.request_ids), earlier === 'unknown' ? earlierSaved.request_ids : []);
  const count = fake.posts.length, later = make(setup, fake); later.clock.now = made.clock.now;
  await runCheck({ cwd: setup.repo, words: [report.batch], options: { '--read': true, '--json': true } }, later.ports);
  assert.equal(fake.posts.length, count, 'read recovery never resends earlier unknown or paused work');
  assert.deepEqual(savedBatch(setup, report.batch).rows.find(r => r.test === 'tests/earlier.json').request_ids, earlierSaved.request_ids);
  if (earlier === 'unknown') assert.match(made.ports.stderr.text, /pdd test --read/);
  assert.ok(checks >= 2);
});

test('before-current-POST stop remains scoped to unsent work after earlier submissions', async t => {
  const setup = harbor(t); let made, lintSent = false;
  const fake = await fakeRuntime(t, (e, f) => { if (e.command === 'lint') lintSent = true; return f.normal(e); });
  made = make(setup, fake);
  const records = new Map(), times = new Map(); let stopRegistration = false;
  made.ports.slotFiles = {
    listRecords: () => ({ jobs: [...records.values()].filter(r => r.state).map(r => structuredClone(r)) }),
    exclusiveCreate: (path, record) => {
      if (records.has(path)) return false; records.set(path, structuredClone(record)); times.set(path, made.clock.now); return true;
    },
    writeAtomic: (path, record) => {
      records.set(path, structuredClone(record)); times.set(path, made.clock.now);
      if (lintSent && record.kind === 'check' && record.state === 'active' && !stopRegistration) { stopRegistration = true; made.clock.interrupt(); }
    },
    modifiedAt: path => times.get(path) ?? null, touch: path => records.has(path), unlink: path => records.delete(path),
  };
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, made.ports), 3);
  const report = JSON.parse(made.ports.stdout.text);
  assert.match(report.rows[0].reason.message, /^Stopped before sending\./);
  assert.equal(fake.posts.filter(p => p.command === 'check').length, 0); assert.equal(fake.posts.filter(p => p.command === 'lint').length, 1);
  const batch = savedBatch(setup, report.batch); assert.equal(batch.lint.request_ids.length, 1);
  assert.ok(receipts(setup).some(r => r.path.endsWith(`${batch.lint.request_ids[0]}.json`)), 'earlier submitted lint receipt remains');
});
