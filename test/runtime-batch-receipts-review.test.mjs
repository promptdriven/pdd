import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const read = path => JSON.parse(readFileSync(path, 'utf8'));
const write = (path, value) => writeFileSync(path, JSON.stringify(value));
async function fixture(t, reply) {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (e, f) => e.command === 'lint'
    ? { status: 200, json: f.lint(e.request.requestId) } : reply(e, f));
  const run = async options => {
    const { ports, clock } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    const words = options?.['--read'] ? [options['--read']] : options ? [] : ['place-order'];
    const normalized = options?.['--read'] ? { ...options, '--read': true } : options;
    const code = await runCheck({ cwd: setup.repo, words, options: { '--json': true, ...normalized } }, ports);
    return { code, json: ports.stdout.text ? JSON.parse(ports.stdout.text) : null, err: ports.stderr.text, clock };
  };
  const first = await run();
  const folder = join(setup.state, 'batches', first.json.batch), file = join(folder, 'batch.json');
  return { setup, fake, run, first, folder, file, batch: first.json.batch, id: first.json.rows[0].request_id,
    edit(fn) { const value = read(file); fn(value.rows[0], value); write(file, value); } };
}
const passed = (e, f) => ({ status: 200, json: f.check(e.request?.requestId ?? e.url.split('/').at(-1)) });

for (const [status, code, exit, state] of [[422, 'invalid-input', 4, 'refused'], [503, 'pool-low-room', 5, 'not_run'], [429, 'rate-limited', 5, 'not_run']]) {
  test(`2655 review M1: ${status} ${code} keeps final POST verdict across repeated legacy reads and retry`, async t => {
    const r = await fixture(t, e => e.method === 'POST' ? { status, json: { error: { code, message: `Final ${code}` } } }
      : { status: 404, json: { error: { code: 'not-found' } } });
    assert.equal(r.first.code, exit);
    // Legacy evidence has no receipt and no new classification field. Retain only existing fields.
    r.edit(row => { for (const key of Object.keys(row)) if (!['story', 'title', 'test', 'state', 'phase', 'request_ids', 'refusals', 'note', 'why', 'next_step', 'max_calls', 'seconds', 'eligible', 'can_retry', 'busy', 'retry_at', 'draft'].includes(key)) delete row[key]; });
    const posts = r.fake.posts.length, gets = r.fake.gets.length;
    for (const options of [{ '--read': r.batch }, { '--read': r.batch }, { '--retry': r.batch, '--timeout': '0.01' }]) {
      const result = await r.run(options);
      assert.equal(result.code, exit, 'final POST outcome keeps exact exit code');
      assert.equal(result.json.rows[0].state, state);
      assert.equal(r.fake.gets.length, gets, 'request ID allocation is not accepted-job evidence');
      assert.equal(r.fake.posts.length, posts, 'final POST outcome never resubmits');
      assert.equal(result.clock.uuids, 0);
    }
  });
}

for (const [name, usage, report] of [
  ['usage false', { calls: 3, known_calls: 2, unknown_calls: 1, accounting_complete: false }, {}],
  ['report false', { calls: 2, known_calls: 2, unknown_calls: 1 }, { accounting_complete: false }],
  ['unknown calls only', { calls: 2, known_calls: 2, unknown_calls: 1 }, {}],
  ['false without unknown count', { calls: 2, known_calls: 2, accounting_complete: false }, {}],
]) test(`2655 review S1: ${name} retains known lower bound plus unknown through reads`, async t => {
  const r = await fixture(t, (e, f) => { const answer = passed(e, f); Object.assign(answer.json.usage, usage); Object.assign(answer.json.result.report, report); return answer; });
  for (const result of [r.first, await r.run({ '--read': r.batch })]) {
    assert.equal(result.code, 0, 'incomplete accounting does not change the terminal verdict');
    assert.equal(result.json.rows[0].calls, 'unknown', 'row must not claim a complete numeric call total');
    assert.match(result.json.summary_line, /2 AI calls \+ 1 unknown/);
  }
});

test('2655 review S3: zero eligible retry continues beyond three GETs to terminal receipt', async t => {
  let recovering = false, reads = 0;
  const r = await fixture(t, (e, f) => {
    if (recovering && e.method === 'GET' && ++reads <= 3) return { status: 200, json: f.check(e.url.split('/').at(-1), 'running') };
    return passed(e, f);
  });
  recovering = true;
  r.edit(row => Object.assign(row, { phase: 'local', state: 'running', can_retry: false, eligible: false }));
  rmSync(join(r.folder, `${r.id}.json`));
  const posts = r.fake.posts.length;
  const result = await r.run({ '--retry': r.batch, '--timeout': '1' });
  assert.equal(result.code, 0);
  assert.ok(reads > 3, 'must continue polling with no eligible POST rows');
  assert.equal(result.json.rows[0].state, 'passed');
  assert.equal(r.fake.posts.length, posts);
  assert.equal(result.clock.uuids, 0);
});

test('2655 review S3: stale busy/retry flags without proof and unavailable GET never POST', async t => {
  let unavailable = false;
  const r = await fixture(t, (e, f) => unavailable && e.method === 'GET' ? { status: 503, json: { error: { code: 'temporary' } } } : passed(e, f));
  unavailable = true;
  r.edit(row => Object.assign(row, { state: 'not_run', phase: 'server', busy: true, eligible: true, can_retry: true, retry_at: null }));
  rmSync(join(r.folder, `${r.id}.json`));
  rmSync(join(r.folder, `${r.id}.admission.json`), { force: true });
  const posts = r.fake.posts.length;
  const result = await r.run({ '--retry': r.batch, '--timeout': '0.1' });
  assert.equal(result.code, 3);
  assert.equal(result.json.rows[0].calls, 'unknown');
  assert.equal(result.json.rows[0].can_retry, false);
  assert.equal(result.json.rows[0].busy, false);
  assert.equal(r.fake.posts.length, posts);
  assert.equal(result.clock.uuids, 0);
});

test('2655 review S5: direct UUID caches raw receipt without rewriting batch or summary', async t => {
  const r = await fixture(t, passed);
  r.edit(row => Object.assign(row, { phase: 'local', state: 'running' }));
  const raw = join(r.folder, `${r.id}.json`), receipt = read(raw); receipt.state = 'running'; receipt.result = null; write(raw, receipt);
  const beforeBatch = readFileSync(r.file), summary = join(r.folder, 'summary.json'), beforeSummary = readFileSync(summary);
  const posts = r.fake.posts.length;
  const result = await r.run({ '--read': r.id });
  assert.equal(result.code, 0);
  assert.equal(read(raw).state, 'passed');
  assert.ok(readFileSync(r.file).equals(beforeBatch), 'UUID read must leave batch.json byte-identical');
  assert.ok(readFileSync(summary).equals(beforeSummary), 'UUID read must leave summary.json byte-identical');
  const gets = r.fake.gets.length;
  const batch = await r.run({ '--read': r.batch });
  assert.equal(batch.code, 0);
  assert.equal(batch.json.rows[0].state, 'passed');
  assert.equal(r.fake.gets.length, gets);
  assert.equal(r.fake.posts.length, posts);
});

test('2655 review N1: one matching batch cache write failure does not crash UUID read', async t => {
  const r = await fixture(t, passed);
  const other = join(r.setup.state, 'batches', '20261027-162748-abcd'); mkdirSync(other); write(join(other, 'batch.json'), read(r.file));
  const raw = join(r.folder, `${r.id}.json`); rmSync(raw); mkdirSync(raw); // EISDIR even when tests run as root.
  let result;
  await assert.doesNotReject(async () => { result = await r.run({ '--read': r.id }); }, 'cache write failure must not fail the authoritative direct read');
  assert.equal(result.code, 0);
  assert.equal(result.json.rows[0].state, 'passed');
  assert.equal(read(join(other, `${r.id}.json`)).state, 'passed', 'one failure must not prevent other matching caches');
});
