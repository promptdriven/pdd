import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync, mkdirSync, cpSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const read = path => JSON.parse(readFileSync(path, 'utf8'));
const write = (path, value) => writeFileSync(path, JSON.stringify(value));
const checks = Array.from({ length: 17 }, (_, i) => ({ criterion_id: `AC${i % 4 + 1}`, target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: 900, passed: true }));
async function fixture(t) {
  const setup = harbor(t);
  let mode = 'terminal';
  const fake = await fakeRuntime(t, (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.command === 'lint') return { status: 200, json: f.lint(id) };
    if (mode === 'unavailable') return { status: 503, json: { error: { code: 'temporary' } } };
    const answer = f.check(id, mode === 'pending' ? 'running' : 'passed', checks);
    answer.usage.calls = mode === 'pending' ? 'unknown' : 4;
    return { status: 200, json: answer };
  });
  async function run(options = {}, extra = {}) {
    const { ports, clock } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, extra);
    const words = options['--read'] ? [options['--read']] : Object.keys(options).length ? [] : ['place-order'];
    const normalized = options['--read'] ? { ...options, '--read': true } : options;
    const code = await runCheck({ cwd: setup.repo, words, options: { '--json': true, ...normalized } }, ports);
    return { code, json: ports.stdout.text ? JSON.parse(ports.stdout.text) : null, err: ports.stderr.text, clock };
  }
  const initial = await run();
  assert.equal(initial.code, 0);
  const folder = join(setup.state, 'batches', initial.json.batch), file = join(folder, 'batch.json');
  const id = initial.json.rows[0].request_id;
  return { setup, fake, run, folder, file, id, batch: initial.json.batch, mode: value => { mode = value; }, edit: fn => { const saved = read(file); fn(saved.rows[0], saved); write(file, saved); } };
}
function complete(result) {
  assert.equal(result.code, 0);
  assert.deepEqual(result.json.rows[0].checks, { passed: 17, total: 17 });
  assert.deepEqual(result.json.rows[0].criteria, { passed: 4, total: 4 });
  assert.equal(result.json.rows[0].calls, 4);
  assert.match(result.json.summary_line, /17\/17 checks.*4 AI calls/);
}

test('2655: dispatching a held local row preserves receipt counts in retry and batch read', async t => {
  const r = await fixture(t);
  r.edit(row => Object.assign(row, { phase: 'local', state: 'not_run', request_ids: [], eligible: true, can_retry: true, busy: true, retry_at: null }));
  const before = r.fake.posts.length;
  const story = join(r.setup.repo, 'user_stories/place-order.md'), originalStory = readFileSync(story, 'utf8');
  writeFileSync(story, originalStory + '\nChanged source.\n');
  const changed = await r.run({ '--retry': r.batch });
  assert.equal(changed.code, 2); assert.match(changed.err, /source.*changed|source.*match/i);
  assert.equal(r.fake.posts.length, before);
  writeFileSync(story, originalStory);
  let stop;
  r.edit(row => { row.retry_at = Date.parse('2026-10-27T16:27:47Z') + 20_000; });
  const interrupted = await r.run({ '--retry': r.batch }, { onInterrupt: handler => { stop = handler; return () => {}; }, sleep: async () => { stop(); } });
  assert.equal(interrupted.code, 3); assert.equal(r.fake.posts.length, before, 'interruption respects saved capacity backoff');
  r.edit(row => { row.retry_at = null; });
  const retried = await r.run({ '--retry': r.batch });
  assert.equal(r.fake.posts.length, before + 1, 'only one held check is sent; saved lint is reused');
  assert.equal(retried.json.rows[0].request_id, r.fake.posts.at(-1).request.requestId);
  complete(retried);
  complete(await r.run({ '--read': r.batch }));
  assert.equal(r.fake.posts.length, before + 1);
});

for (const state of ['running', 'passed']) test(`2655: legacy local ${state} row recovers its known check ID`, async t => {
  const r = await fixture(t);
  r.edit(row => Object.assign(row, { phase: 'local', state }));
  if (state === 'running') rmSync(join(r.folder, `${r.id}.json`));
  const posts = r.fake.posts.length;
  complete(await r.run({ '--read': r.batch }));
  assert.equal(r.fake.posts.length, posts);
  assert.equal(read(r.file).rows[0].phase, 'server');
});

for (const cache of ['missing', 'running', 'wrong-id']) test(`2655: saved passed row refreshes ${cache} receipt by same-ID GET`, async t => {
  const r = await fixture(t), raw = join(r.folder, `${r.id}.json`);
  if (cache === 'missing') rmSync(raw);
  else { const receipt = read(raw); if (cache === 'running') { receipt.state = 'running'; receipt.result = null; } else receipt.id = 'another-id'; write(raw, receipt); }
  const gets = r.fake.gets.length, posts = r.fake.posts.length;
  complete(await r.run({ '--read': r.batch }));
  assert.equal(r.fake.gets.length, gets + 1);
  assert.ok(r.fake.gets.at(-1).url.endsWith(r.id));
  assert.equal(r.fake.posts.length, posts);
});

test('2655: direct UUID read refreshes matching batch raw receipt and row, keeping unrelated caches', async t => {
  const r = await fixture(t), original = read(r.file);
  r.edit(row => Object.assign(row, { phase: 'local', state: 'running' }));
  const raw = join(r.folder, `${r.id}.json`), stale = read(raw); stale.state = 'running'; stale.result = null; write(raw, stale);
  const others = [];
  for (const [i, change] of [{ login: 'someone-else' }, { user_id: '99' }, { origin: 'http://127.0.0.1:1' }, { root: '/another-repo' }].entries()) {
    const folder = join(r.setup.state, 'batches', `20261027-09274${i}-abcd`); mkdirSync(folder); cpSync(raw, join(folder, `${r.id}.json`));
    write(join(folder, 'batch.json'), { ...original, ...change }); others.push({ folder, bytes: readFileSync(join(folder, 'batch.json'), 'utf8') });
  }
  const posts = r.fake.posts.length;
  complete(await r.run({ '--read': r.id }));
  assert.equal(r.fake.posts.length, posts);
  for (const other of others) { assert.equal(readFileSync(join(other.folder, 'batch.json'), 'utf8'), other.bytes); assert.equal(read(join(other.folder, `${r.id}.json`)).state, 'running'); }
  assert.equal(read(raw).state, 'passed', 'direct read persists its authoritative raw check receipt');
  assert.equal(read(r.file).rows[0].state, 'passed');
  const gets = r.fake.gets.length;
  complete(await r.run({ '--read': r.batch }));
  assert.equal(r.fake.gets.length, gets, 'cached terminal receipt needs no GET');
});

for (const mode of ['pending', 'unavailable']) test(`2655: zero-eligible retry polls accepted local rows and keeps ${mode} usage unknown`, async t => {
  const r = await fixture(t); r.mode(mode);
  r.edit(row => Object.assign(row, { phase: 'local', state: 'running', can_retry: false, eligible: false }));
  rmSync(join(r.folder, `${r.id}.json`));
  const posts = r.fake.posts.length, gets = r.fake.gets.length;
  const result = await r.run({ '--retry': r.batch, '--timeout': '0.01' });
  assert.equal(result.code, 3);
  assert.equal(r.fake.posts.length, posts, 'accepted jobs are never submitted again');
  assert.equal(result.clock.uuids, 0);
  assert.ok(r.fake.gets.length > gets, 'zero-eligible retry still polls accepted IDs');
  assert.equal(result.json.rows[0].calls, 'unknown');
  assert.match(result.json.summary_line, mode === 'pending' ? /running.*unknown/ : /no verdict.*unknown/);
});

for (const mode of ['pending', 'unavailable']) test(`2655: saved passed label without terminal evidence becomes ${mode}, never success`, async t => {
  const r = await fixture(t); r.mode(mode);
  rmSync(join(r.folder, `${r.id}.json`));
  const posts = r.fake.posts.length;
  const result = await r.run({ '--read': r.batch });
  assert.equal(r.fake.posts.length, posts);
  assert.equal(result.clock.uuids, 0);
  assert.equal(result.code, 3, 'saved passed label cannot replace unavailable terminal evidence');
  assert.equal(result.json.rows[0].calls, 'unknown');
  assert.match(result.json.summary_line, mode === 'pending' ? /running/ : /no verdict/);
});
