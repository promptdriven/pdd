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

// Independent recovery checks use the Story as oracle; synthetic receipts cost no AI calls.
test('2655 verify: known accepted IDs project receipts across stale states and caches without POST', async t => {
  for (const phase of ['local', 'server']) for (const state of ['not_run', 'running', 'passed']) for (const cache of ['missing', 'terminal', 'stale']) {
    const r = await fixture(t), raw = join(r.folder, `${r.id}.json`);
    r.edit(row => Object.assign(row, { phase, state, calls: 0, checks: null, criteria: null, eligible: true, can_retry: true, busy: true }));
    if (cache === 'missing') rmSync(raw);
    if (cache === 'stale') { const a = read(raw); a.state = 'running'; a.result = null; write(raw, a); }
    const posts = r.fake.posts.length;
    complete(await r.run({ '--retry': r.batch }));
    assert.equal(r.fake.posts.length, posts, `${phase}/${state}/${cache}: accepted ID must not POST again`);
    assert.equal(read(r.file).rows[0].phase, 'server');
  }
});

test('2655 verify: older attempt UUID refreshes its cache while preserving latest attempt projection', async t => {
  const r = await fixture(t), old = r.id, latest = '11111111-1111-4111-8111-111111111111';
  const raw = join(r.folder, `${old}.json`), stale = read(raw); stale.state = 'running'; stale.result = null; write(raw, stale);
  r.edit(row => Object.assign(row, { request_ids: [old, latest], state: 'running', phase: 'server', calls: 'unknown', checks: null, criteria: null }));
  const before = read(r.file).rows[0], posts = r.fake.posts.length;
  complete(await r.run({ '--read': old }));
  assert.equal(read(raw).state, 'passed', 'historical receipt must be saved');
  assert.deepEqual(read(r.file).rows[0], before, 'historical result must not replace latest attempt');
  assert.equal(r.fake.posts.length, posts);
});

test('2655 verify: interruption and deadline cannot preserve unsupported saved success or invent zero usage', async t => {
  for (const stop of ['interrupt', 'deadline']) {
    const r = await fixture(t); rmSync(join(r.folder, `${r.id}.json`));
    const posts = r.fake.posts.length;
    const extra = stop === 'interrupt' ? { onInterrupt: handler => { handler(); return () => {}; } } : {};
    const result = await r.run({ '--retry': r.batch, '--timeout': stop === 'deadline' ? '0' : '1' }, extra);
    assert.equal(result.code, 3, `${stop}: no terminal evidence means no success`);
    assert.equal(result.json.rows[0].calls, 'unknown');
    assert.equal(result.json.rows[0].checks, null);
    assert.equal(result.json.rows[0].criteria, null);
    assert.equal(r.fake.posts.length, posts);
    assert.equal(result.clock.uuids, 0);
  }
});
