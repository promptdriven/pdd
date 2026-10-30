import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

const checks = Array.from({ length: 17 }, (_, i) => ({ criterion_id: `AC${i % 4 + 1}`, target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: 900, passed: true }));
for (const retry of [false, true]) test(`RELAY lint-held ${retry ? 'retry' : 'read'} recovers terminal receipt from stale local verdict`, async t => {
  const h = harbor(t);
  let mode = 'lint-wait';
  const f = await fakeRuntime(t, (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    const prior = f.posts.find(p => p.request.requestId === id);
    if (e.command === 'lint' || prior?.command === 'lint') return { status: 200, json: mode === 'lint-wait' ? f.job(id, 'lint', 'running') : f.lint(id) };
    const answer = f.check(id, mode === 'terminal' ? 'passed' : 'running', checks);
    answer.usage.calls = mode === 'terminal' ? 4 : 'unknown';
    return { status: 200, json: answer };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  async function run(options, words = []) {
    const p = portsFor(env);
    const code = await runCheck({ cwd: h.repo, words, options: { '--json': true, ...options } }, p.ports);
    return { code, json: JSON.parse(p.ports.stdout.text), p };
  }
  const initial = await run({ '--max-calls': 6 }, ['place-order']);
  assert.equal(initial.code, 3);
  assert.equal(initial.json.rows[0].calls, 0);
  assert.equal(f.posts.filter(p => p.command === 'check').length, 0);
  const batch = readdirSync(join(h.state, 'batches'), { withFileTypes: true }).find(e => e.isDirectory()).name;
  const folder = join(h.state, 'batches', batch), path = join(folder, 'batch.json');
  const original = JSON.parse(readFileSync(path));
  assert.equal(original.rows[0].phase, 'lint');
  mode = 'running';
  const recover = () => run({ [retry ? '--retry' : '--read']: retry ? batch : true }, retry ? [] : [batch]);
  const open = await recover();
  assert.equal(open.code, 3);
  const paid = f.posts.filter(p => p.command === 'check');
  assert.equal(paid.length, 1); assert.equal(paid[0].request.max_calls, 6);
  assert.equal(paid[0].request.source_sha256, original.source_sha256);
  assert.equal(f.posts.filter(p => p.command === 'lint').length, 1);
  const id = open.json.rows[0].request_id;
  assert.equal(id, paid[0].request.requestId);
  // A legacy local phase or a stale completed label cannot hide an uncertain
  // receipt. Recover the same ID and its actual accounting without reexecution.
  const stale = JSON.parse(readFileSync(path));
  Object.assign(stale.rows[0], { phase: 'local', state: 'passed', calls: 0 });
  writeFileSync(path, JSON.stringify(stale));
  rmSync(join(folder, `${id}.json`));
  mode = 'terminal';
  const beforeGets = f.gets.length;
  const terminal = await recover();
  assert.equal(terminal.code, 0);
  assert.equal(terminal.json.rows[0].request_id, id);
  assert.deepEqual(terminal.json.rows[0].checks, { passed: 17, total: 17 });
  assert.deepEqual(terminal.json.rows[0].criteria, { passed: 4, total: 4 });
  assert.equal(terminal.json.rows[0].calls, 4);
  assert.match(terminal.json.summary_line, /17\/17 checks.*4 AI calls/);
  assert.ok(f.gets.slice(beforeGets).some(e => e.url.endsWith(id)));
  assert.equal(terminal.p.clock.uuids, 0);
  const again = await recover();
  assert.deepEqual(again.json.rows[0], terminal.json.rows[0]);
  assert.equal(again.p.clock.uuids, 0);
  assert.equal(f.posts.filter(p => p.command === 'check').length, 1);
  assert.equal(JSON.parse(readFileSync(path)).source_sha256, original.source_sha256);
});
