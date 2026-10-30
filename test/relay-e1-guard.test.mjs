import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync, copyFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// E1: within one continuation --read, row A gets a fresh "unknown" verdict (410 or wrong ID),
// row B keeps the budget busy until the deadline. Does the guard replace A's fresh unknown with
// the stale POST-time "queued/running" cache?
for (const kind of ['410', 'wrong-id']) test(`E1 guard vs fresh ${kind} in same continuation`, async t => {
  const h = harbor(t, repo => copyFileSync(join(repo, 'tests/place-order.json'), join(repo, 'tests/second.json')));
  let lintPassed = false, aId = null;
  const f = await fakeRuntime(t, (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.method === 'POST' && e.command === 'lint') return { status: 202, json: f.job(id, 'lint', 'running') };
    const prior = f.posts.find(p => p.request.requestId === id);
    if (prior?.command === 'lint') return { status: 200, json: lintPassed ? f.lint(id) : f.job(id, 'lint', 'running') };
    if (e.method === 'POST') {
      if (e.request.scenario === 'tests/place-order.json') aId = id;
      return { status: 202, json: f.check(id, 'queued') };
    }
    if (id === aId) return kind === '410' ? { status: 410, json: {} } : { status: 200, json: f.check('99999999-9999-4999-8999-999999999999', 'running') };
    return { status: 200, json: f.check(id, 'running') };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  const first = portsFor(env);
  assert.equal(await runCheck({ cwd: h.repo, words: ['tests/place-order.json', 'tests/second.json'], options: { '--json': true, '--max-calls': 6 } }, first.ports), 3);
  const batch = readdirSync(join(h.state, 'batches'), { withFileTypes: true }).find(e => e.isDirectory()).name;
  lintPassed = true;
  const p = portsFor(env);
  const code = await runCheck({ cwd: h.repo, words: [batch], options: { '--read': true, '--json': true } }, p.ports);
  const json = JSON.parse(p.ports.stdout.text);
  const a = json.rows.find(r => r.test === 'tests/place-order.json'), b = json.rows.find(r => r.test === 'tests/second.json');
  const getsA = f.gets.filter(g => g.url.endsWith(aId)).length;
  // Expected by the lifecycle: A's own fresh GET said expired / wrong ID, so A is unknown.
  assert.match(a.why, kind === '410' ? /result expired/i : /another request ID or command/);
  assert.equal(a.state, 'unknown', `A shown as ${a.state} after a fresh ${kind} GET`);
});

// E3: interruption during --read with a cached running receipt.
test('E3 interrupted read keeps verified running cache', async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.method === 'POST' && e.command === 'lint') return { status: 200, json: f.lint(id) };
    return { status: 200, json: f.check(id, 'running') };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  const first = portsFor(env);
  await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--json': true } }, first.ports);
  const batch = readdirSync(join(h.state, 'batches'), { withFileTypes: true }).find(e => e.isDirectory()).name;
  const gets = f.gets.length;
  const p = portsFor(env, { onInterrupt: handler => { handler(); return () => {}; } });
  const code = await runCheck({ cwd: h.repo, words: [batch], options: { '--read': true, '--json': true } }, p.ports);
  const json = JSON.parse(p.ports.stdout.text);
  assert.equal(json.rows[0].state, 'running');
  assert.equal(f.gets.length, gets);
});
