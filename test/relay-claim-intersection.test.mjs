import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync, copyFileSync } from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';
const CLAIMED = '99999999-9999-4999-8999-999999999999';
const WHY = 'No verdict. The judge service was unavailable for this check.';
const NEXT = 'Tell the person; do not change expected values.';

// shape: how the saved row looks at the crash. server: what GET of the claimed ID says.
const cases = [
  ['held', 'missing'], ['held', 'running'], ['held', 'refused'], ['held', 'incomplete'],
  ['ready', 'missing'], ['local', 'missing'], ['local', 'refused'],
];
for (const [shape, server] of cases) for (const mode of ['read', 'retry']) test(`RELAY claim without ID: ${shape} row, server ${server}, via ${mode}`, async t => {
  const h = harbor(t, repo => copyFileSync(join(repo, 'tests/place-order.json'), join(repo, 'tests/second.json')));
  let lintPassed = false;
  const f = await fakeRuntime(t, (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.method === 'POST' && e.command === 'lint') return { status: 202, json: f.job(id, 'lint', 'running') };
    const prior = f.posts.find(p => p.request.requestId === id);
    if (prior?.command === 'lint') return { status: 200, json: lintPassed ? f.lint(id) : f.job(id, 'lint', 'running') };
    if (e.method === 'POST') return { status: 202, json: f.check(id, 'queued') };
    if (id === CLAIMED) {
      if (server === 'missing') return { status: 404, json: {} };
      if (server === 'running') return { status: 200, json: f.check(id, 'running') };
      if (server === 'refused') {
        const a = f.check(id, 'refused', [], [{ code: 'service-unavailable', message: 'Service unavailable.' }]);
        Object.assign(a.result, { why: WHY, next_step: NEXT }); a.usage.calls = 2;
        return { status: 200, json: a };
      }
    }
    return { status: 200, json: f.check(id) };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  assert.equal(await runCheck({ cwd: h.repo, words: ['tests/place-order.json', 'tests/second.json'], options: { '--json': true, '--max-calls': 6 } }, portsFor(env).ports), 3);
  assert.equal(f.posts.filter(p => p.command === 'check').length, 0);
  const batch = readdirSync(join(h.state, 'batches'), { withFileTypes: true }).find(e => e.isDirectory()).name;
  const folder = join(h.state, 'batches', batch), path = join(folder, 'batch.json');
  const doc = JSON.parse(readFileSync(path));
  const row = doc.rows[0];
  assert.equal(row.phase, 'lint'); assert.equal(row.calls, 0); assert.deepEqual(row.request_ids, []);
  // The crash state: a claim exists for attempt 0, the saved row has no request ID.
  if (shape === 'ready') Object.assign(row, { state: 'ready', phase: 'server', note: null, eligible: true });
  if (shape === 'local') Object.assign(row, { state: 'not_run', phase: 'local', calls: 0, why: 'The local check was never sent.', note: { code: null, message: 'pdd stopped before sending this check.' } });
  writeFileSync(path, JSON.stringify(doc));
  const key = createHash('sha256').update(row.test).digest('hex');
  writeFileSync(join(folder, `${key}.0.dispatch.json`), server === 'incomplete' ? '' : JSON.stringify({ id: CLAIMED }));
  lintPassed = true;
  const p = portsFor(env);
  const code = await runCheck({ cwd: h.repo, words: mode === 'retry' ? [] : [batch], options: { [mode === 'retry' ? '--retry' : '--read']: mode === 'retry' ? batch : true, '--json': true } }, p.ports);
  const out = JSON.parse(p.ports.stdout.text).rows[0];
  const paid = f.posts.filter(p => p.command === 'check');
  // The claimed row is never replayed; only the second (genuinely held) row may get its first POST.
  assert.ok(!paid.some(p => p.request.scenario === row.test), 'claimed row is not POSTed again');
  assert.ok(!readdirSync(folder).includes(`${key}.1.dispatch.json`), 'no second claim');
  if (server === 'incomplete') {
    assert.equal(out.state, 'unknown'); assert.equal(out.calls, 'unknown'); assert.equal(out.request_id, null);
    assert.match(out.why ?? '', /interrupted dispatch claim/);
    assert.notEqual(code, 0);
    return;
  }
  assert.equal(out.request_id, CLAIMED);
  if (server === 'refused') {
    assert.equal(code, 4, 'refused beside a passed check');
    assert.equal(out.state, 'refused'); assert.equal(out.calls, 2, 'server usage, not a local zero');
    assert.equal(out.why, WHY); assert.equal(out.next_step, NEXT);
    assert.equal(JSON.parse(readFileSync(path)).rows[0].next_step, NEXT);
  } else {
    assert.equal(code, 3);
    assert.equal(out.state, server === 'running' ? 'running' : 'unknown');
    if (server === 'running') assert.notEqual(out.calls, 0, 'server usage, never a local zero'); else assert.equal(out.calls, 'unknown', 'possibly sent: usage stays unknown');
    assert.notEqual(out.why, 'Checks failed.');
    assert.notEqual(out.why, 'The local check was never sent.', 'claim adoption clears specific stale local why');
  }
  assert.doesNotMatch(JSON.stringify(out.reason ?? {}), /stopped before sending/, 'a claimed row keeps no local never-sent reason');
  const kept = JSON.parse(readFileSync(path)).rows[0];
  assert.deepEqual(kept.request_ids, [CLAIMED]);
  assert.equal(Object.hasOwn(kept, 'calls'), false, 'no zero-call evidence persisted for a claimed row');
  assert.notEqual(kept.phase, 'local');
  // Text mode must not call it "not sent, 0 AI calls".
  const q = portsFor(env);
  await runCheck({ cwd: h.repo, words: [batch], options: { '--read': true } }, q.ports);
  assert.doesNotMatch(q.ports.stdout.text, /not sent, 0 AI calls|stopped before sending/);
  assert.equal(q.clock.uuids, 0);
});
