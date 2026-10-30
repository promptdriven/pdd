// Reviewer probe: a busy row whose next retry claim was written but not saved.
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';
const X = '88888888-8888-4888-8888-888888888888';
const capacity = (f, id) => f.job(id, 'check', 'refused', { outcome: 'Inconclusive', why: 'No verdict. Queue full.', next_step: 'RETRY LATER',
  refusals: [{ code: 'check-queue-timeout', details: { retryable: true, retry_after: 1 } }], report: { dispatch: 'not_started', provider_calls: 0, samples: [] } }, 0);

for (const response of ['lost', '404']) test(`RELAY busy row + unsaved retry claim ${response}`, async t => {
  const h = harbor(t); let busy = true;
  const f = await fakeRuntime(t, (e, f) => {
    if (e.method === 'POST' && e.command === 'check') return busy ? { status: 200, json: capacity(f, e.request.requestId) } : { status: 202, json: f.check(e.request.requestId, 'queued') };
    const id = e.url?.split('/').at(-1);
    if (e.method === 'GET' && id === X) return response === 'lost' ? { destroy: true } : response === '404' ? { status: 404, json: {} } : { status: 200, json: f.check(X, 'running') };
    return f.normal(e);
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  const first = portsFor(env);
  await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--json': true } }, first.ports);
  const batch = JSON.parse(first.ports.stdout.text).batch;
  const folder = join(h.state, 'batches', batch), doc = JSON.parse(readFileSync(join(folder, 'batch.json')));
  const row = doc.rows[0];
  row.next_step = 'Start another check now.';
  writeFileSync(join(folder, 'batch.json'), JSON.stringify(doc));
  const posted = f.posts.filter(p => p.command === 'check').length;
  const key = createHash('sha256').update(row.test).digest('hex');
  writeFileSync(join(folder, `${key}.${row.request_ids.length}.dispatch.json`), JSON.stringify({ id: X }));
  busy = false;
  const p = portsFor(env);
  const code = await runCheck({ cwd: h.repo, words: [], options: { '--retry': batch, '--json': true } }, p.ports);
  const out = JSON.parse(p.ports.stdout.text).rows[0];
  const after = f.posts.filter(p => p.command === 'check').length;
  assert.equal(out.request_id, X);
  assert.equal(out.state, 'unknown');
  assert.equal(out.calls, 'unknown');
  assert.equal(out.busy, false); assert.equal(out.can_retry, false);
  assert.equal(out.next_step, null); assert.equal(p.clock.uuids, 0);
  assert.equal(after - posted, 0, 'possibly-sent claim X must not be followed by a new paid POST');
});
