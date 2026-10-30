import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync, copyFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// The merged contract requires lint continuation and no-verdict evidence together:
// a saved held row may gain one ID, while a prior unknown ID is never replayed.
for (const retry of [false, true]) test(`RELAY held lint + no verdict + unknown via ${retry ? 'retry' : 'read'}`, async t => {
  const h = harbor(t, repo => copyFileSync(join(repo, 'tests/place-order.json'), join(repo, 'tests/second.json')));
  let lintPassed = false, lostId = null;
  const oldId = '77777777-7777-4777-8777-777777777777';
  const why = 'No verdict. The service could not judge this check.';
  const nextStep = 'Tell the person the service reason; do not change expected values.';
  const f = await fakeRuntime(t, (e, f) => {
    const id = e.request?.requestId ?? e.url.split('/').at(-1);
    if (e.method === 'POST' && e.command === 'lint') return { status: 202, json: f.job(id, 'lint', 'running') };
    const prior = f.posts.find(p => p.request.requestId === id);
    if (prior?.command === 'lint') return { status: 200, json: lintPassed ? f.lint(id) : f.job(id, 'lint', 'running') };
    if (id === oldId || id === lostId) return { status: 404, json: {} };
    const answer = f.check(id, 'refused', [], [{ code: 'service-unavailable', message: 'Service unavailable.' }]);
    Object.assign(answer.result, { why, next_step: nextStep });
    answer.usage.calls = 2;
    return { status: 200, json: answer };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  const first = portsFor(env);
  assert.equal(await runCheck({ cwd: h.repo, words: ['tests/place-order.json', 'tests/second.json'], options: { '--json': true, '--max-calls': 6 } }, first.ports), 3);
  assert.equal(f.posts.filter(p => p.command === 'check').length, 0);
  const batch = readdirSync(join(h.state, 'batches'), { withFileTypes: true }).find(e => e.isDirectory()).name;
  const path = join(h.state, 'batches', batch, 'batch.json');
  const doc = JSON.parse(readFileSync(path));
  assert.equal(doc.rows[0].phase, 'lint');
  assert.equal(doc.rows[0].calls, 0);
  Object.assign(doc.rows[1], { request_ids: [oldId], state: 'unknown', phase: 'server', note: null, why: 'Checks failed.' });
  writeFileSync(path, JSON.stringify(doc));
  lintPassed = true;
  const recover = async () => {
    const p = portsFor(env);
    const code = await runCheck({ cwd: h.repo, words: retry ? [] : [batch], options: { [retry ? '--retry' : '--read']: retry ? batch : true, '--json': true } }, p.ports);
    return { code, p, json: JSON.parse(p.ports.stdout.text) };
  };
  const result = await recover();
  assert.equal(result.code, 3, 'the prior unknown row keeps exit-three precedence');
  const paid = f.posts.filter(p => p.command === 'check');
  assert.equal(paid.length, 1, 'only the lint-held row gets its first paid POST');
  assert.equal(paid[0].request.max_calls, 6);
  assert.equal(paid[0].request.source_sha256, doc.source_sha256);
  assert.equal(f.posts.filter(p => p.command === 'lint').length, 1, 'reuse completed lint');
  const [refused, unknown] = result.json.rows;
  assert.equal(refused.state, 'refused'); assert.equal(refused.why, why); assert.equal(refused.next_step, nextStep);
  assert.equal(refused.calls, 2, 'server usage replaces local zero'); assert.equal(refused.checks, null);
  assert.equal(unknown.state, 'unknown'); assert.equal(unknown.request_id, oldId); assert.equal(unknown.calls, 'unknown');
  assert.notEqual(unknown.why, 'Checks failed.');
  const kept = JSON.parse(readFileSync(path));
  assert.equal(kept.rows[0].next_step, nextStep, 'batch persists independent no-verdict advice');
  assert.deepEqual(kept.rows[1].request_ids, [oldId]);
  const again = await recover();
  assert.equal(again.p.clock.uuids, 0); assert.equal(f.posts.filter(p => p.command === 'check').length, 1);
  assert.equal(again.json.rows[0].request_id, refused.request_id);
  assert.equal(again.json.rows[0].next_step, nextStep);
  // In contrast to a truly local fixture, an existing claim must restore an
  // erased batch ID and retain uncertain usage after its receipt is lost.
  const damaged = JSON.parse(readFileSync(path));
  lostId = refused.request_id;
  Object.assign(damaged.rows[0], { request_ids: [], state: 'not_run', phase: 'local', calls: 0 });
  writeFileSync(path, JSON.stringify(damaged));
  rmSync(join(h.state, 'batches', batch, `${lostId}.json`));
  const recovered = await recover();
  assert.equal(recovered.json.rows[0].request_id, lostId);
  assert.equal(recovered.json.rows[0].state, 'unknown');
  assert.equal(recovered.json.rows[0].calls, 'unknown');
  assert.equal(recovered.p.clock.uuids, 0);
  assert.equal(f.posts.filter(p => p.command === 'check').length, 1);
});
