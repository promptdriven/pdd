import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-seam.mjs';
import { readRunResults, resultLines } from '../src/workflow-results.mjs';
import { fakeRuntime, harbor, portsFor, storyTest } from './runtime-fake.mjs';

const envFor = (h, f) => ({ HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin });
const readBatch = h => {
  const batches = readdirSync(join(h.state, 'batches'));
  assert.equal(batches.length, 1);
  return JSON.parse(readFileSync(join(h.state, 'batches', batches[0], 'batch.json')));
};

// AC1/AC4: the caller stop cause wins over a capacity default, at either lint boundary.
for (const mode of ['explicit-lint', 'default-lint', 'free-lint']) {
  for (const boundary of ['maintenance', 'queue']) for (const json of [true, false]) {
    test(`wait reasons: ${mode} ${boundary} retains its deadline in ${json ? 'JSON' : 'text'}`, async t => {
      const h = harbor(t);
      const f = await fakeRuntime(t, (e, f) => {
        assert.equal(boundary, 'queue', 'maintenance must prevent POST');
        assert.equal(e.command, 'lint', 'unadmitted lint must prevent paid checks');
        const refusal = { code: 'lint-queue-timeout', details: { retryable: true, retry_after: 120 } };
        return { status: 200, json: f.job(e.request.requestId, 'lint', 'refused', { report: { refusal } }) };
      });
      const env = envFor(h, f), p = portsFor(env), started = p.clock.now;
      if (boundary === 'maintenance') f.capacity = () => ({ status: 200, json: {
        maintenance: { until: new Date(started + 600_000).toISOString(), reason: 'deploy' }
      } });
      const options = { ...(mode !== 'free-lint' ? { '--lint': true } : {}),
        ...(mode !== 'default-lint' ? { '--timeout': 1 } : {}), ...(json ? { '--json': true } : {}) };
      assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options }, p.ports), 5);
      const expected = mode === 'explicit-lint' ? 'timeout-flag' : 'deadline';
      if (json) {
        const result = JSON.parse(p.ports.stdout.text);
        assert.equal(result.rows[0].state, 'not run');
        assert.equal(result.rows[0].reason?.code, expected);
        if (mode === 'explicit-lint') assert.match(result.rows[0].reason.message, /--timeout/);
      } else {
        assert.ok(p.ports.stdout.text.includes(expected), `text row must include ${expected}`);
      }
      const saved = readBatch(h);
      for (const row of [saved.rows[0], saved.lint]) {
        assert.equal(row.state, 'not run');
        assert.equal(row.reason.code, expected);
        if (mode === 'explicit-lint') assert.match(row.reason.message, /--timeout/);
        else assert.doesNotMatch(row.reason.message, /--timeout/);
      }
      if (mode === 'explicit-lint') assert.match(p.ports.stderr.text, /--timeout/);
      assert.equal(p.clock.now - started, mode === 'default-lint' ? 90_000 : 60_000);
      assert.equal(f.posts.length, boundary === 'maintenance' ? 0 : 1);
      assert.doesNotMatch(p.ports.stderr.text, /\bSent\b/);
    });
  }
}

// AC1/AC4: preserve the stop cause and the separate, fully accounted capacity receipt.
for (const json of [true, false]) test(`wait reasons: busy Check timeout survives ${json ? 'JSON' : 'text'}, saved results and evidence`, async t => {
  const h = harbor(t);
  const f = await fakeRuntime(t, (e, f) => {
    if (e.command === 'lint') return { status: 200, json: f.lint(e.request.requestId) };
    const refusal = { code: 'check-queue-timeout', retryable: true, details: { retryable: true, retry_after: 120 }, message: 'Queue busy' };
    const answer = f.job(e.request.requestId, 'check', 'refused', { refusals: [refusal],
      report: { dispatch: 'not_started', provider_calls: 0, accounting_complete: true, refusal, samples: [] } }, 0);
    Object.assign(answer.usage, { provider_calls: 0, known_calls: 0, unknown_calls: 0, accounting_complete: true });
    return { status: 200, json: answer };
  });
  const env = envFor(h, f), p = portsFor(env), started = p.clock.now;
  assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--timeout': 1, ...(json ? { '--json': true } : {}) } }, p.ports), 5);
  if (json) {
    const r = JSON.parse(p.ports.stdout.text);
    assert.equal(r.rows[0].state, 'not run');
    assert.equal(r.rows[0].reason?.code, 'timeout-flag');
    assert.match(r.rows[0].reason.message, /--timeout/);
    assert.match(r.summary_line, /timeout-flag/);
  } else {
    assert.match(p.ports.stdout.text, /timeout-flag/);
    assert.match(p.ports.stdout.text, /--timeout/);
  }
  const saved = readBatch(h), row = saved.rows[0];
  assert.equal(row.reason.code, 'timeout-flag');
  assert.match(row.reason.message, /--timeout/);
  const receipt = JSON.parse(readFileSync(join(h.state, 'batches', saved.batch, `${row.request_ids[0]}.json`)));
  assert.equal(receipt.result.report.dispatch, 'not_started');
  assert.equal(receipt.result.report.refusal.code, 'check-queue-timeout');
  const evidence = resultLines(readRunResults({ root: h.repo }, { env, capture: () => ({ sha256: saved.source_sha256 }) })).join('\n');
  assert.match(evidence, /timeout-flag/);
  assert.equal(p.clock.now - started, 60_000);
  assert.equal(f.posts.filter(post => post.command === 'check').length, 1);
  assert.doesNotMatch(p.ports.stderr.text, /\bSent\b/);
});

// AC1: one invalid limit prevents this lint request; unaffected selected tests have no verdict.
test('wait reasons: a local limits refusal gives every text and JSON row a reason', async t => {
  const h = harbor(t);
  storyTest(h.repo, 'other');
  const promptPath = join(h.repo, 'prompts/place_order.prompt.md'), prompt = readFileSync(promptPath, 'utf8');
  writeFileSync(join(h.repo, 'prompts/other.prompt.md'), prompt);
  writeFileSync(promptPath, prompt.replace('"max_steps": 4', '"max_steps": -1'));
  const otherPath = join(h.repo, 'tests/other.json'), other = JSON.parse(readFileSync(otherPath));
  other.steps[0].entry_path = 'prompts/other.prompt.md';
  writeFileSync(otherPath, JSON.stringify(other));
  const env = { HOME: h.home, PDD_STATE_DIR: h.state }, outputs = [];
  for (const json of [true, false]) {
    const p = portsFor(env);
    assert.equal(await runCheck({ cwd: h.repo, words: ['place-order', 'other'], options: { '--lint': true, ...(json ? { '--json': true } : {}) } }, p.ports), 4);
    assert.equal(p.clock.gh.length, 0, 'local refusal must not authenticate');
    outputs.push(p.ports.stdout.text);
  }
  const rows = JSON.parse(outputs[0]).rows;
  assert.deepEqual(rows.map(row => [row.test, row.state, row.reason?.code]).sort(([a], [b]) => a.localeCompare(b)), [
    ['tests/other.json', 'not run', 'no-server-verdict'], ['tests/place-order.json', 'refused', 'invalid-limits']
  ]);
  for (const row of rows) {
    const line = outputs[1].split('\n').find(line => line.includes(row.test));
    assert.ok(line?.includes(row.state), `text must retain the state for ${row.test}`);
    assert.ok(line?.includes(row.reason.code), `text must retain the reason code for ${row.test}`);
  }
});
