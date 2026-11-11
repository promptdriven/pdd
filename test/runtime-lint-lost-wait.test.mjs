import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-seam.mjs';
import { captureSource } from '../src/runtime/runtime-preflight.mjs';
import { harbor, portsFor, PLACE, ordinaryCapabilities } from './runtime-fake.mjs';

// Synthetic public-boundary cases derived from runtime-client's Order GET rule:
// unconfirmed lost lint answers use the existing five-minute recovery policy;
// a confirmed queued/running receipt returns to ordinary unlimited Check waiting.
// All service replies, shell identity, time and interruption use injected ports.
async function lostLint(t, { interactive, confirmed = null, timeout } = {}) {
  const setup = harbor(t), posts = [], gets = [];
  let made, started, capture, safetyInterrupted = false;
  const job = (id, command, state, result = null) => ({ id, requestId: id, command, state, result,
    usage: { calls: command === 'check' ? 1 : 0 },
    engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15',
    report_url: `https://offline.invalid/r/${id}` });
  const fetch = async (url, init) => {
    const path = new URL(url).pathname;
    if (path === '/v1/capacity') return Response.json({}, { status: 404 });
    if (init.method === 'POST') {
      const request = JSON.parse(await init.body.get('request').text());
      const command = path.split('/').at(-1);
      posts.push({ command, id: request.requestId });
      assert.equal(request.source_sha256, capture.sha256);
      assert.deepEqual(Buffer.from(await init.body.get('source').arrayBuffer()), capture.tar);
      if (command === 'lint') throw new TypeError('Synthetic lost lint POST reply');
      return Response.json(job(request.requestId, 'check', 'passed', {
        outcome: 'Pass', report: { samples: [{ steps: [{ checks: [{ criterion_id: 'AC1',
          target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: 900, passed: true }] }] }] }
      }));
    }
    const id = path.split('/').at(-1), elapsed = made.clock.now - started;
    gets.push({ id, elapsed });
    if (!confirmed || elapsed < 240000) return Response.json({}, { status: 404 });
    if (elapsed < 420000) return Response.json(job(id, 'lint', confirmed));
    return Response.json(job(id, 'lint', 'passed', { exitCode: 0, refusals: [], report: {
      // Supplied ordinary support for the original upload, not an inference from a pass.
      verdict: 'passed', lint: { complete: true, tests: [{ path: 'tests/place-order.json', verdict: 'passed',
        capabilities: ordinaryCapabilities(capture.sources, 'tests/place-order.json') }] }, program: {
      prompts: [{ path: PLACE, admission_state: 'draft', interface: { calls: [] } }], refused_prompts: []
    } } }));
  };
  made = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: 'https://offline.invalid' }, { fetch, interactive,
    captureSource: (...args) => (capture = captureSource(...args)) });
  started = made.clock.now;
  const sleep = made.ports.sleep;
  made.ports.sleep = async ms => {
    await sleep(ms);
    // A missing recovery boundary must fail an assertion, never hang the suite.
    if (made.clock.now - started >= 600000) { safetyInterrupted = true; made.clock.interrupt(); }
  };
  const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options: {
    '--json': true, ...(timeout === undefined ? {} : { '--timeout': timeout })
  } }, made.ports);
  const json = JSON.parse(made.ports.stdout.text);
  const saved = JSON.parse(readFileSync(join(setup.state, 'batches', json.batch, 'batch.json')));
  return { code, json, saved, posts, gets, elapsed: made.clock.now - started,
    err: made.ports.stderr.text, safetyInterrupted };
}

function originalLintOnly(r) {
  const lint = r.posts.filter(post => post.command === 'lint');
  assert.equal(lint.length, 1, 'a lost reply never authorizes another lint POST');
  assert.ok(r.gets.length > 0);
  assert.ok(r.gets.every(get => get.id === lint[0].id), 'recover only the original lint request ID');
  assert.deepEqual(r.saved.lint.request_ids, [lint[0].id]);
}
function held(r) {
  originalLintOnly(r);
  assert.equal(r.posts.filter(post => post.command === 'check').length, 0);
  assert.equal(r.code, 3);
  assert.equal(r.json.exit_code, 3);
  assert.equal(r.json.rows[0].state, 'not run');
  assert.equal(r.json.rows[0].calls, 0);
  assert.equal(r.json.rows[0].request_id, null);
  assert.ok(r.err.includes(`pdd test --read ${r.json.batch}`), 'retain the saved recovery command');
}

for (const interactive of [false, true]) {
  const shell = interactive ? 'person' : 'agent';
  test(`LOST-LINT ${shell}: unconfirmed 404 recovery ends after five minutes`, async t => {
    const r = await lostLint(t, { interactive });
    assert.equal(r.safetyInterrupted, false, 'lost lint must end under its existing recovery policy before the safety interrupt');
    assert.equal(r.elapsed, 300000, 'five minutes with the injected 2-second receipt interval');
    held(r);
    assert.equal(r.saved.timeout_min, null, 'recovery policy must not become a caller timeout');
  });
  for (const confirmed of ['queued', 'running']) {
    test(`LOST-LINT ${shell}: confirmed ${confirmed} at four minutes may finish after five`, async t => {
      const r = await lostLint(t, { interactive, confirmed });
      assert.equal(r.safetyInterrupted, false);
      assert.equal(r.code, 0);
      assert.equal(r.json.exit_code, 0);
      assert.ok(r.elapsed >= 420000 && r.elapsed <= 422000, 'confirmed lint waits through its seven-minute completion');
      originalLintOnly(r);
      assert.equal(r.posts.filter(post => post.command === 'check').length, 1);
      assert.equal(r.json.rows[0].state, 'passed');
      assert.equal(r.saved.timeout_min, null);
    });
  }
  test(`LOST-LINT ${shell}: explicit timeout bounds preliminary lint recovery`, async t => {
    const r = await lostLint(t, { interactive, timeout: 1 });
    assert.equal(r.safetyInterrupted, false);
    assert.equal(r.elapsed, 60000);
    held(r);
    assert.equal(r.saved.timeout_min, 1);
  });
}
