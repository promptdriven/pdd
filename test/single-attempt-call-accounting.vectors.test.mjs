import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';
import { projectAnswer, renderJson, runCheck } from '../src/runtime-seam.mjs';
import { savedLostCheck } from '../src/workflow-results.mjs';
import { harbor, ordinaryCapabilities, portsFor } from './helpers/runtime-fake.mjs';

const ENGINE = 'eae2202a68d00ab762fcbbf1eba0d8607a132a15';

function pointer(value, path) {
  if (!path || path === '/') return value;
  return path.slice(1).split('/').reduce((current, part) => current?.[part.replaceAll('~1', '/').replaceAll('~0', '~')], value);
}

async function memoryCheckRuntime(setup, handlers) {
  const fake = { checkPosts: [], gets: [], origin: 'https://runtime.invalid' };
  const decode = async form => ({
    request: JSON.parse(await form.get('request').text()),
    tar: Buffer.from(await form.get('source').arrayBuffer()),
  });
  const job = (id, command, state, result, calls = 0) => ({
    requestId: id, id, command, state, engine_sha: ENGINE,
    result,
    usage: { calls, model: 'unknown', requested_model: calls ? 'gpt-6.1-sol' : 'unknown', seconds: 0 },
    report_url: `https://runtime.invalid/r/${id}`,
  });
  fake.job = job;
  const fetch = async (input, init = {}) => {
    const url = new URL(input), method = init.method ?? 'GET';
    if (url.pathname === '/v1/capacity')
      return Response.json({ error: { code: 'not-found' } }, { status: 404 });
    if (method === 'POST' && url.pathname === '/v1/lint') {
      const { request, tar } = await decode(init.body);
      const listing = spawnSync('tar', ['-tf', '-'], { input: tar, encoding: 'utf8' });
      const sources = listing.stdout.split('\n').filter(Boolean).map(path => ({
        path, bytes: spawnSync('tar', ['-xOf', '-', path], { input: tar }).stdout,
      }));
      const paths = sources.filter(source => { try { return JSON.parse(source.bytes).schema_version === 'prompt-runtime.program-scenario.v1'; } catch { return false; } }).map(source => source.path);
      const tests = paths.map(path => ({ path, verdict: 'passed' }));
      const capabilities = paths.map(path => ({ path, report: ordinaryCapabilities(sources, path) }));
      const result = { exitCode: 0, refusals: [], capabilities, capabilities_complete: true,
        report: { verdict: 'passed', lint: { complete: true, tests }, program: { prompts: [{ path: 'prompts/place_order.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } }] } } };
      return Response.json(job(request.requestId, 'lint', 'passed', result));
    }
    if (method === 'POST' && url.pathname === '/v1/check') {
      const { request } = await decode(init.body);
      fake.checkPosts.push(request);
      const reply = await handlers.check(request, fake);
      return new Response(JSON.stringify(reply.json), { status: reply.status, headers: { 'content-type': 'application/json' } });
    }
    if (method === 'GET' && url.pathname.startsWith('/v1/runs/')) {
      const id = url.pathname.split('/').at(-1);
      fake.gets.push(id);
      const reply = handlers.get ? await handlers.get(id, fake) : { status: 404, json: { error: { code: 'not-found' } } };
      return new Response(JSON.stringify(reply.json), { status: reply.status, headers: { 'content-type': 'application/json' } });
    }
    assert.fail(`unexpected request: ${method} ${url.pathname}`);
  };
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };
  return { fake, env, ...portsFor(env, { fetch }), fetch };
}

test('3277 vectors: replay single-attempt-call-accounting-3277 scenario against native runtime-output', () => {
  const scenario = JSON.parse(readFileSync('test/runtime/single-attempt-call-accounting-3277.json', 'utf8'));
  const operations = { projectAnswer, renderJson };
  for (const step of scenario.steps) {
    const result = operations[step.operation](structuredClone(step.input));
    for (const check of step.checks) {
      assert.equal(check.target, 'result');
      assert.equal(check.op, 'equals');
      assert.deepEqual(pointer(result, check.path), check.value, `${step.step_id} ${check.path}`);
    }
  }
});

test('3277 e2e: explicit known_calls=33 with unknown_calls=1 and provider_calls=34 stays 33+1 across runCheck, --read and savedLostCheck', async t => {
  const setup = harbor(t);
  const receipt = (fake, id) => {
    const refusal = { code: 'graph-uncertain-child-dispatch', message: 'Child dispatch uncertain.', cause: 'ai-service' };
    const answer = fake.job(id, 'check', 'unknown', {
      exitCode: 3,
      refusals: [refusal],
      report: { provider_calls: 34, accounting_complete: true, refusal, call_usage: { known_calls: 33, unknown_calls: 1 }, samples: [] },
    }, 34);
    answer.accounting_complete = true;
    Object.assign(answer.usage, { known_calls: 33, unknown_calls: 1, accounting_complete: true });
    return answer;
  };
  const { fake, env, ports, fetch } = await memoryCheckRuntime(setup, {
    check: (request, f) => ({ status: 200, json: receipt(f, request.requestId) }),
    get: (id, f) => ({ status: 200, json: receipt(f, id) }),
  });
  const code = await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: setup.repo }, ports);
  assert.equal(code, 3);
  const initial = JSON.parse(ports.stdout.text), row = initial.rows[0];
  assert.equal(row.calls, 'unknown');
  assert.equal(row.known_calls, 33);
  assert.equal(row.unknown_calls, 1);
  assert.equal(row.accounting_complete, false);
  assert.match(initial.summary_line, /33 AI calls \+ 1 unknown$/);

  const lost = savedLostCheck(initial.batch, { env, root: setup.repo });
  assert.equal(lost.cost.calls, null);
  assert.equal(lost.cost.knownCalls, 33);

  const batchPorts = portsFor(env, { fetch }).ports;
  assert.equal(await runCheck({ words: [initial.batch], options: { '--read': true, '--json': true }, cwd: setup.repo }, batchPorts), 3);
  const batchRead = JSON.parse(batchPorts.stdout.text);
  assert.equal(batchRead.rows[0].known_calls, 33);
  assert.equal(batchRead.rows[0].unknown_calls, 1);
  assert.match(batchRead.summary_line, /33 AI calls \+ 1 unknown$/);

  const uuidPorts = portsFor(env, { fetch }).ports;
  assert.equal(await runCheck({ words: [row.request_id], options: { '--read': true, '--json': true }, cwd: setup.repo }, uuidPorts), 3);
  const uuidRead = JSON.parse(uuidPorts.stdout.text);
  assert.equal(uuidRead.rows[0].known_calls, 33);
  assert.equal(uuidRead.rows[0].unknown_calls, 1);
  assert.match(uuidRead.summary_line, /33 AI calls \+ 1 unknown$/);
});

test('3277 e2e: omitted known_calls subtracts unknown_calls from calls and provider_calls without underflow', async t => {
  const setup = harbor(t);
  const { fake, ports } = await memoryCheckRuntime(setup, {
    check: (request, f) => {
      const answer = f.job(request.requestId, 'check', 'unknown', {
        exitCode: 3,
        report: { provider_calls: 34, samples: [] },
      }, 34);
      Object.assign(answer.usage, { unknown_calls: 1 });
      return { status: 200, json: answer };
    },
  });
  const code = await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: setup.repo }, ports);
  assert.equal(code, 3);
  const json = JSON.parse(ports.stdout.text);
  assert.equal(json.rows[0].calls, 'unknown');
  assert.equal(json.rows[0].known_calls, 33);
  assert.equal(json.rows[0].unknown_calls, 1);
  assert.equal(json.rows[0].accounting_complete, false);
  assert.match(json.summary_line, /33 AI calls \+ 1 unknown$/);

  const clamped = projectAnswer({ command: 'check', state: 'unknown', usage: { calls: 1, unknown_calls: 3 }, result: { report: { provider_calls: 1, samples: [] } } });
  assert.equal(clamped.known_calls, 0);
  assert.equal(clamped.unknown_calls, 3);
  assert.equal(clamped.accounting_complete, false);

  const disagreed = projectAnswer({ command: 'check', state: 'passed', accounting_complete: true, usage: { calls: 2, accounting_complete: true }, result: { report: { provider_calls: 5, accounting_complete: true, samples: [] } } });
  assert.equal(disagreed.calls, 'unknown');
  assert.equal(disagreed.known_calls, 5);
  assert.equal(disagreed.unknown_calls, 1);
  assert.equal(disagreed.accounting_complete, false);
});

test('3277 e2e: restart replacement (#3007) sums disjoint known_calls across attempts without double-counting provider_calls', async t => {
  const setup = harbor(t);
  const { fake, ports } = await memoryCheckRuntime(setup, {
    check: (request, f) => {
      if (f.checkPosts.length === 1) {
        const refusal = { code: 'service-restarted', message: 'Interpreter restarted.' };
        const first = f.job(request.requestId, 'check', 'unknown', {
          exitCode: 3,
          refusals: [refusal],
          report: { provider_calls: 34, refusal, samples: [] },
        }, 34);
        Object.assign(first.usage, { known_calls: 33, unknown_calls: 1, accounting_complete: false });
        return { status: 200, json: first };
      }
      const second = f.job(request.requestId, 'check', 'passed', {
        exitCode: 0,
        report: { provider_calls: 4, accounting_complete: true, samples: [] },
      }, 4);
      second.accounting_complete = true;
      Object.assign(second.usage, { known_calls: 4, unknown_calls: 0, accounting_complete: true });
      return { status: 200, json: second };
    },
  });
  const code = await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: setup.repo }, ports);
  assert.equal(code, 0);
  assert.equal(fake.checkPosts.length, 2);
  const json = JSON.parse(ports.stdout.text), row = json.rows[0];
  assert.equal(row.calls, 'unknown');
  assert.equal(row.known_calls, 37);
  assert.equal(row.unknown_calls, 1);
  assert.equal(row.accounting_complete, false);
  assert.match(json.summary_line, /37 AI calls \+ 1 unknown$/);
  const savedBatch = JSON.parse(readFileSync(join(setup.state, 'batches', json.batch, 'batch.json'), 'utf8'));
  assert.equal(savedBatch.rows[0].request_ids.length, 2);
});
