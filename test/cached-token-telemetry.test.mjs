import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { request } from 'node:http';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import {
  PROMPT_TESTS_WORDS,
  checkInput,
  interfaceBlocks,
  jsonRow,
  openServe,
  projectAnswer,
  renderJson,
  renderText,
  runCheck,
  runtimeOutputSlice,
  tryUsage,
  tryUsageHeaders,
  tryUsageLine,
} from '../src/runtime-seam.mjs';
import { CACHED_INPUT_WEIGHT, applyCostMeasurement, captureCosts, costReport, costStatusLines } from '../src/cost-ledger.mjs';

const { tokenUsageOf } = runtimeOutputSlice();
import { fakeRuntime, harbor, PLACE, portsFor, TOKEN } from './runtime-fake.mjs';

const ORIGIN = 'https://runtime.example';

function checkAnswer({
  id = '11111111-1111-4111-8111-111111111111',
  state = 'passed',
  usage = { calls: 1, requested_model: 'gpt-5.4', seconds: 4.2, input_tokens: 4096, cached_input_tokens: 3840, output_tokens: 256 },
  model_usage = {
    schema_version: 'prompt-runtime.program-model-usage.v1',
    calls: [
      { step_id: 'run', origin: 'current', dispatch_state: 'completed', usage_status: 'reported', input_tokens: 4096, cached_input_tokens: 3840, cached_input_share: 0.9375, share_status: 'reported' },
    ],
    totals: { input_tokens: 4096, cached_input_tokens: 3840, cached_input_share: 0.9375, complete: true },
  },
  extra = {},
  reportExtra = {},
} = {}) {
  return {
    id,
    command: 'check',
    state,
    usage,
    ...extra,
    result: {
      ...(extra.result ?? {}),
      report: {
        criterion_results: [{ criterion_id: 'AC1', status: 'passed' }],
        samples: [{ steps: [{ step_id: 'run', checks: [{ criterion_id: 'AC1', target: 'result', path: '/ok', expected: true, actual: true, passed: true }] }] }],
        ...(model_usage !== undefined ? { model_usage } : {}),
        ...reportExtra,
      },
    },
  };
}

test('AC1: projectAnswer, renderJson and renderText surface cached_input_tokens and cache-hit share while excluding historical replay calls and keeping Prompt tests lines compatible', () => {
  const answer = checkAnswer({
    usage: { calls: 1, requested_model: 'gpt-5.4', seconds: 4.2, output_tokens: 256 },
    model_usage: {
      schema_version: 'prompt-runtime.program-model-usage.v1',
      calls: [
        { step_id: 'seed', origin: 'historical', dispatch_state: 'completed', usage_status: 'reported', input_tokens: 8192, cached_input_tokens: 8192, cached_input_share: 1, share_status: 'reported' },
        { step_id: 'run', origin: 'current', dispatch_state: 'completed', usage_status: 'reported', input_tokens: 4096, cached_input_tokens: 3840, cached_input_share: 0.9375, share_status: 'reported' },
      ],
      totals: { input_tokens: 4096, cached_input_tokens: 3840, cached_input_share: 0.9375, complete: true },
    },
  });
  const view = projectAnswer(answer, { origin: ORIGIN, test: 'tests/cache-demo.json' });
  assert.equal(view.input_tokens, 4096);
  assert.equal(view.cached_input_tokens, 3840);
  assert.equal(view.output_tokens, 256);
  assert.equal(view.cached_input_share, 0.9375);

  const row = { story: 'cache-demo', title: 'Cache demo', test: 'tests/cache-demo.json', phase: 'server', request_ids: [answer.id], seconds: 4.2, ...view };
  const json = renderJson({ batch: '20261112-140000-demo', repo: '/repo', rows: [row], exitCode: 0 });
  assert.deepEqual(json.token_usage, {
    input_tokens: 4096,
    cached_input_tokens: 3840,
    output_tokens: 256,
    cached_input_share: 0.9375,
    complete: true,
  });
  assert.equal(json.rows[0].input_tokens, 4096);
  assert.equal(json.rows[0].cached_input_tokens, 3840);
  assert.equal(json.rows[0].output_tokens, 256);
  assert.equal(json.rows[0].cached_input_share, 0.9375);

  // Verify backward-compatible Prompt tests PR paste line and Runtime interface result_schema.
  assert.equal(json.summary_line, 'Prompt tests: ✓ 1 of 1 criterion · 1/1 checks · 1 AI call');
  assert.match(json.rows[0].summary_line, new RegExp(`^${PROMPT_TESTS_WORDS} \\(cache-demo\\): ✓ 1 of 1 criterion · 1/1 checks · 1 AI call$`));

  const promptText = fs.readFileSync(new URL('../prompts/cli/runtime-output.prompt.md', import.meta.url), 'utf8');
  const iface = JSON.parse(interfaceBlocks(promptText)[0][1]);
  const minimalOut = renderJson({ repo: '/repo', rows: [{ story: 'cache-demo', title: 'Cache demo', test: 'tests/cache-demo.json', state: 'passed', calls: 1, input_tokens: 4096, cached_input_tokens: 3840, output_tokens: 256, cached_input_share: 0.9375 }], exitCode: 0 });
  assert.deepEqual(checkInput(minimalOut, iface.entries[0].result_schema, 0).refusals, []);

  const text = renderText({ batch: '20261112-140000-demo', rows: [row], details: true, exitCode: 0 });
  assert.match(text, /^Prompt tests \(cache-demo\): ✓ 1 of 1 criterion · 1\/1 checks · 1 AI call$/m);
  assert.match(text, /^  Tokens: 4096 input \(3840 cached, 93\.8%\) · 256 output$/m);
  assert.match(text, /^Token usage: 4096 input \(3840 cached, 93\.8%\) · 256 output\.$/m);
});

test('AC1: strictly distinguishes measured 0 cached tokens, zero-input denominator, incomplete/unavailable accounting, and pre-dispatch receipts', () => {
  // 1. Measured 0 cached tokens with positive input -> cached_input_tokens: 0, cached_input_share: 0
  const zeroCached = projectAnswer(checkAnswer({
    usage: { calls: 1, input_tokens: 2000, cached_input_tokens: 0, output_tokens: 100 },
    model_usage: { totals: { input_tokens: 2000, cached_input_tokens: 0, cached_input_share: 0, complete: true } },
  }), { origin: ORIGIN });
  assert.deepEqual(
    { in: zeroCached.input_tokens, cached: zeroCached.cached_input_tokens, out: zeroCached.output_tokens, share: zeroCached.cached_input_share },
    { in: 2000, cached: 0, out: 100, share: 0 },
  );
  const zeroCachedText = renderText({ batch: 'b', rows: [{ story: 's', title: 'S', test: 'tests/s.json', phase: 'server', request_ids: ['1'], ...zeroCached }], exitCode: 0 });
  assert.match(zeroCachedText, /^Token usage: 2000 input \(0 cached, 0\.0%\) · 100 output\.$/m);

  // 2. Zero-input denominator -> cached_input_tokens: 0, cached_input_share: null (no division by zero)
  const zeroInput = projectAnswer(checkAnswer({
    usage: { calls: 0, input_tokens: 0, cached_input_tokens: 0, output_tokens: 0 },
    model_usage: { calls: [], totals: { input_tokens: 0, cached_input_tokens: 0, cached_input_share: null, complete: true } },
  }), { origin: ORIGIN });
  assert.equal(zeroInput.input_tokens, 0);
  assert.equal(zeroInput.cached_input_tokens, 0);
  assert.equal(zeroInput.output_tokens, 0);
  assert.equal(zeroInput.cached_input_share, null);
  const zeroInputText = renderText({ batch: 'b', rows: [{ story: 's', title: 'S', test: 'tests/s.json', phase: 'server', request_ids: ['1'], ...zeroInput }], exitCode: 0 });
  assert.match(zeroInputText, /^Token usage: 0 input \(0 cached\) · 0 output\.$/m);

  // 3. Incomplete model_usage (complete: false) or accounting_complete: false -> 'unknown' / null
  const incompleteModel = tokenUsageOf(checkAnswer({
    usage: { calls: 1, input_tokens: 4096, cached_input_tokens: 3840, output_tokens: 256 },
    model_usage: { totals: { input_tokens: 4096, cached_input_tokens: 3840, cached_input_share: null, complete: false } },
  }));
  assert.deepEqual(incompleteModel, { input_tokens: 'unknown', cached_input_tokens: 'unknown', output_tokens: 'unknown', cached_input_share: null });

  const incompleteFlag = projectAnswer(checkAnswer({ extra: { accounting_complete: false } }), { origin: ORIGIN });
  assert.equal(incompleteFlag.input_tokens, 'unknown');
  assert.equal(incompleteFlag.cached_input_tokens, 'unknown');
  assert.equal(incompleteFlag.cached_input_share, null);

  // 4. Pre-dispatch receipt (dispatch: 'not_started' or all current model_usage calls 'pre-dispatch') -> 'unknown' / null
  const notStarted = tokenUsageOf(checkAnswer({
    usage: { calls: 0, input_tokens: 0, cached_input_tokens: 0, output_tokens: 0 },
    model_usage: undefined,
    extra: { dispatch: 'not_started' },
  }));
  assert.deepEqual(notStarted, { input_tokens: 'unknown', cached_input_tokens: 'unknown', output_tokens: 'unknown', cached_input_share: null });

  const preDispatchCalls = tokenUsageOf(checkAnswer({
    usage: { calls: 0 },
    model_usage: {
      complete: true,
      calls: [{ step_id: 'run', origin: 'current', dispatch_state: 'pre-dispatch', usage_status: 'unknown', input_tokens: null, cached_input_tokens: null, cached_input_share: null, share_status: 'unavailable' }],
    },
  }));
  assert.deepEqual(preDispatchCalls, { input_tokens: 'unknown', cached_input_tokens: 'unknown', output_tokens: 'unknown', cached_input_share: null });

  // 5. Missing cached_input_tokens on usage without model_usage -> input/output preserved, cached_input_tokens 'unknown', share null
  const noCacheField = tokenUsageOf({ usage: { calls: 1, input_tokens: 6835, output_tokens: 110 } });
  assert.deepEqual(noCacheField, { input_tokens: 6835, cached_input_tokens: 'unknown', output_tokens: 110, cached_input_share: null });
});

test('AC1: multi-attempt request_ids accumulate tokens only when all attempts have complete accounting, and Story cache hits report 0 new tokens without fabricating share', async t => {
  // Local Story cache hit row in renderJson / renderText
  const cachedRow = jsonRow({
    story: 'one',
    title: 'One',
    test: 'tests/one.json',
    state: 'passed',
    cached: true,
    passed_at: '2026-11-12T20:00:00.000Z',
    phase: 'cache',
    calls: 0,
    seconds: 0,
    request_ids: [],
    checks: { passed: 2, total: 2 },
    criteria: { passed: 1, total: 1 },
  });
  assert.equal(cachedRow.calls, 0);
  assert.equal(cachedRow.input_tokens, 0);
  assert.equal(cachedRow.cached_input_tokens, 0);
  assert.equal(cachedRow.output_tokens, 0);
  assert.equal(cachedRow.cached_input_share, null);

  // End-to-end offline runCheck with fakeRuntime:
  // Run 1: service-restarted attempt (complete tokens) + replacement passed attempt (complete tokens) -> sums tokens!
  // Run 2: local Story cache reuse -> 0 calls/tokens and null share!
  // Run 3: incomplete service-restarted attempt + replacement passed attempt -> preserves 'unknown' / null!
  const { repo, home, state } = harbor(t);
  let checkPosts = 0;
  let checkGets = 0;
  let mode = 'complete-restart';
  const fake = await fakeRuntime(t, entry => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: fake.lint(entry.request.requestId) };
    if (entry.method === 'POST') {
      checkPosts++;
      if (mode === 'capacity-retry' && checkPosts === 1) {
        return {
          status: 429,
          headers: { 'Retry-After': '1' },
          json: {
            requestId: entry.request.requestId,
            command: 'check',
            dispatch: 'not_started',
            accounting_complete: true,
            provider_calls: 0,
            job_created: false,
            usage: { calls: 0, known_calls: 0, unknown_calls: 0 },
            error: { code: 'server-full', message: 'Busy.', retry_after_s: 1 },
          },
        };
      }
      return { status: 202, json: fake.check(entry.request.requestId, 'queued') };
    }
    const id = entry.url.split('/').at(-1);
    checkGets++;
    if (mode === 'complete-restart' && checkGets === 1) {
      const restarted = fake.check(id, 'unknown', [], [{ code: 'service-restarted', message: 'Restarted.' }]);
      restarted.accounting_complete = true;
      restarted.usage = { calls: 1, requested_model: 'gpt-6.1-sol', seconds: 1, input_tokens: 1000, cached_input_tokens: 800, output_tokens: 40 };
      restarted.result.report.refusal = { code: 'service-restarted', message: 'Restarted.' };
      return { status: 200, json: restarted };
    }
    if (mode === 'incomplete-restart' && checkGets === 1) {
      const restarted = fake.check(id, 'unknown', [], [{ code: 'service-restarted', message: 'Restarted.' }]);
      restarted.accounting_complete = false;
      restarted.usage = { calls: 'unknown', known_calls: 1, unknown_calls: 1, requested_model: 'gpt-6.1-sol', seconds: 1 };
      restarted.result.report.refusal = { code: 'service-restarted', message: 'Restarted.' };
      return { status: 200, json: restarted };
    }
    const passed = fake.check(id, 'passed');
    passed.accounting_complete = true;
    passed.usage = { calls: 1, requested_model: 'gpt-6.1-sol', seconds: 2, input_tokens: 3000, cached_input_tokens: 2700, output_tokens: 160 };
    return { status: 200, json: passed };
  });

  const env = { HOME: home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: state, CI: '' };
  const run1 = portsFor(env);
  const code1 = await runCheck({ cwd: repo, words: ['place-order'], options: { '--json': true, '--cache-clear': true } }, run1.ports);
  assert.equal(code1, 0, run1.ports.stderr.text);
  const parsed1 = JSON.parse(run1.ports.stdout.text);
  assert.equal(parsed1.rows[0].calls, 2);
  assert.equal(parsed1.rows[0].input_tokens, 4000);
  assert.equal(parsed1.rows[0].cached_input_tokens, 3500);
  assert.equal(parsed1.rows[0].output_tokens, 200);
  assert.equal(parsed1.rows[0].cached_input_share, 0.875);
  assert.deepEqual(parsed1.token_usage, {
    input_tokens: 4000,
    cached_input_tokens: 3500,
    output_tokens: 200,
    cached_input_share: 0.875,
    complete: true,
  });

  // Run 1b: Confirmed zero-work 429 capacity attempt + passed replacement attempt -> projects exact second-attempt tokens
  mode = 'capacity-retry';
  checkPosts = 0;
  checkGets = 0;
  const runCap = portsFor(env);
  runCap.clock.now += 5_000;
  const codeCap = await runCheck({ cwd: repo, words: ['place-order'], options: { '--json': true, '--cache-clear': true } }, runCap.ports);
  assert.equal(codeCap, 0, runCap.ports.stderr.text);
  const parsedCap = JSON.parse(runCap.ports.stdout.text);
  assert.equal(checkPosts, 2);
  assert.equal(parsedCap.rows[0].calls, 1);
  assert.equal(parsedCap.rows[0].input_tokens, 3000);
  assert.equal(parsedCap.rows[0].cached_input_tokens, 2700);
  assert.equal(parsedCap.rows[0].output_tokens, 160);
  assert.equal(parsedCap.rows[0].cached_input_share, 0.9);

  // Run 2: Clean single-attempt pass to populate Story cache, then verify cached skip row reports 0 tokens & null share
  mode = 'single-pass';
  checkPosts = 0;
  checkGets = 0;
  const seed = portsFor(env);
  seed.clock.now += 10_000;
  assert.equal(await runCheck({ cwd: repo, cache: true, words: ['place-order'], options: { '--json': true, '--cache-clear': true } }, seed.ports), 0);
  const cachedRun = portsFor(env);
  cachedRun.clock.now += 20_000;
  const codeCached = await runCheck({ cwd: repo, cache: true, words: ['place-order'], options: { '--json': true } }, cachedRun.ports);
  assert.equal(codeCached, 0);
  const parsedCached = JSON.parse(cachedRun.ports.stdout.text);
  assert.equal(parsedCached.rows[0].cached, true);
  assert.equal(parsedCached.rows[0].calls, 0);
  assert.equal(parsedCached.rows[0].input_tokens, 0);
  assert.equal(parsedCached.rows[0].cached_input_tokens, 0);
  assert.equal(parsedCached.rows[0].output_tokens, 0);
  assert.equal(parsedCached.rows[0].cached_input_share, null);

  // Run 3: Incomplete first attempt + complete second attempt -> preserves 'unknown' / null!
  mode = 'incomplete-restart';
  checkPosts = 0;
  checkGets = 0;
  const run3 = portsFor(env);
  run3.clock.now += 30_000;
  const code3 = await runCheck({ cwd: repo, words: ['place-order'], options: { '--json': true, '--cache-clear': true } }, run3.ports);
  assert.equal(code3, 0);
  const parsed3 = JSON.parse(run3.ports.stdout.text);
  assert.equal(parsed3.rows[0].calls, 'unknown');
  assert.equal(parsed3.rows[0].input_tokens, 'unknown');
  assert.equal(parsed3.rows[0].cached_input_tokens, 'unknown');
  assert.equal(parsed3.rows[0].output_tokens, 'unknown');
  assert.equal(parsed3.rows[0].cached_input_share, null);
  assert.equal(parsed3.token_usage.complete, false);
});

test('AC2: tryUsage, tryUsageLine, tryUsageHeaders and try-http serve optional token headers without spoofing or 404 carryover', async t => {
  const reported = tryUsage({
    usage: { calls: 1, input_tokens: 4096, cached_input_tokens: 3840, output_tokens: 256 },
    result: { session: { max_calls: 40, remaining_calls: 39 } },
  });
  assert.deepEqual(reported, {
    calls: 1,
    remaining: 39,
    cap: 40,
    used: 1,
    input_tokens: 4096,
    cached_input_tokens: 3840,
    output_tokens: 256,
    cached_input_share: 0.9375,
  });
  assert.equal(
    tryUsageLine(reported, { command: true }),
    'Try AI usage: 1 this command · 1 used · 39 remaining (session cap 40) · 4096 input (3840 cached, 93.8%) · 256 output.',
  );
  assert.deepEqual(tryUsageHeaders(reported), {
    'x-pdd-ai-calls': '1',
    'x-pdd-try-used': '1',
    'x-pdd-try-remaining': '39',
    'x-pdd-try-cap': '40',
    'x-pdd-input-tokens': '4096',
    'x-pdd-cached-input-tokens': '3840',
  });

  // Absent cache telemetry keeps exact legacy line and omits optional token headers
  const legacy = tryUsage({ usage: { calls: 1, input_tokens: 6835, output_tokens: 110 }, result: { report: { remaining_calls: 39 } } }, { cap: 40 });
  assert.equal(tryUsageLine(legacy, { command: true }), 'Try AI usage: 1 this command · 1 used · 39 remaining (session cap 40).');
  assert.equal(tryUsageHeaders(legacy)['x-pdd-input-tokens'], '6835');
  assert.equal(tryUsageHeaders(legacy)['x-pdd-cached-input-tokens'], undefined);

  // Real localhost openServe test: reported headers -> 404 has no carryover -> program header spoofing stripped
  const { repo, home, state } = harbor(t);
  const sessionId = '99999999-9999-4999-8999-999999999999';
  let callTurn = 0;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (!entry.json) return { status: 200, json: f.jobs.get(entry.url.split('/').at(-1)) };
    callTurn++;
    const program = {
      status: 200,
      headers: { 'x-pdd-input-tokens': '999999', 'x-pdd-cached-input-tokens': '999999' },
      body: callTurn === 1 ? 'ok' : 'ok2',
    };
    const view = {
      ...f.job(entry.json.requestId, 'call', 'passed', {
        program_result: program,
        report: { result: program, remaining_calls: callTurn === 1 ? 39 : 38 },
      }),
      session_id: sessionId,
    };
    view.usage = callTurn === 1
      ? { calls: 1, input_tokens: 4096, cached_input_tokens: 3840, output_tokens: 256 }
      : { calls: 1 };
    f.jobs.set(entry.json.requestId, view);
    return { status: 200, json: view };
  });

  const getLocal = (port, path) => new Promise((resolve, reject) => {
    const req = request({ host: '127.0.0.1', port, path, method: 'GET', headers: { Host: `127.0.0.1:${port}` } }, res => {
      let body = '';
      res.setEncoding('utf8');
      res.on('data', d => { body += d; });
      res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, body }));
    });
    req.on('error', reject);
    req.end();
  });

  const { ports } = portsFor({ HOME: home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: state });
  ports.serve = async server => {
    const port = server.address().port;
    const first = await getLocal(port, '/api/ping');
    assert.equal(first.status, 200);
    assert.equal(first.headers['x-pdd-input-tokens'], '4096');
    assert.equal(first.headers['x-pdd-cached-input-tokens'], '3840');

    const miss = await getLocal(port, '/missing');
    assert.equal(miss.status, 404);
    assert.equal(miss.headers['x-pdd-usage-source'], 'last-known');
    assert.equal(miss.headers['x-pdd-input-tokens'], undefined);
    assert.equal(miss.headers['x-pdd-cached-input-tokens'], undefined);

    const second = await getLocal(port, '/api/ping');
    assert.equal(second.status, 200);
    assert.equal(second.headers['x-pdd-input-tokens'], undefined);
    assert.equal(second.headers['x-pdd-cached-input-tokens'], undefined);
  };

  const entries = [{
    entry_path: PLACE,
    operation: 'main',
    http: { method: 'GET', path: '/api/ping' },
    input_schema: { type: 'object', properties: {}, required: [], additionalProperties: false },
  }];
  const context = {
    root: repo,
    ports,
    store: { dir: state },
    identity: { login: 'octo', userId: '4242', token: TOKEN },
    origin: fake.origin,
    runtime: { send: async () => ({ status: 200, json: { entries, app_map: false, calls: { cap: 40, remaining: 40 } } }) },
  };
  assert.equal(await openServe(context, {}, sessionId, { '--serve': '0' }), 0);
});

test('AC3: cost-ledger preserves pdd.cost.v1 schema while surfacing uncachedInput, cacheHitShare, and analytical 0.1x effectiveTokens', t => {
  assert.equal(CACHED_INPUT_WEIGHT, 0.1);
  const base = fs.mkdtempSync(join(tmpdir(), 'pdd-3300-cost-'));
  t.after(() => fs.rmSync(base, { recursive: true, force: true }));
  const at = Date.parse('2026-11-12T21:00:00Z');
  const sid = '22222222-2222-4222-8222-222222222222';
  const codexHome = join(base, '.codex');
  const dayDir = join(codexHome, 'sessions', '2026', '11', '12');
  fs.mkdirSync(dayDir, { recursive: true });
  fs.writeFileSync(
    join(dayDir, `rollout-2026-11-12-${sid}.jsonl`),
    JSON.stringify({
      type: 'event_msg',
      payload: {
        type: 'token_count',
        info: {
          total_token_usage: {
            input_tokens: 4096,
            cached_input_tokens: 3840,
            output_tokens: 256,
            reasoning_output_tokens: 0,
            total_tokens: 4352,
          },
        },
      },
    }) + '\n',
  );

  const run = {
    runId: 'attempt-1',
    number: 3300,
    repo: 'promptdriven/pdd',
    startedAt: at - 60_000,
    runDir: base,
    root: join(base, 'worktree'),
    state: 'running',
    agent: 'codex',
    chats: [{ agent: 'codex', configDir: codexHome, session: { id: sid }, startedAt: at - 60_000 }],
    pr: [],
    areas: [{ name: 'code' }],
  };
  applyCostMeasurement(run, { id: 'm1', suiteMinutes: 2, personMinutes: 1, outcome: 'merged' }, at);
  run.cost = captureCosts(null, run, { now: () => at, env: { HOME: base }, fs });

  // Raw pdd.cost.v1 token row keys stay strictly backward-compatible.
  assert.equal(run.cost.schema, 'pdd.cost.v1');
  assert.deepEqual(Object.keys(run.cost.tokens[0]).sort(), ['account', 'agent', 'cachedInput', 'input', 'output', 'reasoningOutput', 'total']);
  assert.equal(run.cost.tokens[0].total, 4352);

  const report = costReport([run], at);
  assert.equal(report.runs[0].totalTokens, 4352);
  assert.equal(report.runs[0].uncachedInput, 256);
  assert.equal(report.runs[0].cacheHitShare, 0.9375);
  assert.equal(report.runs[0].effectiveTokens, 896); // 256 + 0.1 * 3840 + 256 = 896

  for (const bucket of [report.day.totals, report.day.p50, report.day.p90, report.week.totals]) {
    assert.equal(bucket.totalTokens, 4352);
    assert.equal(bucket.uncachedInput, 256);
    assert.equal(bucket.cacheHitShare, 0.9375);
    assert.equal(bucket.effectiveTokens, 896);
  }

  const lines = costStatusLines(report);
  assert.match(lines, /analytical effective tokens weight cached input at 0\.1x, not dollar billing/);
  assert.match(lines, /4352 tokens \(896 analytical effective @ 0\.1x cached, uncached input 256, cache hit 93\.8%\)/);
  assert.match(lines, /codex:[0-9a-f]{20}: 4352 tokens, 896 analytical effective @ 0\.1x cached \(input 4096, uncached 256, cached 3840 \[93\.8%\], output 256, reasoning 0\)/);

  // Unknown (no token observations) vs measured 0-input run
  const unknownRun = { ...run, runId: 'attempt-u', number: 3301, chats: [], cost: undefined };
  unknownRun.cost = captureCosts(null, unknownRun, { now: () => at, env: { HOME: base }, fs });
  const unknownReport = costReport([unknownRun], at);
  assert.equal(unknownReport.runs[0].totalTokens, null);
  assert.equal(unknownReport.runs[0].uncachedInput, null);
  assert.equal(unknownReport.runs[0].cacheHitShare, null);
  assert.equal(unknownReport.runs[0].effectiveTokens, null);
  assert.match(costStatusLines(unknownReport), /Last day: unknown tokens;/);

  const zeroSid = '33333333-3333-4333-8333-333333333333';
  const claudeDir = join(base, '.claude', 'projects', join(base, 'worktree').replace(/[^a-zA-Z0-9]/g, '-'));
  fs.mkdirSync(claudeDir, { recursive: true });
  fs.writeFileSync(join(claudeDir, `${zeroSid}.jsonl`), JSON.stringify({
    type: 'assistant',
    sessionId: zeroSid,
    message: { id: 'z1', usage: { input_tokens: 0, output_tokens: 0 } },
  }) + '\n');
  const zeroRun = {
    ...run,
    runId: 'attempt-z',
    number: 3302,
    agent: 'claude',
    chats: [{ agent: 'claude', configDir: join(base, '.claude'), session: { id: zeroSid }, startedAt: at - 60_000 }],
    cost: undefined,
  };
  zeroRun.cost = captureCosts(null, zeroRun, { now: () => at, env: { HOME: base }, fs });
  const zeroReport = costReport([zeroRun], at);
  assert.equal(zeroReport.runs[0].totalTokens, 0);
  assert.equal(zeroReport.runs[0].uncachedInput, 0);
  assert.equal(zeroReport.runs[0].cacheHitShare, null);
  assert.equal(zeroReport.runs[0].effectiveTokens, 0);
  assert.match(costStatusLines(zeroReport), /0 tokens \(0 analytical effective @ 0\.1x cached, uncached input 0, cache hit n\/a\)/);
});
