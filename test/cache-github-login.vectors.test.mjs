import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { chmodSync, existsSync, lstatSync, mkdirSync, readFileSync, readdirSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { checkRuntimeHealth, readTryOwner, runCheck, runDoorCall, runTry } from '../src/runtime-client.mjs';
import { runShim } from '../src/try-doors.mjs';
import { createTryTools, runMcp } from '../src/try-mcp.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { PLACE, fakeRuntime, filesUnder, harbor, portsFor, sink, temp } from './runtime-fake.mjs';

const CASES_PATH = new URL('./runtime/cache-github-login-cases.json', import.meta.url);

// RUNBOOK §17 exact whole-number JSON reviver.
function parseExactJson(text) {
  return JSON.parse(text, (key, value, context) =>
    typeof value === 'number' && /^-?(?:0|[1-9][0-9]*)$/.test(context.source) && !Number.isSafeInteger(value)
      ? BigInt(context.source)
      : value);
}

const SPEC = parseExactJson(readFileSync(CASES_PATH, 'utf8'));
const BY_ID = new Map(SPEC.cases.map(entry => [entry.id, entry]));

const TOKEN_OCTO = 'gho_OCTOTOKEN_secret_do_not_persist_91a4';
const TOKEN_OCTO_2 = 'gho_OCTOTOKEN_ROTATED_secret_do_not_persist_55b2';
const TOKEN_MALLORY = 'gho_MALLORYTOKEN_secret_do_not_persist_88c3';
const ALL_TOKENS = [TOKEN_OCTO, TOKEN_OCTO_2, TOKEN_MALLORY];

const sha256Hex = text => createHash('sha256').update(text, 'utf8').digest('hex');
const modeOctal = path => `0${(statSync(path).mode & 0o777).toString(8).padStart(3, '0')}`;
const authTokenCalls = calls => calls.filter(args => args[0] === 'auth' && args[1] === 'token');
const apiUserCalls = calls => calls.filter(args => args[0] === 'api' && args[1] === 'user');

function assertNoSecretsOrTempFiles(dirs, outputs = [], tokens = ALL_TOKENS) {
  for (const dir of dirs) {
    if (!existsSync(dir)) continue;
    for (const file of filesUnder(dir)) {
      const name = file.split('/').at(-1);
      assert.doesNotMatch(name, /^github-user\.json\..*\.tmp$/, `leftover temp file ${file}`);
      let st;
      try { st = lstatSync(file); } catch { continue; }
      if (!st.isFile()) continue;
      const content = readFileSync(file, 'utf8');
      for (const secret of tokens) {
        assert.equal(content.includes(secret), false, `raw token leaked into ${file}`);
      }
    }
  }
  for (const text of outputs) {
    for (const secret of tokens) {
      assert.equal(String(text).includes(secret), false, 'raw token leaked into command output');
    }
  }
}

function cliHarbor(t) {
  return harbor(t, root => {
    rmSync(join(root, 'tests/unknown-item.json'));
    const input = {
      type: 'object',
      properties: { argv: { type: 'array', items: { type: 'string' } }, stdin: { type: 'string' } },
      required: ['argv'],
      additionalProperties: false,
    };
    const result = {
      type: 'object',
      properties: { stdout: { type: 'string' }, stderr: { type: 'string' }, exit_code: { type: 'integer' } },
      required: ['stdout', 'stderr', 'exit_code'],
      additionalProperties: false,
    };
    const iface = {
      status: 'draft',
      prose_sha256: '',
      entries: [{ operation: 'main', input_schema: input, result_schema: result, errors: [] }],
      calls: [],
      resources: [],
      limits: { max_steps: 1, max_model_calls: 1 },
      conventions: ['input_schema', 'result_schema'].map(key => ({ path: `/entries/0/${key}`, convention: 'cli' })),
    };
    const content = () =>
      `# paperclip\n\nPrint each argument on its own line.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
    iface.prose_sha256 = proseSha256(content());
    writeFileSync(join(root, PLACE), content());
    writeFileSync(
      join(root, 'user_stories/place-order.md'),
      '# Arguments\n\nI can pass words.\n\n## Acceptance criteria\n\n1. Each argument prints on its own line.\n',
    );
    const doc = {
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/place-order.md',
      criteria: [{ id: 'AC1', text: 'Each argument prints on its own line.' }],
      initial_world: {},
      simulation: {},
      context: [],
      steps: [{
        step_id: 'two-words',
        entry_path: PLACE,
        operation: 'main',
        input: { argv: ['say', 'two words'] },
        checks: [
          { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'say\ntwo words\n' },
          { criterion_id: 'AC1', target: 'world', path: '', op: 'equals', value: {} },
        ],
      }],
    };
    writeFileSync(join(root, 'tests/place-order.json'), `${JSON.stringify(doc, null, 2)}\n`);
  });
}

test('cache-github-login inventory: approved draft cases file is intact and complete', () => {
  assert.equal(SPEC.kind, 'native-draft-cases');
  assert.equal(SPEC.draft, false);
  assert.equal(SPEC.story_path, 'user_stories/cache-github-login.md');
  assert.deepEqual(
    SPEC.cases.map(item => item.id),
    [
      'cold-cache-first-run',
      'warm-cache-saved-batch-read-under-rate-limit',
      'warm-cache-across-runtime-commands-and-mcp',
      'switched-token-cross-owner-refusals',
      'missing-or-logged-out-gh-token-with-warm-cache',
      'corrupt-or-incomplete-cache-self-heals',
      'http-401-cached-invalidation-and-single-refresh',
      'gh-api-user-failure-and-rate-limit-boundaries',
    ],
  );
});

test('vector 1 & 2: cold-cache-first-run and warm-cache-saved-batch-read-under-rate-limit', async t => {
  const coldCase = BY_ID.get('cold-cache-first-run');
  const warmPollCase = BY_ID.get('warm-cache-saved-batch-read-under-rate-limit');
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };

  const ghCalls = [];
  const made = portsFor(env, {
    gh: args => {
      ghCalls.push(args);
      if (args[0] === 'auth') return { status: 0, stdout: `  ${TOKEN_OCTO}\n` };
      assert.deepEqual(args, ['api', 'user', '--jq', '.login + " " + (.id|tostring)']);
      return { status: 0, stdout: 'octo 4242\n' };
    },
  });

  const firstCode = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, made.ports);
  assert.equal(firstCode, coldCase.expected.exit_code, made.ports.stderr.text);
  assert.equal(authTokenCalls(ghCalls).length, coldCase.expected.gh_auth_token_calls);
  assert.equal(apiUserCalls(ghCalls).length, coldCase.expected.gh_api_user_calls);

  const cacheFile = join(setup.state, 'github-user.json');
  assert.equal(existsSync(cacheFile), coldCase.expected.cache_file_exists);
  assert.equal(modeOctal(setup.state), SPEC.security_invariants.state_dir_mode);
  assert.equal(modeOctal(cacheFile), coldCase.expected.cache_file_mode_octal);

  const cachedRecord = parseExactJson(readFileSync(cacheFile, 'utf8'));
  assert.deepEqual(cachedRecord, {
    login: coldCase.expected.cached_record.login,
    user_id: coldCase.expected.cached_record.user_id,
    cached_at: coldCase.expected.cached_record.cached_at,
    token_sha256: sha256Hex(TOKEN_OCTO),
  });
  assertNoSecretsOrTempFiles([setup.state, setup.repo], [made.ports.stdout.text, made.ports.stderr.text]);

  const firstSummary = parseExactJson(made.ports.stdout.text);
  const batch = firstSummary.batch;
  assert.ok(batch);

  // Case 2: 5 consecutive pdd test --read <BATCH> --json polls while gh api user is rate-limited (HTTP 403).
  const pollGhCalls = [];
  const postsBefore = fake.posts.length;
  const jsonPostsBefore = fake.jsonPosts.length;
  const getsBefore = fake.gets.length;
  const deletesBefore = fake.deletes.length;

  for (let i = 0; i < 5; i += 1) {
    const poll = portsFor(env, {
      gh: args => {
        pollGhCalls.push(args);
        if (args[0] === 'auth') return { status: 0, stdout: `${TOKEN_OCTO}\n` };
        return { status: 1, stdout: '', stderr: 'gh: API rate limit exceeded (HTTP 403)\n' };
      },
    });
    const code = await runCheck({ cwd: setup.repo, words: [batch], options: { '--read': true, '--json': true } }, poll.ports);
    assert.equal(code, warmPollCase.expected.exit_code_each, poll.ports.stderr.text);
    assert.equal(poll.ports.stderr.text, warmPollCase.expected.stderr_each);
    const readReport = parseExactJson(poll.ports.stdout.text);
    assert.equal(readReport.batch, batch);
    assert.equal(readReport.rows[0].state, 'passed');
    assertNoSecretsOrTempFiles([setup.state, setup.repo], [poll.ports.stdout.text, poll.ports.stderr.text]);
  }

  assert.equal(authTokenCalls(pollGhCalls).length, warmPollCase.expected.gh_auth_token_calls_total);
  assert.equal(apiUserCalls(pollGhCalls).length, warmPollCase.expected.gh_api_user_calls_total);
  const httpDuringPolls =
    (fake.posts.length - postsBefore) +
    (fake.jsonPosts.length - jsonPostsBefore) +
    (fake.gets.length - getsBefore) +
    (fake.deletes.length - deletesBefore);
  assert.equal(httpDuringPolls, warmPollCase.expected.runtime_http_requests_during_polls);
});

test('vector 3: warm-cache-across-runtime-commands-and-mcp', async t => {
  const vector = BY_ID.get('warm-cache-across-runtime-commands-and-mcp');
  const setup = cliHarbor(t);
  let busyCheckOnce = false;

  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.json) {
      const input = entry.json.input ?? { argv: [] };
      const programResult = { stdout: `${(input.argv ?? []).join('\n')}\n`, stderr: '', exit_code: 0 };
      const callId = entry.json.requestId;
      const sessionId = entry.url.split('/')[3];
      const actionId = `act-${callId}`;
      const callJob = {
        ...f.job(callId, 'call', 'passed', {
          program_result: programResult,
          report: { verdict: 'passed', result: programResult, action_id: actionId, remaining_calls: 399 },
          output: programResult,
        }, 1),
        session_id: sessionId,
      };
      f.jobs.set(callId, callJob);
      f.lastAction = { action_id: actionId, input_world: {}, world: {} };
      return { status: 200, json: callJob };
    }
    const tail = entry.url.split('/').at(-1);
    if (entry.method === 'DELETE') {
      const reqId = entry.headers['x-request-id'];
      return { status: 200, json: f.stopJob(reqId, tail) };
    }
    if (f.jobs.has(tail)) return { status: 200, json: f.jobs.get(tail) };
    if (entry.url.endsWith('/model')) {
      return {
        status: 200,
        json: {
          entries: [{ entry_path: PLACE, operation: 'main', cli: true, input_schema: {}, result_schema: {} }],
          calls: { cap: 400, remaining: 399 },
        },
      };
    }
    if (entry.url.endsWith('/state')) {
      return { status: 200, json: { world: {}, actions: f.lastAction ? [f.lastAction] : [] } };
    }
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') {
      const job = f.tryJob(entry.request.requestId);
      f.jobs.set(entry.request.requestId, job);
      return { status: 200, json: job };
    }
    if (entry.command === 'check') {
      if (busyCheckOnce) {
        busyCheckOnce = false;
        return {
          status: 503,
          headers: { 'retry-after': '1' },
          json: {
            requestId: entry.request.requestId,
            id: entry.request.requestId,
            command: 'check',
            state: 'refused',
            job_created: false,
            dispatch: 'not_started',
            accounting_complete: true,
            calls: 0,
            usage: { calls: 0, known_calls: 0, unknown_calls: 0, provider_calls: 0, accounting_complete: true, dispatch: 'not_started', job_created: false },
            result: { report: { provider_calls: 0, accounting_complete: true, dispatch: 'not_started', job_created: false } },
            error: { code: 'check-queue-full', message: 'Queue full', details: { retryable: true, retry_after: 1 } },
          },
        };
      }
      const checkJob = f.check(entry.request.requestId, 'passed', [
        { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', expected: 'say\ntwo words\n', actual: 'say\ntwo words\n', passed: true },
        { criterion_id: 'AC1', target: 'world', path: '', op: 'equals', expected: {}, actual: {}, passed: true },
      ]);
      f.jobs.set(entry.request.requestId, checkJob);
      return { status: 200, json: checkJob };
    }
    return f.normal(entry);
  });

  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };

  // Seed warm github-user.json via initial cold sign-in, plus a held batch for --retry.
  const seedCalls = [];
  busyCheckOnce = true;
  const seedMade = portsFor(env, {
    gh: args => {
      seedCalls.push(args);
      return args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' };
    },
    sleep: async ms => { seedMade.clock.now += ms; seedMade.clock.interrupt(); },
  });
  const heldExit = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, seedMade.ports);
  assert.equal(heldExit, 3);
  const heldBatch = parseExactJson(seedMade.ports.stdout.text).batch;
  assert.equal(apiUserCalls(seedCalls).length, 1);

  // Now gh api user fails if called for all warm-cache commands!
  const warmGhCalls = [];
  let currentClock = seedMade.clock.now + 120_000;
  const makeWarmPorts = (extra = {}) => {
    const invocationCalls = [];
    const built = portsFor(env, {
      stdin: Readable.from([]),
      gh: args => {
        invocationCalls.push(args);
        warmGhCalls.push(args);
        if (args[0] === 'auth') return { status: 0, stdout: `${TOKEN_OCTO}\n` };
        assert.fail(`unexpected gh api user call on warm cache: ${JSON.stringify(args)}`);
      },
      ...extra,
    });
    built.clock.now = currentClock;
    return { ...built, invocationCalls };
  };

  // 1. pdd lint place-order --json
  {
    const w = makeWarmPorts();
    const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true, '--json': true } }, w.ports);
    assert.equal(code, 0, w.ports.stderr.text);
    assert.equal(authTokenCalls(w.invocationCalls).length, vector.expected.gh_auth_token_calls_per_signin);
  }

  // 2. pdd test place-order --cache-clear --json
  let checkRunUuid;
  {
    const w = makeWarmPorts();
    const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--cache-clear': true, '--json': true }, cache: true }, w.ports);
    assert.equal(code, 0, w.ports.stderr.text);
    assert.equal(authTokenCalls(w.invocationCalls).length, vector.expected.gh_auth_token_calls_per_signin);
    checkRunUuid = parseExactJson(w.ports.stdout.text).rows[0].request_id;
    assert.ok(checkRunUuid);
  }

  // 3. pdd test --read <CALL_UUID> --json (checks check-UUID read; call-UUID read also exercised after MCP try_run below)
  {
    const w = makeWarmPorts();
    const code = await runCheck({ cwd: setup.repo, words: [checkRunUuid], options: { '--read': true, '--json': true } }, w.ports);
    assert.equal(code, 0, w.ports.stderr.text);
    assert.equal(authTokenCalls(w.invocationCalls).length, vector.expected.gh_auth_token_calls_per_signin);
  }

  // 4. pdd test --request <UUID> --json
  {
    const w = makeWarmPorts();
    const code = await runCheck({ cwd: setup.repo, options: { '--request': checkRunUuid, '--json': true } }, w.ports);
    assert.equal(code, 0, w.ports.stderr.text);
    assert.equal(authTokenCalls(w.invocationCalls).length, vector.expected.gh_auth_token_calls_per_signin);
  }

  // 5. pdd test --retry <HELD_BATCH> --json
  {
    const w = makeWarmPorts();
    const code = await runCheck({ cwd: setup.repo, options: { '--retry': heldBatch, '--json': true } }, w.ports);
    assert.equal(code, 0, w.ports.stderr.text);
    assert.equal(authTokenCalls(w.invocationCalls).length, vector.expected.gh_auth_token_calls_per_signin);
  }

  // 6. pdd simulate place-order --page --no-open --no-wait (create)
  {
    const w = makeWarmPorts();
    const code = await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--page': true, '--no-open': true, '--no-wait': true } }, w.ports);
    assert.equal(code, 0, w.ports.stderr.text);
    assert.equal(authTokenCalls(w.invocationCalls).length, vector.expected.gh_auth_token_calls_per_signin);
  }

  // 7. pdd simulate place-order --page --no-open --no-wait (attach)
  {
    const w = makeWarmPorts();
    const code = await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--page': true, '--no-open': true, '--no-wait': true } }, w.ports);
    assert.equal(code, 0, w.ports.stderr.text);
    assert.equal(authTokenCalls(w.invocationCalls).length, vector.expected.gh_auth_token_calls_per_signin);
  }

  // 8. MCP try_run over real runMcp JSON-RPC stdio (exercises readTryOwner + runDoorCall)
  let mcpCallId;
  {
    const w = makeWarmPorts();
    const mcpOut = sink();
    const mcpErr = sink();
    const requests = [
      JSON.stringify({ jsonrpc: '2.0', id: 1, method: 'initialize', params: { protocolVersion: '2025-06-18', capabilities: {}, clientInfo: { name: 'test', version: '1.0' } } }),
      JSON.stringify({ jsonrpc: '2.0', id: 2, method: 'tools/call', params: { name: 'try_run', arguments: { story: 'place-order', argv: ['alpha', 'beta'] } } }),
    ].join('\n') + '\n';
    const mcpExit = await runMcp(
      { cwd: setup.repo, env },
      { ...w.ports, stdin: Readable.from([requests]), stdout: mcpOut, stderr: mcpErr },
    );
    assert.equal(mcpExit, 0, mcpErr.text);
    const lines = mcpOut.text.trim().split('\n').map(line => parseExactJson(line));
    const callReply = lines.find(msg => msg.id === 2);
    assert.equal(callReply.result.isError, undefined, JSON.stringify(callReply));
    assert.equal(callReply.result.structuredContent.result.stdout, 'alpha\nbeta\n');
    mcpCallId = callReply.result.structuredContent.run_id;
    // 1 sign-in in readTryOwner + 1 sign-in in runDoorCall, 0 gh api user calls!
    assert.equal(authTokenCalls(w.invocationCalls).length, 2 * vector.expected.gh_auth_token_calls_per_signin);
  }

  // Also verify pdd test --read <CALL_UUID> --json on the door call receipt!
  {
    const w = makeWarmPorts();
    const code = await runCheck({ cwd: setup.repo, words: [mcpCallId], options: { '--read': true, '--json': true } }, w.ports);
    assert.equal(code, 0, w.ports.stderr.text);
    assert.equal(authTokenCalls(w.invocationCalls).length, vector.expected.gh_auth_token_calls_per_signin);
  }

  // Open CLI door on the same Try + run one CLI door command so --save-last has a confirmed door receipt
  {
    const w = makeWarmPorts({
      shell: async () => 0,
      openUrl: async () => assert.fail('CLI door must not open browser'),
    });
    assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--cli': true } }, w.ports), 0, w.ports.stderr.text);
    const descriptorPath = readdirSync(join(setup.state, 'tries')).filter(name => name.endsWith('.door.json')).map(name => join(setup.state, 'tries', name))[0];
    const shimPorts = makeWarmPorts();
    assert.equal(await runShim(descriptorPath, ['saved-arg'], shimPorts.ports), 0, shimPorts.ports.stderr.text);
    assert.equal(authTokenCalls(shimPorts.invocationCalls).length, vector.expected.gh_auth_token_calls_per_signin);
  }

  // 9. pdd simulate --save-last
  {
    const w = makeWarmPorts({ caseHandoff: async ({ testPath }) => ({ kind: 'closed-editor', testPath }) });
    const code = await runTry({ cwd: setup.repo, options: { '--save-last': true } }, w.ports);
    assert.equal(code, 0, w.ports.stderr.text);
    assert.equal(authTokenCalls(w.invocationCalls).length, vector.expected.gh_auth_token_calls_per_signin);
  }

  // 10. pdd simulate place-order --stop
  {
    const w = makeWarmPorts();
    const code = await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--stop': true } }, w.ports);
    assert.equal(code, 0, w.ports.stderr.text);
    assert.equal(authTokenCalls(w.invocationCalls).length, vector.expected.gh_auth_token_calls_per_signin);
  }

  assert.equal(apiUserCalls(warmGhCalls).length, vector.expected.gh_api_user_calls_total);
  assertNoSecretsOrTempFiles([setup.state, setup.repo], [seedMade.ports.stdout.text, seedMade.ports.stderr.text]);
});

test('vector 4: switched-token-cross-owner-refusals', async t => {
  const vector = BY_ID.get('switched-token-cross-owner-refusals');
  const setup = cliHarbor(t);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') {
      const job = f.tryJob(entry.request.requestId);
      f.jobs.set(entry.request.requestId, job);
      return { status: 200, json: job };
    }
    if (entry.command === 'check') {
      const job = f.check(entry.request.requestId, 'passed', [
        { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', expected: 'say\ntwo words\n', actual: 'say\ntwo words\n', passed: true },
        { criterion_id: 'AC1', target: 'world', path: '', op: 'equals', expected: {}, actual: {}, passed: true },
      ]);
      f.jobs.set(entry.request.requestId, job);
      return { status: 200, json: job };
    }
    const tail = entry.url.split('/').at(-1);
    if (f.jobs.has(tail)) return { status: 200, json: f.jobs.get(tail) };
    return f.normal(entry);
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };

  // Seed batch and CLI Try as octo.
  const octoPorts = () => portsFor(env, {
    stdin: Readable.from([]),
    shell: async () => 0,
    gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
  }).ports;

  const checkPorts = octoPorts();
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, checkPorts), 0, checkPorts.stderr.text);
  const octoBatch = parseExactJson(checkPorts.stdout.text).batch;
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--cli': true } }, octoPorts()), 0);
  const descriptorPath = readdirSync(join(setup.state, 'tries')).filter(name => name.endsWith('.door.json')).map(name => join(setup.state, 'tries', name))[0];
  const descriptor = parseExactJson(readFileSync(descriptorPath, 'utf8'));

  // Switch active gh token to TOKEN_MALLORY ('mallory 777').
  const malloryPorts = () => {
    const calls = [];
    const built = portsFor(env, {
      stdin: Readable.from([]),
      gh: args => {
        calls.push(args);
        return args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_MALLORY}\n` } : { status: 0, stdout: 'mallory 777\n' };
      },
    });
    return { ports: built.ports, calls };
  };

  // 1. pdd test --read <OCTO_BATCH> -> 1 gh api user call, updates cache to mallory, exits 5.
  const first = malloryPorts();
  const readExit = await runCheck({ cwd: setup.repo, words: [octoBatch], options: { '--read': true } }, first.ports);
  assert.equal(readExit, vector.expected.read_batch_exit_code);
  assert.equal(apiUserCalls(first.calls).length, vector.expected.first_command_gh_api_user_calls);
  assert.ok(first.ports.stderr.text.includes(vector.expected.read_batch_stderr_contains), first.ports.stderr.text);

  const updatedCache = parseExactJson(readFileSync(join(setup.state, 'github-user.json'), 'utf8'));
  assert.equal(updatedCache.login, vector.expected.updated_cached_login);
  assert.equal(updatedCache.user_id, vector.expected.updated_cached_user_id);
  assert.equal(updatedCache.token_sha256, sha256Hex(TOKEN_MALLORY));

  // 2. pdd simulate place-order --page --no-open --no-wait --max-calls 400 -> 0 gh api user calls, exits 5.
  const second = malloryPorts();
  const simExit = await runTry(
    { cwd: setup.repo, words: ['place-order'], options: { '--page': true, '--no-open': true, '--no-wait': true, '--max-calls': '400' } },
    second.ports,
  );
  assert.equal(simExit, vector.expected.simulate_reuse_exit_code);
  assert.equal(apiUserCalls(second.calls).length, vector.expected.subsequent_commands_gh_api_user_calls);
  assert.ok(second.ports.stderr.text.includes(vector.expected.door_stderr_contains), second.ports.stderr.text);

  // 3. runDoorCall + CLI door shim -> 0 gh api user calls, exit 125.
  const third = malloryPorts();
  await assert.rejects(
    runDoorCall(descriptor, { argv: ['hi'] }, third.ports),
    err => err.exitCode === vector.expected.door_exit_code && err.message.includes(vector.expected.door_stderr_contains),
  );
  assert.equal(apiUserCalls(third.calls).length, vector.expected.subsequent_commands_gh_api_user_calls);

  const thirdShim = malloryPorts();
  const shimExit = await runShim(descriptorPath, ['hi'], thirdShim.ports);
  assert.equal(shimExit, vector.expected.door_exit_code);
  assert.ok(thirdShim.ports.stderr.text.includes(vector.expected.door_stderr_contains), thirdShim.ports.stderr.text);
  assert.equal(apiUserCalls(thirdShim.calls).length, vector.expected.subsequent_commands_gh_api_user_calls);

  // 4. readTryOwner on octo's open Try -> 0 gh api user calls, throws owner mismatch.
  const fourth = malloryPorts();
  await assert.rejects(
    readTryOwner({ cwd: setup.repo }, fourth.ports),
    err => err.message.includes(vector.expected.read_try_owner_throws),
  );
  assert.equal(apiUserCalls(fourth.calls).length, vector.expected.subsequent_commands_gh_api_user_calls);

  assertNoSecretsOrTempFiles([setup.state, setup.repo], [first.ports.stderr.text, second.ports.stderr.text, thirdShim.ports.stderr.text]);
});

test('vector 5: missing-or-logged-out-gh-token-with-warm-cache', async t => {
  const vector = BY_ID.get('missing-or-logged-out-gh-token-with-warm-cache');
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };

  const warm = portsFor(env, {
    gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
  });
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, warm.ports), 0);
  const batch = parseExactJson(warm.ports.stdout.text).batch;
  assert.equal(existsSync(join(setup.state, 'github-user.json')), true);

  // Subcase A: gh binary missing (ENOENT) -> exit 5 (and 125 in door mode), 0 gh api user calls.
  {
    const calls = [];
    const made = portsFor(env, {
      gh: args => {
        calls.push(args);
        if (args[0] === 'auth') return { status: null, stdout: '', stderr: '', error: Object.assign(new Error('spawn gh ENOENT'), { code: 'ENOENT' }) };
        assert.fail('gh api user must not be called when gh auth token fails');
      },
    });
    const code = await runCheck({ cwd: setup.repo, words: [batch], options: { '--read': true } }, made.ports);
    assert.equal(code, vector.expected.enoent_exit_code);
    assert.ok(made.ports.stderr.text.includes(vector.expected.enoent_stderr_contains), made.ports.stderr.text);
    assert.equal(made.ports.stdout.text, '');
    assert.equal(apiUserCalls(calls).length, vector.expected.gh_api_user_calls);

    await assert.rejects(
      runDoorCall({ root: setup.repo, origin: fake.origin, sessionId: '00000000-0000-4000-8000-000000000001', login: 'octo', prompt: PLACE, operation: 'main' }, { argv: [] }, made.ports),
      err => err.exitCode === 125 && err.message.includes(vector.expected.enoent_stderr_contains),
    );
  }

  // Subcase B: gh auth token exits 1 or prints whitespace-only stdout -> exit 5, 0 gh api user calls, cached login NOT returned.
  for (const authReply of [{ status: 1, stdout: '', stderr: 'not logged in\n' }, { status: 0, stdout: '   \n', stderr: '' }]) {
    const calls = [];
    const made = portsFor(env, {
      gh: args => {
        calls.push(args);
        if (args[0] === 'auth') return authReply;
        assert.fail('gh api user must not be called when gh auth token is blank or nonzero');
      },
    });
    const code = await runCheck({ cwd: setup.repo, words: [batch], options: { '--read': true, '--json': true } }, made.ports);
    assert.equal(code, vector.expected.logged_out_exit_code);
    assert.ok(made.ports.stderr.text.includes(vector.expected.logged_out_stderr_contains), made.ports.stderr.text);
    assert.equal(made.ports.stdout.text, '');
    assert.equal(apiUserCalls(calls).length, vector.expected.gh_api_user_calls);
  }
});

test('vector 6: corrupt-or-incomplete-cache-self-heals', async t => {
  const vector = BY_ID.get('corrupt-or-incomplete-cache-self-heals');
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };

  const initial = portsFor(env, {
    gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
  });
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, initial.ports), 0);
  const batch = parseExactJson(initial.ports.stdout.text).batch;
  const cacheFile = join(setup.state, 'github-user.json');

  const corruptPayloads = [
    '{bad',
    JSON.stringify({ login: 'octo', user_id: '4242', cached_at: '2026-10-27T16:27:47.000Z' }),
    JSON.stringify({ login: '', user_id: '4242', cached_at: '2026-10-27T16:27:47.000Z', token_sha256: sha256Hex(TOKEN_OCTO) }),
    JSON.stringify({ login: 'octo user', user_id: '4242', cached_at: '2026-10-27T16:27:47.000Z', token_sha256: sha256Hex(TOKEN_OCTO) }),
    JSON.stringify({ login: 'octo', user_id: '0', cached_at: '2026-10-27T16:27:47.000Z', token_sha256: sha256Hex(TOKEN_OCTO) }),
    JSON.stringify({ login: 'octo', user_id: 'abc', cached_at: '2026-10-27T16:27:47.000Z', token_sha256: sha256Hex(TOKEN_OCTO) }),
  ];

  for (const payload of corruptPayloads) {
    writeFileSync(cacheFile, payload, { mode: 0o600 });
    const calls = [];
    const made = portsFor(env, {
      gh: args => {
        calls.push(args);
        return args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' };
      },
    });
    const code = await runCheck({ cwd: setup.repo, words: [batch], options: { '--read': true, '--json': true } }, made.ports);
    assert.equal(code, vector.expected.exit_code, made.ports.stderr.text);
    assert.equal(authTokenCalls(calls).length, vector.expected.gh_auth_token_calls);
    assert.equal(apiUserCalls(calls).length, vector.expected.gh_api_user_calls);
    assert.equal(modeOctal(cacheFile), '0600');
    const healed = parseExactJson(readFileSync(cacheFile, 'utf8'));
    assert.equal(healed.login, 'octo');
    assert.equal(healed.user_id, '4242');
    assert.equal(healed.token_sha256, sha256Hex(TOKEN_OCTO));
  }
});

test('vector 7: http-401-cached-invalidation-and-single-refresh (Subcases A, B, C, D)', async t => {
  const vector = BY_ID.get('http-401-cached-invalidation-and-single-refresh');

  // Subcase A: warm cache -> first POST /v1/lint returns 401 -> refreshes rotated TOKEN_OCTO_2 -> retries once without duplicate .posted -> exits 0.
  await t.test('Subcase A: cached sign-in refreshes once on 401 and retries POST without duplicate .posted', async t => {
    const setup = harbor(t);
    let lintAttempts = 0;
    let armed401 = false;
    const fake = await fakeRuntime(t, (entry, f) => {
      if (!armed401) return f.normal(entry);
      if (entry.method === 'POST' && entry.command === 'lint') {
        lintAttempts += 1;
        if (lintAttempts === 1) {
          assert.equal(entry.headers.authorization, `Bearer ${TOKEN_OCTO}`);
          return { status: 401, json: { error: { code: 'auth-invalid', message: 'Expired token' } } };
        }
        assert.equal(entry.headers.authorization, `Bearer ${TOKEN_OCTO_2}`);
        return { status: 200, json: f.lint(entry.request.requestId) };
      }
      assert.equal(entry.headers.authorization, `Bearer ${TOKEN_OCTO_2}`);
      return f.normal(entry);
    });
    const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };

    const seed = portsFor(env, {
      gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
    });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true, '--json': true } }, seed.ports), 0);
    armed401 = true;

    // Now run pdd test place-order --json: initial sign-in uses cached TOKEN_OCTO; on 401, gh auth token returns TOKEN_OCTO_2.
    let authCallIndex = 0;
    const calls = [];
    const made = portsFor(env, {
      gh: args => {
        calls.push(args);
        if (args[0] === 'auth') {
          authCallIndex += 1;
          return { status: 0, stdout: `${authCallIndex === 1 ? TOKEN_OCTO : TOKEN_OCTO_2}\n` };
        }
        return { status: 0, stdout: 'octo 4242\n' };
      },
    });
    const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, made.ports);
    assert.equal(code, vector.expected.subcase_a_exit_code, made.ports.stderr.text);
    assert.equal(apiUserCalls(calls).length, vector.expected.subcase_a_gh_api_user_calls);
    assert.equal(lintAttempts, vector.expected.subcase_a_http_attempts_for_rejected_call);

    const summary = parseExactJson(made.ports.stdout.text);
    const batchFolder = join(setup.state, 'batches', summary.batch);
    const postedMarkers = readdirSync(batchFolder).filter(name => name.endsWith('.posted'));
    // Exactly 1 .posted for lint + 1 .posted for check = 0 duplicate .posted markers!
    assert.equal(postedMarkers.length - 2, vector.expected.subcase_a_duplicate_posted_markers);

    const refreshedCache = parseExactJson(readFileSync(join(setup.state, 'github-user.json'), 'utf8'));
    assert.equal(refreshedCache.token_sha256, sha256Hex(TOKEN_OCTO_2));
    assertNoSecretsOrTempFiles([setup.state, setup.repo], [made.ports.stdout.text, made.ports.stderr.text]);
  });

  // Subcase B: warm cache -> GET on octo's open saved batch & Try answers 401 -> refresh returns 'mallory 777' -> 0 HTTP retries, owner mismatch!
  await t.test('Subcase B: owner mismatch after 401 refresh stops before retrying HTTP request', async t => {
    const setup = cliHarbor(t);
    let getAttempts = 0;
    let rejectWith401 = false;
    let pendingRead = true;
    let interruptSeed;

    const fake = await fakeRuntime(t, (entry, f) => {
      if (rejectWith401) {
        getAttempts += 1;
        return { status: 401, json: { error: { code: 'auth-required' } } };
      }
      if (entry.method === 'GET' && pendingRead) {
        interruptSeed?.();
        return { status: 200, json: f.check(entry.url.split('/').at(-1), 'running') };
      }
      if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
      return f.normal(entry);
    });
    const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };

    // Create an open (running) batch owned by octo, plus an open CLI Try owned by octo.
    const seed = portsFor(env, {
      gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
    });
    interruptSeed = () => seed.clock.interrupt();
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: {} }, seed.ports), 3);
    const openBatch = /pdd test --read (\S+)/.exec(seed.ports.stderr.text)[1];

    pendingRead = false;
    const trySeed = portsFor(env, {
      stdin: Readable.from([]),
      shell: async () => 0,
      gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
    });
    assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--cli': true } }, trySeed.ports), 0);
    const descriptorPath = readdirSync(join(setup.state, 'tries')).filter(name => name.endsWith('.door.json')).map(name => join(setup.state, 'tries', name))[0];
    const descriptor = parseExactJson(readFileSync(descriptorPath, 'utf8'));

    // Now enable 401 on HTTP and have post-401 refresh return mallory!
    rejectWith401 = true;

    // Saved batch --read:
    {
      getAttempts = 0;
      let authCalls = 0;
      const made = portsFor(env, {
        gh: args => {
          if (args[0] === 'auth') return { status: 0, stdout: `${++authCalls === 1 ? TOKEN_OCTO : TOKEN_MALLORY}\n` };
          return { status: 0, stdout: 'mallory 777\n' };
        },
      });
      const code = await runCheck({ cwd: setup.repo, words: [openBatch], options: { '--read': true } }, made.ports);
      assert.equal(code, vector.expected.subcase_b_exit_code);
      assert.equal(getAttempts - 1, vector.expected.subcase_b_http_retries_after_owner_mismatch);
      assert.ok(made.ports.stderr.text.includes(vector.expected.subcase_b_stderr_contains), made.ports.stderr.text);
    }

    // Re-seed github-user.json back to octo and test saved Try attach + runDoorCall on 401 -> mallory:
    writeFileSync(
      join(setup.state, 'github-user.json'),
      JSON.stringify({ login: 'octo', user_id: '4242', cached_at: '2026-10-27T16:27:47.000Z', token_sha256: sha256Hex(TOKEN_OCTO) }),
      { mode: 0o600 },
    );
    {
      getAttempts = 0;
      let authCalls = 0;
      const made = portsFor(env, {
        gh: args => {
          if (args[0] === 'auth') return { status: 0, stdout: `${++authCalls === 1 ? TOKEN_OCTO : TOKEN_MALLORY}\n` };
          return { status: 0, stdout: 'mallory 777\n' };
        },
      });
      const code = await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--page': true, '--no-open': true, '--no-wait': true } }, made.ports);
      assert.equal(code, vector.expected.subcase_b_exit_code);
      assert.equal(getAttempts - 1, vector.expected.subcase_b_http_retries_after_owner_mismatch);
      assert.ok(made.ports.stderr.text.includes(vector.expected.subcase_b_stderr_contains), made.ports.stderr.text);
    }

    // Re-seed github-user.json back to octo and test runDoorCall POST 401 -> mallory:
    writeFileSync(
      join(setup.state, 'github-user.json'),
      JSON.stringify({ login: 'octo', user_id: '4242', cached_at: '2026-10-27T16:27:47.000Z', token_sha256: sha256Hex(TOKEN_OCTO) }),
      { mode: 0o600 },
    );
    {
      const doorPostsBefore = fake.jsonPosts.length;
      let authCalls = 0;
      const made = portsFor(env, {
        gh: args => {
          if (args[0] === 'auth') return { status: 0, stdout: `${++authCalls === 1 ? TOKEN_OCTO : TOKEN_MALLORY}\n` };
          return { status: 0, stdout: 'mallory 777\n' };
        },
      });
      await assert.rejects(
        runDoorCall(descriptor, { argv: ['hi'] }, made.ports),
        err => err.exitCode === 125 && err.unknownOutcome === undefined && err.message.includes(vector.expected.subcase_b_stderr_contains),
      );
      assert.equal(fake.jsonPosts.length - doorPostsBefore - 1, vector.expected.subcase_b_http_retries_after_owner_mismatch);
    }
  });

  // Subcase C: warm cache -> single retry after refresh ALSO answers 401 -> 2 HTTP attempts total, cache deleted, exit 5 with AUTH_TEXT on stderr!
  await t.test('Subcase C: single retry also 401 deletes github-user.json and exits 5 with no loop', async t => {
    const setup = harbor(t);
    let lintAttempts = 0;
    let always401 = false;
    const fake = await fakeRuntime(t, (entry, f) => {
      if (always401 && entry.command === 'lint') {
        lintAttempts += 1;
        return { status: 401, json: { error: { code: 'auth-required' } } };
      }
      return f.normal(entry);
    });
    const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };

    // Seed warm cache.
    const seed = portsFor(env, {
      gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
    });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true, '--json': true } }, seed.ports), 0);

    always401 = true;
    let authCalls = 0;
    const calls = [];
    const made = portsFor(env, {
      gh: args => {
        calls.push(args);
        if (args[0] === 'auth') return { status: 0, stdout: `${++authCalls === 1 ? TOKEN_OCTO : TOKEN_OCTO_2}\n` };
        return { status: 0, stdout: 'octo 4242\n' };
      },
    });
    const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, made.ports);
    assert.equal(code, vector.expected.subcase_c_exit_code);
    assert.equal(apiUserCalls(calls).length, vector.expected.subcase_c_gh_api_user_calls);
    assert.equal(lintAttempts, vector.expected.subcase_c_http_attempts_for_rejected_call);
    assert.equal(existsSync(join(setup.state, 'github-user.json')), vector.expected.subcase_c_cache_file_exists_after);
    assert.ok(made.ports.stderr.text.includes(vector.expected.subcase_c_stderr_contains), made.ports.stderr.text);
  });

  // Subcase D: cold-cache sign-in (already called gh api user fresh in this invocation) + 401 -> 0 extra gh calls, 1 HTTP attempt, cache deleted, exit 5.
  await t.test('Subcase D: cold fresh sign-in + 401 does not refresh again or retry and deletes github-user.json', async t => {
    const setup = harbor(t);
    let lintAttempts = 0;
    const fake = await fakeRuntime(t, entry => {
      if (entry.command === 'lint') {
        lintAttempts += 1;
        return { status: 401, json: { error: { code: 'auth-required' } } };
      }
      return { status: 401, json: { error: { code: 'auth-required' } } };
    });
    const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
    const calls = [];
    const made = portsFor(env, {
      gh: args => {
        calls.push(args);
        return args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' };
      },
    });
    const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, made.ports);
    assert.equal(code, vector.expected.subcase_d_exit_code);
    // Initial cold sign-in called gh api user once; 0 extra calls after 401!
    assert.equal(apiUserCalls(calls).length - 1, vector.expected.subcase_d_extra_gh_api_user_calls_after_401);
    assert.equal(lintAttempts, vector.expected.subcase_d_http_attempts_for_rejected_call);
    assert.equal(existsSync(join(setup.state, 'github-user.json')), vector.expected.subcase_d_cache_file_exists_after);
    assert.ok(made.ports.stderr.text.includes(vector.expected.subcase_c_stderr_contains), made.ports.stderr.text);
  });
});

test('vector 8: gh-api-user-failure-and-rate-limit-boundaries (Subcases A & B)', async t => {
  const vector = BY_ID.get('gh-api-user-failure-and-rate-limit-boundaries');

  // Subcase A: cold cache and switched token while gh api user fails with HTTP 403 rate limit -> exit 5, no cache written/overwritten, token redacted.
  await t.test('Subcase A: cold cache or switched token with rate-limited gh api user exits 5', async t => {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
    const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };

    // Cold cache:
    const cold = portsFor(env, {
      gh: args => (args[0] === 'auth'
        ? { status: 0, stdout: `${TOKEN_OCTO}\n` }
        : { status: 1, stdout: '', stderr: `HTTP 403: API rate limit exceeded (${TOKEN_OCTO})\nsecond line\n` }),
    });
    const coldCode = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, cold.ports);
    assert.equal(coldCode, vector.expected.subcase_a_exit_code);
    assert.equal(existsSync(join(setup.state, 'github-user.json')), vector.expected.subcase_a_cache_written);
    assert.ok(cold.ports.stderr.text.includes('pdd could not read your GitHub login (gh api user: HTTP 403: API rate limit exceeded ([secret])). Run gh auth status.'), cold.ports.stderr.text);
    assertNoSecretsOrTempFiles([setup.state, setup.repo], [cold.ports.stdout.text, cold.ports.stderr.text]);

    // Seed valid octo cache + saved batch, then switch token to TOKEN_MALLORY while rate-limited:
    const seed = portsFor(env, {
      gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
    });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, seed.ports), 0);
    const batch = parseExactJson(seed.ports.stdout.text).batch;

    const switched = portsFor(env, {
      gh: args => (args[0] === 'auth'
        ? { status: 0, stdout: `${TOKEN_MALLORY}\n` }
        : { status: 1, stdout: '', stderr: 'HTTP 403: API rate limit exceeded\n' }),
    });
    const switchedCode = await runCheck({ cwd: setup.repo, words: [batch], options: { '--read': true } }, switched.ports);
    assert.equal(switchedCode, vector.expected.subcase_a_exit_code);
    assert.ok(switched.ports.stderr.text.includes(vector.expected.subcase_a_stderr_contains), switched.ports.stderr.text);
    assert.equal(parseExactJson(readFileSync(join(setup.state, 'github-user.json'), 'utf8')).login, 'octo');
  });

  // Subcase B: forced refresh while valid matching-token github-user.json exists and gh api user fails with GitHub rate limit:
  // - local saved-batch --read prints stderr warning and exits 0
  // - remote check, open-batch remote --read, and post-401 refresh exit 5!
  await t.test('Subcase B: forced refresh rate-limit fallback applies only to local saved-batch --read and never remote or post-401', async t => {
    const setup = harbor(t);
    let rejectLint401 = false;
    let holdRunning = false;
    let interruptOpen;
    const fake = await fakeRuntime(t, (entry, f) => {
      if (rejectLint401 && entry.command === 'lint') return { status: 401, json: { error: { code: 'auth-required' } } };
      if (holdRunning && entry.method === 'GET') {
        interruptOpen?.();
        return { status: 200, json: f.check(entry.url.split('/').at(-1), 'running') };
      }
      return f.normal(entry);
    });
    const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };

    // Seed terminal saved batch + matching github-user.json for octo.
    const seed = portsFor(env, {
      gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
    });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, seed.ports), 0);
    const localBatch = parseExactJson(seed.ports.stdout.text).batch;

    // Also seed an open (running) batch that requires remote HTTP GET on --read.
    holdRunning = true;
    const openSeed = portsFor(env, {
      gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
    });
    interruptOpen = () => openSeed.clock.interrupt();
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'] }, openSeed.ports), 3);
    const openBatch = /pdd test --read (\S+)/.exec(openSeed.ports.stderr.text)[1];
    holdRunning = false;

    const rateLimitedForcedPorts = () => portsFor(env, {
      forceAuthRefresh: true,
      gh: args => (args[0] === 'auth'
        ? { status: 0, stdout: `${TOKEN_OCTO}\n` }
        : { status: 1, stdout: '', stderr: 'HTTP 403: API rate limit exceeded\n' }),
    });

    // 1. Local terminal saved-batch --read -> prints warning once and exits 0!
    const localRead = rateLimitedForcedPorts();
    const localCode = await runCheck({ cwd: setup.repo, words: [localBatch], options: { '--read': true, '--json': true } }, localRead.ports);
    assert.equal(localCode, vector.expected.subcase_b_saved_local_read_exit_code, localRead.ports.stderr.text);
    assert.ok(localRead.ports.stderr.text.includes(vector.expected.subcase_b_saved_local_read_stderr_contains), localRead.ports.stderr.text);
    assert.equal((localRead.ports.stderr.text.match(/Warning: GitHub API rate limit reached/g) ?? []).length, 1);

    // 2. Open saved-batch --read needing remote HTTP -> exits 5!
    const openRead = rateLimitedForcedPorts();
    assert.equal(
      await runCheck({ cwd: setup.repo, words: [openBatch], options: { '--read': true, '--json': true } }, openRead.ports),
      vector.expected.subcase_b_remote_or_post_401_exit_code,
    );

    // 3. Remote pdd test -> exits 5!
    const remoteCheck = rateLimitedForcedPorts();
    assert.equal(
      await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, remoteCheck.ports),
      vector.expected.subcase_b_remote_or_post_401_exit_code,
    );

    // 4. Post-401 refresh while gh api user is rate-limited -> never falls back, deletes cache and exits 5!
    rejectLint401 = true;
    const post401 = portsFor(env, {
      gh: args => (args[0] === 'auth'
        ? { status: 0, stdout: `${TOKEN_OCTO}\n` }
        : { status: 1, stdout: '', stderr: 'HTTP 403: API rate limit exceeded\n' }),
    });
    assert.equal(
      await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, post401.ports),
      vector.expected.subcase_b_remote_or_post_401_exit_code,
    );
    assert.equal(existsSync(join(setup.state, 'github-user.json')), false);
    assert.doesNotMatch(post401.ports.stderr.text, /Warning: GitHub API rate limit reached/);
  });
});

test('non-regression & safety boundaries: local lint, Story pass cache, checkRuntimeHealth, inside-repo state refusal, and symlink fail-open', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };

  // 1. pdd lint --local and its saved --read make 0 gh calls.
  {
    const localPorts = portsFor(env, { gh: () => assert.fail('pdd lint --local must not call gh') });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true, '--local': true, '--json': true } }, localPorts.ports), 0);
    const localBatch = parseExactJson(localPorts.ports.stdout.text).batch;
    const readLocalPorts = portsFor(env, { gh: () => assert.fail('saved local lint --read must not call gh') });
    assert.equal(await runCheck({ cwd: setup.repo, words: [localBatch], options: { '--read': true, '--json': true } }, readLocalPorts.ports), 0);
  }

  // 2. Unchanged Story pass reuse in .pdd/cache/test/ makes 0 gh calls on the cached rerun.
  {
    const first = portsFor(env, {
      gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
    });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true }, cache: true }, first.ports), 0, first.ports.stderr.text);
    const cached = portsFor(env, { gh: () => assert.fail('unchanged cached Story pass must not call gh') });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true }, cache: true }, cached.ports), 0, cached.ports.stderr.text);
    assert.equal(parseExactJson(cached.ports.stdout.text).rows[0].cached, true);
  }

  // 3. checkRuntimeHealth calls gh auth token once and gh api user 0 times.
  {
    fake.capacity = () => ({ status: 200, json: { maintenance: null } });
    const calls = [];
    const verdict = await checkRuntimeHealth(
      { env },
      {
        gh: args => {
          calls.push(args);
          if (args[0] === 'auth') return { status: 0, stdout: `${TOKEN_OCTO}\n` };
          assert.fail('checkRuntimeHealth must never call gh api user');
        },
      },
    );
    assert.equal(verdict.state, 'healthy');
    assert.equal(authTokenCalls(calls).length, 1);
    assert.equal(apiUserCalls(calls).length, 0);
  }

  // 4. PDD_STATE_DIR inside repository still exits 2.
  {
    const insideEnv = { HOME: setup.home, PDD_STATE_DIR: join(setup.repo, '.inside-state'), PDD_RUNTIME_URL: fake.origin };
    const insidePorts = portsFor(insideEnv);
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'] }, insidePorts.ports), 2);
    assert.match(insidePorts.ports.stderr.text, /PDD_STATE_DIR is inside this repository/);
  }

  // 5. Optional github-user.json persistence fails open if github-user.json is replaced by a symlink, without following the symlink.
  {
    const targetDir = temp(t);
    const decoy = join(targetDir, 'decoy.json');
    writeFileSync(decoy, 'untouched\n');
    const cacheFile = join(setup.state, 'github-user.json');
    rmSync(cacheFile, { force: true });
    symlinkSync(decoy, cacheFile);

    const made = portsFor(env, {
      gh: args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_OCTO}\n` } : { status: 0, stdout: 'octo 4242\n' }),
    });
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true, '--json': true } }, made.ports), 0, made.ports.stderr.text);
    assert.equal(readFileSync(decoy, 'utf8'), 'untouched\n', 'symlink target must never be overwritten');
    chmodSync(setup.state, 0o700);
  }
});
