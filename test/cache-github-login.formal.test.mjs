import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { chmodSync, cpSync, existsSync, lstatSync, mkdirSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { proseSha256, readTryOwner, runCheck, runDoorCall, runTry } from '../src/runtime-seam.mjs';
import { PLACE, fakeRuntime, filesUnder, harbor, portsFor, temp } from './helpers/runtime-fake.mjs';

// Independent specification oracle derived strictly from
// user_stories/cache-github-login.md ("## Rules to check") and
// prompts/cli/runtime-client.prompt.md ("## Sign-in"), never from implementation code.

const TOKEN_A = 'gho_FORMAL_TOKEN_A_secret_never_persist_101a';
const TOKEN_A2 = 'gho_FORMAL_TOKEN_A2_rotated_never_persist_202b';
const TOKEN_B = 'gho_FORMAL_TOKEN_B_switched_never_persist_303c';
const ALL_SECRETS = [TOKEN_A, TOKEN_A2, TOKEN_B];
const FIXED_ISO = '2026-10-27T16:27:47.000Z';

const sha256 = value => createHash('sha256').update(value, 'utf8').digest('hex');
const SHA_A = sha256(TOKEN_A);
const SHA_A2 = sha256(TOKEN_A2);
const SHA_B = sha256(TOKEN_B);

const modeBits = path => statSync(path).mode & 0o777;
const authCalls = list => list.filter(args => args[0] === 'auth' && args[1] === 'token');
const apiCalls = list => list.filter(args => args[0] === 'api' && args[1] === 'user');

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
    const renderPrompt = () =>
      `# paperclip\n\nPrint each argument on its own line.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
    iface.prose_sha256 = proseSha256(renderPrompt());
    writeFileSync(join(root, PLACE), renderPrompt());
    writeFileSync(
      join(root, 'user_stories/place-order.md'),
      '# Arguments\n\nI can pass words.\n\n## Acceptance criteria\n\n1. Each argument prints on its own line.\n',
    );
    const scenario = {
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
    writeFileSync(join(root, 'tests/place-order.json'), `${JSON.stringify(scenario, null, 2)}\n`);
  });
}

function enforcePrivateModes(dir) {
  if (!existsSync(dir)) return;
  chmodSync(dir, 0o700);
  for (const entry of filesUnder(dir)) {
    const st = lstatSync(entry);
    if (st.isDirectory()) chmodSync(entry, 0o700);
    else if (st.isFile()) chmodSync(entry, 0o600);
  }
}

// Rule 1 universal invariant check: no raw token anywhere on disk, outputs, argv or URLs;
// 0 leftover github-user.json*.tmp files; 0700 state dir and 0600 valid schema when valid.
function assertRule1Invariants({ stateDir, repoDir, outputs = [], ghLog = [], urls = [], expectValidCache = null }, context) {
  for (const args of ghLog) {
    for (const secret of ALL_SECRETS) {
      assert.equal(args.join(' ').includes(secret), false, `${context}: raw token in gh argv`);
    }
  }
  for (const url of urls) {
    for (const secret of ALL_SECRETS) {
      assert.equal(String(url).includes(secret), false, `${context}: raw token in URL`);
    }
  }
  for (const text of outputs) {
    for (const secret of ALL_SECRETS) {
      assert.equal(String(text).includes(secret), false, `${context}: raw token leaked in output`);
    }
  }
  for (const root of [stateDir, repoDir]) {
    if (!existsSync(root)) continue;
    for (const path of filesUnder(root)) {
      const base = path.split('/').at(-1);
      assert.doesNotMatch(base, /^github-user\.json\..*\.tmp$/, `${context}: leftover atomic temp file ${path}`);
      let st;
      try { st = lstatSync(path); } catch { continue; }
      if (!st.isFile()) continue;
      const body = readFileSync(path, 'utf8');
      for (const secret of ALL_SECRETS) {
        assert.equal(body.includes(secret), false, `${context}: raw token leaked to disk at ${path}`);
      }
    }
  }
  if (existsSync(stateDir)) {
    assert.equal(modeBits(stateDir), 0o700, `${context}: $PDD_STATE_DIR must be 0700`);
  }
  const cachePath = join(stateDir, 'github-user.json');
  if (expectValidCache) {
    assert.equal(existsSync(cachePath), true, `${context}: expected valid github-user.json to exist`);
    assert.equal(modeBits(cachePath), 0o600, `${context}: github-user.json must be 0600`);
    const parsed = JSON.parse(readFileSync(cachePath, 'utf8'));
    assert.deepEqual(Object.keys(parsed).sort(), ['cached_at', 'login', 'token_sha256', 'user_id'], `${context}: exact schema keys`);
    assert.equal(parsed.login, expectValidCache.login, `${context}: cached login`);
    assert.equal(parsed.user_id, expectValidCache.user_id, `${context}: cached user_id`);
    assert.match(parsed.login, /^\S+$/, `${context}: nonblank whitespace-free login`);
    assert.match(parsed.user_id, /^[1-9]\d*$/, `${context}: positive decimal user_id`);
    assert.equal(parsed.token_sha256, expectValidCache.token_sha256, `${context}: lowercase 64-hex token_sha256`);
    assert.match(parsed.token_sha256, /^[a-f0-9]{64}$/, `${context}: 64-hex digest`);
    assert.ok(Number.isFinite(Date.parse(parsed.cached_at)), `${context}: ISO cached_at`);
  }
}

const CACHE_STATES = [
  {
    id: 'valid_token_a',
    validFor: { token: TOKEN_A, sha: SHA_A, login: 'octo', user_id: '4242' },
    write(stateDir) {
      writeFileSync(join(stateDir, 'github-user.json'), JSON.stringify({
        login: 'octo', user_id: '4242', cached_at: FIXED_ISO, token_sha256: SHA_A,
      }), { mode: 0o600 });
    },
  },
  {
    id: 'absent',
    validFor: null,
    write(stateDir) { rmSync(join(stateDir, 'github-user.json'), { force: true }); },
  },
  {
    id: 'valid_token_b',
    validFor: { token: TOKEN_B, sha: SHA_B, login: 'mallory', user_id: '777' },
    write(stateDir) {
      writeFileSync(join(stateDir, 'github-user.json'), JSON.stringify({
        login: 'mallory', user_id: '777', cached_at: FIXED_ISO, token_sha256: SHA_B,
      }), { mode: 0o600 });
    },
  },
  {
    id: 'corrupt_json',
    validFor: null,
    write(stateDir) { writeFileSync(join(stateDir, 'github-user.json'), '{partial', { mode: 0o600 }); },
  },
  {
    id: 'missing_token_sha256',
    validFor: null,
    write(stateDir) {
      writeFileSync(join(stateDir, 'github-user.json'), JSON.stringify({
        login: 'octo', user_id: '4242', cached_at: FIXED_ISO,
      }), { mode: 0o600 });
    },
  },
  {
    id: 'blank_login',
    validFor: null,
    write(stateDir) {
      writeFileSync(join(stateDir, 'github-user.json'), JSON.stringify({
        login: '', user_id: '4242', cached_at: FIXED_ISO, token_sha256: SHA_A,
      }), { mode: 0o600 });
    },
  },
  {
    id: 'whitespace_login',
    validFor: null,
    write(stateDir) {
      writeFileSync(join(stateDir, 'github-user.json'), JSON.stringify({
        login: 'octo user', user_id: '4242', cached_at: FIXED_ISO, token_sha256: SHA_A,
      }), { mode: 0o600 });
    },
  },
  {
    id: 'zero_user_id',
    validFor: null,
    write(stateDir) {
      writeFileSync(join(stateDir, 'github-user.json'), JSON.stringify({
        login: 'octo', user_id: '0', cached_at: FIXED_ISO, token_sha256: SHA_A,
      }), { mode: 0o600 });
    },
  },
  {
    id: 'non_numeric_user_id',
    validFor: null,
    write(stateDir) {
      writeFileSync(join(stateDir, 'github-user.json'), JSON.stringify({
        login: 'octo', user_id: 'abc', cached_at: FIXED_ISO, token_sha256: SHA_A,
      }), { mode: 0o600 });
    },
  },
];

const AUTH_STATES = [
  {
    id: 'token_a',
    ok: true,
    token: TOKEN_A,
    sha: SHA_A,
    reply: () => ({ status: 0, stdout: `  ${TOKEN_A}\n`, stderr: '' }),
  },
  {
    id: 'token_b',
    ok: true,
    token: TOKEN_B,
    sha: SHA_B,
    reply: () => ({ status: 0, stdout: `${TOKEN_B}\n`, stderr: '' }),
  },
  {
    id: 'enoent',
    ok: false,
    expectedMsg: 'Install the GitHub CLI, then run gh auth login',
    reply: () => ({ status: null, stdout: '', stderr: '', error: Object.assign(new Error('spawn gh ENOENT'), { code: 'ENOENT' }) }),
  },
  {
    id: 'nonzero',
    ok: false,
    expectedMsg: 'Run gh auth login',
    reply: () => ({ status: 1, stdout: '', stderr: `not logged in (${TOKEN_A})\n` }),
  },
  {
    id: 'blank',
    ok: false,
    expectedMsg: 'Run gh auth login',
    reply: () => ({ status: 0, stdout: '  \t\n', stderr: '' }),
  },
];

const API_STATES = [
  {
    id: 'octo_4242',
    ok: true,
    login: 'octo',
    user_id: '4242',
    reply: () => ({ status: 0, stdout: 'octo 4242\n', stderr: '' }),
  },
  {
    id: 'mallory_777',
    ok: true,
    login: 'mallory',
    user_id: '777',
    reply: () => ({ status: 0, stdout: 'mallory 777\n', stderr: '' }),
  },
  {
    id: 'invalid_blank_login',
    ok: false,
    reply: () => ({ status: 0, stdout: ' 4242\n', stderr: '' }),
  },
  {
    id: 'invalid_zero_id',
    ok: false,
    reply: () => ({ status: 0, stdout: 'octo 0\n', stderr: '' }),
  },
  {
    id: 'rate_limit_403',
    ok: false,
    rateLimit: true,
    reply: () => ({ status: 1, stdout: '', stderr: `HTTP 403: API rate limit exceeded (${TOKEN_A} ${TOKEN_B})\n` }),
  },
];

async function seedFixture(t, runtimeOverride) {
  const setup = cliHarbor(t);
  const goldenState = join(temp(t), 'golden-state');
  let holdOpenBatch = false;
  let interruptOpen;
  const observedUrls = [];

  const fake = await fakeRuntime(t, (entry, f) => {
    observedUrls.push(entry.url);
    if (runtimeOverride) {
      const custom = runtimeOverride(entry, f);
      if (custom) return custom;
    }
    if (entry.json) {
      const argv = entry.json.input?.argv ?? [];
      const programResult = { stdout: `${argv.join('\n')}\n`, stderr: '', exit_code: 0 };
      const callId = entry.json.requestId;
      const sessionId = entry.url.split('/')[3];
      const job = {
        ...f.job(callId, 'call', 'passed', {
          program_result: programResult,
          report: { verdict: 'passed', result: programResult, action_id: `act-${callId}`, remaining_calls: 399 },
          output: programResult,
        }, 1),
        session_id: sessionId,
      };
      f.jobs.set(callId, job);
      return { status: 200, json: job };
    }
    const tail = entry.url.split('/').at(-1);
    if (f.jobs.has(tail) && !holdOpenBatch) return { status: 200, json: f.jobs.get(tail) };
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
      return { status: 200, json: { world: {}, actions: [] } };
    }
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') {
      const job = f.tryJob(entry.request.requestId);
      f.jobs.set(entry.request.requestId, job);
      return { status: 200, json: job };
    }
    if (entry.command === 'check') {
      if (holdOpenBatch) {
        return { status: 202, json: f.check(entry.request.requestId, 'queued') };
      }
      const passed = f.check(entry.request.requestId, 'passed', [
        { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', expected: 'say\ntwo words\n', actual: 'say\ntwo words\n', passed: true },
        { criterion_id: 'AC1', target: 'world', path: '', op: 'equals', expected: {}, actual: {}, passed: true },
      ]);
      f.jobs.set(entry.request.requestId, passed);
      return { status: 200, json: passed };
    }
    if (entry.method === 'GET' && holdOpenBatch) {
      interruptOpen?.();
      return { status: 200, json: f.check(tail, 'running') };
    }
    return f.normal(entry);
  });

  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
  const seedGh = args => (args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_A}\n` } : { status: 0, stdout: 'octo 4242\n' });

  // 1. Terminal saved batch owned by octo.
  const termMade = portsFor(env, { gh: seedGh });
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, termMade.ports), 0);
  const termSummary = JSON.parse(termMade.ports.stdout.text);
  const terminalBatch = termSummary.batch;
  const checkUuid = termSummary.rows[0].request_id;

  // 2. Open (running) saved batch owned by octo.
  holdOpenBatch = true;
  const openMade = portsFor(env, { gh: seedGh });
  interruptOpen = () => openMade.clock.interrupt();
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'] }, openMade.ports), 3);
  const openBatch = /pdd test --read (\S+)/.exec(openMade.ports.stderr.text)[1];
  holdOpenBatch = false;

  // 3. Open CLI Try + door descriptor + call receipt owned by octo.
  const tryMade = portsFor(env, { stdin: Readable.from([]), shell: async () => 0, gh: seedGh });
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--cli': true } }, tryMade.ports), 0);
  const descriptorFile = readdirSync(join(setup.state, 'tries')).filter(name => name.endsWith('.door.json'))[0];
  const descriptor = JSON.parse(readFileSync(join(setup.state, 'tries', descriptorFile), 'utf8'));
  const seededCall = await runDoorCall(descriptor, { argv: ['seed'] }, portsFor(env, { gh: seedGh }).ports);
  const callUuid = seededCall.id;

  rmSync(join(setup.state, 'github-user.json'), { force: true });
  cpSync(setup.state, goldenState, { recursive: true });
  enforcePrivateModes(goldenState);

  function resetState(cacheState, completelyAbsentDir = false) {
    rmSync(setup.state, { recursive: true, force: true });
    if (completelyAbsentDir) return;
    cpSync(goldenState, setup.state, { recursive: true });
    enforcePrivateModes(setup.state);
    cacheState.write(setup.state);
  }

  const httpTotal = () => fake.posts.length + fake.jsonPosts.length + fake.gets.length + fake.deletes.length;

  return { setup, fake, env, terminalBatch, openBatch, checkUuid, callUuid, descriptor, resetState, httpTotal, observedUrls };
}

async function invokeEntry(entryKind, fixture, ports) {
  const { setup, terminalBatch, openBatch, checkUuid, callUuid, descriptor } = fixture;
  if (entryKind === 'check_saved_read') {
    const code = await runCheck({ cwd: setup.repo, words: [terminalBatch], options: { '--read': true, '--json': true } }, ports);
    return { kind: 'code', code, door: false };
  }
  if (entryKind === 'open_batch_read') {
    const code = await runCheck({ cwd: setup.repo, words: [openBatch], options: { '--read': true, '--json': true } }, ports);
    return { kind: 'code', code, door: false };
  }
  if (entryKind === 'call_read') {
    const code = await runCheck({ cwd: setup.repo, words: [callUuid], options: { '--read': true, '--json': true } }, ports);
    return { kind: 'code', code, door: false };
  }
  if (entryKind === 'request_read') {
    const code = await runCheck({ cwd: setup.repo, options: { '--request': checkUuid, '--json': true } }, ports);
    return { kind: 'code', code, door: false };
  }
  if (entryKind === 'check_lint') {
    const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true, '--json': true } }, ports);
    return { kind: 'code', code, door: false };
  }
  if (entryKind === 'check_post') {
    const code = await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true } }, ports);
    return { kind: 'code', code, door: false };
  }
  if (entryKind === 'try_attach') {
    const code = await runTry(
      { cwd: setup.repo, words: ['place-order'], options: { '--page': true, '--no-open': true, '--no-wait': true, '--max-calls': '400' } },
      ports,
    );
    return { kind: 'code', code, door: false };
  }
  if (entryKind === 'door_call') {
    try {
      const value = await runDoorCall(descriptor, { argv: ['x'] }, ports);
      return { kind: 'resolved', value, door: true };
    } catch (error) {
      return { kind: 'rejected', error, door: true };
    }
  }
  if (entryKind === 'mcp_owner') {
    try {
      const value = await readTryOwner({ cwd: setup.repo }, ports);
      return { kind: 'resolved', value, door: false };
    } catch (error) {
      return { kind: 'rejected', error, door: false };
    }
  }
  throw new Error(`Unknown entryKind: ${entryKind}`);
}

// Oracle for Rules 1, 2, 3, and 4 on normal sign-in (runtime 200).
function assertNormalSignInOracle({ entryKind, cacheState, authState, apiState, outcome, ghLog, httpDelta, lastAuthHeader, fixture, stdout, stderr }, ctx) {
  const outputs = [stdout, stderr, outcome.error?.message ?? ''];

  // Every sign-in reads gh auth token live once.
  assert.equal(authCalls(ghLog).length, 1, `${ctx}: gh auth token must run once`);

  // Rule 4: Missing gh or failed/blank gh auth token stops before reading or returning github-user.json.
  if (!authState.ok) {
    assert.equal(apiCalls(ghLog).length, 0, `${ctx}: Rule 4 forbidden gh api user call on failed/blank gh auth token`);
    assert.equal(httpDelta, 0, `${ctx}: Rule 4 must make 0 runtime HTTP calls`);
    if (outcome.kind === 'code') {
      assert.equal(outcome.code, 5, `${ctx}: Rule 4 CLI exit 5`);
      assert.ok(stderr.includes(authState.expectedMsg), `${ctx}: Rule 4 expected auth message in stderr`);
      assert.equal(stdout, '', `${ctx}: Rule 4 must not emit cached result to stdout`);
    } else {
      assert.equal(outcome.kind, 'rejected', `${ctx}: Rule 4 must reject`);
      if (outcome.door) assert.equal(outcome.error.exitCode, 125, `${ctx}: Rule 4 door exitCode 125`);
      assert.ok(outcome.error.message.includes(authState.expectedMsg), `${ctx}: Rule 4 expected auth message`);
    }
    const preservedValid = cacheState.validFor
      ? { login: cacheState.validFor.login, user_id: cacheState.validFor.user_id, token_sha256: cacheState.validFor.sha }
      : null;
    assertRule1Invariants({
      stateDir: fixture.setup.state,
      repoDir: fixture.setup.repo,
      outputs,
      ghLog,
      urls: fixture.observedUrls,
      expectValidCache: preservedValid,
    }, ctx);
    return;
  }

  const warmMatch = cacheState.validFor && cacheState.validFor.sha === authState.sha;

  let resolvedLogin;
  let resolvedUserId;

  if (warmMatch) {
    // Rule 2: Valid matching github-user.json satisfies sign-in with 0 gh api user calls.
    assert.equal(apiCalls(ghLog).length, 0, `${ctx}: Rule 2 forbidden gh api user call on warm matching cache`);
    resolvedLogin = cacheState.validFor.login;
    resolvedUserId = cacheState.validFor.user_id;
  } else {
    // Rule 3: Missing, corrupt, incomplete, or token_sha256-mismatched cache runs gh api user once.
    assert.equal(apiCalls(ghLog).length, 1, `${ctx}: Rule 3 must call gh api user exactly once`);
    assert.deepEqual(apiCalls(ghLog)[0], ['api', 'user', '--jq', '.login + " " + (.id|tostring)'], `${ctx}: Rule 3 exact gh api user args`);

    if (!apiState.ok) {
      // Rule 3 & Rule 6: Cold/corrupt/mismatched or normal sign-in failure never reuses another token's identity
      // and never accepts invalid login or non-positive user_id.
      assert.equal(httpDelta, 0, `${ctx}: failed gh api user must make 0 runtime HTTP calls`);
      if (outcome.kind === 'code') {
        assert.equal(outcome.code, 5, `${ctx}: failed gh api user exits 5`);
        assert.ok(stderr.includes('pdd could not read your GitHub login'), `${ctx}: stderr names gh api user failure`);
        assert.ok(stderr.includes('Run gh auth status.'), `${ctx}: stderr advises gh auth status`);
      } else {
        assert.equal(outcome.kind, 'rejected', `${ctx}: failed gh api user rejects`);
        if (outcome.door) assert.equal(outcome.error.exitCode, 125, `${ctx}: door exitCode 125`);
        assert.ok(outcome.error.message.includes('pdd could not read your GitHub login'), `${ctx}: error names gh api user failure`);
      }
      const cacheFile = join(fixture.setup.state, 'github-user.json');
      if (existsSync(cacheFile) && cacheState.validFor) {
        // Prior valid cache for a DIFFERENT token may remain intact, never rewritten to unverified active token.
        assertRule1Invariants({
          stateDir: fixture.setup.state,
          repoDir: fixture.setup.repo,
          outputs,
          ghLog,
          urls: fixture.observedUrls,
          expectValidCache: { login: cacheState.validFor.login, user_id: cacheState.validFor.user_id, token_sha256: cacheState.validFor.sha },
        }, ctx);
      } else {
        if (cacheState.id === 'absent') {
          assert.equal(existsSync(cacheFile), false, `${ctx}: Rule 3 must not write github-user.json on invalid/failed gh api user`);
        }
        assertRule1Invariants({
          stateDir: fixture.setup.state,
          repoDir: fixture.setup.repo,
          outputs,
          ghLog,
          urls: fixture.observedUrls,
          expectValidCache: null,
        }, ctx);
      }
      return;
    }

    resolvedLogin = apiState.login;
    resolvedUserId = apiState.user_id;
  }

  // Valid sign-in: github-user.json must now hold the active token's verified {login, user_id, cached_at, token_sha256}.
  assertRule1Invariants({
    stateDir: fixture.setup.state,
    repoDir: fixture.setup.repo,
    outputs,
    ghLog,
    urls: fixture.observedUrls,
    expectValidCache: { login: resolvedLogin, user_id: resolvedUserId, token_sha256: authState.sha },
  }, ctx);

  // Saved-owner vs non-saved-owner behavior:
  if (entryKind === 'check_lint') {
    assert.ok(httpDelta >= 1, `${ctx}: check_lint sends runtime HTTP request`);
    assert.equal(lastAuthHeader(), `Bearer ${authState.token}`, `${ctx}: bearer uses trimmed active token`);
    assert.equal(outcome.code, 0, `${ctx}: check_lint exits 0 (${stderr})`);
    return;
  }

  // Saved resources in fixture belong to 'octo'.
  if (resolvedLogin !== 'octo') {
    assert.equal(httpDelta, 0, `${ctx}: cross-owner refusal happens before runtime HTTP`);
    if (entryKind === 'check_saved_read') {
      assert.equal(outcome.code, 5, `${ctx}: cross-owner saved batch read exits 5`);
      assert.ok(stderr.includes('These runs belong to octo. Run: gh auth switch -u octo'), `${ctx}: batch owner refusal message`);
    } else if (entryKind === 'try_attach') {
      assert.equal(outcome.code, 5, `${ctx}: cross-owner Try attach exits 5`);
      assert.ok(stderr.includes('This Try belongs to octo. Run: gh auth switch -u octo'), `${ctx}: Try owner refusal message`);
    } else if (entryKind === 'door_call') {
      assert.equal(outcome.kind, 'rejected', `${ctx}: cross-owner door call rejects`);
      assert.equal(outcome.error.exitCode, 125, `${ctx}: cross-owner door exitCode 125`);
      assert.ok(outcome.error.message.includes('This Try belongs to octo. Run: gh auth switch -u octo'), `${ctx}: door owner refusal`);
    } else if (entryKind === 'mcp_owner') {
      assert.equal(outcome.kind, 'rejected', `${ctx}: cross-owner readTryOwner rejects`);
      assert.ok(outcome.error.message.includes('This Try belongs to octo. Run: gh auth switch -u octo'), `${ctx}: MCP owner refusal`);
    }
    return;
  }

  // Owner matches ('octo'):
  if (entryKind === 'check_saved_read') {
    assert.equal(httpDelta, 0, `${ctx}: terminal saved batch read makes 0 runtime HTTP calls`);
    assert.equal(outcome.code, 0, `${ctx}: terminal saved batch read exits 0`);
  } else if (entryKind === 'try_attach') {
    assert.ok(httpDelta >= 1, `${ctx}: try_attach reads session over HTTP`);
    assert.equal(lastAuthHeader(), `Bearer ${authState.token}`, `${ctx}: bearer uses trimmed active token`);
    assert.equal(outcome.code, 0, `${ctx}: try_attach exits 0`);
  } else if (entryKind === 'door_call') {
    assert.ok(httpDelta >= 1, `${ctx}: door_call dispatches over HTTP`);
    assert.equal(lastAuthHeader(), `Bearer ${authState.token}`, `${ctx}: bearer uses trimmed active token`);
    assert.equal(outcome.kind, 'resolved', `${ctx}: door_call resolves`);
    assert.equal(outcome.value.result.stdout, 'x\n', `${ctx}: door_call program result`);
  } else if (entryKind === 'mcp_owner') {
    assert.ok(httpDelta >= 1, `${ctx}: mcp_owner reads model/state over HTTP`);
    assert.equal(lastAuthHeader(), `Bearer ${authState.token}`, `${ctx}: bearer uses trimmed active token`);
    assert.equal(outcome.kind, 'resolved', `${ctx}: mcp_owner resolves`);
    assert.equal(outcome.value.record.login, 'octo', `${ctx}: mcp_owner record login`);
  }
}

test('formal Rules 1-4: all 9 github-user.json states x all 5 gh auth token states x all 5 gh api user states on saved --read (225 worlds)', { timeout: 120_000 }, async t => {
  let latestAuth = null;
  const fixture = await seedFixture(t, entry => {
    latestAuth = entry.headers.authorization ?? null;
    return null;
  });

  let worlds = 0;
  for (const cacheState of CACHE_STATES) {
    for (const authState of AUTH_STATES) {
      for (const apiState of API_STATES) {
        worlds += 1;
        const ctx = `1A[${cacheState.id} × ${authState.id} × ${apiState.id}]`;
        fixture.resetState(cacheState, false);
        fixture.observedUrls.length = 0;
        latestAuth = null;
        const ghLog = [];
        const beforeHttp = fixture.httpTotal();

        const made = portsFor(fixture.env, {
          stdin: Readable.from([]),
          gh: args => {
            ghLog.push(args);
            return args[0] === 'auth' ? authState.reply() : apiState.reply();
          },
        });

        const outcome = await invokeEntry('check_saved_read', fixture, made.ports);
        const httpDelta = fixture.httpTotal() - beforeHttp;

        assertNormalSignInOracle({
          entryKind: 'check_saved_read',
          cacheState,
          authState,
          apiState,
          outcome,
          ghLog,
          httpDelta,
          lastAuthHeader: () => latestAuth,
          fixture,
          stdout: made.ports.stdout.text,
          stderr: made.ports.stderr.text,
        }, ctx);
      }
    }
  }
  assert.equal(worlds, 225);
});

test('formal Rules 1-4 cross-boundary: all 5 public entry points x 4 cache states x 5 gh auth token states x 4 gh api user states (400 worlds)', { timeout: 120_000 }, async t => {
  let latestAuth = null;
  const fixture = await seedFixture(t, entry => {
    latestAuth = entry.headers.authorization ?? null;
    return null;
  });

  const entryKinds = ['check_saved_read', 'check_lint', 'try_attach', 'door_call', 'mcp_owner'];
  const subCaches = CACHE_STATES.filter(c => ['absent', 'valid_token_a', 'valid_token_b', 'corrupt_json'].includes(c.id));
  const subApis = API_STATES.filter(a => ['octo_4242', 'mallory_777', 'invalid_zero_id', 'rate_limit_403'].includes(a.id));

  let worlds = 0;
  for (const entryKind of entryKinds) {
    for (const cacheState of subCaches) {
      for (const authState of AUTH_STATES) {
        for (const apiState of subApis) {
          worlds += 1;
          const ctx = `1B[${entryKind} × ${cacheState.id} × ${authState.id} × ${apiState.id}]`;
          const completelyAbsentDir = entryKind === 'check_lint' && cacheState.id === 'absent';
          fixture.resetState(cacheState, completelyAbsentDir);
          fixture.observedUrls.length = 0;
          latestAuth = null;
          const ghLog = [];
          const beforeHttp = fixture.httpTotal();

          const made = portsFor(fixture.env, {
            stdin: Readable.from([]),
            gh: args => {
              ghLog.push(args);
              return args[0] === 'auth' ? authState.reply() : apiState.reply();
            },
          });

          const outcome = await invokeEntry(entryKind, fixture, made.ports);
          const httpDelta = fixture.httpTotal() - beforeHttp;

          assertNormalSignInOracle({
            entryKind,
            cacheState,
            authState,
            apiState,
            outcome,
            ghLog,
            httpDelta,
            lastAuthHeader: () => latestAuth,
            fixture,
            stdout: made.ports.stdout.text,
            stderr: made.ports.stderr.text,
          }, ctx);
        }
      }
    }
  }
  assert.equal(worlds, 400);
});

test('formal Rule 5 HTTP 401: 2 initial cache modes x 4 post-401 refresh states x 2 runtime 401 sequences x 7 public boundaries (112 worlds)', { timeout: 120_000 }, async t => {
  const AUTH_DIAGNOSTIC = 'The PDD interpreter did not accept your GitHub login (HTTP 401). Run gh auth login, then run the command again.';
  let activeRule = null;
  let targetAttempts = 0;
  const targetHeaders = [];

  const isTargetEndpoint = (boundary, entry) => {
    if (boundary === 'check_post') return entry.method === 'POST' && entry.command === 'lint';
    if (['open_batch_read', 'call_read', 'request_read', 'try_attach'].includes(boundary)) return entry.method === 'GET' && entry.url.startsWith('/v1/runs/');
    if (boundary === 'door_call') return Boolean(entry.json);
    if (boundary === 'mcp_owner') return entry.method === 'GET' && entry.url.endsWith('/model');
    return false;
  };

  const fixture = await seedFixture(t, (entry, f) => {
    if (!activeRule) return null;
    if (isTargetEndpoint(activeRule.boundary, entry)) {
      targetAttempts += 1;
      targetHeaders.push(entry.headers.authorization);
      if (activeRule.seq === '401_always' || targetAttempts === 1) {
        return { status: 401, json: { error: { code: 'auth-required' } } };
      }
      if (activeRule.boundary === 'open_batch_read') {
        const id = entry.url.split('/').at(-1);
        return {
          status: 200,
          json: f.check(id, 'passed', [
            { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', expected: 'say\ntwo words\n', actual: 'say\ntwo words\n', passed: true },
            { criterion_id: 'AC1', target: 'world', path: '', op: 'equals', expected: {}, actual: {}, passed: true },
          ]),
        };
      }
    }
    return null;
  });

  const initialModes = [
    CACHE_STATES.find(c => c.id === 'valid_token_a'),
    CACHE_STATES.find(c => c.id === 'absent'),
  ];
  const refreshStates = [
    {
      id: 'rotated_same_owner',
      authReply: () => ({ status: 0, stdout: `${TOKEN_A2}\n`, stderr: '' }),
      apiReply: () => ({ status: 0, stdout: 'octo 4242\n', stderr: '' }),
      token: TOKEN_A2,
      sha: SHA_A2,
      login: 'octo',
      user_id: '4242',
      refreshOk: true,
    },
    {
      id: 'switched_owner_mallory',
      authReply: () => ({ status: 0, stdout: `${TOKEN_B}\n`, stderr: '' }),
      apiReply: () => ({ status: 0, stdout: 'mallory 777\n', stderr: '' }),
      token: TOKEN_B,
      sha: SHA_B,
      login: 'mallory',
      user_id: '777',
      refreshOk: true,
    },
    {
      id: 'refresh_auth_blank',
      authReply: () => ({ status: 0, stdout: '   \n', stderr: '' }),
      apiReply: () => assert.fail('gh api user must not run when post-401 gh auth token is blank'),
      refreshOk: false,
    },
    {
      id: 'refresh_api_rate_limit',
      authReply: () => ({ status: 0, stdout: `${TOKEN_A2}\n`, stderr: '' }),
      apiReply: () => ({ status: 1, stdout: '', stderr: `HTTP 403: API rate limit exceeded (${TOKEN_A2})\n` }),
      refreshOk: false,
    },
  ];
  const runtimeSeqs = ['401_then_200', '401_always'];
  const boundaries = ['check_post', 'open_batch_read', 'call_read', 'request_read', 'try_attach', 'door_call', 'mcp_owner'];

  let worlds = 0;
  for (const initCache of initialModes) {
    for (const refresh of refreshStates) {
      for (const seq of runtimeSeqs) {
        for (const boundary of boundaries) {
          worlds += 1;
          const ctx = `Rule5[${initCache.id} × ${refresh.id} × ${seq} × ${boundary}]`;
          const exitCodeOn401 = ['open_batch_read', 'call_read', 'request_read'].includes(boundary) ? 3 : 5;
          fixture.resetState(initCache, false);
          fixture.observedUrls.length = 0;
          targetAttempts = 0;
          targetHeaders.length = 0;
          activeRule = { boundary, seq };

          let authCount = 0;
          let apiCount = 0;
          const ghLog = [];
          const batchesBefore = new Set(existsSync(join(fixture.setup.state, 'batches')) ? readdirSync(join(fixture.setup.state, 'batches')) : []);

          const made = portsFor(fixture.env, {
            stdin: Readable.from([]),
            gh: args => {
              ghLog.push(args);
              if (args[0] === 'auth') {
                authCount += 1;
                if (authCount === 1) return { status: 0, stdout: `${TOKEN_A}\n`, stderr: '' };
                return refresh.authReply();
              }
              apiCount += 1;
              if (initCache.id === 'absent' && apiCount === 1) {
                return { status: 0, stdout: 'octo 4242\n', stderr: '' };
              }
              return refresh.apiReply();
            },
          });

          const outcome = await invokeEntry(boundary, fixture, made.ports);
          activeRule = null;

          const stdout = made.ports.stdout.text;
          const stderr = made.ports.stderr.text;
          const outputs = [stdout, stderr, outcome.error?.message ?? ''];
          const cacheFile = join(fixture.setup.state, 'github-user.json');

          // Check .posted invariant on any newly created batch (Rule 5: never create duplicate <id>.posted markers).
          if (boundary === 'check_post' && existsSync(join(fixture.setup.state, 'batches'))) {
            const newBatches = readdirSync(join(fixture.setup.state, 'batches')).filter(name => !batchesBefore.has(name));
            for (const b of newBatches) {
              const posted = readdirSync(join(fixture.setup.state, 'batches', b)).filter(name => name.endsWith('.posted'));
              const expectedPosted = outcome.code === 0 ? 2 : 1; // 1 lint (+ 1 check when lint retry succeeded)
              assert.equal(posted.length, expectedPosted, `${ctx}: forbidden duplicate .posted marker (${JSON.stringify(posted)})`);
            }
          }

          // Never print rate-limit fallback warning after HTTP 401 (Rule 6).
          assert.doesNotMatch(stderr, /Warning: GitHub API rate limit reached/, `${ctx}: forbidden rate-limit fallback after HTTP 401`);

          if (initCache.id === 'absent') {
            // Cold sign-in already called gh api user fresh in this invocation -> 0 extra gh calls, 0 retries, cache removed!
            assert.equal(authCalls(ghLog).length, 1, `${ctx}: cold sign-in + 401 must make 0 extra gh auth token calls`);
            assert.equal(apiCalls(ghLog).length, 1, `${ctx}: cold sign-in + 401 must make 0 extra gh api user calls`);
            assert.equal(targetAttempts, 1, `${ctx}: cold sign-in + 401 must make 0 HTTP retries`);
            assert.equal(existsSync(cacheFile), false, `${ctx}: forbidden keeping 401-rejected cache file`);
            if (outcome.kind === 'code') {
              assert.equal(outcome.code, exitCodeOn401, `${ctx}: cold 401 exit code`);
              assert.ok(stderr.includes(AUTH_DIAGNOSTIC), `${ctx}: cold 401 AUTH_TEXT on stderr (${stderr})`);
            } else {
              assert.equal(outcome.kind, 'rejected', `${ctx}: cold 401 rejects`);
              if (outcome.door) assert.equal(outcome.error.exitCode, 125, `${ctx}: cold 401 door exitCode 125`);
              assert.ok(outcome.error.message.includes('HTTP 401') || outcome.error.message.includes('Run gh auth login'), `${ctx}: cold 401 error`);
            }
            assertRule1Invariants({ stateDir: fixture.setup.state, repoDir: fixture.setup.repo, outputs, ghLog, urls: fixture.observedUrls }, ctx);
            continue;
          }

          // Warm cached sign-in hit HTTP 401 on attempt 1:
          assert.equal(targetHeaders[0], `Bearer ${TOKEN_A}`, `${ctx}: initial request used cached session token`);
          assert.equal(authCalls(ghLog).length, 2, `${ctx}: warm 401 performs exactly 1 fresh gh auth token lookup`);

          if (!refresh.refreshOk) {
            const expectedApiCalls = refresh.id === 'refresh_auth_blank' ? 0 : 1;
            assert.equal(apiCalls(ghLog).length, expectedApiCalls, `${ctx}: failed post-401 refresh gh api user count`);
            assert.equal(targetAttempts, 1, `${ctx}: failed post-401 refresh must not retry HTTP`);
            assert.equal(existsSync(cacheFile), false, `${ctx}: failed post-401 refresh leaves github-user.json removed`);
            if (outcome.kind === 'code') {
              assert.equal(outcome.code, exitCodeOn401, `${ctx}: failed post-401 refresh exit code`);
              assert.ok(stderr.includes(AUTH_DIAGNOSTIC), `${ctx}: failed post-401 refresh AUTH_TEXT on stderr (${stderr})`);
            } else {
              assert.equal(outcome.kind, 'rejected', `${ctx}: failed post-401 refresh rejects`);
              if (outcome.door) assert.equal(outcome.error.exitCode, 125, `${ctx}: door exitCode 125`);
            }
            assertRule1Invariants({ stateDir: fixture.setup.state, repoDir: fixture.setup.repo, outputs, ghLog, urls: fixture.observedUrls }, ctx);
            continue;
          }

          // Post-401 refresh succeeded:
          assert.equal(apiCalls(ghLog).length, 1, `${ctx}: warm 401 calls gh api user once during refresh`);
          const hasSavedOwner = !['check_post', 'request_read'].includes(boundary);

          if (hasSavedOwner && refresh.login !== 'octo') {
            // Forbidden: skipping saved-owner verification after 401 refresh!
            assert.equal(targetAttempts, 1, `${ctx}: owner mismatch after 401 refresh must stop with 0 HTTP retries`);
            if (outcome.kind === 'code') {
              assert.equal(outcome.code, 5, `${ctx}: owner mismatch after 401 exits 5`);
              assert.ok(stderr.includes('octo'), `${ctx}: owner mismatch names octo`);
            } else {
              assert.equal(outcome.kind, 'rejected', `${ctx}: owner mismatch after 401 rejects`);
              if (outcome.door) assert.equal(outcome.error.exitCode, 125, `${ctx}: door exitCode 125`);
              assert.ok(outcome.error.message.includes('octo'), `${ctx}: owner mismatch error names octo`);
            }
            assertRule1Invariants({
              stateDir: fixture.setup.state,
              repoDir: fixture.setup.repo,
              outputs,
              ghLog,
              urls: fixture.observedUrls,
              expectValidCache: { login: refresh.login, user_id: refresh.user_id, token_sha256: refresh.sha },
            }, ctx);
            continue;
          }

          // Owner matches (or check_post / request_read with no pre-HTTP owner lock): retries rejected HTTP request exactly once!
          assert.equal(targetAttempts, 2, `${ctx}: retries rejected HTTP request once (no loop)`);
          assert.equal(targetHeaders[1], `Bearer ${refresh.token}`, `${ctx}: retry uses refreshed token`);

          if (seq === '401_then_200') {
            if (outcome.kind === 'code') {
              assert.equal(outcome.code, 0, `${ctx}: single retry 200 succeeds (${stderr})`);
            } else {
              assert.equal(outcome.kind, 'resolved', `${ctx}: single retry 200 resolves`);
            }
            assertRule1Invariants({
              stateDir: fixture.setup.state,
              repoDir: fixture.setup.repo,
              outputs,
              ghLog,
              urls: fixture.observedUrls,
              expectValidCache: { login: refresh.login, user_id: refresh.user_id, token_sha256: refresh.sha },
            }, ctx);
          } else {
            // seq === '401_always': single retry also 401 -> stops with 0 further retries and deletes github-user.json!
            assert.equal(existsSync(cacheFile), false, `${ctx}: repeated 401 must remove github-user.json`);
            if (outcome.kind === 'code') {
              assert.equal(outcome.code, exitCodeOn401, `${ctx}: repeated 401 exit code`);
              assert.ok(stderr.includes(AUTH_DIAGNOSTIC), `${ctx}: repeated 401 AUTH_TEXT on stderr (${stderr})`);
            } else {
              assert.equal(outcome.kind, 'rejected', `${ctx}: repeated 401 rejects`);
              if (outcome.door) assert.equal(outcome.error.exitCode, 125, `${ctx}: door exitCode 125`);
              assert.ok(outcome.error.message.includes('HTTP 401') || outcome.error.message.includes('Run gh auth login'), `${ctx}: repeated 401 error`);
            }
            assertRule1Invariants({ stateDir: fixture.setup.state, repoDir: fixture.setup.repo, outputs, ghLog, urls: fixture.observedUrls }, ctx);
          }
        }
      }
    }
  }
  assert.equal(worlds, 112);
});

test('formal Rule 6 refresh rate-limit boundary: 4 on-disk cache states x 3 gh api user failures x 6 caller modes (72 worlds)', { timeout: 120_000 }, async t => {
  const fixture = await seedFixture(t);

  const incompleteCachedAtTokenA = {
    id: 'incomplete_cached_at_token_a',
    validFor: null,
    write(stateDir) {
      writeFileSync(join(stateDir, 'github-user.json'), JSON.stringify({
        login: 'octo', user_id: '4242', cached_at: '', token_sha256: SHA_A,
      }), { mode: 0o600 });
    },
  };

  const cacheModes = [
    incompleteCachedAtTokenA, // matching token_sha256 with incomplete cached_at triggers real refresh
    CACHE_STATES.find(c => c.id === 'absent'),
    CACHE_STATES.find(c => c.id === 'valid_token_b'), // switched token (active token is TOKEN_A)
    CACHE_STATES.find(c => c.id === 'corrupt_json'),
  ];
  const failureModes = [
    {
      id: 'rate_limit_403',
      isRateLimit: true,
      reply: () => ({ status: 1, stdout: '', stderr: `HTTP 403: API rate limit exceeded (${TOKEN_A})\n` }),
    },
    {
      id: 'rate_limit_secondary',
      isRateLimit: true,
      reply: () => ({ status: 1, stdout: '', stderr: 'You have exceeded a secondary rate limit (HTTP 403)\n' }),
    },
    {
      id: 'non_rate_limit_500',
      isRateLimit: false,
      reply: () => ({ status: 1, stdout: '', stderr: `HTTP 500: Internal Server Error (${TOKEN_A})\n` }),
    },
  ];
  const callerModes = [
    'check_saved_read', // local terminal saved-batch --read
    'open_batch_read',  // open saved-batch --read requiring remote GET
    'check_lint',       // remote lint
    'try_attach',       // remote Try attach
    'door_call',        // remote CLI door call
    'mcp_owner',        // remote MCP owner read
  ];

  let worlds = 0;
  for (const cacheState of cacheModes) {
    for (const failure of failureModes) {
      for (const callerMode of callerModes) {
        worlds += 1;
        const ctx = `Rule6[${cacheState.id} × ${failure.id} × ${callerMode}]`;
        fixture.resetState(cacheState, false);
        fixture.observedUrls.length = 0;
        const ghLog = [];
        const beforeHttp = fixture.httpTotal();

        const made = portsFor(fixture.env, {
          stdin: Readable.from([]),
          gh: args => {
            ghLog.push(args);
            return args[0] === 'auth' ? { status: 0, stdout: `${TOKEN_A}\n`, stderr: '' } : failure.reply();
          },
        });

        const outcome = await invokeEntry(callerMode, fixture, made.ports);
        const httpDelta = fixture.httpTotal() - beforeHttp;
        const stdout = made.ports.stdout.text;
        const stderr = made.ports.stderr.text;
        const outputs = [stdout, stderr, outcome.error?.message ?? ''];

        assert.equal(authCalls(ghLog).length, 1, `${ctx}: gh auth token called once`);
        assert.equal(apiCalls(ghLog).length, 1, `${ctx}: refresh calls gh api user once`);
        assert.equal(httpDelta, 0, `${ctx}: refresh failure never makes remote runtime HTTP calls`);

        const eligibleFallback =
          cacheState.id === 'incomplete_cached_at_token_a' &&
          failure.isRateLimit &&
          callerMode === 'check_saved_read';

        if (eligibleFallback) {
          assert.equal(outcome.code, 0, `${ctx}: matching-token local saved-batch --read falls back under rate limit`);
          assert.equal(
            (stderr.match(/Warning: GitHub API rate limit reached; using saved GitHub login octo for this token\./g) ?? []).length,
            1,
            `${ctx}: exact stderr rate-limit warning printed once`,
          );
          const cacheFile = join(fixture.setup.state, 'github-user.json');
          assert.equal(modeBits(cacheFile), 0o600, `${ctx}: github-user.json remains 0600`);
          assert.deepEqual(JSON.parse(readFileSync(cacheFile, 'utf8')), {
            login: 'octo', user_id: '4242', cached_at: '', token_sha256: SHA_A,
          }, `${ctx}: incomplete cached_at record preserved without unverified timestamp`);
          assertRule1Invariants({
            stateDir: fixture.setup.state,
            repoDir: fixture.setup.repo,
            outputs,
            ghLog,
            urls: fixture.observedUrls,
            expectValidCache: null,
          }, ctx);
        } else {
          assert.doesNotMatch(stderr, /Warning: GitHub API rate limit reached/, `${ctx}: forbidden rate-limit fallback outside local saved-batch --read`);
          if (outcome.kind === 'code') {
            assert.equal(outcome.code, 5, `${ctx}: non-eligible refresh failure exits 5`);
            assert.ok(stderr.includes('pdd could not read your GitHub login'), `${ctx}: stderr names login failure`);
          } else {
            assert.equal(outcome.kind, 'rejected', `${ctx}: non-eligible refresh failure rejects`);
            if (outcome.door) assert.equal(outcome.error.exitCode, 125, `${ctx}: door exitCode 125`);
            assert.ok(outcome.error.message.includes('pdd could not read your GitHub login'), `${ctx}: error names login failure`);
          }
          const cacheFile = join(fixture.setup.state, 'github-user.json');
          if (cacheState.id === 'absent') {
            assert.equal(existsSync(cacheFile), false, `${ctx}: cold failure writes no cache`);
          }
          const preserved = cacheState.validFor
            ? { login: cacheState.validFor.login, user_id: cacheState.validFor.user_id, token_sha256: cacheState.validFor.sha }
            : null;
          assertRule1Invariants({
            stateDir: fixture.setup.state,
            repoDir: fixture.setup.repo,
            outputs,
            ghLog,
            urls: fixture.observedUrls,
            expectValidCache: preserved,
          }, ctx);
        }
      }
    }
  }
  assert.equal(worlds, 72);
});
