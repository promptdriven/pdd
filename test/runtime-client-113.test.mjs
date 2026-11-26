import './helpers/test-home.mjs';
import './helpers/test-net-guard.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { request as httpRequest } from 'node:http';
import { delimiter, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import * as seam from '../src/runtime-seam.mjs';
import { CommandInputError, parseArgv } from '../src/argument-parser.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { PLACE, TOKEN, fakeRuntime, harbor, portsFor } from './helpers/runtime-fake.mjs';

const repoRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const RUNTIME_CLIENT_PKG = seam.version().package;

function compareExactSemver(a, b) {
  const pa = a.split('.').map(Number);
  const pb = b.split('.').map(Number);
  for (let i = 0; i < 3; i++) {
    if (pa[i] !== pb[i]) return pa[i] - pb[i];
  }
  return 0;
}

function fakeGhBin(sandbox) {
  const binDir = join(sandbox, 'fake-gh-bin');
  mkdirSync(binDir, { recursive: true });
  const ghPath = join(binDir, 'gh');
  writeFileSync(
    ghPath,
    `#!/bin/sh\nif [ "$1" = "auth" ]; then printf '%s\\n' ${JSON.stringify(TOKEN)}; exit 0; fi\nprintf 'octo 4242\\n'\n`,
  );
  chmodSync(ghPath, 0o755);
  return `${binDir}${delimiter}${process.env.PATH ?? ''}`;
}

function captureStream() {
  return {
    text: '',
    write(chunk) {
      this.text += String(chunk);
      return true;
    },
  };
}

function sendLoopbackHttp({ port, method = 'GET', path = '/', headers = {} }) {
  return new Promise((resolvePromise, reject) => {
    const req = httpRequest({ host: '127.0.0.1', port, method, path, headers }, res => {
      let body = '';
      res.setEncoding('utf8');
      res.on('data', chunk => { body += chunk; });
      res.on('end', () => resolvePromise({ status: res.statusCode, headers: res.headers, body }));
    });
    req.on('error', reject);
    req.end();
  });
}

const SHOUT_PROMPT = [
  '# shout',
  '',
  'A command-line program. It takes one argument and prints it in upper case, followed by a newline, and exits 0.',
  '',
  'Input rules:',
  '',
  '- Leading and trailing spaces are removed.',
  '- Characters that are not letters are removed before printing.',
  '- An empty result prints an empty line.',
  '',
].join('\n');

const SHOUT_STORY = [
  '# Shout',
  '',
  '## Acceptance criteria',
  '',
  '1. Upper-cases a word.',
  '2. Keeps digits in a code like a1.',
  '',
].join('\n');

const SHOUT_TEST = `${JSON.stringify({
  schema_version: 'prompt-runtime.program-scenario.v1',
  story_path: 'user_stories/shout.md',
  criteria: [
    { id: 'AC1', text: 'Upper-cases a word.' },
    { id: 'AC2', text: 'Keeps digits in a code like a1.' },
  ],
  initial_world: {},
  steps: [
    {
      step_id: 'word',
      entry_path: 'prompts/shout.prompt.md',
      operation: 'cli',
      input: { argv: ['abc'] },
      checks: [
        { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'ABC\n' },
      ],
    },
    {
      step_id: 'code',
      entry_path: 'prompts/shout.prompt.md',
      operation: 'cli',
      input: { argv: ['a1'] },
      checks: [
        { criterion_id: 'AC2', target: 'result', path: '/stdout', op: 'equals', value: 'A1\n' },
      ],
    },
  ],
}, null, 2)}\n`;

test('#3716: runtime-client >= 1.1.3 pins exact semver, parses/forwards --serve options, and enforces loopback HTTP origin/proxy/token gates', async t => {
  const pkg = JSON.parse(readFileSync(join(repoRoot, 'package.json'), 'utf8'));
  const lockfile = JSON.parse(readFileSync(join(repoRoot, 'package-lock.json'), 'utf8'));
  const pinned = pkg.dependencies[RUNTIME_CLIENT_PKG];
  const locked = lockfile.packages[`node_modules/${RUNTIME_CLIENT_PKG}`];
  assert.match(pinned, /^\d+\.\d+\.\d+$/, `expected exact semver pin, got ${JSON.stringify(pinned)}`);
  assert.ok(compareExactSemver(pinned, '1.1.3') >= 0, `expected pinned version >= 1.1.3, got ${pinned}`);
  assert.equal(lockfile.packages[''].dependencies[RUNTIME_CLIENT_PKG], pinned);
  assert.equal(locked.version, pinned);

  // 1. Parse --serve tunnel/auth flags across Story, ., trailing .prompt.md, and prefix .prompt.md forms.
  const parsedStory = parseArgv([
    'place-order', '--serve', '8080',
    '--allow-origins', 'https://chatgpt.com,https://chat.openai.com',
    '--trust-proxy',
    '--serve-token', 'dev-secret',
    '--serve-header', 'X-Dev-Gate',
  ], { resolveTarget: w => (w === 'place-order' ? { kind: 'story', operand: w } : null) });
  assert.equal(parsedStory.commandId, 'try');
  assert.equal(parsedStory.options['--serve'], '8080');
  assert.equal(parsedStory.options['--allow-origins'], 'https://chatgpt.com,https://chat.openai.com');
  assert.equal(parsedStory.options['--trust-proxy'], true);
  assert.equal(parsedStory.options['--serve-token'], 'dev-secret');
  assert.equal(parsedStory.options['--serve-header'], 'X-Dev-Gate');

  const parsedTrailingPrompt = parseArgv([
    'prompts/app.prompt.md', '--serve',
    '--allow-origins', 'https://chatgpt.com',
    '--trust-proxy',
    '--serve-token', 'tok-123',
    '--serve-header', 'X-PDD-Gate',
  ]);
  assert.equal(parsedTrailingPrompt.commandId, 'try');
  assert.deepEqual(parsedTrailingPrompt.operands, ['prompts/app.prompt.md']);
  assert.equal(parsedTrailingPrompt.options['--serve'], '8080');
  assert.equal(parsedTrailingPrompt.options['--allow-origins'], 'https://chatgpt.com');
  assert.equal(parsedTrailingPrompt.options['--trust-proxy'], true);
  assert.equal(parsedTrailingPrompt.options['--serve-token'], 'tok-123');
  assert.equal(parsedTrailingPrompt.options['--serve-header'], 'X-PDD-Gate');

  const parsedPrefixPrompt = parseArgv([
    '--allow-origins', 'https://chatgpt.com',
    '--trust-proxy',
    '--serve-token', 'tok-123',
    '--serve-header', 'X-PDD-Gate',
    '--serve', 'prompts/app.prompt.md',
  ]);
  assert.equal(parsedPrefixPrompt.commandId, 'try');
  assert.deepEqual(parsedPrefixPrompt.operands, ['prompts/app.prompt.md']);
  assert.equal(parsedPrefixPrompt.options['--serve'], '8080');
  assert.equal(parsedPrefixPrompt.options['--allow-origins'], 'https://chatgpt.com');
  assert.equal(parsedPrefixPrompt.options['--trust-proxy'], true);
  assert.equal(parsedPrefixPrompt.options['--serve-token'], 'tok-123');
  assert.equal(parsedPrefixPrompt.options['--serve-header'], 'X-PDD-Gate');

  const parsedDot = parseArgv(['.', '--serve', '--trust-proxy']);
  assert.equal(parsedDot.commandId, 'try');
  assert.equal(parsedDot.options['--trust-proxy'], true);

  for (const invalid of [
    ['.', '--serve', '--trust-proxy=true'],
    ['.', '--serve', '--allow-origins', '   '],
    ['.', '--serve', '--serve-token', '   '],
    ['.', '--serve', '--serve-header', '   '],
  ]) {
    assert.throws(() => parseArgv(invalid), CommandInputError, invalid.join(' '));
  }

  // 2. seam.simulate() forwards allowOrigins, trustProxy, serveToken, and serveHeader identically to runtime-client 1.1.3.
  const setup = harbor(t);
  let capturedTryInput = null;
  const simPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state },
    { runTry: async input => { capturedTryInput = input; return 0; } },
  );
  assert.equal(
    await seam.simulate({
      cwd: setup.repo,
      words: ['place-order'],
      mode: 'serve',
      port: 8081,
      allowOrigins: ['https://chatgpt.com', 'https://chat.openai.com'],
      trustProxy: true,
      serveToken: 'sim-gate-token-unique',
      serveHeader: 'X-Sim-Gate',
    }, simPorts.ports),
    0,
  );
  assert.deepEqual(capturedTryInput.options, {
    '--serve': 8081,
    '--allow-origins': 'https://chatgpt.com,https://chat.openai.com',
    '--trust-proxy': true,
    '--serve-token': 'sim-gate-token-unique',
    '--serve-header': 'X-Sim-Gate',
  });

  // 3. Invalid serve-extra combinations fail closed with exit 2 (and do not inject --tab in classifyPlainProseScreenTab).
  let bareExtraInput = null;
  const bareExtraPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state },
    { runTry: async input => { bareExtraInput = input; return 2; } },
  );
  await seam.runTry({ cwd: setup.repo, words: ['place-order'], options: { '--allow-origins': 'https://chatgpt.com' } }, bareExtraPorts.ports);
  assert.equal(bareExtraInput.options['--tab'], undefined);

  const noServePorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.runTry({ cwd: setup.repo, words: ['place-order'], options: { '--allow-origins': 'https://chatgpt.com' } }, noServePorts.ports),
    2,
  );
  assert.match(noServePorts.ports.stderr.text, /require --serve/);

  const headerWithoutTokenPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.runTry({
      cwd: setup.repo,
      words: ['place-order'],
      options: { '--serve': '8080', '--serve-header': 'X-Dev-Gate' },
    }, headerWithoutTokenPorts.ports),
    2,
  );
  assert.match(headerWithoutTokenPorts.ports.stderr.text, /--serve-header requires --serve-token/);

  const stopPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.runTry({ cwd: setup.repo, words: [PLACE], options: { '--stop': true, '--trust-proxy': true } }, stopPorts.ports),
    2,
  );

  // 4. Real loopback HTTP enforcement via seam.openServe: CORS origin check, forwarded host/proto, and custom token gate.
  const uniqueGateToken = 'pdd-serve-113-secret-token-9f2a';
  const sessionId = '11111111-1111-4111-8111-111111111111';
  const serveFake = await fakeRuntime(t, entry => {
    if (entry.method === 'POST' && entry.url === `/v1/try/${sessionId}/call`) {
      const callId = entry.json?.requestId ?? '22222222-2222-4222-8222-222222222222';
      return {
        status: 200,
        json: {
          id: callId,
          requestId: callId,
          command: 'call',
          session_id: sessionId,
          state: 'passed',
          result: {
            program_result: { status: 200, headers: { 'content-type': 'text/plain' }, body: 'pong' },
          },
          usage: { calls: 1, cap: 40, remaining: 39 },
        },
      };
    }
    throw new Error(`unexpected serveFake call: ${entry.method} ${entry.url}`);
  });
  const serveOut = captureStream();
  const serveErr = captureStream();
  const servePorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: serveFake.origin },
    {
      stdout: serveOut,
      stderr: serveErr,
      serve: async server => {
        const port = server.address().port;

        // Disallowed origin fails closed with 403 and never leaks the serve token.
        const badOrigin = await sendLoopbackHttp({
          port,
          method: 'GET',
          path: '/api/ping',
          headers: {
            host: `127.0.0.1:${port}`,
            origin: 'https://evil.example',
            'x-dev-gate': uniqueGateToken,
          },
        });
        assert.equal(badOrigin.status, 403, badOrigin.body);
        assert.equal(badOrigin.body.includes(uniqueGateToken), false);

        // Allowed origin without auth header fails closed with 401 and keeps CORS header.
        const missingAuth = await sendLoopbackHttp({
          port,
          method: 'GET',
          path: '/api/ping',
          headers: {
            host: 'demo.trycloudflare.com',
            'x-forwarded-host': 'demo.trycloudflare.com',
            'x-forwarded-proto': 'https',
            origin: 'https://chatgpt.com',
          },
        });
        assert.equal(missingAuth.status, 401, missingAuth.body);
        assert.equal(missingAuth.headers['access-control-allow-origin'], 'https://chatgpt.com');
        assert.equal(missingAuth.body.includes(uniqueGateToken), false);

        // Allowed origin + forwarded tunnel host + valid custom gate header succeeds with 200.
        const okRes = await sendLoopbackHttp({
          port,
          method: 'GET',
          path: '/api/ping',
          headers: {
            host: 'demo.trycloudflare.com',
            'x-forwarded-host': 'demo.trycloudflare.com',
            'x-forwarded-proto': 'https',
            origin: 'https://chatgpt.com',
            'x-dev-gate': uniqueGateToken,
          },
        });
        assert.equal(okRes.status, 200, okRes.body);
        assert.equal(okRes.headers['access-control-allow-origin'], 'https://chatgpt.com');
        assert.equal(okRes.body, 'pong');
      },
    },
  );
  const serveContext = {
    root: setup.repo,
    cwd: setup.repo,
    origin: serveFake.origin,
    identity: { login: 'octo', id: '4242' },
    ports: servePorts.ports,
    secrets: [uniqueGateToken],
    runtime: {
      send: async url => {
        if (url === `/v1/try/${sessionId}/model`) {
          return {
            status: 200,
            json: {
              entries: [
                {
                  entry_path: PLACE,
                  operation: 'ping',
                  http: { method: 'GET', path: '/api/ping' },
                },
              ],
              calls: { cap: 40, remaining: 40 },
            },
          };
        }
        throw new Error(`unexpected runtime URL in openServe test: ${url}`);
      },
    },
  };
  const openServeCode = await seam.openServe(
    serveContext,
    { path: 'tests/place-order.json', story: 'place-order' },
    sessionId,
    {
      '--serve': 0,
      '--allow-origins': 'https://chatgpt.com',
      '--trust-proxy': true,
      '--serve-token': uniqueGateToken,
      '--serve-header': 'X-Dev-Gate',
    },
  );
  assert.equal(openServeCode, 0, serveErr.text);
  assert.equal(serveOut.text.includes(uniqueGateToken), false, 'serve stdout must not leak serve token');
  assert.equal(serveErr.text.includes(uniqueGateToken), false, 'serve stderr must not leak serve token');
});

test('#2556: pdd lint --remote fails closed with exact exit codes in both JSON and text modes on refused, incomplete, or error-bearing lint', async t => {
  const cases = [
    {
      label: 'refused verdict with lint-incomplete',
      expectedCode: 4,
      expectedLintState: 'refused',
      textPattern: /Lint refused/i,
      checkText: true,
      mutate: answer => {
        answer.result.report.verdict = 'refused';
        answer.result.report.refusal = { code: 'lint-incomplete', message: 'Program lint did not finish.' };
      },
    },
    {
      label: 'problems_complete false on passing answer',
      expectedCode: 5,
      expectedLintState: 'not run',
      textPattern: /incomplete/i,
      checkText: true,
      mutate: answer => {
        answer.result.problems_complete = false;
      },
    },
    {
      label: 'contradictory capabilities_complete false inside report.lint',
      expectedCode: 5,
      expectedLintState: 'not run',
      checkText: false,
      mutate: answer => {
        answer.result.capabilities_complete = true;
        answer.result.report.lint.capabilities_complete = false;
      },
    },
    {
      label: 'severity error problem on passing lint answer',
      expectedCode: 4,
      expectedLintState: 'refused',
      checkText: false,
      mutate: answer => {
        answer.result.problems = [
          { code: 'invalid-digest', file: PLACE, severity: 'error', message: 'prose_sha256 is blank.' },
        ];
      },
    },
  ];

  for (const tc of cases) {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (entry, f) => {
      if (entry.method === 'POST' && entry.command === 'lint') {
        const answer = f.lint(entry.request.requestId);
        tc.mutate(answer);
        return { status: 200, json: answer };
      }
      return f.normal(entry);
    });
    const env = {
      ...process.env,
      HOME: setup.home,
      PDD_STATE_DIR: setup.state,
      PDD_RUNTIME_URL: fake.origin,
      PATH: fakeGhBin(setup.sandbox),
    };

    // JSON mode asserts exact exit code and structured fields.
    const stdout = captureStream();
    const stderr = captureStream();
    const code = await runPdd(['lint', '--remote', 'place-order', '--json'], { cwd: setup.repo, env, stdout, stderr });
    assert.equal(code, tc.expectedCode, `"${tc.label}" JSON exit code\nstdout:\n${stdout.text}\nstderr:\n${stderr.text}`);
    const parsed = JSON.parse(stdout.text);
    assert.equal(parsed.exit_code, tc.expectedCode, tc.label);
    assert.equal(parsed.lint_state, tc.expectedLintState, tc.label);
    assert.notEqual(parsed.rows?.[0]?.state, 'passed', tc.label);
    assert.match(parsed.summary_line, /0 of 1 tests pass/, tc.label);

    // Text mode (distinct CLI branch) asserts exact exit code and non-passing summary.
    if (tc.checkText) {
      const textOut = captureStream();
      const textErr = captureStream();
      const textCode = await runPdd(['lint', '--remote', 'place-order'], { cwd: setup.repo, env, stdout: textOut, stderr: textErr });
      assert.equal(textCode, tc.expectedCode, `"${tc.label}" text exit code\nstdout:\n${textOut.text}\nstderr:\n${textErr.text}`);
      const combined = `${textOut.text}\n${textErr.text}`;
      assert.match(combined, tc.textPattern, `"${tc.label}" text output:\n${combined}`);
      assert.match(combined, /0 of 1 tests pass/, `"${tc.label}" text summary:\n${combined}`);
    }
  }

  // Control: healthy complete passing remote lint still exits 0 and marks row passed.
  const okSetup = harbor(t);
  const okFake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const okOut = captureStream();
  const okErr = captureStream();
  const okCode = await runPdd(['lint', '--remote', 'place-order', '--json'], {
    cwd: okSetup.repo,
    env: {
      ...process.env,
      HOME: okSetup.home,
      PDD_STATE_DIR: okSetup.state,
      PDD_RUNTIME_URL: okFake.origin,
      PATH: fakeGhBin(okSetup.sandbox),
    },
    stdout: okOut,
    stderr: okErr,
  });
  assert.equal(okCode, 0, okErr.text);
  const okJson = JSON.parse(okOut.text);
  assert.equal(okJson.exit_code, 0);
  assert.equal(okJson.rows?.[0]?.state, 'passed');
});

test('#3665: v1 prompt clause citations work end-to-end through seam, --files --json, live --details, --json, --read, and legacy servers', async t => {
  // 1. Seam exports the prompt-clauses helpers and slice loader.
  assert.equal(typeof seam.runtimePromptClausesSlice, 'function');
  assert.equal(typeof seam.extractPromptClauses, 'function');
  assert.equal(typeof seam.buildClauseTable, 'function');
  assert.equal(typeof seam.indexClauseTable, 'function');
  assert.equal(typeof seam.validateStepClauses, 'function');

  const setup = harbor(t, repo => {
    writeFileSync(join(repo, 'prompts/shout.prompt.md'), SHOUT_PROMPT);
    writeFileSync(join(repo, 'user_stories/shout.md'), SHOUT_STORY);
    writeFileSync(join(repo, 'tests/shout.json'), SHOUT_TEST);
  });

  // 2. pdd test --files shout --json lists deterministic clauses with exact line numbers.
  const filesOut = captureStream();
  const filesErr = captureStream();
  const filesCode = await runPdd(['test', '--files', 'shout', '--json'], {
    cwd: setup.repo,
    env: { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state },
    stdout: filesOut,
    stderr: filesErr,
  });
  assert.equal(filesCode, 0, filesErr.text);
  const filesJson = JSON.parse(filesOut.text);
  assert.ok(Array.isArray(filesJson.clauses), 'expected clauses array in pdd test --files --json');
  const offendingClause = filesJson.clauses.find(
    c => c.path === 'prompts/shout.prompt.md' && c.line === 8 && c.text.includes('Characters that are not letters'),
  );
  assert.ok(offendingClause, `expected clause at prompts/shout.prompt.md:8, got ${JSON.stringify(filesJson.clauses)}`);
  assert.match(offendingClause.id, /^cl-sha256-[0-9a-f]{16}$/);

  // Editing an unrelated rule leaves offendingClause.id stable.
  const editedClauses = seam.extractPromptClauses(
    'prompts/shout.prompt.md',
    SHOUT_PROMPT.replace('Leading and trailing spaces are removed.', 'Leading spaces are trimmed.'),
  );
  const sameClauseAfterUnrelatedEdit = editedClauses.find(c => c.line === 8);
  assert.equal(sameClauseAfterUnrelatedEdit?.id, offendingClause.id);

  // 3. Server advertising clause-citations-v1 receives clause_table and failed check displays validated citation + unknown-ID warning.
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') {
      return {
        status: 200,
        json: f.lint(entry.request.requestId, [{ path: 'prompts/shout.prompt.md', state: 'draft', admission_state: 'draft', interface: { calls: [] } }]),
      };
    }
    if (entry.method === 'POST' && entry.command === 'check') {
      const answer = f.check(entry.request.requestId, 'failed', [
        {
          step_id: 'code',
          criterion_id: 'AC2',
          passed: false,
          target: 'result',
          path: '/stdout',
          op: 'equals',
          expected: 'A1\n',
          actual: 'A\n',
          detail: 'Expected A1\\n, got A\\n.',
        },
      ]);
      answer.result.report.samples = [
        {
          sample: 1,
          steps: [
            {
              step_id: 'word',
              checks: [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', expected: 'ABC\n', actual: 'ABC\n', passed: true }],
            },
            {
              step_id: 'code',
              clauses: [offendingClause.id, 'cl-sha256-0000000000000000'],
              checks: [
                {
                  criterion_id: 'AC2',
                  target: 'result',
                  path: '/stdout',
                  op: 'equals',
                  expected: 'A1\n',
                  actual: 'A\n',
                  passed: false,
                  detail: 'Expected A1\\n, got A\\n.',
                },
              ],
            },
          ],
        },
      ];
      return { status: 200, json: answer };
    }
    return f.normal(entry);
  });
  fake.capacity = () => ({ status: 200, json: { features: ['lazy-interfaces', 'clause-citations-v1'] } });

  const env = {
    ...process.env,
    HOME: setup.home,
    PDD_STATE_DIR: setup.state,
    PDD_RUNTIME_URL: fake.origin,
    PATH: fakeGhBin(setup.sandbox),
  };

  // JSON check run verifies clause_table upload, failed_checks[].clauses, and unknown-ID warning.
  const jsonOut = captureStream();
  const jsonErr = captureStream();
  const jsonCode = await runPdd(['test', 'shout', '--json'], { cwd: setup.repo, env, stdout: jsonOut, stderr: jsonErr });
  assert.equal(jsonCode, 1, jsonErr.text);
  const checkPost = fake.posts.find(p => p.command === 'check');
  assert.ok(Array.isArray(checkPost?.request?.clause_table), 'expected POST /v1/check to include clause_table when server advertises clause-citations-v1');
  assert.ok(checkPost.request.clause_table.some(c => c.id === offendingClause.id));

  const jsonPayload = JSON.parse(jsonOut.text);
  const row = jsonPayload.rows[0];
  assert.ok(Array.isArray(row.failed_checks) && row.failed_checks.length === 1);
  assert.deepEqual(row.failed_checks[0].clauses, [offendingClause]);
  assert.ok(
    (jsonPayload.warnings ?? []).some(w => /dropped 1 unknown clause citation/i.test(String(w))),
    `expected unknown clause citation warning in top-level warnings, got ${JSON.stringify(jsonPayload.warnings)}`,
  );

  // Live text-mode `pdd test shout --fresh --details` prints both the cited prompt line and dropped-unknown-citation warning.
  const liveDetailsOut = captureStream();
  const liveDetailsErr = captureStream();
  const liveDetailsCode = await runPdd(['test', 'shout', '--fresh', '--details'], { cwd: setup.repo, env, stdout: liveDetailsOut, stderr: liveDetailsErr });
  assert.equal(liveDetailsCode, 1, liveDetailsErr.text);
  assert.match(liveDetailsOut.text, /Prompt \(cited by the interpreter\): prompts\/shout\.prompt\.md:8\s+Characters that are not letters are removed before printing\./);
  assert.match(`${liveDetailsOut.text}\n${liveDetailsErr.text}`, /dropped 1 unknown clause citation/i);
  assert.doesNotMatch(liveDetailsOut.text, /cl-sha256-0000000000000000/);

  // Offline --read <batch> --details reproduces cited prompt line from saved batch.json.
  const readOut = captureStream();
  const readErr = captureStream();
  const readCode = await runPdd(['test', '--read', jsonPayload.batch, '--details'], { cwd: setup.repo, env, stdout: readOut, stderr: readErr });
  assert.equal(readCode, 1, readErr.text);
  assert.match(readOut.text, /Prompt \(cited by the interpreter\): prompts\/shout\.prompt\.md:8\s+Characters that are not letters are removed before printing\./);
  assert.doesNotMatch(readOut.text, /cl-sha256-0000000000000000/);

  // 4. Legacy server (no clause-citations-v1 capability) omits clause_table and prints no citation lines or unknown warnings.
  const legacyFake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') {
      return {
        status: 200,
        json: f.lint(entry.request.requestId, [{ path: 'prompts/shout.prompt.md', state: 'draft', admission_state: 'draft', interface: { calls: [] } }]),
      };
    }
    if (entry.method === 'POST' && entry.command === 'check') {
      return {
        status: 200,
        json: f.check(entry.request.requestId, 'failed', [
          {
            step_id: 'code',
            criterion_id: 'AC2',
            passed: false,
            target: 'result',
            path: '/stdout',
            op: 'equals',
            expected: 'A1\n',
            actual: 'A\n',
          },
        ]),
      };
    }
    return f.normal(entry);
  });
  legacyFake.capacity = () => ({ status: 200, json: { features: ['lazy-interfaces'] } });

  const legacyOut = captureStream();
  const legacyErr = captureStream();
  const legacyCode = await runPdd(['test', 'shout', '--fresh', '--details'], {
    cwd: setup.repo,
    env: { ...env, PDD_RUNTIME_URL: legacyFake.origin },
    stdout: legacyOut,
    stderr: legacyErr,
  });
  assert.equal(legacyCode, 1, legacyErr.text);
  const legacyPost = legacyFake.posts.find(p => p.command === 'check');
  assert.equal(legacyPost?.request?.clause_table, undefined, 'legacy server without clause-citations-v1 must not receive clause_table');
  assert.doesNotMatch(legacyOut.text, /Prompt \(cited by the interpreter\):/);
});
