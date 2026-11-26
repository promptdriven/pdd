import './helpers/test-home.mjs';
import './helpers/test-net-guard.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
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

test('#3716: runtime-client is pinned to exact semver >= 1.1.3 and --serve tunnel/auth options parse and validate cleanly', async t => {
  const pkg = JSON.parse(readFileSync(join(repoRoot, 'package.json'), 'utf8'));
  const lockfile = JSON.parse(readFileSync(join(repoRoot, 'package-lock.json'), 'utf8'));
  const pinned = pkg.dependencies[RUNTIME_CLIENT_PKG];
  const locked = lockfile.packages[`node_modules/${RUNTIME_CLIENT_PKG}`];
  assert.match(pinned, /^\d+\.\d+\.\d+$/, `expected exact semver pin, got ${JSON.stringify(pinned)}`);
  assert.ok(compareExactSemver(pinned, '1.1.3') >= 0, `expected pinned version >= 1.1.3, got ${pinned}`);
  assert.equal(lockfile.packages[''].dependencies[RUNTIME_CLIENT_PKG], pinned);
  assert.equal(locked.version, pinned);

  // New --serve options parse on Story, ., and direct .prompt.md targets (both prefix and trailing).
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

  const parsedPrompt = parseArgv([
    'prompts/app.prompt.md', '--serve',
    '--allow-origins', 'https://chatgpt.com',
    '--trust-proxy',
    '--serve-token', 'tok-123',
    '--serve-header', 'X-PDD-Gate',
  ]);
  assert.equal(parsedPrompt.commandId, 'try');
  assert.deepEqual(parsedPrompt.operands, ['prompts/app.prompt.md']);
  assert.equal(parsedPrompt.options['--serve'], '8080');
  assert.equal(parsedPrompt.options['--allow-origins'], 'https://chatgpt.com');
  assert.equal(parsedPrompt.options['--trust-proxy'], true);
  assert.equal(parsedPrompt.options['--serve-token'], 'tok-123');
  assert.equal(parsedPrompt.options['--serve-header'], 'X-PDD-Gate');

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

  // Missing --serve or combining --stop with serve extras fails closed with exit 2.
  const setup = harbor(t);
  const noServePorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.runTry({ cwd: setup.repo, words: ['place-order'], options: { '--allow-origins': 'https://chatgpt.com' } }, noServePorts.ports),
    2,
  );
  assert.match(noServePorts.ports.stderr.text, /require --serve/);

  const stopPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
  assert.equal(
    await seam.runTry({ cwd: setup.repo, words: [PLACE], options: { '--stop': true, '--trust-proxy': true } }, stopPorts.ports),
    2,
  );
});

test('#2556: pdd lint --remote fails closed on refused, incomplete, or error-bearing runtime lint responses', async t => {
  const cases = [
    [
      'refused verdict with lint-incomplete',
      answer => {
        answer.result.report.verdict = 'refused';
        answer.result.report.refusal = { code: 'lint-incomplete', message: 'Program lint did not finish.' };
      },
    ],
    [
      'problems_complete false on passing answer',
      answer => {
        answer.result.problems_complete = false;
      },
    ],
    [
      'contradictory capabilities_complete false inside report.lint',
      answer => {
        answer.result.capabilities_complete = true;
        answer.result.report.lint.capabilities_complete = false;
      },
    ],
    [
      'severity error problem on passing lint answer',
      answer => {
        answer.result.problems = [
          { code: 'invalid-digest', file: PLACE, severity: 'error', message: 'prose_sha256 is blank.' },
        ];
      },
    ],
  ];

  for (const [label, mutate] of cases) {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (entry, f) => {
      if (entry.method === 'POST' && entry.command === 'lint') {
        const answer = f.lint(entry.request.requestId);
        mutate(answer);
        return { status: 200, json: answer };
      }
      return f.normal(entry);
    });

    const stdout = captureStream();
    const stderr = captureStream();
    const code = await runPdd(['lint', '--remote', 'place-order', '--json'], {
      cwd: setup.repo,
      env: {
        ...process.env,
        HOME: setup.home,
        PDD_STATE_DIR: setup.state,
        PDD_RUNTIME_URL: fake.origin,
        PATH: fakeGhBin(setup.sandbox),
      },
      stdout,
      stderr,
    });
    assert.notEqual(
      code,
      0,
      `expected pdd lint --remote to fail closed for "${label}", got exit 0\nstdout:\n${stdout.text}\nstderr:\n${stderr.text}`,
    );
  }

  // Control: healthy complete passing remote lint still exits 0.
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
});

test('#3665: v1 prompt clause citations work end-to-end through seam, --files --json, --details, --json, --read, and legacy servers', async t => {
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
