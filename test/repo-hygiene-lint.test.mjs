import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { isAbsolute, join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { buildCodexLintPrompt, runCodexLint } from '../src/codex-lint.mjs';
import {
  lintPromptStructure,
  lintRepoProject,
  loadProjectLintConfig,
  stripPromptMetadata,
} from '../src/repo-hygiene-lint.mjs';
import { compileGlobMatcher } from '../src/shared/glob-match.mjs';
import { lintTestFixedSleeps } from '../src/autopilot/lint-sleep-skip.mjs';
import { runCheck } from '../src/runtime-seam.mjs';
import { lintStories, lintStory } from '../src/story-lint.mjs';
import { fakeRuntime, harbor, portsFor, sink, TOKEN } from './helpers/runtime-fake.mjs';

test('3453 lintStory checks missing acceptance criteria while keeping valid Stories clean', () => {
  const noHeading = '# Export receipt\n\nAs a shop owner, I want a receipt PDF, so that I can file taxes.\n';
  const resNoHeading = lintStory(noHeading, { path: 'user_stories/no-heading.md' });
  assert.equal(resNoHeading.ok, false);
  assert.ok(resNoHeading.problems.some(p => p.line === 1 && p.code === 'story-missing-criteria'));

  const emptyCriteria = [
    '# Export receipt',
    '',
    'As a shop owner, I want a receipt PDF, so that I can file taxes.',
    '',
    '## Acceptance criteria',
    '',
    '## Rules to check',
    '',
    '- Totals match line items.',
  ].join('\n');
  const resEmpty = lintStory(emptyCriteria, { path: 'user_stories/empty-ac.md' });
  assert.equal(resEmpty.ok, false);
  assert.ok(resEmpty.problems.some(p => p.code === 'story-missing-criteria'));

  const sixBullets = [
    '# Export receipt',
    '',
    'As a shop owner, I want a receipt summary, so that I can reconcile daily sales.',
    '',
    '## Acceptance criteria',
    '',
    ...Array.from({ length: 6 }, (_, i) => `- AC${i + 1}: Summary row ${i + 1} prints "$${i + 1}.00"\n  with two decimal places.`),
  ].join('\n');
  assert.equal(lintStory(sixBullets, { path: 'user_stories/six.md' }).ok, true);
  assert.equal(lintStories([{ path: 'user_stories/six.md', text: sixBullets }]).ok, true);
  assert.equal(lintStories([{ path: 'user_stories/no-heading.md', text: noHeading }], { criteriaHygiene: true }).ok, false);
});

test('3453 pdd lint --local emits advisory structural warnings with exit code 0, honors Story scope and preserves port overrides', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-hygiene-3453-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts'), join(repo, 'src'), join(repo, 'user_stories'), join(repo, 'tests'), join(repo, 'test')]) {
    mkdirSync(dir, { recursive: true });
  }

  writeFileSync(join(repo, 'prompts/clean.prompt.md'), '# Clean order\n\nOwn `src/clean.mjs`. Compute order total in cents.\n\n## Dependencies\n\nNone.\n');
  writeFileSync(join(repo, 'src/clean.mjs'), '// Generated from prompts/clean.prompt.md\nexport const clean = () => 100;\n');
  writeFileSync(join(repo, 'user_stories/clean-order.md'), '# Clean order\n\nAs a customer, I want my order total in cents, so that I know the price.\n\n## Acceptance criteria\n\n1. Ordering 1 item returns 100 cents.\n');
  writeFileSync(
    join(repo, 'tests/clean-order.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/clean-order.md',
      criteria: [{ id: 'AC1', text: 'Ordering 1 item returns 100 cents.' }],
      initial_world: {},
      steps: [{
        step_id: 's1',
        entry_path: 'prompts/clean.prompt.md',
        operation: 'clean',
        input: {},
        checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 100 }],
      }],
    }, null, 2) + '\n',
  );

  writeFileSync(join(repo, 'prompts/missing-deps.prompt.md'), '# Missing deps module\n\nOwn `src/missing-deps.mjs`.\n');
  writeFileSync(join(repo, 'src/missing-deps.mjs'), '// Generated from prompts/missing-deps.prompt.md\nexport const missing = () => [];\n');

  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' };

  const jsonOut = sink(), jsonErr = sink();
  const exitJson = await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: jsonOut, stderr: jsonErr });
  assert.equal(exitJson, 0, jsonErr.text);
  const parsed = JSON.parse(jsonOut.text);
  assert.equal(parsed.exit_code, 0);
  assert.deepEqual(parsed.problems, []);
  assert.ok(parsed.warnings.some(w => w.startsWith('Warning:') && w.includes('prompts/missing-deps.prompt.md:1') && w.includes('[prompt-missing-dependencies]')));

  const txtOut = sink(), txtErr = sink();
  const exitTxt = await runPdd(['lint', '--local'], { cwd: repo, env, stdout: txtOut, stderr: txtErr });
  assert.equal(exitTxt, 0, txtErr.text);
  assert.match(txtOut.text, /Warning:.*prompts\/missing-deps\.prompt\.md:1/);

  const scopedOut = sink(), scopedErr = sink();
  const exitScoped = await runPdd(['lint', '--local', 'clean-order', '--json'], { cwd: repo, env, stdout: scopedOut, stderr: scopedErr });
  assert.equal(exitScoped, 0, scopedErr.text);
  const scopedParsed = JSON.parse(scopedOut.text);
  assert.equal(scopedParsed.exit_code, 0);
  assert.ok(!scopedParsed.warnings.some(w => w.includes('missing-deps')));

  const directReport = lintRepoProject({ root: repo });
  assert.ok(directReport.warnings.some(w => w.includes('prompts/missing-deps.prompt.md:1')));

  const overridePorts = portsFor(env, {
    gh: () => assert.fail('No auth in --local'),
    fetch: () => assert.fail('No network in --local'),
    lintSvgLayouts: () => ['Warning: custom caller override warning'],
  }).ports;
  const overrideCode = await runCheck({ cwd: repo, options: { '--lint': true, '--local': true, '--json': true } }, overridePorts);
  assert.equal(overrideCode, 0, overridePorts.stderr.text);
  assert.ok(JSON.parse(overridePorts.stdout.text).warnings.includes('Warning: custom caller override warning'));
});

test('3499 lintPromptStructure checks top-level title and Dependencies section', () => {
  const missingTitleAndDeps = 'Own `src/ship.mjs`. Compute shipping rates in cents.\n';
  const structWarnings = lintPromptStructure(missingTitleAndDeps, {
    path: 'prompts/ship.prompt.md',
    hasOwnedCode: true,
  });
  assert.ok(structWarnings.some(w => w.includes('prompts/ship.prompt.md:1') && w.includes('[prompt-missing-title]')));
  assert.ok(structWarnings.some(w => w.includes('prompts/ship.prompt.md:1') && w.includes('[prompt-missing-dependencies]')));

  assert.deepEqual(
    lintPromptStructure('# Greeting\n\nReturn a plain-English welcome greeting for the signed-in visitor.\n', {
      path: 'prompts/greeting.prompt.md',
      hasOwnedCode: false,
    }),
    [],
  );

  const manyHeadings = '## Runtime interface\n```json\n{}\n```\n## Other\nline\n'.repeat(2500);
  const tHead = performance.now();
  const strippedHeadings = stripPromptMetadata(manyHeadings);
  const msHead = performance.now() - tHead;
  assert.ok(!strippedHeadings.includes('Runtime interface'));
  assert.ok(msHead < 200, `expected linear heading scan on 15k lines, got ${msHead.toFixed(1)}ms`);
});

test('3499 pdd.json lint config supports disabling rules, promoting rules to error and invalid config reporting', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-lint-config-3499-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts'), join(repo, 'src'), join(repo, 'user_stories'), join(repo, 'tests')]) {
    mkdirSync(dir, { recursive: true });
  }

  writeFileSync(join(repo, 'prompts/calc.prompt.md'), 'Own `src/calc.mjs`. Compute tax in cents.\n');
  writeFileSync(join(repo, 'src/calc.mjs'), '// Generated from prompts/calc.prompt.md\nexport const calcTax = n => n;\n');
  writeFileSync(join(repo, 'user_stories/calc.md'), '# Tax\n\nAs a cashier, I want tax shown, so that totals match.\n\n## Acceptance criteria\n\n1. Tax for 100 is 100.\n');
  writeFileSync(
    join(repo, 'tests/calc.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/calc.md',
      criteria: [{ id: 'AC1', text: 'Tax for 100 is 100.' }],
      initial_world: {},
      steps: [{
        step_id: 's1',
        entry_path: 'prompts/calc.prompt.md',
        operation: 'calcTax',
        input: {},
        checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 100 }],
      }],
    }, null, 2) + '\n',
  );
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' };

  const baseProject = lintRepoProject({ root: repo });
  assert.equal(baseProject.ok, true);
  assert.equal(baseProject.configured, false);
  assert.ok(baseProject.warnings.some(w => w.includes('[prompt-missing-title]')));
  assert.ok(baseProject.warnings.some(w => w.includes('[prompt-missing-dependencies]')));

  writeFileSync(
    join(repo, 'pdd.json'),
    JSON.stringify({
      lint: {
        disable: ['prompt-missing-dependencies'],
        rules: {
          'prompt-missing-title': 'error',
        },
      },
    }, null, 2) + '\n',
  );
  execFileSync('git', ['add', 'pdd.json'], { cwd: repo });

  const configuredProject = lintRepoProject({ root: repo });
  assert.equal(configuredProject.ok, false);
  assert.equal(configuredProject.configured, true);
  assert.ok(!configuredProject.warnings.some(w => w.includes('[prompt-missing-dependencies]')));
  assert.ok(configuredProject.errors.some(e => e.startsWith('Error:') && e.includes('[prompt-missing-title]')));

  const errJsonOut = sink(), errJsonErr = sink();
  const exitErrJson = await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: errJsonOut, stderr: errJsonErr });
  assert.equal(exitErrJson, 1, errJsonErr.text);
  const parsedErr = JSON.parse(errJsonOut.text);
  assert.equal(parsedErr.ok, false);
  assert.equal(parsedErr.exit_code, 1);
  assert.ok(parsedErr.problems.some(p => p.includes('[prompt-missing-title]')));

  const errTxtOut = sink(), errTxtErr = sink();
  const exitErrTxt = await runPdd(['lint', '--local'], { cwd: repo, env, stdout: errTxtOut, stderr: errTxtErr });
  assert.equal(exitErrTxt, 1);
  assert.match(errTxtErr.text, /Error:.*\[prompt-missing-title\]/);

  const filesOut = sink(), filesErr = sink();
  const exitFiles = await runPdd(['test', '--files'], { cwd: repo, env, stdout: filesOut, stderr: filesErr });
  assert.equal(exitFiles, 0, filesErr.text);

  const invalidCfg = loadProjectLintConfig({
    lint: { rules: { 'prompt-missing-title': 'bogus' } },
  });
  assert.equal(invalidCfg.configured, true);
  assert.equal(invalidCfg.configErrors.length, 1);
  assert.equal(invalidCfg.configErrors[0].code, 'lint-config-invalid');
});

test('3499 pdd lint --codex runs read-only Codex Prompt and Story readability/quality lint with clear pass/fail output, JSON mode and Story scoping', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-codex-lint-3499-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [
    home,
    state,
    join(repo, 'prompts'),
    join(repo, 'src'),
    join(repo, 'user_stories'),
    join(repo, 'tests'),
  ]) {
    mkdirSync(dir, { recursive: true });
  }

  writeFileSync(
    join(repo, 'prompts/checkout.prompt.md'),
    [
      '# Checkout total',
      '',
      'Own `src/checkout.mjs`. Return integer cent totals for valid cart items.',
      '',
      '## Dependencies',
      '',
      'None.',
      '',
      '<details><summary>Runtime interface</summary>',
      '```json',
      '{"status":"draft","secret_marker":"SHOULD_BE_STRIPPED"}',
      '```',
      '</details>',
    ].join('\n') + '\n',
  );
  writeFileSync(
    join(repo, 'src/checkout.mjs'),
    Array.from({ length: 12 }, (_, i) => `// line ${i}\nexport const checkout${i} = () => ${i};`).join('\n') + '\n',
  );
  writeFileSync(
    join(repo, 'user_stories/checkout.md'),
    '# Checkout total\n\nAs a shopper, I want an itemised cent total, so that I know the final charge.\n\n## Acceptance criteria\n\n1. Two 250-cent drinks return 500 cents.\n',
  );
  writeFileSync(
    join(repo, 'tests/checkout.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/checkout.md',
      criteria: [{ id: 'AC1', text: 'Two 250-cent drinks return 500 cents.' }],
      initial_world: {},
      steps: [{
        step_id: 's1',
        entry_path: 'prompts/checkout.prompt.md',
        operation: 'checkout0',
        input: {},
        checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 0 }],
      }],
    }, null, 2) + '\n',
  );
  writeFileSync(
    join(repo, 'prompts/vague.prompt.md'),
    '# Vague dump\n\nlet x = 1; do stuff cleanly and handle errors fast.\n\n## Dependencies\n\nNone.\n',
  );
  writeFileSync(
    join(repo, 'src/vague.mjs'),
    Array.from({ length: 10 }, (_, i) => `export const vague${i} = ${i};`).join('\n') + '\n',
  );
  writeFileSync(join(repo, '.env'), 'OPENAI_API_KEY=never-send-me\n');

  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const env = {
    HOME: home,
    PDD_STATE_DIR: state,
    GH_TOKEN: 'ghs_should_not_leak',
    GITHUB_TOKEN: 'ghp_should_not_leak',
  };

  // Verify buildCodexLintPrompt numbers lines and labels prompt vs story.
  const builtPrompt = buildCodexLintPrompt([
    { path: 'prompts/checkout.prompt.md', kind: 'prompt', text: '# Checkout total\n\nCompute total.' },
    { path: 'user_stories/checkout.md', kind: 'story', text: '# Checkout total' },
  ]);
  assert.match(builtPrompt, /=== FILE: prompts\/checkout\.prompt\.md \(kind: prompt\) ===/);
  assert.match(builtPrompt, /1: # Checkout total/);
  assert.match(builtPrompt, /=== FILE: user_stories\/checkout\.md \(kind: story\) ===/);

  // 1. Story-scoped PASS run: verifies read-only sandbox flags, token stripping, secret & Runtime-interface exclusion, and PASS output.
  const calls = [];
  const passRunner = async (command, args, opts) => {
    calls.push({ command, args, ...opts });
    const outIdx = args.indexOf('--output-last-message');
    const outFile = args[outIdx + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [
        { path: 'prompts/checkout.prompt.md', verdict: 'pass', summary: 'Concise domain contract with clear integer-cent behavior.', issues: [] },
        { path: 'user_stories/checkout.md', verdict: 'pass', summary: 'Clear shopper role and concrete acceptance criterion.', issues: [] },
      ],
    }));
    return { code: 0, stdout: '', stderr: '' };
  };

  const passOut = sink(), passErr = sink();
  const passCode = await runPdd(['lint', '--codex', 'checkout'], {
    cwd: repo,
    env,
    stdout: passOut,
    stderr: passErr,
    codexLintPorts: { runAgentProcess: passRunner },
  });
  assert.equal(passCode, 0, passErr.text);
  assert.equal(calls.length, 1);
  assert.equal(calls[0].command, 'codex');
  assert.ok(calls[0].args.includes('exec'));
  assert.equal(calls[0].args[calls[0].args.indexOf('--sandbox') + 1], 'read-only');
  assert.equal(calls[0].env.GH_TOKEN, undefined);
  assert.equal(calls[0].env.GITHUB_TOKEN, undefined);
  assert.ok(!calls[0].input.includes('SHOULD_BE_STRIPPED'));
  assert.ok(!calls[0].input.includes('never-send-me'));
  assert.ok(!calls[0].input.includes('prompts/vague.prompt.md'));
  assert.match(passOut.text, /PASS prompts\/checkout\.prompt\.md — Concise domain contract/);
  assert.match(passOut.text, /PASS user_stories\/checkout\.md — Clear shopper role/);
  assert.match(passOut.text, /Lint \(Codex\): PASS \(2\/2 files passed\)/);

  // 2. Repo-wide FAIL run (plain text + --json): reports actionable line-numbered readability issues and exits 1.
  const failRunner = async (_command, args) => {
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [
        { path: 'prompts/checkout.prompt.md', verdict: 'pass', summary: 'Clear contract.', issues: [] },
        {
          path: 'prompts/vague.prompt.md',
          verdict: 'fail',
          summary: 'Uses imperative variable assignment and vague non-observable prose.',
          issues: [{ line: 3, rule: 'prompt-readability', message: 'Replace "let x = 1; do stuff cleanly" with observable inputs, outputs, and error rules.' }],
        },
        { path: 'user_stories/checkout.md', verdict: 'pass', summary: 'Testable acceptance criterion.', issues: [] },
      ],
    }));
    return { code: 0, stdout: '', stderr: '' };
  };

  const failOut = sink(), failErr = sink();
  const failCode = await runPdd(['lint', '--codex'], {
    cwd: repo,
    env,
    stdout: failOut,
    stderr: failErr,
    codexLintPorts: { runAgentProcess: failRunner },
  });
  assert.equal(failCode, 1);
  assert.match(failOut.text, /FAIL prompts\/vague\.prompt\.md — Uses imperative variable assignment/);
  assert.match(failOut.text, /prompts\/vague\.prompt\.md:3 \[prompt-readability\] Replace "let x = 1/);
  assert.match(failOut.text, /Lint \(Codex\): FAIL \(2\/3 files passed, 1 failed\)/);

  const jsonOut = sink(), jsonErr = sink();
  const jsonCode = await runPdd(['lint', '--codex', '--json'], {
    cwd: repo,
    env,
    stdout: jsonOut,
    stderr: jsonErr,
    codexLintPorts: { runAgentProcess: failRunner },
  });
  assert.equal(jsonCode, 1);
  const parsedCodexJson = JSON.parse(jsonOut.text);
  assert.equal(parsedCodexJson.schema_version, 'pdd.codex-lint.v1');
  assert.equal(parsedCodexJson.ok, false);
  assert.equal(parsedCodexJson.exit_code, 1);
  assert.equal(parsedCodexJson.passed, 2);
  assert.equal(parsedCodexJson.failed, 1);
  assert.equal(parsedCodexJson.files.find(f => f.path === 'prompts/vague.prompt.md')?.status, 'fail');

  // 3. Unknown target and invalid option combinations exit 2 with clear guidance.
  const unknownOut = sink(), unknownErr = sink();
  assert.equal(
    await runPdd(['lint', '--codex', 'missing-story'], {
      cwd: repo,
      env,
      stdout: unknownOut,
      stderr: unknownErr,
      codexLintPorts: { runAgentProcess: passRunner },
    }),
    2,
  );
  assert.match(unknownErr.text, /Unknown Story or prompt path: missing-story/);

  const badTestFlagErr = sink();
  assert.equal(await runPdd(['test', '--codex'], { cwd: repo, env, stdout: sink(), stderr: badTestFlagErr }), 2);
  assert.match(badTestFlagErr.text, /Use pdd lint --codex/);

  const badComboErr = sink();
  assert.equal(await runPdd(['lint', '--codex', '--local'], { cwd: repo, env, stdout: sink(), stderr: badComboErr }), 2);
  assert.match(badComboErr.text, /accepts only Story or prompt paths, --json, and --timeout MIN/);
});

test('3499 glob guards and no-symlink pdd.json checks reject excessive wildcards and symlinked configs', async t => {
  assert.ok(compileGlobMatcher('**/a/**/**/b/*.mjs').test('x/a/y/z/b/handler.mjs'));
  assert.ok(compileGlobMatcher('**/a/**/**/b/*.mjs').test('a/b/handler.mjs'));
  assert.equal(compileGlobMatcher('a/*/*/*/*/*/*/*/*/*/*/*/*/*.mjs'), null);

  const scratch = mkdtempSync(join(tmpdir(), 'pdd-symlink-cfg-3499-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const outsideConfig = join(scratch, 'outside-pdd.json');
  writeFileSync(outsideConfig, JSON.stringify({
    lint: { rules: { 'prompt-missing-dependencies': 'error' } },
  }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts'), join(repo, 'src')]) mkdirSync(dir, { recursive: true });
  writeFileSync(join(repo, 'prompts/order.prompt.md'), '# Order\n\nOwn `src/order.mjs`.\n');
  writeFileSync(join(repo, 'src/order.mjs'), '// Prompt: prompts/order.prompt.md\nexport const o = 1;\n');
  symlinkSync(outsideConfig, join(repo, 'pdd.json'));

  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', 'prompts/order.prompt.md', 'src/order.mjs'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  assert.equal(loadProjectLintConfig(repo).configured, false);
  const out = sink(), err = sink();
  const code = await runPdd(['lint', '--local'], {
    cwd: repo,
    env: { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' },
    stdout: out,
    stderr: err,
  });
  assert.equal(code, 0, err.text);
});

test('3499 runCodexLint enforces --ignore-rules, -- end-of-options, global batch deadline, full credential/session scrubbing and output redaction', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-codex-hardening-3499-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts'), join(repo, 'src')]) mkdirSync(dir, { recursive: true });

  // Create 7 prompts (> 6 files per batch) with an embedded secret value to test redaction + 2-batch global deadline.
  for (let idx = 0; idx < 7; idx++) {
    writeFileSync(
      join(repo, `prompts/mod-${idx}.prompt.md`),
      `# Module ${idx}\n\nOwn \`src/mod-${idx}.mjs\`. Reference value: sec_live_verysecretvalue999.\n\n## Dependencies\n\nNone.\n`,
    );
    writeFileSync(
      join(repo, `src/mod-${idx}.mjs`),
      Array.from({ length: 8 }, (_, line) => `export const m${idx}_${line} = ${line};`).join('\n') + '\n',
    );
  }
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const sensitiveEnv = {
    HOME: home,
    PDD_STATE_DIR: state,
    PATH: process.env.PATH,
    GH_TOKEN: 'ghs_tok1234567890abcdef',
    GITHUB_TOKEN: 'ghp_tok1234567890abcdef',
    GITHUB_PAT: 'github_pat_1234567890abcdef',
    GH_PAT: 'ghp_pat1234567890abcdef',
    PDD_CLOUD_TOKEN: 'pddg_cloudtoken1234567890',
    NPM_TOKEN: 'npm_secret_token_12345',
    AWS_SECRET_ACCESS_KEY: 'aws_secret_access_key_val',
    AWS_SESSION_TOKEN: 'aws_session_token_val',
    OPENAI_API_KEY: 'sk-proj-1234567890abcdef',
    ANTHROPIC_API_KEY: 'sk-ant-1234567890abcdef',
    CODEX_THREAD_ID: 'thread-parent-1',
    CODEX_SANDBOX_NETWORK_DISABLED: '1',
    CLAUDECODE: '1',
    HERDR_SESSION: 'pdd',
    PDD_AGENT_SESSION: 'sess-1',
    PDD_AUTOPILOT_CONTEXT: 'auto-1',
    CUSTOM_SERVICE_SECRET: 'sec_live_verysecretvalue999',
  };

  // 1. Single-file run checks clamped timeoutMinutes, --ignore-rules, resolved outFile, trailing ['--', '-'], env scrubbing, and input/output redaction.
  const observedCalls = [];
  const leakingFailRunner = async (command, args, opts) => {
    observedCalls.push({ command, args, ...opts });
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [{
        path: 'prompts/mod-0.prompt.md',
        verdict: 'fail',
        summary: 'Leaked secret sec_live_verysecretvalue999 and ghp_tok1234567890abcdef in summary.',
        issues: [{ line: 3, rule: 'prompt-readability', message: 'Remove sec_live_verysecretvalue999 from prose.' }],
      }],
    }));
    return { code: 0, stdout: '', stderr: '' };
  };

  const jsonOut = sink(), jsonErr = sink();
  const singleExit = await runCodexLint(
    { cwd: repo, words: ['prompts/mod-0.prompt.md'], timeoutMinutes: 999, json: true, env: sensitiveEnv },
    { stdout: jsonOut, stderr: jsonErr, now: () => 1_000_000, runAgentProcess: leakingFailRunner },
  );
  assert.equal(singleExit, 1);
  assert.equal(observedCalls.length, 1);
  const call = observedCalls[0];
  assert.equal(call.timeoutMs, 120 * 60 * 1000, 'timeoutMinutes > 120 clamps to 120 minutes');
  assert.ok(call.args.includes('--ignore-rules'));
  const outFileArg = call.args[call.args.indexOf('--output-last-message') + 1];
  assert.equal(isAbsolute(outFileArg), true);
  assert.deepEqual(call.args.slice(-2), ['--', '-']);

  for (const strippedKey of [
    'GH_TOKEN', 'GITHUB_TOKEN', 'GITHUB_PAT', 'GH_PAT', 'PDD_CLOUD_TOKEN', 'NPM_TOKEN',
    'AWS_SECRET_ACCESS_KEY', 'AWS_SESSION_TOKEN', 'OPENAI_API_KEY', 'ANTHROPIC_API_KEY',
    'CODEX_THREAD_ID', 'CODEX_SANDBOX_NETWORK_DISABLED', 'CLAUDECODE', 'HERDR_SESSION',
    'PDD_AGENT_SESSION', 'PDD_AUTOPILOT_CONTEXT',
  ]) {
    assert.equal(call.env[strippedKey], undefined, `${strippedKey} must be scrubbed from Codex env`);
  }
  assert.ok(!call.input.includes('sec_live_verysecretvalue999'), 'known env secret must be redacted from prompt input');
  assert.ok(call.input.includes('[redacted]'));

  const parsedJson = JSON.parse(jsonOut.text);
  assert.equal(parsedJson.ok, false);
  assert.ok(!jsonOut.text.includes('sec_live_verysecretvalue999'));
  assert.ok(!jsonOut.text.includes('ghp_tok1234567890abcdef'));
  assert.match(parsedJson.files[0].summary, /\[redacted\]/);
  assert.match(parsedJson.files[0].issues[0].message, /\[redacted\]/);

  // 2. Multi-batch global deadline: 7 files (batch 1 = 6 files, batch 2 = 1 file) share one overall budget instead of multiplying.
  let fakeNow = 1_000_000;
  const batchTimeouts = [];
  const clockAdvancingRunner = async (_cmd, args, opts) => {
    batchTimeouts.push(opts.timeoutMs);
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: Array.from({ length: 6 }, (_, idx) => ({
        path: `prompts/mod-${idx}.prompt.md`,
        verdict: 'pass',
        summary: 'Clean.',
        issues: [],
      })),
    }));
    // Advance clock past the clamped 0.1-minute (6000ms) overall deadline during batch 1.
    fakeNow += 6_500;
    return { code: 0, stdout: '', stderr: '' };
  };

  const deadlineOut = sink(), deadlineErr = sink();
  const deadlineExit = await runCodexLint(
    { cwd: repo, words: [], timeoutMinutes: 0.01, json: false, env: { HOME: home, PDD_STATE_DIR: state } },
    { stdout: deadlineOut, stderr: deadlineErr, now: () => fakeNow, runAgentProcess: clockAdvancingRunner },
  );
  assert.equal(deadlineExit, 1);
  assert.deepEqual(batchTimeouts, [6000], 'timeoutMinutes < 0.1 clamps to 6000ms and batch 2 stops once overall deadline expires');
  assert.match(deadlineErr.text, /Codex lint timed out after 6s/);
});

test('3499 + 3522 Short JSON scenarios omitting story_path with singular entry_path scope Story and Prompt rules in lint --local and lint --codex while keeping --emit-v1 and --bind-criteria clean', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-short-json-lint-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts'), join(repo, 'user_stories'), join(repo, 'tests')]) {
    mkdirSync(dir, { recursive: true });
  }
  const env = { HOME: home, PDD_STATE_DIR: state };

  writeFileSync(join(repo, 'prompts/calc.prompt.md'), '# Calculator\n\nAdd two numbers.\n\n```json\n{"cut": true\n');
  writeFileSync(join(repo, 'user_stories/calc.md'), '# Calculator\n\nAs a shopper, I want totals added, so that I see my bill.\n\n## Acceptance criteria\n\n1. Adding 2 and 3 returns 5.\n');
  writeFileSync(
    join(repo, 'tests/calc.json'),
    JSON.stringify({
      schema_version: 'pdd.scenario.short.v1',
      entry_path: 'prompts/calc.prompt.md',
      steps: [{ op: 'add', input: { a: 2, b: 3 }, checks: [['1', 'result', '/sum', '=', 5]] }],
    }, null, 2) + '\n',
  );

  execFileSync('git', ['init'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });

  const localOut = sink(), localErr = sink();
  const localExit = await runPdd(['lint', '--local', 'calc', '--json'], { cwd: repo, env, stdout: localOut, stderr: localErr });
  assert.equal(localExit, 1, localErr.text);
  const localJson = JSON.parse(localOut.text);
  assert.equal(localJson.ok, false);
  assert.ok(localJson.problems.some(p => p.includes('prompts/calc.prompt.md') && p.includes('[truncated-markdown-fence]')));

  const codexRunner = async (_cmd, args) => {
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [
        { path: 'prompts/calc.prompt.md', verdict: 'pass', summary: 'Clear calculator prompt.', issues: [] },
        { path: 'user_stories/calc.md', verdict: 'pass', summary: 'Clear shopper Story.', issues: [] },
      ],
    }));
    return { code: 0, stdout: '', stderr: '' };
  };
  const codexOut = sink(), codexErr = sink();
  const codexExit = await runCodexLint(
    { cwd: repo, words: ['calc'], json: true, env },
    { stdout: codexOut, stderr: codexErr, runAgentProcess: codexRunner },
  );
  assert.equal(codexExit, 1);
  assert.deepEqual(JSON.parse(codexOut.text).files.map(f => f.path).sort(), ['prompts/calc.prompt.md', 'user_stories/calc.md']);

  const emitOut = sink(), emitErr = sink();
  const emitExit = await runPdd(['lint', '--emit-v1', 'calc', '--json'], { cwd: repo, env, stdout: emitOut, stderr: emitErr });
  assert.equal(emitExit, 0, emitErr.text);
  assert.equal(JSON.parse(emitOut.text).scenarios[0].scenario.story_path, 'user_stories/calc.md');

  writeFileSync(
    join(repo, 'tests/calc.json'),
    JSON.stringify({
      schema_version: 'pdd.scenario.short.v1',
      story_path: 'user_stories/calc.md',
      entry_path: 'prompts/calc.prompt.md',
      steps: [{ op: 'add', input: { a: 2, b: 3 }, checks: [['1', 'result', '/sum', '=', 5]] }],
    }, null, 2) + '\n',
  );
  const bindOut = sink(), bindErr = sink();
  const bindExit = await runPdd(['lint', '--bind-criteria', 'calc', '--json'], { cwd: repo, env, stdout: bindOut, stderr: bindErr });
  assert.equal(bindExit, 0, bindErr.text);
  assert.equal(JSON.parse(bindOut.text).ok, true);
});

test('3574 + 3578 Round 2/3 regressions: Story-scoped sibling isolation and hosted repo-wide pdd lint errors', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-r2-p1a-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts'), join(repo, 'user_stories'), join(repo, 'tests')]) {
    mkdirSync(dir, { recursive: true });
  }
  writeFileSync(join(repo, 'prompts/shared.prompt.md'), '# Shared pricing\n\nOwn `src/shared.mjs`. Compute totals in cents.\n\n## Dependencies\n\nNone.\n');
  writeFileSync(join(repo, 'user_stories/good.md'), '# Good story\n\nAs a shopper, I want my subtotal shown in cents, so that I know the price.\n\n## Acceptance criteria\n\n1. One item costs 100 cents.\n');
  writeFileSync(join(repo, 'tests/good.json'), JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/good.md',
    criteria: [{ id: 'AC1', text: 'One item costs 100 cents.' }],
    initial_world: {},
    steps: [{ step_id: 's1', entry_path: 'prompts/shared.prompt.md', operation: 'price', input: {}, checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 100 }] }],
  }, null, 2) + '\n');
  writeFileSync(join(repo, 'user_stories/bad.md'), '# Bad story\n\nAs a shopper, I want a table.\n\n## Acceptance criteria\n\n1. Check 1 returns 1.\n\n| A | B |\n| --- | --- |\n| 1 | cut\n');
  writeFileSync(join(repo, 'tests/bad.json'), JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/bad.md',
    criteria: [{ id: 'AC1', text: 'Check 1 returns 1.' }],
    initial_world: {},
    steps: [{ step_id: 's1', entry_path: 'prompts/shared.prompt.md', operation: 'price', input: {}, checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 1 }] }],
  }, null, 2) + '\n');
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' };
  const goodOut = sink(), goodErr = sink();
  assert.equal(await runPdd(['lint', '--local', 'user_stories/good.md'], { cwd: repo, env, stdout: goodOut, stderr: goodErr }), 0, goodErr.text);

  const badOut = sink(), badErr = sink();
  assert.equal(await runPdd(['lint', '--local', 'user_stories/bad.md'], { cwd: repo, env, stdout: badOut, stderr: badErr }), 1);
  assert.match(badErr.text, /user_stories\/bad\.md.*\[truncated-markdown-table\]/);

  const repoOut = sink(), repoErr = sink();
  assert.equal(await runPdd(['lint', '--local'], { cwd: repo, env, stdout: repoOut, stderr: repoErr }), 1);
  assert.match(repoErr.text, /user_stories\/bad\.md.*\[truncated-markdown-table\]/);

  const h = harbor(t, hRepo => {
    writeFileSync(
      join(hRepo, 'prompts/adapter.prompt.md'),
      '---\nkind: native-only\nreason: Live persistence adapter.\n---\n\n# Harbor adapter\n\n```json\n{"cut": true\n',
    );
  });
  const fake = await fakeRuntime(t, entry => fake.normal(entry));
  const fakeBin = join(h.sandbox, 'bin');
  mkdirSync(fakeBin, { recursive: true });
  writeFileSync(join(fakeBin, 'gh'), `#!/bin/sh\nif [ "$1" = "auth" ]; then echo "${TOKEN}"; else echo "octo 4242"; fi\n`, { mode: 0o755 });
  const hostedEnv = { ...process.env, HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: fake.origin, PATH: `${fakeBin}:${process.env.PATH ?? ''}` };
  const hostedOut = sink(), hostedErr = sink();
  const hostedCode = await runPdd(['lint', '--remote', '--json'], { cwd: h.repo, env: hostedEnv, stdout: hostedOut, stderr: hostedErr });
  assert.equal(hostedCode, 1);
  assert.ok(JSON.parse(hostedOut.text).problems.some(p => p.includes('prompts/adapter.prompt.md') && p.includes('[truncated-markdown-fence]')));
});

test('3562 polling FP fix: test-fixed-sleep exempts waitFor/until polling helpers, bounded retry loops, and Promise.race watchdogs while still flagging bare unguarded sleeps', () => {
  const safePollingJs = [
    "import { setTimeout } from 'node:timers/promises';",
    'const until = async (check, ms = 5000) => {',
    '  const deadline = Date.now() + ms;',
    '  while (Date.now() < deadline) {',
    '    const val = check();',
    '    if (val) return val;',
    '    await new Promise(r => setTimeout(r, 25));',
    '  }',
    '  throw new Error("timeout");',
    '};',
    'async function waitForFile(path) {',
    '  for (let i = 0; i < 100; i++) {',
    '    if (exists(path)) return true;',
    '    await sleep(10);',
    '  }',
    '  return false;',
    '}',
    "test('polling and retry backoff loops', async () => {",
    '  const end = Date.now() + 5000;',
    '  while (Date.now() < end && !ready()) await new Promise(r => setTimeout(r, 20));',
    '  while (!stopped() && performance.now() < end) await setTimeout(10);',
    '  for (let i = 0; i < 20 && !isReady(); i++) await new Promise(r => setTimeout(r, 15));',
    '  for (;;) {',
    '    try { readReady(); break; } catch { await new Promise(r => setTimeout(r, 5)); }',
    '  }',
    '  for (const delayMs of [10, 20, 40]) {',
    '    if (checkDone()) break;',
    '    await new Promise(r => setTimeout(r, 15));',
    '  }',
    '  await Promise.race([pendingOp(), new Promise(resolve => setTimeout(() => resolve(null), 5000))]);',
    '  void until; void waitForFile;',
    '});',
  ].join('\n');
  assert.deepEqual(
    lintTestFixedSleeps(safePollingJs, { path: 'test/polling-safe.test.mjs' }),
    [],
    'legitimate polling helpers, bounded retry loops, and Promise.race watchdogs must emit 0 warnings',
  );

  const safePollingPy = [
    'import time',
    'def wait_for_ready(check):',
    '    deadline = time.time() + 5',
    '    while time.time() < deadline:',
    '        if check():',
    '            return True',
    '        time.sleep(0.05)',
    '    return False',
    'def test_retry_loop():',
    '    for _ in range(10):',
    '        try:',
    '            probe()',
    '            break',
    '        except RuntimeError:',
    '            time.sleep(0.02)',
  ].join('\n');
  assert.deepEqual(
    lintTestFixedSleeps(safePollingPy, { path: 'tests/test_polling_safe.py' }),
    [],
    'Python polling and bounded retry loops must emit 0 warnings',
  );

  // Bare unguarded sleeps (including inside data-driven test loops or unconditional loops) MUST STILL FAIL!
  const badUnguardedJs = [
    "test('bare sleep', async () => {",
    '  await new Promise(r => setTimeout(r, 200));',
    '  await sleep(150);',
    '  for (let i = 0; i < 3; i++) { await sleep(50); }',
    '  while (true) { await sleep(50); }',
    '});',
    'for (const size of [1, 2]) {',
    "  test('data loop with bare sleep', async () => {",
    '    await new Promise(r => setTimeout(r, 30));',
    '  });',
    '}',
  ].join('\n');
  const badWarnings = lintTestFixedSleeps(badUnguardedJs, { path: 'test/bare-sleeps.test.mjs' });
  assert.equal(badWarnings.length, 5, `expected 5 bare unguarded sleep warnings, got:\n${badWarnings.join('\n')}`);

  const badUnguardedPy = [
    'import time',
    'def test_bare_sleep():',
    '    time.sleep(0.5)',
    'def test_unconditional_for():',
    '    for _ in range(3):',
    '        time.sleep(0.1)',
  ].join('\n');
  const badPyWarnings = lintTestFixedSleeps(badUnguardedPy, { path: 'tests/test_bare_sleep.py' });
  assert.equal(badPyWarnings.length, 2, `expected 2 bare Python sleep warnings, got:\n${badPyWarnings.join('\n')}`);
});

test('3562 cross-family polling regressions: state polling, data-drain, Promise.race arm isolation, and Python O(N)', () => {
  // #3: Polling classification (state === PENDING exempt without `.`; data-draining while(rows.length){rows.pop()} flagged;
  // Promise.race ONLY exempts direct timeout arm, NEVER sleep inside sibling work callback!).
  const statePollJs = [
    "test('state polling without dot', async () => {",
    '  while (state === PENDING) { await sleep(10); }',
    '  do { await sleep(10); } while (status !== READY);',
    '});',
  ].join('\n');
  assert.deepEqual(lintTestFixedSleeps(statePollJs, { path: 'test/state-poll.test.mjs' }), []);

  const dataDrainAndRaceWorkJs = [
    "test('data drain, pure counters, and race chained work', async () => {",
    '  while (rows.length) { rows.pop(); await sleep(10); }',
    '  while (queue.length > 0) { queue.shift(); await new Promise(r => setTimeout(r, 10)); }',
    '  while (i !== limit) { i++; await sleep(10); }',
    '  for (let i = 0; i !== limit; i++) { await sleep(10); }',
    '  for (let i = 0; i !== batch.length; i++) { await sleep(10); }',
    '  await Promise.race([',
    '    (async () => { await sleep(500); return "work"; })(),',
    '    sleep(50).then(() => doWork()),',
    '    new Promise(resolve => setTimeout(() => resolve(null), 5000)),',
    '  ]);',
    '});',
  ].join('\n');
  const drainRaceWarnings = lintTestFixedSleeps(dataDrainAndRaceWorkJs, { path: 'test/drain-race.test.mjs' });
  assert.equal(drainRaceWarnings.length, 7, `expected 7 warnings (2 drains + 3 pure counters + sibling callback + chained .then arm, 0 on direct timeout arm), got:\n${drainRaceWarnings.join('\n')}`);
  assert.match(drainRaceWarnings[0], /:2 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[1], /:3 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[2], /:4 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[3], /:5 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[4], /:6 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[5], /:8 \[test-fixed-sleep\]/);
  assert.match(drainRaceWarnings[6], /:9 \[test-fixed-sleep\]/);

  // #3 & #4 Python: state == PENDING exempt (including tab-indented!), rows.pop() drain & pure counter flagged, and 4,000 sleeps inside 1 loop stay strictly O(N) (< 400ms)!
  const pyMixed = [
    'import time',
    'def test_py_poll_and_drain():',
    '    while state == PENDING:',
    '        time.sleep(0.05)',
    '    while rows:',
    '        rows.pop()',
    '        time.sleep(0.05)',
    '    while i != limit:',
    '        i += 1',
    '        time.sleep(0.05)',
    'def test_py_tab_indented():',
    '\twhile state == PENDING:',
    '\t\ttime.sleep(0.05)',
    '\twhile i != batch.size:',
    '\t\ti += 1',
    '\t\ttime.sleep(0.05)',
  ].join('\n');
  const pyMixedWarnings = lintTestFixedSleeps(pyMixed, { path: 'tests/test_py_mixed.py' });
  assert.equal(pyMixedWarnings.length, 3, `expected rows.pop() drain + 2 pure counters flagged (and tab-indented polling exempt), got:\n${pyMixedWarnings.join('\n')}`);
  assert.match(pyMixedWarnings[0], /:7 \[test-fixed-sleep\]/);
  assert.match(pyMixedWarnings[1], /:10 \[test-fixed-sleep\]/);
  assert.match(pyMixedWarnings[2], /:16 \[test-fixed-sleep\]/);

  const hugePyInOneLoop = `import time\ndef test_many_in_one_loop():\n    while i != limit:\n        i += 1\n${'        time.sleep(0.01)\n'.repeat(4000)}`;
  const t0 = performance.now();
  const hugePyWarnings = lintTestFixedSleeps(hugePyInOneLoop, { path: 'tests/test_many_sleeps.py' });
  const elapsedMs = performance.now() - t0;
  assert.equal(hugePyWarnings.length, 4000);
  assert.ok(elapsedMs < 400, `expected linear O(N) memoized scan on 4,000 Python sleeps inside 1 loop, took ${elapsedMs.toFixed(1)}ms`);
});
