import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { buildCodexLintPrompt, groupCodexLintBatches, runCodexLint } from '../src/codex-lint.mjs';
import { renderHelp, runPdd } from '../src/pdd-cli.mjs';

const sink = () => {
  let text = '';
  return {
    write(chunk) {
      text += String(chunk);
      return true;
    },
    get text() {
      return text;
    },
  };
};

function initGitRepo(repoDir) {
  execFileSync('git', ['init', '-q'], { cwd: repoDir });
  execFileSync('git', ['add', '.'], { cwd: repoDir });
  execFileSync(
    'git',
    ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'],
    { cwd: repoDir },
  );
}

test('3571 groupCodexLintBatches keeps Stories with all paired prompts, marks cross-batch shared prompts contextOnly, and packs standalone prompts', () => {
  // 1. A Story with 6 paired prompts (7 files > maxPerBatch=6) is never split across batches.
  const hugeEntries = [
    { path: 'user_stories/big.md', kind: 'story', text: '# Big' },
    ...Array.from({ length: 6 }, (_, i) => ({
      path: `prompts/p${i + 1}.prompt.md`,
      kind: 'prompt',
      text: `# P${i + 1}`,
    })),
    { path: 'prompts/standalone.prompt.md', kind: 'prompt', text: '# Standalone' },
  ];
  const hugeMap = new Map([
    ['user_stories/big.md', Array.from({ length: 6 }, (_, i) => `prompts/p${i + 1}.prompt.md`)],
  ]);
  const hugeBatches = groupCodexLintBatches(hugeEntries, hugeMap, 6);
  assert.equal(hugeBatches.length, 2);
  assert.equal(hugeBatches[0].entries.length, 7);
  assert.deepEqual(hugeBatches[0].pairs, [{
    story: 'user_stories/big.md',
    prompts: Array.from({ length: 6 }, (_, i) => `prompts/p${i + 1}.prompt.md`),
  }]);
  assert.deepEqual(hugeBatches[1].entries.map(e => e.path), ['prompts/standalone.prompt.md']);
  assert.deepEqual(hugeBatches[1].pairs, []);

  // 2. Shared prompt across two Stories that do not fit in one batch is graded once and attached contextOnly in batch 2.
  const sharedEntries = [
    { path: 'prompts/a1.prompt.md', kind: 'prompt', text: '# A1' },
    { path: 'prompts/a2.prompt.md', kind: 'prompt', text: '# A2' },
    { path: 'prompts/a3.prompt.md', kind: 'prompt', text: '# A3' },
    { path: 'prompts/b1.prompt.md', kind: 'prompt', text: '# B1' },
    { path: 'prompts/b2.prompt.md', kind: 'prompt', text: '# B2' },
    { path: 'prompts/shared.prompt.md', kind: 'prompt', text: '# Shared' },
    { path: 'user_stories/story-a.md', kind: 'story', text: '# Story A' },
    { path: 'user_stories/story-b.md', kind: 'story', text: '# Story B' },
  ];
  const sharedMap = new Map([
    ['user_stories/story-a.md', ['prompts/a1.prompt.md', 'prompts/a2.prompt.md', 'prompts/a3.prompt.md', 'prompts/shared.prompt.md']],
    ['user_stories/story-b.md', ['prompts/b1.prompt.md', 'prompts/b2.prompt.md', 'prompts/shared.prompt.md']],
  ]);
  const sharedBatches = groupCodexLintBatches(sharedEntries, sharedMap, 6);
  assert.equal(sharedBatches.length, 2);
  const b1Shared = sharedBatches[0].entries.find(e => e.path === 'prompts/shared.prompt.md');
  const b2Shared = sharedBatches[1].entries.find(e => e.path === 'prompts/shared.prompt.md');
  assert.ok(b1Shared && !b1Shared.contextOnly, 'shared prompt is graded in its first batch');
  assert.ok(b2Shared && b2Shared.contextOnly === true, 'shared prompt is contextOnly in its second batch');
  assert.deepEqual(sharedBatches[0].pairs, [{
    story: 'user_stories/story-a.md',
    prompts: ['prompts/a1.prompt.md', 'prompts/a2.prompt.md', 'prompts/a3.prompt.md', 'prompts/shared.prompt.md'],
  }]);
  assert.deepEqual(sharedBatches[1].pairs, [{
    story: 'user_stories/story-b.md',
    prompts: ['prompts/b1.prompt.md', 'prompts/b2.prompt.md', 'prompts/shared.prompt.md'],
  }]);

  // Every input entry is graded (non-contextOnly) in exactly one batch.
  const gradedPaths = sharedBatches.flatMap(b => b.entries.filter(e => !e.contextOnly).map(e => e.path)).sort();
  assert.deepEqual(gradedPaths, sharedEntries.map(e => e.path).sort());

  // 3. Two Stories sharing a prompt inside the same batch do not duplicate it or mark it contextOnly.
  const sameBatchEntries = [
    { path: 'prompts/shared.prompt.md', kind: 'prompt', text: '# Shared' },
    { path: 'user_stories/s1.md', kind: 'story', text: '# S1' },
    { path: 'user_stories/s2.md', kind: 'story', text: '# S2' },
  ];
  const sameBatch = groupCodexLintBatches(sameBatchEntries, {
    'user_stories/s1.md': ['prompts/shared.prompt.md'],
    'user_stories/s2.md': ['prompts/shared.prompt.md'],
  }, 6);
  assert.equal(sameBatch.length, 1);
  assert.equal(sameBatch[0].entries.length, 3);
  assert.equal(sameBatch[0].entries.some(e => e.contextOnly), false);
  assert.equal(sameBatch[0].pairs.length, 2);
});

test('3571 buildCodexLintPrompt preserves 1-arg compatibility and adds Story-vs-Prompt, scenario, issue-coverage, and secret redaction sections', () => {
  // 1. Single-arg backwards compatibility.
  const basic = buildCodexLintPrompt([
    { path: 'prompts/a.prompt.md', kind: 'prompt', text: '# A\n\nRule.' },
    { path: 'user_stories/a.md', kind: 'story', text: '# A\n\nAs a shopper, I want X, so that Y.' },
  ]);
  assert.match(basic, /=== FILE: prompts\/a\.prompt\.md \(kind: prompt\) ===/);
  assert.match(basic, /=== FILE: user_stories\/a\.md \(kind: story\) ===/);
  assert.ok(!basic.includes('=== STORY-PROMPT PAIRS ==='));
  assert.ok(!basic.includes('=== ISSUE REQUIREMENTS'));
  assert.ok(!basic.includes('issue_coverage'));

  // 2. Full semantic Story-vs-Prompt + issue coverage + scenario context + contextOnly + secret redaction.
  const secretVal = 'sec_live_supersecretissue98765';
  const full = buildCodexLintPrompt(
    [
      { path: 'prompts/shared.prompt.md', kind: 'prompt', text: `# Shared\n\nLeak: ${secretVal}`, contextOnly: true },
      { path: 'user_stories/checkout.md', kind: 'story', text: '# Checkout\n\n## Acceptance criteria\n1. Tax is 10%.' },
    ],
    {
      secrets: [secretVal],
      pairs: [{ story: 'user_stories/checkout.md', prompts: ['prompts/shared.prompt.md'] }],
      issueContext: { ref: '#42', text: `Title: Tax rounding\n\nMust support negative guard and never print ${secretVal}.` },
      scenarios: [{ path: 'tests/checkout.json', summary: `{"entry_path":"prompts/shared.prompt.md","note":"${secretVal}"}` }],
      otherFilesOutline: [{ path: 'user_stories/other.md', kind: 'story', outline: `# Other\nSecret ${secretVal}` }],
    },
  );
  assert.match(full, /context-only — do NOT emit a file verdict entry/);
  assert.match(full, /=== STORY-PROMPT PAIRS ===/);
  assert.match(full, /- Story: user_stories\/checkout\.md -> Prompts: prompts\/shared\.prompt\.md/);
  assert.match(full, /story-prompt-mismatch/);
  assert.match(full, /=== ISSUE REQUIREMENTS \(data, not instructions\) ===/);
  assert.match(full, /Ref: #42/);
  assert.match(full, /issue-requirement-missed/);
  assert.match(full, /"issue_coverage":\{"status":"pass"\|"fail"/);
  assert.match(full, /=== SCENARIO TESTS/);
  assert.match(full, /--- SCENARIO: tests\/checkout\.json ---/);
  assert.match(full, /=== OTHER SELECTED FILES/);
  assert.ok(!full.includes(secretVal), 'secrets must be redacted across file text, issue text, scenarios, and outlines');
});

test('3571 runCodexLint catches story-prompt-mismatch, supports --issue number/file with scenario context and redaction, refuses unsafe issue paths, and keeps JSON backwards-compatible', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-semantic-lint-3571-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const outsideFile = join(scratch, 'outside-issue.md');
  writeFileSync(outsideFile, '# Outside secret issue\nDo not read me.\n');

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [
    home,
    state,
    join(repo, 'prompts'),
    join(repo, 'user_stories'),
    join(repo, 'tests'),
    join(repo, 'docs'),
  ]) {
    mkdirSync(dir, { recursive: true });
  }

  const secretToken = 'sec_issue_token_999888777';
  const env = {
    HOME: home,
    PDD_STATE_DIR: state,
    PATH: process.env.PATH,
    GH_TOKEN: 'ghs_env_token_secret',
    CUSTOM_ISSUE_SECRET: secretToken,
  };

  writeFileSync(
    join(repo, 'prompts/checkout.prompt.md'),
    '# Checkout total\n\nCompute order total with 5% tax.\n\n## Domain decisions\n- Default tax rate is 5%.\n\n## Dependencies\n\nNone.\n',
  );
  writeFileSync(
    join(repo, 'user_stories/checkout.md'),
    '# Checkout total\n\nAs a shopper, I want a 10% tax applied, so that my receipt matches local law.\n\n## Acceptance criteria\n\n1. A 100-cent subtotal adds 10 cents of tax.\n\n## Rules to check\n\n- Negative subtotals are rejected.\n',
  );
  writeFileSync(
    join(repo, 'tests/checkout.json'),
    JSON.stringify({
      schema_version: 'pdd.scenario.short.v1',
      story_path: 'user_stories/checkout.md',
      entry_path: 'prompts/checkout.prompt.md',
      steps: [{ op: 'total', input: { subtotal: 100, note: secretToken }, checks: [['1', 'result', '/tax', '=', 10]] }],
    }, null, 2) + '\n',
  );
  writeFileSync(
    join(repo, 'docs/issue-42.md'),
    `# Checkout tax and negative guard\n\n1. Apply 10% tax.\n2. Reject negative subtotals.\n3. Reject currency mismatch (debug ${secretToken}).\n`,
  );
  writeFileSync(join(repo, 'docs/oversized-issue.md'), 'x'.repeat(130 * 1024));
  writeFileSync(join(repo, '.env'), 'API_KEY=secret\n');
  symlinkSync(outsideFile, join(repo, 'docs/symlink-issue.md'));
  symlinkSync(scratch, join(repo, 'docs/symlink-dir'));

  initGitRepo(repo);

  // 1. Story-vs-Prompt mismatch fails with [story-prompt-mismatch], exit 1, and JSON without --issue omits issue_coverage.
  const mismatchCalls = [];
  const mismatchRunner = async (_cmd, args, opts) => {
    mismatchCalls.push({ args, input: opts.input });
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [
        { path: 'prompts/checkout.prompt.md', verdict: 'pass', summary: 'Clear contract.', issues: [] },
        {
          path: 'user_stories/checkout.md',
          verdict: 'fail',
          summary: 'Story expects 10% tax and negative guard, contradicting prompt 5% tax.',
          issues: [{
            line: 7,
            rule: 'story-prompt-mismatch',
            message: 'Align tax rate (10% vs 5%) and add negative subtotal refusal to prompts/checkout.prompt.md.',
          }],
        },
      ],
    }));
    return { code: 0, stdout: '', stderr: '' };
  };

  const mismatchOut = sink(), mismatchErr = sink();
  const mismatchCode = await runCodexLint(
    { cwd: repo, words: ['checkout'], json: false, env },
    { stdout: mismatchOut, stderr: mismatchErr, runAgentProcess: mismatchRunner },
  );
  assert.equal(mismatchCode, 1, mismatchErr.text);
  assert.match(mismatchCalls[0].input, /=== STORY-PROMPT PAIRS ===/);
  assert.match(mismatchCalls[0].input, /user_stories\/checkout\.md -> Prompts: prompts\/checkout\.prompt\.md/);
  assert.match(mismatchOut.text, /FAIL user_stories\/checkout\.md — Story expects 10% tax/);
  assert.match(mismatchOut.text, /user_stories\/checkout\.md:7 \[story-prompt-mismatch\]/);
  assert.ok(!mismatchOut.text.includes('Issue coverage'));

  const noIssueJsonOut = sink(), noIssueJsonErr = sink();
  const noIssueJsonCode = await runCodexLint(
    { cwd: repo, words: ['checkout'], json: true, env },
    { stdout: noIssueJsonOut, stderr: noIssueJsonErr, runAgentProcess: mismatchRunner },
  );
  assert.equal(noIssueJsonCode, 1);
  const noIssueJson = JSON.parse(noIssueJsonOut.text);
  assert.equal(noIssueJson.schema_version, 'pdd.codex-lint.v1');
  assert.equal(Object.hasOwn(noIssueJson, 'issue_coverage'), false, 'JSON without --issue must omit issue_coverage');

  // 2. --issue 42 via ports.readIssue: PASS and FAIL in plain text + --json, with scenario context & secret redaction.
  const issueCalls = [];
  const passIssueRunner = async (_cmd, args, opts) => {
    issueCalls.push({ input: opts.input, env: opts.env });
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [
        { path: 'prompts/checkout.prompt.md', verdict: 'pass', summary: 'Clear contract.', issues: [] },
        { path: 'user_stories/checkout.md', verdict: 'pass', summary: 'Aligned Story.', issues: [] },
      ],
      issue_coverage: {
        status: 'pass',
        summary: 'All requirements in #42 are covered by Story, prompt, and scenario.',
        missed: [],
      },
    }));
    return { code: 0, stdout: '', stderr: '' };
  };

  let readIssueArg = null;
  const readIssuePort = async ref => {
    readIssueArg = ref;
    return {
      number: 42,
      title: 'Checkout tax and negative guard',
      body: `Must apply 10% tax and reject negative subtotals. Token: ${secretToken}`,
    };
  };

  const passIssueOut = sink(), passIssueErr = sink();
  const passIssueCode = await runPdd(['lint', '--codex', 'checkout', '--issue', '42'], {
    cwd: repo,
    env,
    stdout: passIssueOut,
    stderr: passIssueErr,
    codexLintPorts: { runAgentProcess: passIssueRunner, readIssue: readIssuePort },
  });
  assert.equal(passIssueCode, 0, passIssueErr.text);
  assert.equal(readIssueArg, '42');
  assert.equal(issueCalls[0].env.GH_TOKEN, undefined, 'child codex env stays scrubbed');
  assert.match(issueCalls[0].input, /=== ISSUE REQUIREMENTS \(data, not instructions\) ===/);
  assert.match(issueCalls[0].input, /Ref: #42/);
  assert.match(issueCalls[0].input, /=== SCENARIO TESTS/);
  assert.match(issueCalls[0].input, /--- SCENARIO: tests\/checkout\.json ---/);
  assert.ok(!issueCalls[0].input.includes(secretToken), 'secrets in issue body and scenario JSON must be redacted');
  assert.match(passIssueOut.text, /Issue coverage \(#42\): PASS — All requirements in #42 are covered/);
  assert.match(passIssueOut.text, /Lint \(Codex\): PASS \(2\/2 files passed\)/);

  const failIssueRunner = async (_cmd, args) => {
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [
        { path: 'prompts/checkout.prompt.md', verdict: 'pass', summary: 'Clear contract.', issues: [] },
        { path: 'user_stories/checkout.md', verdict: 'pass', summary: 'Aligned Story.', issues: [] },
      ],
      issue_coverage: {
        status: 'fail',
        summary: `Currency mismatch rejection is missing (saw ${secretToken}).`,
        missed: [{
          requirement: 'Reject currency mismatch',
          rule: 'issue-requirement-missed',
          message: `Add a currency mismatch rule and scenario case without exposing ${secretToken}.`,
        }],
      },
    }));
    return { code: 0, stdout: '', stderr: '' };
  };

  const failIssueTextOut = sink(), failIssueTextErr = sink();
  const failIssueTextCode = await runCodexLint(
    { cwd: repo, words: ['checkout'], issue: '42', json: false, env },
    { stdout: failIssueTextOut, stderr: failIssueTextErr, runAgentProcess: failIssueRunner, readIssue: readIssuePort },
  );
  assert.equal(failIssueTextCode, 1);
  assert.match(failIssueTextOut.text, /Issue coverage \(#42\): FAIL — Currency mismatch rejection is missing/);
  assert.match(failIssueTextOut.text, /\[issue-requirement-missed\] Reject currency mismatch: Add a currency mismatch rule/);
  assert.match(failIssueTextOut.text, /Lint \(Codex\): FAIL \(2\/2 files passed, issue coverage failed\)/);
  assert.ok(!failIssueTextOut.text.includes(secretToken), 'issue_coverage output must be redacted');

  const failIssueJsonOut = sink(), failIssueJsonErr = sink();
  const failIssueJsonCode = await runCodexLint(
    { cwd: repo, words: ['checkout'], issue: '42', json: true, env },
    { stdout: failIssueJsonOut, stderr: failIssueJsonErr, runAgentProcess: failIssueRunner, readIssue: readIssuePort },
  );
  assert.equal(failIssueJsonCode, 1);
  const failIssueJson = JSON.parse(failIssueJsonOut.text);
  assert.equal(failIssueJson.ok, false);
  assert.equal(failIssueJson.exit_code, 1);
  assert.equal(failIssueJson.issue_coverage.ref, '#42');
  assert.equal(failIssueJson.issue_coverage.status, 'fail');
  assert.equal(failIssueJson.issue_coverage.missed[0].rule, 'issue-requirement-missed');
  assert.ok(!failIssueJsonOut.text.includes(secretToken));

  // Fail closed when Codex omits issue_coverage.
  const omittedCoverageRunner = async (_cmd, args) => {
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [
        { path: 'prompts/checkout.prompt.md', verdict: 'pass', summary: 'Clear.', issues: [] },
        { path: 'user_stories/checkout.md', verdict: 'pass', summary: 'Clear.', issues: [] },
      ],
    }));
    return { code: 0, stdout: '', stderr: '' };
  };
  const omitOut = sink(), omitErr = sink();
  const omitCode = await runCodexLint(
    { cwd: repo, words: ['checkout'], issue: '42', json: false, env },
    { stdout: omitOut, stderr: omitErr, runAgentProcess: omittedCoverageRunner, readIssue: readIssuePort },
  );
  assert.equal(omitCode, 1);
  assert.match(omitErr.text, /omitted or returned invalid issue_coverage/);

  // 3. --issue <local file>: valid read + secret redaction, symlink refusal, escaping path refusal, oversized & secret file refusal.
  const fileIssueCalls = [];
  const fileIssueRunner = async (_cmd, args, opts) => {
    fileIssueCalls.push(opts.input);
    const outFile = args[args.indexOf('--output-last-message') + 1];
    writeFileSync(outFile, JSON.stringify({
      files: [
        { path: 'prompts/checkout.prompt.md', verdict: 'pass', summary: 'Clear.', issues: [] },
        { path: 'user_stories/checkout.md', verdict: 'pass', summary: 'Clear.', issues: [] },
      ],
      issue_coverage: { status: 'pass', summary: 'Covered.', missed: [] },
    }));
    return { code: 0, stdout: '', stderr: '' };
  };
  const fileOut = sink(), fileErr = sink();
  const fileCode = await runCodexLint(
    { cwd: repo, words: ['checkout'], issue: 'docs/issue-42.md', json: false, env },
    { stdout: fileOut, stderr: fileErr, runAgentProcess: fileIssueRunner },
  );
  assert.equal(fileCode, 0, fileErr.text);
  assert.match(fileIssueCalls[0], /Ref: docs\/issue-42\.md/);
  assert.ok(!fileIssueCalls[0].includes(secretToken), 'local issue file secrets must be redacted');
  assert.match(fileOut.text, /Issue coverage \(docs\/issue-42\.md\): PASS — Covered\./);

  let unexpectedCodexCalls = 0;
  const neverCalledRunner = async () => {
    unexpectedCodexCalls += 1;
    return { code: 0, stdout: '', stderr: '' };
  };
  for (const badIssue of [
    'docs/symlink-issue.md',
    'docs/symlink-dir/outside-issue.md',
    '../outside-issue.md',
    outsideFile,
    'docs/oversized-issue.md',
    '.env',
    'docs/does-not-exist.md',
    '0',
  ]) {
    const err = sink();
    const code = await runCodexLint(
      { cwd: repo, words: ['checkout'], issue: badIssue, env },
      { stdout: sink(), stderr: err, runAgentProcess: neverCalledRunner },
    );
    assert.equal(code, 2, `expected exit 2 for bad --issue ${badIssue}, got ${code}: ${err.text}`);
  }
  assert.equal(unexpectedCodexCalls, 0, 'invalid --issue values must fail before invoking Codex');

  // 4. CLI dispatch refuses --issue without --codex with exit 2 and advertises --issue in help.
  for (const argv of [
    ['lint', '--issue', '42'],
    ['lint', '--local', '--issue', '42'],
    ['test', '--issue', '42'],
    ['test', '--codex', '--issue', '42'],
  ]) {
    const err = sink();
    const code = await runPdd(argv, { cwd: repo, env, stdout: sink(), stderr: err });
    assert.equal(code, 2, `expected exit 2 for pdd ${argv.join(' ')}`);
    assert.match(err.text, /pdd lint --codex/);
  }
  assert.match(renderHelp(['lint']), /--issue N\|FILE/);
});

test('3571 repo-wide runCodexLint (words: []) builds promptsByStory across >6 files and ignores verdicts for contextOnly shared prompts', async t => {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-semantic-wide-3571-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  for (const dir of [home, state, join(repo, 'prompts'), join(repo, 'user_stories'), join(repo, 'tests')]) {
    mkdirSync(dir, { recursive: true });
  }

  // 2 Stories sharing prompts/shared.prompt.md plus 5 distinct prompts = 8 files total -> 2 batches.
  for (const name of ['a1', 'a2', 'a3', 'b1', 'b2', 'shared']) {
    writeFileSync(join(repo, `prompts/${name}.prompt.md`), `# ${name}\n\nBehavior for ${name}.\n\n## Dependencies\n\nNone.\n`);
  }
  writeFileSync(
    join(repo, 'user_stories/story-a.md'),
    '# Story A\n\nAs a shopper, I want A, so that A works.\n\n## Acceptance criteria\n\n1. A returns ok.\n',
  );
  writeFileSync(
    join(repo, 'user_stories/story-b.md'),
    '# Story B\n\nAs a shopper, I want B, so that B works.\n\n## Acceptance criteria\n\n1. B returns ok.\n',
  );
  writeFileSync(
    join(repo, 'tests/story-a.json'),
    JSON.stringify({
      schema_version: 'pdd.scenario.short.v1',
      entry_paths: ['prompts/a1.prompt.md', 'prompts/a2.prompt.md', 'prompts/a3.prompt.md', 'prompts/shared.prompt.md'],
      steps: [{ op: 'run', input: {}, checks: [['1', 'result', '/ok', '=', true]] }],
    }, null, 2) + '\n',
  );
  writeFileSync(
    join(repo, 'tests/story-b.json'),
    JSON.stringify({
      schema_version: 'pdd.scenario.short.v1',
      entry_paths: ['prompts/b1.prompt.md', 'prompts/b2.prompt.md', 'prompts/shared.prompt.md'],
      steps: [{ op: 'run', input: {}, checks: [['1', 'result', '/ok', '=', true]] }],
    }, null, 2) + '\n',
  );
  initGitRepo(repo);

  const batchInputs = [];
  const multiBatchRunner = async (_cmd, args, opts) => {
    batchInputs.push(opts.input);
    const outFile = args[args.indexOf('--output-last-message') + 1];
    if (batchInputs.length === 1) {
      writeFileSync(outFile, JSON.stringify({
        files: [
          { path: 'prompts/a1.prompt.md', verdict: 'pass', summary: 'Clean a1.', issues: [] },
          { path: 'prompts/a2.prompt.md', verdict: 'pass', summary: 'Clean a2.', issues: [] },
          { path: 'prompts/a3.prompt.md', verdict: 'pass', summary: 'Clean a3.', issues: [] },
          { path: 'prompts/shared.prompt.md', verdict: 'pass', summary: 'Original batch-1 verdict for shared.', issues: [] },
          { path: 'user_stories/story-a.md', verdict: 'pass', summary: 'Aligned Story A.', issues: [] },
        ],
      }));
    } else {
      // Deliberately emit a stray FAIL row for contextOnly shared.prompt.md in batch 2 to prove it is ignored.
      writeFileSync(outFile, JSON.stringify({
        files: [
          { path: 'prompts/b1.prompt.md', verdict: 'pass', summary: 'Clean b1.', issues: [] },
          { path: 'prompts/b2.prompt.md', verdict: 'pass', summary: 'Clean b2.', issues: [] },
          { path: 'prompts/shared.prompt.md', verdict: 'fail', summary: 'STRAY OVERWRITE MUST BE IGNORED', issues: [{ line: 1, rule: 'prompt-readability', message: 'Stray.' }] },
          { path: 'user_stories/story-b.md', verdict: 'pass', summary: 'Aligned Story B.', issues: [] },
        ],
      }));
    }
    return { code: 0, stdout: '', stderr: '' };
  };

  const out = sink(), err = sink();
  const code = await runCodexLint(
    { cwd: repo, words: [], json: true, env: { HOME: home, PDD_STATE_DIR: state } },
    { stdout: out, stderr: err, runAgentProcess: multiBatchRunner },
  );
  assert.equal(code, 0, err.text);
  assert.equal(batchInputs.length, 2);
  assert.match(batchInputs[0], /=== STORY-PROMPT PAIRS ===[\s\S]*story-a\.md -> Prompts:[^\n]*prompts\/shared\.prompt\.md/);
  assert.match(batchInputs[1], /=== STORY-PROMPT PAIRS ===[\s\S]*story-b\.md -> Prompts:[^\n]*prompts\/shared\.prompt\.md/);
  assert.match(batchInputs[1], /=== FILE: prompts\/shared\.prompt\.md \(kind: prompt, context-only/);

  const parsed = JSON.parse(out.text);
  assert.equal(parsed.ok, true);
  assert.equal(parsed.passed, 8);
  assert.equal(parsed.failed, 0);
  const sharedRow = parsed.files.find(f => f.path === 'prompts/shared.prompt.md');
  assert.equal(sharedRow?.status, 'pass');
  assert.equal(sharedRow?.summary, 'Original batch-1 verdict for shared.');

  // Multi-batch --issue run includes === OTHER SELECTED FILES === context and merges issue_coverage across batches.
  const multiIssueInputs = [];
  const multiIssueRunner = async (_cmd, args, opts) => {
    multiIssueInputs.push(opts.input);
    const outFile = args[args.indexOf('--output-last-message') + 1];
    if (multiIssueInputs.length === 1) {
      writeFileSync(outFile, JSON.stringify({
        files: [
          { path: 'prompts/a1.prompt.md', verdict: 'pass', summary: 'Ok.', issues: [] },
          { path: 'prompts/a2.prompt.md', verdict: 'pass', summary: 'Ok.', issues: [] },
          { path: 'prompts/a3.prompt.md', verdict: 'pass', summary: 'Ok.', issues: [] },
          { path: 'prompts/shared.prompt.md', verdict: 'pass', summary: 'Ok.', issues: [] },
          { path: 'user_stories/story-a.md', verdict: 'pass', summary: 'Ok.', issues: [] },
        ],
        issue_coverage: { status: 'pass', summary: 'Batch 1 covered.', missed: [] },
      }));
    } else {
      writeFileSync(outFile, JSON.stringify({
        files: [
          { path: 'prompts/b1.prompt.md', verdict: 'pass', summary: 'Ok.', issues: [] },
          { path: 'prompts/b2.prompt.md', verdict: 'pass', summary: 'Ok.', issues: [] },
          { path: 'user_stories/story-b.md', verdict: 'pass', summary: 'Ok.', issues: [] },
        ],
        issue_coverage: {
          status: 'fail',
          summary: 'Missing timeout edge case.',
          missed: [{ requirement: 'Timeout handling', rule: 'issue-requirement-missed', message: 'Add timeout rule.' }],
        },
      }));
    }
    return { code: 0, stdout: '', stderr: '' };
  };
  const multiIssueOut = sink(), multiIssueErr = sink();
  const multiIssueCode = await runCodexLint(
    { cwd: repo, words: [], issue: '99', json: true, env: { HOME: home, PDD_STATE_DIR: state } },
    {
      stdout: multiIssueOut,
      stderr: multiIssueErr,
      runAgentProcess: multiIssueRunner,
      readIssue: async () => ({ number: 99, title: 'Multi story feature', body: 'Need A, B, and timeout handling.' }),
    },
  );
  assert.equal(multiIssueCode, 1, multiIssueErr.text);
  assert.equal(multiIssueInputs.length, 2);
  assert.match(multiIssueInputs[0], /=== OTHER SELECTED FILES/);
  assert.match(multiIssueInputs[0], /OUTLINE: user_stories\/story-b\.md/);
  assert.match(multiIssueInputs[1], /=== OTHER SELECTED FILES/);
  assert.match(multiIssueInputs[1], /OUTLINE: user_stories\/story-a\.md/);
  const multiIssueParsed = JSON.parse(multiIssueOut.text);
  assert.equal(multiIssueParsed.ok, false);
  assert.equal(multiIssueParsed.issue_coverage.status, 'fail');
  assert.equal(multiIssueParsed.issue_coverage.missed.length, 1);
  assert.equal(multiIssueParsed.issue_coverage.missed[0].requirement, 'Timeout handling');
});

test('3571 PR 1 skill steps reference review.md and advisory pdd lint --codex --issue preflight', () => {
  const root = new URL('..', import.meta.url);
  for (const rel of [
    'skills/pdd-feature/steps/prompt-story.md',
    'skills/pdd-feature/steps/check.md',
    'skills/pdd-bug/steps/prompt-story.md',
    'skills/pdd-bug/steps/check.md',
  ]) {
    const content = readFileSync(new URL(rel, root), 'utf8');
    assert.match(content, /review\.md/, `${rel} should reference review.md`);
    assert.match(content, /pdd lint --codex <story> --issue <N>/, `${rel} should reference pdd lint --codex <story> --issue <N>`);
  }
});
