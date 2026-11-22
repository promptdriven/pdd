import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  existsSync,
  mkdtempSync,
  mkdirSync,
  readdirSync,
  readFileSync,
  rmSync,
  statSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const RUN_REVIEW_EVAL_SCRIPT = fileURLToPath(new URL('../scripts/benchmark/run-review-eval.mjs', import.meta.url));

import {
  ALLOWED_FIXTURE_EVIDENCE_KEYS,
  CliUsageError,
  DEFAULT_MANIFEST_PATH,
  FORBIDDEN_SCRATCH_PATHS,
  REVIEW_EVAL_TARGETS,
  assertCleanPublicText,
  assertPromptIsolation,
  assertSafeCheckedOutSymlink,
  buildReviewerPrompt,
  computeReviewEvalScorecard,
  createCliReviewerRunner,
  inspectFixtureDiffReadOnly,
  loadReviewEvalManifest,
  matchDefectSignals,
  parseReviewEvalCliArgs,
  parseReviewerOutput,
  prepareScratchCheckout,
  projectAllowedFixtureEvidence,
  renderReviewEvalMarkdown,
  runReviewEval,
  scoreReviewCase,
  validateFixtureSpec,
  validateGitRef,
} from '../scripts/benchmark/run-review-eval.mjs';

function gitIn(dir, args) {
  const res = spawnSync('git', args, {
    cwd: dir,
    encoding: 'utf8',
    env: {
      ...process.env,
      GIT_CONFIG_NOSYSTEM: '1',
      GIT_TERMINAL_PROMPT: '0',
    },
  });
  assert.equal(res.status, 0, `git ${args.join(' ')} failed: ${res.stderr || res.stdout}`);
  return res.stdout.trim();
}

function makeSyntheticManifest() {
  return {
    schema_version: 'pdd.review-eval-manifest.v1',
    fixtures: [
      {
        id: 'case-bad-symlink',
        label: 'bad',
        repo: 'promptdriven/pdd',
        pr: 2559,
        issue: 2444,
        base: 'a1b09cb9',
        head: '0db39638',
        issue_title: 'Open PR fails under symlinked repo',
        issue_body: 'Resolve realpath for worktree root and add a symlinked repo test.',
        pr_title: 'Fix symlinked repo open PR',
        pr_body: 'Updates workflow github body handling.',
        expected_signals: [
          {
            id: 'deleted-safety-tests',
            description: 'CANARY_SIGNAL_DELETED_SAFETY_TESTS_991',
            any_all_of: [[['deleted', 'removed'], ['safety', '19'], ['test', 'tests']]],
          },
          {
            id: 'missing-real-symlink-test',
            description: 'CANARY_SIGNAL_MISSING_SYMLINK_TEST_992',
            any_all_of: [[['missing', 'no', 'without'], ['symlink', 'symlinked'], ['test', 'tests']]],
          },
          {
            id: 'wrong-reason-pass',
            description: 'CANARY_SIGNAL_WRONG_REASON_PASS_993',
            any_all_of: [[['wrong reason', 'wrong-reason']]],
          },
        ],
        min_signals_required: 1,
      },
      {
        id: 'case-clean-guidance',
        label: 'clean',
        repo: 'promptdriven/pdd',
        pr: 2560,
        issue: 2438,
        base: '515dae711',
        head: '1a4b37803',
        issue_title: 'Explain missing workflow name',
        issue_body: 'When first arg is numeric, explain that workflow name is missing.',
        pr_title: 'fix: explain missing workflow name',
        pr_body: 'Adds parser guard and regression tests.',
        expected_signals: [],
      },
    ],
  };
}

function stubScratchPort() {
  const cleanedIds = [];
  return {
    cleanedIds,
    prepareScratch({ fixture }) {
      return {
        scratchDir: join(tmpdir(), `stub-scratch-${fixture.id}`),
        resultPath: null,
        changedFiles: ['M\tsrc/example.mjs', 'M\ttest/example.test.mjs'],
        diffStat: ' src/example.mjs | 4 ++--\n 1 file changed, 2 insertions(+), 2 deletions(-)',
        diffExcerpt: 'diff --git a/src/example.mjs b/src/example.mjs\n@@ -1 +1 @@\n-old\n+new',
        cleanup() {
          cleanedIds.push(fixture.id);
        },
      };
    },
  };
}

test('default manifest seeds #2559 bad PR and #2560 clean control with valid schema', () => {
  const manifest = loadReviewEvalManifest(DEFAULT_MANIFEST_PATH);
  assert.equal(manifest.schema_version, 'pdd.review-eval-manifest.v1');
  assert.ok(manifest.fixtures.length >= 2);

  const bad2559 = manifest.fixtures.find(f => f.pr === 2559);
  assert.ok(bad2559, 'Manifest must include bad PR #2559');
  assert.equal(bad2559.label, 'bad');
  assert.ok(bad2559.base.startsWith('a1b09cb9'));
  assert.ok(bad2559.head.startsWith('0db39638'));
  assert.equal(bad2559.issue, 2444);
  const signalIds = bad2559.expected_signals.map(s => s.id);
  assert.ok(signalIds.includes('deleted-safety-tests'));
  assert.ok(signalIds.includes('missing-real-symlink-test'));
  assert.ok(signalIds.includes('wrong-reason-pass'));

  const clean2560 = manifest.fixtures.find(f => f.pr === 2560);
  assert.ok(clean2560, 'Manifest must include clean control PR #2560');
  assert.equal(clean2560.label, 'clean');
  assert.ok(clean2560.base.startsWith('515dae711'));
  assert.ok(clean2560.head.startsWith('1a4b37803'));
  assert.equal(clean2560.issue, 2438);
  assert.deepEqual(clean2560.expected_signals, []);
});

test('manifest validation supports string signals and merge_commit while rejecting bad inputs and unsafe refs', () => {
  const spec = validateFixtureSpec({
    id: 'hist-merge-1',
    label: 'bad',
    merge_commit: '5d47451e4',
    expected_signals: ['deleted safety tests', 'missing null check'],
  });
  assert.equal(spec.base, '5d47451e4^1');
  assert.equal(spec.head, '5d47451e4^2');
  assert.equal(spec.expected_signals.length, 2);
  assert.equal(spec.min_signals_required, 1);

  assert.throws(() => validateGitRef('--upload-pack=evil'), /Unsafe or invalid/);
  assert.throws(() => validateGitRef('abc..def'), /Unsafe or invalid/);
  assert.throws(() => validateGitRef('HEAD@{1}'), /Unsafe or invalid/);
  assert.throws(() => validateGitRef('main;rm -rf /'), /Unsafe or invalid/);

  assert.throws(() => validateFixtureSpec({
    id: 'bad-label',
    label: 'maybe',
    base: 'a1b09cb9',
    head: '0db39638',
  }), /invalid label/);

  assert.throws(() => validateFixtureSpec({
    id: 'clean-with-signals',
    label: 'clean',
    base: 'a1b09cb9',
    head: '0db39638',
    expected_signals: ['should not be here'],
  }), /must not define expected_signals/);

  assert.throws(() => validateFixtureSpec({
    id: 'regex-signal',
    label: 'bad',
    base: 'a1b09cb9',
    head: '0db39638',
    expected_signals: [{ id: 'evil', patterns: ['(a+)+b'] }],
  }), /Refusing regex syntax/);

  // Safe literal/wildcard/alternation patterns work without RegExp
  const wildcardSpec = validateFixtureSpec({
    id: 'wildcard-signal',
    label: 'bad',
    base: 'a1b09cb9',
    head: '0db39638',
    expected_signals: [{ id: 'wild', patterns: ['deleted * safety tests|removed * safety tests'] }],
  });
  assert.deepEqual(
    matchDefectSignals(['P1 test/a.test.mjs:1 Removed 19 existing safety tests'], wildcardSpec.expected_signals).matched_signals,
    ['wild'],
  );
  assert.deepEqual(
    matchDefectSignals(['P1 test/a.test.mjs:1 Formatting nit'], wildcardSpec.expected_signals).matched_signals,
    [],
  );

  // Reject min_signals_required === 0 when expected_signals is non-empty, and > 0 when empty
  assert.throws(() => validateFixtureSpec({
    id: 'bad-zero-min',
    label: 'bad',
    base: 'a1b09cb9',
    head: '0db39638',
    expected_signals: ['deleted safety tests'],
    min_signals_required: 0,
  }), /invalid min_signals_required/);

  assert.throws(() => validateFixtureSpec({
    id: 'empty-nonzero-min',
    label: 'bad',
    base: 'a1b09cb9',
    head: '0db39638',
    expected_signals: [],
    min_signals_required: 1,
  }), /invalid min_signals_required/);

  assert.throws(() => loadReviewEvalManifest({
    fixtures: [
      { id: 'dup-id', label: 'clean', base: 'a1b09cb9', head: '0db39638' },
      { id: 'dup-id', label: 'clean', base: 'a1b09cb9', head: '0db39638' },
    ],
  }), /Duplicate fixture id/);
});

test('parseReviewerOutput follows fail-closed P1/P2/P3 verdict rules and handles fenced, embedded escaped JSON, and manual markdown', () => {
  // PASS with P1 blocking item -> FAIL
  const passWithP1 = parseReviewerOutput({
    verdict: 'PASS',
    summary: 'Looks fine except one bug.',
    mustFix: ['P1 src/a.mjs:10 Null dereference'],
  });
  assert.equal(passWithP1.verdict, 'FAIL');
  assert.equal(passWithP1.mustFix.length, 1);

  // FAIL with P3-only follow-ups -> PASS
  const failWithP3Only = parseReviewerOutput({
    verdict: 'FAIL',
    summary: 'Only minor follow-up.',
    mustFix: ['P3 src/a.mjs:20 Consider renaming local variable'],
  });
  assert.equal(failWithP3Only.verdict, 'PASS');
  assert.equal(failWithP3Only.mustFix.length, 0);
  assert.equal(failWithP3Only.followUps.length, 1);

  // FAIL with empty mustFix stays FAIL (fail-closed)
  const bareFail = parseReviewerOutput({ verdict: 'FAIL', summary: 'Broken', mustFix: [] });
  assert.equal(bareFail.verdict, 'FAIL');

  // Embedded JSON in noisy stdout containing escaped quotes \"
  const noisyStdout = [
    'Inspecting diff...',
    'Result: {"verdict":"FAIL","summary":"Fix \\"broken\\" symlink check","mustFix":["P1 test/workflow-github.test.mjs:1 Removed \\"19\\" safety tests"]}',
    'Done.',
  ].join('\n');
  const parsedNoisy = parseReviewerOutput(noisyStdout);
  assert.equal(parsedNoisy.verdict, 'FAIL');
  assert.match(parsedNoisy.summary, /Fix "broken" symlink check/);
  assert.equal(parsedNoisy.mustFix.length, 1);

  // Fenced JSON block
  const fenced = 'Review complete:\n```json\n{"verdict":"PASS","summary":"Clean","mustFix":[]}\n```';
  assert.equal(parseReviewerOutput(fenced).verdict, 'PASS');

  // Manual review markdown format
  assert.equal(parseReviewerOutput('Review: no must-fix\nAll checks verified.').verdict, 'PASS');
  const manualFail = parseReviewerOutput('Review: 2 must-fix\n- P1 deleted 19 safety tests\n- P2 missing real symlink test');
  assert.equal(manualFail.verdict, 'FAIL');
  assert.equal(manualFail.mustFix.length, 2);

  // Unparseable output -> ERROR
  const malformed = parseReviewerOutput('not valid review output at all');
  assert.equal(malformed.verdict, 'ERROR');
  assert.ok(malformed.parse_error);
});

test('scoring computes bug_recall, clean_fp_rate, signal_recall, and handles edge cases (0 bad, 0 clean, FAIL without signal, P3 demotion, rounding)', () => {
  const manifest = loadReviewEvalManifest(makeSyntheticManifest());
  const badFix = manifest.fixtures[0];
  const cleanFix = manifest.fixtures[1];

  // Word-boundary signal guard: "no" must NOT match "canonical" or "annotation"
  const falseWordMatch = matchDefectSignals(
    ['P2 src/workflow-github.mjs:5 Canonical path annotation needs a symlink comment'],
    badFix.expected_signals,
  );
  assert.deepEqual(falseWordMatch.matched_signals, []);

  // Case 1: Bad PR caught with matching defect signal
  const caughtCase = scoreReviewCase({
    fixture: badFix,
    parsedReview: parseReviewerOutput({
      verdict: 'FAIL',
      summary: 'Multiple safety regressions.',
      mustFix: [
        'P1 test/workflow-github.test.mjs:1 Deleted 19 safety tests without reason',
        'P1 test/workflow-github.test.mjs:20 Missing a real symlinked repository test',
      ],
    }),
    model: 'model-a',
    promptVersion: 'autopilot-v1',
  });
  assert.equal(caughtCase.outcome, 'caught_bad');
  assert.equal(caughtCase.caught, true);
  assert.deepEqual(caughtCase.matched_signals, ['deleted-safety-tests', 'missing-real-symlink-test']);

  // Case 2: Bad PR flagged FAIL for unrelated style nit (NO matching defect signal -> NOT recalled!)
  const failWrongSignal = scoreReviewCase({
    fixture: badFix,
    parsedReview: parseReviewerOutput({
      verdict: 'FAIL',
      summary: 'Formatting issue.',
      mustFix: ['P2 src/workflow-github.mjs:4 Remove trailing whitespace'],
    }),
    model: 'model-b',
    promptVersion: 'autopilot-v1',
  });
  assert.equal(failWrongSignal.verdict, 'FAIL');
  assert.equal(failWrongSignal.outcome, 'fail_wrong_signal');
  assert.equal(failWrongSignal.caught, false);
  assert.deepEqual(failWrongSignal.matched_signals, []);

  // Case 3: Bad PR where real defect is demoted to P3 non-blocking follow-up -> becomes PASS, NOT caught!
  const demotedP3 = scoreReviewCase({
    fixture: badFix,
    parsedReview: parseReviewerOutput({
      verdict: 'PASS',
      summary: 'Passed with follow-up.',
      mustFix: ['P3 test/workflow-github.test.mjs:1 Deleted 19 safety tests could be restored later'],
    }),
    model: 'model-b',
    promptVersion: 'autopilot-v1',
  });
  assert.equal(demotedP3.verdict, 'PASS');
  assert.equal(demotedP3.outcome, 'missed_bad');
  assert.equal(demotedP3.caught, false);

  // Case 4: Partial signal match when min_signals_required = 2 and only 1 matches
  const strictBad = validateFixtureSpec({
    ...makeSyntheticManifest().fixtures[0],
    min_signals_required: 2,
  });
  const partialCase = scoreReviewCase({
    fixture: strictBad,
    parsedReview: parseReviewerOutput({
      verdict: 'FAIL',
      summary: 'Partial catch.',
      mustFix: ['P1 test/workflow-github.test.mjs:1 Deleted 19 safety tests'],
    }),
  });
  assert.equal(partialCase.outcome, 'fail_partial_signal');
  assert.equal(partialCase.caught, false);

  // Case 5: Clean control PASS vs clean control FP
  const cleanPass = scoreReviewCase({
    fixture: cleanFix,
    parsedReview: parseReviewerOutput({ verdict: 'PASS', summary: 'Clean PR', mustFix: [] }),
    model: 'model-a',
    promptVersion: 'autopilot-v1',
  });
  assert.equal(cleanPass.outcome, 'clean_pass');
  assert.equal(cleanPass.false_positive, false);

  const cleanFp = scoreReviewCase({
    fixture: cleanFix,
    parsedReview: parseReviewerOutput({
      verdict: 'FAIL',
      summary: 'False alarm',
      mustFix: ['P2 src/argument-parser.mjs:12 Prefer ternary expression'],
    }),
    model: 'model-b',
    promptVersion: 'autopilot-v1',
  });
  assert.equal(cleanFp.outcome, 'clean_false_positive');
  assert.equal(cleanFp.false_positive, true);

  // Edge case: 0 bad cases
  const onlyClean = computeReviewEvalScorecard([cleanPass]);
  assert.equal(onlyClean.bad_total, 0);
  assert.equal(onlyClean.bug_recall, null);
  assert.equal(onlyClean.clean_total, 1);
  assert.equal(onlyClean.clean_fp_rate, 0);
  assert.equal(onlyClean.meets_target, false);

  // Edge case: 0 clean cases
  const onlyBad = computeReviewEvalScorecard([caughtCase]);
  assert.equal(onlyBad.bad_total, 1);
  assert.equal(onlyBad.bug_recall, 100);
  assert.equal(onlyBad.clean_total, 0);
  assert.equal(onlyBad.clean_fp_rate, null);
  assert.equal(onlyBad.meets_target, false);

  // Edge case: empty cases
  const emptyCard = computeReviewEvalScorecard([]);
  assert.equal(emptyCard.bug_recall, null);
  assert.equal(emptyCard.clean_fp_rate, null);
  assert.equal(emptyCard.meets_target, false);

  // Edge case: FAIL without signal lowers bug_recall to 0%
  const wrongSignalCard = computeReviewEvalScorecard([failWrongSignal, cleanPass]);
  assert.equal(wrongSignalCard.bug_recall, 0);
  assert.equal(wrongSignalCard.bad_failed_without_signal, 1);
  assert.equal(wrongSignalCard.clean_fp_rate, 0);
  assert.equal(wrongSignalCard.meets_target, false);

  // Edge case: raw unrounded target boundary (1599/2000 = 79.95% rounds to 80.0% but does NOT meet >= 80.0%)
  const rawBoundaryCases = [
    ...Array.from({ length: 1599 }, () => ({ label: 'bad', verdict: 'FAIL', caught: true, expected_signals_count: 1, matched_signals: ['x'] })),
    ...Array.from({ length: 401 }, () => ({ label: 'bad', verdict: 'PASS', caught: false, expected_signals_count: 1, matched_signals: [] })),
    { label: 'clean', verdict: 'PASS', false_positive: false },
  ];
  const boundaryCard = computeReviewEvalScorecard(rawBoundaryCases);
  assert.equal(boundaryCard.bug_recall, 80);
  assert.equal(boundaryCard.meets_target, false);
});

test('strict fixture isolation excludes expected_signals, label, fixture id, and manual guide from reviewer prompt and context', async () => {
  const manifest = loadReviewEvalManifest(makeSyntheticManifest());
  const badFixture = manifest.fixtures[0];
  const cleanFixture = manifest.fixtures[1];

  // Projection allows ONLY allowed public PR/issue evidence keys
  const projected = projectAllowedFixtureEvidence(badFixture);
  assert.deepEqual(
    Object.keys(projected).sort(),
    [...ALLOWED_FIXTURE_EVIDENCE_KEYS].sort(),
  );
  assert.equal('label' in projected, false);
  assert.equal('expected_signals' in projected, false);
  assert.equal('id' in projected, false);
  assert.equal('base' in projected, false);
  assert.equal('head' in projected, false);

  // Both built-in prompt versions never leak forbidden values
  for (const version of ['autopilot-v1', 'strict-checklist-v1']) {
    for (const fixture of [badFixture, cleanFixture]) {
      const prompt = buildReviewerPrompt({
        fixture,
        changedFiles: ['M\tsrc/workflow-github.mjs', 'M\ttest/manual/independent-code-review.md'],
        diffStat: ' src/workflow-github.mjs | 10 +++-------',
        promptVersion: version,
      });
      assert.ok(!prompt.includes('CANARY_SIGNAL_DELETED_SAFETY_TESTS_991'));
      assert.ok(!prompt.includes('CANARY_SIGNAL_MISSING_SYMLINK_TEST_992'));
      assert.ok(!prompt.includes('CANARY_SIGNAL_WRONG_REASON_PASS_993'));
      assert.ok(!prompt.includes('deleted-safety-tests'));
      assert.ok(!prompt.includes('missing-real-symlink-test'));
      assert.ok(!prompt.includes('wrong-reason-pass'));
      assert.ok(!prompt.includes(fixture.id));
      assert.ok(!prompt.includes('expected_signals'));
      assert.ok(!prompt.includes('test/manual/independent-code-review.md'));
      assert.ok(!/\blabel\s*[:=]\s*["']?(?:bad|clean)["']?/i.test(prompt));
      assert.ok(!/\bclean[_\s-]control\b/i.test(prompt));
    }
  }

  // assertPromptIsolation actively catches leaks
  assert.throws(
    () => assertPromptIsolation('Read test/manual/independent-code-review.md first', badFixture),
    err => err.code === 'EVAL_ISOLATION_VIOLATION',
  );
  assert.throws(
    () => assertPromptIsolation('Check expected_signals carefully', badFixture),
    err => err.code === 'EVAL_ISOLATION_VIOLATION',
  );
  assert.throws(
    () => assertPromptIsolation('This PR has label: bad', badFixture),
    err => err.code === 'EVAL_ISOLATION_VIOLATION',
  );
  assert.throws(
    () => assertPromptIsolation('Look for CANARY_SIGNAL_DELETED_SAFETY_TESTS_991', badFixture),
    err => err.code === 'EVAL_ISOLATION_VIOLATION',
  );

  // End-to-end runReviewEval enforces isolation and re-throws isolation breach while cleaning up scratch dir
  const capturedInputs = [];
  const stub = stubScratchPort();
  await runReviewEval(
    { manifest: makeSyntheticManifest(), models: ['test-model'], promptVersions: ['autopilot-v1'] },
    {
      prepareScratch: stub.prepareScratch,
      runReviewer: input => {
        capturedInputs.push(input);
        return { verdict: 'PASS', summary: 'ok', mustFix: [] };
      },
    },
  );
  assert.equal(capturedInputs.length, 2);
  for (const input of capturedInputs) {
    assert.equal(input.fixture.label, undefined);
    assert.equal(input.fixture.expected_signals, undefined);
    assert.equal(input.fixture.id, undefined);
    assert.ok(!input.prompt.includes('CANARY_SIGNAL_'));
    assert.ok(!input.prompt.includes('expected_signals'));
    assert.ok(!input.prompt.includes('test/manual/independent-code-review.md'));
  }
  assert.deepEqual(stub.cleanedIds, ['case-bad-symlink', 'case-clean-guidance']);

  // Custom prompt template that leaks forbidden path must fail loudly AND still clean up scratch dir
  const tmp = mkdtempSync(join(tmpdir(), 'pdd-eval-iso-'));
  try {
    const leakyTpl = join(tmp, 'leaky.txt');
    writeFileSync(leakyTpl, 'Please inspect test/manual/independent-code-review.md.\n{{EVIDENCE}}', 'utf8');
    const leakyStub = stubScratchPort();
    await assert.rejects(
      () => runReviewEval(
        { manifest: makeSyntheticManifest(), promptTemplate: leakyTpl },
        {
          prepareScratch: leakyStub.prepareScratch,
          runReviewer: () => ({ verdict: 'PASS', summary: 'ok', mustFix: [] }),
        },
      ),
      err => err.code === 'EVAL_ISOLATION_VIOLATION',
    );
    assert.deepEqual(leakyStub.cleanedIds, ['case-bad-symlink']);
  } finally {
    rmSync(tmp, { recursive: true, force: true });
  }
});

test('prepareScratchCheckout creates read-only isolated git repo, strips forbidden files, leaves caller untouched, and cleans up in finally', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-eval-git-'));
  const workDirRoot = join(root, 'scratch-root');
  const repoDir = join(root, 'caller-repo');
  mkdirSync(workDirRoot, { recursive: true });
  mkdirSync(repoDir, { recursive: true });
  t.after(() => rmSync(root, { recursive: true, force: true }));

  gitIn(repoDir, ['init', '-q']);
  gitIn(repoDir, ['config', 'user.name', 'Test User']);
  gitIn(repoDir, ['config', 'user.email', 'test@example.invalid']);
  gitIn(repoDir, ['config', 'commit.gpgsign', 'false']);

  // Base commit includes normal code AND forbidden evaluation/manual files
  mkdirSync(join(repoDir, 'src'), { recursive: true });
  mkdirSync(join(repoDir, 'test/manual'), { recursive: true });
  mkdirSync(join(repoDir, 'scripts/benchmark'), { recursive: true });
  writeFileSync(join(repoDir, 'src/app.mjs'), 'export const val = 1;\n');
  writeFileSync(join(repoDir, 'test/manual/independent-code-review.md'), 'SECRET EXPECTED FINDINGS\n');
  writeFileSync(join(repoDir, 'scripts/benchmark/review-eval-manifest.json'), '{"secret":true}\n');
  writeFileSync(join(repoDir, 'custom-eval-manifest.json'), '{"secret":true}\n');
  gitIn(repoDir, ['add', '.']);
  gitIn(repoDir, ['commit', '-qm', 'base']);
  const baseSha = gitIn(repoDir, ['rev-parse', 'HEAD']);

  // Head commit modifies src/app.mjs and also modifies the forbidden manual doc
  writeFileSync(join(repoDir, 'src/app.mjs'), 'export const val = 2;\n');
  writeFileSync(join(repoDir, 'test/manual/independent-code-review.md'), 'UPDATED SECRET EXPECTED FINDINGS\n');
  gitIn(repoDir, ['add', '.']);
  gitIn(repoDir, ['commit', '-qm', 'head']);
  const headSha = gitIn(repoDir, ['rev-parse', 'HEAD']);

  // Future revert commit on caller repo must NEVER be visible in scratch checkout
  writeFileSync(join(repoDir, 'src/app.mjs'), 'export const val = 1;\n');
  gitIn(repoDir, ['add', '.']);
  gitIn(repoDir, ['commit', '-qm', 'Revert bad change']);
  const callerHeadBefore = gitIn(repoDir, ['rev-parse', 'HEAD']);
  const callerIndexBefore = readFileSync(join(repoDir, '.git/index'));

  const fixture = validateFixtureSpec({
    id: 'real-scratch-case',
    label: 'bad',
    base: baseSha,
    head: headSha,
    expected_signals: ['changed val to 2'],
  });

  const scratch = prepareScratchCheckout({
    repoRoot: repoDir,
    fixture,
    workDirRoot,
    extraForbiddenPaths: ['custom-eval-manifest.json'],
    readOnly: true,
  });

  try {
    // Opaque scratch paths never leak fixture id or label
    assert.ok(!scratch.scratchDir.includes(fixture.id));
    assert.ok(!scratch.resultPath.includes(fixture.id));
    assert.ok(!scratch.scratchDir.includes(fixture.label));
    assert.ok(!scratch.resultPath.includes(fixture.label));

    // Caller repo completely untouched
    assert.equal(gitIn(repoDir, ['rev-parse', 'HEAD']), callerHeadBefore);
    assert.equal(gitIn(repoDir, ['status', '--porcelain']), '');
    assert.equal(Buffer.compare(readFileSync(join(repoDir, '.git/index')), callerIndexBefore), 0);

    // Scratch checkout has exact diff and strips all forbidden files from disk AND git trees
    assert.equal(readFileSync(join(scratch.scratchDir, 'src/app.mjs'), 'utf8'), 'export const val = 2;\n');
    for (const forbidden of [...FORBIDDEN_SCRATCH_PATHS, 'custom-eval-manifest.json']) {
      assert.equal(existsSync(join(scratch.scratchDir, forbidden)), false, `Expected ${forbidden} stripped from disk`);
    }
    const baseTree = gitIn(scratch.scratchDir, ['ls-tree', '-r', '--name-only', 'eval-base']);
    const headTree = gitIn(scratch.scratchDir, ['ls-tree', '-r', '--name-only', 'HEAD']);
    assert.ok(!baseTree.includes('independent-code-review.md'));
    assert.ok(!headTree.includes('independent-code-review.md'));
    assert.ok(!headTree.includes('review-eval-manifest.json'));
    assert.ok(!headTree.includes('custom-eval-manifest.json'));

    // Future revert commit is NOT in scratch history
    const logSubjects = gitIn(scratch.scratchDir, ['log', '--all', '--format=%s']);
    assert.ok(!logSubjects.includes('Revert bad change'));
    assert.deepEqual(scratch.changedFiles, ['M\tsrc/app.mjs']);
    assert.ok(!scratch.diffExcerpt.includes('SECRET EXPECTED FINDINGS'));

    // Tracked worktree file is read-only (no write bits on POSIX)
    if (process.platform !== 'win32') {
      const mode = statSync(join(scratch.scratchDir, 'src/app.mjs')).mode & 0o222;
      assert.equal(mode, 0, 'Scratch checkout file should be read-only');
    }
  } finally {
    scratch.cleanup();
  }

  // Cleanup removed both scratchDir and metaDir cleanly
  assert.deepEqual(readdirSync(workDirRoot), []);

  // Even when runReviewer throws, runReviewEval cleans up scratch checkout in finally
  const manifestObj = {
    schema_version: 'pdd.review-eval-manifest.v1',
    fixtures: [{ id: 'throw-cleanup-case', label: 'bad', base: baseSha, head: headSha, expected_signals: ['val'] }],
  };
  const errReport = await runReviewEval(
    { manifest: manifestObj, repoRoot: repoDir, workDirRoot },
    {
      runReviewer: () => {
        throw new Error('simulated reviewer crash');
      },
    },
  );
  assert.equal(errReport.cases[0].verdict, 'ERROR');
  assert.match(errReport.cases[0].parse_error, /simulated reviewer crash/);
  assert.deepEqual(readdirSync(workDirRoot), []);
});

test('security hygiene: refuses escaping git tree symlinks and symlinked manifest/out/result paths', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-eval-sec-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));

  // 1. Escaping symlink inside a git commit tree is refused by prepareScratchCheckout
  const evilRepo = join(root, 'evil-repo');
  mkdirSync(evilRepo, { recursive: true });
  gitIn(evilRepo, ['init', '-q']);
  gitIn(evilRepo, ['config', 'user.name', 'Test User']);
  gitIn(evilRepo, ['config', 'user.email', 'test@example.invalid']);
  gitIn(evilRepo, ['config', 'commit.gpgsign', 'false']);
  writeFileSync(join(evilRepo, 'ok.txt'), 'ok\n');
  gitIn(evilRepo, ['add', '.']);
  gitIn(evilRepo, ['commit', '-qm', 'base']);
  const baseSha = gitIn(evilRepo, ['rev-parse', 'HEAD']);

  symlinkSync('../../outside-target', join(evilRepo, 'escape-link'));
  gitIn(evilRepo, ['add', 'escape-link']);
  gitIn(evilRepo, ['commit', '-qm', 'add escaping symlink']);
  const headSha = gitIn(evilRepo, ['rev-parse', 'HEAD']);

  const workDir = join(root, 'work');
  mkdirSync(workDir, { recursive: true });
  assert.throws(
    () => prepareScratchCheckout({
      repoRoot: evilRepo,
      workDirRoot: workDir,
      fixture: validateFixtureSpec({ id: 'escape-case', label: 'clean', base: baseSha, head: headSha }),
    }),
    /Refusing escaping symlink/,
  );
  assert.deepEqual(readdirSync(workDir), []);

  // 2. Symlinked manifest file is refused
  const realManifest = join(root, 'real-manifest.json');
  writeFileSync(realManifest, JSON.stringify(makeSyntheticManifest()));
  const linkedManifest = join(root, 'linked-manifest.json');
  symlinkSync(realManifest, linkedManifest);
  assert.throws(() => loadReviewEvalManifest(linkedManifest), /Refusing symlink for manifest file/);

  // 3. Symlinked --out target (leaf and parent directory) is refused
  const targetDir = join(root, 'real-out-dir');
  mkdirSync(targetDir, { recursive: true });
  const linkedOutDir = join(root, 'linked-out-dir');
  symlinkSync(targetDir, linkedOutDir);
  const stub = stubScratchPort();
  await assert.rejects(
    () => runReviewEval(
      {
        manifest: makeSyntheticManifest(),
        outFile: join(linkedOutDir, 'sub', 'report.json'),
      },
      {
        prepareScratch: stub.prepareScratch,
        runReviewer: () => ({ verdict: 'PASS', summary: 'ok', mustFix: [] }),
      },
    ),
    /Refusing symlink for --out file/,
  );

  // 4. Reviewer swapping resultPath with a symlink is refused
  const secretFile = join(root, 'secret.json');
  writeFileSync(secretFile, '{"verdict":"PASS","summary":"tampered","mustFix":[]}', 'utf8');
  const tamperDir = join(root, 'tamper-result');
  mkdirSync(tamperDir, { recursive: true });
  const tamperResultPath = join(tamperDir, 'review-result.json');
  const tamperReport = await runReviewEval(
    { manifest: { fixtures: [makeSyntheticManifest().fixtures[0]] } },
    {
      prepareScratch: () => ({
        scratchDir: join(root, 'stub-work'),
        resultPath: tamperResultPath,
        changedFiles: ['M\tsrc/a.mjs'],
        diffStat: '',
        diffExcerpt: '',
        cleanup() {},
      }),
      runReviewer: ({ resultPath }) => {
        symlinkSync(secretFile, resultPath);
        return '';
      },
    },
  );
  assert.equal(tamperReport.cases[0].verdict, 'ERROR');
  assert.match(tamperReport.cases[0].parse_error, /Refusing symlink for reviewer result file/);
});

test('multi-model and multi-prompt-version comparison, JSON + Markdown rendering, secret redaction, and --compare aggregation', async t => {
  const tmp = mkdtempSync(join(tmpdir(), 'pdd-eval-render-'));
  t.after(() => rmSync(tmp, { recursive: true, force: true }));

  const outJson = join(tmp, 'scorecard.json');
  const outMd = join(tmp, 'scorecard.md');
  const stub = stubScratchPort();

  const report = await runReviewEval(
    {
      manifest: makeSyntheticManifest(),
      models: ['model-alpha', 'model-beta'],
      promptVersions: ['autopilot-v1', 'strict-checklist-v1'],
      outFile: outJson,
      markdownOutFile: outMd,
    },
    {
      prepareScratch: stub.prepareScratch,
      now: () => Date.parse('2026-11-20T08:00:00Z'),
      runReviewer: ({ fixture, model, promptVersion }) => {
        if (model === 'model-alpha') {
          if (fixture.pr === 2559) {
            return {
              verdict: 'FAIL',
              summary: 'Caught defect; token ghp_SecretTokenValue1234567890 and sha a1b09cb9641d021d391a87ffd9f4d3ba90340b85 must be scrubbed.',
              mustFix: [
                'P1 test/workflow-github.test.mjs:1 Deleted 19 safety tests without reason',
                ...(promptVersion === 'strict-checklist-v1'
                  ? ['P1 test/workflow-github.test.mjs:40 Test passes for the wrong reason']
                  : []),
              ],
              duration_ms: 420,
            };
          }
          return { verdict: 'PASS', summary: 'Clean change verified.', mustFix: [], duration_ms: 310 };
        }
        // model-beta: misses #2559 (wrong signal) and false-positives on #2560
        if (fixture.pr === 2559) {
          return {
            verdict: 'FAIL',
            summary: 'Minor nit only.',
            mustFix: ['P2 src/workflow-github.mjs:1 Prefer const over let'],
            duration_ms: 250,
          };
        }
        return {
          verdict: 'FAIL',
          summary: 'Overly strict.',
          mustFix: ['P2 src/argument-parser.mjs:10 Rename helper'],
          duration_ms: 200,
        };
      },
    },
  );

  assert.equal(report.schema_version, 'pdd.review-eval.v1');
  assert.equal(report.cases.length, 8);
  assert.equal(report.scorecard.comparison.length, 4);

  const alphaV1 = report.scorecard.comparison.find(r => r.model === 'model-alpha' && r.prompt_version === 'autopilot-v1');
  const alphaStrict = report.scorecard.comparison.find(r => r.model === 'model-alpha' && r.prompt_version === 'strict-checklist-v1');
  const betaV1 = report.scorecard.comparison.find(r => r.model === 'model-beta' && r.prompt_version === 'autopilot-v1');

  assert.equal(alphaV1.bug_recall, 100);
  assert.equal(alphaV1.clean_fp_rate, 0);
  assert.equal(alphaV1.signal_recall, 33.3);
  assert.equal(alphaV1.meets_target, true);

  assert.equal(alphaStrict.bug_recall, 100);
  assert.equal(alphaStrict.clean_fp_rate, 0);
  assert.equal(alphaStrict.signal_recall, 66.7);
  assert.equal(alphaStrict.meets_target, true);

  assert.equal(betaV1.bug_recall, 0);
  assert.equal(betaV1.bad_failed_without_signal, 1);
  assert.equal(betaV1.clean_fp_rate, 100);
  assert.equal(betaV1.meets_target, false);

  // Saved JSON and Markdown pass strict public output hygiene (zero secrets, zero 40-char SHAs)
  const jsonText = readFileSync(outJson, 'utf8');
  const mdText = readFileSync(outMd, 'utf8');
  assertCleanPublicText(jsonText);
  assertCleanPublicText(mdText);
  assert.ok(!jsonText.includes('ghp_SecretTokenValue1234567890'));
  assert.ok(!mdText.includes('ghp_SecretTokenValue1234567890'));
  assert.ok(!jsonText.includes('a1b09cb9641d021d391a87ffd9f4d3ba90340b85'));
  assert.match(mdText, /## Model & Prompt Version Comparison/);
  assert.match(mdText, /\| model-alpha \| autopilot-v1 \| 100% \| 1\/1 \| 0% \| 0\/1 \|/);
  assert.match(mdText, /\| model-beta \| autopilot-v1 \| 0% \| 0\/1 \| 100% \| 1\/1 \|/);
  assert.match(mdText, /## Per-Case Breakdown/);

  // Direct renderReviewEvalMarkdown handles empty reports and escapes pipe characters cleanly
  const emptyMd = renderReviewEvalMarkdown({ generated_at: '2026-11-20T08:00:00Z', cases: [] });
  assert.match(emptyMd, /Bug Recall: \*\*n\/a\*\*/);
  assert.match(emptyMd, /Clean-Control FP Rate: \*\*n\/a\*\*/);
  const pipedMd = renderReviewEvalMarkdown({
    generated_at: '2026-11-20T08:00:00Z',
    cases: [{ id: 'pipe-case', pr: 1, label: 'clean', model: 'm|1', prompt_version: 'v1', verdict: 'PASS', outcome: 'clean_pass', summary: 'a | b', must_fix: [] }],
  });
  assert.ok(pipedMd.includes('m\\|1'));
  assert.ok(pipedMd.includes('a \\| b'));

  // --compare aggregates saved JSON reports cleanly and --out *.md writes Markdown directly
  const compareMdOut = join(tmp, 'compare.md');
  const aggregated = await runReviewEval({ compareFiles: [outJson], outFile: compareMdOut });
  assert.deepEqual(aggregated.models, ['model-alpha', 'model-beta']);
  assert.deepEqual(aggregated.prompt_versions, ['autopilot-v1', 'strict-checklist-v1']);
  assert.equal(aggregated.fixture_count, 2);
  assert.equal(aggregated.scorecard.comparison.length, 4);
  assert.match(readFileSync(compareMdOut, 'utf8'), /^# Autopilot Reviewer \/ Verifier Eval Scorecard/);
});

test('CLI flag parsing, dry-run against real repo manifest, and isolated live --agent-cmd execution', t => {
  const tmp = mkdtempSync(join(tmpdir(), 'pdd-eval-cli-'));
  t.after(() => rmSync(tmp, { recursive: true, force: true }));

  // Parser validation
  const parsed = parseReviewEvalCliArgs([
    '--manifest', 'custom.json',
    '--out', 'out.json',
    '--markdown-out', 'out.md',
    '--model', 'gpt-5.3-codex',
    '--model', 'claude-sonnet-4',
    '--prompt-version', 'autopilot-v1',
    '--prompt-version', 'strict-checklist-v1',
    '--fixture', 'pr-2559-symlink-pr-body',
    '--timeout-ms', '45000',
    '--agent-cmd', 'node',
    '--agent-arg', '-e',
    '--agent-arg=process.exit(0)',
    '--dry-run',
    '--json',
  ]);
  assert.equal(parsed.manifest, 'custom.json');
  assert.equal(parsed.outFile, 'out.json');
  assert.equal(parsed.markdownOutFile, 'out.md');
  assert.deepEqual(parsed.models, ['gpt-5.3-codex', 'claude-sonnet-4']);
  assert.deepEqual(parsed.promptVersions, ['autopilot-v1', 'strict-checklist-v1']);
  assert.deepEqual(parsed.fixtures, ['pr-2559-symlink-pr-body']);
  assert.equal(parsed.timeoutMs, 45000);
  assert.equal(parsed.agentCmd, 'node');
  assert.deepEqual(parsed.agentArgs, ['-e', 'process.exit(0)']);
  assert.equal(parsed.dryRun, true);
  assert.equal(parsed.json, true);

  assert.throws(() => parseReviewEvalCliArgs(['--manifest']), /Missing value/);
  assert.throws(() => parseReviewEvalCliArgs(['--model', '--json']), /Missing value/);
  assert.throws(() => parseReviewEvalCliArgs(['--timeout-ms', '0']), /positive integer/);
  assert.throws(() => parseReviewEvalCliArgs(['--unknown-flag']), /Unknown argument/);
  assert.throws(() => createCliReviewerRunner({}), /requires --agent-cmd/);

  const scriptPath = RUN_REVIEW_EVAL_SCRIPT;

  // Exit code 2 for CLI usage error
  const badFlag = spawnSync(process.execPath, [scriptPath, '--timeout-ms', '-10'], { encoding: 'utf8' });
  assert.equal(badFlag.status, 2);

  // Exit code 1 for missing manifest file
  const missingManifest = spawnSync(
    process.execPath,
    [scriptPath, '--manifest', join(tmp, 'missing.json'), '--dry-run'],
    { encoding: 'utf8' },
  );
  assert.equal(missingManifest.status, 1);

  // Hermetic temporary git repo so CLI subprocess tests work identically in shallow CI clones (fetch-depth: 1)
  const cliRepo = join(tmp, 'cli-repo');
  mkdirSync(cliRepo, { recursive: true });
  gitIn(cliRepo, ['init', '-q']);
  gitIn(cliRepo, ['config', 'user.name', 'Test User']);
  gitIn(cliRepo, ['config', 'user.email', 'test@example.invalid']);
  gitIn(cliRepo, ['config', 'commit.gpgsign', 'false']);
  mkdirSync(join(cliRepo, 'src'), { recursive: true });
  mkdirSync(join(cliRepo, 'test/manual'), { recursive: true });
  writeFileSync(join(cliRepo, 'src/workflow-github.mjs'), 'export const safe = true;\n');
  writeFileSync(join(cliRepo, 'test/manual/independent-code-review.md'), 'DO NOT LEAK\n');
  gitIn(cliRepo, ['add', '.']);
  gitIn(cliRepo, ['commit', '-qm', 'base']);
  const cBase = gitIn(cliRepo, ['rev-parse', 'HEAD']);
  writeFileSync(join(cliRepo, 'src/workflow-github.mjs'), 'export const safe = false;\n');
  gitIn(cliRepo, ['add', '.']);
  gitIn(cliRepo, ['commit', '-qm', 'bad head']);
  const cBadHead = gitIn(cliRepo, ['rev-parse', 'HEAD']);
  writeFileSync(join(cliRepo, 'src/argument-parser.mjs'), 'export const help = "Name the workflow";\n');
  gitIn(cliRepo, ['add', '.']);
  gitIn(cliRepo, ['commit', '-qm', 'clean head']);
  const cCleanHead = gitIn(cliRepo, ['rev-parse', 'HEAD']);

  const cliManifestPath = join(tmp, 'cli-manifest.json');
  writeFileSync(cliManifestPath, JSON.stringify({
    schema_version: 'pdd.review-eval-manifest.v1',
    fixtures: [
      {
        id: 'cli-pr-2559',
        label: 'bad',
        repo: 'promptdriven/pdd',
        pr: 2559,
        issue: 2444,
        base: cBase,
        head: cBadHead,
        issue_title: 'Symlinked repo open PR',
        issue_body: 'Keep safety checks intact.',
        expected_signals: [
          {
            id: 'deleted-safety-tests',
            description: 'Deleted 19 existing safety tests',
            any_all_of: [[['deleted', 'removed'], ['safety', '19'], ['test', 'tests']]],
          },
        ],
      },
      {
        id: 'cli-pr-2560',
        label: 'clean',
        repo: 'promptdriven/pdd',
        pr: 2560,
        issue: 2438,
        base: cBadHead,
        head: cCleanHead,
        issue_title: 'Explain missing workflow name',
        issue_body: 'Explain missing workflow name before running.',
        expected_signals: [],
      },
    ],
  }, null, 2));

  // Subprocess --dry-run --json validates fixtures & isolation and writes JSON + Markdown
  const dryJsonOut = join(tmp, 'dry.json');
  const dryMdOut = join(tmp, 'dry.md');
  const dryRes = spawnSync(
    process.execPath,
    [
      scriptPath,
      '--repo-root', cliRepo,
      '--manifest', cliManifestPath,
      '--dry-run', '--json',
      '--model', 'eval-model',
      '--prompt-version', 'strict-checklist-v1',
      '--out', dryJsonOut,
      '--markdown-out', dryMdOut,
    ],
    { encoding: 'utf8' },
  );
  assert.equal(dryRes.status, 0, dryRes.stderr);
  const dryParsed = JSON.parse(dryRes.stdout);
  assert.equal(dryParsed.dry_run, true);
  assert.equal(dryParsed.dry_run_plan.length, 2);
  assert.ok(dryParsed.dry_run_plan.every(row => row.isolation_verified === true && row.changed_files_count === 1));
  assert.ok(existsSync(dryJsonOut));
  assert.ok(existsSync(dryMdOut));

  // When full repo history is present (non-shallow clone), also verify all 4 shipped manifest SHAs (#2559 + #2560) resolve cleanly
  const shippedShas = [
    'a1b09cb9641d021d391a87ffd9f4d3ba90340b85',
    '0db39638250f8fd11bc08bffa78ef8c4a6b03be8',
    '515dae711345f93b622ed19d4a3f825eb4e339d4',
    '1a4b37803022b604f2ab576c9683a79e47943135',
  ];
  const hasRealShippedCommits = shippedShas.every(
    sha => spawnSync('git', ['cat-file', '-e', `${sha}^{commit}`], { encoding: 'utf8' }).status === 0,
  );
  if (hasRealShippedCommits) {
    const realDry = spawnSync(process.execPath, [scriptPath, '--dry-run', '--json'], { encoding: 'utf8' });
    assert.equal(realDry.status, 0, realDry.stderr);
    const realParsed = JSON.parse(realDry.stdout);
    assert.equal(realParsed.dry_run_plan.length, 2);
    assert.ok(realParsed.dry_run_plan.every(row => row.isolation_verified === true && row.changed_files_count === 5));
  }

  // Real subprocess live --agent-cmd strips GH tokens, runs inside isolated scratch checkout, writes JSON + MD, cleans scratch dir
  const workDir = join(tmp, 'live-work');
  mkdirSync(workDir, { recursive: true });
  const envLogPath = join(tmp, 'seen-env.json');
  const fakeReviewer = join(tmp, 'fake-reviewer.mjs');
  writeFileSync(fakeReviewer, `
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
const prompt = readFileSync(0, 'utf8');
writeFileSync(${JSON.stringify(envLogPath)}, JSON.stringify({
  GH_TOKEN: process.env.GH_TOKEN ?? null,
  GITHUB_TOKEN: process.env.GITHUB_TOKEN ?? null,
  hasExpectedSignalsWord: prompt.includes('expected_signals'),
  hasManualDoc: prompt.includes('independent-code-review.md'),
  manualFileExistsInCwd: existsSync('test/manual/independent-code-review.md'),
  modelArg: process.argv[2] ?? null,
}));
const resultPath = process.env.PDD_REVIEW_RESULT_PATH;
const is2559 = prompt.includes('PR #2559');
const verdictObj = is2559
  ? { verdict: 'FAIL', summary: 'Found regressions.', mustFix: ['P1 test/workflow-github.test.mjs:1 Deleted 19 safety tests'] }
  : { verdict: 'PASS', summary: 'Clean PR.', mustFix: [] };
writeFileSync(resultPath, JSON.stringify(verdictObj), 'utf8');
`, 'utf8');

  const liveJsonOut = join(tmp, 'live.json');
  const liveMdOut = join(tmp, 'live.md');
  const liveRes = spawnSync(
    process.execPath,
    [
      scriptPath,
      '--repo-root', cliRepo,
      '--manifest', cliManifestPath,
      '--model', 'stub-llm-v1',
      '--prompt-version', 'autopilot-v1',
      '--work-dir', workDir,
      '--out', liveJsonOut,
      '--markdown-out', liveMdOut,
      '--json',
      '--agent-cmd', process.execPath,
      '--agent-arg', fakeReviewer,
      '--agent-arg', '{model}',
    ],
    {
      encoding: 'utf8',
      env: {
        ...process.env,
        GH_TOKEN: 'ghp_ShouldBeStripped1234567890',
        GITHUB_TOKEN: 'gho_ShouldBeStripped1234567890',
      },
    },
  );
  assert.equal(liveRes.status, 0, liveRes.stderr);
  const liveReport = JSON.parse(liveRes.stdout);
  assert.equal(liveReport.scorecard.bug_recall, 100);
  assert.equal(liveReport.scorecard.clean_fp_rate, 0);
  assert.equal(liveReport.scorecard.meets_target, true);
  assert.deepEqual(readdirSync(workDir), [], 'Scratch dirs must be cleaned up after live run');

  const seenEnv = JSON.parse(readFileSync(envLogPath, 'utf8'));
  assert.equal(seenEnv.GH_TOKEN, null);
  assert.equal(seenEnv.GITHUB_TOKEN, null);
  assert.equal(seenEnv.hasExpectedSignalsWord, false);
  assert.equal(seenEnv.hasManualDoc, false);
  assert.equal(seenEnv.manualFileExistsInCwd, false);
  assert.equal(seenEnv.modelArg, 'stub-llm-v1');
  assertCleanPublicText(readFileSync(liveMdOut, 'utf8'));
});

test('regression: symlink ancestor bypass is strictly refused across --out, --markdown-out, --work-dir, manifest, --prompt-template, --compare, and resultPath', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-eval-anc-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));

  const realTarget = join(root, 'real-target');
  const existingSub = join(realTarget, 'existing-sub');
  mkdirSync(existingSub, { recursive: true });
  const symlinkDir = join(root, 'symlink-dir');
  symlinkSync(realTarget, symlinkDir);

  // Create real files inside existingSub so the immediate parent directory EXISTS (previously bypassed!)
  const realManifest = join(existingSub, 'manifest.json');
  const realTemplate = join(existingSub, 'template.txt');
  const realCompare = join(existingSub, 'compare.json');
  writeFileSync(realManifest, JSON.stringify(makeSyntheticManifest()), 'utf8');
  writeFileSync(realTemplate, 'Review:\n{{EVIDENCE}}', 'utf8');
  writeFileSync(realCompare, JSON.stringify({ cases: [] }), 'utf8');

  const stub = stubScratchPort();
  const passReviewer = () => ({ verdict: 'PASS', summary: 'ok', mustFix: [] });

  // --out symlinkDir/existing-sub/report.json
  await assert.rejects(
    () => runReviewEval(
      { manifest: makeSyntheticManifest(), outFile: join(symlinkDir, 'existing-sub', 'report.json') },
      { prepareScratch: stub.prepareScratch, runReviewer: passReviewer },
    ),
    /Refusing symlink for --out file/,
  );

  // --markdown-out symlinkDir/existing-sub/report.md
  await assert.rejects(
    () => runReviewEval(
      { manifest: makeSyntheticManifest(), markdownOutFile: join(symlinkDir, 'existing-sub', 'report.md') },
      { prepareScratch: stub.prepareScratch, runReviewer: passReviewer },
    ),
    /Refusing symlink for --markdown-out file/,
  );

  // --work-dir symlinkDir/existing-sub
  assert.throws(
    () => prepareScratchCheckout({
      repoRoot: root,
      workDirRoot: join(symlinkDir, 'existing-sub'),
      fixture: makeSyntheticManifest().fixtures[0],
    }),
    /Refusing symlink for work-dir/,
  );

  // manifest under symlinkDir/existing-sub/manifest.json
  assert.throws(
    () => loadReviewEvalManifest(join(symlinkDir, 'existing-sub', 'manifest.json')),
    /Refusing symlink for manifest file/,
  );

  // --prompt-template under symlinkDir/existing-sub/template.txt
  await assert.rejects(
    () => runReviewEval(
      { manifest: makeSyntheticManifest(), promptTemplate: join(symlinkDir, 'existing-sub', 'template.txt') },
      { prepareScratch: stub.prepareScratch, runReviewer: passReviewer },
    ),
    /Refusing symlink for prompt template/,
  );

  // --compare under symlinkDir/existing-sub/compare.json
  await assert.rejects(
    () => runReviewEval(
      { compareFiles: [join(symlinkDir, 'existing-sub', 'compare.json')] },
    ),
    /Refusing symlink for compare report/,
  );

  // resultPath whose parent dir inside metaDir was replaced with a symlink
  const fakeMetaDir = join(root, 'meta-dir');
  const outsideDir = join(root, 'outside-result');
  mkdirSync(fakeMetaDir, { recursive: true });
  mkdirSync(outsideDir, { recursive: true });
  writeFileSync(join(outsideDir, 'review-result.json'), '{"verdict":"PASS","summary":"hijacked","mustFix":[]}', 'utf8');
  const linkedResultDir = join(fakeMetaDir, 'result');
  symlinkSync(outsideDir, linkedResultDir);

  const tamperedRes = await runReviewEval(
    { manifest: { fixtures: [makeSyntheticManifest().fixtures[0]] } },
    {
      prepareScratch: () => ({
        scratchDir: join(root, 'stub-scratch'),
        metaDir: fakeMetaDir,
        resultPath: join(linkedResultDir, 'review-result.json'),
        changedFiles: ['M\tsrc/a.mjs'],
        diffStat: '',
        diffExcerpt: '',
        cleanup() {},
      }),
      runReviewer: () => '',
    },
  );
  assert.equal(tamperedRes.cases[0].verdict, 'ERROR');
  assert.match(tamperedRes.cases[0].parse_error, /Refusing symlink for reviewer result file/);
});

test('regression: chained/loop/dangling git-tree symlinks are refused pre-checkout and post-checkout', t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-eval-symchain-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));

  const initRepo = name => {
    const dir = join(root, name);
    mkdirSync(dir, { recursive: true });
    gitIn(dir, ['init', '-q']);
    gitIn(dir, ['config', 'user.name', 'Test User']);
    gitIn(dir, ['config', 'user.email', 'test@example.invalid']);
    gitIn(dir, ['config', 'commit.gpgsign', 'false']);
    writeFileSync(join(dir, 'ok.txt'), 'ok\n');
    gitIn(dir, ['add', '.']);
    gitIn(dir, ['commit', '-qm', 'base']);
    return { dir, baseSha: gitIn(dir, ['rev-parse', 'HEAD']) };
  };

  // 1. Chained symlink escape: a/b/up -> ../.. (inside root), a/b/escape -> up/.. (escapes via a/b/up!)
  const chained = initRepo('chained-repo');
  mkdirSync(join(chained.dir, 'a/b'), { recursive: true });
  symlinkSync('../..', join(chained.dir, 'a/b/up'));
  symlinkSync('up/..', join(chained.dir, 'a/b/escape'));
  gitIn(chained.dir, ['add', 'a/b/up', 'a/b/escape']);
  gitIn(chained.dir, ['commit', '-qm', 'chained escape']);
  const chainedHead = gitIn(chained.dir, ['rev-parse', 'HEAD']);

  const workDir = join(root, 'work');
  mkdirSync(workDir, { recursive: true });
  assert.throws(
    () => prepareScratchCheckout({
      repoRoot: chained.dir,
      workDirRoot: workDir,
      fixture: validateFixtureSpec({ id: 'chained-escape', label: 'clean', base: chained.baseSha, head: chainedHead }),
    }),
    /Refusing escaping symlink/,
  );
  assert.deepEqual(readdirSync(workDir), []);

  // 2. Symlink loop inside git tree is refused
  const loopRepo = initRepo('loop-repo');
  symlinkSync('loop-b', join(loopRepo.dir, 'loop-a'));
  symlinkSync('loop-a', join(loopRepo.dir, 'loop-b'));
  gitIn(loopRepo.dir, ['add', 'loop-a', 'loop-b']);
  gitIn(loopRepo.dir, ['commit', '-qm', 'loop']);
  const loopHead = gitIn(loopRepo.dir, ['rev-parse', 'HEAD']);
  assert.throws(
    () => prepareScratchCheckout({
      repoRoot: loopRepo.dir,
      workDirRoot: workDir,
      fixture: validateFixtureSpec({ id: 'loop-case', label: 'clean', base: loopRepo.baseSha, head: loopHead }),
    }),
    /Refusing symlink loop/,
  );

  // 3. Dangling symlink in git tree pointing outside scratch is refused
  const danglingRepo = initRepo('dangling-repo');
  mkdirSync(join(danglingRepo.dir, 'sub'), { recursive: true });
  symlinkSync('../../nonexistent-outside-dir/secret', join(danglingRepo.dir, 'sub/dangling'));
  gitIn(danglingRepo.dir, ['add', 'sub/dangling']);
  gitIn(danglingRepo.dir, ['commit', '-qm', 'dangling escape']);
  const danglingHead = gitIn(danglingRepo.dir, ['rev-parse', 'HEAD']);
  assert.throws(
    () => prepareScratchCheckout({
      repoRoot: danglingRepo.dir,
      workDirRoot: workDir,
      fixture: validateFixtureSpec({ id: 'dangling-escape', label: 'clean', base: danglingRepo.baseSha, head: danglingHead }),
    }),
    /Refusing escaping symlink/,
  );

  // 4. Post-checkout defense-in-depth directly rejects dangling symlinks escaping realScratch (direct, via missing dir, and chained)
  const postScratch = join(root, 'post-scratch');
  mkdirSync(join(postScratch, 'a/b'), { recursive: true });
  writeFileSync(join(postScratch, 'inside.txt'), 'safe\n');
  symlinkSync('../../nonexistent-outside/file', join(postScratch, 'a/direct-dangling'));
  symlinkSync('missing-dir/../../../outside-file', join(postScratch, 'a/backtrack-dangling'));
  symlinkSync('../..', join(postScratch, 'a/b/up'));
  symlinkSync('up/../nonexistent-outside', join(postScratch, 'a/b/chained-dangling'));
  symlinkSync('../future-inside.txt', join(postScratch, 'a/safe-dangling'));
  symlinkSync('../inside.txt', join(postScratch, 'a/safe-link'));

  assert.throws(() => assertSafeCheckedOutSymlink(postScratch, 'a/direct-dangling'), /Refusing symlink escaping scratch checkout/);
  assert.throws(() => assertSafeCheckedOutSymlink(postScratch, 'a/backtrack-dangling'), /Refusing symlink escaping scratch checkout/);
  assert.throws(() => assertSafeCheckedOutSymlink(postScratch, 'a/b/chained-dangling'), /Refusing symlink escaping scratch checkout/);
  assert.ok(assertSafeCheckedOutSymlink(postScratch, 'a/safe-dangling').endsWith('future-inside.txt'));
  assert.ok(assertSafeCheckedOutSymlink(postScratch, 'a/safe-link').endsWith('inside.txt'));
});

test('regression: inherited GIT_* env vars, global gitconfig defaultBranch=eval-base, .gitignore tracked files, and GH_CONFIG_DIR isolation', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-eval-gitenv-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));

  // Decoy repo whose GIT_DIR/GIT_WORK_TREE are injected into env to verify they are stripped
  const decoyRepo = join(root, 'decoy-repo');
  mkdirSync(decoyRepo, { recursive: true });
  gitIn(decoyRepo, ['init', '-q']);
  gitIn(decoyRepo, ['config', 'user.name', 'Decoy']);
  gitIn(decoyRepo, ['config', 'user.email', 'decoy@example.invalid']);
  gitIn(decoyRepo, ['config', 'commit.gpgsign', 'false']);
  writeFileSync(join(decoyRepo, 'decoy.txt'), 'decoy\n');
  gitIn(decoyRepo, ['add', '.']);
  gitIn(decoyRepo, ['commit', '-qm', 'decoy']);

  // Poisoned HOME with global gitconfig setting init.defaultBranch = eval-base
  const fakeHome = join(root, 'fake-home');
  mkdirSync(fakeHome, { recursive: true });
  writeFileSync(join(fakeHome, '.gitconfig'), '[init]\n\tdefaultBranch = eval-base\n', 'utf8');
  const fakeHostGhDir = join(root, 'host-gh-config');
  mkdirSync(fakeHostGhDir, { recursive: true });
  writeFileSync(join(fakeHostGhDir, 'hosts.yml'), 'github.com:\n  oauth_token: gho_must_not_be_seen\n', 'utf8');

  // Target fixture repo with a .gitignore-matched force-tracked file
  const targetRepo = join(root, 'target-repo');
  mkdirSync(targetRepo, { recursive: true });
  gitIn(targetRepo, ['init', '-q']);
  gitIn(targetRepo, ['config', 'user.name', 'Test User']);
  gitIn(targetRepo, ['config', 'user.email', 'test@example.invalid']);
  gitIn(targetRepo, ['config', 'commit.gpgsign', 'false']);
  writeFileSync(join(targetRepo, '.gitignore'), '*.ignored\n');
  writeFileSync(join(targetRepo, 'tracked.ignored'), 'v1\n');
  writeFileSync(join(targetRepo, 'normal.txt'), 'a\n');
  gitIn(targetRepo, ['add', '-f', '.gitignore', 'tracked.ignored', 'normal.txt']);
  gitIn(targetRepo, ['commit', '-qm', 'base']);
  const baseSha = gitIn(targetRepo, ['rev-parse', 'HEAD']);

  writeFileSync(join(targetRepo, 'tracked.ignored'), 'v2\n');
  writeFileSync(join(targetRepo, 'normal.txt'), 'b\n');
  gitIn(targetRepo, ['add', '-f', 'tracked.ignored', 'normal.txt']);
  gitIn(targetRepo, ['commit', '-qm', 'head']);
  const headSha = gitIn(targetRepo, ['rev-parse', 'HEAD']);

  const poisonedEnv = {
    ...process.env,
    HOME: fakeHome,
    GIT_DIR: join(decoyRepo, '.git'),
    GIT_WORK_TREE: decoyRepo,
    GIT_INDEX_FILE: join(decoyRepo, '.git', 'index'),
    GIT_COMMON_DIR: join(decoyRepo, '.git'),
    GIT_OBJECT_DIRECTORY: join(decoyRepo, '.git', 'objects'),
    GIT_ALTERNATE_OBJECT_DIRECTORIES: join(decoyRepo, '.git', 'objects'),
    GH_CONFIG_DIR: fakeHostGhDir,
  };

  const fixture = validateFixtureSpec({ id: 'gitenv-case', label: 'clean', base: baseSha, head: headSha });
  const workDir = join(root, 'work');
  mkdirSync(workDir, { recursive: true });

  const scratch = prepareScratchCheckout({
    repoRoot: targetRepo,
    fixture,
    workDirRoot: workDir,
    env: poisonedEnv,
    readOnly: false,
  });
  try {
    // eval-base and HEAD must be distinct commits and preserve .gitignore-matched tracked file!
    assert.equal(readFileSync(join(scratch.scratchDir, 'tracked.ignored'), 'utf8'), 'v2\n');
    assert.ok(scratch.changedFiles.includes('M\ttracked.ignored'), `Expected tracked.ignored in changedFiles, got ${scratch.changedFiles}`);
    assert.ok(scratch.changedFiles.includes('M\tnormal.txt'));
    const activeBranch = gitIn(scratch.scratchDir, ['rev-parse', '--abbrev-ref', 'HEAD']);
    assert.equal(activeBranch, 'eval-head');
    assert.notEqual(
      gitIn(scratch.scratchDir, ['rev-parse', 'eval-base']),
      gitIn(scratch.scratchDir, ['rev-parse', 'HEAD']),
    );
  } finally {
    scratch.cleanup();
  }

  // Verify live runner strips GIT_* repo vars and points GH_CONFIG_DIR at a fresh empty dir inside metaDir
  const envCapturePath = join(root, 'captured-child-env.json');
  const probeScript = join(root, 'probe-env.mjs');
  writeFileSync(probeScript, `
import { readdirSync, writeFileSync } from 'node:fs';
writeFileSync(${JSON.stringify(envCapturePath)}, JSON.stringify({
  GIT_DIR: process.env.GIT_DIR ?? null,
  GIT_WORK_TREE: process.env.GIT_WORK_TREE ?? null,
  GIT_INDEX_FILE: process.env.GIT_INDEX_FILE ?? null,
  GIT_COMMON_DIR: process.env.GIT_COMMON_DIR ?? null,
  GIT_OBJECT_DIRECTORY: process.env.GIT_OBJECT_DIRECTORY ?? null,
  GIT_ALTERNATE_OBJECT_DIRECTORIES: process.env.GIT_ALTERNATE_OBJECT_DIRECTORIES ?? null,
  GIT_CONFIG_NOSYSTEM: process.env.GIT_CONFIG_NOSYSTEM ?? null,
  GIT_CONFIG_GLOBAL: process.env.GIT_CONFIG_GLOBAL ?? null,
  GH_CONFIG_DIR: process.env.GH_CONFIG_DIR ?? null,
  ghConfigEntries: process.env.GH_CONFIG_DIR ? readdirSync(process.env.GH_CONFIG_DIR) : null,
}));
process.stdout.write(JSON.stringify({ verdict: 'PASS', summary: 'ok', mustFix: [] }));
`, 'utf8');

  const liveRes = await runReviewEval(
    {
      manifest: { fixtures: [{ id: 'gitenv-live', label: 'clean', base: baseSha, head: headSha }] },
      repoRoot: targetRepo,
      workDirRoot: workDir,
      agentCmd: process.execPath,
      agentArgs: [probeScript],
      env: poisonedEnv,
    },
  );
  assert.equal(liveRes.cases[0].verdict, 'PASS');
  const seen = JSON.parse(readFileSync(envCapturePath, 'utf8'));
  assert.equal(seen.GIT_DIR, null);
  assert.equal(seen.GIT_WORK_TREE, null);
  assert.equal(seen.GIT_INDEX_FILE, null);
  assert.equal(seen.GIT_COMMON_DIR, null);
  assert.equal(seen.GIT_OBJECT_DIRECTORY, null);
  assert.equal(seen.GIT_ALTERNATE_OBJECT_DIRECTORIES, null);
  assert.equal(seen.GIT_CONFIG_NOSYSTEM, '1');
  assert.equal(seen.GIT_CONFIG_GLOBAL, process.platform === 'win32' ? 'NUL' : '/dev/null');
  assert.ok(seen.GH_CONFIG_DIR && seen.GH_CONFIG_DIR !== fakeHostGhDir);
  assert.ok(seen.GH_CONFIG_DIR.startsWith(workDir), `Expected GH_CONFIG_DIR inside metaDir under ${workDir}, got ${seen.GH_CONFIG_DIR}`);
  assert.deepEqual(seen.ghConfigEntries, []);
  assert.deepEqual(readdirSync(workDir), []);
});

test('regression: --prompt-version rejects prototype keys and typos, non-P3 followUps keep FAIL, signal-killed child fails, scorecard caps signal_recall, and P3 guards hold', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-eval-reg-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));

  const manifest = loadReviewEvalManifest(makeSyntheticManifest());
  const badFix = manifest.fixtures[0];

  // 1. Prototype keys & typos on --prompt-version throw CliUsageError (exitCode 2)
  for (const badVersion of ['constructor', 'toString', '__proto__', 'autopilot-v99']) {
    assert.throws(
      () => buildReviewerPrompt({ fixture: badFix, promptVersion: badVersion }),
      err => err instanceof CliUsageError && err.exitCode === 2 && /Unknown --prompt-version/.test(err.message),
    );
    await assert.rejects(
      () => runReviewEval(
        { manifest: makeSyntheticManifest(), promptVersions: [badVersion], dryRun: true },
        { inspectFixture: () => ({ changedFiles: ['M\tsrc/a.mjs'], diffStat: '' }) },
      ),
      err => err instanceof CliUsageError && err.exitCode === 2,
    );
  }
  const scriptPath = RUN_REVIEW_EVAL_SCRIPT;
  const cliProto = spawnSync(process.execPath, [scriptPath, '--prompt-version', 'constructor', '--dry-run'], { encoding: 'utf8' });
  assert.equal(cliProto.status, 2);

  // Custom --prompt-template still allows custom prompt-version labels
  const customTpl = join(root, 'custom.txt');
  writeFileSync(customTpl, 'Custom review prompt\n{{EVIDENCE}}', 'utf8');
  const customDry = await runReviewEval(
    { manifest: makeSyntheticManifest(), promptTemplate: customTpl, promptVersions: ['custom-exp-v2'], dryRun: true },
    { inspectFixture: () => ({ changedFiles: ['M\tsrc/a.mjs'], diffStat: '' }) },
  );
  assert.equal(customDry.dry_run_plan[0].prompt_version, 'custom-exp-v2');

  // 2. Non-P3 entries inside obj.followUps are routed to mustFix and cannot demote FAIL -> PASS
  const p1InFollowUps = parseReviewerOutput({
    verdict: 'FAIL',
    summary: 'Blocking bug placed in followUps.',
    mustFix: [],
    followUps: ['P1 src/workflow-github.mjs:10 Missing path check'],
  });
  assert.equal(p1InFollowUps.verdict, 'FAIL');
  assert.equal(p1InFollowUps.mustFix.length, 1);
  assert.equal(p1InFollowUps.followUps.length, 0);

  const unprefixedInFollowUps = parseReviewerOutput({
    verdict: 'FAIL',
    summary: 'Unprefixed issue in followUps.',
    mustFix: [],
    followUps: ['Deleted safety tests without justification'],
  });
  assert.equal(unprefixedInFollowUps.verdict, 'FAIL');
  assert.equal(unprefixedInFollowUps.mustFix.length, 1);

  const p2InPassFollowUps = parseReviewerOutput({
    verdict: 'PASS',
    summary: 'Claimed PASS with P2 in followUps.',
    mustFix: [],
    followUps: ['P2 src/a.mjs:5 Handle edge case'],
  });
  assert.equal(p2InPassFollowUps.verdict, 'FAIL');
  assert.equal(p2InPassFollowUps.mustFix.length, 1);

  const genuineP3FollowUp = parseReviewerOutput({
    verdict: 'FAIL',
    summary: 'Only P3.',
    mustFix: [],
    followUps: ['P3 src/a.mjs:9 Minor rename'],
  });
  assert.equal(genuineP3FollowUp.verdict, 'PASS');
  assert.equal(genuineP3FollowUp.mustFix.length, 0);
  assert.equal(genuineP3FollowUp.followUps.length, 1);

  // 3. Linear fenced JSON extraction handles non-JSON fences + inline JSON fence + many backticks cleanly
  const multiFence = [
    '```diff',
    '-old',
    '+new',
    '```',
    '```'.repeat(500),
    '```json',
    '{"verdict":"FAIL","summary":"Fenced ok","mustFix":["P1 a.mjs:1 fix"]}',
    '```',
  ].join('\n');
  assert.equal(parseReviewerOutput(multiFence).verdict, 'FAIL');
  assert.equal(parseReviewerOutput('```json {"verdict":"PASS","summary":"inline","mustFix":[]}```').verdict, 'PASS');

  // 4. Signal-killed child process fails loudly (even when stdout was written) and maps SIGTERM -> 143
  const sigRunner = createCliReviewerRunner({
    agentCmd: process.execPath,
    agentArgs: ['-e', 'process.stdout.write("partial"); process.kill(process.pid, "SIGTERM");'],
  });
  await assert.rejects(
    () => sigRunner({ prompt: 'test', scratchDir: root, resultPath: null, model: 'test-model' }),
    /terminated by signal SIGTERM \(exit code 143\)/,
  );

  const enoentRunner = createCliReviewerRunner({
    agentCmd: join(root, 'definitely-missing-binary-xyz'),
  });
  await assert.rejects(
    () => enoentRunner({ prompt: 'test', scratchDir: root, resultPath: null, model: 'test-model' }),
    /Reviewer command failed \(ENOENT\)/,
  );

  // 5. scorecard.mjs caps signal_recall <= 100% when expectedCount === 0 or matched > expected or error row
  const cappedCard = computeReviewEvalScorecard([
    { label: 'bad', verdict: 'FAIL', caught: true, expected_signals_count: 0, matched_signals: ['spurious-1', 'spurious-2'] },
    { label: 'bad', verdict: 'FAIL', caught: true, expected_signals_count: 1, matched_signals: ['real-1', 'extra-2'] },
    { label: 'bad', verdict: 'FAIL', outcome: 'error', caught: false, expected_signals_count: 1, matched_signals: ['err-sig'] },
    { label: 'clean', verdict: 'PASS', false_positive: false },
  ]);
  assert.equal(cappedCard.expected_signals_total, 2);
  assert.equal(cappedCard.matched_signals_total, 1);
  assert.equal(cappedCard.signal_recall, 50);

  // 6. P3 guards: safeChangedFiles filters forbidden source column in tab-separated renames & resolveCommitOrThrow validates git refs
  const renamePrompt = buildReviewerPrompt({
    fixture: badFix,
    changedFiles: [
      'R100\ttest/manual/independent-code-review.md\tdocs/moved.md',
      'M\tsrc/dir with space/file.mjs',
    ],
  });
  assert.ok(!renamePrompt.includes('independent-code-review.md'));
  assert.ok(!renamePrompt.includes('docs/moved.md'));
  assert.ok(renamePrompt.includes('src/dir with space/file.mjs'));

  assert.throws(
    () => inspectFixtureDiffReadOnly({
      repoRoot: root,
      fixture: { id: 'raw-bad-ref', base: '--upload-pack=evil', head: 'HEAD' },
    }),
    /Unsafe or invalid/,
  );
});

test('R2 adversarial regressions: metaDir symlink swap, full Git config/template/ext-diff isolation, dangling escape-reenter, and unknown scorecard verdicts', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-eval-r2-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));

  // 1. Swapping metaDir itself for a symlink to a target directory with result/review-result.json must be refused
  const decoyTarget = join(root, 'decoy-target');
  mkdirSync(join(decoyTarget, 'result'), { recursive: true });
  writeFileSync(
    join(decoyTarget, 'result', 'review-result.json'),
    JSON.stringify({ verdict: 'PASS', summary: 'Spoofed via metaDir symlink.', mustFix: [] }),
    'utf8',
  );

  const metaDir = join(root, 'meta-real');
  const resultDir = join(metaDir, 'result');
  mkdirSync(resultDir, { recursive: true });
  const resultPath = join(resultDir, 'review-result.json');

  const runnerSwapMeta = createCliReviewerRunner({
    agentCmd: process.execPath,
    agentArgs: [
      '-e',
      `const fs = require('node:fs');
       fs.rmSync(${JSON.stringify(metaDir)}, { recursive: true, force: true });
       fs.symlinkSync(${JSON.stringify(decoyTarget)}, ${JSON.stringify(metaDir)});
       process.stdout.write('ok');`,
    ],
  });
  await assert.rejects(
    () => runnerSwapMeta({ prompt: 'test', scratchDir: root, metaDir, resultPath, model: 'test-model' }),
    /Refusing symlink/,
  );

  // Also test runReviewEval fallback path when custom runReviewer omits resultFileText and swaps metaDir
  const repo = join(root, 'repo-r2');
  mkdirSync(repo, { recursive: true });
  gitIn(repo, ['init', '-q']);
  gitIn(repo, ['config', 'user.name', 'Test User']);
  gitIn(repo, ['config', 'user.email', 'test@example.invalid']);
  gitIn(repo, ['config', 'commit.gpgsign', 'false']);
  writeFileSync(join(repo, 'app.mjs'), 'export const v = 1;\n', 'utf8');
  gitIn(repo, ['add', '-A']);
  gitIn(repo, ['commit', '-qm', 'base']);
  const baseSha = gitIn(repo, ['rev-parse', 'HEAD']);
  writeFileSync(join(repo, 'app.mjs'), 'export const v = 2;\n', 'utf8');
  gitIn(repo, ['add', '-A']);
  gitIn(repo, ['commit', '-qm', 'head']);
  const headSha = gitIn(repo, ['rev-parse', 'HEAD']);

  const manifestPath = join(root, 'manifest-r2.json');
  writeFileSync(manifestPath, JSON.stringify({
    schema_version: 'pdd.review-eval-manifest.v1',
    fixtures: [
      {
        id: 'r2-bad',
        repo: 'example/repo',
        pr: 1,
        base: baseSha,
        head: headSha,
        label: 'bad',
        expected_signals: [{ id: 'sig', description: 'desc', any_terms: ['v = 2'] }],
        min_signals_required: 1,
      },
    ],
  }), 'utf8');

  const metaSwapReport = await runReviewEval(
    { manifest: manifestPath, repoRoot: repo, models: ['test-model'], promptVersions: ['autopilot-v1'] },
    {
      runReviewer: ({ metaDir: mDir }) => {
        rmSync(mDir, { recursive: true, force: true });
        symlinkSync(decoyTarget, mDir);
        return { stdout: '' };
      },
    },
  );
  assert.equal(metaSwapReport.cases[0].verdict, 'ERROR');
  assert.match(metaSwapReport.cases[0].parse_error, /Refusing symlink/);

  // 2. Full Git config/env/template/ext-diff isolation in prepareScratchCheckout AND createCliReviewerRunner
  const evilTemplate = join(root, 'evil-template');
  mkdirSync(join(evilTemplate, 'hooks'), { recursive: true });
  writeFileSync(join(evilTemplate, 'hooks', 'post-commit'), '#!/bin/sh\necho PWNED\n', { mode: 0o755 });

  const poisonedEnv = {
    ...process.env,
    GIT_CONFIG_PARAMETERS: "'http.extraHeader=Authorization: Bearer secret' 'diff.external=/bin/false'",
    GIT_CONFIG_COUNT: '2',
    GIT_CONFIG_KEY_0: 'core.hooksPath',
    GIT_CONFIG_VALUE_0: evilTemplate,
    GIT_CONFIG_KEY_1: 'credential.helper',
    GIT_CONFIG_VALUE_1: 'store',
    GIT_EXTERNAL_DIFF: '/bin/false',
    GIT_TEMPLATE_DIR: evilTemplate,
    GIT_CONFIG: join(root, 'evil.gitconfig'),
    GIT_ASKPASS: '/bin/false',
    SSH_ASKPASS: '/bin/false',
    GH_CONFIG_DIR: join(root, 'host-gh-config'),
  };

  const scratch = prepareScratchCheckout({
    repoRoot: repo,
    fixture: { id: 'r2-iso', base: baseSha, head: headSha },
    env: poisonedEnv,
  });
  t.after(() => scratch.cleanup());
  assert.match(scratch.diffExcerpt, /\+export const v = 2;/);
  assert.equal(existsSync(join(scratch.scratchDir, '.git', 'hooks', 'post-commit')), false);

  const inspectOut = inspectFixtureDiffReadOnly({
    repoRoot: repo,
    fixture: { id: 'r2-iso', base: baseSha, head: headSha },
    env: poisonedEnv,
  });
  assert.deepEqual(inspectOut.changedFiles, ['M\tapp.mjs']);

  const envCheckRunner = createCliReviewerRunner({
    agentCmd: process.execPath,
    agentArgs: [
      '-e',
      `const keys = [
         'GIT_CONFIG_PARAMETERS', 'GIT_CONFIG_COUNT', 'GIT_CONFIG_KEY_0', 'GIT_CONFIG_VALUE_0',
         'GIT_CONFIG_KEY_1', 'GIT_CONFIG_VALUE_1', 'GIT_EXTERNAL_DIFF', 'GIT_TEMPLATE_DIR',
         'GIT_CONFIG', 'GIT_ASKPASS', 'SSH_ASKPASS'
       ];
       const leaked = keys.filter(k => Object.hasOwn(process.env, k));
       process.stdout.write(JSON.stringify({
         leaked,
         attrNoSys: process.env.GIT_ATTR_NOSYSTEM,
         lfsSkip: process.env.GIT_LFS_SKIP_SMUDGE,
         ghConfig: process.env.GH_CONFIG_DIR,
       }));`,
    ],
    env: poisonedEnv,
  });
  const envCheckRes = await envCheckRunner({
    prompt: 'check',
    scratchDir: scratch.scratchDir,
    metaDir: scratch.metaDir,
    resultPath: null,
    model: 'test-model',
  });
  const envObserved = JSON.parse(envCheckRes.stdout);
  assert.deepEqual(envObserved.leaked, []);
  assert.equal(envObserved.attrNoSys, '1');
  assert.equal(envObserved.lfsSkip, '1');
  assert.notEqual(envObserved.ghConfig, poisonedEnv.GH_CONFIG_DIR);
  assert.ok(envObserved.ghConfig && envObserved.ghConfig.startsWith(scratch.metaDir));

  // 3. Dangling symlink temporary escape-and-reenter must be refused by assertSafeCheckedOutSymlink
  const scratchSub = join(root, 'dangling-scratch');
  mkdirSync(scratchSub, { recursive: true });
  const baseName = scratchSub.split('/').at(-1);
  symlinkSync(`missing/../../${baseName}/inside.txt`, join(scratchSub, 'bounce-link'));
  assert.throws(
    () => assertSafeCheckedOutSymlink(scratchSub, 'bounce-link'),
    /Refusing symlink escaping scratch checkout/,
  );

  // 4. Malformed external --compare row with unknown verdict increments clean_errors & error_count
  const malformedCard = computeReviewEvalScorecard([
    { label: 'bad', verdict: 'FAIL', caught: true, expected_signals_count: 1, matched_signals: ['s1'] },
    { label: 'clean', verdict: 'MAYBE', false_positive: false },
  ]);
  assert.equal(malformedCard.clean_total, 1);
  assert.equal(malformedCard.clean_errors, 1);
  assert.equal(malformedCard.error_count, 1);
  assert.equal(malformedCard.meets_target, false);
});
