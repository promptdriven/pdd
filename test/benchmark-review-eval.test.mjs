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

import {
  REVIEW_EVAL_TARGETS,
  assertCleanPublicText,
  computeNorthStarScorecard,
  computeReviewEvalScorecard,
} from '../scripts/benchmark/scorecard.mjs';
import {
  ALLOWED_FIXTURE_EVIDENCE_KEYS,
  DEFAULT_MANIFEST_PATH,
  FORBIDDEN_SCRATCH_PATHS,
  assertPromptIsolation,
  buildReviewerPrompt,
  createCliReviewerRunner,
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
    id: 'redos-signal',
    label: 'bad',
    base: 'a1b09cb9',
    head: '0db39638',
    expected_signals: [{ id: 'evil', patterns: ['(a+)+b'] }],
  }), /exponential regex/);

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

  // North-Star scorecard compatibility (opt-in reviewEval does not alter default callers)
  const defaultNs = computeNorthStarScorecard();
  assert.equal('review_eval' in defaultNs, false);
  const withReviewNs = computeNorthStarScorecard({ reviewEval: [caughtCase, cleanPass] });
  assert.equal(withReviewNs.review_eval.bug_recall, 100);
  assert.equal(withReviewNs.review_eval.clean_fp_rate, 0);
  assert.equal(withReviewNs.review_eval.meets_target, true);
  assert.deepEqual(withReviewNs.review_eval.targets, REVIEW_EVAL_TARGETS);
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

  const scriptPath = resolve('scripts/benchmark/run-review-eval.mjs');

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

  // When full repo history is present (non-shallow clone), also verify the shipped default manifest (#2559 + #2560) resolves cleanly
  const hasReal2559 = spawnSync('git', ['cat-file', '-e', 'a1b09cb9^{commit}'], { encoding: 'utf8' }).status === 0
    && spawnSync('git', ['cat-file', '-e', '1a4b37803^{commit}'], { encoding: 'utf8' }).status === 0;
  if (hasReal2559) {
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
