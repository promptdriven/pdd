import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { coreWorld } from './helpers/core-world.mjs';
import { failingLogLines, failingTests } from '../src/autopilot-core.mjs';

const jobRecord = (w, issue) => JSON.parse(readFileSync(join(w.root, 'jobs', `${issue}.json`), 'utf8'));

test('RR1 failingLogLines extracts early TAP, spec and CI failure lines and strips Actions prefixes + secrets', () => {
  const manyOk = Array.from({ length: 30 }, (_, i) => `ok ${i + 4} - passing case ${i + 4}`).join('\n');
  const tapLog = [
    'test\tRun suite\t2026-11-13T06:00:01.1000000Z TAP version 13',
    'test\tRun suite\t2026-11-13T06:00:01.2000000Z ok 1 - boots cleanly',
    'test\tRun suite\t2026-11-13T06:00:01.3000000Z not ok 3 - rejects /proc read on restricted runner',
    'test\tRun suite\t2026-11-13T06:00:01.3100000Z   ---',
    "test\tRun suite\t2026-11-13T06:00:01.3200000Z   location: 'test/proc-guard.test.mjs:18:5'",
    "test\tRun suite\t2026-11-13T06:00:01.3300000Z   error: \"EACCES: permission denied, open '/proc/1/cmdline' token=ghp_1234567890abcdefghijklmnopqrstuv\"",
    'test\tRun suite\t2026-11-13T06:00:01.3400000Z   ...',
    manyOk,
    '1..33', '# tests 33', '# pass 32', '# fail 1',
  ].join('\n');
  const lines = failingLogLines(tapLog);
  assert.ok(lines.some(l => l.includes('not ok 3 - rejects /proc read on restricted runner')));
  assert.ok(lines.some(l => l.includes("location: 'test/proc-guard.test.mjs:18:5'")));
  assert.ok(lines.some(l => l.includes("EACCES: permission denied, open '/proc/1/cmdline'")));
  assert.ok(lines.every(l => !l.includes('ghp_1234567890') && !l.startsWith('test\tRun suite\t')));

  const specLog = [
    '▶ queue recovery',
    '  ✖ restores pending batch (12.4ms)',
    'ℹ tests 10', 'ℹ suites 1', 'ℹ pass 9', 'ℹ fail 1',
    '✖ failing tests:',
    'test at test/queue-recovery.test.mjs:42:3',
    '✖ restores pending batch (12.4ms)',
    '  AssertionError [ERR_ASSERTION]: expected 0 to equal 1',
  ].join('\n');
  const specLines = failingLogLines(specLog);
  assert.ok(specLines.some(l => l.includes('test at test/queue-recovery.test.mjs:42:3')));
  assert.ok(specLines.some(l => l.includes('AssertionError [ERR_ASSERTION]')));
});

test('RR2 #3247 reproducible CI and suite failures give test names, log lines and env; repair reproduces first, fixes, re-verifies and merges', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, repairs: 3 } });

  // Issue #17: CI fails one test that reproduces when run with CI=true before editing, then passes after fix.
  w.issue(17, { title: 'Handle restricted /proc reader in CI mode' });
  await w.tick();
  const buildJob = w.job(17, 'build');
  writeFileSync(join(buildJob.cwd, 'calc.mjs'), "export const readLimit = () => process.env.CI === 'true' ? -1 : 4;\n");
  writeFileSync(join(buildJob.cwd, 'calc.ci.mjs'), "import assert from 'node:assert/strict';\nimport { readLimit } from './calc.mjs';\nassert.equal(readLimit(), 4);\n");
  const first = w.build(17, {
    write: false,
    pathLine: false,
    body: 'Fixes #17\n\nRuntime: not run (no prompt)\nEvidence: tests=pass (1/1)\nPath: d — calc.mjs, calc.ci.mjs — unowned — no contract change — Test: calc.ci.mjs',
    result: { promptChanged: false },
    checks: null,
  });
  w.github.setChecks(first.head, 'failure', 'completed', {
    name: 'ubuntu-latest / test',
    runId: 9101,
    annotations: [{ path: 'test/proc-guard.test.mjs', start_line: 18, title: 'rejects /proc read on restricted runner', message: "EACCES: permission denied, open '/proc/1/cmdline'" }],
    log: [
      'ubuntu-latest / test\tRun tests\t2026-11-13T06:01:00.0000000Z TAP version 13',
      'ubuntu-latest / test\tRun tests\t2026-11-13T06:01:01.0000000Z not ok 1 - rejects /proc read on restricted runner',
      'ubuntu-latest / test\tRun tests\t2026-11-13T06:01:01.0010000Z   ---',
      "ubuntu-latest / test\tRun tests\t2026-11-13T06:01:01.0020000Z   location: 'test/proc-guard.test.mjs:18:5'",
      "ubuntu-latest / test\tRun tests\t2026-11-13T06:01:01.0030000Z   error: \"EACCES: permission denied, open '/proc/1/cmdline'\"",
      'ubuntu-latest / test\tRun tests\t2026-11-13T06:01:01.0040000Z   ...',
    ].join('\n'),
  });

  await w.tick();
  const repair = w.job(17, 'repair');
  assert.ok(repair, 'red CI starts a repair with structured reproduction context');
  assert.match(repair.input, /Failure reproduction details \(#3247\):/);
  assert.match(repair.input, /CI failure \(ubuntu-latest \/ test\):/);
  assert.match(repair.input, /platform: Linux \(CI runner\)/);
  assert.match(repair.input, /concurrency: .*\$PDD_CHECK_CPUS/);
  assert.match(repair.input, /restricted non-root CI container permissions/);
  assert.match(repair.input, /Failing tests: rejects \/proc read on restricted runner \(proc-guard\.test\.mjs\)/);
  assert.match(repair.input, /EACCES: permission denied, open '\/proc\/1\/cmdline'/);
  assert.match(repair.input, /Before you edit any file, run those exact failing tests first in the matching environment/);
  assert.match(repair.input, /After your fix, run those exact failing tests again in the same environment/);

  // Repair step 1: reproduce failure in CI=true environment BEFORE changing code.
  const beforeFix = spawnSync(process.execPath, ['calc.ci.mjs'], { cwd: repair.cwd, env: { ...process.env, CI: 'true' }, encoding: 'utf8' });
  assert.notEqual(beforeFix.status, 0, 'reproduction fails in CI=true before editing code');

  // Repair step 2: fix code and verify same test passes in CI=true environment.
  writeFileSync(join(repair.cwd, 'calc.mjs'), 'export const readLimit = () => 4;\n');
  const afterFix = spawnSync(process.execPath, ['calc.ci.mjs'], { cwd: repair.cwd, env: { ...process.env, CI: 'true' }, encoding: 'utf8' });
  assert.equal(afterFix.status, 0, 'same test passes in CI=true after fix');

  w.build(17, {
    role: 'repair',
    write: false,
    pathLine: false,
    body: 'Fixes #17\n\nRuntime: not run (no prompt)\nEvidence: tests=pass (1/1)\nPath: d — calc.mjs, calc.ci.mjs — unowned — no contract change — Test: calc.ci.mjs',
    result: { promptChanged: false },
    checks: 'success',
  });
  await w.tick();
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick();
  assert.deepEqual(w.github.merges, [first.pr.number], 'fixed PR merges cleanly');

  // Issue #18: local full suite fails early in a long TAP log -> repair brief shows early TAP error + suite environment.
  w.issue(18, { title: 'Preserve suite recorder completion' });
  await w.tick();
  w.build(18, { body: 'Fixes #18\n\nRuntime: not run (no prompt)', result: { promptChanged: false } });
  await w.tick();
  w.review(18, 'PASS');
  const trailingOk = Array.from({ length: 20 }, (_, i) => `ok ${i + 2} - unrelated test ${i + 2}`).join('\n');
  w.say(18, 'suite', [
    'TAP version 13',
    'not ok 1 - suite recorder keeps completion marker',
    '  ---',
    "  location: 'test/suite-recorder.test.mjs:29:7'",
    "  error: 'AssertionError: expected completion to be saved'",
    '  ...',
    trailingOk,
    '1..21', '# tests 21', '# pass 20', '# fail 1',
  ].join('\n'));
  w.suite(18, 1);
  await w.tick();
  const suiteRepair = w.job(18, 'repair');
  assert.ok(suiteRepair);
  assert.match(suiteRepair.input, /Full test suite failure \(`npm test`/);
  assert.match(suiteRepair.input, /local full-suite runner \(pdd workflow suite\)/);
  assert.match(suiteRepair.input, /Failing tests: suite recorder keeps completion marker \(suite-recorder\.test\.mjs\)/);
  assert.match(suiteRepair.input, /AssertionError: expected completion to be saved/, 'early TAP assertion is preserved even past 20 trailing lines');
});

test('RR3 #3247 "not reproduced" triggers one check rerun with zero code change and zero burned repair round, then merges', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, repairs: 1 } });
  w.issue(21, { title: 'Keep helper fast' });
  await w.tick();
  const built = w.build(21, { body: 'Fixes #21\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });
  w.github.setChecks(built.head, 'failure', 'completed', {
    name: 'ubuntu-latest / test',
    runId: 9202,
    completedAt: '2026-11-13T06:10:00Z',
    log: "ubuntu-latest / test\tRun tests\t2026-11-13T06:09:59.0000000Z not ok 4 - transient socket race\nubuntu-latest / test\tRun tests\t2026-11-13T06:09:59.0010000Z   ---\nubuntu-latest / test\tRun tests\t2026-11-13T06:09:59.0020000Z   location: 'test/flaky-socket.test.mjs:11:3'\nubuntu-latest / test\tRun tests\t2026-11-13T06:09:59.0030000Z   ...",
  });
  // Simulate GitHub briefly returning the stale completed failure right after rerun-failed-jobs before flipping to green.
  w.github.onRerun = () => {};

  await w.tick();
  const repair = w.job(21, 'repair');
  assert.ok(repair);
  assert.match(repair.input, /"outcome":"not reproduced"/);

  // Repair runs exact test, does not reproduce, leaves an untracked temp file that must be cleaned, and pushes nothing.
  writeFileSync(join(repair.cwd, 'scratch-repro.tmp'), 'ran repro\n');
  w.finish(21, 'repair', {
    result: {
      outcome: 'not reproduced',
      command: 'CI=true node --test --test-concurrency=$PDD_CHECK_CPUS test/flaky-socket.test.mjs',
      detail: '1..1\n# pass 1\n# fail 0',
    },
  });

  await w.tick();
  assert.equal(w.github.reruns.length, 1, 'triggers exactly one CI rerun');
  assert.deepEqual(w.github.reruns[0], { kind: 'rerun-failed-jobs', id: 9202, at: w.now() });
  const afterRerun = jobRecord(w, 21);
  assert.equal(afterRerun.phase, 'pr', 'returns to merge check without starting a second repair on stale pre-rerun CI');
  assert.equal(afterRerun.repairs, 0, 'does not burn the 1-repair safety cap');
  assert.deepEqual(afterRerun.rounds ?? [], [], 'does not keep tentative round in sameFinding history');
  assert.equal(afterRerun.head, built.head, 'no code change or new commit');
  const statusOut = spawnSync('git', ['status', '--porcelain'], { cwd: repair.cwd, encoding: 'utf8' }).stdout.trim();
  assert.equal(statusOut, '', 'worktree remains completely clean');

  // Now the GitHub Actions rerun completes green; review and suite pass -> PR merges with 0 repairs used.
  w.github.setChecks(built.head, 'success', 'completed', { name: 'ubuntu-latest / test', runId: 9202, completedAt: '2026-11-13T06:12:00Z' });
  await w.tick();
  w.review(21, 'PASS');
  w.suite(21, 0);
  await w.tick();
  assert.deepEqual(w.github.merges, [built.pr.number]);
  assert.equal(w.started.filter(j => j.issue === 21 && j.role === 'repair').length, 1);

  // Local suite flake: review already passed, suite fails transiently, "not reproduced" reruns ONLY the suite (reusing the passing review) and merges.
  w.issue(22, { title: 'Local suite transient flake' });
  await w.tick();
  const built22 = w.build(22, { body: 'Fixes #22\n\nRuntime: not run (no prompt)', result: { promptChanged: false } });
  await w.tick();
  w.review(22, 'PASS');
  w.say(22, 'suite', "not ok 1 - transient timer\n  ---\n  location: 'test/timer.test.mjs:9:3'\n  ...");
  w.suite(22, 1);
  await w.tick();
  w.finish(22, 'repair', { result: { outcome: 'not reproduced', command: 'CI=true node --test test/timer.test.mjs' } });
  await w.tick();
  assert.equal(w.started.filter(j => j.issue === 22 && j.role === 'review').length, 1, 'passing review at same head is preserved');
  assert.equal(w.started.filter(j => j.issue === 22 && j.role === 'suite').length, 2, 'failing local suite is rerun once');
  w.suite(22, 0);
  await w.tick();
  assert.deepEqual(w.github.merges, [built.pr.number, built22.pr.number]);
});

test('RR4 #3247 + #3181 guards: at most one rerun per head, rejected on non-test reds, and base-test-red files deduped pdd report without burning a repair', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, repairs: 2 } });

  // 4a. Second "not reproduced" at the same head after rerun fails again stops cleanly without a second rerun.
  w.issue(31, { title: 'Bounded rerun guard' });
  await w.tick();
  const p31 = w.build(31, { body: 'Fixes #31\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });
  w.github.setChecks(p31.head, 'failure', 'completed', { name: 'ci', runId: 9301, completedAt: '2026-11-13T06:20:00Z' });
  await w.tick();
  w.finish(31, 'repair', { result: { outcome: 'not-reproduced', command: 'CI=true npm test' } });
  await w.tick();
  assert.equal(w.github.reruns.length, 1);
  // Rerun finishes red again with a new completion timestamp -> second repair prompt forbids "not reproduced".
  w.github.setChecks(p31.head, 'failure', 'completed', { name: 'ci', runId: 9301, completedAt: '2026-11-13T06:25:00Z' });
  await w.tick();
  const secondRepair = w.job(31, 'repair');
  assert.match(secondRepair.input, /already reran the failing check once/);
  assert.doesNotMatch(secondRepair.input, /- Not reproduced \(only when/);
  w.finish(31, 'repair', { result: { outcome: 'not reproduced', command: 'CI=true npm test' } });
  await w.tick();
  assert.equal(w.github.reruns.length, 1, 'never triggers a second rerun at the same head');
  assert.ok(w.github.issues.get(31).labels.includes('pdd:stuck'), 'ends cleanly instead of looping');

  // 4b. Review FAIL + suite fail: "not reproduced" is disallowed and triggers zero reruns.
  w.issue(32, { title: 'Non-test red guard' });
  await w.tick();
  w.build(32, { body: 'Fixes #32\n\nRuntime: not run (no prompt)', result: { promptChanged: false } });
  await w.tick();
  w.review(32, 'FAIL', ['P2 change-32.txt:1 missing edge check']);
  w.suite(32, 1);
  await w.tick();
  const mixedRepair = w.job(32, 'repair');
  assert.doesNotMatch(mixedRepair.input, /- Not reproduced \(only when/);
  w.finish(32, 'repair', { result: { outcome: 'not reproduced', command: 'npm test' } });
  await w.tick();
  assert.equal(w.github.reruns.length, 1, 'no extra rerun on non-test red');
  assert.ok(w.github.issues.get(32).labels.includes('pdd:stuck'));

  // 4c. #3181: failing test also fails on origin/main -> base-test-red files one deduped pdd report, 0 guessed edits.
  w.issue(33, { title: 'Unrelated main failure (#3181)' });
  await w.tick();
  const p33 = w.build(33, { body: 'Fixes #33\n\nRuntime: not run (no prompt)', result: { promptChanged: false } });
  await w.tick();
  w.review(33, 'PASS');
  w.say(33, 'suite', "not ok 1 - queue repair on main\n  ---\n  location: 'test/interpreter-queue-repair.test.mjs:12:3'\n  ...");
  w.suite(33, 1);
  await w.tick();
  w.finish(33, 'repair', {
    result: {
      outcome: 'failed',
      kind: 'pdd',
      component: 'base-suite',
      code: 'base-test-red',
      cause: 'test/interpreter-queue-repair.test.mjs also fails on origin/main',
      detail: 'CI=true node --test test/interpreter-queue-repair.test.mjs -> exit 1 on merge-base',
    },
  });
  await w.tick();
  assert.equal(w.github.prs.get(p33.pr.number).head, p33.head, 'PR head has zero guessed edits');
  const drafts = readdirSync(join(w.reportRoot, 'drafts')).filter(f => f.endsWith('.json'));
  assert.equal(drafts.length, 1, 'saves one deduped pdd report for the main failure');
});

test('RR5 #3247 ANSI escapes and UTF-8 BOM Actions prefixes are stripped before secret redaction and TAP/spec parsing, and spec tree rows do not starve failing-tests details', () => {
  const fakePat = `ghp_${'x'.repeat(30)}`;
  const fakeSk = `sk-${'y'.repeat(20)}`;
  const fakeKvSecret = 'super_secret_ci_value_99';
  const coloredTap = [
    `\uFEFFubuntu\tRun tests\t2026-11-13T07:00:01.0000000Z \x1b[31mnot ok 1 - colored tap check\x1b[39m`,
    `\uFEFFubuntu\tRun tests\t2026-11-13T07:00:01.0010000Z   ---`,
    `\uFEFFubuntu\tRun tests\t2026-11-13T07:00:01.0020000Z   \x1b[90mlocation: 'test/colored-tap.test.mjs:19:5'\x1b[39m`,
    `\uFEFFubuntu\tRun tests\t2026-11-13T07:00:01.0030000Z   error: "leaked \x1b[31m${fakePat}\x1b[39m and \x1b[31mtoken\x1b[0m=${fakeKvSecret} and \x1b[33mBearer ${fakeSk}\x1b[0m"`,
    `\uFEFFubuntu\tRun tests\t2026-11-13T07:00:01.0040000Z   ...`,
  ].join('\n');

  const parsedTapTests = failingTests(coloredTap);
  assert.deepEqual(parsedTapTests, [{ name: 'colored tap check', file: 'test/colored-tap.test.mjs' }]);
  const parsedTapLines = failingLogLines(coloredTap);
  assert.ok(parsedTapLines.some(l => l.includes('not ok 1 - colored tap check') && !l.includes('[31m')));
  assert.ok(parsedTapLines.some(l => l.includes("location: 'test/colored-tap.test.mjs:19:5'")));
  for (const line of parsedTapLines) {
    assert.ok(!line.includes(fakePat), `PAT must be redacted even inside ANSI color codes: ${line}`);
    assert.ok(!line.includes(fakeKvSecret), `split token= secret must be redacted: ${line}`);
    assert.ok(!line.includes(fakeSk), `Bearer secret must be redacted: ${line}`);
    assert.ok(!line.includes('\uFEFF') && !line.includes('ubuntu\tRun tests\t'), `UTF-8 BOM + Actions prefix must be stripped: ${line}`);
  }

  // Large spec tree with 30 failed rows and interleaved ✔/▶/ℹ rows must NOT starve the ✖ failing tests: detail section.
  const specTree = Array.from({ length: 30 }, (_, i) => [
    `  \x1b[31m✖\x1b[39m tree case ${i + 1} (2.1ms)`,
    `  \x1b[32m✔\x1b[39m passing sibling ${i + 1} (0.5ms)`,
  ]).flat();
  const fullSpecLog = [
    '▶ big suite',
    ...specTree,
    '✖ big suite (85.0ms)',
    'ℹ tests 60', 'ℹ suites 1', 'ℹ pass 30', 'ℹ fail 30',
    '\x1b[31m✖ failing tests:\x1b[39m',
    'test at test/spec-starvation.test.mjs:74:3',
    '\x1b[31m✖ tree case 1 (2.1ms)\x1b[39m',
    '  AssertionError [ERR_ASSERTION]: expected 42 to equal 7',
    '      at TestContext.<anonymous> (file:///repo/test/spec-starvation.test.mjs:76:12)',
    '      at Test.runInAsyncScope (node:async_hooks:206:9)',
  ].join('\n');

  const specTests = failingTests(fullSpecLog, 5);
  assert.deepEqual(specTests[0], { name: 'tree case 1', file: 'test/spec-starvation.test.mjs' });
  const specLines = failingLogLines(fullSpecLog, 25);
  assert.ok(specLines.some(l => l.includes('✖ failing tests:')));
  assert.ok(specLines.some(l => l.includes('test at test/spec-starvation.test.mjs:74:3')), 'file:line detail is preserved despite 30 tree ✖ rows');
  assert.ok(specLines.some(l => l.includes('AssertionError [ERR_ASSERTION]: expected 42 to equal 7')));
  assert.ok(specLines.every(l => !l.includes('passing sibling') && !/^\s*ℹ\s/.test(l)), 'passing/info rows never consume failure context');

  // Partial spec log without ✖ failing tests: keeps tree ✖ row without pulling ✔/ℹ siblings into ctxLeft.
  const partialSpec = [
    '▶ live suite',
    '  ✖ early flake (3.2ms)',
    '  ✔ healthy sibling (1.0ms)',
    '  ℹ pass 1',
  ].join('\n');
  const partialLines = failingLogLines(partialSpec, 25);
  assert.deepEqual(partialLines, ['  ✖ early flake (3.2ms)']);
});

test('RR6 #3247 check preservation keeps passing vectors/coverage/untested across "not reproduced" and never drops a prior Review: FAIL when CI turns red later', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, repairs: 2 } });

  // 6a. Passing vectors (state: 'done'), review, coverage and untested are preserved across a local suite "not reproduced" rerun.
  w.baseCommit('test/sample.vectors.test.mjs', "import test from 'node:test';\ntest('v1', () => {});\n");
  w.issue(41, { title: 'Preserve vectors and coverage on suite rerun' });
  await w.tick();
  const build41 = w.job(41, 'build');
  writeFileSync(join(build41.cwd, 'test/sample.vectors.test.mjs'), "import test from 'node:test';\ntest('v1 updated', () => {});\n");
  const built41 = w.build(41, {
    body: 'Fixes #41\n\nRuntime: PASS\nEvidence: runtime=pass (1/1); vectors=pass (3/3); tests=pass (3/3)\nPath: d — test/sample.vectors.test.mjs, change-41.txt — unowned — no contract change — Test: test/sample.vectors.test.mjs',
    result: { promptChanged: false, evidence: 'Evidence: runtime=pass (1/1); vectors=pass (3/3); tests=pass (3/3)' },
  });
  await w.tick();
  assert.equal(w.started.filter(j => j.issue === 41 && j.role === 'vectors').length, 1);
  const evidenceReadsBefore = w.evidenceReads.length;
  w.review(41, 'PASS');
  w.vectorsRun(41, { tests: 3 });
  w.say(41, 'suite', "not ok 1 - transient suite socket\n  ---\n  location: 'test/socket.test.mjs:8:3'\n  ...");
  w.suite(41, 1);
  await w.tick();

  w.finish(41, 'repair', { result: { outcome: 'not reproduced', command: 'CI=true node --test test/socket.test.mjs' } });
  await w.tick();
  const rec41 = jobRecord(w, 41);
  assert.equal(rec41.vectors?.state, 'done', 'passing vectors state: done is preserved across not-reproduced');
  assert.equal(w.started.filter(j => j.issue === 41 && j.role === 'vectors').length, 1, 'vectors job does not re-run');
  assert.equal(w.started.filter(j => j.issue === 41 && j.role === 'review').length, 1, 'passing review does not re-run');
  assert.equal(w.evidenceReads.length, evidenceReadsBefore, 'green runtimeCoverage is preserved without re-reading');
  assert.equal(w.started.filter(j => j.issue === 41 && j.role === 'suite').length, 2, 'only failing suite reruns');
  w.suite(41, 0);
  await w.tick();
  assert.deepEqual(w.github.merges, [built41.pr.number]);

  // 6b. Prior Review: FAIL recorded while CI was pending + vectors running must stay in reds/findings when CI turns red on a later tick.
  w.issue(42, { title: 'Keep prior Review FAIL when CI turns red later' });
  await w.tick();
  const build42 = w.job(42, 'build');
  writeFileSync(join(build42.cwd, 'test/sample.vectors.test.mjs'), "import test from 'node:test';\ntest('v2 updated', () => {});\n");
  const built42 = w.build(42, {
    body: 'Fixes #42\n\nRuntime: not run (no prompt)\nEvidence: runtime=not-run; vectors=pass (3/3); tests=pass (3/3)\nPath: d — test/sample.vectors.test.mjs, change-42.txt — unowned — no contract change — Test: test/sample.vectors.test.mjs',
    result: { promptChanged: false, evidence: 'Evidence: runtime=not-run; vectors=pass (3/3); tests=pass (3/3)' },
    checks: null,
  });
  w.github.setChecks(built42.head, null, 'in_progress', { name: 'ci', runId: 9402 });
  await w.tick();

  // Review finishes with FAIL while vectors is still running -> mergeCheck records job.review.verdict = 'FAIL' and waits in red-wait.
  w.review(42, 'FAIL', ['P2 change-42.txt:1 missing input validation']);
  await w.tick();
  assert.equal(jobRecord(w, 42).review?.verdict, 'FAIL');
  assert.equal(jobRecord(w, 42).phase, 'pr', 'waits briefly for running vectors before starting repair');

  // Next tick: CI turns red! Prior Review: FAIL must NOT be skipped when CI makes reds non-empty before reviewState runs.
  w.github.setChecks(built42.head, 'failure', 'completed', { name: 'ci', runId: 9402, completedAt: '2026-11-13T07:10:00Z' });
  await w.tick();
  const repair42 = w.job(42, 'repair');
  assert.ok(repair42, 'starts repair with both CI failure and prior Review FAIL');
  assert.match(repair42.input, /CI check ci failed/);
  assert.match(repair42.input, /Review FAIL from a fresh reviewer: P2 change-42\.txt:1 missing input validation/);
  assert.doesNotMatch(repair42.input, /- Not reproduced \(only when/, 'disallows not-reproduced because Review FAIL is also red');

  w.finish(42, 'repair', { result: { outcome: 'not reproduced', command: 'CI=true npm test' } });
  await w.tick();
  assert.equal(w.github.reruns.length, 0, 'never triggers a CI rerun when Review FAIL was present');
  assert.ok(w.github.issues.get(42).labels.includes('pdd:stuck'));
});

test('RR7 #3247 duplicate-named passing vs failing check runs, >5 failed shards, single log per runId, and sibling check completion during ciRerunPending', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, repairs: 1 } });
  w.issue(51, { title: 'Matrix duplicate check names and sibling pending rerun' });
  await w.tick();
  const built = w.build(51, { body: 'Fixes #51\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });

  let logFetches9501 = 0;
  const origGh = w.github.gh;
  w.github.gh = async (args, opts) => {
    if (args[0] === 'run' && args[1] === 'view' && args[2] === '9501') logFetches9501++;
    return origGh(args, opts);
  };
  w.github.runLogs.set(9500, 'matrix\tPass\t2026-11-13T07:20:00.0000000Z not ok 99 - should never be read from passing run');
  w.github.runLogs.set(9501, "matrix\tFail\t2026-11-13T07:20:01.0000000Z not ok 1 - unique-matrix-flake-marker\nmatrix\tFail\t2026-11-13T07:20:01.0010000Z   location: 'test/matrix-flake.test.mjs:12:3'");
  w.github.runLogs.set(9502, "extra\tFail\t2026-11-13T07:20:02.0000000Z not ok 2 - extra-workflow-flake\nextra\tFail\t2026-11-13T07:20:02.0010000Z   location: 'test/extra-flake.test.mjs:7:3'");
  w.github.workflowRuns.set(9501, { id: 9501, head_sha: built.head, status: 'completed', conclusion: 'failure' });
  w.github.workflowRuns.set(9502, { id: 9502, head_sha: built.head, status: 'completed', conclusion: 'failure' });

  const checks = [
    // Passing check sharing the exact same name 'matrix-test' as failing shards below:
    {
      id: 8101, name: 'matrix-test', status: 'completed', conclusion: 'success', completed_at: '2026-11-13T07:19:50Z',
      details_url: `https://github.com/${w.github.repo}/actions/runs/9500/job/8101`,
      output: { title: 'Passing shard marker', summary: 'Error: Passing-Shard-Noise-Should-Be-Ignored' },
    },
    // 5 failing shards in workflow run 9501:
    ...Array.from({ length: 5 }, (_, i) => ({
      id: 8102 + i, name: 'matrix-test', status: 'completed', conclusion: 'failure', completed_at: '2026-11-13T07:20:05Z',
      details_url: `https://github.com/${w.github.repo}/actions/runs/9501/job/${8102 + i}`,
      output: { title: `Shard ${i + 1} failed`, summary: '' },
    })),
    // 6th failing check in a second workflow run 9502 (beyond .slice(0, 5)):
    {
      id: 8107, name: 'extra-ci', status: 'completed', conclusion: 'failure', completed_at: '2026-11-13T07:20:06Z',
      details_url: `https://github.com/${w.github.repo}/actions/runs/9502/job/8107`,
      output: { title: 'Extra CI failed', summary: '' },
    },
    // Slow sibling check still in progress:
    { id: 8108, name: 'slow-macos', status: 'in_progress', conclusion: null, started_at: '2026-11-13T07:18:00Z' },
  ];
  w.github.checks.set(built.head, checks);
  w.github.onRerun = () => {};

  await w.tick();
  const rec = jobRecord(w, 51);
  assert.deepEqual(rec.repairReproduce.runIds, [9501, 9502], 'excludes passing duplicate-name runId 9500 and includes 6th failed check runId 9502');
  assert.deepEqual(rec.repairReproduce.checkIds, [8102, 8103, 8104, 8105, 8106, 8107], 'excludes passing checkId 8101 and keeps all 6 failed checkIds');
  assert.equal(logFetches9501, 1, 'fetches workflow 9501 log once');

  const repair = w.job(51, 'repair');
  assert.doesNotMatch(repair.input, /Passing-Shard-Noise-Should-Be-Ignored/, 'ignores passing duplicate-named check output');
  const logLineOccurrences = rec.repairReproduce.checks[0].lines.filter(l => l.includes('unique-matrix-flake-marker')).length;
  assert.equal(logLineOccurrences, 1, 'workflow log line appears once in failing log lines rather than duplicated per shard');
  assert.match(repair.input, /extra-workflow-flake/, '6th failed check workflow log is also included');

  // Repair reports "not reproduced" -> both 9501 and 9502 are rerun; GitHub still serves stale failed snapshots right after rerun.
  w.finish(51, 'repair', { result: { outcome: 'not reproduced', command: 'CI=true node --test test/matrix-flake.test.mjs test/extra-flake.test.mjs' } });
  await w.tick();
  assert.deepEqual(w.github.reruns.map(r => r.id), [9501, 9502]);
  assert.equal(jobRecord(w, 51).phase, 'pr');

  // Unrelated sibling 'slow-macos' completes green while 8102..8107 STILL return stale pre-rerun failures!
  w.github.checks.set(built.head, checks.map(c => c.id === 8108 ? { ...c, status: 'completed', conclusion: 'success', completed_at: '2026-11-13T07:20:30Z' } : c));
  await w.tick();
  assert.equal(jobRecord(w, 51).phase, 'pr', 'sibling check finishing does NOT clear ciRerunPending while failed checks remain at stale pre-rerun snapshot');
  assert.equal(w.started.filter(j => j.issue === 51 && j.role === 'repair').length, 1, 'no premature second repair started');

  // Now the rerun checks complete green -> review and suite pass -> merges!
  w.github.checks.set(built.head, checks.map(c => ({ ...c, status: 'completed', conclusion: 'success', completed_at: '2026-11-13T07:21:30Z' })));
  await w.tick();
  w.review(51, 'PASS');
  w.suite(51, 0);
  await w.tick();
  assert.deepEqual(w.github.merges, [built.pr.number]);
});

test('RR8 #3247 rerunFailedCi rejects status === 0 / un-rerunnable CI cleanly, and "not reproduced" handles transient PR API failure and closed PRs', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, repairs: 2 } });

  // 8a. gh failing with no HTTP status (status === 0) on rerun endpoints + external status with no rerunnable ID -> ends as checks-red with 0 false rerun claims.
  w.issue(61, { title: 'Unrerunnable CI and status 0 guard' });
  await w.tick();
  const built61 = w.build(61, { body: 'Fixes #61\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });
  w.github.setChecks(built61.head, 'failure', 'completed', { name: 'ci', runId: 9601, completedAt: '2026-11-13T07:30:00Z' });
  const baseGh = w.github.gh;
  let failRerunNoHeader = true;
  let failNextPullRead = false;
  w.github.gh = async (args, opts) => {
    const endpoint = args.find((word, i) => i > 0 && /^repos\//.test(word)) ?? '';
    if (failRerunNoHeader && /\/(?:rerun-failed-jobs|rerun|rerequest)$/.test(endpoint)) {
      return { code: 1, stdout: '', stderr: 'gh: transport reset before HTTP status\n' };
    }
    if (failNextPullRead && /\/pulls\/\d+$/.test(endpoint) && !args.includes('--method')) {
      // methodOf defaults to GET; also match explicit --method GET
    }
    if (failNextPullRead && /\/pulls\/\d+$/.test(endpoint) && (!args.includes('--method') || args[args.indexOf('--method') + 1] === 'GET')) {
      failNextPullRead = false;
      return { code: 1, stdout: 'HTTP/2.0 502 Bad Gateway\r\n\r\n{"message":"Bad Gateway"}', stderr: 'gh: HTTP 502\n' };
    }
    return baseGh(args, opts);
  };

  await w.tick();
  w.finish(61, 'repair', { result: { outcome: 'not reproduced', command: 'CI=true npm test' } });
  await w.tick();
  assert.equal(w.github.reruns.length, 0, 'status === 0 never counts as a successful rerun');
  assert.equal(w.started.filter(j => j.issue === 61 && j.role === 'repair').length, 1, 'does not start a second repair claiming CI was reran');
  assert.ok(w.github.issues.get(61).labels.includes('pdd:stuck'), 'ends cleanly as checks-red');
  assert.match(w.comments(61).at(-1), /could not be rerun automatically on GitHub/);
  failRerunNoHeader = false;

  // 8b. Transient GET /pulls/P 502 is NOT swallowed to bypass head-moved; retry sees moved head and ends as head-moved with 0 reruns.
  w.issue(62, { title: 'Transient PR read failure before head-moved' });
  await w.tick();
  const built62 = w.build(62, { body: 'Fixes #62\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });
  w.github.setChecks(built62.head, 'failure', 'completed', { name: 'ci', runId: 9602, completedAt: '2026-11-13T07:35:00Z' });
  await w.tick();
  // Someone pushes a new commit to the PR branch while repair runs, and the first GET /pulls/P returns 502.
  const pr62 = w.github.prs.get(built62.pr.number);
  const movedSha = 'b'.repeat(40);
  pr62.head = movedSha;
  pr62.syncedTip = spawnSync('git', ['--git-dir', w.remote, 'rev-parse', `refs/heads/${pr62.branch}`], { encoding: 'utf8' }).stdout.trim();
  failNextPullRead = true;
  w.finish(62, 'repair', { result: { outcome: 'not reproduced', command: 'CI=true npm test' } });

  await w.tick();
  assert.equal(w.github.reruns.length, 0, 'transient PR GET failure does not proceed to rerunFailedCi');
  assert.ok(!w.github.issues.get(62).labels.includes('pdd:stuck'), 'waits to retry after transient GitHub 502');

  await w.tick();
  assert.equal(w.github.reruns.length, 0, 'retry detects head-moved and triggers zero reruns');
  assert.match(w.comments(62).at(-1), /at head bbbbbbb/);

  // 8c. Closed PR while repair ran -> ends as pr-closed without calling rerunFailedCi.
  w.issue(63, { title: 'PR closed before not-reproduced completes' });
  await w.tick();
  const built63 = w.build(63, { body: 'Fixes #63\n\nRuntime: not run (no prompt)', result: { promptChanged: false }, checks: null });
  w.github.setChecks(built63.head, 'failure', 'completed', { name: 'ci', runId: 9603, completedAt: '2026-11-13T07:40:00Z' });
  await w.tick();
  w.github.prs.get(built63.pr.number).state = 'closed';
  w.finish(63, 'repair', { result: { outcome: 'not reproduced', command: 'CI=true npm test' } });
  await w.tick();
  assert.equal(w.github.reruns.length, 0, 'closed PR never triggers rerunFailedCi');
  assert.match(w.comments(63).at(-1), /closed without a merge/);
});
