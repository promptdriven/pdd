import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { coreWorld } from './helpers/core-world.mjs';
import { failingLogLines } from '../src/autopilot-core.mjs';

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
