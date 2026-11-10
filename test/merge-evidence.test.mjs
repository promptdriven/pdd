import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { runTestSuite, calculateCheckCapacity } from '../src/test-suite-queue.mjs';
import { checkAutopilotBase } from '../src/autopilot-base.mjs';
import { readablePrTop, prStatus } from '../src/workflow-pr-body.mjs';
import { stepDone, approveRun } from '../src/workflow-runner.mjs';
import { checkMachine, withCheckLifetime } from './helpers/check-machine.mjs';
import { fixture } from './helpers/workflow-runner-fixture.mjs';
import { pr2Fix6 } from './helpers/readable-pr-fixtures.mjs';

function makeGitRepo(t, { withRecipe = true } = {}) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-merge-evidence-'));
  const env = {
    ...process.env,
    HOME: join(root, 'home'),
    XDG_CONFIG_HOME: join(root, 'config'),
    PDD_SUITE_QUEUE: join(root, 'suite-queue'),
    GIT_CONFIG_NOSYSTEM: '1',
    GIT_CONFIG_GLOBAL: '/dev/null',
  };
  const repo = join(root, 'repo');
  for (const dir of [repo, env.HOME, env.XDG_CONFIG_HOME, env.PDD_SUITE_QUEUE]) {
    fs.mkdirSync(dir, { recursive: true });
  }
  const ports = { ...checkMachine({ taskset: null }).ports, say: () => {} };
  fs.writeFileSync(
    join(env.PDD_SUITE_QUEUE, 'capacity.json'),
    JSON.stringify(withCheckLifetime(calculateCheckCapacity({ checks: 1 }, ports))),
  );
  const git = (...args) =>
    execFileSync('git', args, { cwd: repo, env, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).trim();
  git('init', '-q', '-b', 'main');
  git('config', 'user.email', 'test@example.invalid');
  git('config', 'user.name', 'Test');
  fs.writeFileSync(
    join(repo, 'AGENTS.md'),
    withRecipe
      ? '# Project\n\n## Verification\n\nRun `node --test` on old and new code.\n'
      : '# Project\n\nUse the installed PDD skills.\n',
  );
  fs.writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'demo', scripts: { test: 'node -e "process.exit(0)"' } }));
  fs.writeFileSync(join(repo, 'value.mjs'), 'export const value = 2;\n');
  git('add', '.');
  git('commit', '-qm', 'Initial commit');
  git('update-ref', 'refs/remotes/origin/main', git('rev-parse', 'HEAD'));
  const commonDir = git('rev-parse', '--path-format=absolute', '--git-common-dir');
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  return { root, repo, env, ports, git, commonDir };
}

test('3087 item 1: judgeRealValidation requires a fresh verifier, recipe, old-code reproduction, new-code pass, and relative evidence paths on the exact head', async t => {
  const { judgeRealValidation } = await import('../src/workflow-pr-evidence.mjs');
  assert.equal(typeof judgeRealValidation, 'function', '3087_REAL_VALIDATION_JUDGE_REQUIRED');
  const { git } = makeGitRepo(t);
  const head = git('rev-parse', 'HEAD');

  assert.equal(judgeRealValidation(null, { workflow: 'small-change', headSha: head }).status, 'not-applicable');

  const missing = judgeRealValidation({ content: '', error: 'missing' }, { workflow: 'bug', headSha: head });
  assert.equal(missing.status, 'missing');
  assert.match(missing.reason, /real-validation\.json/);

  const validRecord = {
    schema_version: 'pdd.real-validation.v1',
    run_id: 'run-17',
    head,
    verifier: { session: 'fresh-verifier-17', fresh: true },
    recipe: { path: 'AGENTS.md#Verification', command: 'node --test' },
    oldCode: { outcome: 'reproduced', command: 'node --test', exitCode: 1, summary: 'Bug reproduced on old code.' },
    newCode: { outcome: 'passed', command: 'node --test', exitCode: 0, summary: 'Real validation passed on new code.' },
    evidencePaths: ['old-code-proof.json'],
  };

  const passed = judgeRealValidation(validRecord, {
    workflow: 'bug',
    runId: 'run-17',
    headSha: head,
    builderSessions: ['builder-session-1'],
  });
  assert.equal(passed.status, 'passed');
  assert.equal(passed.head, head);

  const staleHead = judgeRealValidation(validRecord, {
    workflow: 'bug',
    runId: 'run-17',
    headSha: 'f'.repeat(40),
  });
  assert.equal(staleHead.status, 'stale');
  assert.match(staleHead.reason, /PR head is fffffff/);

  const reusedBuilder = judgeRealValidation(validRecord, {
    workflow: 'feature',
    runId: 'run-17',
    headSha: head,
    builderSessions: ['fresh-verifier-17'],
  });
  assert.equal(reusedBuilder.status, 'failed');
  assert.match(reusedBuilder.reason, /builder session instead of a fresh verifier/);

  for (const [override, pattern] of [
    [{ recipe: { path: '', command: '' } }, /missing the verification recipe/],
    [{ oldCode: { outcome: 'passed', command: 'node --test', exitCode: 0, summary: 'Passed on old code' } }, /old-code run did not reproduce/],
    [{ newCode: { outcome: 'failed', command: 'node --test', exitCode: 1, summary: 'Failed on new code' } }, /failed on the new code/],
    [{ evidencePaths: ['/abs/path/log.txt'] }, /missing relative evidence paths/],
  ]) {
    const check = judgeRealValidation(
      { ...validRecord, ...override },
      { workflow: 'feature', runId: 'run-17', headSha: head },
    );
    assert.equal(check.status, 'failed');
    assert.match(check.reason, pattern);
  }
});

test('3087 item 1: workflow done verify records real-validation status and warns when missing or failed on bug/feature', async t => {
  const f = await fixture(t, { name: 'bug' });
  f.ports.skipMetricsDelivery = true;
  await f.run();
  const run0 = f.record();
  await stepDone({ step: 'reproduce', summary: 'Verdict: the bug is in the PROMPT (its check fails on the issue case).', cwd: run0.root }, f.ports);
  fs.mkdirSync(join(run0.root, 'user_stories'), { recursive: true });
  fs.writeFileSync(join(run0.root, 'user_stories/value.md'), 'As a user, I want value 2, so that it works.\n\n## Acceptance criteria\n\n1. Value is 2.\n');
  await stepDone({ step: 'prompt-story', summary: 'Story ready.', cwd: run0.root }, f.ports);
  await approveRun({ ref: '17', cwd: f.source }, f.ports);
  await stepDone({ step: 'check', summary: 'Prompt tests (value): 1 of 1 criteria', cwd: run0.root }, f.ports);
  if (f.record().gate) await approveRun({ ref: '17', cwd: f.source }, f.ports);
  if (f.record().gate) await approveRun({ ref: '17', cwd: f.source }, f.ports);
  fs.writeFileSync(join(run0.root, 'value.mjs'), 'export const value = 2;\n');
  f.git(run0.root, 'add', '.');
  f.git(run0.root, 'commit', '-qm', 'Fix value');
  await stepDone({ step: 'build', summary: 'Built fix', cwd: run0.root }, f.ports);

  const head = f.git(run0.root, 'rev-parse', 'HEAD');
  fs.writeFileSync(
    join(run0.runDir, 'real-validation.json'),
    JSON.stringify({
      schema_version: 'pdd.real-validation.v1',
      run_id: run0.runId,
      head,
      verifier: 'fresh-verifier-bug',
      recipe: 'AGENTS.md#Verification',
      oldCode: { outcome: 'passed', exitCode: 0 },
      newCode: { outcome: 'passed', exitCode: 0 },
      evidencePaths: ['verify.md'],
    }),
  );
  const failedVerify = await stepDone({ step: 'verify', summary: 'Verify with bad oldCode', cwd: run0.root }, f.ports);
  assert.equal(failedVerify.exitCode, 0);
  assert.match(failedVerify.message, /warning: fresh-verifier real-validation record is failed.*Autopilot merge is held/i, '3087_VERIFY_STEP_MUST_CHECK_REAL_VALIDATION');
  assert.equal(f.record().done.verify.realValidation.status, 'failed');

  fs.writeFileSync(
    join(run0.runDir, 'real-validation.json'),
    JSON.stringify({
      schema_version: 'pdd.real-validation.v1',
      run_id: run0.runId,
      head,
      verifier: 'fresh-verifier-bug',
      recipe: 'AGENTS.md#Verification',
      oldCode: { outcome: 'reproduced', exitCode: 1 },
      newCode: { outcome: 'passed', exitCode: 0 },
      evidencePaths: ['verify.md'],
    }),
  );
  const passedVerify = await stepDone({ step: 'verify', summary: 'Verify with valid real-validation.json', cwd: run0.root }, f.ports);
  assert.equal(passedVerify.exitCode, 0);
  assert.match(passedVerify.message, /Real validation: PASS/);
  assert.equal(f.record().done.verify.realValidation.status, 'passed');
});

test('3087 item 2: missing verification recipe opens one small-change PR and asks one grouped question across waiting runs', async t => {
  const { findVerificationRecipe } = await import('../src/workflow-pr-evidence.mjs');
  const { ensureVerificationRecipe, readVerificationRecipeState } = await import('../src/autopilot-base.mjs');
  assert.equal(typeof ensureVerificationRecipe, 'function', '3087_VERIFICATION_RECIPE_DRAFT_PR_REQUIRED');
  const { repo, commonDir } = makeGitRepo(t, { withRecipe: false });
  assert.equal(findVerificationRecipe(repo).present, false);

  const ghCalls = [];
  const execFile = async (file, args, options = {}) => {
    ghCalls.push({ file, args, options });
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'create') {
      return { code: 0, stdout: 'https://github.com/example/project/pull/77\n', stderr: '' };
    }
    if (file === 'git' && args[0] === 'push') {
      return { code: 0, stdout: '', stderr: '' };
    }
    return {
      code: 0,
      stdout: execFileSync(file, args, { cwd: options.cwd ?? repo, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }),
      stderr: '',
    };
  };

  const firstRun = { number: 17, workflow: 'bug', repo: 'example/project', baseBranch: 'main', sourceRoot: repo, root: repo, commonDir };
  const secondRun = { number: 18, workflow: 'feature', repo: 'example/project', baseBranch: 'main', sourceRoot: repo, root: repo, commonDir };

  const first = await ensureVerificationRecipe(firstRun, { execFile, fs });
  assert.equal(first.present, false);
  assert.equal(first.waiting, true);
  assert.equal(first.prRecord.pr, 77);
  assert.equal(first.prRecord.groupedQuestion.questionCount, 1);
  assert.deepEqual(first.prRecord.waitingRuns, [17]);
  assert.equal(ghCalls.filter(c => c.file === 'gh' && c.args[0] === 'pr' && c.args[1] === 'create').length, 1);

  const second = await ensureVerificationRecipe(secondRun, { execFile, fs });
  assert.equal(second.present, false);
  assert.equal(second.waiting, true);
  assert.equal(second.prRecord.pr, 77);
  assert.equal(second.prRecord.groupedQuestion.questionCount, 1, 'must maintain one grouped question, not one per run');
  assert.deepEqual(second.prRecord.waitingRuns, [17, 18]);
  assert.match(second.prRecord.groupedQuestion.text, /#17, #18/);
  assert.equal(ghCalls.filter(c => c.file === 'gh' && c.args[0] === 'pr' && c.args[1] === 'create').length, 1);

  const saved = readVerificationRecipeState(firstRun, fs);
  assert.equal(saved.present, false);
  assert.equal(saved.waiting, true);
  assert.equal(saved.prRecord.pr, 77);
  assert.equal(saved.prRecord.groupedQuestion.questionCount, 1);
  assert.deepEqual(saved.prRecord.waitingRuns, [17, 18]);
});

test('3087 item 3: pdd records an exact-head full-suite receipt and checkAutopilotBase holds merge when receipt or real-validation is missing or stale', async t => {
  const { repo, env, ports, git, commonDir } = makeGitRepo(t, { withRecipe: true });
  const runDir = join(commonDir, 'pdd', 'runs', '17');
  fs.mkdirSync(runDir, { recursive: true });
  const head1 = git('rev-parse', 'HEAD');

  const summary = 'TAP version 13\n1..3\n# tests 3\n# suites 1\n# pass 3\n# fail 0\n# cancelled 0\n# skipped 0\n# todo 0\n';
  const capture = { write() {} };
  const suiteResult = await runTestSuite(
    { cwd: repo, command: `${JSON.stringify(process.execPath)} -e ${JSON.stringify(`process.stdout.write(${JSON.stringify(summary)})`)}`, env },
    { ...ports, stdout: capture, stderr: capture },
  );
  assert.equal(suiteResult.exitCode, 0);

  fs.writeFileSync(join(repo, 'value.mjs'), 'export const value = 3;\n');
  git('add', 'value.mjs');
  git('commit', '-qm', 'Advance head after suite receipt');
  const head2 = git('rev-parse', 'HEAD');

  const runRecord = {
    number: 17,
    runId: 'run-17',
    workflow: 'bug',
    repo: 'example/project',
    baseBranch: 'main',
    sourceRoot: repo,
    root: repo,
    commonDir,
    runDir,
    pr: [{ number: 102, stage: 'code', branch: 'pdd/bug/17-fix' }],
  };
  const ghExec = headSha => async (file, args) => {
    if (file === 'gh' && args[0] === 'api') {
      const path = args[1];
      if (path === 'repos/example/project/pulls/102') {
        return {
          code: 0,
          stdout: JSON.stringify({
            number: 102,
            merged: false,
            head: { sha: headSha },
            base: { ref: 'main', repo: { full_name: 'example/project' } },
          }),
        };
      }
      if (path === 'repos/example/project') {
        return { code: 0, stdout: JSON.stringify({ default_branch: 'main' }) };
      }
      if (path.startsWith('repos/example/project/releases')) {
        return { code: 0, stdout: JSON.stringify([[]]) };
      }
      if (path.startsWith('repos/example/project/compare/')) {
        return { code: 0, stdout: JSON.stringify({ status: 'identical', behind_by: 0 }) };
      }
    }
    return { code: 0, stdout: '' };
  };

  // On head2, no suite receipt matches head2 -> checkAutopilotBase must hold merge (#3087)
  const heldStaleReceipt = await checkAutopilotBase(
    { run: runRecord, pr: 102 },
    { execFile: ghExec(head2), fs, env, suitePorts: ports },
  );
  assert.equal(heldStaleReceipt.exitCode, 1, '3087_CHECK_BASE_MUST_HOLD_WHEN_SUITE_RECEIPT_DOES_NOT_MATCH_PR_HEAD');
  assert.match(heldStaleReceipt.message, /full-suite receipt check failed: missing pdd full-suite receipt/);

  const { readSuiteReceipt } = await import('../src/test-suite-queue.mjs');
  const { judgeSuiteReceipt } = await import('../src/workflow-pr-evidence.mjs');
  const receipt1 = readSuiteReceipt({ cwd: repo, headSha: head1, env }, ports);
  assert.ok(receipt1, 'pdd must record an exact-head receipt');
  assert.equal(receipt1.source.head, head1);
  assert.equal(receipt1.source.clean, true);
  assert.equal(receipt1.exitCode, 0);
  assert.deepEqual(receipt1.counts, { tests: 3, suites: 1, pass: 3, fail: 0, cancelled: 0, skipped: 0, todo: 0 });
  assert.equal(judgeSuiteReceipt(receipt1, { headSha: head1 }).status, 'passed');
  assert.equal(readSuiteReceipt({ cwd: repo, headSha: head2, env }, ports), null);

  // On head1, suite receipt matches head1, but real-validation.json is still missing -> held
  const heldMissingReal = await checkAutopilotBase(
    { run: runRecord, pr: 102 },
    { execFile: ghExec(head1), fs, env, suitePorts: ports },
  );
  assert.equal(heldMissingReal.exitCode, 1);
  assert.match(heldMissingReal.message, /fresh-verifier real validation held: missing fresh-verifier real-validation record/);

  // Write valid real-validation.json for head1 -> checkAutopilotBase passes
  fs.writeFileSync(
    join(runDir, 'real-validation.json'),
    JSON.stringify({
      schema_version: 'pdd.real-validation.v1',
      run_id: 'run-17',
      head: head1,
      verifier: { session: 'fresh-verifier-17', fresh: true },
      recipe: { path: 'AGENTS.md#Verification', command: 'node --test' },
      oldCode: { outcome: 'reproduced', command: 'node --test', exitCode: 1, summary: 'Old code failed.' },
      newCode: { outcome: 'passed', command: 'node --test', exitCode: 0, summary: 'New code passed.' },
      evidencePaths: ['old-code-proof.json'],
    }),
  );
  const ok = await checkAutopilotBase(
    { run: runRecord, pr: 102 },
    { execFile: ghExec(head1), fs, env, suitePorts: ports },
  );
  assert.equal(ok.exitCode, 0, ok.message);
});

test('3087 PR proof table and status reflect realValidation, suiteReceipt, and verificationRecipePr', () => {
  const baseFacts = pr2Fix6();
  baseFacts.records.ci = 'passing';
  baseFacts.records.checker = { verdict: 'PASS' };
  baseFacts.pr1.merged = true;
  baseFacts.stacked = false;
  baseFacts.records.realValidation = {
    applicable: true,
    status: 'passed',
    head: 'a'.repeat(40),
    recipe: 'AGENTS.md#Verification',
    oldCode: { outcome: 'reproduced', exitCode: 1 },
    newCode: { outcome: 'passed', exitCode: 0 },
    evidencePaths: ['old-code-proof.json'],
  };
  baseFacts.records.suiteReceipt = {
    status: 'passed',
    ticket: 4,
    head: 'a'.repeat(40),
    exitCode: 0,
    counts: { tests: 5, pass: 5, fail: 0 },
  };
  assert.equal(prStatus(baseFacts), '✅ Ready to merge');
  const body = readablePrTop(baseFacts).text;
  assert.match(body, /Real validation \(fresh verifier\).*✓ passed \(AGENTS\.md#Verification\)/, '3087_PR_PROOF_MUST_RENDER_REAL_VALIDATION');
  assert.match(body, /Full-suite receipt \(pdd\).*✓ pass \(5 of 5 tests, head aaaaaaa\)/, '3087_PR_PROOF_MUST_RENDER_SUITE_RECEIPT');

  const missingReal = structuredClone(baseFacts);
  missingReal.records.realValidation = { applicable: true, status: 'missing', reason: 'missing fresh-verifier real-validation record' };
  assert.match(prStatus(missingReal), /^⏳ Waiting for fresh-verifier real validation/);
  assert.match(readablePrTop(missingReal).text, /Real validation \(fresh verifier\).*missing \(`real-validation\.json`\)/);

  const failedReal = structuredClone(baseFacts);
  failedReal.records.realValidation = { applicable: true, status: 'failed', reason: 'old-code run did not reproduce the bug' };
  assert.match(prStatus(failedReal), /^⛔ Blocked: .*old-code run did not reproduce the bug/);

  const waitingRecipe = structuredClone(baseFacts);
  waitingRecipe.records.verificationRecipePr = { waiting: true, pr: 88, url: 'https://github.com/example/project/pull/88' };
  assert.match(prStatus(waitingRecipe), /^⏳ Waiting for the verification recipe PR \(#88\)/);
});
