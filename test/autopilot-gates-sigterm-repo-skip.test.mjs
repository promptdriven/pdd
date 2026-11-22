import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { coreWorld } from './helpers/core-world.mjs';
import { checkMachine, withCheckLifetime } from './helpers/check-machine.mjs';
import { coreSettings, coreStatus } from '../src/autopilot-core.mjs';
import { calculateCheckCapacity, readSuiteProgress, reconcileSuiteQueue, runTestSuite, suiteStatusWords } from '../src/test-suite-queue.mjs';
import {
  NEEDS_OTHER_REPO_LABEL,
  OTHER_REPO_MARKER_PREFIX,
  activeIntake,
  cardCommand,
  detectWrongRepositoryIssue,
  improveCommand,
  nativeFacts,
  shadowIntake,
} from '../src/autopilot-intake.mjs';
import { codexProviderConfigArgs, forensicsCommand, runPreRunForensics } from '../src/autopilot-forensics.mjs';
import { prepareCloudStepExecution } from '../src/login-pool.mjs';
import { serializeValidationReceipt } from '../src/validation-evidence.mjs';

const okHttp = (status, body) => ({
  code: status < 300 ? 0 : 1,
  stdout: `HTTP/2.0 ${status} OK\r\nX-Ratelimit-Remaining: 4000\r\n\r\n${JSON.stringify(body)}`,
  stderr: status < 300 ? '' : `gh: HTTP ${status}\n`,
});

const endpointOf = args => args.find((word, index) => index > 0 && /^repos\//.test(word)) ?? '';
const methodOf = args => (args.includes('--method') ? args[args.indexOf('--method') + 1] : 'GET').toUpperCase();

function seedPullRequestWorkflow(w, text = 'name: CI\non:\n  pull_request:\njobs:\n  test:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm test\n') {
  w.baseCommit('.github/workflows/ci.yml', text);
  w.git(w.cwd, 'pull', '-q', 'origin', 'main');
}

function getConfigFlagValues(args) {
  const out = [];
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '-c' && i + 1 < args.length) out.push(args[i + 1]);
  }
  return out;
}

test('#3471: autopilot.ci="local" clears saved ciDown holds, requires local testCommand + fresh review, and merges when GitHub Actions is billing-blocked or produces zero checks', async t => {
  assert.equal(Object.hasOwn(coreSettings({}), 'ci'), false, 'omitted when unset');
  assert.equal(coreSettings({ autopilot: { ci: 'local' } }).ci, 'local');
  assert.equal(coreSettings({ autopilot: { ci: 'github' } }).ci, 'github');
  assert.equal(coreSettings({ autopilot: { ci: 'invalid' } }).ci, 'github', 'unknown ci value falls back safely to github');

  const w = await coreWorld(t, { settings: { runs: 1 } });
  seedPullRequestWorkflow(w);
  w.github.mergeMovesBase = true;

  // Seed a valid saved CI outage hold that loadMachine retains, and prove it holds intake under ci="github".
  mkdirSync(w.root, { recursive: true });
  writeFileSync(
    join(w.root, 'core.json'),
    JSON.stringify({
      streak: 0,
      hours: 1,
      ciDown: {
        since: w.now() - 600_000,
        reason: 'billing',
        message: 'The job was not started because your spending limit needs to be increased.',
        issue: 99,
        pr: 99,
        head: 'a'.repeat(40),
        at: w.now() - 50_000,
      },
    }, null, 2),
  );

  w.issue(1, { labels: ['pdd:autopilot'], title: 'Fix widget rounding', body: 'Fix rounding in widget.' });

  const heldTick = await w.tick();
  assert.match(heldTick.message, /intake held: GitHub Actions did not start a run/, 'valid ciDown record holds intake before switching to local CI');
  assert.equal(w.job(1, 'build'), undefined, 'no job started while ci="github" is held by ciDown');

  // Switch to autopilot.ci="local": next tick clears ciDown hold and starts build for #1!
  w.settings.ci = 'local';
  const first = await w.tick();
  assert.doesNotMatch(first.message, /intake held:/i);
  const coreSaved = JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
  assert.equal(coreSaved.ciDown, null, 'saved ciDown outage hold is cleared under local CI policy');
  assert.ok(w.job(1, 'build'), 'build started immediately after clearing ciDown');

  // Builder opens PR #100 while GitHub Actions fails to start due to billing/spending limits.
  const { pr, head: firstHead } = w.build(1, {
    body: 'Fixes #1.\n\nRuntime: PASS',
    checks: false,
  });
  w.github.setChecks(firstHead, 'failure', 'completed', {
    name: 'test',
    output: {
      title: 'The job was not started because recent account payments have failed or your spending limit needs to be increased.',
      summary: 'Billing limit reached.',
    },
  });

  // Start local suite + fresh review; fail local suite first and verify Autopilot refuses to merge and enters repair!
  await w.tick();
  w.review(1, 'PASS');
  w.suite(1, 1);
  await w.tick();
  assert.equal(w.github.merges.length, 0, 'local suite failure blocks merge even under ci="local"');
  assert.ok(w.job(1, 'repair'), 'failed local suite triggers repair');

  // Repair pushes a new head that produces 0 check runs on GitHub; review fails first -> still cannot merge.
  w.build(1, {
    role: 'repair',
    body: 'Fixes #1.\n\nRuntime: PASS',
    checks: false,
  });
  await w.tick();
  w.review(1, 'FAIL', ['P2 change-1.txt:1 missing edge check']);
  w.suite(1, 0);
  await w.tick();
  assert.equal(w.github.merges.length, 0, 'failing review blocks merge under ci="local"');

  // Second repair pushes final head with 0 check runs; both local suite and fresh review pass -> merges cleanly!
  const { head: finalHead } = w.build(1, {
    role: 'repair',
    body: 'Fixes #1.\n\nRuntime: PASS',
    checks: false,
  });
  await w.tick();
  w.review(1, 'PASS');
  w.suite(1, 0);
  await w.tick();

  assert.deepEqual(w.github.merges, [pr.number], 'PR merges with 0 GitHub check runs once local suite + review pass');
  const prComments = w.github.prs.get(pr.number).comments.map(c => c.body);
  assert.ok(
    prComments.some(body => body.includes('- CI: not required by local policy (autopilot.ci is local; local testCommand (npm test) and fresh review gate merge)')),
    'merge comment honestly reports local CI policy without claiming GitHub Actions passed',
  );
  const evidencePath = join(w.root, 'logs', `1-evidence-${finalHead}.json`);
  const evidence = JSON.parse(readFileSync(evidencePath, 'utf8'));
  assert.equal(evidence.ci?.state, 'local');
});

test('#3471: auto-detects disabled GitHub Actions, filters non-PR release workflows in ciHold, fails closed on protection/review API errors, preserves 0 approvals, and filters bots/outsiders across local and green PRs', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  seedPullRequestWorkflow(w);
  w.baseCommit('.github/workflows/release.yml', 'name: Release\non:\n  push:\n    tags:\n      - "v*"\njobs:\n  publish:\n    runs-on: ubuntu-latest\n    steps:\n      - run: echo publish\n');
  w.git(w.cwd, 'pull', '-q', 'origin', 'main');
  w.github.mergeMovesBase = true;

  let actionsEnabled = true;
  let workflowsPayload = [
    { path: '.github/workflows/ci.yml', state: 'disabled_manually' },
    { path: '.github/workflows/release.yml', state: 'active' },
  ];
  let requiredContexts = [];
  let reviewProtStatus = 404;
  let requiredApprovals = 0;
  let reviewsApiStatus = 200;

  const baseGh = w.gh;
  const customGh = async (args, options) => {
    const ep = endpointOf(args).split('?')[0];
    const method = methodOf(args);
    if (method === 'GET' && ep === 'repos/acme/widgets/actions/permissions') {
      return okHttp(200, { enabled: actionsEnabled });
    }
    if (method === 'GET' && ep === 'repos/acme/widgets/actions/workflows') {
      return okHttp(200, { total_count: workflowsPayload.length, workflows: workflowsPayload });
    }
    if (method === 'GET' && ep === 'repos/acme/widgets/branches/main/protection/required_status_checks') {
      return requiredContexts.length
        ? okHttp(200, { contexts: requiredContexts, checks: [] })
        : okHttp(404, { message: 'Required status checks not enabled' });
    }
    if (method === 'GET' && ep === 'repos/acme/widgets/branches/main/protection/required_pull_request_reviews') {
      if (reviewProtStatus !== 200) return okHttp(reviewProtStatus, { message: `HTTP ${reviewProtStatus}` });
      return okHttp(200, { required_approving_review_count: requiredApprovals });
    }
    if (method === 'GET' && ep === 'repos/acme/widgets/rules/branches/main') {
      return okHttp(404, { message: 'Not Found' });
    }
    if (method === 'GET' && /^repos\/acme\/widgets\/pulls\/\d+\/reviews$/.test(ep) && reviewsApiStatus !== 200) {
      return okHttp(reviewsApiStatus, { message: 'Server Error' });
    }
    return baseGh(args, options);
  };

  // Legacy saved ciDown (no hadWorkflows field) clears in ciHold even while non-PR release.yml is active and PR ci.yml is disabled!
  mkdirSync(w.root, { recursive: true });
  writeFileSync(
    join(w.root, 'core.json'),
    JSON.stringify({
      streak: 0,
      hours: 1,
      ciDown: { since: w.now() - 600_000, reason: 'queued', at: w.now() - 50_000, issue: 90, pr: 90, head: 'b'.repeat(40) },
    }),
  );

  // Case A: Server-side branch protection requires status check "external-ci" -> ciHold stays held until cleared, and PR waits on required checks.
  actionsEnabled = false;
  requiredContexts = [];
  w.issue(2, { labels: ['pdd:autopilot'], title: 'Handle disabled actions', body: 'Test local gate.' });
  await w.tick({ gh: customGh });
  assert.equal(JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8')).ciDown, null, 'legacy ciDown cleared when PR workflow is disabled despite active release.yml');
  assert.ok(w.job(2, 'build'), 'intake resumed after clearing legacy ciDown');

  requiredContexts = ['external-ci'];
  const { pr } = w.build(2, { body: 'Fixes #2.\n\nRuntime: PASS', checks: false });
  await w.tick({ gh: customGh });
  w.review(2, 'PASS');
  w.suite(2, 0);
  await w.tick({ gh: customGh });
  assert.equal(w.github.merges.length, 0, 'server-side required status checks still gate merge');
  const evidenceWhileServerRequired = JSON.parse(readFileSync(join(w.root, 'logs', `2-evidence-${pr.head}.json`), 'utf8'));
  assert.equal(evidenceWhileServerRequired.ci?.state, 'pending', 'waits on server-side required status checks');

  // Case B: 403 on required_pull_request_reviews fails closed (waits as retryable github error; neither merges nor parks!).
  requiredContexts = [];
  reviewProtStatus = 403;
  await w.tick({ gh: customGh });
  assert.equal(w.github.merges.length, 0, '403 on review protection fails closed and blocks merge');
  assert.equal(w.labels(2).includes('pdd:needs-decision'), false, '403 transient/permission error does not park PR');
  assert.equal(JSON.parse(readFileSync(join(w.root, 'jobs', '2.json'), 'utf8')).lastErrorTool, true);

  // Case C: Transient 500 on /pulls/N/reviews when requiredApprovals = 1 retries without parking!
  reviewProtStatus = 200;
  requiredApprovals = 1;
  reviewsApiStatus = 500;
  await w.tick({ gh: customGh });
  assert.equal(w.github.merges.length, 0);
  assert.equal(w.labels(2).includes('pdd:needs-decision'), false, 'transient reviews API error retries instead of parking');
  assert.equal(JSON.parse(readFileSync(join(w.root, 'jobs', '2.json'), 'utf8')).lastErrorTool, true);

  // Case D: Bot, [bot] login, untrusted NONE outsider, and stale commit_id reviews do NOT count -> parks with branch-protection PR note!
  reviewsApiStatus = 200;
  w.github.prs.get(pr.number).reviews = [
    { state: 'APPROVED', commit_id: pr.head, user: { login: 'ci-helper', type: 'Bot' }, author_association: 'COLLABORATOR' },
    { state: 'APPROVED', commit_id: pr.head, user: { login: 'copilot-reviewer[bot]', type: 'User' }, author_association: 'COLLABORATOR' },
    { state: 'APPROVED', commit_id: pr.head, user: { login: 'outside-contrib', type: 'User' }, author_association: 'NONE' },
    { state: 'APPROVED', commit_id: '0'.repeat(40), user: { login: 'reviewer-alice', type: 'User' }, author_association: 'COLLABORATOR' },
  ];
  await w.tick({ gh: customGh });
  assert.equal(w.github.merges.length, 0, 'bot, outsider, and stale-commit approvals do not satisfy requiredApprovals');
  assert.ok(w.labels(2).includes('pdd:needs-decision'), 'parks issue for human PR approval');
  const parkedPrNotes = w.github.prs.get(pr.number).comments.map(c => c.body);
  assert.ok(
    parkedPrNotes.some(body => /pull-request review approval on GitHub required by branch protection/i.test(body)),
    'PR comment accurately states branch-protection review approval wait',
  );
  assert.equal(
    parkedPrNotes.some(body => /approval of the prompt changes/i.test(body)),
    false,
    'never mislabels branch-protection review wait as prompt-change approval',
  );

  //Trusted collaborator approves at current head (case-insensitive SHA) and removes pdd:needs-decision -> merges!
  w.github.prs.get(pr.number).reviews.push({
    state: 'APPROVED',
    commit_id: pr.head.toUpperCase(),
    user: { login: 'reviewer-alice', type: 'User' },
    author_association: 'COLLABORATOR',
  });
  w.github.unlabel(2, 'pdd:needs-decision');
  await w.tick({ gh: customGh });
  await w.tick({ gh: customGh });
  if (w.job(2, 'review') && w.alive.has(w.job(2, 'review').pid)) w.review(2, 'PASS');
  if (w.job(2, 'suite') && w.alive.has(w.job(2, 'suite').pid)) w.suite(2, 0);
  await w.tick({ gh: customGh });
  assert.deepEqual(w.github.merges, [pr.number]);

  // Case E: Explicit required_approving_review_count: 0 is preserved as 0 (not inflated to 1), AND green GitHub CI PRs also honor requiredApprovals > 0!
  actionsEnabled = true;
  workflowsPayload = [
    { path: '.github/workflows/ci.yml', state: 'active' },
    { path: '.github/workflows/release.yml', state: 'active' },
  ];
  reviewProtStatus = 200;
  requiredApprovals = 1;
  w.issue(3, { labels: ['pdd:autopilot'], title: 'Green CI approval gate', body: 'Check green CI.' });
  await w.tick({ gh: customGh });
  const { pr: greenPr } = w.build(3, { body: 'Fixes #3.\n\nRuntime: PASS', checks: 'success' });
  await w.tick({ gh: customGh });
  w.review(3, 'PASS');
  w.suite(3, 0);
  await w.tick({ gh: customGh });
  assert.equal(w.github.merges.includes(greenPr.number), false, 'green GitHub CI PR also honors requiredApprovals = 1');
  assert.ok(w.labels(3).includes('pdd:needs-decision'));

  // Lower required_approving_review_count explicitly to 0 and remove pdd:needs-decision -> merges with 0 human reviews!
  requiredApprovals = 0;
  w.github.unlabel(3, 'pdd:needs-decision');
  await w.tick({ gh: customGh });
  await w.tick({ gh: customGh });
  if (w.job(3, 'review') && w.alive.has(w.job(3, 'review').pid)) w.review(3, 'PASS');
  if (w.job(3, 'suite') && w.alive.has(w.job(3, 'suite').pid)) w.suite(3, 0);
  await w.tick({ gh: customGh });
  assert.deepEqual(w.github.merges, [pr.number, greenPr.number], 'explicit required_approving_review_count: 0 merges without inflating 0 to 1');
});

test('#3473: SIGTERM during runTestSuite queue wait finalizes ticket to interrupted and releases queue capacity', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-sigterm-queue-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));

  const queueDir = join(dir, 'queue');
  const repo1 = join(dir, 'repo-1');
  const repo2 = join(dir, 'repo-2');
  const repo3 = join(dir, 'repo-3');
  for (const p of [queueDir, repo1, repo2, repo3]) mkdirSync(p, { recursive: true });

  writeFileSync(
    join(queueDir, 'capacity.json'),
    JSON.stringify(withCheckLifetime(calculateCheckCapacity({ checks: 1 }, checkMachine({ taskset: null }).ports))),
  );

  const env = { ...process.env, PDD_SUITE_QUEUE: queueDir, HOME: join(dir, 'home') };
  mkdirSync(env.HOME, { recursive: true });

  // Occupy the single check slot with suite #1 in-process.
  let releaseFirst;
  const firstPromise = runTestSuite(
    { cwd: repo1, command: 'check-1', env },
    {
      ...checkMachine({ taskset: null }).ports,
      execute: async (_cmd, opts) => {
        opts.onChild(process.pid);
        await new Promise(resolve => { releaseFirst = resolve; });
        return { exitCode: 0 };
      },
    },
  );

  // Wait until ticket-1.json is running.
  for (let i = 0; i < 200; i++) {
    if (existsSync(join(queueDir, 'ticket-1.json'))) {
      const t1 = JSON.parse(readFileSync(join(queueDir, 'ticket-1.json'), 'utf8'));
      if (t1.state === 'running') break;
    }
    await new Promise(r => setTimeout(r, 10));
  }

  // Spawn real test-suite-entry.mjs child process via a symlinked cwd waiting in the queue for repo2, then send SIGTERM while it waits!
  const repo2Link = join(dir, 'repo-2-link');
  symlinkSync(repo2, repo2Link);
  const entryPath = fileURLToPath(new URL('../src/test-suite-entry.mjs', import.meta.url));
  const waiter = spawn(process.execPath, [entryPath], {
    cwd: repo2Link,
    env: { ...env, SUITE: `${JSON.stringify(process.execPath)} -e "process.exit(0)"` },
    stdio: ['ignore', 'pipe', 'pipe'],
  });

  // Wait for ticket-2.json to appear in waiting state.
  for (let i = 0; i < 300; i++) {
    if (existsSync(join(queueDir, 'ticket-2.json'))) {
      const t2 = JSON.parse(readFileSync(join(queueDir, 'ticket-2.json'), 'utf8'));
      if (t2.state === 'waiting') break;
    }
    await new Promise(r => setTimeout(r, 10));
  }
  assert.equal(existsSync(join(queueDir, 'ticket-2.json')), true, 'waiting child registered ticket-2.json');

  waiter.kill('SIGTERM');
  const exitInfo = await new Promise(resolve => waiter.on('close', (code, signal) => resolve({ code, signal })));
  assert.ok(exitInfo.signal === 'SIGTERM' || exitInfo.code === 143, 'waiter terminated on SIGTERM');

  const ticket2 = JSON.parse(readFileSync(join(queueDir, 'ticket-2.json'), 'utf8'));
  assert.equal(ticket2.state, 'finished');
  assert.equal(ticket2.outcome, 'interrupted');
  assert.equal(ticket2.signal, 'SIGTERM');
  assert.equal(ticket2.counts, null);
  assert.equal(typeof ticket2.finishedAt, 'number');

  // Verify readSuiteProgress matches BOTH un-realpathed symlink path and canonical path, and suiteStatusWords reports "interrupted"!
  const progViaTarget = readSuiteProgress({ cwd: repo2, env });
  const progViaSymlink = readSuiteProgress({ cwd: repo2Link, env });
  assert.equal(progViaTarget?.outcome, 'interrupted');
  assert.equal(progViaSymlink?.outcome, 'interrupted');
  assert.match(suiteStatusWords(progViaTarget), /^full test suite interrupted:/);
  assert.doesNotMatch(suiteStatusWords(progViaTarget), /full test suite failed:/);

  // Release slot #1 and verify a third suite immediately acquires the slot without being blocked by ticket #2.
  releaseFirst();
  await firstPromise;

  let thirdRan = false;
  const thirdResult = await runTestSuite(
    { cwd: repo3, command: 'check-3', env },
    {
      ...checkMachine({ taskset: null }).ports,
      execute: async (_cmd, opts) => {
        opts.onChild(process.pid);
        thirdRan = true;
        return { exitCode: 0 };
      },
    },
  );
  assert.equal(thirdRan, true);
  assert.equal(thirdResult.exitCode, 0);
});

test('#3473: reconcileSuiteQueue reclaims recycled PIDs via pidIdentity, and autopilot-core preserves interrupted suite evidence and retries to no-result', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-reconcile-queue-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const queueDir = join(dir, 'queue');
  const repoStale = join(dir, 'repo-stale');
  mkdirSync(queueDir, { recursive: true });
  mkdirSync(repoStale, { recursive: true });
  const env = { ...process.env, PDD_SUITE_QUEUE: queueDir, HOME: join(dir, 'home') };

  // Write a stale ticket whose PID matches a currently alive process (process.pid) with a recycled pidIdentity!
  const staleTicketPath = join(queueDir, 'ticket-1.json');
  const staleLogPath = join(dir, 'validation-1.log');
  writeFileSync(staleLogPath, '', { mode: 0o600 });
  writeFileSync(
    staleTicketPath,
    serializeValidationReceipt({
      ticket: 1,
      pid: process.pid,
      pidIdentity: 'old-proc-start-id',
      executionStarted: false,
      childPid: null,
      cwd: repoStale,
      state: 'running',
      queuedAt: 1000,
      startedAt: 2000,
      finishedAt: null,
      reason: null,
      environmentPolicy: 'clean-v1',
      command: '[redacted]',
      commandFingerprint: 'a'.repeat(64),
      source: { head: null, fingerprint: null, runId: null, issue: null, error: 'ENOENT' },
      logPath: staleLogPath,
      receiptPath: staleTicketPath,
      recorderPid: null,
      recorderIdentity: null,
      exitCode: null,
      signal: null,
      counts: null,
      outcome: 'running',
    }),
  );

  const repoStaleLink = join(dir, 'repo-stale-link');
  symlinkSync(repoStale, repoStaleLink);
  const progress = readSuiteProgress(
    { cwd: repoStaleLink, since: 500, env },
    {
      now: () => 5000,
      alive: () => true,
      processIdentity: () => 'recycled-proc-start-id',
    },
  );
  assert.equal(progress.state, 'finished');
  assert.equal(progress.outcome, 'interrupted');
  assert.match(suiteStatusWords(progress), /^full test suite interrupted:/);

  const reconciledCount = await reconcileSuiteQueue(
    { cwd: repoStaleLink, env },
    {
      now: () => 5000,
      alive: () => true,
      processIdentity: () => 'recycled-proc-start-id',
    },
  );
  assert.equal(reconciledCount, 1);
  const persisted = JSON.parse(readFileSync(staleTicketPath, 'utf8'));
  assert.equal(persisted.state, 'finished');
  assert.equal(persisted.outcome, 'interrupted');

  // Verify autopilot-core records interrupted suite status and converges 3 signal deaths to machine no-result (never test failure or suite-broken).
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.suiteQueued = true;
  w.issue(3, { labels: ['pdd:autopilot'], title: 'Interrupted suite check', body: 'Verify SIGTERM handling.' });
  await w.tick({ env });
  const { head } = w.build(3, { body: 'Fixes #3.\n\nRuntime: PASS', checks: 'success' });

  for (let attempt = 1; attempt <= 3; attempt++) {
    await w.tick({ env });
    if (w.job(3, 'review') && w.alive.has(w.job(3, 'review').pid)) w.review(3, 'PASS');
    const suiteJob = w.job(3, 'suite');
    assert.ok(suiteJob, `suite attempt ${attempt} started`);
    w.alive.delete(suiteJob.pid);
    writeFileSync(suiteJob.exit, JSON.stringify({ code: null, signal: 'SIGTERM', at: w.now() }));
    if (attempt === 1) {
      const statusText = coreStatus({ state: w.state, settings: w.settings }, w.ports({ env }));
      assert.match(statusText, /suite interrupted \(SIGTERM, not run\)/);
    }
    await w.tick({ env });
    w.advance(31_000);
  }

  assert.equal(w.job(3, 'repair'), undefined, 'signal-interrupted suite wait never sends fake test failures to repair');
  assert.equal(w.labels(3).includes('pdd:working'), false, 'released pdd:working cleanly');
  assert.equal(w.labels(3).includes('pdd:stuck'), false, 'never marks issue pdd:stuck for machine SIGTERM');
  const historyRows = readFileSync(join(w.root, 'history.jsonl'), 'utf8')
    .trim()
    .split('\n')
    .map(line => JSON.parse(line));
  const releasedRow = historyRows.find(r => r.issue === 3);
  assert.equal(releasedRow?.outcome, 'released');
  assert.equal(releasedRow?.owner, 'machine');
  const evidence = JSON.parse(readFileSync(join(w.root, 'logs', `3-evidence-${head}.json`), 'utf8'));
  assert.equal(evidence.suite?.state, 'interrupted');
  assert.equal(evidence.suite?.signal, 'SIGTERM');
});

test('#3500: detectWrongRepositoryIssue skips wrong-repo issues before claim with one deduped comment while leaving greenfield paths and shadow mode untouched', async t => {
  const configuredSiblings = ['pdd_cloud', 'extensions/github_pdd_app', 'prompt-runtime', 'runtime-client'];
  const w = await coreWorld(t, { repository: 'promptdriven/pdd', settings: { runs: 2, siblingRepos: configuredSiblings } });
  mkdirSync(join(w.cwd, 'src'), { recursive: true });
  writeFileSync(join(w.cwd, 'src', 'runtime-seam.mjs'), 'export const localSeam = true;\n');

  // Direct unit checks on detectWrongRepositoryIssue:
  assert.equal(
    detectWrongRepositoryIssue(
      { title: 'Add new helper', body: 'Create `src/brand-new-helper.mjs` and `test/brand-new-helper.test.mjs`.' },
      { repo: 'promptdriven/pdd', cwd: w.cwd, siblingRepos: configuredSiblings },
    ),
    null,
    'missing greenfield paths in the current repo never trigger wrong-repo skip',
  );
  assert.equal(
    detectWrongRepositoryIssue(
      {
        title: 'Add src/runtime-retry.mjs for prompt-runtime transient 503s',
        body: 'Create `src/runtime-retry.mjs` and `test/runtime-retry.test.mjs` so PDD retries transient 503s from `prompt-runtime` (see https://github.com/promptdriven/pdd-cloud/blob/main/pdd_cloud/gateway/retry.py for reference).',
      },
      { repo: 'promptdriven/pdd', cwd: w.cwd, siblingRepos: configuredSiblings },
    ),
    null,
    'greenfield local-root paths in pdd are never skipped even when prose mentions prompt-runtime and links an external GitHub blob URL',
  );
  assert.equal(
    detectWrongRepositoryIssue(
      { title: 'Fix runtime-client payload in CLI', body: 'Update `src/runtime-seam.mjs` when calling `runtime-client`.' },
      { repo: 'promptdriven/pdd', cwd: w.cwd, siblingRepos: configuredSiblings },
    ),
    null,
    'issue naming an existing local file in cwd is never skipped',
  );
  assert.ok(
    detectWrongRepositoryIssue(
      { title: 'Fix Stripe webhook retry', body: 'Repo: promptdriven/pdd-cloud\nUpdate `pdd_cloud/billing/stripe.py` and `README.md`.' },
      { repo: 'promptdriven/pdd', cwd: w.cwd, siblingRepos: configuredSiblings },
    ),
    'explicit Repo header + missing sibling path triggers wrong-repo detection even when README.md exists',
  );
  assert.ok(
    detectWrongRepositoryIssue(
      { title: 'GitHub App installation token refresh', body: 'Fix token refresh in `extensions/github_pdd_app/webhook.ts`.' },
      { repo: 'promptdriven/pdd', cwd: w.cwd, siblingRepos: configuredSiblings },
    ),
    'sibling repo root path absent locally triggers wrong-repo detection',
  );
  assert.ok(
    detectWrongRepositoryIssue(
      { title: 'Worker sandbox timeout inside prompt-runtime', body: 'See https://github.com/promptdriven/prompt-runtime/blob/main/src/runner.ts#L42' },
      { repo: 'promptdriven/pdd', cwd: w.cwd, siblingRepos: configuredSiblings },
    ),
    'external GitHub blob URL with zero local files triggers wrong-repo detection',
  );
  assert.equal(nativeFacts({ labels: [NEEDS_OTHER_REPO_LABEL] })?.kind, 'elsewhere');

  // Integration check: #40 is a wrong-repo issue; #41 is a greenfield local issue.
  w.issue(40, {
    user: 'promptdriven',
    labels: ['pdd:autopilot'],
    title: 'Fix Cloud Run webhook handler in pdd_cloud',
    body: 'Update `pdd_cloud/webhooks/github.py` and `extensions/github_pdd_app/handler.py` to validate signatures.',
  });
  w.issue(41, {
    user: 'promptdriven',
    labels: ['pdd:autopilot'],
    title: 'Add local formatter helper',
    body: 'Create `src/new-formatter.mjs` and `test/new-formatter.test.mjs`.',
  });

  // Shadow intake must remain 100% read-only on GitHub!
  const writesBeforeShadow = w.github.writes.length;
  await shadowIntake(
    {
      fs: await import('node:fs'),
      now: w.now,
      root: w.root,
      repo: 'promptdriven/pdd',
      state: w.state,
      settings: { intake: 'shadow', label: 'pdd:autopilot' },
      budget: { state: 'normal' },
      gh: {
        all: async route => {
          const r = await w.gh(['api', '--include', '--method', 'GET', route]);
          return JSON.parse(r.stdout.split(/\r?\n\r?\n/).slice(1).join('\n\n'));
        },
      },
      jobs: w.jobs,
      ports: w.ports(),
      warn: () => {},
    },
    await w.ports().listIssues(),
  );
  assert.equal(w.github.writes.length, writesBeforeShadow, 'shadowIntake makes zero GitHub writes');

  // Core tick skips #40 BEFORE claiming it, labels it needs-other-repo, posts ONE comment, and claims #41!
  await w.tick();
  assert.equal(w.job(40, 'build'), undefined, '#40 was never claimed or built');
  assert.equal(w.labels(40).includes('pdd:working'), false, '#40 never received pdd:working');
  assert.equal(w.labels(40).includes(NEEDS_OTHER_REPO_LABEL), true, '#40 received needs-other-repo');
  const routingComments1 = w.comments(40).filter(c => c.includes(`${OTHER_REPO_MARKER_PREFIX}40 -->`));
  assert.equal(routingComments1.length, 1, 'exactly one routing comment posted');
  assert.match(routingComments1[0], /pdd_cloud\/webhooks\/github\.py/);
  assert.ok(w.job(41, 'build'), 'greenfield local issue #41 was claimed and started normally');

  // Subsequent ticks (even if someone removes needs-other-repo without changing the issue body) do not spam comments!
  w.github.unlabel(40, NEEDS_OTHER_REPO_LABEL);
  await w.tick();
  await w.tick();
  const routingComments2 = w.comments(40).filter(c => c.includes(`${OTHER_REPO_MARKER_PREFIX}40 -->`));
  assert.equal(routingComments2.length, 1, 'zero duplicate routing comments on subsequent polls');
  assert.equal(w.labels(40).includes(NEEDS_OTHER_REPO_LABEL), true, 're-applies label without reposting comment');
});

test('#3503: cardCommand, improveCommand, forensicsCommand, activeIntake, shadowIntake, and runPreRunForensics forward CODEX_HOME gateway provider overrides alongside --ignore-user-config without leaking MCP or profiles', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-codex-gateway-3503-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));

  // 1. Direct synthesized CODEX_HOME with both pdd_codex_gateway AND hostile user MCP/profile/feature keys.
  const managedHome = join(dir, 'managed-codex-home');
  mkdirSync(managedHome, { recursive: true });
  writeFileSync(
    join(managedHome, 'config.toml'),
    [
      'cli_auth_credentials_store = "file"',
      'model_provider = "pdd_codex_gateway"',
      'web_search = "live"',
      'approval_policy = "on-request"',
      '',
      '[features]',
      'hooks = true',
      'plugins = true',
      'shell_snapshot = false',
      '',
      '[mcp_servers.bad_user_server]',
      'command = "evil-mcp"',
      '',
      '[profiles.bad_profile]',
      'model = "o1"',
      '',
      '[shell_environment_policy]',
      'filters = { PDD_CODEX_GATEWAY_GRANT = "exclude" }',
      '',
      '[model_providers.pdd_codex_gateway]',
      'name = "PDD Codex Gateway"',
      'base_url = "https://gateway.example.test/v1"',
      'model_catalog_url = "https://gateway.example.test/v1/models"',
      'wire_api = "responses"',
      'requires_openai_auth = false',
      'supports_websockets = false',
      'http_headers = { "x-pdd-gateway-grant" = "pddg_direct_token_1234567890", "authorization" = "Bearer sk-secret-never-on-argv" }',
      'experimental_bearer_token = "pddg_bearer_secret_999"',
      'query_params = { api_key = "qp_secret_888" }',
      '',
    ].join('\n'),
  );

  for (const build of [
    env => cardCommand({ kind: 'codex' }, { model: 'gpt-5.4-mini', result: '/tmp/card.txt', env }),
    env => improveCommand({ kind: 'codex' }, { model: 'gpt-5.4-mini', result: '/tmp/imp.txt', env }),
    env => forensicsCommand({ kind: 'codex' }, { model: 'gpt-5.4-mini', resultFile: '/tmp/for.txt', env }),
  ]) {
    const cmdEnv = { HOME: dir, PATH: '/usr/bin', CODEX_HOME: managedHome };
    const cmd = build(cmdEnv);
    assert.ok(cmd.args.includes('--ignore-user-config'), 'keeps --ignore-user-config');
    const cVals = getConfigFlagValues(cmd.args);
    assert.ok(cVals.includes('mcp_servers={}'), 'keeps mcp_servers={}');
    assert.ok(cVals.includes('web_search="disabled"'), 'keeps web_search="disabled"');
    assert.ok(cVals.includes('cli_auth_credentials_store="file"'));
    assert.ok(cVals.includes('model_provider="pdd_codex_gateway"'));
    assert.ok(cVals.includes('model_providers.pdd_codex_gateway.base_url="https://gateway.example.test/v1"'));
    assert.ok(cVals.includes('model_providers.pdd_codex_gateway.model_catalog_url="https://gateway.example.test/v1/models"'));
    assert.ok(cVals.includes('model_providers.pdd_codex_gateway.wire_api="responses"'));
    assert.ok(cVals.includes('model_providers.pdd_codex_gateway.requires_openai_auth=false'));
    assert.ok(cVals.includes('model_providers.pdd_codex_gateway.supports_websockets=false'));
    assert.ok(cVals.includes('model_providers.pdd_codex_gateway.env_http_headers={ x-pdd-gateway-grant = "PDD_CODEX_GATEWAY_GRANT" }'));
    assert.ok(cVals.includes('shell_environment_policy.filters.PDD_CODEX_GATEWAY_GRANT="exclude"'));
    assert.ok(cVals.includes('features.shell_snapshot=false'));
    assert.equal(cmdEnv.PDD_CODEX_GATEWAY_GRANT, 'pddg_direct_token_1234567890', 'legacy http_headers grant moved into child env');
    const serializedArgs = JSON.stringify(cmd.args);
    assert.equal(serializedArgs.includes('pddg_'), false, 'raw pddg_* secret NEVER appears in CLI args');
    assert.equal(serializedArgs.includes('sk-secret-never-on-argv'), false, 'raw bearer secret NEVER appears in CLI args');
    assert.equal(serializedArgs.includes('qp_secret_888'), false, 'raw query_params secret NEVER appears in CLI args');
    assert.equal(/\.http_headers=/.test(serializedArgs), false, 'http_headers NEVER serialized into CLI args');
    assert.equal(serializedArgs.includes('experimental_bearer_token'), false, 'experimental_bearer_token NEVER serialized into CLI args');
    assert.equal(serializedArgs.includes('query_params'), false, 'query_params NEVER serialized into CLI args');
    assert.equal(cVals.some(v => v.includes('bad_user_server') || v.includes('bad_profile') || v.includes('hooks=true')), false, 'never leaks user MCP, profiles, or hooks');
  }

  // Without explicit CODEX_HOME in env/agent, user's ~/.codex/config.toml is NOT read into -c flags.
  const userDotCodex = join(dir, '.codex');
  mkdirSync(userDotCodex, { recursive: true });
  writeFileSync(join(userDotCodex, 'config.toml'), 'model_provider = "should_not_load"\n');
  assert.deepEqual(codexProviderConfigArgs({ env: { HOME: dir, PATH: '/usr/bin' }, agent: { kind: 'codex' } }), []);

  // Symlinked config.toml (as created by OAuth step overlays pointing to ~/.codex/config.toml) MUST be skipped!
  const symlinkOverlayHome = join(dir, 'symlink-overlay-home');
  mkdirSync(symlinkOverlayHome, { recursive: true });
  symlinkSync(join(userDotCodex, 'config.toml'), join(symlinkOverlayHome, 'config.toml'));
  assert.deepEqual(
    codexProviderConfigArgs({ env: { HOME: dir, PATH: '/usr/bin', CODEX_HOME: symlinkOverlayHome }, agent: { kind: 'codex' } }),
    [],
    'symlinked config.toml is rejected so personal ~/.codex/config.toml never leaks past --ignore-user-config',
  );

  // 2. Cloud Accounts gateway_grant lease via prepareCloudStepExecution (runner.prepareStep) in shadowIntake, activeIntake (card + improve), and runPreRunForensics!
  const leaseReply = {
    account: { id: 'cloud-1', provider: 'codex' },
    lease: {
      delivery_mode: 'gateway_grant',
      codex_gateway_url: 'https://cloud-gw.example.test/v1',
      codex_gateway_token: 'pddg_step_lease_token_abcdef123456',
    },
  };
  const selectCloudGatewayLogin = async () => ({
    state: 'ready',
    cloud: true,
    login: { id: 'cloud-1' },
    agent: { kind: 'codex', command: 'codex', model: 'gpt-5.4-mini' },
    env: { HOME: dir, PATH: process.env.PATH },
    prepareStep: (baseEnv, opts) => prepareCloudStepExecution(leaseReply, baseEnv, { tmpRoot: dir }, opts),
  });

  // Verify runPreRunForensics with prepareStep gateway runner:
  const wt = join(dir, 'worktree');
  mkdirSync(join(wt, 'src'), { recursive: true });
  writeFileSync(join(wt, 'src', 'x.mjs'), 'export const x = 1;\n');
  let seenForensicsArgs = null;
  let seenForensicsEnv = null;
  const selectedForForensics = await selectCloudGatewayLogin();
  await runPreRunForensics(
    {
      repo: 'acme/widgets',
      baseBranch: 'main',
      worktree: wt,
      issue: { number: 50, title: 'Check gateway forensics', body: 'Check src/x.mjs', labels: [] },
      agent: selectedForForensics.agent,
      selected: selectedForForensics,
    },
    {
      env: { HOME: dir, PATH: process.env.PATH, GH_TOKEN: 'ghp_strip_me' },
      run: async (_cmd, args, opts) => {
        seenForensicsArgs = args;
        seenForensicsEnv = opts.env;
        const outIdx = args.indexOf('--output-last-message');
        writeFileSync(args[outIdx + 1], JSON.stringify({ already_fixed: false, summary: 'Still needed', target_files: ['src/x.mjs'] }));
        return { code: 0, stdout: '', stderr: '' };
      },
    },
  );
  assert.ok(seenForensicsArgs.includes('--ignore-user-config'));
  const forensicsCVals = getConfigFlagValues(seenForensicsArgs);
  assert.ok(forensicsCVals.includes('model_provider="pdd_codex_gateway"'));
  assert.ok(forensicsCVals.includes('model_providers.pdd_codex_gateway.base_url="https://cloud-gw.example.test/v1"'));
  assert.ok(forensicsCVals.includes('model_providers.pdd_codex_gateway.env_http_headers={ x-pdd-gateway-grant = "PDD_CODEX_GATEWAY_GRANT" }'));
  assert.equal(seenForensicsEnv.PDD_CODEX_GATEWAY_GRANT, 'pddg_step_lease_token_abcdef123456');
  assert.equal(seenForensicsEnv.GH_TOKEN, undefined);

  // Verify shadowIntake AND activeIntake (both card job and auto-improve job) prepare CODEX_HOME BEFORE building Codex args!
  const w = await coreWorld(t, { settings: { runs: 0, intake: 'active' } });
  w.issue(51, { title: 'Vague widget bug', body: 'Widgets behave strangely sometimes.' });

  // First run shadowIntake on a separate root with the Cloud gateway prepareStep runner:
  const shadowRoot = join(dir, 'shadow-root');
  await shadowIntake(
    {
      fs: await import('node:fs'),
      now: w.now,
      root: shadowRoot,
      repo: 'acme/widgets',
      state: w.state,
      settings: { intake: 'shadow' },
      budget: { state: 'normal' },
      gh: { all: async () => [] },
      jobs: w.jobs,
      ports: { ...w.ports(), env: { HOME: dir, PATH: process.env.PATH }, selectLogin: selectCloudGatewayLogin },
      warn: () => {},
    },
    await w.ports().listIssues(),
  );
  const shadowJob = w.started.find(j => j.role === 'intake' && j.issue === 51);
  assert.ok(shadowJob, 'shadowIntake started card job');
  const shadowCVals = getConfigFlagValues(shadowJob.args);
  assert.ok(shadowCVals.includes('model_provider="pdd_codex_gateway"'), 'shadowIntake card job received -c model_provider from prepareStep overlay');
  assert.ok(shadowCVals.includes('model_providers.pdd_codex_gateway.env_http_headers={ x-pdd-gateway-grant = "PDD_CODEX_GATEWAY_GRANT" }'));
  assert.equal(shadowJob.env.PDD_CODEX_GATEWAY_GRANT, 'pddg_step_lease_token_abcdef123456');
  for (const d of shadowJob.cleanupDirs ?? []) rmSync(d, { recursive: true, force: true });
  w.started.length = 0;
  w.alive.clear();

  // Now run activeIntake through BOTH card ("improve") and auto-improve ("intake-improve") stages with Cloud gateway prepareStep!
  await w.tick({ env: { HOME: dir, PATH: process.env.PATH }, selectLogin: selectCloudGatewayLogin });
  const activeCardJob = w.started.find(j => j.role === 'intake' && j.issue === 51);
  assert.ok(activeCardJob, 'activeIntake started card job');
  const activeCardCVals = getConfigFlagValues(activeCardJob.args);
  assert.ok(activeCardCVals.includes('model_provider="pdd_codex_gateway"'));
  assert.ok(activeCardCVals.includes('model_providers.pdd_codex_gateway.base_url="https://cloud-gw.example.test/v1"'));
  assert.equal(activeCardJob.env.PDD_CODEX_GATEWAY_GRANT, 'pddg_step_lease_token_abcdef123456');

  // Finish the card job with class="improve" so the next tick launches improveCommand via startIntakeJob!
  w.alive.delete(activeCardJob.pid);
  writeFileSync(
    activeCardJob.args[activeCardJob.args.indexOf('--output-last-message') + 1],
    JSON.stringify({ class: 'improve', reason: 'Needs exact files and criteria.', confidence: 0.7, areas: ['README.md'], model: 'gpt-5.4-mini' }),
  );
  writeFileSync(activeCardJob.exit, JSON.stringify({ code: 0, signal: null, at: w.now() }));

  await w.tick({ env: { HOME: dir, PATH: process.env.PATH }, selectLogin: selectCloudGatewayLogin });
  const improveJob = w.started.find(j => j.role === 'intake-improve' && j.issue === 51);
  assert.ok(improveJob, 'activeIntake started auto-improve job');
  assert.ok(improveJob.args.includes('--ignore-user-config'));
  const improveCVals = getConfigFlagValues(improveJob.args);
  assert.ok(improveCVals.includes('model_provider="pdd_codex_gateway"'), 'improveCommand received gateway provider from prepareStep overlay');
  assert.ok(improveCVals.includes('model_providers.pdd_codex_gateway.env_http_headers={ x-pdd-gateway-grant = "PDD_CODEX_GATEWAY_GRANT" }'));
  assert.ok(improveCVals.includes('shell_environment_policy.filters.PDD_CODEX_GATEWAY_GRANT="exclude"'));
  assert.equal(improveJob.env.PDD_CODEX_GATEWAY_GRANT, 'pddg_step_lease_token_abcdef123456');
  for (const argsList of [seenForensicsArgs, shadowJob.args, activeCardJob.args, improveJob.args]) {
    assert.equal(JSON.stringify(argsList).includes('pddg_'), false, 'step lease token NEVER appears in job CLI args');
  }
  for (const d of improveJob.cleanupDirs ?? []) rmSync(d, { recursive: true, force: true });
});
