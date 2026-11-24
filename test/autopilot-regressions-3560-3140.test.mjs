import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { coreWorld } from './helpers/core-world.mjs';
import {
  collectLocalAutopilotIncidents,
  coreStatus,
  runAutopilotInvestigate,
  runDailyAutopilotInvestigation,
} from '../src/autopilot-core.mjs';
import { selectCircuitBreakerRegression } from '../src/autopilot-regressions.mjs';
import {
  INVESTIGATOR_MARKER_PREFIX,
  classifyIncidentBucket,
  diagnoseStuckCause,
  formatInvestigationIssueBody,
  hasStrongInvestigationEvidence,
  investigateIncidents,
  loadInvestigationLedger,
} from '../src/autopilot/investigator/investigator.mjs';
import { runMetrics } from '../src/metrics-command.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const MIN = 60 * 1000;
const HOUR = 60 * MIN;

function makeTempDir(t, prefix) {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

function capture() {
  return { text: '', write(chunk) { this.text += String(chunk); } };
}

test('3560: selectCircuitBreakerRegression trips on >=2 distinct reopened issues within rolling 24h (across ticks), respects clearedAfter, and keeps instant revert/CI priority', () => {
  const nowMs = Date.parse('2026-11-23T18:00:00Z');
  const now = () => nowMs;
  const ago = hours => new Date(nowMs - hours * HOUR).toISOString();

  // 1 reopen alone -> null
  assert.equal(selectCircuitBreakerRegression([
    { pr: 101, issue: 11, kind: 'reopened', code: 'post-merge-reopen', at: ago(2), mergedAt: ago(4), detail: 'Issue #11 reopened' },
  ], { now }), null);

  // Same single issue present in BOTH newlyDetected AND postMergeState -> still 1 distinct issue -> null!
  const singlePmState = {
    merges: {
      101: {
        pr: 101,
        issue: 11,
        issues: [11],
        mergedAt: ago(4),
        reopened: true,
        signals: [
          { kind: 'reopened', level: 'proven', issue: 11, at: ago(2), url: 'https://github.com/acme/widgets/issues/11#event-1', detail: 'Issue #11 reopened' },
          { kind: 'reopened', level: 'proven', issue: 11, at: ago(1), url: 'https://github.com/acme/widgets/issues/11#event-2', detail: 'Issue #11 reopened again' },
        ],
      },
    },
  };
  assert.equal(selectCircuitBreakerRegression([
    { pr: 101, issue: 11, kind: 'reopened', code: 'post-merge-reopen', at: ago(1), mergedAt: ago(4), detail: 'Issue #11 reopened again' },
  ], { now, postMergeState: singlePmState }), null);

  // 2 distinct issues reopened across DIFFERENT ticks (issue #11 persisted in post-merge.json 10h ago; issue #12 newly detected 1h ago) -> TRIPS!
  const crossTickPmState = {
    merges: {
      101: {
        pr: 101,
        issue: 11,
        issues: [11],
        mergedAt: ago(14),
        reopened: true,
        signals: [
          { kind: 'reopened', level: 'proven', issue: 11, at: ago(10), url: 'https://github.com/acme/widgets/issues/11#event-1', detail: 'Issue #11 reopened after PR #101 merged' },
        ],
      },
    },
  };
  const cluster = selectCircuitBreakerRegression([
    {
      pr: 102,
      issue: 12,
      kind: 'reopened',
      code: 'post-merge-reopen',
      at: ago(1),
      mergedAt: ago(3),
      url: 'https://github.com/acme/widgets/issues/12#event-2',
      detail: 'Issue #12 reopened token=ghp_1234567890abcdef1234567890abcdef',
    },
  ], { now, postMergeState: crossTickPmState });
  assert.ok(cluster, '2 distinct reopened issues within rolling 24h must trip circuit breaker');
  assert.equal(cluster.active, true);
  assert.equal(cluster.kind, 'reopened_cluster');
  assert.equal(cluster.code, 'post-merge-reopen');
  assert.equal(cluster.count, 2);
  assert.equal(cluster.pr, 102);
  assert.equal(cluster.issue, 12);
  assert.deepEqual(cluster.issues, [11, 12]);
  assert.deepEqual(cluster.prs, [101, 102]);
  assert.equal(cluster.windowHours, 24);
  assert.ok(!cluster.reason.includes('ghp_1234567890'), 'secret must be redacted from circuit-breaker reason');
  assert.match(cluster.reason, /2 merged issues reopened within 24h/);

  // 2 distinct reopens >24h apart (25h ago + 1h ago) -> only 1 inside rolling 24h window -> null!
  const stalePmState = {
    merges: {
      101: {
        pr: 101,
        issue: 11,
        issues: [11],
        mergedAt: ago(30),
        reopened: true,
        signals: [
          { kind: 'reopened', level: 'proven', issue: 11, at: ago(25), url: 'https://github.com/acme/widgets/issues/11#event-1', detail: 'Old reopen' },
        ],
      },
    },
  };
  assert.equal(selectCircuitBreakerRegression([
    { pr: 102, issue: 12, kind: 'reopened', code: 'post-merge-reopen', at: ago(1), mergedAt: ago(2), detail: 'Recent reopen' },
  ], { now, postMergeState: stalePmState }), null);

  // clearedAfter ignores historical reopens before clear (1 before + 1 after clear -> null; 2 after clear -> trips!)
  const clearedAt = nowMs - 5 * HOUR;
  assert.equal(selectCircuitBreakerRegression([
    { pr: 102, issue: 12, kind: 'reopened', code: 'post-merge-reopen', at: ago(1), mergedAt: ago(2), detail: 'Post-clear reopen #1' },
  ], { now, postMergeState: crossTickPmState, clearedAfter: clearedAt }), null);

  const postClearCluster = selectCircuitBreakerRegression([
    { pr: 102, issue: 12, kind: 'reopened', code: 'post-merge-reopen', at: ago(2), mergedAt: ago(3), detail: 'Post-clear reopen #1' },
    { pr: 103, issue: 13, kind: 'reopened', code: 'post-merge-reopen', at: ago(1), mergedAt: ago(2), detail: 'Post-clear reopen #2' },
  ], { now, postMergeState: crossTickPmState, clearedAfter: clearedAt });
  assert.equal(postClearCluster?.kind, 'reopened_cluster');
  assert.deepEqual(postClearCluster?.issues, [12, 13]);

  // Revert & CI still win priority over reopened_cluster
  const revertPriority = selectCircuitBreakerRegression([
    { pr: 102, issue: 12, kind: 'reopened', code: 'post-merge-reopen', at: ago(1), mergedAt: ago(2), detail: 'Reopen 2' },
    { pr: 104, issue: 14, kind: 'revert', code: 'post-merge-revert', at: ago(0.5), mergedAt: ago(2), detail: 'Reverted PR #104' },
  ], { now, postMergeState: crossTickPmState });
  assert.equal(revertPriority?.kind, 'reverted');
  assert.equal(revertPriority?.pr, 104);
});

test('3560: coreWorld clustered reopen across separate ticks trips auto -> observe, fires alert, and readMachine preserves reopened_cluster across restarts', async t => {
  const alerts = [];
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1, report: 'draft' } });
  w.github.mergeMovesBase = true;
  const tickWithAlert = () => w.tick({ alert: async payload => { alerts.push(payload); } });

  // Merge #17 and reopen it on tick A -> single reopen keeps mode='auto'
  w.issue(17, { title: 'Fix alpha', body: 'Alpha bug.' });
  await tickWithAlert();
  w.build(17);
  await tickWithAlert();
  w.review(17, 'PASS');
  w.suite(17, 0);
  await tickWithAlert();
  assert.equal(w.github.issues.get(17).state, 'closed');

  w.advance(5 * MIN);
  await tickWithAlert();
  await w.gh(['api', '--include', '--method', 'PATCH', 'repos/acme/widgets/issues/17', '--input', '-'], {
    input: JSON.stringify({ state: 'open' }),
  });
  w.github.label(17, 'pdd:stuck');
  w.advance(20 * MIN);
  await tickWithAlert();

  assert.equal(w.settings.mode, 'auto', '1 reopen must NOT pause auto mode');
  assert.equal(alerts.length, 0);

  // Merge #18 2 hours later, then reopen #18 on a separate tick -> 2nd distinct reopen within 24h trips breaker!
  w.advance(2 * HOUR);
  w.issue(18, { title: 'Fix beta', body: 'Beta bug.' });
  await tickWithAlert();
  w.build(18);
  await tickWithAlert();
  w.review(18, 'PASS');
  w.suite(18, 0);
  await tickWithAlert();
  assert.equal(w.github.issues.get(18).state, 'closed');

  await w.gh(['api', '--include', '--method', 'PATCH', 'repos/acme/widgets/issues/18', '--input', '-'], {
    input: JSON.stringify({ state: 'open' }),
  });
  w.github.label(18, 'pdd:stuck');
  w.advance(20 * MIN);
  await tickWithAlert();

  assert.equal(w.settings.mode, 'observe', '2nd distinct reopened issue within 24h must downgrade auto -> observe');
  assert.equal(w.state.mode, 'observe');
  assert.equal(w.state.circuitBreaker?.kind, 'reopened_cluster');
  assert.equal(w.state.circuitBreaker?.code, 'post-merge-reopen');
  assert.deepEqual(w.state.circuitBreaker?.issues, [17, 18]);
  assert.equal(alerts.length, 1);
  assert.match(alerts[0].text, /post-merge-reopen/);
  assert.match(alerts[0].tried, /2 or more merged issues were reopened within 24 hours/);

  // Simulate process restart: wipe in-memory state.circuitBreaker and re-read from core.json via readMachine (via coreStatus + tickCore)
  const savedCore = JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
  assert.equal(savedCore.circuitBreaker?.kind, 'reopened_cluster');
  assert.equal(savedCore.circuitBreaker?.code, 'post-merge-reopen');
  delete w.state.circuitBreaker;
  w.settings.mode = 'auto';
  w.state.mode = 'auto';

  const statusAfterRestart = coreStatus({ state: w.state, settings: w.settings }, { root: w.root, reportRoot: w.reportRoot, now: w.now });
  assert.match(statusAfterRestart, /Circuit breaker: mode downgraded from auto to observe/);
  assert.match(statusAfterRestart, /2 merged issues reopened within 24h/);

  w.advance(MIN);
  await tickWithAlert();
  assert.equal(w.settings.mode, 'observe', 'persisted reopened_cluster breaker must survive restart and hold observe');
  assert.equal(w.state.circuitBreaker?.kind, 'reopened_cluster', 'readMachine must preserve reopened_cluster kind (not coerce to ci_broken)');
  assert.equal(w.state.circuitBreaker?.code, 'post-merge-reopen');
  assert.deepEqual(w.state.circuitBreaker?.issues, [17, 18]);
});

test('3140: post-merge history rows & report drafts are ingested cleanly (0% data loss), classified accurately, deduplicated, capped, and redacted when auto-filing', async t => {
  // 1. Verify exact structured-code alignment for post-merge codes
  assert.deepEqual(classifyIncidentBucket({ code: 'post-merge-reopen' }), {
    bucket: 'agent-quality', reasonCode: 'reopened-regression', rule: 'agent-quality-structured-code',
  });
  assert.deepEqual(classifyIncidentBucket({ code: 'post-merge-revert' }), {
    bucket: 'agent-quality', reasonCode: 'reverted-regression', rule: 'agent-quality-structured-code',
  });
  assert.deepEqual(classifyIncidentBucket({ code: 'post-merge-ci' }), {
    bucket: 'agent-quality', reasonCode: 'post-merge-ci-regression', rule: 'agent-quality-structured-code',
  });

  // 2. Seed a core root with 0.1.50-style postMerge:true rows (no `outcome` field!), post-merge.json, flakes.jsonl, and reports/drafts/
  const root = makeTempDir(t, 'pdd-postmerge-ingest-');
  const reportRoot = join(root, 'reports');
  mkdirSync(join(reportRoot, 'drafts'), { recursive: true });
  const secretToken = 'ghp_SuperSecretLiveToken1234567890abcd';
  const customSecret = 'my-super-secret-db-password-999';
  const mergeSha1 = 'a'.repeat(40);
  const mergeSha2 = 'b'.repeat(40);
  const mergeSha3 = 'c'.repeat(40);

  writeFileSync(join(root, 'post-merge.json'), JSON.stringify({
    schema: 'pdd.autopilot-post-merge.v1',
    merges: {
      201: {
        pr: 201, issue: 51, issues: [51], mergeCommit: mergeSha1, mergedAt: '2026-11-22T10:00:00Z', reopened: true,
        signals: [{ kind: 'reopened', level: 'proven', issue: 51, at: '2026-11-22T11:00:00Z', url: 'https://github.com/acme/app/issues/51#event-10', detail: 'Issue #51 reopened' }],
      },
      202: {
        pr: 202, issue: 52, issues: [52], mergeCommit: mergeSha2, mergedAt: '2026-11-22T10:30:00Z', reverted: true,
        signals: [{ kind: 'revert', level: 'proven', issue: 52, at: '2026-11-22T11:30:00Z', url: 'https://github.com/acme/app/commit/' + mergeSha2, detail: 'Commit reverted PR #202' }],
      },
      203: {
        pr: 203, issue: 53, issues: [53], mergeCommit: mergeSha3, mergedAt: '2026-11-22T10:45:00Z', ciRegression: true,
        signals: [{ kind: 'ci', level: 'proven', issue: 53, at: '2026-11-22T11:45:00Z', url: 'https://github.com/acme/app/runs/999', detail: 'ci/unit failed on main' }],
      },
    },
  }));

  writeFileSync(join(root, 'history.jsonl'), [
    // Historical 0.1.50 postMerge rows with NO `outcome` field!
    JSON.stringify({ at: Date.parse('2026-11-22T11:05:00Z'), issue: 51, pr: 201, postMerge: true, kind: 'reopened', code: 'post-merge-reopen', text: `Issue #51 reopened; ping @alice token=${secretToken} path=/Users/serhan/private/key.pem ${customSecret}` }),
    JSON.stringify({ at: Date.parse('2026-11-22T11:35:00Z'), issue: 52, pr: 202, postMerge: true, kind: 'revert', code: 'post-merge-revert', text: 'PR #202 reverted on main' }),
    JSON.stringify({ at: Date.parse('2026-11-22T11:50:00Z'), issue: 53, pr: 203, postMerge: true, kind: 'ci', code: 'post-merge-ci', text: 'unit-tests failed on main after merge' }),
    // Vague / non-actionable rows that MUST NOT auto-file noisy GitHub issues
    JSON.stringify({ at: Date.parse('2026-11-22T12:00:00Z'), issue: 54, outcome: 'ended', poolExhausted: true, text: 'quota exhausted 429' }),
    JSON.stringify({ at: Date.parse('2026-11-22T12:05:00Z'), outcome: 'ended', text: 'failed' }),
  ].join('\n') + '\n');

  writeFileSync(join(reportRoot, 'drafts', 'pdd.autopilot-core.lease-bug.0.1.json'), JSON.stringify({
    fingerprint: 'pdd.autopilot-core.lease-bug.0.1',
    kind: 'pdd',
    component: 'autopilot-core',
    code: 'lease-bug',
    step: 'claim',
    cause: 'Claim lease leaked across restart',
    detail: 'Lease collision on issue #55',
  }));

  const harvested = collectLocalAutopilotIncidents(root, { repo: 'acme/app', reportRoot });
  const pmRows = harvested.filter(i => i.stage === 'post-merge');
  assert.equal(pmRows.length, 3, 'ALL 3 post-merge history rows must be ingested (0 dropped!)');
  assert.equal(pmRows.find(r => r.pr === 201).mergeCommit, mergeSha1, 'enriched mergeCommit from post-merge.json');
  assert.equal(pmRows.find(r => r.pr === 201).url, 'https://github.com/acme/app/issues/51#event-10', 'enriched signal URL from post-merge.json');
  assert.ok(harvested.some(i => i.code === 'lease-bug'), 'report drafts must be ingested via { root }, { fs }');

  // Strong-evidence gate checks
  assert.equal(hasStrongInvestigationEvidence({
    bucket: 'environment', reasonCode: 'quota-or-rate-limit', occurrences: 5, provenance: [{ repo: 'acme/app', issue: 54, snippet: '429 quota' }],
  }), false, 'quota exhaustion must not auto-file GitHub issues');
  assert.equal(hasStrongInvestigationEvidence({
    bucket: 'environment', reasonCode: 'flaky-infra', occurrences: 1, provenance: [{ repo: 'acme/app', issue: 54, target: 'test/a.mjs', snippet: 'one flake' }],
  }), false, 'single flake must not auto-file GitHub issues');
  assert.equal(hasStrongInvestigationEvidence({
    bucket: 'environment', reasonCode: 'flaky-infra', occurrences: 3, provenance: [{ repo: 'acme/app', issue: 54, target: 'test/a.mjs', snippet: 'recurring flake' }],
  }), true, 'recurring flake (>=3x) with concrete target qualifies');
  assert.equal(hasStrongInvestigationEvidence({
    bucket: 'agent-quality', reasonCode: 'agent-quality-defect', occurrences: 1, provenance: [{ repo: 'acme/app', snippet: 'failed' }],
  }), false, 'vague incident with no PR/issue/commit/target must not auto-file');

  // 3. Run daily investigator with writeIssues:true + maxIssuesPerRun=2 cap
  const created = [];
  const ghPort = {
    listIssues: async () => created.map(c => ({ body: c.body })),
    createIssue: async payload => { created.push(payload); return { number: 900 + created.length, html_url: `https://github.com/acme/app/issues/${900 + created.length}` }; },
  };
  const nowMs = Date.parse('2026-11-22T18:00:00Z');
  const run1 = await runDailyAutopilotInvestigation({
    root, repo: 'acme/app', reportRoot, date: '2026-11-22', now: () => nowMs,
    writeIssues: true, gh: ghPort, maxIssuesPerRun: 2, secrets: [customSecret],
  });
  assert.equal(run1.report.summary.totalInputs, 6);
  assert.equal(run1.report.createdIssues.length, 2, 'strictly capped at maxIssuesPerRun=2');
  assert.equal(loadInvestigationLedger(root).filed.size, 2);

  // Verify rich structured body + zero secret/path/mention leaks
  for (const issue of created) {
    assert.deepEqual(issue.labels, ['pdd:autopilot-report']);
    assert.match(issue.body, /## Root-Cause Diagnosis/);
    assert.match(issue.body, /## Concrete Evidence & Provenance/);
    assert.match(issue.body, /## Reproduction & Verification Context/);
    assert.match(issue.body, new RegExp(INVESTIGATOR_MARKER_PREFIX));
    assert.equal(issue.body.includes(secretToken), false, 'ghp token must be redacted');
    assert.equal(issue.body.includes(customSecret), false, 'custom secret must be redacted');
    assert.equal(issue.body.includes('/Users/serhan/'), false, 'local home path must be scrubbed');
  }

  // Run 2 on same day with higher cap: files remaining 2 strong-evidence findings (NOT the 2 already filed, NOT quota, NOT vague)!
  const run2 = await runDailyAutopilotInvestigation({
    root, repo: 'acme/app', reportRoot, date: '2026-11-22', now: () => nowMs + 60_000,
    writeIssues: true, gh: ghPort, maxIssuesPerRun: 10, secrets: [customSecret],
  });
  assert.equal(run2.report.createdIssues.length, 2, 'files remaining 2 strong findings (total 4: lease-bug + 3 post-merge regressions), skips quota + vague + already-filed');
  const reopenIssue = created.find(c => c.body.includes('reopened-regression'));
  assert.ok(reopenIssue, 'post-merge-reopen was auto-filed with rich evidence');
  assert.match(reopenIssue.body, new RegExp(mergeSha1));
  assert.match(reopenIssue.body, /PR: #201/);
  assert.match(reopenIssue.body, /Issue: #51/);
  assert.match(reopenIssue.body, /`@alice`/);
  assert.equal(reopenIssue.body.includes(secretToken), false);
  assert.equal(reopenIssue.body.includes('/Users/serhan/'), false);

  // Run 3 AFTER deleting local fingerprints.json: GitHub open-issue marker dedupe STILL prevents any duplicate!
  rmSync(join(root, 'investigations', 'fingerprints.json'));
  const run3 = await runDailyAutopilotInvestigation({
    root, repo: 'acme/app', reportRoot, date: '2026-11-22', now: () => nowMs + 120_000,
    writeIssues: true, gh: ghPort, maxIssuesPerRun: 10, secrets: [customSecret],
  });
  assert.equal(run3.report.createdIssues.length, 0, 'open GitHub issue markers prevent duplicates even without local fingerprints.json');
  assert.equal(loadInvestigationLedger(root).filed.size, 4, 're-synced filed fingerprints from GitHub markers');

  // Fail-closed: if gh.listIssues throws, 0 issues are filed
  const failingGh = {
    listIssues: async () => { throw new Error('503 Service Unavailable'); },
    createIssue: async () => { assert.fail('must NOT create issue when listIssues fails'); },
  };
  rmSync(join(root, 'investigations', 'fingerprints.json'));
  const failClosed = await runDailyAutopilotInvestigation({
    root, repo: 'acme/app', reportRoot, date: '2026-11-22', now: () => nowMs + 180_000,
    writeIssues: true, gh: failingGh, maxIssuesPerRun: 5,
  });
  assert.equal(failClosed.report.createdIssues.length, 0, 'must fail closed when listIssues throws');
});

test('3140: daily tick runs investigator at most once/day/repo, never blocks ticks on errors, auto-files under report:file, and surfaces in coreStatus + pdd metrics + CLI', async t => {
  // Part A: coreWorld daily tick wiring
  const w = await coreWorld(t, { settings: { mode: 'observe', runs: 1, report: 'file' } });
  mkdirSync(w.root, { recursive: true });
  writeFileSync(join(w.root, 'history.jsonl'), [
    JSON.stringify({
      at: w.now() - 10 * MIN, repo: 'acme/widgets', issue: 77, pr: 177, postMerge: true,
      kind: 'reopened', code: 'post-merge-reopen', mergeCommit: 'd'.repeat(40),
      url: 'https://github.com/acme/widgets/issues/77#event-9', text: 'Issue #77 reopened after PR #177 merged',
    }),
  ].join('\n') + '\n');

  // Tick 1: runs daily investigation once, auto-files 1 issue in acme/widgets (labeled pdd:autopilot-report), persists report + core.json lastInvestigation
  const t1 = await w.tick();
  assert.equal(t1.exitCode, 0);
  const invIssues1 = [...w.github.issues.values()].filter(i => i.labels.includes('pdd:autopilot-report'));
  assert.equal(invIssues1.length, 1, 'daily tick auto-filed 1 strong-evidence issue in repo');
  assert.match(invIssues1[0].body, /reopened-regression/);
  assert.match(invIssues1[0].body, /PR: #177/);

  const coreAfterT1 = JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
  assert.match(coreAfterT1.lastInvestigation?.date ?? '', /^\d{4}-\d{2}-\d{2}$/);
  assert.equal(coreAfterT1.lastInvestigation?.uniqueFindings, 1);
  assert.equal(coreAfterT1.lastInvestigation?.createdIssuesCount, 1);

  // coreStatus surfaces the persisted daily investigation summary
  const stText = coreStatus({ state: w.state, settings: w.settings }, { root: w.root, reportRoot: w.reportRoot, now: w.now });
  assert.match(stText, /Investigation \(\d{4}-\d{2}-\d{2}\): 1 unique finding\(s\) \(1 new, 1 filed; orchestrator=0, agent-quality=1, environment=0, real-hold=0\)\./);

  // Tick 2 on same day: must NOT re-run or file again (even if a new incident is appended)
  let ghCreateCalls = 0;
  w.advance(30 * MIN);
  await w.tick({
    investigationGh: {
      listIssues: async () => [],
      createIssue: async () => { ghCreateCalls += 1; return { number: 999 }; },
    },
  });
  assert.equal(ghCreateCalls, 0, 'daily investigator runs at most once per standup day per repo');

  // Tick 3 next day with a failing investigationGh: must NOT block or fail the tick!
  w.advance(25 * HOUR);
  w.issue(88, { title: 'Normal work', body: 'Still proceeds cleanly.' });
  const t3 = await w.tick({
    investigationGh: {
      listIssues: async () => { throw new Error('simulated GitHub failure'); },
      createIssue: async () => { throw new Error('simulated GitHub failure'); },
    },
  });
  assert.equal(t3.exitCode, 0, 'investigation error must never block or fail a tick');
  assert.ok(w.job(88, 'build'), 'normal job intake still proceeded despite investigation error');

  // Part B: pdd metrics surfaces read-only standup investigation summary in text, JSON, and HTML
  const stateDir = makeTempDir(t, 'pdd-metrics-inv-');
  const autopilotDir = join(stateDir, 'autopilot');
  const coreDir = join(autopilotDir, 'abc123-core');
  mkdirSync(coreDir, { recursive: true });
  writeFileSync(join(autopilotDir, 'abc123.json'), JSON.stringify({ repo: 'acme/widgets', enabled: true, mode: 'observe' }));
  writeFileSync(join(coreDir, 'history.jsonl'), [
    JSON.stringify({ at: Date.parse('2026-11-22T15:00:00Z'), issue: 10, pr: 110, outcome: 'merged', text: 'Merged PR #110' }),
    JSON.stringify({ at: Date.parse('2026-11-22T16:00:00Z'), issue: 10, pr: 110, postMerge: true, kind: 'reopened', code: 'post-merge-reopen', text: 'Issue #10 reopened after PR #110 merged' }),
  ].join('\n') + '\n');

  const outText = capture(), errText = capture();
  const codeText = await runMetrics({
    argv: ['--standup', '--timezone', 'America/Los_Angeles'],
    cwd: stateDir,
    stdout: outText,
    stderr: errText,
    ports: {
      stateDir,
      now: () => Date.parse('2026-11-22T18:00:00Z'),
      openIssues: { 'acme/widgets': 3 },
      regressions: [],
    },
  });
  assert.equal(codeText, 0, errText.text);
  assert.match(outText.text, /Daily Investigation \(2026-11-22\) · Unique: 1/);
  assert.match(outText.text, /agent-quality\/reopened-regression/);

  const htmlFile = join(stateDir, 'report.html');
  const outHtml = capture(), errHtml = capture();
  const codeHtml = await runMetrics({
    argv: ['--html', '--file', htmlFile, '--timezone', 'America/Los_Angeles'],
    cwd: stateDir,
    stdout: outHtml,
    stderr: errHtml,
    ports: {
      stateDir,
      now: () => Date.parse('2026-11-22T18:00:00Z'),
      openIssues: { 'acme/widgets': 3 },
      regressions: [],
      openBrowser: false,
    },
  });
  assert.equal(codeHtml, 0, errHtml.text);
  assert.match(readFileSync(htmlFile, 'utf8'), /Daily Investigation \(2026-11-22\)/);

  // Part C: CLI `pdd autopilot investigate` (read-only default, --json, --write-issues --max-issues, invalid flag)
  const cliOut = capture(), cliErr = capture();
  const cliExit = await runPdd(['autopilot', 'investigate', '--date', '2026-11-22', '--json'], {
    cwd: stateDir,
    stdout: cliOut,
    stderr: cliErr,
    syncOwnedUserSkills: () => ({ updated: [] }),
    autopilotInvestigatePorts: { root: coreDir, repo: 'acme/widgets', now: () => Date.parse('2026-11-22T18:00:00Z') },
  });
  assert.equal(cliExit, 0, cliErr.text);
  const cliJson = JSON.parse(cliOut.text);
  assert.equal(cliJson.readOnly, true);
  assert.equal(cliJson.summary.uniqueFindings, 1);
  assert.equal(cliJson.findings[0].reasonCode, 'reopened-regression');

  const badDate = await runAutopilotInvestigate({ date: 'not-a-date' });
  assert.equal(badDate.exitCode, 2);
});

test('3140: continueEnd posts deterministic 4-bucket root-cause diagnosis and next step before labeling pdd:stuck, and saves diagnosis in history.jsonl', async t => {
  // 1. Direct unit check across all 4 plain-English buckets
  assert.equal(diagnoseStuckCause({ code: 'no-test-command', reason: 'no full test command' }).label, 'repo/spec problem');
  assert.equal(diagnoseStuckCause({ code: 'suite-fail', reason: 'tests failed' }).label, 'agent-quality');
  assert.equal(diagnoseStuckCause({ code: 'suite-broken', harnessBug: true, reason: 'runner crashed' }).label, 'pdd/harness bug');
  assert.equal(diagnoseStuckCause({ reason: 'killed by SIGKILL out of memory (exit 137)' }).label, 'infra/quota/flake');

  // 2. End-to-end coreWorld test #1: repo/spec problem (`no-test-command`) -> pdd:stuck comment + history.jsonl diagnosis
  {
    const w = await coreWorld(t, { settings: { runs: 1, testCommand: null, report: 'draft' } });
    // Remove package.json / test files so base has no test command
    w.issue(31, { title: 'Add helper', body: 'Add a helper.' });
    await w.tick();
    w.build(31);
    await w.tick();
    w.review(31, 'PASS');
    await w.tick();

    assert.ok(w.labels(31).includes('pdd:stuck'), 'issue #31 should be labeled pdd:stuck');
    const stuckComment = w.comments(31).find(c => c.includes('<!-- pdd:autopilot-core:end:31:'));
    assert.ok(stuckComment, 'END comment posted before pdd:stuck');
    assert.match(stuckComment, /- Diagnosis: repo\/spec problem \(`real-hold` \/ `no-test-command`\)/);
    assert.match(stuckComment, /- Next step: Configure `autopilot\.testCommand`/);

    const history = readFileSync(join(w.root, 'history.jsonl'), 'utf8').trim().split('\n').map(l => JSON.parse(l));
    const endedRow = history.find(r => r.issue === 31 && r.outcome === 'ended');
    assert.equal(endedRow?.code, 'no-test-command');
    assert.equal(endedRow?.diagnosis?.bucket, 'real-hold');
    assert.equal(endedRow?.diagnosis?.label, 'repo/spec problem');
  }

  // 3. End-to-end coreWorld test #2: agent-quality (`checks-red` after review FAIL with 0 repairs) -> pdd:stuck comment + history.jsonl
  {
    const w = await coreWorld(t, { settings: { runs: 1, maxRepairs: 0, report: 'draft' } });
    w.issue(32, { title: 'Fix parser', body: 'Fix parser bug.' });
    await w.tick();
    w.build(32);
    await w.tick();
    w.review(32, 'FAIL', ['Missing error handling for empty input']);
    w.suite(32, 0);
    await w.tick();

    assert.ok(w.labels(32).includes('pdd:stuck'), 'issue #32 should be labeled pdd:stuck');
    const stuckComment = w.comments(32).find(c => c.includes('<!-- pdd:autopilot-core:end:32:'));
    assert.ok(stuckComment);
    assert.match(stuckComment, /- Diagnosis: agent-quality \(`agent-quality` \/ `(?:review-fail|suite-fail|checks-red)`\)/);
    assert.match(stuckComment, /- Next step: Inspect the failing checks/);

    const history = readFileSync(join(w.root, 'history.jsonl'), 'utf8').trim().split('\n').map(l => JSON.parse(l));
    const endedRow = history.find(r => r.issue === 32 && r.outcome === 'ended');
    assert.equal(endedRow?.diagnosis?.bucket, 'agent-quality');
    assert.equal(endedRow?.diagnosis?.label, 'agent-quality');
  }

  // 4. End-to-end coreWorld test #3: pdd/harness bug (draft report with no GitHub report ref -> pdd:stuck)
  {
    const w = await coreWorld(t, { settings: { runs: 1, report: 'draft' } });
    w.issue(33, { title: 'Test pdd failure', body: 'Triggers pdd draft failure.' });
    await w.tick();
    w.finish(33, 'build', { result: { outcome: 'failed', kind: 'pdd', component: 'pdd-cli', code: 'crash', cause: 'Unexpected pdd crash with ghp_SecretToken99999999999999999999' } });
    await w.tick();

    assert.ok(w.labels(33).includes('pdd:stuck'));
    const stuckComment = w.comments(33).find(c => c.includes('<!-- pdd:autopilot-core:end:33:'));
    assert.ok(stuckComment);
    assert.match(stuckComment, /- Diagnosis: pdd\/harness bug \(`orchestrator` \/ `harness-bug`\)/);
    assert.match(stuckComment, /- Next step: Inspect the PDD\/harness report/);
    assert.equal(stuckComment.includes('ghp_SecretToken99999999999999999999'), false, 'secrets must be redacted in stuck diagnosis');
  }

  // 5. End-to-end coreWorld test #4: infra/quota/flake (3rd no-result strike with OOM log tail -> pdd:stuck with infra/quota/flake diagnosis)
  {
    const w = await coreWorld(t, { settings: { runs: 1, report: 'draft' } });
    mkdirSync(w.root, { recursive: true });
    writeFileSync(join(w.root, 'history.jsonl'), [
      JSON.stringify({ at: w.now() - 2 * HOUR, issue: 34, strike: true }),
      JSON.stringify({ at: w.now() - HOUR, issue: 34, strike: true }),
    ].join('\n') + '\n');
    w.issue(34, { title: 'Memory heavy test', body: 'OOM on worker.' });
    await w.tick();
    w.say(34, 'build', 'FATAL ERROR: process killed with SIGKILL out of memory (exit 137)');
    w.finish(34, 'build', { code: 137 });
    await w.tick();

    assert.ok(w.labels(34).includes('pdd:stuck'), '3rd strike should label pdd:stuck');
    const stuckComment = w.comments(34).find(c => c.includes('<!-- pdd:autopilot-core:end:34:'));
    assert.ok(stuckComment);
    assert.match(stuckComment, /- Diagnosis: infra\/quota\/flake \(`environment` \/ `runner-oom`\)/);
    assert.match(stuckComment, /- Next step: Check machine\/CI memory/);
  }
});

test('adversarial review hardening: anti-spam, cross-repo isolation, pagination fail-closed, mention/backtick/secret redaction, clearedAfter coreWorld, log-tail EOF, and metrics windowing', async t => {
  // 1. Cross-repo core-reports isolation: machine-wide shared reportRoot drafts MUST NOT leak or auto-file into ctx.repo
  {
    const w = await coreWorld(t, { settings: { mode: 'observe', runs: 1, report: 'file' } });
    mkdirSync(join(w.reportRoot, 'drafts'), { recursive: true });
    writeFileSync(join(w.reportRoot, 'drafts', 'pdd.other-repo.secret-bug.0.1.json'), JSON.stringify({
      fingerprint: 'pdd.other-repo.secret-bug.0.1',
      kind: 'pdd',
      component: 'private-billing-service',
      code: 'lease-bug',
      step: 'claim',
      cause: 'Private repo secret crash details',
      detail: 'Private repo internal stack trace',
    }));
    await w.tick();
    const filedInRepo = [...w.github.issues.values()].filter(i => i.labels.includes('pdd:autopilot-report'));
    assert.equal(filedInRepo.length, 0, 'shared machine-wide core-reports drafts must NEVER auto-file into an unrelated repo');
  }

  // 2. Human stops, machine-sleep releases, negative maxIssuesPerRun, and pagination truncation MUST fail closed (0 issues filed)
  {
    const root = makeTempDir(t, 'pdd-antispam-');
    const nowMs = Date.parse('2026-11-23T18:00:00Z');
    writeFileSync(join(root, 'history.jsonl'), [
      JSON.stringify({ at: nowMs - HOUR, issue: 10, outcome: 'stopped', text: 'stopped by a person: pdd:working was removed' }),
      JSON.stringify({ at: nowMs - 2 * HOUR, issue: 11, outcome: 'released', owner: 'machine', text: 'this machine ran no tick for 3.2 hours (for example while it slept), and the job stopped' }),
      JSON.stringify({ at: nowMs - 3 * HOUR, issue: 12, outcome: 'ended', code: 'claim-expired', text: 'the claim expired while the machine slept' }),
    ].join('\n') + '\n');
    let createCalls = 0;
    const gh = {
      listIssues: async () => [],
      createIssue: async () => { createCalls += 1; return { number: 1 }; },
    };
    const res = await runDailyAutopilotInvestigation({
      root, repo: 'acme/app', date: '2026-11-23', now: () => nowMs, writeIssues: true, gh,
    });
    assert.equal(res.report.createdIssues.length, 0);
    assert.equal(createCalls, 0, 'human stops, laptop sleeps, and claim-expired must NEVER auto-file issues');

    // Negative maxIssuesPerRun fails closed (0 issues, never defaults to 5)
    const strongIncident = [{ repo: 'acme/app', issue: 50, pr: 150, code: 'post-merge-reopen', detail: 'Issue #50 reopened' }];
    const negCap = await investigateIncidents({
      incidents: strongIncident, repo: 'acme/app', date: '2026-11-23', writeIssues: true, gh, maxIssuesPerRun: -1,
    });
    assert.equal(negCap.createdIssues.length, 0, 'negative maxIssuesPerRun must fail closed to 0');

    // Pagination truncation in collectExistingIssueBodies fails closed (0 issues filed)
    let pagesFetched = 0;
    const truncatedGh = {
      listIssues: async ({ page }) => { pagesFetched = page; return { items: [], hasNext: true }; },
      createIssue: async () => { createCalls += 1; return { number: 2 }; },
    };
    const trunc = await investigateIncidents({
      incidents: strongIncident, repo: 'acme/app', date: '2026-11-23', writeIssues: true, gh: truncatedGh, maxIssuesPerRun: 5,
    });
    assert.equal(pagesFetched, 50);
    assert.equal(trunc.createdIssues.length, 0, 'truncated pagination must fail closed and create 0 issues');
    assert.equal(createCalls, 0);
  }

  // 3. Backtick breakout, @mention defanging, local-path scrubbing, and CLI --write-issues --max-issues 1
  {
    const body = formatInvestigationIssueBody({
      fingerprint: 'abcd1234abcd1234',
      marker: '<!-- pdd:investigator:v1:abcd1234abcd1234 -->',
      bucket: 'agent-quality',
      reasonCode: 'reopened-regression',
      occurrences: 2,
      proposal: { rung: 'runtime-proof', rank: 3, title: 'Fix', action: 'Check `x`@bob and ``@carol in /home/dev/app and ~/secrets' },
      provenance: [{
        repo: 'acme/app',
        issue: 99,
        pr: 199,
        command: 'npm test -- `@alice` /private/tmp/x C:\\Users\\bob\\proj',
        component: 'src/`evil`@dave',
        snippet: 'Run `x`@eve and ``@frank in /Users/serhan/proj',
      }],
    }, { repo: 'acme/app' });
    // Strip all balanced inline code spans and verify ZERO bare @mentions remain anywhere!
    const outsideCode = body.replace(/`[^`\r\n]+`/g, '');
    assert.doesNotMatch(outsideCode, /@[a-zA-Z0-9]/, `no bare @mention may survive outside inline code spans:\n${body}`);
    assert.equal(body.includes('/home/dev/'), false);
    assert.equal(body.includes('/Users/serhan/'), false);
    assert.equal(body.includes('/private/tmp/'), false);
    assert.equal(body.includes('~/secrets'), false);
    assert.equal(body.includes('C:\\Users\\bob\\'), false);

    // Real CLI --write-issues --max-issues 1 path + invalid calendar date 2026-02-31
    const cliRoot = makeTempDir(t, 'pdd-cli-write-');
    writeFileSync(join(cliRoot, 'history.jsonl'), [
      JSON.stringify({ at: Date.parse('2026-11-23T12:00:00Z'), issue: 1, pr: 11, postMerge: true, kind: 'reopened', code: 'post-merge-reopen', text: 'Reopened #1' }),
      JSON.stringify({ at: Date.parse('2026-11-23T12:05:00Z'), issue: 2, pr: 12, postMerge: true, kind: 'revert', code: 'post-merge-revert', text: 'Reverted #2' }),
    ].join('\n') + '\n');
    const ghCalls = [];
    const fakeGh = async (args, opts) => {
      ghCalls.push({ args, input: opts?.input });
      const ep = args.find(a => String(a).startsWith('repos/')) ?? '';
      if (args.includes('GET')) {
        assert.match(ep, /state=all/, 'CLI investigator listIssues must query state=all');
        assert.match(ep, /labels=pdd%3Aautopilot-report/, 'CLI investigator listIssues must filter by pdd:autopilot-report');
        return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n[]', stderr: '' };
      }
      return { code: 0, stdout: 'HTTP/2.0 201 Created\r\n\r\n{"number":701,"html_url":"https://github.com/acme/app/issues/701"}', stderr: '' };
    };
    const out = capture(), err = capture();
    const exit = await runPdd(['autopilot', 'investigate', '--date', '2026-11-23', '--write-issues', '--max-issues', '1', '--json'], {
      cwd: cliRoot,
      stdout: out,
      stderr: err,
      syncOwnedUserSkills: () => ({ updated: [] }),
      autopilotInvestigatePorts: { root: cliRoot, repo: 'acme/app', gh: fakeGh, now: () => Date.parse('2026-11-23T18:00:00Z') },
    });
    assert.equal(exit, 0, err.text);
    const parsed = JSON.parse(out.text);
    assert.equal(parsed.readOnly, false);
    assert.equal(parsed.createdIssues.length, 1, 'CLI --write-issues --max-issues 1 must file exactly 1 issue');

    const badCal = await runAutopilotInvestigate({ date: '2026-02-31' });
    assert.equal(badCal.exitCode, 2, 'impossible calendar date 2026-02-31 must return exit 2');
  }

  // 4. selectCircuitBreakerRegression edge cases: now: null, invalid-PR revert before valid CI, undated old reopen, and coreWorld clearedAfter with 2 old reopens in post-merge.json
  {
    const nowMs = Date.parse('2026-11-23T18:00:00Z');
    // now: null falls back to Date.now() instead of epoch 0
    const withNullNow = selectCircuitBreakerRegression([
      { pr: 500, issue: 50, kind: 'ci', code: 'post-merge-ci', detail: 'ci broke' },
    ], { now: null });
    assert.equal(withNullNow?.pr, 500);

    // Invalid PR revert must NOT shadow valid CI behind it
    const validBehindBad = selectCircuitBreakerRegression([
      { pr: null, issue: 51, kind: 'revert', code: 'post-merge-revert', detail: 'malformed' },
      { pr: 501, issue: 52, kind: 'ci', code: 'post-merge-ci', detail: 'real CI break' },
    ], { now: () => nowMs });
    assert.equal(validBehindBad?.pr, 501);
    assert.equal(validBehindBad?.kind, 'ci_broken');

    // Undated incoming reopens with 30-day-old mergedAt must NOT trip 24h cluster
    const oldUndated = selectCircuitBreakerRegression([
      { pr: 601, issue: 61, kind: 'reopened', code: 'post-merge-reopen', mergedAt: new Date(nowMs - 30 * 24 * HOUR).toISOString() },
      { pr: 602, issue: 62, kind: 'reopened', code: 'post-merge-reopen', mergedAt: new Date(nowMs - 30 * 24 * HOUR).toISOString() },
    ], { now: () => nowMs });
    assert.equal(oldUndated, null);

    // coreWorld: after clearing circuitBreakerClearedAt, 2 old reopens remaining in post-merge.json do NOT re-trip auto!
    const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1, report: 'draft' } });
    mkdirSync(w.root, { recursive: true });
    const oldAt1 = new Date(w.now() - 2 * HOUR).toISOString();
    const oldAt2 = new Date(w.now() - HOUR).toISOString();
    writeFileSync(join(w.root, 'history.jsonl'), `${JSON.stringify({ at: w.now() - 4 * HOUR, issue: 1, pr: 101, outcome: 'merged', text: 'merged' })}\n`);
    writeFileSync(join(w.root, 'post-merge.json'), JSON.stringify({
      schema: 'pdd.autopilot-post-merge.v1',
      merges: {
        101: { pr: 101, issue: 1, issues: [1], mergedAt: new Date(w.now() - 4 * HOUR).toISOString(), reopened: true, signals: [{ kind: 'reopened', level: 'proven', issue: 1, at: oldAt1, detail: 'reopened #1' }] },
        102: { pr: 102, issue: 2, issues: [2], mergedAt: new Date(w.now() - 3 * HOUR).toISOString(), reopened: true, signals: [{ kind: 'reopened', level: 'proven', issue: 2, at: oldAt2, detail: 'reopened #2' }] },
      },
    }));
    w.state.circuitBreakerClearedAt = w.now() - 10 * MIN;
    await w.tick({ checkPostMerge: async () => ({ newlyDetected: [] }) });
    assert.equal(w.settings.mode, 'auto', 'clearedAfter must prevent 2 pre-clear reopens in post-merge.json from re-tripping auto');
  }

  // 5. buildStuckDiagnosis >4 KiB log tail: detects fatal error at EOF, redacts secret, preserves detail when stderr empty, and ignores symlinked log
  {
    const w = await coreWorld(t, { settings: { runs: 1, report: 'draft' } });
    mkdirSync(w.root, { recursive: true });
    writeFileSync(join(w.root, 'history.jsonl'), [
      JSON.stringify({ at: w.now() - 2 * HOUR, issue: 40, strike: true }),
      JSON.stringify({ at: w.now() - HOUR, issue: 40, strike: true }),
    ].join('\n') + '\n');
    w.issue(40, { title: 'Long log OOM', body: 'Long output then OOM at EOF.' });
    await w.tick();
    // Write >5 KiB of benign noise followed by secret + SIGKILL OOM at EOF
    const padding = `${'info: normal test output line without errors\n'.repeat(130)}`;
    const eofSecret = 'ghp_EndOfFileSecretToken1234567890abcdef';
    w.say(40, 'build', `${padding}FATAL: process killed with SIGKILL out of memory (exit 137) token=${eofSecret}`);
    w.finish(40, 'build', { code: 137 });
    await w.tick();
    const stuckComment = w.comments(40).find(c => c.includes('<!-- pdd:autopilot-core:end:40:'));
    assert.ok(stuckComment);
    assert.match(stuckComment, /- Diagnosis: infra\/quota\/flake \(`environment` \/ `runner-oom`\)/, 'must read EOF of >4 KiB log tail, not first 600 bytes');
    assert.equal(stuckComment.includes(eofSecret), false, 'secret in >4 KiB log tail must be redacted before slicing');

    // Empty stderr still preserves `detail` in diagnoseStuckCause evidence
    const diagWithDetail = diagnoseStuckCause({ pr: 77, code: 'suite-fail', detail: 'test/foo.test.mjs failed 2 assertions', stderr: '' });
    assert.match(diagWithDetail.evidence ?? '', /test\/foo\.test\.mjs failed 2 assertions/);

    // Symlinked log file is safely ignored without reading target outside logs dir
    const outsideDir = makeTempDir(t, 'pdd-sym-outside-');
    const outsideSecretFile = join(outsideDir, 'secret.txt');
    writeFileSync(outsideSecretFile, 'FATAL: SIGKILL out of memory LEAKED_OUTSIDE_DATA');
    const wSym = await coreWorld(t, { settings: { runs: 1, report: 'draft' } });
    mkdirSync(wSym.root, { recursive: true });
    writeFileSync(join(wSym.root, 'history.jsonl'), [
      JSON.stringify({ at: wSym.now() - 2 * HOUR, issue: 41, strike: true }),
      JSON.stringify({ at: wSym.now() - HOUR, issue: 41, strike: true }),
    ].join('\n') + '\n');
    wSym.issue(41, { title: 'Symlink log test', body: 'Ignore symlinked log.' });
    await wSym.tick();
    const job41 = wSym.job(41, 'build');
    rmSync(job41.log, { force: true });
    symlinkSync(outsideSecretFile, job41.log);
    wSym.finish(41, 'build', { code: 1 });
    await wSym.tick();
    const symComment = wSym.comments(41).find(c => c.includes('<!-- pdd:autopilot-core:end:41:'));
    assert.ok(symComment);
    assert.equal(symComment.includes('LEAKED_OUTSIDE_DATA'), false, 'symlinked log file must never be read');
  }

  // 6. pdd metrics --date respects requested time window for investigation summary
  {
    const stateDir = makeTempDir(t, 'pdd-metrics-win-');
    const autopilotDir = join(stateDir, 'autopilot');
    const coreDir = join(autopilotDir, 'win1-core');
    mkdirSync(coreDir, { recursive: true });
    writeFileSync(join(autopilotDir, 'win1.json'), JSON.stringify({ repo: 'acme/widgets', enabled: true, mode: 'observe' }));
    writeFileSync(join(coreDir, 'history.jsonl'), [
      JSON.stringify({ at: Date.parse('2026-11-22T15:00:00Z'), issue: 90, pr: 190, postMerge: true, kind: 'reopened', code: 'post-merge-reopen', text: 'Reopened on Nov 22' }),
    ].join('\n') + '\n');

    const outOld = capture(), errOld = capture();
    const codeOld = await runMetrics({
      argv: ['--date', '2026-11-01', '--timezone', 'UTC', '--json'],
      cwd: stateDir,
      stdout: outOld,
      stderr: errOld,
      ports: { stateDir, now: () => Date.parse('2026-11-23T18:00:00Z'), openIssues: { 'acme/widgets': 1 }, regressions: [] },
    });
    assert.equal(codeOld, 0, errOld.text);
    assert.equal(JSON.parse(outOld.text).investigation, undefined, 'historical --date 2026-11-01 must NOT include Nov 22 incident');
  }
});
