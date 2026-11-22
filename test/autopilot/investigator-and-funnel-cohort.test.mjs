import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  INVESTIGATOR_BUCKETS,
  INVESTIGATOR_MARKER_PREFIX,
  LADDER_OF_FIXES,
  classifyIncidentBucket,
  formatInvestigationMarkdown,
  incidentFingerprint,
  investigateIncidents,
  loadKnownInvestigationFingerprints,
  persistDailyInvestigationReport,
} from '../../src/autopilot/investigator/investigator.mjs';
import {
  computeStageFunnel,
  evaluateMatureCohort,
  extractGraphQlReopenedEvents,
  localAnchorUtcMs,
  resolveStandupWindow,
} from '../../src/autopilot/metrics/funnel-cohort.mjs';
import * as metricsModel from '../../src/metrics-model.mjs';

function makeTempDir(t, prefix) {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

test('investigator: strict 4-bucket classification and Ladder-of-Fixes prioritization (zero LLM confidence scores)', async () => {
  assert.deepEqual(INVESTIGATOR_BUCKETS, ['orchestrator', 'agent-quality', 'environment', 'real-hold']);
  assert.deepEqual(LADDER_OF_FIXES, ['architecture-api', 'lint-checker', 'runtime-proof', 'skill-prose']);

  const incidents = [
    // Real hold -> rung #4 skill-prose
    { repo: 'acme/app', issue: 10, reasonCode: 'protected-path', reason: 'Touches protected billing config requiring CODEOWNERS sign-off' },
    // Agent quality missed-proof regression (PR #3220 style) -> rung #3 runtime-proof
    { repo: 'acme/app', pr: 3220, issue: 3219, kind: 'regression', reopened: true, missedProof: true, reason: 'PR #3220 merged without runtime proof and regressed on real host' },
    // Agent quality weakened assertion -> rung #2 lint-checker (4-part diagnostic template)
    { repo: 'acme/app', pr: 401, issue: 400, kind: 'review-fail', reason: 'Weakened assertion replaced real integration check with tautology', target: 'test/auth.test.mjs' },
    // Environment runner SIGTERM -> rung #1 architecture-api
    { repo: 'acme/app', pr: 501, issue: 500, kind: 'ci-failed', exitSignal: 'SIGTERM', exitCode: 143, detail: 'Suspect CI runner killed with SIGTERM (exit 143)' },
    // Orchestrator lease/state bug -> rung #1 architecture-api
    { repo: 'acme/app', issue: 600, kind: 'lease-collision', reason: 'Autopilot harness lease collision caused duplicate dispatch' },
  ];

  let ghWriteCalls = 0;
  const report = await investigateIncidents({
    incidents,
    repo: 'acme/app',
    date: '2026-11-22',
    now: () => Date.parse('2026-11-22T18:00:00Z'),
    gh: { createIssue: async () => { ghWriteCalls += 1; return { number: 999 }; } },
  });

  assert.equal(report.readOnly, true, 'must default to read-only');
  assert.equal(ghWriteCalls, 0, 'read-only default must make ZERO GitHub issue writes');
  assert.equal(report.findings.length, 5);
  assert.equal(report.summary.buckets.orchestrator.count, 1);
  assert.equal(report.summary.buckets['agent-quality'].count, 2);
  assert.equal(report.summary.buckets.environment.count, 1);
  assert.equal(report.summary.buckets['real-hold'].count, 1);

  // Strictly ordered down Ladder of Fixes: rank 1 -> 2 -> 3 -> 4 (never inverted).
  const ranks = report.proposals.map(p => p.rank);
  assert.deepEqual(ranks, [1, 1, 2, 3, 4]);
  assert.deepEqual(report.proposals.map(p => p.rung), ['architecture-api', 'architecture-api', 'lint-checker', 'runtime-proof', 'skill-prose']);

  const lintFinding = report.findings.find(f => f.proposal.rung === 'lint-checker');
  assert.ok(lintFinding.proposal.diagnosticTemplate?.invariant);
  assert.ok(lintFinding.proposal.diagnosticTemplate?.fix);
  assert.ok(lintFinding.proposal.diagnosticTemplate?.rerun);

  const pr3220 = report.findings.find(f => f.provenance[0]?.pr === 3220);
  assert.equal(pr3220.bucket, 'agent-quality');
  assert.equal(pr3220.proposal.rung, 'runtime-proof');
  assert.match(pr3220.proposal.action, /verify\.paths|pdd prove/);

  // Zero LLM numeric confidence fields anywhere in findings/proposals.
  for (const f of report.findings) {
    assert.equal(Object.hasOwn(f, 'confidence'), false);
    assert.equal(Object.hasOwn(f.proposal, 'confidence'), false);
  }
  assert.equal(classifyIncidentBucket({ reasonCode: 'quota-exhausted' }).bucket, 'environment');
  assert.equal(classifyIncidentBucket({ reasonCode: 'human_decision' }).bucket, 'real-hold');
});

test('investigator: PR #3220 missed-proof + suspect CI/SIGTERM double-replay produces 0 duplicates, redacts secrets, and guards symlinks', async t => {
  const stateDir = makeTempDir(t, 'pdd-investigator-');
  const secretToken = 'ghp_SuperSecretToken9876543210';
  const bearerJwt = 'eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxMjM0NTYifQ.signatureXYZ';
  const apiKey = 'sk-proj-abcd1234efgh5678ijkl';
  const customSecret = 'my-ultra-private-webhook-value';

  const makeBatch = ({ ts, pid, tmpPath }) => [
    {
      repo: 'acme/app',
      pr: 3220,
      issue: 3219,
      kind: 'regression',
      reopened: true,
      missedProof: true,
      reason: `PR #3220 missed runtime proof at ${ts} pid=${pid}`,
      stderr: `Auth failed with ${secretToken} Bearer ${bearerJwt} url=https://bot:pw123@ci.example.test/run?api_key=${apiKey} extra=${customSecret} in ${tmpPath}`,
      url: 'https://user:pass99@github.com/acme/app/pull/3220?token=leakme',
    },
    {
      repo: 'acme/app',
      pr: 3255,
      issue: 3250,
      kind: 'ci-failed',
      exitSignal: 'SIGTERM',
      exitCode: 143,
      detail: `Suspect CI runner SIGTERM at ${ts} pid=${pid} log=${tmpPath}/ci.log`,
      snippet: `-----BEGIN RSA PRIVATE KEY-----\nMIIEowIBAAKCAQEAsecret\n-----END RSA PRIVATE KEY-----`,
    },
  ];

  // Run 1: persist daily investigation report atomically.
  const batch1 = makeBatch({ ts: '2026-11-22T08:00:00Z', pid: 4123, tmpPath: '/tmp/run-aaa' });
  const r1 = await investigateIncidents({
    incidents: batch1, repo: 'acme/app', date: '2026-11-22',
    now: () => Date.parse('2026-11-22T17:00:00Z'), secrets: [customSecret],
  });
  assert.equal(r1.summary.uniqueFindings, 2);
  assert.equal(r1.summary.newFindings, 2);
  assert.equal(r1.summary.deduplicatedCount, 0);

  const p1 = persistDailyInvestigationReport(stateDir, r1, { now: () => Date.parse('2026-11-22T17:00:00Z') });
  assert.equal(p1.newFingerprints.length, 2);
  assert.equal(p1.duplicateFingerprints.length, 0);
  assert.equal(p1.totalUniqueFindings, 2);
  assert.equal(statSync(p1.reportPath).mode & 0o777, 0o600);

  // Verify ALL secrets redacted in JSON on disk and rendered markdown!
  const rawDisk = readFileSync(p1.reportPath, 'utf8');
  const md = formatInvestigationMarkdown(r1, { secrets: [customSecret] });
  for (const leaked of [secretToken, bearerJwt, apiKey, customSecret, 'pw123', 'pass99', 'leakme', 'MIIEowIBAAKCAQEAsecret']) {
    assert.equal(rawDisk.includes(leaked), false, `report JSON must not contain secret "${leaked}"`);
    assert.equal(md.includes(leaked), false, `markdown must not contain secret "${leaked}"`);
  }

  // Run 2: replay exact same two incidents with different timestamps/PIDs/tmp paths -> 0 duplicates!
  const batch2 = makeBatch({ ts: '2026-11-22T11:30:00Z', pid: 9876, tmpPath: '/tmp/run-bbb' });
  assert.equal(incidentFingerprint(batch1[0], null, { secrets: [customSecret] }), incidentFingerprint(batch2[0], null, { secrets: [customSecret] }));
  assert.equal(incidentFingerprint(batch1[1]), incidentFingerprint(batch2[1]));

  const known = loadKnownInvestigationFingerprints(stateDir);
  assert.equal(known.size, 2);
  const r2 = await investigateIncidents({
    incidents: batch2, repo: 'acme/app', date: '2026-11-22',
    knownFingerprints: known, now: () => Date.parse('2026-11-22T19:00:00Z'), secrets: [customSecret],
  });
  assert.equal(r2.newFindings.length, 0, 'replayed incidents must yield 0 new findings');
  assert.equal(r2.summary.deduplicatedCount, 2);

  const p2 = persistDailyInvestigationReport(stateDir, r2, { now: () => Date.parse('2026-11-22T19:00:00Z') });
  assert.equal(p2.newFingerprints.length, 0, 'persisted replay must produce 0 new fingerprints');
  assert.equal(p2.duplicateFingerprints.length, 2);
  assert.equal(p2.totalUniqueFindings, 2, 'daily JSON on disk must contain 0 duplicate entries');
  assert.equal(JSON.parse(readFileSync(p2.reportPath, 'utf8')).findings.length, 2);

  // Explicit opt-in writeIssues creates dedupe-marker issues once and 0 on replay.
  const created = [];
  const gh = {
    listIssues: async () => created.map(c => ({ body: c.body })),
    createIssue: async payload => { created.push(payload); return { number: 700 + created.length }; },
  };
  const w1 = await investigateIncidents({ incidents: batch1, repo: 'acme/app', date: '2026-11-22', writeIssues: true, gh, secrets: [customSecret] });
  assert.equal(w1.readOnly, false);
  assert.equal(w1.createdIssues.length, 2);
  assert.ok(created.every(c => c.body.includes(INVESTIGATOR_MARKER_PREFIX) && !c.body.includes(secretToken)));
  const w2 = await investigateIncidents({ incidents: batch2, repo: 'acme/app', date: '2026-11-22', writeIssues: true, gh, secrets: [customSecret] });
  assert.equal(w2.createdIssues.length, 0, 'marker check prevents duplicate GitHub issues on replay');

  // Symlink guard rejects symlinked daily report target.
  const symState = makeTempDir(t, 'pdd-investigator-sym-');
  mkdirSync(join(symState, 'investigations'), { recursive: true });
  const outside = join(makeTempDir(t, 'pdd-inv-outside-'), 'target.json');
  writeFileSync(outside, '{}');
  symlinkSync(outside, join(symState, 'investigations', '2026-11-22.json'));
  assert.throws(() => persistDailyInvestigationReport(symState, r1), /unsafe_state_path|symlink/i);
});

test('funnel-cohort: honest stage-by-stage funnel % separates dispositions and never mixes not-run into pass counts', () => {
  assert.equal(metricsModel.computeStageFunnel, computeStageFunnel);
  assert.equal(metricsModel.resolveStandupWindow, resolveStandupWindow);
  assert.equal(metricsModel.evaluateMatureCohort, evaluateMatureCohort);

  const funnel = computeStageFunnel([
    // 1. Auto-merged (clean)
    { repo: 'acme/app', issue: 1, status: 'merged', pr: 101, gates: { runtime: 'pass', suite: 'pass', review: 'pass', ci: 'green' } },
    // 2. Auto-merged (regressed)
    { repo: 'acme/app', issue: 2, status: 'merged', pr: 102, reopened: true, gates: { runtime: 'not-run', suite: 'pass', review: 'pass', ci: 'pass' } },
    // 3. Human-merged (distinct from autoMerged)
    { repo: 'acme/app', issue: 3, status: 'merged', mergeSource: 'human', pr: 103, gates: { runtime: 'na', suite: 'pass', review: 'pass', ci: 'pass' } },
    // 4. Would-merge (PR created, NOT merged!)
    { repo: 'acme/app', issue: 4, status: 'would-merge', pr: 104, gates: { runtime: 'fail', suite: 'pass', review: 'pass', ci: 'pass' } },
    // 5. Claimed, no PR yet (dropped/failed before PR)
    { repo: 'acme/app', issue: 5, status: 'ended', pr: null, gates: { runtime: 'not-run', suite: 'fail', review: 'not-run', ci: 'na' } },
    // Duplicate older entry for issue #1 must deduplicate cleanly by stable ID without inflating counts!
    { repo: 'acme/app', issue: 1, status: 'running', at: '2026-11-21T01:00:00Z' },
    // 6. Eligible but missing capacity (unclaimed)
    { repo: 'acme/app', issue: 6, disposition: 'missing-capacity', eligible: true },
    // 7-8. Real holds (ineligible)
    { repo: 'acme/app', issue: 7, reasonCode: 'protected-path' },
    { repo: 'acme/app', issue: 8, reasonCode: 'human_decision' },
  ]);

  assert.equal(funnel.counts.considered, 8);
  assert.equal(funnel.counts.eligible, 6);
  assert.equal(funnel.counts.claimed, 5);
  assert.equal(funnel.counts.pr, 4);
  assert.equal(funnel.counts.merged, 3, 'wouldMerge must NEVER inflate merged');
  assert.equal(funnel.counts.autoMerged, 2);
  assert.equal(funnel.counts.humanMerged, 1);
  assert.equal(funnel.counts.wouldMerge, 1);
  assert.equal(funnel.counts.realHold, 2);
  assert.equal(funnel.counts.missingCapacity, 1);
  assert.equal(funnel.counts.regressed, 1);

  assert.equal(funnel.rates.eligiblePct, 75);            // 6/8
  assert.equal(funnel.rates.takenPct, 83.3);             // 5/6 eligible
  assert.equal(funnel.rates.takenOfConsideredPct, 62.5); // 5/8 considered
  assert.equal(funnel.rates.prPct, 80);                  // 4/5 claimed
  assert.equal(funnel.rates.mergedPct, 75);              // 3/4 PRs
  assert.equal(funnel.rates.autoMergedPct, 50);          // 2/4 PRs
  assert.equal(funnel.rates.regressionPct, 33.3);        // 1/3 merged

  // Gate pass stats NEVER mix `not-run` / `na` into `passed` or `applicable`!
  assert.deepEqual(funnel.gateStats.runtime, { passed: 1, failed: 1, running: 0, notRun: 6, applicable: 2, passPct: 50 });
  assert.deepEqual(funnel.gateStats.vectors, { passed: 0, failed: 0, running: 0, notRun: 8, applicable: 0, passPct: null });
  assert.deepEqual(funnel.gateStats.suite, { passed: 4, failed: 1, running: 0, notRun: 3, applicable: 5, passPct: 80 });
});

test('funnel-cohort: DST-safe America/Los_Angeles 09:00-09:00 standup windows across spring-forward (23h) and fall-back (25h)', () => {
  // Spring-forward: 2026-03-08 (US Pacific clocks jump 02:00 PST -> 03:00 PDT => exact 23h standup window!)
  const spring = resolveStandupWindow({ date: '2026-03-08', timezone: 'America/Los_Angeles' });
  assert.equal(spring.startAt, '2026-03-07T17:00:00.000Z'); // 09:00 PST (UTC-8)
  assert.equal(spring.endAt, '2026-03-08T15:59:59.999Z');   // 08:59:59.999 PDT (UTC-7)
  assert.equal(spring.durationHours, 23);

  // Fall-back: 2026-11-01 (US Pacific clocks repeat 01:00-02:00 PDT -> PST => exact 25h standup window!)
  const fall = resolveStandupWindow({ date: '2026-11-01', timezone: 'America/Los_Angeles' });
  assert.equal(fall.startAt, '2026-10-31T16:00:00.000Z');   // 09:00 PDT (UTC-7)
  assert.equal(fall.endAt, '2026-11-01T16:59:59.999Z');     // 08:59:59.999 PST (UTC-8)
  assert.equal(fall.durationHours, 25);

  // Standard summer (PDT) & winter (PST) days are exact 24h with dynamic UTC offsets.
  const summer = resolveStandupWindow({ date: '2026-07-15', timezone: 'America/Los_Angeles' });
  assert.equal(summer.startAt, '2026-07-14T16:00:00.000Z');
  assert.equal(summer.durationHours, 24);
  const winter = resolveStandupWindow({ date: '2026-01-15', timezone: 'America/Los_Angeles' });
  assert.equal(winter.startAt, '2026-01-14T17:00:00.000Z');
  assert.equal(winter.durationHours, 24);

  // Live window on spring-forward morning at 08:30 PDT (15:30Z) caps at `now`, while 09:30 PDT (16:30Z) caps at 08:59:59.999 PDT.
  const beforeNine = resolveStandupWindow({ now: '2026-03-08T15:30:00Z', timezone: 'America/Los_Angeles' });
  assert.equal(beforeNine.startAt, '2026-03-07T17:00:00.000Z');
  assert.equal(beforeNine.endAt, '2026-03-08T15:30:00.000Z');
  const afterNine = resolveStandupWindow({ now: '2026-03-08T16:30:00Z', timezone: 'America/Los_Angeles' });
  assert.equal(afterNine.endAt, '2026-03-08T15:59:59.999Z');
  assert.equal((localAnchorUtcMs(2026, 3, 8, 9, 'America/Los_Angeles') - localAnchorUtcMs(2026, 3, 7, 9, 'America/Los_Angeles')) / 3_600_000, 23);
});

test('funnel-cohort: mature 7-day cohort tracks GraphQL REOPENED_EVENT, reverts, and follow-up defects separately from immature merges', () => {
  const now = '2026-11-22T12:00:00Z';
  const graphqlPayload = {
    data: {
      r0: {
        nameWithOwner: 'acme/app',
        issues: {
          nodes: [
            { number: 12, timelineItems: { nodes: [{ __typename: 'ReopenedEvent', createdAt: '2026-11-16T05:00:00Z', actor: { login: 'dev' } }] } },
            // Pre-merge reopen (Nov 5) on issue #14 merged Nov 10 -> MUST NOT count as post-merge regression!
            { number: 14, timelineItems: { nodes: [{ __typename: 'ReopenedEvent', createdAt: '2026-11-05T05:00:00Z', actor: { login: 'dev' } }] } },
          ],
        },
        closedIssues: { nodes: [] },
      },
    },
  };
  const reopenedEvents = extractGraphQlReopenedEvents(graphqlPayload);
  assert.equal(reopenedEvents.length, 2);

  const cohort = evaluateMatureCohort([
    { repo: 'acme/app', issue: 11, pr: 211, mergedAt: '2026-11-12T12:00:00Z' }, // 10d -> mature-clean
    { repo: 'acme/app', issue: 12, pr: 212, mergedAt: '2026-11-13T12:00:00Z' }, // 9d -> mature-regressed (REOPENED_EVENT Nov 16)
    { repo: 'acme/app', issue: 13, pr: 213, mergedAt: '2026-11-14T12:00:00Z' }, // 8d -> mature-regressed (revert + follow-up #401)
    { repo: 'acme/app', issue: 14, pr: 214, mergedAt: '2026-11-10T12:00:00Z' }, // 12d -> mature-clean (pre-merge reopen ignored!)
    { repo: 'acme/app', issue: 15, pr: 215, mergedAt: '2026-11-20T12:00:00Z' }, // 2d -> immature-clean (must NOT dilute mature %)
    { repo: 'acme/app', issue: 16, pr: 216, mergedAt: '2026-11-21T12:00:00Z', reverted: true, revertedAt: '2026-11-21T18:00:00Z' }, // 1d -> immature-regressed
  ], {
    now,
    maturityDays: 7,
    reopenedEvents,
    reverts: [{ repo: 'acme/app', pr: 213, revertedAt: '2026-11-15T09:00:00Z' }],
    followUpIssues: [{ repo: 'acme/app', targetPr: 213, issue: 401, createdAt: '2026-11-15T10:00:00Z' }],
  });

  assert.equal(cohort.maturityDays, 7);
  assert.equal(cohort.mature.total, 4);
  assert.equal(cohort.mature.clean, 2);
  assert.equal(cohort.mature.regressed, 2);
  assert.equal(cohort.mature.regressionPct, 50, 'immature merges must not dilute mature 7-day regression rate');
  assert.equal(cohort.mature.reopened, 1);
  assert.equal(cohort.mature.reverted, 1);
  assert.equal(cohort.mature.followUpDefects, 1);

  assert.equal(cohort.immature.total, 2);
  assert.equal(cohort.immature.clean, 1);
  assert.equal(cohort.immature.regressed, 1);
  assert.equal(cohort.immature.earlyRegressionPct, 50);

  const pr212 = cohort.mature.items.find(x => x.pr === 212);
  assert.equal(pr212.cohortStatus, 'mature-regressed');
  assert.equal(pr212.reopenedAt, '2026-11-16T05:00:00.000Z');
  const pr213 = cohort.mature.items.find(x => x.pr === 213);
  assert.deepEqual(pr213.followUpIssues, [401]);
  assert.equal(pr213.revertedAt, '2026-11-15T09:00:00.000Z');
  const pr214 = cohort.mature.items.find(x => x.pr === 214);
  assert.equal(pr214.cohortStatus, 'mature-clean');
  assert.equal(pr214.reopened, false);

  // Exact 7-day maturity boundary: 7d exactly is mature; 7d - 1ms is immature.
  const exactBoundary = evaluateMatureCohort([
    { repo: 'acme/app', issue: 31, pr: 301, mergedAt: '2026-11-15T12:00:00.000Z' },
    { repo: 'acme/app', issue: 32, pr: 302, mergedAt: '2026-11-15T12:00:00.001Z' },
  ], { now, maturityDays: 7 });
  assert.equal(exactBoundary.mature.total, 1);
  assert.equal(exactBoundary.mature.items[0].pr, 301);
  assert.equal(exactBoundary.immature.total, 1);
  assert.equal(exactBoundary.immature.items[0].pr, 302);
});
