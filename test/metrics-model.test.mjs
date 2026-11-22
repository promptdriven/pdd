import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  applyMetricsToggle,
  calculateAutopilotMetrics,
  formatMetricsText,
  isMetricsEnabled,
  normalizeSkill,
  renderMetricsHtml,
} from '../src/metrics-model.mjs';

test('Monday 00:00 local week refresh excludes prior Sunday and keeps Last 24h rolling', () => {
  // Monday 2026-11-16 02:00:00 PST = 2026-11-16T10:00:00Z
  const report = calculateAutopilotMetrics({
    now: '2026-11-16T10:00:00Z',
    timezone: 'America/Los_Angeles',
    repos: ['promptdriven/pdd'],
    openIssues: { 'promptdriven/pdd': 12 },
    runs: [
      // Sunday 2026-11-15 22:00 PST (2026-11-16T06:00:00Z): inside Last 24h, outside Week (Mon-Sun)!
      { repo: 'promptdriven/pdd', issue: 1, at: '2026-11-16T06:00:00Z', status: 'merged', pr: 10 },
      // Monday 2026-11-16 01:00 PST (2026-11-16T09:00:00Z): inside both Last 24h and Week (Mon-Sun)!
      { repo: 'promptdriven/pdd', issue: 2, at: '2026-11-16T09:00:00Z', status: 'would-merge', pr: 11 },
    ],
  });

  const [last24h, week] = report.overview.windows;
  assert.equal(last24h.label, 'Last 24h');
  assert.equal(last24h.taken, 2);
  assert.equal(last24h.mwmDisplay, '2 (100.0%)');

  assert.equal(week.label, 'Week (Mon-Sun)');
  assert.equal(week.taken, 1);
  assert.equal(week.mwmDisplay, '1 (100.0%)');
});

test('deduplicates retried issues within a window and expands grouped companion issues', () => {
  const report = calculateAutopilotMetrics({
    now: '2026-11-17T18:00:00Z',
    timezone: 'UTC',
    repos: ['promptdriven/pdd'],
    openIssues: { 'promptdriven/pdd': 5 },
    runs: [
      // Retry 1 failed, Retry 2 merged -> counted once as merged
      { repo: 'promptdriven/pdd', issue: 40, at: '2026-11-17T10:00:00Z', status: 'ended', pr: null },
      { repo: 'promptdriven/pdd', issue: 40, at: '2026-11-17T12:00:00Z', status: 'merged', pr: 99, durationMinutes: 15 },
      // Grouped run solving #41 and #42 together
      { repo: 'promptdriven/pdd', issue: 41, issues: [41, 42], at: '2026-11-17T14:00:00Z', status: 'would-merge', pr: 100, durationMinutes: 20 },
    ],
  });

  const last24h = report.overview.windows[0];
  assert.equal(last24h.taken, 3);
  assert.equal(last24h.prCreated, 3);
  assert.equal(last24h.mwm, 3);
  assert.equal(last24h.mwmDisplay, '3 (100.0%)');
});

test('formatMetricsText renders v2 Overview, Per-Repo, Funnel & Gates, Skills, Full, Target row, and Recording OFF note', () => {
  const baseInput = {
    now: '2026-11-17T18:00:00Z',
    timezone: 'America/Los_Angeles',
    repos: ['promptdriven/pdd', 'promptdriven/pocket'],
    openIssues: { 'promptdriven/pdd': 14, 'promptdriven/pocket': 8 },
    prStates: [
      { repo: 'promptdriven/pdd', pr: 10, merged: true, mergedAt: '2026-11-17T13:00:00Z', state: 'MERGED' },
    ],
    runs: [
      { repo: 'promptdriven/pdd', issue: 1, skill: 'small-change', at: '2026-11-17T12:00:00Z', status: 'would-merge', pr: 10, durationMinutes: 9, gates: { suite: 'pass', review: 'pass', ci: 'pass' } },
      { repo: 'promptdriven/pocket', issue: 2, skill: 'bug', at: '2026-11-17T14:00:00Z', status: 'running', pr: null, gates: {} },
    ],
  };

  const overviewText = formatMetricsText(calculateAutopilotMetrics(baseInput));
  assert.match(overviewText, /PDD Autopilot Metrics · pdd \+ pocket · Tue, Nov 17 · Open now: 22/);
  assert.match(overviewText, /Window\s+Pool\s+Taken\s+PRs\s+Merged \(Conv%\)\s+Regressions/);
  assert.match(overviewText, /Last 24h\s+23\s+2\s+1\s+1 \(50\.0%\)\s+0 \(0\.0%\)/);
  assert.match(overviewText, /Target \(Nov\)\s+-\s+-\s+-\s+>=90%\s+0\.0%/);
  assert.match(overviewText, /Funnel & Gates · Week \(Mon-Sun\) · 2 Taken -> 1 PRs -> 1 Merged/);
  assert.match(overviewText, /- Before PR \(1\): 1 running/);
  assert.match(overviewText, /- Unmerged PRs \(0\): none/);
  assert.match(overviewText, /- PR Gates \(of 1 PR\): Suite 1\/1 · Review 1\/1 · CI 1\/1/);
  assert.match(overviewText, /- Prompt Checks \(of 0 prompt PRs\): none/);
  assert.match(overviewText, /- Regressions \(0\): 0 reopened · 0 reverted · 0 regression issues/);

  const reposText = formatMetricsText(calculateAutopilotMetrics({ ...baseInput, byRepo: true }));
  assert.match(reposText, /Per Repo · pdd \+ pocket/);
  assert.match(reposText, /promptdriven\/pdd/);
  assert.match(reposText, /promptdriven\/pocket/);
  assert.match(reposText, /Total\s+23\s+2\s+1\s+1 \(50\.0%\)\s+0 \(0\.0%\)/);

  const stagesText = formatMetricsText(calculateAutopilotMetrics({ ...baseInput, view: 'stages' }));
  assert.match(stagesText, /Funnel & Gates · Week \(Mon-Sun\) · 2 Taken -> 1 PRs -> 1 Merged/);
  assert.match(stagesText, /- Before PR \(1\): 1 running/);

  const skillsText = formatMetricsText(calculateAutopilotMetrics({ ...baseInput, view: 'skills' }));
  assert.match(skillsText, /Skill\s+Taken\s+PRs\s+Merged \(Conv%\)\s+Median Time/);
  assert.match(skillsText, /small-change\s+1\s+1\s+1 \(100\.0%\)\s+9m/);
  assert.match(skillsText, /feature\s+0\s+0\s+0 \(n\/a\)\s+n\/a/);

  const pausedText = formatMetricsText(calculateAutopilotMetrics({
    ...baseInput,
    view: 'full',
    recording: { enabled: false },
  }));
  assert.match(pausedText, /Recording: OFF/);
  assert.match(pausedText, /Funnel & Gates/);
  assert.match(pausedText, /Work Mix/);

  const html = renderMetricsHtml(calculateAutopilotMetrics({ ...baseInput, view: 'full' }));
  assert.match(html, /<!doctype html>/i);
  assert.match(html, /Open now: 22/);
  assert.match(html, /1\. Overview/);
  assert.match(html, /Target \(Nov\)/);
  assert.match(html, /2\. Funnel &amp; Gates/);
  assert.match(html, /3\. Work Mix by Skill/);
});

test('v2 scorecard reconciles Pool, E2E, Prompt Checks, Regressions, turned-off repo exclusion, and colliding repo names (#3530)', () => {
  const report = calculateAutopilotMetrics({
    now: '2026-11-19T18:00:00Z',
    timezone: 'America/Los_Angeles',
    repos: ['promptdriven/pdd', 'promptdriven/pocket', 'Serhan-Asad/pdd-autopilot-sandbox'],
    openIssues: {
      'promptdriven/pdd': 2,
      'promptdriven/pocket': 1,
      'Serhan-Asad/pdd-autopilot-sandbox': 99,
    },
    openIssueNumbers: [
      { repo: 'promptdriven/pdd', issues: [10, 11] },
      { repo: 'promptdriven/pocket', issues: [20] },
      { repo: 'Serhan-Asad/pdd-autopilot-sandbox', issues: [901, 902] },
    ],
    closedIssues: [
      { repo: 'promptdriven/pdd', issue: 12, closedAt: '2026-11-18T12:00:00Z' },
    ],
    prStates: [
      { repo: 'promptdriven/pdd', pr: 112, merged: true, mergedAt: '2026-11-18T12:00:00Z', state: 'MERGED' },
      { repo: 'promptdriven/pdd', pr: 110, merged: false, state: 'OPEN', isDraft: true },
    ],
    regressions: [
      { repo: 'promptdriven/pdd', pr: 112, issue: 12, reopened: false, reverted: false, regressionIssues: [3528] },
    ],
    recording: {
      enabled: true,
      repos: { 'serhan-asad/pdd-autopilot-sandbox': false },
      targets: { convMinPct: 92.5, maxRegressionPct: 1, label: 'Nov' },
    },
    runs: [
      {
        repo: 'promptdriven/pdd',
        issue: 12,
        at: '2026-11-18T11:30:00Z',
        status: 'would-merge',
        pr: 112,
        promptChanged: true,
        gates: { runtime: 'pass', vectors: 'pass', formal: 'proved', suite: 'pass', review: 'pass', ci: 'green', e2e: 'pass' },
        gateCounts: { runtime: { passed: 6, total: 6 }, vectors: { passed: 20, total: 20 }, formal: { passed: 4, total: 4 } },
      },
      {
        repo: 'promptdriven/pdd',
        issue: 10,
        at: '2026-11-19T14:00:00Z',
        status: 'would-merge',
        pr: 110,
        gates: { suite: 'pass', review: 'pass', ci: 'red', e2e: 'fail' },
      },
      {
        repo: 'Serhan-Asad/pdd-autopilot-sandbox',
        issue: 901,
        at: '2026-11-19T15:00:00Z',
        status: 'merged',
        pr: 999,
      },
    ],
  });

  assert.equal(report.scopeLabel, 'pdd + pocket');
  assert.deepEqual(report.repos, ['promptdriven/pdd', 'promptdriven/pocket']);
  assert.equal(report.openNow, 3);
  const week = report.overview.windows[1];
  assert.equal(week.pool, 4); // {10, 11, 12} on pdd + {20} on pocket
  assert.equal(week.taken, 2);
  assert.equal(week.prCreated, 2);
  assert.equal(week.merged, 1);
  assert.equal(week.regressions, 1);
  assert.equal(week.regressionsDisplay, '1 (100.0%)');
  assert.equal(report.overview.target.convDisplay, '>=92.5%');
  assert.equal(report.overview.target.regressionDisplay, '1.0%');
  assert.equal(report.stages.prGates.summary, 'PR Gates (of 2 PRs): Suite 2/2 · Review 2/2 · CI 1/2 · E2E 1/2');
  assert.equal(report.stages.promptChecks.summary, 'Prompt Checks (of 1 prompt PR): Runtime 1/1 · Vectors 1/1 · Formal 1/1');
  assert.equal(report.stages.unmergedPrs.summary, 'Unmerged PRs (1): 1 failed ci');
  assert.equal(report.stages.regressions.summary, 'Regressions (1): 0 reopened · 0 reverted · 1 regression issue (#3528)');

  // Colliding short names preserve owner/repo
  const colliding = calculateAutopilotMetrics({
    now: '2026-11-19T18:00:00Z',
    repos: ['orgA/app', 'orgB/app', 'orgA/cli'],
    openIssues: { 'orgA/app': 1, 'orgB/app': 2, 'orgA/cli': 3 },
  });
  assert.equal(colliding.scopeLabel, 'orgA/app + cli + orgB/app');
});

test('handles incomplete regression scans honestly, non-retroactive historical --date merges, and HTML conversion pill status (#3530)', () => {
  // 1. Incomplete regression scan: 0 detected on merged > 0 displays "?" and "(scan incomplete)"; >0 displays "1+ (50.0%+)"
  const incompleteZero = calculateAutopilotMetrics({
    now: '2026-11-18T18:00:00Z',
    repos: ['promptdriven/pdd'],
    openIssues: { 'promptdriven/pdd': 2 },
    regressionsComplete: false,
    runs: [
      { repo: 'promptdriven/pdd', issue: 1, at: '2026-11-18T12:00:00Z', status: 'merged', pr: 11 },
    ],
  });
  assert.equal(incompleteZero.regressionsComplete, false);
  assert.equal(incompleteZero.overview.windows[0].regressionsDisplay, '?');
  assert.equal(incompleteZero.overview.windows[0].regressionsPct, null);
  assert.match(incompleteZero.stages.regressions.summary, /\(scan incomplete\)$/);

  const incompletePartial = calculateAutopilotMetrics({
    now: '2026-11-18T18:00:00Z',
    repos: ['promptdriven/pdd'],
    openIssues: { 'promptdriven/pdd': 2 },
    regressionsComplete: false,
    regressions: [{ repo: 'promptdriven/pdd', pr: 11, issue: 1, reverted: true }],
    runs: [
      { repo: 'promptdriven/pdd', issue: 1, at: '2026-11-18T12:00:00Z', status: 'merged', pr: 11 },
      { repo: 'promptdriven/pdd', issue: 2, at: '2026-11-18T13:00:00Z', status: 'merged', pr: 12 },
    ],
  });
  assert.equal(incompletePartial.overview.windows[0].regressionsDisplay, '1+ (50.0%+)');

  // 2. Historical --date does not retroactively count a merge from 2 days later, and future mergedAt > now is rejected
  const runs = [
    { repo: 'promptdriven/pdd', issue: 10, at: '2026-11-16T15:00:00Z', status: 'would-merge', pr: 110 },
    { repo: 'promptdriven/pdd', issue: 11, at: '2026-11-18T10:00:00Z', status: 'would-merge', pr: 111 },
  ];
  const prStates = [
    { repo: 'promptdriven/pdd', pr: 110, merged: true, mergedAt: '2026-11-18T12:00:00Z', state: 'MERGED' },
    { repo: 'promptdriven/pdd', pr: 111, merged: true, mergedAt: '2026-11-20T12:00:00Z', state: 'MERGED' },
  ];
  const day16 = calculateAutopilotMetrics({
    now: '2026-11-18T18:00:00Z',
    date: '2026-11-16',
    timezone: 'UTC',
    repos: ['promptdriven/pdd'],
    runs,
    prStates,
  });
  assert.equal(day16.overview.windows[0].taken, 1);
  assert.equal(day16.overview.windows[0].prCreated, 1);
  assert.equal(day16.overview.windows[0].merged, 0, 'PR merged on Nov 18 must not count as merged on Nov 16');

  const day18 = calculateAutopilotMetrics({
    now: '2026-11-18T18:00:00Z',
    date: '2026-11-18',
    timezone: 'UTC',
    repos: ['promptdriven/pdd'],
    runs,
    prStates,
  });
  assert.equal(day18.overview.windows[0].merged, 1, 'PR #110 merged on Nov 18 counts; future PR #111 (> now) does not');

  // 3. HTML conversion pill uses pill-warn below target and no pill on 0 (n/a)
  const lowConvHtml = renderMetricsHtml(day16);
  assert.match(lowConvHtml, /pill-warn">0 \(0\.0%\)/);
  assert.doesNotMatch(lowConvHtml, /pill-good">0 \(0\.0%\)/);
});

test('normalizeSkill, isMetricsEnabled, and input validation errors', () => {
  assert.equal(normalizeSkill('pdd-small-change'), 'small-change');
  assert.equal(normalizeSkill('BUG'), 'bug');
  assert.equal(normalizeSkill(null, { pathsOnlyD: true }), 'small-change');
  assert.equal(normalizeSkill(null, { title: 'fix crash on empty config' }), 'bug');
  assert.equal(normalizeSkill(null, { title: 'add dashboard export' }), 'feature');

  assert.equal(isMetricsEnabled(null), true);
  const offGlobal = applyMetricsToggle(null, { action: 'off', at: '2026-11-17T00:00:00Z' });
  assert.equal(isMetricsEnabled(offGlobal, 'acme/api'), false);
  const onOneRepo = applyMetricsToggle(offGlobal, { action: 'on', repo: 'acme/api', at: '2026-11-17T01:00:00Z' });
  assert.equal(isMetricsEnabled(onOneRepo, 'acme/api'), true);
  assert.equal(isMetricsEnabled(onOneRepo, 'acme/other'), false);

  assert.throws(() => calculateAutopilotMetrics({ now: '2026-11-17T00:00:00Z', date: '2026-02-30' }), { code: 'invalid-date' });
  assert.throws(() => calculateAutopilotMetrics({ now: '2026-11-17T00:00:00Z', timezone: 'Mars/Phobos' }), { code: 'invalid-timezone' });
  assert.throws(() => calculateAutopilotMetrics({ now: '2026-11-17T00:00:00Z', repoFilter: 'bad-repo' }), { code: 'invalid-repo' });
  assert.throws(() => calculateAutopilotMetrics({ now: '2026-11-17T00:00:00Z', view: 'unknown' }), { code: 'invalid-view' });
  assert.throws(() => calculateAutopilotMetrics({ now: 'not-a-timestamp' }), { code: 'invalid-now' });
  assert.throws(() => applyMetricsToggle(null, { action: 'toggle' }), { code: 'invalid-action' });
  assert.throws(() => applyMetricsToggle(null, { action: 'off', at: 'not-a-timestamp' }), { code: 'invalid-at' });

  // Omitted now/at default deterministically without reading wall clock
  assert.equal(calculateAutopilotMetrics({}).generatedAt, '1970-01-01T00:00:00.000Z');
  assert.equal(applyMetricsToggle(null, { action: 'off' }).updatedAt, '1970-01-01T00:00:00.000Z');

  // Existing canonical repository casing wins when repoFilter uses lowercase
  const canonicalReport = calculateAutopilotMetrics({
    now: '2026-11-17T00:00:00Z',
    repos: ['Serhan-Asad/pdd-autopilot-sandbox'],
    repoFilter: 'serhan-asad/pdd-autopilot-sandbox',
  });
  assert.deepEqual(canonicalReport.repos, ['Serhan-Asad/pdd-autopilot-sandbox']);
  assert.equal(canonicalReport.repoFilter, 'Serhan-Asad/pdd-autopilot-sandbox');
});
