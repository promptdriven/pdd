import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  GATES,
  SKILLS,
  applyMetricsToggle,
  calculateAutopilotMetrics,
  renderMetricsHtml,
} from '../src/metrics-model.mjs';

function mulberry32(seed) {
  let a = seed >>> 0;
  return function next() {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

test('formal invariants: funnel bounds, cross-view reconciliation, skill partition, and gate denominators hold across 200 generated worlds', () => {
  const rng = mulberry32(0x5eed2026);
  const reposPool = ['acme/api', 'acme/web', 'acme/cli'];
  const statuses = ['merged', 'would-merge', 'running', 'needs-person', 'ended', 'released'];
  const gateVals = ['pass', 'fail', 'not-run', 'na', null];
  const nowMs = Date.parse('2026-11-18T18:00:00Z');

  for (let trial = 0; trial < 200; trial++) {
    const runCount = Math.floor(rng() * 25);
    const runs = [];
    for (let i = 0; i < runCount; i++) {
      const repo = reposPool[Math.floor(rng() * reposPool.length)];
      const issue = 1 + Math.floor(rng() * 12);
      const offsetHours = Math.floor(rng() * 96);
      const atMs = nowMs - offsetHours * 3_600_000;
      const dur = 2 + Math.floor(rng() * 45);
      const startMs = atMs - dur * 60_000;
      const status = statuses[Math.floor(rng() * statuses.length)];
      const skill = rng() < 0.75 ? SKILLS[Math.floor(rng() * SKILLS.length)] : undefined;
      const gates = {};
      for (const g of GATES) gates[g] = gateVals[Math.floor(rng() * gateVals.length)];
      runs.push({
        repo,
        issue,
        skill,
        startedAt: new Date(startMs).toISOString(),
        at: new Date(atMs).toISOString(),
        status,
        pr: rng() < 0.7 ? 100 + i : null,
        gates,
        reopened: rng() < 0.15,
        durationMinutes: rng() < 0.85 ? dur : null,
        pathsOnlyD: rng() < 0.2,
        promptChanged: rng() < 0.5,
      });
    }

    const report = calculateAutopilotMetrics({
      runs,
      repos: reposPool.slice(0, 1 + (trial % 3)),
      openIssues: trial % 4 === 0 ? null : { 'acme/api': 10, 'acme/web': 4, 'acme/cli': 2 },
      view: 'full',
      byRepo: true,
      date: trial % 5 === 0 ? '2026-11-17' : null,
      timezone: 'America/Los_Angeles',
      now: new Date(nowMs).toISOString(),
    });

    for (const w of report.overview.windows) {
      assert.ok(w.taken >= 0);
      assert.ok(w.prCreated >= 0 && w.prCreated <= w.taken, `prCreated <= taken in trial ${trial}`);
      assert.ok(w.merged >= 0 && w.merged <= w.prCreated, `merged <= prCreated in trial ${trial}`);
      assert.ok(w.mwm >= 0 && w.mwm <= w.taken, `mwm <= taken in trial ${trial}`);
      assert.ok(w.regressions >= 0 && w.regressions <= w.merged, `regressions <= merged in trial ${trial}`);
      if (w.pool !== null) {
        assert.ok(w.pool >= w.taken, `pool >= taken in trial ${trial}`);
      }
    }

    for (const pw of report.overview.perRepoWindows) {
      const sumTaken = pw.rows.reduce((acc, r) => acc + r.taken, 0);
      const sumPr = pw.rows.reduce((acc, r) => acc + r.prCreated, 0);
      const sumMerged = pw.rows.reduce((acc, r) => acc + r.merged, 0);
      const sumMwm = pw.rows.reduce((acc, r) => acc + r.mwm, 0);
      const sumReg = pw.rows.reduce((acc, r) => acc + r.regressions, 0);
      assert.equal(sumTaken, pw.total.taken);
      assert.equal(sumPr, pw.total.prCreated);
      assert.equal(sumMerged, pw.total.merged);
      assert.equal(sumMwm, pw.total.mwm);
      assert.equal(sumReg, pw.total.regressions);
      if (pw.total.pool !== null) {
        assert.equal(pw.rows.reduce((acc, r) => acc + r.pool, 0), pw.total.pool);
      }
    }

    const primaryOverview = report.overview.windows.at(-1);
    assert.equal(report.stages.taken, primaryOverview.taken);
    assert.equal(report.stages.pr, primaryOverview.prCreated);
    assert.equal(report.stages.merged, primaryOverview.merged);
    assert.equal(report.stages.mwm, primaryOverview.mwm);
    assert.equal(report.stages.regressions.total, primaryOverview.regressions);
    assert.equal(report.skills.total.taken, primaryOverview.taken);
    assert.equal(report.skills.total.prCreated, primaryOverview.prCreated);
    assert.equal(report.skills.total.merged, primaryOverview.merged);
    assert.equal(report.skills.total.mwm, primaryOverview.mwm);

    assert.equal(
      report.skills.rows.reduce((acc, r) => acc + r.taken, 0),
      report.skills.total.taken,
    );
    assert.equal(
      report.skills.rows.reduce((acc, r) => acc + r.merged, 0),
      report.skills.total.merged,
    );
    assert.equal(
      report.skills.rows.reduce((acc, r) => acc + r.mwm, 0),
      report.skills.total.mwm,
    );

    assert.equal(report.stages.beforePr.total + report.stages.pr, report.stages.taken);
    assert.equal(report.stages.merged + report.stages.unmergedPrs.total, report.stages.pr);
    assert.equal(
      report.stages.beforePr.total + report.stages.unmergedPrs.total + report.stages.merged,
      report.stages.taken,
    );
    assert.equal(
      report.stages.beforePr.breakdown.reduce((acc, b) => acc + b.count, 0),
      report.stages.beforePr.total,
    );
    assert.equal(
      report.stages.unmergedPrs.breakdown.reduce((acc, b) => acc + b.count, 0),
      report.stages.unmergedPrs.total,
    );
    for (const key of ['suite', 'review', 'ci', 'e2e']) {
      const cell = report.stages.prGates[key];
      assert.equal(cell.total, report.stages.pr);
      assert.ok(cell.passed >= 0 && cell.passed <= cell.total);
    }

    for (const g of GATES) {
      const cell = report.stages.gates[g];
      assert.ok(cell.passed >= 0 && cell.passed <= cell.applicable);
      assert.ok(cell.applicable <= report.stages.taken);
      assert.equal(cell.display === '-', cell.applicable === 0);
    }

    assert.equal(report.stages.mwm + report.stages.nonMerged.total, report.stages.taken);
    assert.equal(
      report.stages.nonMerged.breakdown.reduce((acc, b) => acc + b.count, 0),
      report.stages.nonMerged.total,
    );
    assert.ok(report.stages.reopen >= 0 && report.stages.reopen <= report.stages.mwm);
  }
});

test('formal invariants: on/off toggle excludes turned-off repos in unified rollups while preserving pre-pause history under explicit --repo', () => {
  let cfg = applyMetricsToggle(null, { action: 'off', at: '2026-11-17T10:00:00Z' });
  cfg = applyMetricsToggle(cfg, { action: 'on', at: '2026-11-17T12:00:00Z' });
  cfg = applyMetricsToggle(cfg, { action: 'off', repo: 'acme/web', at: '2026-11-17T13:00:00Z' });

  const runs = [
    { repo: 'acme/api', issue: 1, startedAt: '2026-11-17T09:00:00Z', at: '2026-11-17T09:30:00Z', status: 'merged', pr: 11 },
    { repo: 'acme/api', issue: 2, startedAt: '2026-11-17T11:00:00Z', at: '2026-11-17T11:20:00Z', status: 'merged', pr: 12 },
    { repo: 'acme/api', issue: 3, startedAt: '2026-11-17T12:30:00Z', at: '2026-11-17T12:45:00Z', status: 'merged', pr: 13 },
    { repo: 'acme/web', issue: 4, startedAt: '2026-11-17T12:30:00Z', at: '2026-11-17T12:50:00Z', status: 'merged', pr: 14 },
    { repo: 'acme/web', issue: 5, startedAt: '2026-11-17T13:30:00Z', at: '2026-11-17T13:50:00Z', status: 'merged', pr: 15 },
  ];

  // Unified rollup excludes explicitly turned-off acme/web completely; acme/api #1 and #3 survive (#2 excluded by global pause).
  const unified = calculateAutopilotMetrics({
    runs,
    repos: ['acme/api', 'acme/web'],
    openIssues: { 'acme/api': 1, 'acme/web': 1 },
    now: '2026-11-17T15:00:00Z',
    timezone: 'UTC',
    recording: cfg,
  });
  assert.deepEqual(unified.repos, ['acme/api']);
  assert.equal(unified.scopeLabel, 'api');
  assert.equal(unified.openNow, 1);
  assert.equal(unified.overview.windows[0].taken, 2);
  assert.equal(unified.overview.windows[0].merged, 2);

  // Explicit --repo acme/web still shows pre-pause #4 while excluding paused #5.
  const webOnly = calculateAutopilotMetrics({
    runs,
    repos: ['acme/api', 'acme/web'],
    openIssues: { 'acme/api': 1, 'acme/web': 1 },
    repoFilter: 'acme/web',
    now: '2026-11-17T15:00:00Z',
    timezone: 'UTC',
    recording: cfg,
  });
  assert.deepEqual(webOnly.repos, ['acme/web']);
  assert.equal(webOnly.recording.enabled, false);
  assert.equal(webOnly.overview.windows[0].taken, 1);
  assert.equal(webOnly.overview.windows[0].merged, 1);
});

test('formal HTML escaping prevents unescaped markup in rendered HTML', () => {
  const report = calculateAutopilotMetrics({
    runs: [],
    repos: ['acme/safe-repo'],
    openIssues: { 'acme/safe-repo': 3 },
    now: '2026-11-17T15:00:00Z',
    timezone: 'UTC',
  });
  report.displayDate = '<script>alert("xss")</script>';
  const html = renderMetricsHtml(report);
  assert.doesNotMatch(html, /<script>alert/);
  assert.match(html, /&lt;script&gt;alert\(&quot;xss&quot;\)&lt;\/script&gt;/);
});
