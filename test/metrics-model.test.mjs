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

test('formatMetricsText renders Overview, Per-Repo, Stages, Skills, Full, and Recording OFF note without personal targets', () => {
  const baseInput = {
    now: '2026-11-17T18:00:00Z',
    timezone: 'America/Los_Angeles',
    repos: ['promptdriven/pdd', 'promptdriven/pocket'],
    openIssues: { 'promptdriven/pdd': 14, 'promptdriven/pocket': 8 },
    runs: [
      { repo: 'promptdriven/pdd', issue: 1, skill: 'small-change', at: '2026-11-17T12:00:00Z', status: 'would-merge', pr: 10, durationMinutes: 9, gates: { suite: 'pass', review: 'pass', ci: 'pass' } },
      { repo: 'promptdriven/pocket', issue: 2, skill: 'bug', at: '2026-11-17T14:00:00Z', status: 'running', pr: null, gates: {} },
    ],
  };

  const overviewText = formatMetricsText(calculateAutopilotMetrics(baseInput));
  assert.match(overviewText, /PDD Autopilot Metrics · Unified \(2 repos\)/);
  assert.match(overviewText, /Window\s+Open\s+Taken\s+PR Created\s+M\/WM \(Conv%\)/);
  assert.match(overviewText, /Last 24h\s+22\s+2\s+1\s+1 \(50\.0%\)/);
  assert.doesNotMatch(overviewText, /Targets|Merged or would-merge\/day/i);

  const reposText = formatMetricsText(calculateAutopilotMetrics({ ...baseInput, byRepo: true }));
  assert.match(reposText, /promptdriven\/pdd/);
  assert.match(reposText, /promptdriven\/pocket/);
  assert.match(reposText, /Total\s+22\s+2\s+1\s+1 \(50\.0%\)/);

  const stagesText = formatMetricsText(calculateAutopilotMetrics({ ...baseInput, view: 'stages' }));
  assert.match(stagesText, /Taken\s+PR\s+Runtime\s+Vectors\s+Formal\s+Suite\s+Review\s+CI\s+M\/WM\s+Reopen/);
  assert.match(stagesText, /Non-merged \(1\): 1 running/);

  const skillsText = formatMetricsText(calculateAutopilotMetrics({ ...baseInput, view: 'skills' }));
  assert.match(skillsText, /small-change\s+1\s+1\s+1 \(100\.0%\)\s+9m/);
  assert.match(skillsText, /feature\s+0\s+0\s+0 \(n\/a\)\s+n\/a/);

  const pausedText = formatMetricsText(calculateAutopilotMetrics({
    ...baseInput,
    view: 'full',
    recording: { enabled: false },
  }));
  assert.match(pausedText, /Recording: OFF/);
  assert.match(pausedText, /Autopilot Stages/);
  assert.match(pausedText, /Work Mix/);

  const html = renderMetricsHtml(calculateAutopilotMetrics({ ...baseInput, view: 'full' }));
  assert.match(html, /<!doctype html>/i);
  assert.match(html, /1\. Overview/);
  assert.match(html, /2\. Autopilot Stages/);
  assert.match(html, /3\. Work Mix by Skill/);
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
