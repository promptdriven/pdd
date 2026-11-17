import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';

import {
  BENCHMARK_WORKLOADS,
  NORTH_STAR_TARGETS,
  assertCleanPublicText,
  computeNorthStarScorecard,
  sanitizePublicData,
  sanitizePublicText,
} from '../scripts/benchmark/scorecard.mjs';
import {
  compareReleaseRuns,
  executeLiveAgentWorkload,
  measureSkillsFootprint,
  parseAgentSessionUsage,
  parseRuntimeCheckOutput,
  runReleaseBenchmark,
  seedBrownfieldTemplate,
} from '../scripts/benchmark/run-release-benchmark.mjs';
import {
  assertGetOnlyMethod,
  buildSpreadDispatchPlan,
  createObserveEtagCache,
  createReadOnlyGithubClient,
  evaluateQualityAndZeroEdit,
  observeRepository,
  runAutopilotObserve,
} from '../scripts/benchmark/run-autopilot-observe.mjs';
import {
  renderBenchmarkReport,
  renderSvgDualBarChart,
} from '../scripts/benchmark/render-benchmark-report.mjs';

test('workloads include small builds (snake, 2048, task-manager) and brownfield multi-module repo sync', () => {
  assert.equal(BENCHMARK_WORKLOADS.snake.tier, 'small');
  assert.equal(BENCHMARK_WORKLOADS['2048'].tier, 'small');
  assert.equal(BENCHMARK_WORKLOADS['task-manager'].tier, 'small');
  assert.equal(BENCHMARK_WORKLOADS['brownfield-repo-sync'].tier, 'brownfield');
  assert.equal(NORTH_STAR_TARGETS.pdd_vs_direct_coding.small_builds.speed_ratio_max, 1.0);
  assert.equal(NORTH_STAR_TARGETS.pdd_vs_direct_coding.large_codebases.feature_iteration_speedup_min_x, 2.0);
  assert.equal(NORTH_STAR_TARGETS.pdd_vs_direct_coding.large_codebases.rework_cost_reduction_min_pct, 50.0);
  assert.deepEqual(
    [NORTH_STAR_TARGETS.autopilot_zero_edit.target_min_pct, NORTH_STAR_TARGETS.autopilot_zero_edit.target_max_pct],
    [90.0, 95.0],
  );
});

test('measureSkillsFootprint counts bundled skill files and bytes', t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-bench-skills-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  mkdirSync(join(root, 'skills/pdd-prompting'), { recursive: true });
  mkdirSync(join(root, 'skills/pdd-product'), { recursive: true });
  writeFileSync(join(root, 'skills/pdd-prompting/SKILL.md'), '# Prompting\nLine two\n');
  writeFileSync(join(root, 'skills/pdd-product/SKILL.md'), '# Product\n');
  writeFileSync(join(root, 'skills/pdd-prompting/.pdd-skill.json'), '{"version":"0.1.34"}');

  const stats = measureSkillsFootprint(root);
  assert.equal(stats.total_files, 2);
  assert.equal(stats.by_skill['pdd-prompting'].files, 1);
  assert.equal(stats.by_skill['pdd-product'].files, 1);
  assert.ok(stats.total_bytes > 20);
});

test('parseRuntimeCheckOutput extracts refusal codes and unreported runtime tokens', () => {
  const lintPass = parseRuntimeCheckOutput('PASS (0 errors)', '', 0);
  assert.equal(lintPass.status, 'pass');
  assert.deepEqual(lintPass.refusal_codes, []);

  const refused = parseRuntimeCheckOutput(
    '1 refused (interface-unapproved) · 1 refused (invalid-simulation-override) · 1 AI call · tokens: unknown',
    '',
    4,
  );
  assert.equal(refused.status, 'fail');
  assert.ok(refused.refusal_codes.includes('interface-unapproved'));
  assert.ok(refused.refusal_codes.includes('invalid-simulation-override'));
  assert.equal(refused.tokens_unreported, true);

  const notRun = parseRuntimeCheckOutput('no verdict · 1 not run (native-only)', '', 5);
  assert.equal(notRun.status, 'not_run');
  assert.ok(notRun.refusal_codes.includes('native-only'));
});

test('parseAgentSessionUsage aggregates token streams, USD cost, and distinct skill reads', t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-bench-session-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const skillFile = join(root, 'skills/pdd-prompting/SKILL.md');
  mkdirSync(join(root, 'skills/pdd-prompting'), { recursive: true });
  writeFileSync(skillFile, 'A'.repeat(500));

  const stream = [
    JSON.stringify({ type: 'turn', usage: { input_tokens: 100_000, cached_input_tokens: 80_000, output_tokens: 2_000 }, read: skillFile }),
    JSON.stringify({ type: 'turn', usage: { input_tokens: 50_000, cached_input_tokens: 40_000, output_tokens: 1_000 }, read: skillFile }),
  ].join('\n');

  const usage = parseAgentSessionUsage(stream);
  assert.equal(usage.input_tokens, 150_000);
  assert.equal(usage.cached_tokens, 120_000);
  assert.equal(usage.uncached_input_tokens, 30_000);
  assert.equal(usage.output_tokens, 3_000);
  assert.equal(usage.skill_files_read, 1);
  assert.equal(usage.skill_total_bytes, 500);
  assert.ok(usage.authoring_usd > 0);
});

test('compareReleaseRuns flags >25% authoring/token regressions and lint-pass test-fail drift as advisory warnings', () => {
  const baseline = {
    version: '0.1.32',
    skills: { total_bytes: 140_000 },
    workloads: [
      {
        workload: '2048',
        prompt_only_seconds: 250,
        post_prompt_pre_test_seconds: 50,
        total_authoring_seconds: 300,
        input_tokens: 1_000_000,
        cached_tokens: 850_000,
        output_tokens: 12_000,
        pdd_lint_status: { status: 'pass', duration_seconds: 3 },
        pdd_test_status: { status: 'pass', duration_seconds: 77, input_tokens: 150_000, output_tokens: 2_000, refusal_codes: [] },
      },
    ],
  };

  const candidate = {
    version: '0.1.34',
    skills: { total_bytes: 200_000 },
    workloads: [
      {
        workload: '2048',
        prompt_only_seconds: 400,
        post_prompt_pre_test_seconds: 220,
        total_authoring_seconds: 620,
        input_tokens: 2_400_000,
        cached_tokens: 2_000_000,
        output_tokens: 28_000,
        pdd_lint_status: { status: 'pass', duration_seconds: 3 },
        pdd_test_status: {
          status: 'fail',
          duration_seconds: 46,
          tokens_unreported: true,
          refusal_codes: ['interface-unapproved', 'invalid-simulation-override'],
        },
      },
    ],
  };

  const cmp = compareReleaseRuns(candidate, baseline, { regressionThresholdPct: 25 });
  const kinds = new Set(cmp.warnings.map(w => w.kind));
  assert.ok(kinds.has('skill_size_bloat'));
  assert.ok(kinds.has('authoring_time_regression'));
  assert.ok(kinds.has('post_prompt_overhead_regression'));
  assert.ok(kinds.has('input_token_regression'));
  assert.ok(kinds.has('output_token_regression'));
  assert.ok(kinds.has('lint_test_parity_mismatch'));
  assert.ok(kinds.has('runtime_verdict_regression'));
  assert.ok(kinds.has('runtime_tokens_unreported'));
});

test('computeNorthStarScorecard evaluates Bar 1 (small + brownfield) and Bar 2 (Autopilot 90-95% zero-edit)', () => {
  const releaseRun = {
    version: '0.1.35',
    workloads: [
      {
        workload: 'snake',
        tier: 'small',
        total_authoring_seconds: 120,
        input_tokens: 90_000,
        cached_tokens: 70_000,
        output_tokens: 4_000,
        authoring_usd: 0.20,
        pdd_test_status: { status: 'pass', duration_seconds: 55, input_tokens: 10_000, output_tokens: 1_000 },
      },
      {
        workload: '2048',
        tier: 'small',
        total_authoring_seconds: 310,
        input_tokens: 800_000,
        cached_tokens: 700_000,
        output_tokens: 10_000,
        authoring_usd: 0.42,
        pdd_test_status: { status: 'pass', duration_seconds: 80, input_tokens: 20_000, output_tokens: 2_000 },
      },
      {
        workload: 'task-manager',
        tier: 'small',
        total_authoring_seconds: 400,
        input_tokens: 900_000,
        cached_tokens: 800_000,
        output_tokens: 12_000,
        authoring_usd: 0.48,
        pdd_test_status: { status: 'pass', duration_seconds: 95, input_tokens: 25_000, output_tokens: 2_500 },
      },
      {
        workload: 'brownfield-repo-sync',
        tier: 'brownfield',
        total_authoring_seconds: 600,
        input_tokens: 1_200_000,
        cached_tokens: 1_000_000,
        output_tokens: 15_000,
        authoring_usd: 0.65,
        rework_usd: 0.5,
        direct_rework_usd: 2.5,
        existing_repo_sync_ready: true,
        pdd_test_status: { status: 'pass', duration_seconds: 480, input_tokens: 40_000, output_tokens: 4_000 },
      },
    ],
  };
  const observeRuns = [
    {
      repo: 'promptdriven/pdd',
      repo_open_issues: 40,
      eligible_issues: 12,
      taken_pct: 30,
      quality: {
        evaluated_runs: 20,
        zero_edit_merged_runs: 19,
        observe_would_merge_runs: 0,
        human_intervention_runs: 1,
        failed_or_reopened_runs: 0,
        grade_a: 18,
        grade_b: 1,
        grade_c: 1,
        reopened_7d: 0,
      },
    },
  ];

  const ns = computeNorthStarScorecard({ releaseRun, observeRuns });
  assert.equal(ns.pdd_vs_direct_coding.small_builds.meets_target, true);
  assert.ok(ns.pdd_vs_direct_coding.small_builds.speed_ratio_vs_direct <= 1.0);
  assert.equal(ns.pdd_vs_direct_coding.large_codebases.meets_target, true);
  assert.equal(ns.pdd_vs_direct_coding.large_codebases.feature_iteration_speedup_x, 2.5);
  assert.equal(ns.pdd_vs_direct_coding.large_codebases.rework_cost_reduction_pct, 80);
  assert.equal(ns.autopilot_zero_edit.zero_edit_completion_pct, 95);
  assert.equal(ns.autopilot_zero_edit.meets_target, true);
});

test('observe runner enforces GET-only guard, tracks ETag hits, classifies skip reasons, and writes JSONL', t => {
  assert.equal(assertGetOnlyMethod('GET'), 'GET');
  assert.throws(() => assertGetOnlyMethod('POST'), /forbids non-GET/);
  assert.throws(() => assertGetOnlyMethod('DELETE'), /forbids non-GET/);

  const stateDir = mkdtempSync(join(tmpdir(), 'pdd-observe-test-'));
  t.after(() => rmSync(stateDir, { recursive: true, force: true }));

  const issuesPayload = [
    { number: 10, state: 'open', title: 'External runtime issue', labels: [{ name: 'pdd:runtime' }], assignees: [], created_at: '2026-11-10T00:00:00Z' },
    { number: 11, state: 'open', title: 'Assigned to person', labels: [], assignees: [{ login: 'dev' }], created_at: '2026-11-10T01:00:00Z' },
    { number: 12, state: 'open', title: 'Already fixed', labels: [], assignees: [], created_at: '2026-11-10T02:00:00Z' },
    { number: 13, state: 'open', title: 'Blocked feature', body: 'Blocked by #14', labels: [], assignees: [], created_at: '2026-11-10T03:00:00Z' },
    { number: 14, state: 'open', title: 'Update src/metrics-model.mjs', body: 'Improve src/metrics-model.mjs', labels: [], assignees: [], created_at: '2026-11-10T04:00:00Z' },
    { number: 15, state: 'open', title: 'Update docs/metrics.md', body: 'Document docs/metrics.md', labels: [], assignees: [], created_at: '2026-11-10T05:00:00Z' },
    { number: 16, state: 'open', title: 'Follow-up in src/metrics-model.mjs', body: 'Touch src/metrics-model.mjs again', labels: [], assignees: [], created_at: '2026-11-10T06:00:00Z' },
  ];
  const openPullsPayload = [];
  const closedPullsPayload = [
    {
      number: 99,
      merged_at: '2026-11-12T00:00:00Z',
      title: 'Fix #12',
      body: 'Closes #12',
      user: { login: 'pdd-autopilot[bot]', type: 'Bot' },
      head: { ref: 'pdd/bug-12-abc' },
    },
  ];
  const pr99CommitsPayload = [
    { author: { login: 'pdd-autopilot[bot]' }, committer: { login: 'web-flow' } },
  ];

  const seenCalls = [];
  const fakeExec = (cmd, args) => {
    seenCalls.push([cmd, ...args]);
    assert.equal(cmd, 'gh');
    const methodIdx = args.indexOf('--method');
    assert.equal(args[methodIdx + 1], 'GET');
    const ifNoneMatch = args.includes('-H') ? args[args.indexOf('-H') + 1] : '';
    const endpoint = args.find(a => a.startsWith('repos/'));

    if (endpoint.includes('/issues?')) {
      if (ifNoneMatch.includes('W/"issues-v1"')) {
        return { code: 0, stdout: 'HTTP/2.0 304 Not Modified\r\nEtag: W/"issues-v1"\r\n\r\n', stderr: '' };
      }
      return { code: 0, stdout: `HTTP/2.0 200 OK\r\nEtag: W/"issues-v1"\r\n\r\n${JSON.stringify(issuesPayload)}`, stderr: '' };
    }
    if (endpoint.includes('/pulls?state=open')) {
      if (ifNoneMatch.includes('W/"open-pr-v1"')) {
        return { code: 0, stdout: 'HTTP/2.0 304 Not Modified\r\nEtag: W/"open-pr-v1"\r\n\r\n', stderr: '' };
      }
      return { code: 0, stdout: `HTTP/2.0 200 OK\r\nEtag: W/"open-pr-v1"\r\n\r\n${JSON.stringify(openPullsPayload)}`, stderr: '' };
    }
    if (endpoint.includes('/issues/12/events')) {
      if (ifNoneMatch.includes('W/"ev-12"')) {
        return { code: 0, stdout: 'HTTP/2.0 304 Not Modified\r\nEtag: W/"ev-12"\r\n\r\n', stderr: '' };
      }
      return { code: 0, stdout: 'HTTP/2.0 200 OK\r\nEtag: W/"ev-12"\r\n\r\n[]', stderr: '' };
    }
    if (endpoint.includes('/pulls/99/commits')) {
      if (ifNoneMatch.includes('W/"cm-99"')) {
        return { code: 0, stdout: 'HTTP/2.0 304 Not Modified\r\nEtag: W/"cm-99"\r\n\r\n', stderr: '' };
      }
      return { code: 0, stdout: `HTTP/2.0 200 OK\r\nEtag: W/"cm-99"\r\n\r\n${JSON.stringify(pr99CommitsPayload)}`, stderr: '' };
    }
    if (ifNoneMatch.includes('W/"closed-pr-v1"')) {
      return { code: 0, stdout: 'HTTP/2.0 304 Not Modified\r\nEtag: W/"closed-pr-v1"\r\n\r\n', stderr: '' };
    }
    return { code: 0, stdout: `HTTP/2.0 200 OK\r\nEtag: W/"closed-pr-v1"\r\n\r\n${JSON.stringify(closedPullsPayload)}`, stderr: '' };
  };

  const localContextFactory = () => ({
    checkoutDir: null,
    intakeCardsByIssue: new Map(),
    historyRows: [
      { issue: 1, pr: 50, outcome: 'would-merge', at: Date.parse('2026-11-14T00:00:00Z'), text: 'passed' },
      { issue: 2, pr: 51, outcome: 'needs-person', at: Date.parse('2026-11-14T01:00:00Z'), text: 'question' },
    ],
    mainFixedIssues: new Set(),
    tokensLast7d: 500_000,
    cacheHitPct: 95.2,
  });

  // Pass 1 populates ETag cache
  const first = runAutopilotObserve(
    { repos: ['promptdriven/pdd'], stateDir, slots: 4 },
    { exec: fakeExec, localContextFactory },
  );
  assert.equal(first.mutations, 0);
  const r1 = first.runs[0];
  assert.equal(r1.repo_open_issues, 7);
  assert.equal(r1.eligible_issues, 3);
  assert.equal(r1.skipped_by_reason.label_skip, 1);
  assert.equal(r1.skipped_by_reason.human_owned, 1);
  assert.equal(r1.skipped_by_reason.already_fixed_on_main, 1);
  assert.equal(r1.skipped_by_reason.blocked_by_graph, 1);
  // #14 and #15 dispatch in parallel slots; #16 overlaps src/metrics-model.mjs with #14 and queues!
  assert.deepEqual(r1.dispatch_plan.selected.map(s => s.issue), [14, 15]);
  assert.equal(r1.dispatch_plan.queued_area_overlap, 1);
  // 1 bot-verified merged PR (#99) + 1 observe would-merge (#50) out of 3 evaluated runs
  assert.equal(r1.quality.zero_edit_merged_runs, 1);
  assert.equal(r1.quality.observe_would_merge_runs, 1);
  assert.equal(r1.quality.observe_included_completed_runs, 2);
  assert.equal(r1.quality.evaluated_runs, 3);

  // Pass 2 hits ETag 304 cache
  const second = runAutopilotObserve(
    { repos: ['promptdriven/pdd'], stateDir, slots: 4 },
    { exec: fakeExec, localContextFactory },
  );
  assert.ok(second.runs[0].etag_hits >= 2);
  assert.ok(second.runs[0].etag_hit_rate > 0.5);

  const jsonlLines = readFileSync(join(stateDir, 'observe-runs.jsonl'), 'utf8').trim().split('\n');
  assert.equal(jsonlLines.length, 2);
});

test('renderBenchmarkReport builds self-contained SVG HTML and scrubs commit hashes and UUIDs', t => {
  const tmp = mkdtempSync(join(tmpdir(), 'pdd-bench-html-'));
  t.after(() => rmSync(tmp, { recursive: true, force: true }));

  const fakeSha = '0123456789abcdef0123456789abcdef01234567';
  const fakeUuid = 'ddf354cb-3426-4436-a1fb-5bc16d5289c9';
  const sanitized = sanitizePublicText(`Run ${fakeUuid} at ${fakeSha} and head a1b2c3d4`);
  assertCleanPublicText(sanitized);

  const releaseReport = runReleaseBenchmark({
    candidateJson: {
      version: '0.1.34',
      date: '2026-11-16',
      skills: { total_files: 68, total_lines: 3500, total_bytes: 280_000 },
      workloads: [
        {
          workload: 'snake',
          prompt_only_seconds: 262,
          post_prompt_pre_test_seconds: 292,
          total_authoring_seconds: 554,
          input_tokens: 3_070_000,
          cached_tokens: 2_800_000,
          output_tokens: 24_600,
          pdd_lint_status: { status: 'pass', duration_seconds: 3 },
          pdd_test_status: { status: 'pass', duration_seconds: 186 },
        },
      ],
    },
    baselineJson: {
      version: '0.1.32',
      date: '2026-11-14',
      skills: { total_files: 68, total_lines: 3400, total_bytes: 270_000 },
      workloads: [
        {
          workload: 'snake',
          prompt_only_seconds: 200,
          post_prompt_pre_test_seconds: 124,
          total_authoring_seconds: 324,
          input_tokens: 1_580_000,
          cached_tokens: 1_400_000,
          output_tokens: 13_100,
          pdd_lint_status: { status: 'pass', duration_seconds: 3 },
          pdd_test_status: { status: 'pass', duration_seconds: 115 },
        },
      ],
    },
  });

  const html = renderBenchmarkReport({
    releaseReport,
    observeRuns: [
      {
        repo: 'promptdriven/pdd',
        date: '2026-11-16',
        mutations: 0,
        repo_open_issues: 50,
        eligible_issues: 15,
        taken_pct: 30,
        skipped_by_reason: { label_skip: 5, human_owned: 10 },
        dispatch_plan: { selected: [{ slot: 1, issue: 3462, areas: ['scripts/benchmark'], companions: [] }] },
        api_calls: 4,
        etag_hit_rate: 0.75,
        latency_ms: 420,
        quality: {
          evaluated_runs: 50,
          zero_edit_completed_runs: 25,
          zero_edit_completion_pct: 50,
          grade_a: 23,
          grade_b: 2,
          grade_c: 25,
          reopened_7d: 0,
        },
      },
    ],
    subtitle: `Note with ${fakeSha} and ${fakeUuid}`,
  });

  assert.ok(html.includes('<!DOCTYPE html>'));
  assert.ok(html.includes('<svg viewBox='));
  assert.ok(html.includes('Locked Next-Month North-Star Investor Scorecard'));
  assert.ok(html.includes('90%–95%'));
  assert.ok(html.includes('2.0x–3.0x'));
  assertCleanPublicText(html, 'rendered HTML');

  // Verify CLI entrypoint writes clean HTML file
  const relFile = join(tmp, 'release.json');
  const outHtml = join(tmp, 'report.html');
  writeFileSync(relFile, JSON.stringify(releaseReport));
  const cli = spawnSync(
    process.execPath,
    [resolve('scripts/benchmark/render-benchmark-report.mjs'), '--release-json', relFile, '--out', outHtml],
    { encoding: 'utf8' },
  );
  assert.equal(cli.status, 0, cli.stderr);
  assert.ok(readFileSync(outHtml, 'utf8').includes('<svg'));
});

test('scorecard guards unrounded target thresholds, incomplete small-build telemetry, runtime USD, and brownfield overrides', () => {
  // 196.5s / 196s = 1.00255 -> displays 1.0x when rounded to 2 decimals, yet MUST fail strict <= 1.0x check
  const slightlyOverSpeed = computeNorthStarScorecard({
    releaseRun: {
      workloads: [{
        workload: 'snake',
        tier: 'small',
        total_authoring_seconds: 150,
        authoring_usd: 0.2,
        pdd_test_status: { status: 'pass', duration_seconds: 46.5, input_tokens: 0, output_tokens: 0 },
      }],
    },
  });
  assert.equal(slightlyOverSpeed.pdd_vs_direct_coding.small_builds.speed_ratio_vs_direct, 1.0);
  assert.equal(slightlyOverSpeed.pdd_vs_direct_coding.small_builds.meets_target, false);

  // Runtime token cost pushes total USD over $0.35 direct baseline, and unreported runtime tokens fail completeness
  const runtimeCostOver = computeNorthStarScorecard({
    releaseRun: {
      workloads: [{
        workload: 'snake',
        tier: 'small',
        total_authoring_seconds: 100,
        authoring_usd: 0.30,
        pdd_test_status: { status: 'pass', duration_seconds: 30, input_tokens: 20_000, output_tokens: 5_000 },
      }],
    },
  });
  assert.ok(runtimeCostOver.pdd_vs_direct_coding.small_builds.cost_ratio_vs_direct > 1.0);
  assert.equal(runtimeCostOver.pdd_vs_direct_coding.small_builds.meets_target, false);

  const missingRuntimeTokens = computeNorthStarScorecard({
    releaseRun: {
      workloads: [{
        workload: 'snake',
        tier: 'small',
        total_authoring_seconds: 100,
        authoring_usd: 0.15,
        pdd_test_status: { status: 'pass', duration_seconds: 30, tokens_unreported: true },
      }],
    },
  });
  assert.equal(missingRuntimeTokens.pdd_vs_direct_coding.small_builds.complete_measurements, false);
  assert.equal(missingRuntimeTokens.pdd_vs_direct_coding.small_builds.meets_target, false);

  // Failed brownfield workload cannot be overridden by top-level existing_repo_sync_ready: true
  const failedBrownfield = computeNorthStarScorecard({
    releaseRun: {
      existing_repo_sync_ready: true,
      workloads: [{
        workload: 'brownfield-repo-sync',
        tier: 'brownfield',
        total_authoring_seconds: 500,
        rework_usd: 0.4,
        direct_rework_usd: 2.5,
        existing_repo_sync_ready: false,
        pdd_test_status: { status: 'fail', duration_seconds: 200 },
      }],
    },
  });
  assert.equal(failedBrownfield.pdd_vs_direct_coding.large_codebases.existing_repo_sync_ready, false);
  assert.equal(failedBrownfield.pdd_vs_direct_coding.large_codebases.meets_target, false);
});

test('evaluateQualityAndZeroEdit separates observe would-merge from merged, tracks sticky human intervention, and detects 7d reopened events', () => {
  const mergedAt = Date.parse('2026-11-10T00:00:00Z');
  const reopened2dLater = '2026-11-12T00:00:00Z';

  // Observe-only would-merge runs do NOT satisfy Bar 2 strict merged 90-95% target
  const observeOnlyQual = evaluateQualityAndZeroEdit({
    historyRows: Array.from({ length: 10 }, (_, idx) => ({
      issue: idx + 1,
      pr: 100 + idx,
      outcome: 'would-merge',
      at: mergedAt,
      text: 'passed in observe mode',
    })),
  });
  assert.equal(observeOnlyQual.zero_edit_merged_runs, 0);
  assert.equal(observeOnlyQual.observe_would_merge_runs, 10);
  assert.equal(observeOnlyQual.zero_edit_completion_pct, 0);
  assert.equal(observeOnlyQual.observe_included_completion_pct, 100);
  const nsObserveOnly = computeNorthStarScorecard({
    observeRuns: [{ repo: 'promptdriven/pdd', quality: observeOnlyQual }],
  });
  assert.equal(nsObserveOnly.autopilot_zero_edit.meets_target, false);

  // Sticky needs-person + authoritative GitHub merged_at reopen (even when ledger row.at was delayed) + missing commit audit -> unverified
  const mixedQual = evaluateQualityAndZeroEdit({
    historyRows: [
      { issue: 201, pr: 301, outcome: 'needs-person', at: mergedAt - 3600_000, text: 'asked human' },
      { issue: 201, pr: 301, outcome: 'merged', at: mergedAt, text: 'merged after human answer' },
      { issue: 202, pr: 302, outcome: 'merged', at: Date.parse('2026-11-15T00:00:00Z'), text: 'delayed ledger row after reopen' },
      { issue: 203, pr: 303, outcome: 'merged', at: mergedAt, text: 'merged cleanly with commit & event audit' },
      { issue: 205, pr: 305, outcome: 'merged', at: mergedAt, text: 'ledger merge with missing commit audit' },
    ],
    closedPulls: [
      { number: 301, merged_at: '2026-11-10T00:00:00Z', title: 'PR 301', body: 'Closes #201', user: { login: 'bot', type: 'User' }, head: { ref: 'pdd/bug-201-a' } },
      { number: 302, merged_at: '2026-11-10T00:00:00Z', title: 'PR 302', body: 'Closes #202', user: { login: 'bot', type: 'User' }, head: { ref: 'pdd/bug-202-a' } },
      { number: 303, merged_at: '2026-11-10T00:00:00Z', title: 'PR 303', body: 'Closes #203', user: { login: 'bot', type: 'User' }, head: { ref: 'pdd/bug-203-a' } },
      {
        number: 304,
        merged_at: '2026-11-10T00:00:00Z',
        title: 'Unledgered human-token PR',
        body: 'Closes #204',
        user: { login: 'alice', type: 'User' },
        head: { ref: 'pdd/bug-204-fix' },
      },
      { number: 305, merged_at: '2026-11-10T00:00:00Z', title: 'PR 305', body: 'Closes #205', user: { login: 'bot', type: 'User' }, head: { ref: 'pdd/bug-205-a' } },
    ],
    issueEventsByIssue: new Map([
      [201, []],
      [202, [{ event: 'reopened', created_at: reopened2dLater }]],
      [203, [{ event: 'subscribed', created_at: reopened2dLater }]],
      [204, []],
      [205, []],
    ]),
    prCommitsByPr: new Map([
      [301, [{ author: { login: 'bot' } }]],
      [302, [{ author: { login: 'bot' } }]],
      [303, [{ author: { login: 'bot' } }]],
      [304, [{ author: { login: 'alice' } }]],
    ]),
  });
  assert.equal(mixedQual.zero_edit_merged_runs, 1); // only #203 has ledger + audited commits + audited events
  assert.equal(mixedQual.human_intervention_runs, 1); // #201 sticky needs-person
  assert.equal(mixedQual.reopened_7d, 1); // #202 reopened 2d after GitHub merged_at despite later ledger row.at
  assert.equal(mixedQual.unverified_merged_runs, 2); // #204 non-bot without ledger + #205 missing commit audit
});

test('sanitizePublicText scrubs underscore-delimited hashes/UUIDs/URLs, SVG/HTML escapes attributes, and seedBrownfieldTemplate builds passing multi-module repo', t => {
  const embeddedSha40 = 'ref_0123456789abcdef0123456789abcdef01234567_tail';
  const embeddedUuid = 'id_ddf354cb-3426-4436-a1fb-5bc16d5289c9_done';
  const commitUrl = 'https://github.com/promptdriven/pdd/commit/a1b2c3d4e5f6';
  assert.throws(() => assertCleanPublicText(embeddedSha40), /Forbidden/);
  assert.throws(() => assertCleanPublicText(embeddedUuid), /Forbidden/);
  assert.throws(() => assertCleanPublicText(commitUrl), /Forbidden/);
  const cleaned = sanitizePublicText(`${embeddedSha40} ${embeddedUuid} ${commitUrl} revision=deadbeef1234`);
  assertCleanPublicText(cleaned);
  assert.ok(!cleaned.includes('deadbeef1234'));

  const svgAttr = renderSvgDualBarChart({
    title: 'Chart',
    subtitle: 'Sub',
    labels: ['v1'],
    seriesA: [10],
    colorA: '#2563eb" onload="alert(1)',
  });
  assert.ok(!svgAttr.includes('" onload="'));
  assert.ok(svgAttr.includes('&quot; onload=&quot;alert(1)'));

  const xssHtml = renderBenchmarkReport({
    observeRuns: [{
      repo: 'promptdriven/pdd',
      date: '2026-11-16',
      mutations: 0,
      repo_open_issues: 1,
      eligible_issues: 1,
      taken_pct: 100,
      skipped_by_reason: {},
      dispatch_plan: {
        selected: [{ slot: 1, issue: 99, areas: ['area:<img src=x onerror=alert(1)>'], companions: [] }],
      },
      quality: { evaluated_runs: 0 },
    }],
  });
  assert.ok(!xssHtml.includes('<img src=x'));
  assert.ok(xssHtml.includes('&lt;img src=x onerror=alert(1)&gt;'));

  const brownfieldDir = mkdtempSync(join(tmpdir(), 'pdd-brownfield-seed-'));
  t.after(() => rmSync(brownfieldDir, { recursive: true, force: true }));
  spawnSync('git', ['init', '-q'], { cwd: brownfieldDir });
  seedBrownfieldTemplate(brownfieldDir);
  const existingTest = spawnSync(process.execPath, ['--test', 'test/existing.test.mjs'], {
    cwd: brownfieldDir,
    encoding: 'utf8',
  });
  assert.equal(existingTest.status, 0, existingTest.stderr);

  // Structured short hex commit/revision/sha fields are scrubbed recursively
  const scrubbedObj = sanitizePublicData({
    revision: 'a1b2c3d4',
    commitSha: 'deadbeef1234',
    history: [{ sha: '1234567890ab', version: '0.1.34' }],
  });
  assert.equal(scrubbedObj.revision, 'redacted-ref');
  assert.equal(scrubbedObj.commitSha, 'redacted-ref');
  assert.equal(scrubbedObj.history[0].sha, 'redacted-ref');
  assert.equal(scrubbedObj.history[0].version, '0.1.34');

  // PR-only ledger rows inherit issue from closedPulls for 7d reopen check, and multi-PR issues never mask later reopens
  const prOnlyAndMultiPr = evaluateQualityAndZeroEdit({
    historyRows: [
      { pr: 401, outcome: 'merged', at: Date.parse('2026-11-10T00:00:00Z'), text: 'PR-only ledger row' },
      { issue: 502, pr: 402, outcome: 'merged', at: Date.parse('2026-11-12T00:00:00Z'), text: 'latest merge on #502' },
    ],
    closedPulls: [
      { number: 401, merged_at: '2026-11-10T00:00:00Z', title: 'Fix #501', body: 'Closes #501', user: { login: 'bot', type: 'User' }, head: { ref: 'pdd/bug-501-a' } },
      { number: 402, merged_at: '2026-11-12T00:00:00Z', title: 'Fix #502 v2', body: 'Closes #502', user: { login: 'bot', type: 'User' }, head: { ref: 'pdd/bug-502-b' } },
      { number: 400, merged_at: '2026-11-01T00:00:00Z', title: 'Fix #502 v1', body: 'Closes #502', user: { login: 'bot', type: 'User' }, head: { ref: 'pdd/bug-502-a' } },
    ],
    issueEventsByIssue: new Map([
      [501, [{ event: 'reopened', created_at: '2026-11-11T00:00:00Z' }]],
      [502, [{ event: 'reopened', created_at: '2026-11-14T00:00:00Z' }]],
    ]),
    prCommitsByPr: new Map([
      [401, [{ author: { login: 'bot' } }]],
      [402, [{ author: { login: 'bot' } }]],
      [400, [{ author: { login: 'bot' } }]],
    ]),
  });
  assert.equal(prOnlyAndMultiPr.zero_edit_merged_runs, 0);
  assert.equal(prOnlyAndMultiPr.reopened_7d, 2);

  // Two PR-only ledger rows for one issue collapse into 1 multi-PR rework run; delayed ledger date after 10d reopen does not false-positive
  const dedupAndDelayed = evaluateQualityAndZeroEdit({
    historyRows: [
      { pr: 601, outcome: 'merged', at: Date.parse('2026-11-01T00:00:00Z') },
      { pr: 602, outcome: 'merged', at: Date.parse('2026-11-05T00:00:00Z') },
      { issue: 702, pr: 603, outcome: 'merged', at: Date.parse('2026-11-10T00:00:00Z') },
    ],
    closedPulls: [
      { number: 601, merged_at: '2026-11-01T00:00:00Z', body: 'Closes #701', user: { login: 'bot', type: 'User' }, head: { ref: 'pdd/bug-701-a' } },
      { number: 602, merged_at: '2026-11-05T00:00:00Z', body: 'Closes #701', user: { login: 'bot', type: 'User' }, head: { ref: 'pdd/bug-701-b' } },
      { number: 603, merged_at: '2026-11-01T00:00:00Z', body: 'Closes #702', user: { login: 'bot', type: 'User' }, head: { ref: 'pdd/bug-702-a' } },
    ],
    issueEventsByIssue: new Map([
      [701, []],
      [702, [{ event: 'reopened', created_at: '2026-11-11T00:00:00Z' }]], // 10 days after actual merge -> NOT a 7d reopen
    ]),
    prCommitsByPr: new Map([
      [601, [{ author: { login: 'bot' } }]],
      [602, [{ author: { login: 'bot' } }]],
      [603, [{ author: { login: 'bot' } }]],
    ]),
  });
  assert.equal(dedupAndDelayed.evaluated_runs, 2); // #701 (1 collapsed run) + #702 (1 run)
  assert.equal(dedupAndDelayed.human_intervention_runs, 1); // #701 multi-PR rework
  assert.equal(dedupAndDelayed.reopened_7d, 0); // #702 reopened 10d after GitHub merged_at
  assert.equal(dedupAndDelayed.zero_edit_merged_runs, 1); // #702 clean within 7d

  // Issue-qualified row + PR-only row for the SAME PR collapse cleanly in either order without false human intervention
  const samePrObj = { number: 801, merged_at: '2026-11-10T00:00:00Z', body: 'Closes #901', user: { login: 'bot', type: 'User' }, head: { ref: 'pdd/bug-901-a' } };
  for (const rows of [
    [{ issue: 901, pr: 801, outcome: 'released', text: 'out of credits' }, { pr: 801, outcome: 'merged', at: Date.parse('2026-11-10T00:00:00Z') }],
    [{ pr: 801, outcome: 'released', text: 'out of credits' }, { issue: 901, pr: 801, outcome: 'merged', at: Date.parse('2026-11-10T00:00:00Z') }],
  ]) {
    const qSame = evaluateQualityAndZeroEdit({
      historyRows: rows,
      closedPulls: [samePrObj],
      issueEventsByIssue: new Map([[901, []]]),
      prCommitsByPr: new Map([[801, [{ author: { login: 'bot' } }]]]),
    });
    assert.equal(qSame.evaluated_runs, 1);
    assert.equal(qSame.zero_edit_merged_runs, 1);
    assert.equal(qSame.human_intervention_runs, 0);
  }

  // Unreported runtime tokens render Total: — rather than falling back to authoring-only USD
  const unreportedTotalHtml = renderBenchmarkReport({
    releaseReport: {
      candidate: {
        version: '0.1.35',
        date: '2026-11-16',
        workloads: [{
          workload: 'snake',
          label: 'Snake',
          tier: 'small',
          total_authoring_seconds: 100,
          authoring_usd: 0.15,
          input_tokens: 10_000,
          output_tokens: 2_000,
          pdd_lint_status: { status: 'pass', duration_seconds: 1 },
          pdd_test_status: { status: 'pass', duration_seconds: 20, tokens_unreported: true },
        }],
      },
    },
  });
  assert.ok(unreportedTotalHtml.includes('Auth: $0.15 · Total: —'));

  // Missing commit author login stays unverified, and GitHub-merged would-merge PR promotes to merged + reopen check
  const nullAuthorAndPromoted = evaluateQualityAndZeroEdit({
    historyRows: [
      { issue: 1001, pr: 951, outcome: 'merged', at: Date.parse('2026-11-10T00:00:00Z') },
      { issue: 1002, pr: 952, outcome: 'would-merge', at: Date.parse('2026-11-10T00:00:00Z') },
      { issue: 1003, pr: 953, outcome: 'would-merge', at: Date.parse('2026-11-10T00:00:00Z') },
    ],
    closedPulls: [
      { number: 951, merged_at: '2026-11-10T00:00:00Z', body: 'Closes #1001', user: { login: 'bot', type: 'Bot' }, head: { ref: 'pdd/bug-1001-a' } },
      { number: 952, merged_at: '2026-11-10T00:00:00Z', body: 'Closes #1002', user: { login: 'bot', type: 'Bot' }, head: { ref: 'pdd/bug-1002-a' } },
      { number: 953, merged_at: '2026-11-10T00:00:00Z', body: 'Closes #1003', user: { login: 'bot', type: 'Bot' }, head: { ref: 'pdd/bug-1003-a' } },
    ],
    issueEventsByIssue: new Map([
      [1001, []],
      [1002, []],
      [1003, [{ event: 'reopened', created_at: '2026-11-12T00:00:00Z' }]],
    ]),
    prCommitsByPr: new Map([
      [951, [{ author: null }]],
      [952, [{ author: { login: 'bot' } }]],
      [953, [{ author: { login: 'bot' } }]],
    ]),
  });
  assert.equal(nullAuthorAndPromoted.merged_prs, 3);
  assert.equal(nullAuthorAndPromoted.would_merge_prs, 0);
  assert.equal(nullAuthorAndPromoted.unverified_merged_runs, 1); // #1001 author: null
  assert.equal(nullAuthorAndPromoted.zero_edit_merged_runs, 1); // #1002 bot-verified promoted merge
  assert.equal(nullAuthorAndPromoted.reopened_7d, 1); // #1003 promoted merge caught 7d reopen

  // Closed-unmerged Autopilot PR counts in failed_or_reopened_runs; User-token would-merge merged untouched stays in observe_would_merge_runs
  const closedUnmergedAndObserveMerge = evaluateQualityAndZeroEdit({
    historyRows: [
      { issue: 1102, pr: 962, outcome: 'would-merge', at: Date.parse('2026-11-10T00:00:00Z') },
    ],
    closedPulls: [
      { number: 961, merged_at: null, state: 'closed', body: 'Closes #1101', user: { login: 'bot', type: 'Bot' }, head: { ref: 'pdd/bug-1101-a' } },
      { number: 962, merged_at: '2026-11-10T00:00:00Z', body: 'Closes #1102', user: { login: 'alice', type: 'User' }, head: { ref: 'pdd/bug-1102-a' } },
    ],
    issueEventsByIssue: new Map([[1101, []], [1102, []]]),
    prCommitsByPr: new Map([[962, [{ author: { login: 'alice' } }]]]),
  });
  assert.equal(closedUnmergedAndObserveMerge.evaluated_runs, 2);
  assert.equal(closedUnmergedAndObserveMerge.failed_or_reopened_runs, 1);
  assert.equal(closedUnmergedAndObserveMerge.observe_would_merge_runs, 1);
  assert.equal(closedUnmergedAndObserveMerge.zero_edit_merged_runs, 0);

  // Bare abbreviated hex commit ref in title or version is scrubbed while semver stays intact
  const shortShaHtml = renderBenchmarkReport({
    title: 'Release abc1234',
    releaseReport: { candidate: { version: 'abc1234', workloads: [] }, baseline: { version: '0.1.35', workloads: [] } },
  });
  assert.ok(!shortShaHtml.includes('abc1234'));
  assert.ok(shortShaHtml.includes('0.1.35'));

  // 60+ clean merged runs keep 100% completion because audit window covers the evaluated window
  const sixtyPrs = Array.from({ length: 60 }, (_, idx) => ({
    number: idx + 101,
    merged_at: '2026-11-10T00:00:00Z',
    body: `Closes #${idx + 1}`,
    head: { ref: `pdd/bug-${idx + 1}-a` },
    user: { login: 'bot', type: 'Bot' },
  }));
  const sixtyObs = observeRepository({
    repo: 'promptdriven/pdd',
    ghClient: {
      paginate: ep => (ep.includes('state=closed') ? sixtyPrs : []),
      paginateWithMeta: ep => ({ items: ep.includes('/commits?') ? [{ author: { login: 'bot' } }] : [], truncated: false }),
    },
    localContext: {
      historyRows: sixtyPrs.map((p, idx) => ({ issue: idx + 1, pr: p.number, outcome: 'merged', at: Date.parse(p.merged_at) })),
    },
  });
  assert.equal(sixtyObs.quality.evaluated_runs, 60);
  assert.equal(sixtyObs.quality.zero_edit_completion_pct, 100);

  // Live brownfield execution measures rework_usd (0 on clean first-try pass) so Bar 1 large_codebases can pass
  const liveRoot = mkdtempSync(join(tmpdir(), 'pdd-live-bf-'));
  t.after(() => rmSync(liveRoot, { recursive: true, force: true }));
  let fakeClock = 1_000_000;
  const bfRecord = executeLiveAgentWorkload({
    workload: BENCHMARK_WORKLOADS['brownfield-repo-sync'],
    pddBin: '/fake/pdd.mjs',
    packageRoot: liveRoot,
    workDirRoot: liveRoot,
    agentCommand: ['fake-agent'],
    now: () => { fakeClock += 100_000; return fakeClock; },
    run: (bin, args, opts = {}) => {
      if (bin === 'fake-agent') {
        mkdirSync(join(opts.cwd, 'prompts'), { recursive: true });
        mkdirSync(join(opts.cwd, 'user_stories'), { recursive: true });
        writeFileSync(join(opts.cwd, 'prompts/summary.prompt.md'), 'Sync src/summary.mjs\n');
        writeFileSync(join(opts.cwd, 'user_stories/orders.md'), '# Story\n');
        const shimLog = join(opts.cwd, '.bench-shim/pdd-calls.jsonl');
        writeFileSync(shimLog, [
          JSON.stringify({ argv: ['lint'], start_ms: 1_200_000, end_ms: 1_205_000, duration_s: 5, exit_code: 0, stdout: 'PASS (0 errors)', stderr: '' }),
          JSON.stringify({ argv: ['test'], start_ms: 1_210_000, end_ms: 1_310_000, duration_s: 100, exit_code: 0, stdout: 'PASS · 1000 input tokens · 200 output tokens', stderr: '' }),
        ].join('\n') + '\n');
        return { code: 0, stdout: JSON.stringify({ usage: { input_tokens: 50_000, cached_input_tokens: 40_000, output_tokens: 2_000 } }), stderr: '' };
      }
      return { code: 0, stdout: '', stderr: '' };
    },
  });
  assert.equal(bfRecord.rework_usd, 0);
  assert.equal(bfRecord.existing_repo_sync_ready, true);
  const bfScorecard = computeNorthStarScorecard({ releaseRun: { workloads: [bfRecord] } });
  assert.equal(bfScorecard.pdd_vs_direct_coding.large_codebases.rework_cost_reduction_pct, 100);
  assert.equal(bfScorecard.pdd_vs_direct_coding.large_codebases.meets_target, true);
});
