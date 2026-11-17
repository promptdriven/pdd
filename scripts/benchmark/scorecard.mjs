// Shared North-Star scorecard, workload catalog, and output hygiene helpers.

export const DEFAULT_PRICING_PER_MILLION = Object.freeze({
  uncached_input_usd: 2.0,
  cached_input_usd: 0.1,
  output_usd: 10.0,
});

export const NORTH_STAR_TARGETS = Object.freeze({
  pdd_vs_direct_coding: Object.freeze({
    small_builds: Object.freeze({
      speed_ratio_max: 1.0,
      cost_ratio_max: 1.0,
      first_try_runtime_pass_pct: 100.0,
    }),
    large_codebases: Object.freeze({
      direct_baseline_window: '30-60+ min',
      feature_iteration_speedup_min_x: 2.0,
      feature_iteration_speedup_max_x: 3.0,
      rework_cost_reduction_min_pct: 50.0,
      require_existing_repo_sync_ready: true,
    }),
  }),
  autopilot_zero_edit: Object.freeze({
    baseline_pct: 50.0,
    target_min_pct: 90.0,
    target_max_pct: 95.0,
  }),
});

export const BENCHMARK_WORKLOADS = Object.freeze({
  snake: Object.freeze({
    id: 'snake',
    label: 'Snake',
    tier: 'small',
    direct_baseline_seconds: 196,
    direct_baseline_tokens: 128_000,
    direct_baseline_usd: 0.35,
    prompt: 'use pdd cli to create a snake game that I can run in prompt space. Do not look at work outside this directory',
  }),
  '2048': Object.freeze({
    id: '2048',
    label: '2048',
    tier: 'small',
    direct_baseline_seconds: 440,
    direct_baseline_tokens: 1_520_000,
    direct_baseline_usd: 0.65,
    prompt: 'use pdd cli to create a 2048 game that I can run in prompt space. Do not look at work outside this directory',
  }),
  'task-manager': Object.freeze({
    id: 'task-manager',
    label: 'Task Manager',
    tier: 'small',
    direct_baseline_seconds: 568,
    direct_baseline_tokens: 1_620_000,
    direct_baseline_usd: 0.75,
    prompt: 'use pdd cli to create a task manager app with priorities, active/completed filter, and storage persistence that I can run in prompt space. Do not look at work outside this directory',
  }),
  'brownfield-repo-sync': Object.freeze({
    id: 'brownfield-repo-sync',
    label: 'Brownfield Multi-Module Sync & Feature',
    tier: 'brownfield',
    direct_baseline_seconds: 2700,
    direct_baseline_tokens: 4_500_000,
    direct_baseline_usd: 4.5,
    direct_rework_usd: 2.5,
    prompt: 'Sync existing multi-module repository modules incrementally into PDD prompts and deliver a cross-module feature with Story and verification checks while preserving existing behavior.',
  }),
});

export function roundNum(value, digits = 2) {
  if (typeof value !== 'number' || !Number.isFinite(value)) return null;
  const factor = 10 ** digits;
  return Math.round(value * factor) / factor;
}

export function estimateTokenUsd({
  uncachedInputTokens = 0,
  cachedTokens = 0,
  outputTokens = 0,
  pricing = DEFAULT_PRICING_PER_MILLION,
} = {}) {
  const unc = Math.max(0, Number(uncachedInputTokens) || 0);
  const cached = Math.max(0, Number(cachedTokens) || 0);
  const out = Math.max(0, Number(outputTokens) || 0);
  const usd = (unc / 1_000_000) * pricing.uncached_input_usd
    + (cached / 1_000_000) * pricing.cached_input_usd
    + (out / 1_000_000) * pricing.output_usd;
  return roundNum(usd, 4);
}

export const REQUIRED_SMALL_WORKLOADS = Object.freeze(['snake', '2048', 'task-manager']);

// Match hex commit/receipt hashes (40-64 hex chars), commit URLs, labeled/bare short SHAs, and UUIDs.
const UUID_RE = /(?<![0-9a-f])[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}(?![0-9a-f])/gi;
const SHA40_RE = /(?<![0-9a-f])[0-9a-f]{40,64}(?![0-9a-f])/gi;
const COMMIT_URL_RE = /\/commits?\/[0-9a-f]{7,64}(?![0-9a-f])/gi;
const HEAD_HEX_RE = /\b(head|at|commit|rev|revision|sha)(\s*[:=]\s*|\s+)[0-9a-f]{7,64}(?![0-9a-f])/gi;
const BARE_SHORT_HEX_RE = /(?<![#0-9a-z_.-])(?=[0-9a-f]*[a-f])(?=[0-9a-f]*[0-9])[0-9a-f]{7,64}(?![0-9a-z_.-])/gi;

export function sanitizePublicText(value) {
  return String(value ?? '')
    .replace(UUID_RE, 'redacted-id')
    .replace(SHA40_RE, 'redacted-ref')
    .replace(COMMIT_URL_RE, '/commit/redacted-ref')
    .replace(HEAD_HEX_RE, '$1$2current-ref')
    .replace(BARE_SHORT_HEX_RE, 'redacted-ref');
}

const SENSITIVE_REF_KEY_RE = /(?:^|[_-])(?:commit|commits|sha|rev|revision|head|hash|receipt|run_id|runid|version)(?:$|[_-])/i;
const SHORT_HEX_VALUE_RE = /^[0-9a-f]{7,64}$/i;

function isSensitiveRefKey(key = '') {
  const norm = String(key).replace(/([a-z0-9])([A-Z])/g, '$1_$2');
  return SENSITIVE_REF_KEY_RE.test(norm);
}

export function sanitizePublicData(node, parentKey = '') {
  if (typeof node === 'string') {
    if (parentKey && isSensitiveRefKey(parentKey) && SHORT_HEX_VALUE_RE.test(node.trim())) {
      return 'redacted-ref';
    }
    return sanitizePublicText(node);
  }
  if (Array.isArray(node)) return node.map(item => sanitizePublicData(item, parentKey));
  if (node && typeof node === 'object') {
    const out = {};
    for (const [k, v] of Object.entries(node)) {
      out[sanitizePublicText(k)] = sanitizePublicData(v, k);
    }
    return out;
  }
  return node;
}

export function assertCleanPublicText(value, label = 'output') {
  const text = String(value ?? '');
  const sha = text.match(SHA40_RE);
  if (sha) throw new Error(`Forbidden commit/receipt hash in ${label}: ${sha[0]}`);
  const commitUrl = text.match(COMMIT_URL_RE);
  if (commitUrl) throw new Error(`Forbidden commit URL hash in ${label}: ${commitUrl[0]}`);
  const uuid = text.match(UUID_RE);
  if (uuid) throw new Error(`Forbidden UUID in ${label}: ${uuid[0]}`);
  return text;
}

export function computeNorthStarScorecard({ releaseRun = null, observeRuns = [] } = {}) {
  const workloads = Array.isArray(releaseRun?.workloads) ? releaseRun.workloads : [];
  const smallRows = [];
  const brownfieldRows = [];

  for (const w of workloads) {
    const spec = BENCHMARK_WORKLOADS[w.workload] || {};
    const tier = w.tier || spec.tier || 'small';
    const baseSec = Number(w.direct_baseline_seconds ?? spec.direct_baseline_seconds) || null;
    const baseTok = Number(w.direct_baseline_tokens ?? spec.direct_baseline_tokens) || null;
    const baseUsd = Number(w.direct_baseline_usd ?? spec.direct_baseline_usd) || null;

    const authSec = Number.isFinite(w.total_authoring_seconds) ? w.total_authoring_seconds : null;
    const testSec = Number.isFinite(w.pdd_test_status?.duration_seconds) ? w.pdd_test_status.duration_seconds : null;
    const runtimePassed = w.pdd_test_status?.status === 'pass'
      && w.pdd_test_status?.first_try_pass !== false;
    const e2eSec = authSec !== null && testSec !== null ? authSec + testSec : null;

    const inTok = Number.isFinite(w.input_tokens) ? w.input_tokens : null;
    const cachedTok = Number.isFinite(w.cached_tokens) ? w.cached_tokens : 0;
    const outTok = Number.isFinite(w.output_tokens) ? w.output_tokens : null;
    const runtimeIn = Number.isFinite(w.pdd_test_status?.input_tokens) ? w.pdd_test_status.input_tokens : null;
    const runtimeOut = Number.isFinite(w.pdd_test_status?.output_tokens) ? w.pdd_test_status.output_tokens : null;
    const runtimeCostKnown = Number.isFinite(w.runtime_usd)
      || (!w.pdd_test_status?.tokens_unreported && runtimeIn !== null && runtimeOut !== null);

    const totalTok = inTok !== null && outTok !== null && runtimeIn !== null && runtimeOut !== null
      ? inTok + outTok + runtimeIn + runtimeOut
      : null;

    const authoringCostKnown = (Number.isFinite(w.authoring_usd) && w.authoring_usd > 0)
      || (inTok !== null && outTok !== null && inTok + outTok > 0);
    const authUsd = authoringCostKnown
      ? (Number.isFinite(w.authoring_usd) && w.authoring_usd > 0
        ? w.authoring_usd
        : estimateTokenUsd({
          uncachedInputTokens: Math.max(0, inTok - cachedTok),
          cachedTokens: cachedTok,
          outputTokens: outTok,
        }))
      : null;
    const runtimeUsd = Number.isFinite(w.runtime_usd)
      ? w.runtime_usd
      : (runtimeCostKnown
        ? estimateTokenUsd({ uncachedInputTokens: runtimeIn, cachedTokens: 0, outputTokens: runtimeOut })
        : null);
    const totalUsd = authUsd !== null && runtimeUsd !== null ? authUsd + runtimeUsd : null;

    const rawSpeedRatio = e2eSec !== null && baseSec ? e2eSec / baseSec : null;
    const rawAuthoringSpeedRatio = authSec !== null && baseSec ? authSec / baseSec : null;
    const rawTokenRatio = totalTok !== null && baseTok ? totalTok / baseTok : null;
    const rawCostRatio = totalUsd !== null && baseUsd ? totalUsd / baseUsd : null;

    const item = {
      workload: w.workload,
      label: w.label || spec.label || w.workload,
      tier,
      e2e_seconds: roundNum(e2eSec, 1),
      authoring_seconds: roundNum(authSec, 1),
      runtime_test_seconds: roundNum(testSec, 1),
      total_usd: roundNum(totalUsd, 4),
      direct_baseline_seconds: baseSec,
      direct_baseline_tokens: baseTok,
      direct_baseline_usd: baseUsd,
      speed_ratio_vs_direct: roundNum(rawSpeedRatio, 2),
      authoring_speed_ratio_vs_direct: roundNum(rawAuthoringSpeedRatio, 2),
      cost_ratio_vs_direct: roundNum(rawCostRatio, 2),
      token_ratio_vs_direct: roundNum(rawTokenRatio, 2),
      _raw_speed_ratio: rawSpeedRatio,
      _raw_cost_ratio: rawCostRatio,
      _raw_e2e_seconds: e2eSec,
      first_try_runtime_pass: runtimePassed,
      existing_repo_sync_ready: Boolean(w.existing_repo_sync_ready),
      rework_usd: Number.isFinite(w.rework_usd) ? w.rework_usd : null,
      direct_rework_usd: Number(w.direct_rework_usd ?? spec.direct_rework_usd) || null,
    };

    if (tier === 'brownfield') brownfieldRows.push(item);
    else smallRows.push(item);
  }

  // Bar 1a: Small builds — require complete time & USD measurements on every small workload, compare unrounded ratios.
  const rawSpeedVals = smallRows.map(r => r._raw_speed_ratio).filter(v => v !== null);
  const rawCostVals = smallRows.map(r => r._raw_cost_ratio).filter(v => v !== null);
  const tokVals = smallRows.map(r => r.token_ratio_vs_direct).filter(v => v !== null);

  const rawAvgSpeed = rawSpeedVals.length
    ? rawSpeedVals.reduce((a, b) => a + b, 0) / rawSpeedVals.length
    : null;
  const rawAvgCost = rawCostVals.length
    ? rawCostVals.reduce((a, b) => a + b, 0) / rawCostVals.length
    : null;
  const avgTokenRatio = tokVals.length
    ? roundNum(tokVals.reduce((a, b) => a + b, 0) / tokVals.length, 2)
    : null;

  const passCount = smallRows.filter(r => r.first_try_runtime_pass).length;
  const firstTryPassPct = smallRows.length ? roundNum((passCount / smallRows.length) * 100, 1) : null;
  const smallTargets = NORTH_STAR_TARGETS.pdd_vs_direct_coding.small_builds;
  const hasAllCanonicalSmall = REQUIRED_SMALL_WORKLOADS.every(id => smallRows.some(r => r.workload === id));
  const allSmallMeasured = hasAllCanonicalSmall
    && smallRows.length >= REQUIRED_SMALL_WORKLOADS.length
    && rawSpeedVals.length === smallRows.length
    && rawCostVals.length === smallRows.length;
  const everySmallWithinBar = allSmallMeasured
    && smallRows.every(r => (
      r._raw_speed_ratio <= smallTargets.speed_ratio_max
      && r._raw_cost_ratio <= smallTargets.cost_ratio_max
      && r.first_try_runtime_pass
    ));
  const smallMeets = everySmallWithinBar
    && rawAvgSpeed <= smallTargets.speed_ratio_max
    && rawAvgCost <= smallTargets.cost_ratio_max;

  // Strip private raw fields from output rows
  const publicSmallRows = smallRows.map(({ _raw_speed_ratio, _raw_cost_ratio, _raw_e2e_seconds, ...pub }) => pub);

  // Bar 1b: Larger brownfield codebases — workload evidence always governs over top-level flags.
  const largeTargets = NORTH_STAR_TARGETS.pdd_vs_direct_coding.large_codebases;
  let rawSpeedupX = null;
  let rawReworkCutPct = null;
  let syncReady = false;

  if (brownfieldRows.length > 0) {
    const completeSpeedups = brownfieldRows.map(r => (
      r._raw_e2e_seconds && r._raw_e2e_seconds > 0 && r.direct_baseline_seconds
        ? r.direct_baseline_seconds / r._raw_e2e_seconds
        : null
    ));
    if (completeSpeedups.every(v => v !== null)) {
      rawSpeedupX = completeSpeedups.reduce((a, b) => a + b, 0) / completeSpeedups.length;
    }
    const completeReworkCuts = brownfieldRows.map(r => (
      r.rework_usd !== null && r.direct_rework_usd
        ? ((r.direct_rework_usd - r.rework_usd) / r.direct_rework_usd) * 100
        : null
    ));
    if (completeReworkCuts.every(v => v !== null)) {
      rawReworkCutPct = completeReworkCuts.reduce((a, b) => a + b, 0) / completeReworkCuts.length;
    }
    syncReady = brownfieldRows.every(r => r.existing_repo_sync_ready && r.first_try_runtime_pass);
  } else if (releaseRun?.large_codebase_summary) {
    const ls = releaseRun.large_codebase_summary;
    rawSpeedupX = Number.isFinite(ls.feature_iteration_speedup_x) ? ls.feature_iteration_speedup_x : null;
    rawReworkCutPct = Number.isFinite(ls.rework_cost_reduction_pct) ? ls.rework_cost_reduction_pct : null;
    syncReady = Boolean(ls.existing_repo_sync_ready);
  }

  const publicBrownfieldRows = brownfieldRows.map(({ _raw_speed_ratio, _raw_cost_ratio, _raw_e2e_seconds, ...pub }) => pub);
  const speedupX = roundNum(rawSpeedupX, 2);
  const reworkCutPct = roundNum(rawReworkCutPct, 1);
  const largeMeets = rawSpeedupX !== null
    && rawSpeedupX >= largeTargets.feature_iteration_speedup_min_x
    && rawReworkCutPct !== null
    && rawReworkCutPct > largeTargets.rework_cost_reduction_min_pct
    && (!largeTargets.require_existing_repo_sync_ready || syncReady);

  // Bar 2: Autopilot End-to-End Zero-Edit Completion (strict merged zero-edit vs observe would-merge).
  const latestByRepo = new Map();
  for (const row of Array.isArray(observeRuns) ? observeRuns : []) {
    if (row && typeof row.repo === 'string' && row.repo) {
      latestByRepo.set(row.repo, row);
    }
  }
  const latestObserve = [...latestByRepo.values()];
  let evaluatedRuns = 0;
  let zeroEditMerged = 0;
  let observeWouldMerge = 0;
  let humanInterventionRuns = 0;
  let failedOrReopenedRuns = 0;
  let unverifiedMergedRuns = 0;
  let infraReleasedRuns = 0;
  let reopened7d = 0;
  let gradeA = 0;
  let gradeB = 0;
  let gradeC = 0;

  let countsValid = true;
  const byRepo = latestObserve.map(row => {
    const q = row.quality || {};
    const evalCount = Math.max(0, Number(q.evaluated_runs ?? 0));
    const rawMergedClean = Number(q.zero_edit_merged_runs ?? q.merged_zero_edit_runs ?? 0);
    const rawWouldMergeClean = Number(q.observe_would_merge_runs ?? q.would_merge_prs ?? 0);
    if (rawMergedClean < 0 || rawWouldMergeClean < 0 || rawMergedClean + rawWouldMergeClean > evalCount) {
      countsValid = false;
    }
    const mergedClean = Math.min(evalCount, Math.max(0, rawMergedClean));
    const wouldMergeClean = Math.min(Math.max(0, evalCount - mergedClean), Math.max(0, rawWouldMergeClean));
    const observeIncludedClean = mergedClean + wouldMergeClean;
    const humanCount = Math.max(0, Number(q.human_intervention_runs ?? 0));
    const failCount = Math.max(0, Number(q.failed_or_reopened_runs ?? 0));
    const unverifiedCount = Math.max(0, Number(q.unverified_merged_runs ?? 0));
    const infraCount = Math.max(0, Number(q.infra_released_runs ?? 0));

    evaluatedRuns += evalCount;
    zeroEditMerged += mergedClean;
    observeWouldMerge += wouldMergeClean;
    humanInterventionRuns += humanCount;
    failedOrReopenedRuns += failCount;
    unverifiedMergedRuns += unverifiedCount;
    infraReleasedRuns += infraCount;
    reopened7d += Number(q.reopened_7d ?? 0);
    gradeA += Number(q.grade_a ?? 0);
    gradeB += Number(q.grade_b ?? 0);
    gradeC += Number(q.grade_c ?? 0);

    return {
      repo: row.repo,
      repo_open_issues: Number(row.repo_open_issues ?? 0),
      eligible_issues: Number(row.eligible_issues ?? 0),
      taken_pct: roundNum(Number(row.taken_pct ?? 0), 1),
      evaluated_runs: evalCount,
      zero_edit_merged_runs: mergedClean,
      observe_would_merge_runs: wouldMergeClean,
      zero_edit_completed_runs: mergedClean,
      observe_included_completed_runs: observeIncludedClean,
      human_intervention_runs: humanCount,
      failed_or_reopened_runs: failCount,
      unverified_merged_runs: unverifiedCount,
      infra_released_runs: infraCount,
      zero_edit_completion_pct: evalCount > 0 ? roundNum((mergedClean / evalCount) * 100, 1) : null,
      observe_included_completion_pct: evalCount > 0 ? roundNum((observeIncludedClean / evalCount) * 100, 1) : null,
      reopened_7d: Number(q.reopened_7d ?? 0),
    };
  });

  const pipelineCleanTotal = zeroEditMerged + observeWouldMerge;
  const rawMergedZeroEditPct = evaluatedRuns > 0 ? (zeroEditMerged / evaluatedRuns) * 100 : null;
  const rawPipelineZeroEditPct = evaluatedRuns > 0 ? (pipelineCleanTotal / evaluatedRuns) * 100 : null;
  const apTargets = NORTH_STAR_TARGETS.autopilot_zero_edit;

  // Target bar requires confirmed merged zero-edit delivery >= 90% with 0 7-day reopens;
  // observe-only would-merge runs are reported alongside in observe_included_completion_pct.
  const apMeets = countsValid
    && rawMergedZeroEditPct !== null
    && rawMergedZeroEditPct >= apTargets.target_min_pct
    && reopened7d === 0;

  return {
    targets: NORTH_STAR_TARGETS,
    pdd_vs_direct_coding: {
      small_builds: {
        target_speed_ratio_max: smallTargets.speed_ratio_max,
        target_cost_ratio_max: smallTargets.cost_ratio_max,
        target_first_try_runtime_pass_pct: smallTargets.first_try_runtime_pass_pct,
        speed_ratio_vs_direct: roundNum(rawAvgSpeed, 2),
        cost_ratio_vs_direct: roundNum(rawAvgCost, 2),
        token_ratio_vs_direct: avgTokenRatio,
        first_try_runtime_pass_pct: firstTryPassPct,
        workloads_passed: passCount,
        workloads_total: publicSmallRows.length,
        complete_measurements: allSmallMeasured,
        meets_target: smallMeets,
        workloads: publicSmallRows,
      },
      large_codebases: {
        direct_baseline_window: largeTargets.direct_baseline_window,
        target_feature_speedup_range_x: [
          largeTargets.feature_iteration_speedup_min_x,
          largeTargets.feature_iteration_speedup_max_x,
        ],
        target_rework_cost_reduction_min_pct: largeTargets.rework_cost_reduction_min_pct,
        feature_iteration_speedup_x: speedupX,
        rework_cost_reduction_pct: reworkCutPct,
        existing_repo_sync_ready: syncReady,
        meets_target: largeMeets,
        status: rawSpeedupX === null ? 'pending_measurement' : (largeMeets ? 'met' : 'gap'),
        workloads: publicBrownfieldRows,
      },
    },
    autopilot_zero_edit: {
      baseline_pct: apTargets.baseline_pct,
      target_range_pct: [apTargets.target_min_pct, apTargets.target_max_pct],
      evaluated_runs: evaluatedRuns,
      zero_edit_merged_runs: zeroEditMerged,
      observe_would_merge_runs: observeWouldMerge,
      zero_edit_completed_runs: zeroEditMerged,
      observe_included_completed_runs: pipelineCleanTotal,
      human_intervention_runs: humanInterventionRuns,
      failed_or_reopened_runs: failedOrReopenedRuns,
      unverified_merged_runs: unverifiedMergedRuns,
      infra_released_runs: infraReleasedRuns,
      zero_edit_completion_pct: roundNum(rawMergedZeroEditPct, 1),
      observe_included_completion_pct: roundNum(rawPipelineZeroEditPct, 1),
      grade_a: gradeA,
      grade_b: gradeB,
      grade_c: gradeC,
      reopened_7d: reopened7d,
      meets_target: apMeets,
      repos: byRepo,
    },
  };
}
