// Minimal observe-only scorecard & output hygiene helpers retained for daily pdd-vm run-autopilot-observe.mjs.

const AUTOPILOT_ZERO_EDIT_TARGETS = Object.freeze({
  baseline_pct: 50.0,
  target_min_pct: 90.0,
  target_max_pct: 95.0,
});

export function roundNum(value, digits = 2) {
  if (typeof value !== 'number' || !Number.isFinite(value)) return null;
  const factor = 10 ** digits;
  return Math.round(value * factor) / factor;
}

const GITHUB_TOKEN_RE = /\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+)\b/g;
const SK_TOKEN_RE = /\bsk-[A-Za-z0-9_-]{12,}\b/g;
const BEARER_TOKEN_RE = /\bBearer\s+(?!redacted-token\b)\S+/gi;
const UUID_RE = /(?<![0-9a-f])[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}(?![0-9a-f])/gi;
const SHA40_RE = /(?<![0-9a-f])[0-9a-f]{40,64}(?![0-9a-f])/gi;
const COMMIT_URL_RE = /\/commits?\/[0-9a-f]{7,64}(?![0-9a-f])/gi;
const HEAD_HEX_RE = /\b(head|at|commit|rev|revision|sha)(\s*[:=]\s*|\s+)[0-9a-f]{7,64}(?![0-9a-f])/gi;
const BARE_SHORT_HEX_RE = /(?<![#0-9a-z_.-])(?=[0-9a-f]*[a-f])(?=[0-9a-f]*[0-9])[0-9a-f]{7,64}(?![0-9a-z_.-])/gi;
const SENSITIVE_REF_KEY_RE = /(?:^|[_-])(?:commit|commits|sha|rev|revision|head|hash|receipt|run_id|runid|version)(?:$|[_-])/i;
const SENSITIVE_SECRET_KEY_RE = /(?:^|[_-])(?:auth_token|access_token|github_token|gh_token|secret|password|authorization|api_key|apikey)(?:$|[_-])/i;
const SHORT_HEX_VALUE_RE = /^[0-9a-f]{7,64}$/i;

export class CliUsageError extends Error {
  constructor(message) {
    super(message);
    this.name = 'CliUsageError';
    this.exitCode = 2;
  }
}

export function readCliFlagValue(argv, index, flag, { allowLeadingDash = false } = {}) {
  const next = argv[index + 1];
  if (
    next === undefined
    || next === ''
    || next === '-h'
    || next === '--help'
    || (allowLeadingDash ? next.startsWith('--') : next.startsWith('-'))
  ) {
    throw new CliUsageError(`Missing value for ${flag}`);
  }
  return next;
}

export function parsePositiveNumberFlag(rawValue, flag, { integer = false } = {}) {
  const num = Number(rawValue);
  if (!Number.isFinite(num) || num <= 0 || (integer && !Number.isInteger(num))) {
    throw new CliUsageError(
      `Invalid value for ${flag}: expected a positive ${integer ? 'integer' : 'number'}, got "${rawValue}"`,
    );
  }
  return num;
}

export function sanitizePublicText(value) {
  return String(value ?? '')
    .replace(GITHUB_TOKEN_RE, 'redacted-token')
    .replace(SK_TOKEN_RE, 'redacted-token')
    .replace(BEARER_TOKEN_RE, 'Bearer redacted-token')
    .replace(UUID_RE, 'redacted-id')
    .replace(SHA40_RE, 'redacted-ref')
    .replace(COMMIT_URL_RE, '/commit/redacted-ref')
    .replace(HEAD_HEX_RE, '$1$2current-ref')
    .replace(BARE_SHORT_HEX_RE, 'redacted-ref');
}

export function sanitizePublicData(node, parentKey = '') {
  if (typeof node === 'string') {
    const norm = String(parentKey).replace(/([a-z0-9])([A-Z])/g, '$1_$2');
    if (parentKey && SENSITIVE_SECRET_KEY_RE.test(norm) && node.trim()) return 'redacted-token';
    if (parentKey && SENSITIVE_REF_KEY_RE.test(norm) && SHORT_HEX_VALUE_RE.test(node.trim())) return 'redacted-ref';
    return sanitizePublicText(node);
  }
  if (Array.isArray(node)) return node.map(item => sanitizePublicData(item, parentKey));
  if (node && typeof node === 'object') {
    const out = {};
    for (const [k, v] of Object.entries(node)) out[sanitizePublicText(k)] = sanitizePublicData(v, k);
    return out;
  }
  return node;
}

export function computeNorthStarScorecard({ observeRuns = [] } = {}) {
  const latestByRepo = new Map();
  for (const row of Array.isArray(observeRuns) ? observeRuns : []) {
    if (row && typeof row.repo === 'string' && row.repo) latestByRepo.set(row.repo, row);
  }
  let evaluatedRuns = 0, zeroEditMerged = 0, observeWouldMerge = 0, humanInterventionRuns = 0;
  let failedOrReopenedRuns = 0, unverifiedMergedRuns = 0, infraReleasedRuns = 0, reopened7d = 0;
  let gradeA = 0, gradeB = 0, gradeC = 0, countsValid = true;
  const byRepo = [...latestByRepo.values()].map(row => {
    const q = row.quality || {};
    const evalCount = Math.max(0, Number(q.evaluated_runs ?? 0));
    const rawMergedClean = Number(q.zero_edit_merged_runs ?? q.merged_zero_edit_runs ?? 0);
    const rawWouldMergeClean = Number(q.observe_would_merge_runs ?? q.would_merge_prs ?? 0);
    if (rawMergedClean < 0 || rawWouldMergeClean < 0 || rawMergedClean + rawWouldMergeClean > evalCount) countsValid = false;
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
  const apTargets = AUTOPILOT_ZERO_EDIT_TARGETS;
  const apMeets = countsValid && rawMergedZeroEditPct !== null && rawMergedZeroEditPct >= apTargets.target_min_pct && reopened7d === 0;
  return {
    targets: { autopilot_zero_edit: apTargets },
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
