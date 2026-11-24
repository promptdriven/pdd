// Generated from prompts/cli/metrics-model.prompt.md (sha256: 965e27a4c6b5c07204070f858cb6848c0a92c8267ff0ffd4008e02f35eb3193c).
import {
  buildFunnelSummary,
  computeStageFunnel,
  evaluateMatureCohort,
  extractGraphQlReopenedEvents,
  fmtPct,
  localAnchorUtcMs,
  localDateParts,
  resolveStandupWindow,
  validateTimezone,
} from './autopilot/metrics/funnel-cohort.mjs';
import {
  formatInvestigationMarkdown,
  investigateIncidents,
} from './autopilot/investigator/investigator.mjs';

export {
  buildFunnelSummary,
  computeStageFunnel,
  evaluateMatureCohort,
  extractGraphQlReopenedEvents,
  formatInvestigationMarkdown,
  investigateIncidents,
  localAnchorUtcMs,
  resolveStandupWindow,
};

/** Build a pure read-only standup/report investigation summary across all 4 Ladder-of-Fixes buckets. */
export async function buildStandupInvestigationSummary({
  incidents = [],
  repo = null,
  date = null,
  timezone = 'America/Los_Angeles',
  now = Date.now,
  knownFingerprints = null,
  filedFingerprints = null,
  secrets = [],
} = {}) {
  const report = await investigateIncidents({
    incidents,
    repo,
    date,
    timezone,
    now,
    knownFingerprints,
    filedFingerprints,
    secrets,
    writeIssues: false,
  });
  return {
    report,
    markdown: formatInvestigationMarkdown(report, { secrets }),
  };
}

export const SKILLS = Object.freeze(['small-change', 'bug', 'feature']);
export const GATES = Object.freeze(['runtime', 'vectors', 'formal', 'suite', 'review', 'ci']);
export const PR_GATES = Object.freeze(['suite', 'review', 'ci', 'e2e']);
export const PROMPT_CHECKS = Object.freeze(['runtime', 'vectors', 'formal']);

const ALL_GATES = Object.freeze([...GATES, 'e2e']);
const DEFAULT_TARGETS = Object.freeze({ convMinPct: 90, maxRegressionPct: 0, label: null });
const REPO_PATTERN = /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/;
const VALID_VIEWS = new Set(['overview', 'stages', 'skills', 'full']);
const VALID_FLAKE_OUTCOMES = new Set(['flaked-then-passed', 'reproduced-red', 'base-test-red']);
const DEFAULT_FLAKE_WINDOW_DAYS = 7;
const DEFAULT_FLAKE_THRESHOLD = 3;
const DAY_MS = 86_400_000;
const MAX_DATE_MS = 8_640_000_000_000_000;
const validDateMs = ms => typeof ms === 'number' && Number.isFinite(ms) && Math.abs(ms) <= MAX_DATE_MS;
const nonNegativeSafeInt = value => (Number.isSafeInteger(value) && value >= 0 ? value : 0);

function modelError(code, message) {
  return Object.assign(new Error(message), { code });
}

function isPlainObject(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function positiveInt(value) {
  return Number.isSafeInteger(value) && value > 0;
}

export function validateRepoName(repo) {
  if (typeof repo !== 'string' || !REPO_PATTERN.test(repo.trim())) {
    throw modelError('invalid-repo', `Invalid repository "${repo ?? ''}". Expected OWNER/REPO.`);
  }
  const trimmed = repo.trim();
  const [owner, name] = trimmed.split('/');
  if (owner === '.' || owner === '..' || name === '.' || name === '..') {
    throw modelError('invalid-repo', `Invalid repository "${repo}". Expected OWNER/REPO.`);
  }
  return trimmed;
}

function parseTimestampMs(value, fallback = null) {
  if (typeof value === 'number' && Number.isFinite(value)) return value;
  if (typeof value === 'string' && value.trim()) {
    const ms = Date.parse(value);
    if (Number.isFinite(ms)) return ms;
  }
  return fallback;
}

function validateCalendarDate(date) {
  if (typeof date !== 'string' || !/^\d{4}-\d{2}-\d{2}$/.test(date.trim())) {
    throw modelError('invalid-date', `Invalid date "${date ?? ''}". Expected YYYY-MM-DD.`);
  }
  const trimmed = date.trim();
  const [y, m, d] = trimmed.split('-').map(Number);
  const probe = new Date(Date.UTC(y, m - 1, d));
  if (probe.getUTCFullYear() !== y || probe.getUTCMonth() !== m - 1 || probe.getUTCDate() !== d) {
    throw modelError('invalid-date', `Invalid calendar date "${trimmed}". Expected YYYY-MM-DD.`);
  }
  return { text: trimmed, year: y, month: m, day: d };
}

function localMidnightUtcMs(year, month, day, timezone) {
  return localAnchorUtcMs(year, month, day, 0, timezone);
}

function formatShortDate(ms, timezone) {
  return new Intl.DateTimeFormat('en-US', {
    timeZone: timezone,
    weekday: 'short',
    month: 'short',
    day: 'numeric',
  }).format(new Date(ms));
}

function formatShortMonth(ms, timezone) {
  return new Intl.DateTimeFormat('en-US', {
    timeZone: timezone,
    month: 'short',
  }).format(new Date(ms));
}

function normalizeTargets(raw) {
  const obj = isPlainObject(raw) ? raw : {};
  const convMinPct = typeof obj.convMinPct === 'number' && Number.isFinite(obj.convMinPct) && obj.convMinPct >= 0 && obj.convMinPct <= 100
    ? obj.convMinPct
    : DEFAULT_TARGETS.convMinPct;
  const maxRegressionPct = typeof obj.maxRegressionPct === 'number' && Number.isFinite(obj.maxRegressionPct) && obj.maxRegressionPct >= 0 && obj.maxRegressionPct <= 100
    ? obj.maxRegressionPct
    : DEFAULT_TARGETS.maxRegressionPct;
  const label = typeof obj.label === 'string' && obj.label.trim() ? obj.label.trim() : null;
  return { convMinPct, maxRegressionPct, label };
}

function buildTargetRow(targets, referenceMs, timezone) {
  const month = formatShortMonth(referenceMs, timezone);
  const label = `Target (${targets.label ?? month})`;
  const convDisplay = `>=${Number.isInteger(targets.convMinPct) ? targets.convMinPct : targets.convMinPct.toFixed(1)}%`;
  const regressionDisplay = `${targets.maxRegressionPct.toFixed(1)}%`;
  return {
    label,
    month,
    convMinPct: targets.convMinPct,
    maxRegressionPct: targets.maxRegressionPct,
    convDisplay,
    regressionDisplay,
  };
}

/** Parse either a plain `{ [repo]: value }` map or an `Array<{ repo, [valueField] }>` entry list. */
function entriesFromMapOrList(raw, valueField) {
  const pairs = [];
  if (Array.isArray(raw)) {
    for (const item of raw) {
      if (isPlainObject(item) && typeof item.repo === 'string' && REPO_PATTERN.test(item.repo.trim())) {
        pairs.push([item.repo.trim().toLowerCase(), item[valueField]]);
      }
    }
    return pairs;
  }
  if (isPlainObject(raw)) {
    for (const [key, val] of Object.entries(raw)) {
      if (typeof key === 'string' && REPO_PATTERN.test(key.trim())) {
        pairs.push([key.trim().toLowerCase(), val]);
      }
    }
  }
  return pairs;
}

export function normalizeSkill(value, hints = {}) {
  if (typeof value === 'string') {
    const clean = value.trim().toLowerCase().replace(/^pdd-/, '');
    if (SKILLS.includes(clean)) return clean;
  }
  if (hints?.pathsOnlyD === true) return 'small-change';
  if (typeof hints?.title === 'string' && /\b(?:fix|bug|regression|broken|crash|error|fail(?:ed|ing|s)?)\b/i.test(hints.title)) {
    return 'bug';
  }
  if (hints?.promptChanged === false) return 'bug';
  return 'feature';
}

export function normalizeMetricsConfig(raw) {
  const cfg = isPlainObject(raw) ? raw : {};
  const enabled = cfg.enabled !== false;
  const repos = {};
  for (const [lower, val] of entriesFromMapOrList(cfg.repos, 'enabled')) {
    if (typeof val === 'boolean') repos[lower] = val;
  }
  const repoPausedSince = {};
  for (const [lower, val] of entriesFromMapOrList(cfg.repoPausedSince, 'pausedSince')) {
    if (typeof val === 'string' && Number.isFinite(Date.parse(val))) {
      repoPausedSince[lower] = new Date(Date.parse(val)).toISOString();
    }
  }
  const pausedIntervals = Array.isArray(cfg.pausedIntervals)
    ? cfg.pausedIntervals
      .filter(item => isPlainObject(item) && typeof item.from === 'string' && Number.isFinite(Date.parse(item.from)))
      .map(item => ({
        repo: typeof item.repo === 'string' && REPO_PATTERN.test(item.repo.trim()) ? item.repo.trim().toLowerCase() : null,
        from: new Date(Date.parse(item.from)).toISOString(),
        to: typeof item.to === 'string' && Number.isFinite(Date.parse(item.to)) ? new Date(Date.parse(item.to)).toISOString() : null,
      }))
    : [];
  const pausedSince = typeof cfg.pausedSince === 'string' && Number.isFinite(Date.parse(cfg.pausedSince))
    ? new Date(Date.parse(cfg.pausedSince)).toISOString()
    : null;
  const updatedAt = typeof cfg.updatedAt === 'string' && Number.isFinite(Date.parse(cfg.updatedAt))
    ? new Date(Date.parse(cfg.updatedAt)).toISOString()
    : null;
  const targets = normalizeTargets(cfg.targets);
  return { enabled, repos, pausedSince, repoPausedSince, pausedIntervals, targets, updatedAt };
}

export function isMetricsEnabled(config, repo = null) {
  const cfg = normalizeMetricsConfig(config);
  if (typeof repo === 'string' && repo.trim()) {
    const lower = repo.trim().toLowerCase();
    if (typeof cfg.repos[lower] === 'boolean') return cfg.repos[lower];
  }
  return cfg.enabled;
}

export function applyMetricsToggle(first, second) {
  const singleInput = second === undefined && isPlainObject(first) && ('action' in first || 'config' in first);
  const rawConfig = singleInput ? first.config : first;
  const opts = singleInput ? first : (second ?? {});
  const action = typeof opts.action === 'string' ? opts.action.trim().toLowerCase() : '';
  if (action !== 'on' && action !== 'off') {
    throw modelError('invalid-action', `Invalid metrics toggle action "${opts.action ?? ''}". Expected "on" or "off".`);
  }
  const atMs = opts.at === undefined ? 0 : parseTimestampMs(opts.at, null);
  if (atMs === null) {
    throw modelError('invalid-at', `Invalid timestamp "${opts.at ?? ''}".`);
  }
  const atIso = new Date(atMs).toISOString();
  const cfg = normalizeMetricsConfig(rawConfig);
  const repos = { ...cfg.repos };
  const repoPausedSince = { ...cfg.repoPausedSince };
  const intervals = cfg.pausedIntervals.map(item => ({ ...item }));
  const targets = { ...cfg.targets };

  if (opts.repo !== undefined && opts.repo !== null && opts.repo !== '') {
    const valid = validateRepoName(opts.repo);
    const lower = valid.toLowerCase();
    if (action === 'off') {
      repos[lower] = false;
      if (!repoPausedSince[lower]) repoPausedSince[lower] = atIso;
      if (!intervals.some(i => i.repo === lower && i.to === null)) {
        intervals.push({ repo: lower, from: atIso, to: null });
      }
    } else {
      if (cfg.enabled) delete repos[lower];
      else repos[lower] = true;
      delete repoPausedSince[lower];
      for (const interval of intervals) {
        if (interval.repo === lower && interval.to === null) interval.to = atIso;
      }
    }
    return {
      enabled: cfg.enabled,
      repos,
      pausedSince: cfg.pausedSince,
      repoPausedSince,
      pausedIntervals: intervals,
      targets,
      updatedAt: atIso,
    };
  }

  if (action === 'off') {
    const pausedSince = cfg.pausedSince ?? atIso;
    if (!intervals.some(i => i.repo === null && i.to === null)) {
      intervals.push({ repo: null, from: atIso, to: null });
    }
    return {
      enabled: false,
      repos,
      pausedSince,
      repoPausedSince,
      pausedIntervals: intervals,
      targets,
      updatedAt: atIso,
    };
  }

  for (const interval of intervals) {
    if (interval.repo === null && interval.to === null) interval.to = atIso;
  }
  return {
    enabled: true,
    repos,
    pausedSince: null,
    repoPausedSince,
    pausedIntervals: intervals,
    targets,
    updatedAt: atIso,
  };
}

function isTimestampPaused(ms, repoLower, config) {
  if (!Number.isFinite(ms)) return false;
  for (const interval of config.pausedIntervals) {
    if (interval.repo !== null && interval.repo !== repoLower) continue;
    const fromMs = Date.parse(interval.from);
    const toMs = interval.to ? Date.parse(interval.to) : Infinity;
    if (ms >= fromMs && ms < toMs) return true;
  }
  if (!config.enabled && config.pausedSince) {
    const fromMs = Date.parse(config.pausedSince);
    if (Number.isFinite(fromMs) && ms >= fromMs) return true;
  }
  if (config.repos[repoLower] === false && config.repoPausedSince[repoLower]) {
    const fromMs = Date.parse(config.repoPausedSince[repoLower]);
    if (Number.isFinite(fromMs) && ms >= fromMs) return true;
  }
  return false;
}

function isRunPaused(runStartMs, runAtMs, status, repoLower, config) {
  if (isTimestampPaused(runStartMs, repoLower, config)) return true;
  if (status !== 'running' && isTimestampPaused(runAtMs, repoLower, config)) return true;
  return false;
}

function normalizeGateState(gate, rawValue) {
  const val = typeof rawValue === 'string' ? rawValue.trim().toLowerCase() : '';
  if (!val) return 'na';
  switch (gate) {
    case 'runtime':
    case 'vectors':
      if (val === 'pass') return 'pass';
      if (val === 'fail') return 'fail';
      return 'na';
    case 'formal':
      if (val === 'proved' || val === 'bounded' || val === 'pass') return 'pass';
      if (val === 'failed' || val === 'fail') return 'fail';
      return 'na';
    case 'suite':
      if (val === 'pass') return 'pass';
      if (val === 'fail' || val === 'broken' || val === 'hung') return 'fail';
      if (val === 'running') return 'running';
      return 'na';
    case 'review':
      if (val === 'pass') return 'pass';
      if (val === 'fail') return 'fail';
      if (val === 'running') return 'running';
      return 'na';
    case 'ci':
      if (val === 'green' || val === 'pass') return 'pass';
      if (val === 'red' || val === 'fail') return 'fail';
      if (val === 'pending' || val === 'running') return 'running';
      return 'na';
    case 'e2e':
      if (val === 'green' || val === 'pass') return 'pass';
      if (val === 'red' || val === 'fail' || val === 'broken' || val === 'hung') return 'fail';
      if (val === 'pending' || val === 'running') return 'running';
      return 'na';
    default:
      return 'na';
  }
}

function normalizeGateCounts(rawCounts) {
  if (!isPlainObject(rawCounts)) return {};
  const result = {};
  for (const check of PROMPT_CHECKS) {
    const pair = rawCounts[check];
    if (!isPlainObject(pair)) continue;
    const passed = pair.passed;
    const total = pair.total;
    if (Number.isSafeInteger(passed) && Number.isSafeInteger(total) && total > 0 && passed >= 0 && passed <= total) {
      result[check] = { passed, total };
    }
  }
  return result;
}

function normalizeStatus(rawStatus) {
  const s = typeof rawStatus === 'string' ? rawStatus.trim().toLowerCase() : '';
  if (s === 'merged' || s === 'would-merge' || s === 'running' || s === 'needs-person') return s;
  if (s === 'ended' || s === 'failed' || s === 'released' || s === 'stopped' || s === 'abandoned') return s;
  return 'ended';
}

function itemRank(item) {
  if (item.merged) return 6;
  if (item.status === 'would-merge') return 4;
  if (item.status === 'running') return 3;
  if (item.status === 'needs-person') return 2;
  return 1;
}

function formatRatioDisplay(numerator, denominator) {
  if (denominator <= 0) return { pct: null, display: '0 (n/a)' };
  const pct = Math.round((numerator / denominator) * 1000) / 10;
  return { pct, display: `${numerator} (${pct.toFixed(1)}%)` };
}

function computeMedianMinutes(durations) {
  const valid = durations.filter(d => typeof d === 'number' && Number.isFinite(d) && d > 0).sort((a, b) => a - b);
  if (valid.length === 0) return { medianMinutes: null, medianDisplay: 'n/a' };
  const mid = Math.floor(valid.length / 2);
  const raw = valid.length % 2 === 1 ? valid[mid] : (valid[mid - 1] + valid[mid]) / 2;
  const rounded = Math.max(1, Math.round(raw));
  return { medianMinutes: rounded, medianDisplay: `${rounded}m` };
}

/** Build explicit human-readable repository scope label (e.g. `pdd + pocket`). */
function formatRepoNamesLabel(reposList) {
  if (reposList.length === 0) return '0 repos';
  const shortCounts = new Map();
  for (const repo of reposList) {
    const shortLower = repo.split('/')[1].toLowerCase();
    shortCounts.set(shortLower, (shortCounts.get(shortLower) ?? 0) + 1);
  }
  return reposList
    .map(repo => {
      const shortName = repo.split('/')[1];
      return shortCounts.get(shortName.toLowerCase()) === 1 ? shortName : repo;
    })
    .join(' + ');
}

function indexPrStates(rawPrStates, excludedRepos) {
  const map = new Map();
  if (!Array.isArray(rawPrStates)) return map;
  for (const entry of rawPrStates) {
    if (!isPlainObject(entry) || typeof entry.repo !== 'string' || !REPO_PATTERN.test(entry.repo.trim())) continue;
    if (!positiveInt(entry.pr)) continue;
    const repoLower = entry.repo.trim().toLowerCase();
    if (excludedRepos.has(repoLower)) continue;
    map.set(`${repoLower}#${entry.pr}`, {
      merged: typeof entry.merged === 'boolean' ? entry.merged : null,
      mergedAtMs: parseTimestampMs(entry.mergedAt, null),
      state: typeof entry.state === 'string' ? entry.state.trim().toUpperCase() : null,
    });
  }
  return map;
}

function earliestIso(a, b) {
  const aMs = parseTimestampMs(a, null);
  const bMs = parseTimestampMs(b, null);
  if (aMs === null && bMs === null) return null;
  if (aMs === null) return new Date(bMs).toISOString();
  if (bMs === null) return new Date(aMs).toISOString();
  return new Date(Math.min(aMs, bMs)).toISOString();
}

function indexRegressions(rawRegressions, excludedRepos) {
  const byPr = new Map();
  const byIssue = new Map();
  if (!Array.isArray(rawRegressions)) return { byPr, byIssue };
  const mergeSignal = (map, key, entry) => {
    const prev = map.get(key) ?? {
      reopened: false,
      reverted: false,
      regressionIssues: new Set(),
      reopenedAt: null,
      revertedAt: null,
      regressionIssueAt: null,
      detectedAt: null,
      signals: [],
    };
    if (entry.reopened === true) prev.reopened = true;
    if (entry.reverted === true) prev.reverted = true;
    if (Array.isArray(entry.regressionIssues)) {
      for (const n of entry.regressionIssues) {
        if (positiveInt(n)) prev.regressionIssues.add(n);
      }
    }
    prev.reopenedAt = earliestIso(prev.reopenedAt, entry.reopenedAt);
    prev.revertedAt = earliestIso(prev.revertedAt, entry.revertedAt);
    prev.regressionIssueAt = earliestIso(prev.regressionIssueAt, entry.regressionIssueAt);
    prev.detectedAt = earliestIso(prev.detectedAt, entry.detectedAt);
    if (Array.isArray(entry.signals)) {
      for (const sig of entry.signals) {
        if (!isPlainObject(sig) || typeof sig.kind !== 'string') continue;
        const at = earliestIso(sig.at, null);
        if (sig.kind === 'reopened') prev.reopenedAt = earliestIso(prev.reopenedAt, at);
        if (sig.kind === 'revert') prev.revertedAt = earliestIso(prev.revertedAt, at);
        if (sig.kind === 'reference') prev.regressionIssueAt = earliestIso(prev.regressionIssueAt, at);
        prev.detectedAt = earliestIso(prev.detectedAt, at);
        prev.signals.push({
          kind: sig.kind,
          level: typeof sig.level === 'string' ? sig.level : 'proven',
          at,
          url: typeof sig.url === 'string' ? sig.url : null,
        });
      }
    }
    prev.detectedAt = earliestIso(
      prev.detectedAt,
      earliestIso(prev.reopenedAt, earliestIso(prev.revertedAt, prev.regressionIssueAt)),
    );
    map.set(key, prev);
  };
  for (const entry of rawRegressions) {
    if (!isPlainObject(entry) || typeof entry.repo !== 'string' || !REPO_PATTERN.test(entry.repo.trim())) continue;
    const repoLower = entry.repo.trim().toLowerCase();
    if (excludedRepos.has(repoLower)) continue;
    if (positiveInt(entry.pr)) mergeSignal(byPr, `${repoLower}#${entry.pr}`, entry);
    const issues = [
      ...(positiveInt(entry.issue) ? [entry.issue] : []),
      ...(Array.isArray(entry.issues) ? entry.issues.filter(positiveInt) : []),
    ];
    for (const issue of issues) mergeSignal(byIssue, `${repoLower}#${issue}`, entry);
  }
  return { byPr, byIssue };
}

function resolveItemRegression(item, regIndex) {
  const prReg = item.pr ? regIndex.byPr.get(`${item.repoLower}#${item.pr}`) : null;
  const issueReg = regIndex.byIssue.get(`${item.repoLower}#${item.issue}`) ?? null;
  const hasReopened = item.reopened === true || prReg?.reopened === true || issueReg?.reopened === true;
  const hasReverted = item.reverted === true || prReg?.reverted === true || issueReg?.reverted === true;
  const issueSet = new Set(item.regressionIssues ?? []);
  for (const n of prReg?.regressionIssues ?? []) issueSet.add(n);
  for (const n of issueReg?.regressionIssues ?? []) issueSet.add(n);
  const regressionIssueNumbers = [...issueSet].sort((a, b) => a - b);
  const hasRegression = hasReopened || hasReverted || regressionIssueNumbers.length > 0;
  const reopenedAt = earliestIso(item.reopenedAt, earliestIso(prReg?.reopenedAt, issueReg?.reopenedAt));
  const revertedAt = earliestIso(item.revertedAt, earliestIso(prReg?.revertedAt, issueReg?.revertedAt));
  const regressionIssueAt = earliestIso(item.regressionIssueAt, earliestIso(prReg?.regressionIssueAt, issueReg?.regressionIssueAt));
  const detectedAt = earliestIso(
    earliestIso(item.detectedAt, earliestIso(prReg?.detectedAt, issueReg?.detectedAt)),
    earliestIso(reopenedAt, earliestIso(revertedAt, regressionIssueAt)),
  );
  const signalSeen = new Set();
  const regressionSignals = [];
  for (const sig of [...(prReg?.signals ?? []), ...(issueReg?.signals ?? [])]) {
    const key = `${sig.kind}|${sig.level}|${sig.at ?? ''}|${sig.url ?? ''}`;
    if (signalSeen.has(key)) continue;
    signalSeen.add(key);
    regressionSignals.push(sig);
  }
  return {
    hasReopened,
    hasReverted,
    regressionIssueNumbers,
    hasRegression,
    reopenedAt,
    revertedAt,
    regressionIssueAt,
    detectedAt,
    regressionSignals,
  };
}

function selectWindowIssues(normalizedRuns, windowDef, nowMs, regIndex) {
  const byIssue = new Map();
  for (const run of normalizedRuns) {
    const inRange = (run.atMs >= windowDef.startMs && run.atMs <= windowDef.endMs)
      || (run.mergedAtMs !== null && run.mergedAtMs >= windowDef.startMs && run.mergedAtMs <= windowDef.endMs)
      || (run.status === 'running' && nowMs >= windowDef.startMs && nowMs <= windowDef.endMs && run.startMs <= windowDef.endMs);
    if (!inRange) continue;
    // Do not retroactively attribute a later merge to an earlier historical --date window.
    const mergedAfterWindow = run.merged && run.mergedAtMs !== null && run.mergedAtMs > windowDef.endMs;
    const effective = mergedAfterWindow
      ? { ...run, merged: false, mwmFlag: false, status: run.rawStatus === 'merged' ? 'ended' : run.rawStatus }
      : run;
    for (const issueNumber of effective.issues) {
      const key = `${effective.repoLower}#${issueNumber}`;
      const prev = byIssue.get(key);
      if (
        !prev
        || itemRank(effective) > itemRank(prev)
        || (itemRank(effective) === itemRank(prev) && effective.atMs >= prev.atMs)
      ) {
        const candidate = { ...effective, issue: issueNumber };
        const reg = resolveItemRegression(candidate, regIndex);
        byIssue.set(key, { ...candidate, ...reg });
      }
    }
  }
  return [...byIssue.values()];
}

function resolveOpenCount(repoLowers, openMap, openNumbersMap) {
  const hasOpenData = openMap !== null || openNumbersMap.size > 0;
  if (!hasOpenData) return { open: null, openDisplay: '?' };
  if (repoLowers.length === 0) return { open: 0, openDisplay: '0' };
  let sum = 0;
  for (const lower of repoLowers) {
    const numeric = openMap?.get(lower);
    if (typeof numeric === 'number' && Number.isInteger(numeric) && numeric >= 0) {
      sum += numeric;
      continue;
    }
    if (openNumbersMap.has(lower)) {
      sum += openNumbersMap.get(lower).size;
      continue;
    }
    return { open: null, openDisplay: '?' };
  }
  return { open: sum, openDisplay: String(sum) };
}

function resolveWindowPool(repoLowers, windowDef, items, openMap, openNumbersMap, closedIssues) {
  const hasOpenData = openMap !== null || openNumbersMap.size > 0;
  if (!hasOpenData) return { pool: null, poolDisplay: '?' };
  if (repoLowers.length === 0) return { pool: 0, poolDisplay: '0' };
  let totalPool = 0;
  for (const lower of repoLowers) {
    const repoItems = items.filter(i => i.repoLower === lower);
    const takenSet = new Set(repoItems.map(i => i.issue));
    const closedSet = new Set();
    for (const closed of closedIssues) {
      if (closed.repoLower === lower && closed.closedAtMs >= windowDef.startMs && closed.closedAtMs <= windowDef.endMs) {
        closedSet.add(closed.issue);
      }
    }
    const openCount = openMap?.get(lower);
    const hasCount = typeof openCount === 'number' && Number.isInteger(openCount) && openCount >= 0;
    const openSet = openNumbersMap.get(lower) ?? null;
    if (!hasCount && !openSet) return { pool: null, poolDisplay: '?' };
    if (openSet) {
      const effectiveOpenCount = hasCount ? openCount : openSet.size;
      const unlistedOpen = Math.max(0, effectiveOpenCount - openSet.size);
      const union = new Set([...openSet, ...closedSet, ...takenSet]);
      totalPool += Math.max(takenSet.size, union.size + unlistedOpen);
    } else {
      const mergedSet = new Set(repoItems.filter(i => i.merged).map(i => i.issue));
      const closedOrMerged = new Set([...closedSet, ...mergedSet]);
      totalPool += Math.max(takenSet.size, openCount + closedOrMerged.size);
    }
  }
  return { pool: totalPool, poolDisplay: String(totalPool) };
}

function summarizeOverviewRow(key, label, windowDef, items, repoLowers, openMap, openNumbersMap, closedIssues, regressionsComplete = true) {
  const { open, openDisplay } = resolveOpenCount(repoLowers, openMap, openNumbersMap);
  const { pool, poolDisplay } = resolveWindowPool(repoLowers, windowDef, items, openMap, openNumbersMap, closedIssues);
  const taken = items.length;
  const prCreated = items.filter(i => i.prCreated).length;
  const mergedItems = items.filter(i => i.merged);
  const merged = mergedItems.length;
  const { pct: convPct, display: mergedDisplay } = formatRatioDisplay(merged, taken);
  const mwm = items.filter(i => i.mwmFlag).length;
  const { display: mwmDisplay } = formatRatioDisplay(mwm, taken);
  const regressions = mergedItems.filter(i => i.hasRegression).length;
  let { pct: regressionsPct, display: regressionsDisplay } = formatRatioDisplay(regressions, merged);
  if (!regressionsComplete && merged > 0) {
    if (regressions === 0) {
      regressionsPct = null;
      regressionsDisplay = '?';
    } else {
      regressionsDisplay = `${regressions}+ (${regressionsPct.toFixed(1)}%+)`;
    }
  }
  const funnel = buildFunnelSummary({
    pool,
    poolDisplay,
    taken,
    pr: prCreated,
    merged,
    regressions,
    regressionsComplete,
  });
  return {
    key,
    label,
    startAt: new Date(windowDef.startMs).toISOString(),
    endAt: new Date(windowDef.endMs).toISOString(),
    pool,
    poolDisplay,
    open,
    openDisplay,
    taken,
    prCreated,
    merged,
    convPct,
    mergedDisplay,
    mwm,
    mwmDisplay,
    regressions,
    regressionsPct,
    regressionsDisplay,
    funnel,
  };
}

function formatBreakdownSummary(prefix, total, breakdown) {
  if (total === 0) return `${prefix} (0): none`;
  return `${prefix} (${total}): ${breakdown.map(b => `${b.count} ${b.reason}`).join(' · ')}`;
}

function summarizeBeforePr(items) {
  const order = ['running', 'needs-person', 'stopped'];
  const counts = Object.fromEntries(order.map(k => [k, 0]));
  let total = 0;
  for (const item of items) {
    if (item.prCreated) continue;
    total++;
    if (item.status === 'running') counts.running++;
    else if (item.status === 'needs-person') counts['needs-person']++;
    else counts.stopped++;
  }
  const breakdown = order.filter(k => counts[k] > 0).map(reason => ({ reason, count: counts[reason] }));
  return { total, breakdown, summary: formatBreakdownSummary('Before PR', total, breakdown) };
}

function summarizeUnmergedPrs(items) {
  const order = [
    'failed runtime',
    'failed vectors',
    'failed formal',
    'failed suite',
    'failed review',
    'failed ci',
    'failed e2e',
    'needs-person',
    'open/draft',
    'closed unmerged',
  ];
  const counts = Object.fromEntries(order.map(k => [k, 0]));
  let total = 0;
  for (const item of items) {
    if (!item.prCreated || item.merged) continue;
    total++;
    const failedGate = ALL_GATES.find(g => item.gates[g] === 'fail');
    if (failedGate) counts[`failed ${failedGate}`]++;
    else if (item.status === 'needs-person') counts['needs-person']++;
    else if (item.prStateCode === 'CLOSED') counts['closed unmerged']++;
    else counts['open/draft']++;
  }
  const breakdown = order.filter(k => counts[k] > 0).map(reason => ({ reason, count: counts[reason] }));
  return { total, breakdown, summary: formatBreakdownSummary('Unmerged PRs', total, breakdown) };
}

function summarizePrGates(prItems) {
  const totalPrs = prItems.length;
  const countPass = gate => {
    const passed = prItems.filter(i => i.gates[gate] === 'pass').length;
    return { passed, total: totalPrs, display: totalPrs === 0 ? '-' : `${passed}/${totalPrs}` };
  };
  const suite = countPass('suite');
  const review = countPass('review');
  const ci = countPass('ci');
  const e2ePresent = prItems.some(i => i.gates.e2e !== 'na');
  const e2eBase = countPass('e2e');
  const e2e = { ...e2eBase, present: e2ePresent };
  const summary = totalPrs === 0
    ? 'PR Gates (of 0 PRs): none'
    : `PR Gates (of ${totalPrs} ${totalPrs === 1 ? 'PR' : 'PRs'}): Suite ${suite.display} · Review ${review.display} · CI ${ci.display}${e2ePresent ? ` · E2E ${e2e.display}` : ''}`;
  return { totalPrs, suite, review, ci, e2e, summary };
}

function summarizePromptChecks(prItems) {
  // Grade strictly at PR granularity (excluding not-run/na and raw vector test-case counts).
  const promptItems = prItems.filter(item =>
    item.promptChanged === true
    || PROMPT_CHECKS.some(g => item.gates[g] === 'pass' || item.gates[g] === 'fail'),
  );
  const promptPrs = promptItems.length;
  const checks = {};
  for (const g of PROMPT_CHECKS) {
    let passed = 0;
    let total = 0;
    for (const item of promptItems) {
      if (item.gates[g] === 'pass') {
        passed += 1;
        total += 1;
      } else if (item.gates[g] === 'fail') {
        total += 1;
      }
    }
    checks[g] = { passed, total, display: total === 0 ? '-' : `${passed}/${total}` };
  }
  const summary = promptPrs === 0
    ? 'Prompt Checks (of 0 prompt PRs): none'
    : `Prompt Checks (of ${promptPrs} ${promptPrs === 1 ? 'prompt PR' : 'prompt PRs'}): Runtime ${checks.runtime.display} · Vectors ${checks.vectors.display} · Formal ${checks.formal.display}`;
  return { promptPrs, runtime: checks.runtime, vectors: checks.vectors, formal: checks.formal, summary };
}

function summarizeRegressionsBreakdown(mergedItems, regressionsComplete = true) {
  const regressed = mergedItems.filter(i => i.hasRegression);
  const total = regressed.length;
  const reopened = regressed.filter(i => i.hasReopened).length;
  const reverted = regressed.filter(i => i.hasReverted).length;
  const issueSet = new Set();
  const events = [];
  for (const item of regressed) {
    for (const n of item.regressionIssueNumbers) issueSet.add(n);
    events.push({
      repo: item.repo,
      pr: item.pr,
      issue: item.issue,
      reopened: item.hasReopened,
      reverted: item.hasReverted,
      regressionIssues: item.regressionIssueNumbers,
      reopenedAt: item.reopenedAt ?? null,
      revertedAt: item.revertedAt ?? null,
      regressionIssueAt: item.regressionIssueAt ?? null,
      detectedAt: item.detectedAt ?? null,
      signals: item.regressionSignals ?? [],
    });
  }
  const regressionIssues = [...issueSet].sort((a, b) => a - b);
  const regressionIssueCount = regressionIssues.length;
  const issueLabel = regressionIssueCount === 1 ? 'regression issue' : 'regression issues';
  const issueList = regressionIssues.length > 0 ? ` (${regressionIssues.map(n => `#${n}`).join(', ')})` : '';
  const suffix = regressionsComplete ? '' : ' (scan incomplete)';
  const summary = `Regressions (${total}): ${reopened} reopened · ${reverted} reverted · ${regressionIssueCount} ${issueLabel}${issueList}${suffix}`;
  return { total, reopened, reverted, regressionIssueCount, regressionIssues, complete: regressionsComplete, events, summary };
}

function summarizeStages(windowDef, items, regressionsComplete = true, poolInfo = { pool: null, poolDisplay: '?' }) {
  const gates = {};
  for (const gate of GATES) {
    let passed = 0;
    let applicable = 0;
    for (const item of items) {
      const state = item.gates[gate];
      if (state === 'pass') {
        passed++;
        applicable++;
      } else if (state === 'fail') {
        applicable++;
      }
    }
    gates[gate] = {
      passed,
      applicable,
      display: applicable === 0 ? '-' : `${passed}/${applicable}`,
    };
  }
  const taken = items.length;
  const prItems = items.filter(i => i.prCreated);
  const pr = prItems.length;
  const mergedItems = items.filter(i => i.merged);
  const merged = mergedItems.length;
  const mwmItems = items.filter(i => i.mwmFlag);
  const mwm = mwmItems.length;
  const reopen = mwmItems.filter(i => i.hasRegression).length;

  const beforePr = summarizeBeforePr(items);
  const unmergedPrs = summarizeUnmergedPrs(items);
  const prGates = summarizePrGates(prItems);
  const promptChecks = summarizePromptChecks(prItems);
  const regressions = summarizeRegressionsBreakdown(mergedItems, regressionsComplete);

  const bucketOrder = [
    'running',
    'needs-person',
    'failed runtime',
    'failed vectors',
    'failed formal',
    'failed suite',
    'failed review',
    'failed ci',
    'ended',
  ];
  const counts = Object.fromEntries(bucketOrder.map(b => [b, 0]));
  let nonMergedTotal = 0;
  for (const item of items) {
    if (item.mwmFlag) continue;
    nonMergedTotal++;
    if (item.status === 'running') {
      counts.running++;
      continue;
    }
    if (item.status === 'needs-person') {
      counts['needs-person']++;
      continue;
    }
    const failedGate = GATES.find(g => item.gates[g] === 'fail');
    if (failedGate) counts[`failed ${failedGate}`]++;
    else counts.ended++;
  }
  const breakdown = bucketOrder.filter(b => counts[b] > 0).map(b => ({ reason: b, count: counts[b] }));
  const nonMergedSummary = formatBreakdownSummary('Non-merged', nonMergedTotal, breakdown);

  const funnel = buildFunnelSummary({
    pool: poolInfo?.pool ?? null,
    poolDisplay: poolInfo?.poolDisplay ?? '?',
    taken,
    pr,
    merged,
    regressions: regressions.total,
    regressionsComplete,
  });

  const stageFunnel = computeStageFunnel(
    items.map(item => ({
      repo: item.repo,
      issue: item.issue,
      status: item.status,
      merged: item.merged,
      pr: item.pr,
      prCreated: item.prCreated,
      wouldMerge: item.status === 'would-merge' && !item.merged,
      regressed: item.hasRegression,
      reopened: item.hasReopened,
      reverted: item.hasReverted,
      regressionIssues: item.regressionIssueNumbers,
      gates: item.gates,
      at: item.atMs,
      mergedAt: item.mergedAtMs,
    })),
    { gates: GATES },
  );
  const sf = stageFunnel;
  const stageFunnelLine = `Stage funnel: ${sf.counts.considered} considered -> ${sf.counts.eligible} eligible (${fmtPct(sf.rates.eligiblePct)}) -> ${sf.counts.claimed} claimed (${fmtPct(sf.rates.takenPct)}) -> ${sf.counts.pr} PRs (${fmtPct(sf.rates.prPct)}) -> ${sf.counts.merged} merged (${fmtPct(sf.rates.mergedPct)} of PRs, ${fmtPct(sf.rates.mergedOfClaimedPct)} of claimed)`;

  return {
    window: { key: windowDef.key, label: windowDef.label },
    taken,
    pr,
    merged,
    mwm,
    funnel,
    stageFunnel,
    stageFunnelLine,
    beforePr,
    unmergedPrs,
    prGates,
    promptChecks,
    regressions,
    gates,
    reopen,
    nonMerged: { total: nonMergedTotal, breakdown },
    nonMergedSummary,
  };
}

function summarizeSkillBucket(skill, matching) {
  const taken = matching.length;
  const prCreated = matching.filter(i => i.prCreated).length;
  const merged = matching.filter(i => i.merged).length;
  const { pct: convPct, display: mergedDisplay } = formatRatioDisplay(merged, taken);
  const mwmItems = matching.filter(i => i.mwmFlag);
  const mwm = mwmItems.length;
  const { display: mwmDisplay } = formatRatioDisplay(mwm, taken);
  const durationItems = matching.filter(i => i.merged || i.mwmFlag);
  const { medianMinutes, medianDisplay } = computeMedianMinutes(durationItems.map(i => i.durationMinutes));
  return { skill, taken, prCreated, merged, convPct, mergedDisplay, mwm, mwmDisplay, medianMinutes, medianDisplay };
}

function summarizeSkills(windowDef, items) {
  const rows = SKILLS.map(skill => summarizeSkillBucket(skill, items.filter(i => i.skill === skill)));
  const total = summarizeSkillBucket('Total', items);
  return {
    window: { key: windowDef.key, label: windowDef.label },
    rows,
    total,
  };
}

function summarizeMetricsRecurringFlakes({
  recurringFlakes,
  flakeEntries,
  refMs,
  windowDays = DEFAULT_FLAKE_WINDOW_DAYS,
  threshold = DEFAULT_FLAKE_THRESHOLD,
  excludedRepos,
  repoFilterLower,
}) {
  const days = typeof windowDays === 'number' && Number.isFinite(windowDays) && windowDays > 0
    ? windowDays
    : DEFAULT_FLAKE_WINDOW_DAYS;
  const minCount = positiveInt(threshold) ? threshold : DEFAULT_FLAKE_THRESHOLD;

  if (isPlainObject(recurringFlakes) && Array.isArray(recurringFlakes.recurring)) {
    const filtered = recurringFlakes.recurring
      .filter(item => {
        if (!isPlainObject(item) || typeof item.target !== 'string' || !item.target.trim()) return false;
        const rLower = typeof item.repo === 'string' && item.repo.trim() ? item.repo.trim().toLowerCase() : null;
        if (rLower && excludedRepos.has(rLower)) return false;
        if (repoFilterLower && rLower !== repoFilterLower) return false;
        return positiveInt(item.count) && item.count >= (positiveInt(recurringFlakes.threshold) ? recurringFlakes.threshold : minCount);
      })
      .map(item => ({
        repo: typeof item.repo === 'string' && item.repo.trim() ? item.repo.trim() : null,
        target: item.target.trim().slice(0, 200),
        count: item.count,
        outcomes: {
          'flaked-then-passed': nonNegativeSafeInt(item.outcomes?.['flaked-then-passed']),
          'reproduced-red': nonNegativeSafeInt(item.outcomes?.['reproduced-red']),
          'base-test-red': nonNegativeSafeInt(item.outcomes?.['base-test-red']),
        },
        lastSeen: typeof item.lastSeen === 'string' && validDateMs(Date.parse(item.lastSeen))
          ? new Date(Date.parse(item.lastSeen)).toISOString()
          : null,
        issues: Array.isArray(item.issues) ? [...new Set(item.issues.filter(positiveInt))].sort((a, b) => a - b) : [],
        prs: Array.isArray(item.prs) ? [...new Set(item.prs.filter(positiveInt))].sort((a, b) => a - b) : [],
      }))
      .sort((a, b) => b.count - a.count || a.target.localeCompare(b.target) || (a.repo ?? '').localeCompare(b.repo ?? ''));
    return {
      totalEntries: Number.isSafeInteger(recurringFlakes.totalEntries) && recurringFlakes.totalEntries >= 0
        ? recurringFlakes.totalEntries
        : filtered.reduce((acc, item) => acc + item.count, 0),
      windowDays: typeof recurringFlakes.windowDays === 'number' && Number.isFinite(recurringFlakes.windowDays) && recurringFlakes.windowDays > 0
        ? recurringFlakes.windowDays
        : days,
      threshold: positiveInt(recurringFlakes.threshold) ? recurringFlakes.threshold : minCount,
      recurring: filtered,
    };
  }

  const safeRefMs = validDateMs(refMs) ? refMs : 0;
  const cutoffMs = Math.max(-MAX_DATE_MS, safeRefMs - days * DAY_MS);
  const groups = new Map();
  let totalEntries = 0;

  for (const raw of Array.isArray(flakeEntries) ? flakeEntries : []) {
    if (!isPlainObject(raw)) continue;
    const outcome = typeof raw.outcome === 'string' ? raw.outcome.trim() : '';
    if (!VALID_FLAKE_OUTCOMES.has(outcome)) continue;
    const target = typeof raw.target === 'string' ? raw.target.replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 200) : '';
    if (!target) continue;
    const tsMs = parseTimestampMs(raw.ts, null);
    if (tsMs === null || !validDateMs(tsMs) || tsMs < cutoffMs || tsMs > safeRefMs) continue;
    const repo = typeof raw.repo === 'string' && REPO_PATTERN.test(raw.repo.trim()) ? raw.repo.trim() : null;
    const repoLower = repo ? repo.toLowerCase() : null;
    if (repoLower && excludedRepos.has(repoLower)) continue;
    if (repoFilterLower && repoLower !== repoFilterLower) continue;
    totalEntries += 1;

    const groupKey = `${repoLower ?? ''}\0${target.toLowerCase()}`;
    let bucket = groups.get(groupKey);
    if (!bucket) {
      bucket = {
        repo,
        target,
        count: 0,
        outcomes: { 'flaked-then-passed': 0, 'reproduced-red': 0, 'base-test-red': 0 },
        lastSeenMs: tsMs,
        lastSeen: new Date(tsMs).toISOString(),
        issues: new Set(),
        prs: new Set(),
      };
      groups.set(groupKey, bucket);
    }
    bucket.count += 1;
    bucket.outcomes[outcome] += 1;
    if (tsMs >= bucket.lastSeenMs) {
      bucket.lastSeenMs = tsMs;
      bucket.lastSeen = new Date(tsMs).toISOString();
    }
    if (positiveInt(raw.issue)) bucket.issues.add(raw.issue);
    if (positiveInt(raw.pr)) bucket.prs.add(raw.pr);
  }

  const recurring = [...groups.values()]
    .filter(bucket => bucket.count >= minCount)
    .map(bucket => ({
      repo: bucket.repo,
      target: bucket.target,
      count: bucket.count,
      outcomes: bucket.outcomes,
      lastSeen: bucket.lastSeen,
      issues: [...bucket.issues].sort((a, b) => a - b),
      prs: [...bucket.prs].sort((a, b) => a - b),
    }))
    .sort((a, b) => b.count - a.count || a.target.localeCompare(b.target) || (a.repo ?? '').localeCompare(b.repo ?? ''));

  return {
    totalEntries,
    windowDays: days,
    threshold: minCount,
    recurring,
  };
}

export function calculateAutopilotMetrics(input = {}) {
  const opts = isPlainObject(input) ? input : {};
  const view = opts.view === undefined ? 'overview' : String(opts.view).trim().toLowerCase();
  if (!VALID_VIEWS.has(view)) {
    throw modelError('invalid-view', `Invalid metrics view "${opts.view}".`);
  }
  const standup = Boolean(opts.standup);
  const timezone = validateTimezone(opts.timezone ?? (standup ? 'America/Los_Angeles' : 'UTC'));
  const nowMs = opts.now === undefined ? 0 : parseTimestampMs(opts.now, null);
  if (nowMs === null) {
    throw modelError('invalid-now', `Invalid timestamp "${opts.now ?? ''}".`);
  }
  const nowIso = new Date(nowMs).toISOString();
  const parsedDate = opts.date !== undefined && opts.date !== null && opts.date !== ''
    ? validateCalendarDate(opts.date)
    : null;
  const repoFilterCanonical = opts.repoFilter !== undefined && opts.repoFilter !== null && opts.repoFilter !== ''
    ? validateRepoName(opts.repoFilter)
    : null;
  const repoFilterLower = repoFilterCanonical ? repoFilterCanonical.toLowerCase() : null;

  const recordingCfg = normalizeMetricsConfig(opts.recording);
  // In unified rollups, any repo explicitly turned off via `pdd metrics off --repo` is excluded completely.
  const excludedRepos = new Set();
  if (!repoFilterLower) {
    for (const [lower, enabled] of Object.entries(recordingCfg.repos)) {
      if (enabled === false) excludedRepos.add(lower);
    }
  }

  const canonicalRepos = new Map();
  const rememberRepo = raw => {
    if (typeof raw !== 'string' || !REPO_PATTERN.test(raw.trim())) return null;
    const trimmed = raw.trim();
    const lower = trimmed.toLowerCase();
    if (excludedRepos.has(lower)) return null;
    if (repoFilterLower && lower !== repoFilterLower) return null;
    if (!canonicalRepos.has(lower)) canonicalRepos.set(lower, trimmed);
    return lower;
  };

  if (Array.isArray(opts.repos)) {
    for (const r of opts.repos) rememberRepo(r);
  }

  let openMap = null;
  if (isPlainObject(opts.openIssues) || Array.isArray(opts.openIssues)) {
    openMap = new Map();
    for (const [lower, v] of entriesFromMapOrList(opts.openIssues, 'count')) {
      if (excludedRepos.has(lower)) continue;
      openMap.set(lower, typeof v === 'number' && Number.isInteger(v) && v >= 0 ? v : null);
    }
  }

  const openNumbersMap = new Map();
  if (Array.isArray(opts.openIssueNumbers)) {
    for (const entry of opts.openIssueNumbers) {
      if (!isPlainObject(entry) || typeof entry.repo !== 'string' || !REPO_PATTERN.test(entry.repo.trim())) continue;
      const lower = entry.repo.trim().toLowerCase();
      if (excludedRepos.has(lower)) continue;
      const nums = Array.isArray(entry.issues) ? entry.issues.filter(positiveInt) : [];
      openNumbersMap.set(lower, new Set(nums));
    }
  }

  const closedIssues = [];
  if (Array.isArray(opts.closedIssues)) {
    for (const entry of opts.closedIssues) {
      if (!isPlainObject(entry) || typeof entry.repo !== 'string' || !REPO_PATTERN.test(entry.repo.trim())) continue;
      if (!positiveInt(entry.issue)) continue;
      const closedAtMs = parseTimestampMs(entry.closedAt, null);
      if (closedAtMs === null) continue;
      const lower = entry.repo.trim().toLowerCase();
      if (excludedRepos.has(lower)) continue;
      closedIssues.push({ repoLower: lower, issue: entry.issue, closedAtMs });
    }
  }

  const prStateMap = indexPrStates(opts.prStates, excludedRepos);
  const regIndex = indexRegressions(opts.regressions, excludedRepos);

  const normalizedRuns = [];
  for (const raw of Array.isArray(opts.runs) ? opts.runs : []) {
    if (!isPlainObject(raw)) continue;
    const repoLower = rememberRepo(raw.repo);
    if (!repoLower) continue;
    const issues = Array.isArray(raw.issues) && raw.issues.length > 0
      ? [...new Set(raw.issues.filter(positiveInt))]
      : (positiveInt(raw.issue) ? [raw.issue] : []);
    if (issues.length === 0) continue;

    const atMs = parseTimestampMs(raw.at ?? raw.endedAt ?? raw.updatedAt ?? raw.startedAt, null);
    if (atMs === null) continue;
    const startMs = parseTimestampMs(raw.startedAt, atMs);
    const rawStatus = normalizeStatus(raw.status ?? raw.outcome);
    if (isRunPaused(startMs, atMs, rawStatus, repoLower, recordingCfg)) continue;

    const prNumber = positiveInt(raw.pr) ? raw.pr : null;
    const prState = prNumber !== null ? prStateMap.get(`${repoLower}#${prNumber}`) ?? null : null;
    const runMergedAtMs = parseTimestampMs(raw.mergedAt, null);

    let merged = false;
    let mwmFlag = false;
    let status = rawStatus;
    let mergedAtMs = null;
    let prStateCode = null;

    if (prState) {
      prStateCode = prState.state;
      const mergedNotInFuture = prState.mergedAtMs === null || prState.mergedAtMs <= nowMs;
      const reconciledMerged = mergedNotInFuture && (
        prState.merged === true
        || prState.state === 'MERGED'
        || prState.mergedAtMs !== null
      );
      if (reconciledMerged) {
        merged = true;
        mwmFlag = true;
        status = 'merged';
        mergedAtMs = prState.mergedAtMs ?? runMergedAtMs ?? atMs;
      } else {
        merged = false;
        mwmFlag = false;
      }
    } else {
      merged = rawStatus === 'merged' || raw.prMerged === true || (runMergedAtMs !== null && runMergedAtMs <= nowMs);
      mwmFlag = merged || rawStatus === 'would-merge';
      if (merged) {
        status = 'merged';
        mergedAtMs = runMergedAtMs ?? atMs;
      }
    }

    const prCreated = prNumber !== null || raw.prCreated === true || merged || rawStatus === 'would-merge';
    const rawGates = isPlainObject(raw.gates) ? raw.gates : {};
    const gates = {};
    for (const gate of ALL_GATES) {
      let state = normalizeGateState(gate, rawGates[gate]);
      if ((merged || rawStatus === 'would-merge') && state === 'na' && (gate === 'suite' || gate === 'review')) {
        state = 'pass';
      }
      gates[gate] = state;
    }
    const gateCounts = normalizeGateCounts(raw.gateCounts);
    const skill = normalizeSkill(raw.skill, {
      pathsOnlyD: raw.pathsOnlyD === true,
      promptChanged: raw.promptChanged,
      title: raw.title,
    });
    const durationMinutes = typeof raw.durationMinutes === 'number' && Number.isFinite(raw.durationMinutes) && raw.durationMinutes > 0
      ? raw.durationMinutes
      : null;
    const regressionIssues = Array.isArray(raw.regressionIssues) ? raw.regressionIssues.filter(positiveInt) : [];
    normalizedRuns.push({
      repoLower,
      repo: canonicalRepos.get(repoLower),
      issues,
      skill,
      startMs,
      atMs,
      mergedAtMs,
      rawStatus,
      status,
      merged,
      mwmFlag,
      pr: prNumber,
      prCreated,
      prStateCode,
      gates,
      gateCounts,
      promptChanged: raw.promptChanged === true,
      reopened: raw.reopened === true,
      reverted: raw.reverted === true,
      regressionIssues,
      durationMinutes,
    });
  }

  if (repoFilterCanonical && !canonicalRepos.has(repoFilterLower)) {
    canonicalRepos.set(repoFilterLower, repoFilterCanonical);
  }
  const resolvedRepoFilter = repoFilterLower
    ? (canonicalRepos.get(repoFilterLower) ?? repoFilterCanonical)
    : null;

  const sortedRepoLowers = [...canonicalRepos.keys()].sort();
  const reposList = sortedRepoLowers.map(lower => canonicalRepos.get(lower));
  const byRepo = Boolean(opts.byRepo);
  const repoNamesLabel = formatRepoNamesLabel(reposList);
  const scopeLabel = resolvedRepoFilter ?? (byRepo ? `Per Repo · ${repoNamesLabel}` : repoNamesLabel);

  let windowDefs;
  let targetRefMs = nowMs;
  if (standup && parsedDate) {
    const win = resolveStandupWindow({ date: parsedDate, timezone });
    windowDefs = [{ key: win.key, label: win.label, startMs: win.startMs, endMs: win.endMs }];
    targetRefMs = win.endMs;
  } else if (parsedDate) {
    const startMs = localMidnightUtcMs(parsedDate.year, parsedDate.month, parsedDate.day, timezone);
    const nextDay = new Date(Date.UTC(parsedDate.year, parsedDate.month - 1, parsedDate.day + 1));
    const endMs = localMidnightUtcMs(nextDay.getUTCFullYear(), nextDay.getUTCMonth() + 1, nextDay.getUTCDate(), timezone) - 1;
    windowDefs = [{ key: 'date', label: parsedDate.text, startMs, endMs }];
    targetRefMs = startMs + 12 * 3_600_000;
  } else {
    const nowLocal = localDateParts(nowMs, timezone);
    const mondayUtcDate = new Date(Date.UTC(nowLocal.year, nowLocal.month - 1, nowLocal.day - nowLocal.weekday));
    const weekStartMs = localMidnightUtcMs(
      mondayUtcDate.getUTCFullYear(),
      mondayUtcDate.getUTCMonth() + 1,
      mondayUtcDate.getUTCDate(),
      timezone,
    );
    if (standup) {
      const win = resolveStandupWindow({ now: nowMs, timezone });
      windowDefs = [
        { key: win.key, label: win.label, startMs: win.startMs, endMs: win.endMs },
        { key: 'week', label: 'Week (Mon-Sun)', startMs: weekStartMs, endMs: nowMs },
      ];
    } else {
      windowDefs = [
        { key: 'last24h', label: 'Last 24h', startMs: nowMs - DAY_MS, endMs: nowMs },
        { key: 'week', label: 'Week (Mon-Sun)', startMs: weekStartMs, endMs: nowMs },
      ];
    }
  }

  const windowItemsMap = new Map();
  for (const w of windowDefs) {
    windowItemsMap.set(w.key, selectWindowIssues(normalizedRuns, w, nowMs, regIndex));
  }

  const regressionsComplete = opts.regressionsComplete !== false;
  const { open: openNow, openDisplay: openNowDisplay } = resolveOpenCount(sortedRepoLowers, openMap, openNumbersMap);
  const overviewWindows = windowDefs.map(w =>
    summarizeOverviewRow(w.key, w.label, w, windowItemsMap.get(w.key), sortedRepoLowers, openMap, openNumbersMap, closedIssues, regressionsComplete),
  );
  const target = buildTargetRow(recordingCfg.targets, targetRefMs, timezone);

  const perRepoDefs = parsedDate ? windowDefs : [windowDefs[1], windowDefs[0]];
  const perRepoWindows = perRepoDefs.map(w => {
    const items = windowItemsMap.get(w.key);
    const rows = sortedRepoLowers.map(lower =>
      summarizeOverviewRow(
        lower,
        canonicalRepos.get(lower),
        w,
        items.filter(i => i.repoLower === lower),
        [lower],
        openMap,
        openNumbersMap,
        closedIssues,
        regressionsComplete,
      ),
    );
    const total = summarizeOverviewRow('total', 'Total', w, items, sortedRepoLowers, openMap, openNumbersMap, closedIssues, regressionsComplete);
    return { key: w.key, label: w.label, rows, total };
  });

  const primaryIndex = parsedDate ? 0 : 1;
  const primaryWindow = windowDefs[primaryIndex];
  const primaryOverviewRow = overviewWindows[primaryIndex];
  const primaryItems = windowItemsMap.get(primaryWindow.key);

  // Evaluate 7-day mature vs immature post-merge reopen/regression cohort across all merged runs.
  const mergedForCohort = new Map();
  for (const run of normalizedRuns) {
    if (!run.merged || run.mergedAtMs === null) continue;
    for (const issueNumber of run.issues) {
      const candidate = { ...run, issue: issueNumber };
      const reg = resolveItemRegression(candidate, regIndex);
      const key = `${run.repoLower}#${run.pr ? `pr:${run.pr}` : `issue:${issueNumber}`}`;
      const prev = mergedForCohort.get(key);
      if (!prev || run.mergedAtMs >= prev.mergedAtMs) {
        mergedForCohort.set(key, {
          id: key,
          repo: run.repo,
          issue: issueNumber,
          pr: run.pr,
          mergedAt: new Date(run.mergedAtMs).toISOString(),
          mergedAtMs: run.mergedAtMs,
          reopened: reg.hasReopened,
          reopenedAt: reg.reopenedAt,
          reverted: reg.hasReverted,
          revertedAt: reg.revertedAt,
          regressionIssues: reg.regressionIssueNumbers,
        });
      }
    }
  }
  const cohortRefMs = parsedDate ? windowDefs[0].endMs : nowMs;
  const cohortRaw = evaluateMatureCohort([...mergedForCohort.values()], {
    now: cohortRefMs,
    maturityDays: opts.cohortMaturityDays,
    reopenedEvents: Array.isArray(opts.reopenedEvents) ? opts.reopenedEvents : [],
    reverts: Array.isArray(opts.cohortReverts) ? opts.cohortReverts : [],
    followUpIssues: Array.isArray(opts.cohortFollowUpIssues) ? opts.cohortFollowUpIssues : [],
  });
  const cohortSummary = `${cohortRaw.maturityDays}d Cohort: Mature (>=${cohortRaw.maturityDays}d) ${cohortRaw.mature.total} merged (${cohortRaw.mature.reopened} reopened, ${cohortRaw.mature.regressed} regressed / ${fmtPct(cohortRaw.mature.regressionPct)}) · Immature (<${cohortRaw.maturityDays}d) ${cohortRaw.immature.total} merged (${cohortRaw.immature.reopened} reopened, ${cohortRaw.immature.regressed} regressed / ${fmtPct(cohortRaw.immature.earlyRegressionPct)})`;
  const cohort = { ...cohortRaw, summary: cohortSummary };

  const stages = {
    ...summarizeStages(primaryWindow, primaryItems, regressionsComplete, {
      pool: primaryOverviewRow?.pool ?? null,
      poolDisplay: primaryOverviewRow?.poolDisplay ?? '?',
    }),
    cohort,
  };
  const skills = summarizeSkills(primaryWindow, primaryItems);
  const recurringFlakes = summarizeMetricsRecurringFlakes({
    recurringFlakes: opts.recurringFlakes,
    flakeEntries: opts.flakeEntries,
    refMs: parsedDate ? windowDefs[0].endMs : nowMs,
    windowDays: opts.flakeWindowDays,
    threshold: opts.flakeThreshold,
    excludedRepos,
    repoFilterLower,
  });

  const effectiveEnabled = repoFilterLower
    ? isMetricsEnabled(recordingCfg, repoFilterLower)
    : recordingCfg.enabled;

  return {
    schema: 'pdd.autopilot.metrics.v1',
    generatedAt: nowIso,
    displayDate: formatShortDate(nowMs, timezone),
    timezone,
    standup,
    date: parsedDate ? parsedDate.text : null,
    view,
    byRepo,
    repoFilter: resolvedRepoFilter,
    scopeLabel,
    openNow,
    openNowDisplay,
    regressionsComplete,
    recording: {
      enabled: effectiveEnabled,
      globalEnabled: recordingCfg.enabled,
      repoOverrides: recordingCfg.repos,
      targets: recordingCfg.targets,
    },
    repos: reposList,
    overview: {
      windows: overviewWindows,
      target,
      perRepoWindows,
    },
    stages,
    cohort,
    skills,
    recurringFlakes,
    ...(isPlainObject(opts.investigation) ? { investigation: opts.investigation } : {}),
  };
}

function renderTable(headers, alignments, rows) {
  const widths = headers.map((h, col) =>
    Math.max(h.length, ...rows.map(r => String(r[col] ?? '').length)),
  );
  const formatRow = cells =>
    cells
      .map((cell, col) => {
        const text = String(cell ?? '');
        return alignments[col] === 'right' ? text.padStart(widths[col]) : text.padEnd(widths[col]);
      })
      .join('   ')
      .trimEnd();
  return [formatRow(headers), ...rows.map(formatRow)].join('\n');
}

function renderOverviewSection(report) {
  if (report.byRepo) {
    return report.overview.perRepoWindows
      .map(win => {
        const bodyRows = win.rows.length > 0 ? [...win.rows, win.total] : [win.total];
        const table = renderTable(
          ['Repo', 'Pool', 'Taken', 'PRs', 'Merged (Conv%)', 'Regressions'],
          ['left', 'right', 'right', 'right', 'right', 'right'],
          bodyRows.map(r => [r.label, r.poolDisplay, r.taken, r.prCreated, r.mergedDisplay, r.regressionsDisplay]),
        );
        return `${win.label}\n${table}`;
      })
      .join('\n\n');
  }
  const rows = report.overview.windows.map(w => [
    w.label,
    w.poolDisplay,
    w.taken,
    w.prCreated,
    w.mergedDisplay,
    w.regressionsDisplay,
  ]);
  if (report.overview.target) {
    const t = report.overview.target;
    rows.push([t.label, '-', '-', '-', t.convDisplay, t.regressionDisplay]);
  }
  return renderTable(
    ['Window', 'Pool', 'Taken', 'PRs', 'Merged (Conv%)', 'Regressions'],
    ['left', 'right', 'right', 'right', 'right', 'right'],
    rows,
  );
}

function renderStagesSection(report) {
  const s = report.stages;
  const cohortLine = report.cohort?.summary ?? s.cohort?.summary ?? null;
  return [
    `Funnel & Gates · ${s.window.label} · ${s.taken} Taken -> ${s.pr} PRs -> ${s.merged} Merged`,
    ...(s.funnel?.line ? [`- Funnel: ${s.funnel.line}`] : []),
    ...(s.stageFunnelLine ? [`- ${s.stageFunnelLine}`] : []),
    `- ${s.beforePr.summary}`,
    `- ${s.unmergedPrs.summary}`,
    `- ${s.prGates.summary}`,
    `- ${s.promptChecks.summary}`,
    `- ${s.regressions.summary}`,
    ...(cohortLine ? [`- ${cohortLine}`] : []),
  ].join('\n');
}

function renderSkillsSection(report) {
  const sk = report.skills;
  const allRows = [...sk.rows, sk.total];
  const table = renderTable(
    ['Skill', 'Taken', 'PRs', 'Merged (Conv%)', 'Median Time'],
    ['left', 'right', 'right', 'right', 'right'],
    allRows.map(r => [r.skill, r.taken, r.prCreated, r.mergedDisplay, r.medianDisplay]),
  );
  return `Work Mix · ${sk.window.label}\n${table}`;
}

function renderRecurringFlakesSection(report) {
  const rf = report.recurringFlakes;
  if (!rf || !Array.isArray(rf.recurring) || rf.recurring.length === 0) return null;
  const multiRepo = !report.repoFilter && Array.isArray(report.repos) && report.repos.length > 1;
  const header = `Recurring flakes (${rf.windowDays ?? DEFAULT_FLAKE_WINDOW_DAYS}d, >=${rf.threshold ?? DEFAULT_FLAKE_THRESHOLD})`;
  const bullets = rf.recurring.slice(0, 10).map(item => {
    const parts = [];
    for (const key of ['flaked-then-passed', 'reproduced-red', 'base-test-red']) {
      if ((item.outcomes?.[key] ?? 0) > 0) parts.push(`${item.outcomes[key]} ${key}`);
    }
    const label = multiRepo && item.repo ? `${item.repo}: ${item.target}` : item.target;
    const issuesNote = Array.isArray(item.issues) && item.issues.length > 0
      ? ` · issues ${item.issues.map(n => `#${n}`).join(', ')}`
      : '';
    return `- ${label}: ${item.count}x${parts.length ? ` (${parts.join(', ')})` : ''}${issuesNote}`;
  });
  return [header, ...bullets].join('\n');
}

function renderInvestigationSection(report) {
  const inv = report.investigation;
  if (!isPlainObject(inv) || !isPlainObject(inv.summary)) return null;
  const findings = Array.isArray(inv.findings) ? inv.findings : [];
  const header = `Daily Investigation (${inv.date ?? 'latest'}) · Unique: ${inv.summary.uniqueFindings ?? findings.length} · New: ${inv.summary.newFindings ?? 0} · Deduplicated: ${inv.summary.deduplicatedCount ?? 0}`;
  const buckets = ['orchestrator', 'agent-quality', 'environment', 'real-hold']
    .map(b => `${b}=${inv.summary.buckets?.[b]?.count ?? 0}`)
    .join(' · ');
  return [
    header,
    `- Buckets: ${buckets}`,
    ...findings.slice(0, 5).map(f => `- [#${f.proposal?.rank ?? '?'} ${f.proposal?.rung ?? 'fix'}] ${f.bucket}/${f.reasonCode}: ${f.proposal?.title ?? f.title}`),
  ].join('\n');
}

export function formatMetricsText(report, options = {}) {
  const view = options.view ?? report.view ?? 'overview';
  const scopeLabel = report.scopeLabel
    ?? (report.repoFilter ?? formatRepoNamesLabel(Array.isArray(report.repos) ? report.repos : []));
  const dateLabel = report.date ?? report.displayDate;
  const openLabel = report.openNowDisplay ?? '?';
  const lines = [`PDD Autopilot Metrics · ${scopeLabel} · ${dateLabel} · Open now: ${openLabel}`];
  if (!report.recording.enabled) {
    lines.push('Recording: OFF (existing history shown; run "pdd metrics on" to resume)');
  }
  lines.push('');

  const flakesBlock = renderRecurringFlakesSection(report);
  const invBlock = renderInvestigationSection(report);
  if (view === 'overview') {
    lines.push(renderOverviewSection(report));
    lines.push('');
    lines.push(renderStagesSection(report));
    if (flakesBlock) {
      lines.push('');
      lines.push(flakesBlock);
    }
    if (invBlock) {
      lines.push('');
      lines.push(invBlock);
    }
  } else if (view === 'stages') {
    lines.push(renderStagesSection(report));
    if (flakesBlock) {
      lines.push('');
      lines.push(flakesBlock);
    }
    if (invBlock) {
      lines.push('');
      lines.push(invBlock);
    }
  } else if (view === 'skills') {
    lines.push(renderSkillsSection(report));
  } else {
    lines.push(renderOverviewSection(report));
    lines.push('');
    lines.push(renderStagesSection(report));
    lines.push('');
    lines.push(renderSkillsSection(report));
    if (flakesBlock) {
      lines.push('');
      lines.push(flakesBlock);
    }
    if (invBlock) {
      lines.push('');
      lines.push(invBlock);
    }
  }
  return lines.join('\n');
}

function escapeHtml(value) {
  return String(value ?? '')
    .replaceAll('&', '&amp;')
    .replaceAll('<', '&lt;')
    .replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;')
    .replaceAll("'", '&#39;');
}

export function renderMetricsHtml(report) {
  const scopeLabel = report.scopeLabel
    ?? (report.repoFilter ?? formatRepoNamesLabel(Array.isArray(report.repos) ? report.repos : []));
  const primaryOverview = report.overview.windows.at(-1) ?? report.overview.windows[0];
  const target = report.overview.target;
  const s = report.stages;
  const sk = report.skills;

  const convMinPct = target?.convMinPct ?? 90;
  const formatConvCell = w => {
    const text = escapeHtml(w.mergedDisplay);
    if (w.convPct === null) return text;
    const cls = w.convPct >= convMinPct ? 'pill-good' : 'pill-warn';
    return `<span class="pill ${cls}">${text}</span>`;
  };
  const unifiedRowsHtml = [
    ...report.overview.windows.map(w => `<tr>
      <td><strong>${escapeHtml(w.label)}</strong></td>
      <td class="num">${escapeHtml(w.poolDisplay)}</td>
      <td class="num">${w.taken}</td>
      <td class="num">${w.prCreated}</td>
      <td class="num">${formatConvCell(w)}</td>
      <td class="num">${escapeHtml(w.regressionsDisplay)}</td>
    </tr>`),
    ...(target ? [`<tr class="target-row">
      <td>${escapeHtml(target.label)}</td>
      <td class="num">-</td>
      <td class="num">-</td>
      <td class="num">-</td>
      <td class="num">${escapeHtml(target.convDisplay)}</td>
      <td class="num">${escapeHtml(target.regressionDisplay)}</td>
    </tr>`] : []),
  ].join('\n');

  const perRepoSectionHtml = report.overview.perRepoWindows
    .map(win => {
      const rows = [...win.rows, win.total]
        .map(r => `<tr class="${r.key === 'total' ? 'total-row' : ''}">
          <td>${escapeHtml(r.label)}</td>
          <td class="num">${escapeHtml(r.poolDisplay)}</td>
          <td class="num">${r.taken}</td>
          <td class="num">${r.prCreated}</td>
          <td class="num">${escapeHtml(r.mergedDisplay)}</td>
          <td class="num">${escapeHtml(r.regressionsDisplay)}</td>
        </tr>`)
        .join('\n');
      return `<div class="subcard">
        <h3>Per Repository · ${escapeHtml(win.label)}</h3>
        <table>
          <thead><tr><th>Repo</th><th class="num">Pool</th><th class="num">Taken</th><th class="num">PRs</th><th class="num">Merged (Conv%)</th><th class="num">Regressions</th></tr></thead>
          <tbody>${rows}</tbody>
        </table>
      </div>`;
    })
    .join('\n');

  const cohortLine = report.cohort?.summary ?? s.cohort?.summary ?? null;
  const funnelLinesHtml = [
    ...(s.funnel?.line ? [`Funnel: ${s.funnel.line}`] : []),
    ...(s.stageFunnelLine ? [s.stageFunnelLine] : []),
    s.beforePr.summary,
    s.unmergedPrs.summary,
    s.prGates.summary,
    s.promptChecks.summary,
    s.regressions.summary,
    ...(cohortLine ? [cohortLine] : []),
  ].map(line => `<li>${escapeHtml(line)}</li>`).join('\n');

  const skillRowsHtml = [...sk.rows, sk.total]
    .map(r => `<tr class="${r.skill === 'Total' ? 'total-row' : ''}">
      <td><code>${escapeHtml(r.skill)}</code></td>
      <td class="num">${r.taken}</td>
      <td class="num">${r.prCreated}</td>
      <td class="num">${escapeHtml(r.mergedDisplay)}</td>
      <td class="num">${escapeHtml(r.medianDisplay)}</td>
    </tr>`)
    .join('\n');

  const recurringList = Array.isArray(report.recurringFlakes?.recurring) ? report.recurringFlakes.recurring : [];
  const recurringFlakesHtml = recurringList.length > 0
    ? `
    <section class="card">
      <h2>4. Recurring Flakes (${escapeHtml(String(report.recurringFlakes.windowDays ?? DEFAULT_FLAKE_WINDOW_DAYS))}d, &gt;=${escapeHtml(String(report.recurringFlakes.threshold ?? DEFAULT_FLAKE_THRESHOLD))})</h2>
      <ul class="funnel-list">
        ${recurringList.slice(0, 10).map(item => {
          const parts = ['flaked-then-passed', 'reproduced-red', 'base-test-red']
            .filter(k => (item.outcomes?.[k] ?? 0) > 0)
            .map(k => `${item.outcomes[k]} ${k}`);
          const label = item.repo ? `${item.repo}: ${item.target}` : item.target;
          return `<li><code>${escapeHtml(label)}</code> — ${item.count}x${parts.length ? ` (${escapeHtml(parts.join(', '))})` : ''}</li>`;
        }).join('\n        ')}
      </ul>
    </section>`
    : '';

  const invFindings = Array.isArray(report.investigation?.findings) ? report.investigation.findings : [];
  const investigationHtml = invFindings.length > 0 && isPlainObject(report.investigation?.summary)
    ? `
    <section class="card">
      <h2>Daily Investigation (${escapeHtml(report.investigation.date ?? 'latest')}) · Unique: ${report.investigation.summary.uniqueFindings ?? invFindings.length}</h2>
      <ul class="funnel-list">
        <li>Buckets: ${['orchestrator', 'agent-quality', 'environment', 'real-hold'].map(b => `${b}=${report.investigation.summary.buckets?.[b]?.count ?? 0}`).join(' · ')}</li>
        ${invFindings.slice(0, 5).map(f => `<li><code>[#${escapeHtml(String(f.proposal?.rank ?? '?'))} ${escapeHtml(f.proposal?.rung ?? 'fix')}]</code> <code>${escapeHtml(f.bucket)}/${escapeHtml(f.reasonCode)}</code>: ${escapeHtml(f.proposal?.title ?? f.title ?? '')}</li>`).join('\n        ')}
      </ul>
    </section>`
    : '';

  return `<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>PDD Autopilot Metrics · ${escapeHtml(scopeLabel)}</title>
  <style>
    :root { --bg: #0f172a; --card: #1e293b; --border: #334155; --text: #f8fafc; --muted: #94a3b8; --accent: #38bdf8; --good: #34d399; --warn: #fbbf24; }
    * { box-sizing: border-box; }
    body { margin: 0; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Inter, sans-serif; background: var(--bg); color: var(--text); line-height: 1.5; padding: 32px 20px; }
    .wrap { max-width: 1080px; margin: 0 auto; }
    header { display: flex; flex-wrap: wrap; justify-content: space-between; align-items: baseline; gap: 12px; margin-bottom: 24px; border-bottom: 1px solid var(--border); padding-bottom: 16px; }
    h1 { margin: 0; font-size: 1.5rem; letter-spacing: -0.02em; }
    h2 { margin: 0 0 12px; font-size: 1.1rem; color: var(--accent); }
    h3 { margin: 0 0 10px; font-size: 0.95rem; color: var(--muted); }
    .meta { color: var(--muted); font-size: 0.9rem; }
    .kpis { display: grid; grid-template-columns: repeat(auto-fit, minmax(180px, 1fr)); gap: 14px; margin-bottom: 24px; }
    .kpi { background: var(--card); border: 1px solid var(--border); border-radius: 10px; padding: 16px; }
    .kpi .label { color: var(--muted); font-size: 0.8rem; text-transform: uppercase; letter-spacing: 0.05em; }
    .kpi .val { font-size: 1.6rem; font-weight: 700; margin-top: 4px; }
    .card { background: var(--card); border: 1px solid var(--border); border-radius: 12px; padding: 20px; margin-bottom: 20px; overflow-x: auto; }
    .subcard { margin-top: 18px; padding-top: 16px; border-top: 1px solid var(--border); }
    table { width: 100%; border-collapse: collapse; font-size: 0.92rem; }
    th, td { padding: 10px 12px; border-bottom: 1px solid var(--border); text-align: left; }
    th { color: var(--muted); font-weight: 600; font-size: 0.82rem; text-transform: uppercase; letter-spacing: 0.04em; }
    .num { text-align: right; font-variant-numeric: tabular-nums; }
    .total-row td { font-weight: 700; border-top: 2px solid var(--border); border-bottom: none; }
    .target-row td { color: var(--muted); font-style: italic; }
    .pill { display: inline-block; padding: 2px 8px; border-radius: 999px; font-size: 0.82rem; font-weight: 600; }
    .pill-good { background: rgba(52, 211, 153, 0.15); color: var(--good); }
    .pill-warn { background: rgba(251, 191, 36, 0.18); color: var(--warn); }
    .funnel-list { margin: 8px 0 0; padding-left: 20px; color: var(--text); }
    .funnel-list li { margin-bottom: 6px; }
    code { background: rgba(15, 23, 42, 0.6); padding: 2px 6px; border-radius: 4px; font-size: 0.86rem; }
  </style>
</head>
<body>
  <div class="wrap">
    <header>
      <div>
        <h1>PDD Autopilot Metrics</h1>
        <div class="meta">${escapeHtml(scopeLabel)} · ${escapeHtml(report.date ?? report.displayDate)} · Open now: ${escapeHtml(report.openNowDisplay ?? '?')} · Timezone: ${escapeHtml(report.timezone)}</div>
      </div>
      <div>
        <span class="pill ${report.recording.enabled ? 'pill-good' : 'pill-warn'}">Recording: ${report.recording.enabled ? 'ON' : 'OFF'}</span>
      </div>
    </header>

    <div class="kpis">
      <div class="kpi"><div class="label">Open Now</div><div class="val">${escapeHtml(report.openNowDisplay ?? '?')}</div></div>
      <div class="kpi"><div class="label">Pool (${escapeHtml(primaryOverview?.label ?? '')})</div><div class="val">${escapeHtml(primaryOverview?.poolDisplay ?? '?')}</div></div>
      <div class="kpi"><div class="label">Taken / PRs</div><div class="val">${primaryOverview?.taken ?? 0} / ${primaryOverview?.prCreated ?? 0}</div></div>
      <div class="kpi"><div class="label">Merged (Conv%)</div><div class="val">${escapeHtml(primaryOverview?.mergedDisplay ?? '0 (n/a)')}</div></div>
      <div class="kpi"><div class="label">Regressions</div><div class="val">${escapeHtml(primaryOverview?.regressionsDisplay ?? '0 (n/a)')}</div></div>
    </div>

    <section class="card">
      <h2>1. Overview</h2>
      <table>
        <thead><tr><th>Window</th><th class="num">Pool</th><th class="num">Taken</th><th class="num">PRs</th><th class="num">Merged (Conv%)</th><th class="num">Regressions</th></tr></thead>
        <tbody>${unifiedRowsHtml}</tbody>
      </table>
      ${report.repos.length > 0 ? perRepoSectionHtml : ''}
    </section>

    <section class="card">
      <h2>2. Funnel &amp; Gates · ${escapeHtml(s.window.label)} · ${s.taken} Taken -&gt; ${s.pr} PRs -&gt; ${s.merged} Merged</h2>
      <ul class="funnel-list">
        ${funnelLinesHtml}
      </ul>
    </section>

    <section class="card">
      <h2>3. Work Mix by Skill · ${escapeHtml(sk.window.label)}</h2>
      <table>
        <thead><tr><th>Skill</th><th class="num">Taken</th><th class="num">PRs</th><th class="num">Merged (Conv%)</th><th class="num">Median Time</th></tr></thead>
        <tbody>${skillRowsHtml}</tbody>
      </table>
    </section>${recurringFlakesHtml}${investigationHtml}
  </div>
</body>
</html>
`;
}
