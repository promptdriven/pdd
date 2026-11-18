// Generated from prompts/cli/metrics-model.prompt.md (sha256: 0dc903a7fd0fd752d4e3b45157187de03ec0bc7757aa1a509cddc9941b7f99f1).

export const SKILLS = Object.freeze(['small-change', 'bug', 'feature']);
export const GATES = Object.freeze(['runtime', 'vectors', 'formal', 'suite', 'review', 'ci']);

const REPO_PATTERN = /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/;
const VALID_VIEWS = new Set(['overview', 'stages', 'skills', 'full']);
const DAY_MS = 86_400_000;
const WEEKDAY_INDEX = { Mon: 0, Tue: 1, Wed: 2, Thu: 3, Fri: 4, Sat: 5, Sun: 6 };

function modelError(code, message) {
  return Object.assign(new Error(message), { code });
}

function isPlainObject(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
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

function validateTimezone(timezone) {
  const tz = typeof timezone === 'string' && timezone.trim() ? timezone.trim() : 'UTC';
  try {
    new Intl.DateTimeFormat('en-US', { timeZone: tz }).format(0);
    return tz;
  } catch {
    throw modelError('invalid-timezone', `Invalid IANA timezone "${timezone}".`);
  }
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

function localParts(ms, timezone) {
  const dtf = new Intl.DateTimeFormat('en-US', {
    timeZone: timezone,
    weekday: 'short',
    year: 'numeric',
    month: '2-digit',
    day: '2-digit',
    hour: '2-digit',
    minute: '2-digit',
    second: '2-digit',
    hourCycle: 'h23',
  });
  const map = {};
  for (const part of dtf.formatToParts(new Date(ms))) {
    if (part.type !== 'literal') map[part.type] = part.value;
  }
  return {
    weekday: WEEKDAY_INDEX[map.weekday] ?? 0,
    year: Number(map.year),
    month: Number(map.month),
    day: Number(map.day),
    hour: Number(map.hour === '24' ? 0 : map.hour),
    minute: Number(map.minute),
    second: Number(map.second),
  };
}

function localMidnightUtcMs(year, month, day, timezone) {
  const targetUtc = Date.UTC(year, month - 1, day, 0, 0, 0, 0);
  let guess = targetUtc;
  for (let i = 0; i < 3; i++) {
    const p = localParts(guess, timezone);
    const observedAsUtc = Date.UTC(p.year, p.month - 1, p.day, p.hour, p.minute, p.second, 0);
    guess -= observedAsUtc - targetUtc;
  }
  return guess;
}

function formatShortDate(ms, timezone) {
  return new Intl.DateTimeFormat('en-US', {
    timeZone: timezone,
    weekday: 'short',
    month: 'short',
    day: 'numeric',
  }).format(new Date(ms));
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
  if (isPlainObject(cfg.repos)) {
    for (const [key, val] of Object.entries(cfg.repos)) {
      if (typeof val === 'boolean' && REPO_PATTERN.test(key.trim())) {
        repos[key.trim().toLowerCase()] = val;
      }
    }
  }
  const repoPausedSince = {};
  if (isPlainObject(cfg.repoPausedSince)) {
    for (const [key, val] of Object.entries(cfg.repoPausedSince)) {
      if (typeof val === 'string' && Number.isFinite(Date.parse(val)) && REPO_PATTERN.test(key.trim())) {
        repoPausedSince[key.trim().toLowerCase()] = new Date(Date.parse(val)).toISOString();
      }
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
  return { enabled, repos, pausedSince, repoPausedSince, pausedIntervals, updatedAt };
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
    default:
      return 'na';
  }
}

function normalizeStatus(rawStatus) {
  const s = typeof rawStatus === 'string' ? rawStatus.trim().toLowerCase() : '';
  if (s === 'merged' || s === 'would-merge' || s === 'running' || s === 'needs-person') return s;
  if (s === 'ended' || s === 'failed' || s === 'released' || s === 'stopped' || s === 'abandoned') return s;
  return 'ended';
}

function statusRank(status) {
  if (status === 'merged') return 5;
  if (status === 'would-merge') return 4;
  if (status === 'running') return 3;
  if (status === 'needs-person') return 2;
  return 1;
}

function formatConvDisplay(mwm, taken) {
  if (taken <= 0) return { convPct: null, mwmDisplay: '0 (n/a)' };
  const convPct = Math.round((mwm / taken) * 1000) / 10;
  return { convPct, mwmDisplay: `${mwm} (${convPct.toFixed(1)}%)` };
}

function computeMedianMinutes(durations) {
  const valid = durations.filter(d => typeof d === 'number' && Number.isFinite(d) && d > 0).sort((a, b) => a - b);
  if (valid.length === 0) return { medianMinutes: null, medianDisplay: 'n/a' };
  const mid = Math.floor(valid.length / 2);
  const raw = valid.length % 2 === 1 ? valid[mid] : (valid[mid - 1] + valid[mid]) / 2;
  const rounded = Math.max(1, Math.round(raw));
  return { medianMinutes: rounded, medianDisplay: `${rounded}m` };
}

function selectWindowIssues(normalizedRuns, windowDef, nowMs) {
  const byIssue = new Map();
  for (const run of normalizedRuns) {
    const inRange = (run.atMs >= windowDef.startMs && run.atMs <= windowDef.endMs)
      || (run.status === 'running' && nowMs >= windowDef.startMs && nowMs <= windowDef.endMs && run.startMs <= windowDef.endMs);
    if (!inRange) continue;
    for (const issueNumber of run.issues) {
      const key = `${run.repoLower}#${issueNumber}`;
      const prev = byIssue.get(key);
      if (
        !prev
        || statusRank(run.status) > statusRank(prev.status)
        || (statusRank(run.status) === statusRank(prev.status) && run.atMs >= prev.atMs)
      ) {
        byIssue.set(key, { ...run, issue: issueNumber });
      }
    }
  }
  return [...byIssue.values()];
}

function resolveOpenCount(repoLowers, openMap) {
  if (!openMap) return { open: null, openDisplay: '?' };
  if (repoLowers.length === 0) return { open: 0, openDisplay: '0' };
  let sum = 0;
  for (const lower of repoLowers) {
    const v = openMap.get(lower);
    if (typeof v !== 'number' || !Number.isInteger(v) || v < 0) {
      return { open: null, openDisplay: '?' };
    }
    sum += v;
  }
  return { open: sum, openDisplay: String(sum) };
}

function summarizeOverviewRow(key, label, items, repoLowers, openMap) {
  const { open, openDisplay } = resolveOpenCount(repoLowers, openMap);
  const taken = items.length;
  const prCreated = items.filter(i => i.prCreated).length;
  const mwm = items.filter(i => i.status === 'merged' || i.status === 'would-merge').length;
  const { convPct, mwmDisplay } = formatConvDisplay(mwm, taken);
  return { key, label, open, openDisplay, taken, prCreated, mwm, convPct, mwmDisplay };
}

function summarizeStages(windowDef, items) {
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
  const pr = items.filter(i => i.prCreated).length;
  const mwmItems = items.filter(i => i.status === 'merged' || i.status === 'would-merge');
  const mwm = mwmItems.length;
  const reopen = mwmItems.filter(i => i.reopened).length;

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
    if (item.status === 'merged' || item.status === 'would-merge') continue;
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
  const nonMergedSummary = nonMergedTotal === 0
    ? 'Non-merged (0): none'
    : `Non-merged (${nonMergedTotal}): ${breakdown.map(b => `${b.count} ${b.reason}`).join(' · ')}`;

  return {
    window: { key: windowDef.key, label: windowDef.label },
    taken,
    pr,
    gates,
    mwm,
    reopen,
    nonMerged: { total: nonMergedTotal, breakdown },
    nonMergedSummary,
  };
}

function summarizeSkills(windowDef, items) {
  const rows = SKILLS.map(skill => {
    const matching = items.filter(i => i.skill === skill);
    const taken = matching.length;
    const prCreated = matching.filter(i => i.prCreated).length;
    const mwmItems = matching.filter(i => i.status === 'merged' || i.status === 'would-merge');
    const mwm = mwmItems.length;
    const { convPct, mwmDisplay } = formatConvDisplay(mwm, taken);
    const { medianMinutes, medianDisplay } = computeMedianMinutes(mwmItems.map(i => i.durationMinutes));
    return { skill, taken, prCreated, mwm, convPct, mwmDisplay, medianMinutes, medianDisplay };
  });
  const taken = items.length;
  const prCreated = items.filter(i => i.prCreated).length;
  const mwmItems = items.filter(i => i.status === 'merged' || i.status === 'would-merge');
  const mwm = mwmItems.length;
  const { convPct, mwmDisplay } = formatConvDisplay(mwm, taken);
  const { medianMinutes, medianDisplay } = computeMedianMinutes(mwmItems.map(i => i.durationMinutes));
  return {
    window: { key: windowDef.key, label: windowDef.label },
    rows,
    total: { skill: 'Total', taken, prCreated, mwm, convPct, mwmDisplay, medianMinutes, medianDisplay },
  };
}

export function calculateAutopilotMetrics(input = {}) {
  const opts = isPlainObject(input) ? input : {};
  const view = opts.view === undefined ? 'overview' : String(opts.view).trim().toLowerCase();
  if (!VALID_VIEWS.has(view)) {
    throw modelError('invalid-view', `Invalid metrics view "${opts.view}".`);
  }
  const timezone = validateTimezone(opts.timezone ?? 'UTC');
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
  const canonicalRepos = new Map();
  const rememberRepo = raw => {
    if (typeof raw !== 'string' || !REPO_PATTERN.test(raw.trim())) return null;
    const trimmed = raw.trim();
    const lower = trimmed.toLowerCase();
    if (repoFilterLower && lower !== repoFilterLower) return null;
    if (!canonicalRepos.has(lower)) canonicalRepos.set(lower, trimmed);
    return lower;
  };

  if (Array.isArray(opts.repos)) {
    for (const r of opts.repos) rememberRepo(r);
  }

  let openMap = null;
  if (isPlainObject(opts.openIssues)) {
    openMap = new Map();
    for (const [k, v] of Object.entries(opts.openIssues)) {
      if (typeof k === 'string' && REPO_PATTERN.test(k.trim())) {
        openMap.set(k.trim().toLowerCase(), typeof v === 'number' && Number.isInteger(v) && v >= 0 ? v : null);
      }
    }
  }

  const normalizedRuns = [];
  for (const raw of Array.isArray(opts.runs) ? opts.runs : []) {
    if (!isPlainObject(raw)) continue;
    const repoLower = rememberRepo(raw.repo);
    if (!repoLower) continue;
    const issues = Array.isArray(raw.issues) && raw.issues.length > 0
      ? [...new Set(raw.issues.filter(n => Number.isSafeInteger(n) && n > 0))]
      : (Number.isSafeInteger(raw.issue) && raw.issue > 0 ? [raw.issue] : []);
    if (issues.length === 0) continue;

    const atMs = parseTimestampMs(raw.at ?? raw.endedAt ?? raw.updatedAt ?? raw.startedAt, null);
    if (atMs === null) continue;
    const startMs = parseTimestampMs(raw.startedAt, atMs);
    const status = normalizeStatus(raw.status ?? raw.outcome);
    if (isRunPaused(startMs, atMs, status, repoLower, recordingCfg)) continue;

    const prNumber = Number.isSafeInteger(raw.pr) && raw.pr > 0 ? raw.pr : null;
    const prCreated = prNumber !== null || raw.prCreated === true || status === 'merged' || status === 'would-merge';
    const rawGates = isPlainObject(raw.gates) ? raw.gates : {};
    const gates = {};
    for (const gate of GATES) {
      let state = normalizeGateState(gate, rawGates[gate]);
      if ((status === 'merged' || status === 'would-merge') && state === 'na' && (gate === 'suite' || gate === 'review')) {
        state = 'pass';
      }
      gates[gate] = state;
    }
    const skill = normalizeSkill(raw.skill, {
      pathsOnlyD: raw.pathsOnlyD === true,
      promptChanged: raw.promptChanged,
      title: raw.title,
    });
    const durationMinutes = typeof raw.durationMinutes === 'number' && Number.isFinite(raw.durationMinutes) && raw.durationMinutes > 0
      ? raw.durationMinutes
      : null;
    normalizedRuns.push({
      repoLower,
      repo: canonicalRepos.get(repoLower),
      issues,
      skill,
      startMs,
      atMs,
      status,
      pr: prNumber,
      prCreated,
      gates,
      reopened: raw.reopened === true || raw.reverted === true,
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

  let windowDefs;
  if (parsedDate) {
    const startMs = localMidnightUtcMs(parsedDate.year, parsedDate.month, parsedDate.day, timezone);
    const nextDay = new Date(Date.UTC(parsedDate.year, parsedDate.month - 1, parsedDate.day + 1));
    const endMs = localMidnightUtcMs(nextDay.getUTCFullYear(), nextDay.getUTCMonth() + 1, nextDay.getUTCDate(), timezone) - 1;
    windowDefs = [{ key: 'date', label: parsedDate.text, startMs, endMs }];
  } else {
    const nowLocal = localParts(nowMs, timezone);
    const mondayUtcDate = new Date(Date.UTC(nowLocal.year, nowLocal.month - 1, nowLocal.day - nowLocal.weekday));
    const weekStartMs = localMidnightUtcMs(
      mondayUtcDate.getUTCFullYear(),
      mondayUtcDate.getUTCMonth() + 1,
      mondayUtcDate.getUTCDate(),
      timezone,
    );
    windowDefs = [
      { key: 'last24h', label: 'Last 24h', startMs: nowMs - DAY_MS, endMs: nowMs },
      { key: 'week', label: 'Week (Mon-Sun)', startMs: weekStartMs, endMs: nowMs },
    ];
  }

  const windowItemsMap = new Map();
  for (const w of windowDefs) {
    windowItemsMap.set(w.key, selectWindowIssues(normalizedRuns, w, nowMs));
  }

  const overviewWindows = windowDefs.map(w =>
    summarizeOverviewRow(w.key, w.label, windowItemsMap.get(w.key), sortedRepoLowers, openMap),
  );

  const perRepoDefs = parsedDate ? windowDefs : [windowDefs[1], windowDefs[0]];
  const perRepoWindows = perRepoDefs.map(w => {
    const items = windowItemsMap.get(w.key);
    const rows = sortedRepoLowers.map(lower =>
      summarizeOverviewRow(
        lower,
        canonicalRepos.get(lower),
        items.filter(i => i.repoLower === lower),
        [lower],
        openMap,
      ),
    );
    const total = summarizeOverviewRow('total', 'Total', items, sortedRepoLowers, openMap);
    return { key: w.key, label: w.label, rows, total };
  });

  const primaryWindow = parsedDate ? windowDefs[0] : windowDefs[1];
  const primaryItems = windowItemsMap.get(primaryWindow.key);
  const stages = summarizeStages(primaryWindow, primaryItems);
  const skills = summarizeSkills(primaryWindow, primaryItems);

  const effectiveEnabled = repoFilterLower
    ? isMetricsEnabled(recordingCfg, repoFilterLower)
    : recordingCfg.enabled;

  return {
    schema: 'pdd.autopilot.metrics.v1',
    generatedAt: nowIso,
    displayDate: formatShortDate(nowMs, timezone),
    timezone,
    date: parsedDate ? parsedDate.text : null,
    view,
    byRepo: Boolean(opts.byRepo),
    repoFilter: resolvedRepoFilter,
    recording: {
      enabled: effectiveEnabled,
      globalEnabled: recordingCfg.enabled,
      repoOverrides: recordingCfg.repos,
    },
    repos: reposList,
    overview: {
      windows: overviewWindows,
      perRepoWindows,
    },
    stages,
    skills,
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
        const bodyRows = win.rows.length > 0
          ? [...win.rows, win.total]
          : [win.total];
        const table = renderTable(
          ['Repo', 'Open', 'Taken', 'PR Created', 'M/WM (Conv%)'],
          ['left', 'right', 'right', 'right', 'right'],
          bodyRows.map(r => [r.label, r.openDisplay, r.taken, r.prCreated, r.mwmDisplay]),
        );
        return `${win.label}\n${table}`;
      })
      .join('\n\n');
  }
  return renderTable(
    ['Window', 'Open', 'Taken', 'PR Created', 'M/WM (Conv%)'],
    ['left', 'right', 'right', 'right', 'right'],
    report.overview.windows.map(w => [w.label, w.openDisplay, w.taken, w.prCreated, w.mwmDisplay]),
  );
}

function renderStagesSection(report) {
  const s = report.stages;
  const g = s.gates;
  const table = renderTable(
    ['Window', 'Taken', 'PR', 'Runtime', 'Vectors', 'Formal', 'Suite', 'Review', 'CI', 'M/WM', 'Reopen'],
    ['left', 'right', 'right', 'right', 'right', 'right', 'right', 'right', 'right', 'right', 'right'],
    [[
      s.window.label,
      s.taken,
      s.pr,
      g.runtime.display,
      g.vectors.display,
      g.formal.display,
      g.suite.display,
      g.review.display,
      g.ci.display,
      s.mwm,
      s.reopen,
    ]],
  );
  return `${table}\n${s.nonMergedSummary}`;
}

function renderSkillsSection(report) {
  const sk = report.skills;
  const allRows = [...sk.rows, sk.total];
  const table = renderTable(
    ['Skill', 'Taken', 'PR Created', 'M/WM (Conv%)', 'Median Time'],
    ['left', 'right', 'right', 'right', 'right'],
    allRows.map(r => [r.skill, r.taken, r.prCreated, r.mwmDisplay, r.medianDisplay]),
  );
  return `Work Mix · ${sk.window.label}\n${table}`;
}

export function formatMetricsText(report, options = {}) {
  const view = options.view ?? report.view ?? 'overview';
  const scopeLabel = report.repoFilter
    ? report.repoFilter
    : report.byRepo
      ? `Per Repo (${report.repos.length} ${report.repos.length === 1 ? 'repo' : 'repos'})`
      : `Unified (${report.repos.length} ${report.repos.length === 1 ? 'repo' : 'repos'})`;
  const dateLabel = report.date ?? report.displayDate;
  const lines = [`PDD Autopilot Metrics · ${scopeLabel} · ${dateLabel}`];
  if (!report.recording.enabled) {
    lines.push('Recording: OFF (existing history shown; run "pdd metrics on" to resume)');
  }
  lines.push('');

  if (view === 'overview') {
    lines.push(renderOverviewSection(report));
  } else if (view === 'stages') {
    lines.push(renderStagesSection(report));
  } else if (view === 'skills') {
    lines.push(renderSkillsSection(report));
  } else {
    lines.push(renderOverviewSection(report));
    lines.push('');
    lines.push('Autopilot Stages');
    lines.push(renderStagesSection(report));
    lines.push('');
    lines.push(renderSkillsSection(report));
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
  const scopeLabel = report.repoFilter
    ? report.repoFilter
    : `Unified (${report.repos.length} ${report.repos.length === 1 ? 'repo' : 'repos'})`;
  const primaryOverview = report.overview.windows.at(-1) ?? report.overview.windows[0];
  const s = report.stages;
  const sk = report.skills;

  const unifiedRowsHtml = report.overview.windows
    .map(w => `<tr>
      <td><strong>${escapeHtml(w.label)}</strong></td>
      <td class="num">${escapeHtml(w.openDisplay)}</td>
      <td class="num">${w.taken}</td>
      <td class="num">${w.prCreated}</td>
      <td class="num"><span class="pill pill-good">${escapeHtml(w.mwmDisplay)}</span></td>
    </tr>`)
    .join('\n');

  const perRepoSectionHtml = report.overview.perRepoWindows
    .map(win => {
      const rows = [...win.rows, win.total]
        .map(r => `<tr class="${r.key === 'total' ? 'total-row' : ''}">
          <td>${escapeHtml(r.label)}</td>
          <td class="num">${escapeHtml(r.openDisplay)}</td>
          <td class="num">${r.taken}</td>
          <td class="num">${r.prCreated}</td>
          <td class="num">${escapeHtml(r.mwmDisplay)}</td>
        </tr>`)
        .join('\n');
      return `<div class="subcard">
        <h3>Per Repository · ${escapeHtml(win.label)}</h3>
        <table>
          <thead><tr><th>Repo</th><th class="num">Open</th><th class="num">Taken</th><th class="num">PR Created</th><th class="num">M/WM (Conv%)</th></tr></thead>
          <tbody>${rows}</tbody>
        </table>
      </div>`;
    })
    .join('\n');

  const gateCellsHtml = GATES.map(g => {
    const cell = s.gates[g];
    return `<td class="num">${escapeHtml(cell.display)}</td>`;
  }).join('');

  const skillRowsHtml = [...sk.rows, sk.total]
    .map(r => `<tr class="${r.skill === 'Total' ? 'total-row' : ''}">
      <td><code>${escapeHtml(r.skill)}</code></td>
      <td class="num">${r.taken}</td>
      <td class="num">${r.prCreated}</td>
      <td class="num">${escapeHtml(r.mwmDisplay)}</td>
      <td class="num">${escapeHtml(r.medianDisplay)}</td>
    </tr>`)
    .join('\n');

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
    .pill { display: inline-block; padding: 2px 8px; border-radius: 999px; font-size: 0.82rem; font-weight: 600; }
    .pill-good { background: rgba(52, 211, 153, 0.15); color: var(--good); }
    .pill-warn { background: rgba(251, 191, 36, 0.18); color: var(--warn); }
    .summary-note { margin-top: 12px; color: var(--muted); font-size: 0.88rem; }
    code { background: rgba(15, 23, 42, 0.6); padding: 2px 6px; border-radius: 4px; font-size: 0.86rem; }
  </style>
</head>
<body>
  <div class="wrap">
    <header>
      <div>
        <h1>PDD Autopilot Metrics</h1>
        <div class="meta">${escapeHtml(scopeLabel)} · ${escapeHtml(report.date ?? report.displayDate)} · Timezone: ${escapeHtml(report.timezone)}</div>
      </div>
      <div>
        <span class="pill ${report.recording.enabled ? 'pill-good' : 'pill-warn'}">Recording: ${report.recording.enabled ? 'ON' : 'OFF'}</span>
      </div>
    </header>

    <div class="kpis">
      <div class="kpi"><div class="label">Open Issues</div><div class="val">${escapeHtml(primaryOverview?.openDisplay ?? '?')}</div></div>
      <div class="kpi"><div class="label">Taken (${escapeHtml(primaryOverview?.label ?? '')})</div><div class="val">${primaryOverview?.taken ?? 0}</div></div>
      <div class="kpi"><div class="label">PR Created</div><div class="val">${primaryOverview?.prCreated ?? 0}</div></div>
      <div class="kpi"><div class="label">M/WM (Conv%)</div><div class="val">${escapeHtml(primaryOverview?.mwmDisplay ?? '0 (n/a)')}</div></div>
    </div>

    <section class="card">
      <h2>1. Overview</h2>
      <table>
        <thead><tr><th>Window</th><th class="num">Open</th><th class="num">Taken</th><th class="num">PR Created</th><th class="num">M/WM (Conv%)</th></tr></thead>
        <tbody>${unifiedRowsHtml}</tbody>
      </table>
      ${report.repos.length > 0 ? perRepoSectionHtml : ''}
    </section>

    <section class="card">
      <h2>2. Autopilot Stages · ${escapeHtml(s.window.label)}</h2>
      <table>
        <thead>
          <tr>
            <th class="num">Taken</th><th class="num">PR</th><th class="num">Runtime</th><th class="num">Vectors</th>
            <th class="num">Formal</th><th class="num">Suite</th><th class="num">Review</th><th class="num">CI</th>
            <th class="num">M/WM</th><th class="num">Reopen</th>
          </tr>
        </thead>
        <tbody>
          <tr>
            <td class="num">${s.taken}</td>
            <td class="num">${s.pr}</td>
            ${gateCellsHtml}
            <td class="num"><strong>${s.mwm}</strong></td>
            <td class="num">${s.reopen}</td>
          </tr>
        </tbody>
      </table>
      <div class="summary-note">${escapeHtml(s.nonMergedSummary)}</div>
    </section>

    <section class="card">
      <h2>3. Work Mix by Skill · ${escapeHtml(sk.window.label)}</h2>
      <table>
        <thead><tr><th>Skill</th><th class="num">Taken</th><th class="num">PR Created</th><th class="num">M/WM (Conv%)</th><th class="num">Median Time</th></tr></thead>
        <tbody>${skillRowsHtml}</tbody>
      </table>
    </section>
  </div>
</body>
</html>
`;
}
