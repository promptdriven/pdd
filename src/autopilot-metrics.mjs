// Generated from prompts/cli/autopilot-metrics.prompt.md (sha256: d378f46f857827af090d4ed83348135a2fd18168180d179fd5e2dafa2ae9135c).
import * as nativeFs from 'node:fs';
import { randomUUID } from 'node:crypto';
import { homedir } from 'node:os';
import { dirname, join } from 'node:path';
import {
  applyMetricsToggle,
  isMetricsEnabled,
  normalizeMetricsConfig,
  normalizeSkill,
  validateRepoName,
} from './metrics-model.mjs';

const JOB_OUTCOMES = new Set(['merged', 'would-merge', 'ended', 'needs-person', 'released', 'abandoned', 'stopped']);
const SKIP_CONFIG_FILES = new Set(['autopilot-update.json', 'metrics-config.json']);

function isPlainObject(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

export function autopilotStateRoot({ stateDir, env = process.env, home = homedir() } = {}) {
  const base = stateDir || env?.PDD_STATE_DIR || join(home || homedir(), '.local', 'state', 'pdd');
  return join(base, 'autopilot');
}

function readJsonSafe(fs, path, fallback = null) {
  try {
    return JSON.parse(fs.readFileSync(path, 'utf8'));
  } catch {
    return fallback;
  }
}

function writeAtomicJson(fs, path, value) {
  const dir = dirname(path);
  fs.mkdirSync(dir, { recursive: true, mode: 0o700 });
  const temp = `${path}.${randomUUID()}.tmp`;
  fs.writeFileSync(temp, `${JSON.stringify(value, null, 2)}\n`, { mode: 0o600 });
  fs.renameSync(temp, path);
}

export function readMetricsConfig(options = {}) {
  const fs = options.fs ?? nativeFs;
  const root = autopilotStateRoot(options);
  return normalizeMetricsConfig(readJsonSafe(fs, join(root, 'metrics-config.json'), null));
}

export function setAutopilotMetricsRecording(options = {}) {
  const fs = options.fs ?? nativeFs;
  const nowFn = options.now ?? Date.now;
  const root = autopilotStateRoot(options);
  const current = readMetricsConfig({ ...options, fs });
  const updated = applyMetricsToggle(current, {
    action: options.action,
    repo: options.repo,
    at: new Date(nowFn()).toISOString(),
  });
  writeAtomicJson(fs, join(root, 'metrics-config.json'), updated);
  return updated;
}

export function recordAutopilotMetric(entry, options = {}) {
  try {
    if (!isPlainObject(entry)) return { recorded: false, enabled: true };
    const fs = options.fs ?? nativeFs;
    const nowFn = options.now ?? Date.now;
    const repo = validateRepoName(entry.repo);
    const config = readMetricsConfig({ ...options, fs });
    if (!isMetricsEnabled(config, repo)) {
      return { recorded: false, enabled: false };
    }
    const issue = Number(entry.issue);
    if (!Number.isSafeInteger(issue) || issue <= 0) return { recorded: false, enabled: true };

    const atIso = typeof entry.at === 'string' && Number.isFinite(Date.parse(entry.at))
      ? new Date(Date.parse(entry.at)).toISOString()
      : typeof entry.at === 'number' && Number.isFinite(entry.at)
        ? new Date(entry.at).toISOString()
        : new Date(nowFn()).toISOString();
    const startedAtIso = typeof entry.startedAt === 'string' && Number.isFinite(Date.parse(entry.startedAt))
      ? new Date(Date.parse(entry.startedAt)).toISOString()
      : typeof entry.startedAt === 'number' && Number.isFinite(entry.startedAt)
        ? new Date(entry.startedAt).toISOString()
        : atIso;

    const record = {
      id: typeof entry.id === 'string' && entry.id.trim() ? entry.id.trim() : `${repo.toLowerCase()}#${issue}@${startedAtIso}`,
      repo,
      issue,
      ...(Array.isArray(entry.issues) && entry.issues.length > 0 ? { issues: entry.issues.filter(n => Number.isSafeInteger(n) && n > 0) } : {}),
      skill: normalizeSkill(entry.skill, {
        pathsOnlyD: entry.pathsOnlyD === true,
        promptChanged: entry.promptChanged,
        title: entry.title,
      }),
      startedAt: startedAtIso,
      at: atIso,
      status: String(entry.status ?? entry.outcome ?? 'ended'),
      pr: Number.isSafeInteger(entry.pr) && entry.pr > 0 ? entry.pr : null,
      gates: isPlainObject(entry.gates) ? entry.gates : {},
      ...(isPlainObject(entry.gateCounts) ? { gateCounts: entry.gateCounts } : {}),
      reopened: entry.reopened === true,
      reverted: entry.reverted === true,
      durationMinutes: typeof entry.durationMinutes === 'number' && Number.isFinite(entry.durationMinutes) && entry.durationMinutes > 0
        ? Math.round(entry.durationMinutes * 100) / 100
        : null,
      ...(typeof entry.promptChanged === 'boolean' ? { promptChanged: entry.promptChanged } : {}),
      ...(typeof entry.pathsOnlyD === 'boolean' ? { pathsOnlyD: entry.pathsOnlyD } : {}),
      ...(typeof entry.title === 'string' && entry.title.trim() ? { title: entry.title.trim().slice(0, 200) } : {}),
    };

    const root = autopilotStateRoot(options);
    const metricsDir = join(root, 'metrics');
    const runsPath = join(metricsDir, 'runs.jsonl');
    fs.mkdirSync(metricsDir, { recursive: true, mode: 0o700 });
    fs.appendFileSync(runsPath, `${JSON.stringify(record)}\n`, { mode: 0o600 });
    return { recorded: true, enabled: true, record };
  } catch {
    return { recorded: false, enabled: true };
  }
}

function inferSkillFromBuildLog(fs, logPath) {
  if (typeof logPath !== 'string' || !logPath) return null;
  try {
    const fd = fs.openSync(logPath, 'r');
    try {
      const buf = Buffer.alloc(262_144);
      const bytes = fs.readSync(fd, buf, 0, buf.length, 0);
      const text = buf.subarray(0, bytes).toString('utf8');
      const matches = [...text.matchAll(/(?<!\$PDD_SKILLS\/)pdd-(small-change|bug|feature)\/SKILL\.md/g)];
      if (matches.length > 0) return matches.at(-1)[1];
    } finally {
      fs.closeSync(fd);
    }
  } catch {
    // Missing or unreadable log is fine.
  }
  return null;
}

function addIssueAndPrKeys(targetSet, item) {
  if (Number.isSafeInteger(item.issue) && item.issue > 0) targetSet.add(`issue:${item.issue}`);
  if (Array.isArray(item.issues)) {
    for (const n of item.issues) {
      if (Number.isSafeInteger(n) && n > 0) targetSet.add(`issue:${n}`);
    }
  }
  if (Number.isSafeInteger(item.pr) && item.pr > 0) targetSet.add(`pr:${item.pr}`);
}

function readRegressedIssues(fs, coreDir) {
  const reopened = new Set();
  const reverted = new Set();
  const postMerge = readJsonSafe(fs, join(coreDir, 'post-merge.json'), null);
  if (!isPlainObject(postMerge)) return { reopened, reverted };
  const entries = Array.isArray(postMerge.items)
    ? postMerge.items
    : Array.isArray(postMerge.merges)
      ? postMerge.merges
      : isPlainObject(postMerge.merges)
        ? Object.values(postMerge.merges)
        : Object.values(postMerge);
  for (const item of entries) {
    if (!isPlainObject(item)) continue;
    if (item.reopened === true) addIssueAndPrKeys(reopened, item);
    if (item.reverted === true) addIssueAndPrKeys(reverted, item);
    if (
      item.reopened !== true
      && item.reverted !== true
      && (item.regression === true || (Array.isArray(item.regressions) && item.regressions.length > 0))
    ) {
      addIssueAndPrKeys(reopened, item);
    }
  }
  return { reopened, reverted };
}

function indexLatestEvidenceByIssue(fs, logsDir) {
  const byIssue = new Map();
  let files = [];
  try {
    files = fs.readdirSync(logsDir);
  } catch {
    return byIssue;
  }
  for (const name of files) {
    const m = /^(\d+)-evidence-([0-9a-f]+)\.json$/i.exec(name);
    if (!m) continue;
    const issue = Number(m[1]);
    const head = m[2].toLowerCase();
    const full = join(logsDir, name);
    let mtimeMs = 0;
    try {
      mtimeMs = fs.statSync(full).mtimeMs || 0;
    } catch {
      continue;
    }
    let list = byIssue.get(issue);
    if (!list) {
      list = [];
      byIssue.set(issue, list);
    }
    list.push({ path: full, head, mtimeMs });
  }
  for (const list of byIssue.values()) {
    list.sort((a, b) => a.mtimeMs - b.mtimeMs);
  }
  return byIssue;
}

function extractPairCount(obj) {
  if (!isPlainObject(obj)) return null;
  const passed = Number(obj.passed ?? obj.pass);
  const total = Number(obj.total ?? obj.applicable ?? obj.count);
  if (Number.isSafeInteger(passed) && Number.isSafeInteger(total) && total > 0 && passed >= 0 && passed <= total) {
    return { passed, total };
  }
  return null;
}

function deriveGates({ evidence, evDoc, outcome, text }) {
  const ev = isPlainObject(evidence) ? evidence : (isPlainObject(evDoc?.evidence) ? evDoc.evidence : {});
  let runtime = ev.runtime?.state ?? null;
  let runtimeCount = extractPairCount(ev.runtime);
  if (Array.isArray(evDoc?.runtime?.lines) && evDoc.runtime.lines.length > 0) {
    const verdicts = evDoc.runtime.lines.map(l => l?.verdict);
    if (!runtime) {
      if (verdicts.includes('other') || verdicts.includes('fail')) runtime = 'fail';
      else if (verdicts.every(v => v === 'pass')) runtime = 'pass';
      else runtime = 'not-run';
    }
    if (!runtimeCount) {
      const passed = verdicts.filter(v => v === 'pass').length;
      runtimeCount = { passed, total: verdicts.length };
    }
  }
  let vectors = ev.vectors?.state ?? evDoc?.vectors?.kinds?.vectors?.state ?? null;
  let formal = ev.formal?.state ?? evDoc?.vectors?.kinds?.formal?.state ?? null;
  const vectorsCount = extractPairCount(ev.vectors) ?? extractPairCount(evDoc?.vectors?.kinds?.vectors);
  const formalCount = extractPairCount(ev.formal) ?? extractPairCount(evDoc?.vectors?.kinds?.formal);
  let suite = evDoc?.suite?.state ?? null;
  let review = evDoc?.review?.state ?? evDoc?.review?.verdict ?? null;
  let ci = evDoc?.ci?.state ?? null;
  let e2e = evDoc?.e2e?.state ?? ev.e2e?.state ?? null;

  const reason = String(text ?? '');
  if (outcome === 'merged' || outcome === 'would-merge') {
    suite ||= 'pass';
    review ||= 'pass';
    if (!ci) ci = 'pass';
  } else if (outcome === 'ended' || outcome === 'failed') {
    if (!suite && /full test suite|suite runner failed/i.test(reason)) suite = 'fail';
    if (!ci && /\bCI check\b.*failed|\bchecks-stuck\b/i.test(reason)) ci = 'fail';
    if (!review && /\bReview FAIL\b|fresh reviewer ended/i.test(reason)) review = 'fail';
    if (!e2e && /\be2e\b.*fail/i.test(reason)) e2e = 'fail';
    if ((!runtime || runtime === 'not-run') && /Runtime coverage went down|saved pdd test check.*failed|Runtime:\s*FAIL/i.test(reason)) {
      runtime = 'fail';
    }
  }
  const gateCounts = {};
  if (runtimeCount) gateCounts.runtime = runtimeCount;
  if (vectorsCount) gateCounts.vectors = vectorsCount;
  if (formalCount) gateCounts.formal = formalCount;
  return {
    gates: { runtime, vectors, formal, suite, review, ci, ...(e2e !== null ? { e2e } : {}) },
    gateCounts: Object.keys(gateCounts).length > 0 ? gateCounts : null,
  };
}

function outcomeRank(status) {
  const s = typeof status === 'string' ? status.trim().toLowerCase() : '';
  if (s === 'merged') return 5;
  if (s === 'would-merge') return 4;
  if (s === 'running') return 3;
  if (s === 'needs-person') return 2;
  return 1;
}

function readCoreRuns(fs, repo, coreDir, nowMs) {
  const runs = [];
  const logsDir = join(coreDir, 'logs');
  const evidenceIndex = indexLatestEvidenceByIssue(fs, logsDir);
  const regressed = readRegressedIssues(fs, coreDir);

  const pickEvidenceDoc = (issue, text) => {
    const candidates = evidenceIndex.get(issue);
    if (!candidates || candidates.length === 0) return null;
    const shaMatch = /\b([0-9a-f]{7,40})\b/i.exec(String(text ?? ''));
    if (shaMatch) {
      const prefix = shaMatch[1].toLowerCase();
      const matched = candidates.findLast(c => c.head.startsWith(prefix));
      if (matched) return readJsonSafe(fs, matched.path, null);
    }
    return readJsonSafe(fs, candidates.at(-1).path, null);
  };

  const historyPath = join(coreDir, 'history.jsonl');
  let historyText = '';
  try {
    historyText = fs.readFileSync(historyPath, 'utf8');
  } catch {
    historyText = '';
  }
  for (const line of historyText.split('\n')) {
    if (!line.trim()) continue;
    let row;
    try {
      row = JSON.parse(line);
    } catch {
      continue;
    }
    if (!isPlainObject(row) || !JOB_OUTCOMES.has(row.outcome)) continue;
    if (!Number.isSafeInteger(row.issue) || row.issue <= 0 || !Number.isFinite(row.at)) continue;

    const evDoc = pickEvidenceDoc(row.issue, row.text);
    const { gates, gateCounts } = deriveGates({
      evidence: row.evidence,
      evDoc,
      outcome: row.outcome,
      text: row.text,
    });
    const wallMin = row.telemetry?.phases?.wallClockMinutes ?? row.telemetry?.phases?.totalDurationMinutes ?? null;
    const durationMinutes = typeof wallMin === 'number' && Number.isFinite(wallMin) && wallMin > 0 ? wallMin : null;
    const startedMs = durationMinutes ? Math.round(row.at - durationMinutes * 60_000) : row.at;
    const logSkill = inferSkillFromBuildLog(fs, row.log);
    const rowLetters = Array.isArray(row.paths?.letters) ? row.paths.letters : [];
    const rowPathsOnlyD = row.pathsOnlyD === true || (rowLetters.length > 0 && rowLetters.every(l => l === 'd'));
    const reopened = row.reopened === true
      || regressed.reopened.has(`issue:${row.issue}`)
      || (Number.isSafeInteger(row.pr) && regressed.reopened.has(`pr:${row.pr}`));
    const reverted = row.reverted === true
      || regressed.reverted.has(`issue:${row.issue}`)
      || (Number.isSafeInteger(row.pr) && regressed.reverted.has(`pr:${row.pr}`));
    const hasPromptCheck = Boolean(gateCounts)
      || ['runtime', 'vectors', 'formal'].some(k => {
        const v = typeof gates[k] === 'string' ? gates[k].trim().toLowerCase() : '';
        return v === 'pass' || v === 'fail' || v === 'proved' || v === 'bounded' || v === 'failed';
      });
    const promptChanged = typeof row.promptChanged === 'boolean'
      ? row.promptChanged
      : typeof evDoc?.promptChanged === 'boolean'
        ? evDoc.promptChanged
        : hasPromptCheck
          ? true
          : undefined;

    runs.push({
      id: `${repo.toLowerCase()}#${row.issue}@${row.at}`,
      repo,
      issue: row.issue,
      ...(Array.isArray(row.issues) && row.issues.length > 0 ? { issues: row.issues } : {}),
      skill: normalizeSkill(row.skill ?? logSkill, {
        pathsOnlyD: rowPathsOnlyD,
        promptChanged,
        title: typeof row.title === 'string' ? row.title : undefined,
      }),
      startedAt: new Date(startedMs).toISOString(),
      at: new Date(row.at).toISOString(),
      status: row.outcome,
      pr: Number.isSafeInteger(row.pr) && row.pr > 0 ? row.pr : null,
      gates,
      ...(gateCounts ? { gateCounts } : {}),
      ...(typeof promptChanged === 'boolean' ? { promptChanged } : {}),
      reopened,
      reverted,
      durationMinutes,
    });
  }

  let jobFiles = [];
  try {
    jobFiles = fs.readdirSync(join(coreDir, 'jobs')).filter(name => name.endsWith('.json'));
  } catch {
    jobFiles = [];
  }
  for (const file of jobFiles) {
    const job = readJsonSafe(fs, join(coreDir, 'jobs', file), null);
    if (!isPlainObject(job) || !Number.isSafeInteger(job.issue) || job.issue <= 0) continue;
    const startedMs = Number.isFinite(job.started) ? job.started : nowMs;
    const updatedMs = Number.isFinite(job.progress?.at) ? job.progress.at : (Number.isFinite(job.prAt) ? job.prAt : startedMs);
    const evDoc = pickEvidenceDoc(job.issue, job.head);
    const { gates, gateCounts } = deriveGates({
      evidence: job.evidence,
      evDoc,
      outcome: 'running',
      text: job.lastError ?? '',
    });
    const logSkill = inferSkillFromBuildLog(fs, job.agent?.log);
    const letters = Array.isArray(job.paths?.letters) ? job.paths.letters : [];
    const pathsOnlyD = letters.length > 0 && letters.every(l => l === 'd');
    const promptChanged = typeof job.promptChanged === 'boolean'
      ? job.promptChanged
      : typeof evDoc?.promptChanged === 'boolean'
        ? evDoc.promptChanged
        : undefined;
    runs.push({
      id: `${repo.toLowerCase()}#${job.issue}@running`,
      repo,
      issue: job.issue,
      ...(Array.isArray(job.issues) && job.issues.length > 0 ? { issues: job.issues } : {}),
      skill: normalizeSkill(job.skill ?? logSkill, {
        pathsOnlyD,
        promptChanged,
        title: job.title,
      }),
      startedAt: new Date(startedMs).toISOString(),
      at: new Date(updatedMs).toISOString(),
      status: 'running',
      pr: Number.isSafeInteger(job.pr) && job.pr > 0 ? job.pr : null,
      gates,
      ...(gateCounts ? { gateCounts } : {}),
      ...(typeof promptChanged === 'boolean' ? { promptChanged } : {}),
      reopened: false,
      reverted: false,
      durationMinutes: null,
    });
  }

  return runs;
}

export function readAutopilotMetricsState(options = {}) {
  const fs = options.fs ?? nativeFs;
  const nowFn = options.now ?? Date.now;
  const nowMs = nowFn();
  const root = autopilotStateRoot(options);
  const config = readMetricsConfig({ ...options, fs });
  let filterLower = null;
  if (typeof options.repoFilter === 'string' && options.repoFilter.trim()) {
    try {
      filterLower = validateRepoName(options.repoFilter).toLowerCase();
    } catch {
      filterLower = null;
    }
  }

  const activeRepos = new Map();
  const coreDirs = {};
  const rememberRepo = (repo, isPreferred = false) => {
    if (typeof repo !== 'string') return;
    try {
      const valid = validateRepoName(repo);
      const lower = valid.toLowerCase();
      if (filterLower && lower !== filterLower) return;
      if (!activeRepos.has(lower) || isPreferred) activeRepos.set(lower, valid);
    } catch {
      // Ignore malformed repo strings.
    }
  };

  const byRunKey = new Map();
  const addRun = (run, preferRecorded = false) => {
    const status = String(run.status ?? run.outcome ?? 'ended');
    const key = `${run.repo.toLowerCase()}#${run.issue}@${status === 'running' ? 'running' : (run.pr ?? run.at)}`;
    const existing = byRunKey.get(key);
    if (!existing) {
      byRunKey.set(key, run);
      return;
    }
    const newRank = outcomeRank(status);
    const prevRank = outcomeRank(existing.status ?? existing.outcome);
    const newAtMs = Date.parse(run.at) || 0;
    const prevAtMs = Date.parse(existing.at) || 0;
    if (
      newRank > prevRank
      || (newRank === prevRank && newAtMs > prevAtMs)
      || (newRank === prevRank && newAtMs === prevAtMs && preferRecorded)
    ) {
      byRunKey.set(key, run);
    }
  };

  let entries = [];
  try {
    entries = fs.readdirSync(root);
  } catch {
    entries = [];
  }

  for (const name of entries.sort()) {
    if (!name.endsWith('.json') || SKIP_CONFIG_FILES.has(name)) continue;
    const cfg = readJsonSafe(fs, join(root, name), null);
    if (!isPlainObject(cfg) || typeof cfg.repo !== 'string') continue;
    if (filterLower && cfg.repo.trim().toLowerCase() !== filterLower) continue;
    const stem = name.slice(0, -5);
    const coreDir = join(root, `${stem}-core`);
    const coreRuns = readCoreRuns(fs, cfg.repo, coreDir, nowMs);
    if (cfg.enabled === true || coreRuns.length > 0) {
      rememberRepo(cfg.repo, cfg.enabled === true);
      const repoLower = cfg.repo.trim().toLowerCase();
      if (!coreDirs[repoLower] || cfg.enabled === true) coreDirs[repoLower] = coreDir;
    }
    for (const r of coreRuns) addRun(r, false);
  }

  const runsPath = join(root, 'metrics', 'runs.jsonl');
  let recordedText = '';
  try {
    recordedText = fs.readFileSync(runsPath, 'utf8');
  } catch {
    recordedText = '';
  }
  for (const line of recordedText.split('\n')) {
    if (!line.trim()) continue;
    try {
      const row = JSON.parse(line);
      if (!isPlainObject(row) || typeof row.repo !== 'string') continue;
      if (filterLower && row.repo.trim().toLowerCase() !== filterLower) continue;
      rememberRepo(row.repo, false);
      addRun(row, true);
    } catch {
      // Skip malformed line.
    }
  }

  return {
    config,
    repos: [...activeRepos.values()],
    runs: [...byRunKey.values()],
    coreDirs,
  };
}
