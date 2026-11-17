#!/usr/bin/env node
// Part B: Autopilot Daily Read-Only (--observe) Dogfood & Funnel Runner.
// Strictly GET-only against GitHub: zero issue, label, comment, branch, or PR writes.

import * as nativeFs from 'node:fs';
import { join, resolve, dirname } from 'node:path';
import { homedir, tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import {
  computeNorthStarScorecard,
  roundNum,
  sanitizePublicData,
  sanitizePublicText,
} from './scorecard.mjs';

const DEFAULT_ROOT = fileURLToPath(new URL('../../', import.meta.url));
const REPO_RE = /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/;
const EXTERNAL_SKIP_LABELS = new Set([
  'external',
  'other-repo',
  'elsewhere',
  'pdd:elsewhere',
  'pdd:runtime',
  'wontfix',
  'invalid',
]);
const STUCK_OR_PARKED_LABELS = new Set([
  'pdd:stuck',
  'pdd:would-merge',
  'pdd:autopilot-report',
  'duplicate',
]);
const DECISION_LABELS = new Set([
  'pdd:needs-decision',
  'question',
]);
const SEVEN_DAYS_MS = 7 * 24 * 60 * 60 * 1000;
const DAY_MS = 24 * 60 * 60 * 1000;

export function assertGetOnlyMethod(method) {
  const normalized = String(method || 'GET').toUpperCase();
  if (normalized !== 'GET') {
    throw new Error(`Observe mode forbids non-GET GitHub call: ${normalized}`);
  }
  return 'GET';
}

function parseHttpIncludeResponse(rawOutput = '') {
  const text = String(rawOutput ?? '');
  const matchAll = [...text.matchAll(/^HTTP\/[\d.]+\s+(\d{3})[^\r\n]*\r?\n([\s\S]*?)\r?\n\r?\n/gm)];
  if (!matchAll.length) {
    return { status: 200, etag: null, nextEndpoint: null, body: text };
  }
  const last = matchAll[matchAll.length - 1];
  const status = Number(last[1]);
  const headersRaw = last[2] || '';
  const bodyStart = last.index + last[0].length;
  const body = text.slice(bodyStart);

  let etag = null;
  let nextEndpoint = null;
  for (const line of headersRaw.split(/\r?\n/)) {
    const idx = line.indexOf(':');
    if (idx <= 0) continue;
    const key = line.slice(0, idx).trim().toLowerCase();
    const val = line.slice(idx + 1).trim();
    if (key === 'etag') etag = val;
    else if (key === 'link') {
      const nextMatch = val.match(/<([^>]+)>;\s*rel="next"/i);
      if (nextMatch) {
        const url = nextMatch[1];
        nextEndpoint = url.replace(/^https:\/\/api\.github\.com\//i, '');
      }
    }
  }
  return { status, etag, nextEndpoint, body };
}

export function createObserveEtagCache({ cacheFile, fs = nativeFs, now = Date.now } = {}) {
  let entries = {};
  if (cacheFile && fs.existsSync(cacheFile)) {
    try {
      const parsed = JSON.parse(fs.readFileSync(cacheFile, 'utf8'));
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) entries = parsed;
    } catch {
      entries = {};
    }
  }

  return {
    get(key) {
      const hit = entries[key];
      if (!hit || typeof hit.etag !== 'string' || typeof hit.body !== 'string') return null;
      if (Number.isFinite(hit.saved_at) && now() - hit.saved_at > DAY_MS) return null;
      return hit;
    },
    set(key, { etag, body, nextEndpoint = null }) {
      if (!etag || typeof body !== 'string') return;
      entries[key] = {
        etag,
        body,
        nextEndpoint,
        saved_at: now(),
      };
    },
    save() {
      if (!cacheFile) return;
      const cutoff = now() - DAY_MS;
      const kept = Object.entries(entries)
        .filter(([, v]) => v && typeof v.etag === 'string' && (!v.saved_at || v.saved_at >= cutoff))
        .sort((a, b) => (b[1].saved_at || 0) - (a[1].saved_at || 0))
        .slice(0, 400);
      fs.mkdirSync(dirname(cacheFile), { recursive: true });
      fs.writeFileSync(cacheFile, JSON.stringify(Object.fromEntries(kept)), 'utf8');
    },
  };
}

function nativeExec(cmd, args, options = {}) {
  const res = spawnSync(cmd, args, {
    encoding: 'utf8',
    timeout: options.timeoutMs ?? 60_000,
    maxBuffer: 32 * 1024 * 1024,
    cwd: options.cwd,
    env: options.env ?? process.env,
  });
  return {
    code: res.status ?? 1,
    stdout: res.stdout ?? '',
    stderr: res.stderr ?? '',
  };
}

export function createReadOnlyGithubClient({ exec = nativeExec, etagCache = null } = {}) {
  let apiCalls = 0;
  let conditionalRequests = 0;
  let etagHits = 0;

  function getJson(endpoint, { method = 'GET', allowCachedFullPage = true } = {}) {
    assertGetOnlyMethod(method);
    const cacheKey = endpoint;
    const cached = etagCache ? etagCache.get(cacheKey) : null;
    const ghArgs = ['api', '--include', '--method', 'GET', endpoint];
    if (cached?.etag && allowCachedFullPage) {
      ghArgs.push('-H', `If-None-Match: ${cached.etag}`);
      conditionalRequests += 1;
    }

    apiCalls += 1;
    const res = exec('gh', ghArgs);
    const parsed = parseHttpIncludeResponse(res.stdout);

    if (parsed.status === 304 && cached) {
      etagHits += 1;
      return {
        data: JSON.parse(cached.body),
        nextEndpoint: cached.nextEndpoint || null,
        fromCache: true,
      };
    }

    if (res.code !== 0 || (parsed.status !== 200 && parsed.status !== 304)) {
      throw new Error(`Read-only GitHub GET failed for ${endpoint} (status ${parsed.status || res.code})`);
    }

    const data = JSON.parse(parsed.body);
    if (etagCache && parsed.etag) {
      const perPageMatch = endpoint.match(/[?&]per_page=(\d+)/);
      const perPage = perPageMatch ? Number(perPageMatch[1]) : 30;
      const isFullUnlinkedLastPage = Array.isArray(data) && data.length >= perPage && !parsed.nextEndpoint;
      if (!isFullUnlinkedLastPage) {
        etagCache.set(cacheKey, {
          etag: parsed.etag,
          body: parsed.body,
          nextEndpoint: parsed.nextEndpoint,
        });
      }
    }

    return {
      data,
      nextEndpoint: parsed.nextEndpoint || null,
      fromCache: false,
    };
  }

  function paginateWithMeta(initialEndpoint, { maxPages = 10 } = {}) {
    const items = [];
    let endpoint = initialEndpoint;
    let pages = 0;
    while (endpoint && pages < maxPages) {
      pages += 1;
      const { data, nextEndpoint } = getJson(endpoint);
      if (Array.isArray(data)) items.push(...data);
      endpoint = nextEndpoint;
    }
    return { items, truncated: Boolean(endpoint) };
  }

  function paginate(initialEndpoint, { maxPages = 10 } = {}) {
    return paginateWithMeta(initialEndpoint, { maxPages }).items;
  }

  return {
    getJson,
    paginate,
    paginateWithMeta,
    stats() {
      const hitRate = conditionalRequests > 0 ? roundNum(etagHits / conditionalRequests, 4) : 0;
      return {
        api_calls: apiCalls,
        conditional_requests: conditionalRequests,
        etag_hits: etagHits,
        etag_hit_rate: hitRate,
      };
    },
  };
}

function labelsOf(issue) {
  if (!Array.isArray(issue?.labels)) return [];
  return issue.labels
    .map(l => (typeof l === 'string' ? l : l?.name))
    .filter(name => typeof name === 'string' && name.trim().length > 0)
    .map(name => name.trim().toLowerCase());
}

function extractClosingIssues(text = '', branch = '') {
  const found = new Set();
  for (const m of String(text ?? '').matchAll(/\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?)\s+#(\d+)\b/gi)) {
    found.add(Number(m[1]));
  }
  const branchMatch = String(branch ?? '').match(/^pdd\/(?:core|feature|bug|small-change)-(\d+)\b/i);
  if (branchMatch) found.add(Number(branchMatch[1]));
  return [...found].filter(n => Number.isSafeInteger(n) && n > 0);
}

function extractBlockerIssues(body = '') {
  const blockers = new Set();
  const text = String(body ?? '');
  for (const m of text.matchAll(/\b(?:depends\s+on|blocked\s+by|requires)\s+#(\d+)\b/gi)) {
    blockers.add(Number(m[1]));
  }
  for (const m of text.matchAll(/"blocker"\s*:\s*(\d+)/g)) {
    blockers.add(Number(m[1]));
  }
  return [...blockers].filter(n => Number.isSafeInteger(n) && n > 0);
}

export function inferIssueAreas(issue, intakeCard = null) {
  const fromCard = Array.isArray(intakeCard?.areas) ? intakeCard.areas : [];
  if (fromCard.length) return fromCard.slice(0, 6);

  const areas = new Set();
  for (const lbl of labelsOf(issue)) {
    if (lbl.startsWith('area:')) areas.add(lbl);
  }
  const combined = `${issue?.title ?? ''}\n${issue?.body ?? ''}`;
  for (const m of combined.matchAll(/\b((?:src|prompts|skills|scripts|docs|test|tests|user_stories|contracts)\/[A-Za-z0-9_./-]+)\b/g)) {
    const parts = m[1].split('/');
    areas.add(parts.length >= 2 ? `${parts[0]}/${parts[1]}` : parts[0]);
    if (areas.size >= 6) break;
  }
  return areas.size ? [...areas] : ['general'];
}

function areasConflict(leftAreas = [], rightAreas = []) {
  for (const a of leftAreas) {
    if (a === 'general') continue;
    for (const b of rightAreas) {
      if (b === 'general') continue;
      if (a === b || a.startsWith(`${b}/`) || b.startsWith(`${a}/`)) return true;
    }
  }
  return false;
}

export function buildSpreadDispatchPlan(eligibleRows = [], { slots = 4, intakeCardsByIssue = new Map() } = {}) {
  const sorted = [...eligibleRows].sort((a, b) => {
    const ta = Date.parse(a.created_at || '') || 0;
    const tb = Date.parse(b.created_at || '') || 0;
    return ta - tb || (a.number - b.number);
  });

  const selected = [];
  const queued = [];
  const claimedAreas = [];

  for (const issue of sorted) {
    const card = intakeCardsByIssue.get(issue.number) || null;
    const areas = inferIssueAreas(issue, card);
    if (selected.length < slots) {
      const conflictIdx = claimedAreas.findIndex(existing => areasConflict(existing.areas, areas));
      if (conflictIdx === -1) {
        const slot = selected.length + 1;
        selected.push({
          slot,
          issue: issue.number,
          title: sanitizePublicText(String(issue.title || '').slice(0, 120)),
          areas,
          companions: [],
        });
        claimedAreas.push({ slot, issue: issue.number, areas });
      } else {
        const owner = claimedAreas[conflictIdx];
        if (card?.size === 'small' && selected[conflictIdx].companions.length < 2) {
          selected[conflictIdx].companions.push(issue.number);
        } else {
          queued.push({
            issue: issue.number,
            areas,
            deferred_reason: `area_overlap_with_#${owner.issue}`,
          });
        }
      }
    } else {
      queued.push({
        issue: issue.number,
        areas,
        deferred_reason: 'slot_capacity',
      });
    }
  }

  return {
    slots,
    selected,
    queued_area_overlap: queued.filter(q => q.deferred_reason.startsWith('area_overlap')).length,
    queued_slot_capacity: queued.filter(q => q.deferred_reason === 'slot_capacity').length,
    queued_preview: queued.slice(0, 10),
  };
}

function loadLocalAutopilotContext({
  repo,
  checkoutDir = null,
  autopilotStateDir,
  stateDir = null,
  pddBin,
  fs = nativeFs,
  exec = nativeExec,
  env = process.env,
}) {
  const intakeCardsByIssue = new Map();
  const historyRows = [];
  let resolvedCheckout = checkoutDir ? resolve(checkoutDir) : null;
  let tokensLast7d = null;
  let cacheHitPct = null;
  const mainFixedIssues = new Set();

  if (autopilotStateDir && fs.existsSync(autopilotStateDir)) {
    for (const name of fs.readdirSync(autopilotStateDir)) {
      if (!name.endsWith('.json') || name === 'autopilot-update.json') continue;
      const full = join(autopilotStateDir, name);
      try {
        const st = JSON.parse(fs.readFileSync(full, 'utf8'));
        if (String(st?.repo || '').toLowerCase() !== repo.toLowerCase()) continue;
        if (!resolvedCheckout && st.cwd && fs.existsSync(st.cwd)) {
          resolvedCheckout = st.cwd;
        }
        const coreDir = join(autopilotStateDir, `${name.slice(0, -5)}-core`);
        const histFile = join(coreDir, 'history.jsonl');
        if (fs.existsSync(histFile)) {
          for (const line of fs.readFileSync(histFile, 'utf8').split('\n')) {
            if (!line.trim()) continue;
            try {
              historyRows.push(JSON.parse(line));
            } catch {
              // Ignore malformed line.
            }
          }
        }
      } catch {
        // Ignore unreadable state file.
      }
    }
  }

  if (resolvedCheckout && fs.existsSync(resolvedCheckout)) {
    // Strip all GitHub and SSH credentials and point GH_CONFIG_DIR to an empty directory so local CLI reads can never mutate GitHub.
    const offlineChildEnv = {
      ...env,
      GH_TOKEN: '',
      GITHUB_TOKEN: '',
      GH_ENTERPRISE_TOKEN: '',
      GITHUB_ENTERPRISE_TOKEN: '',
      GH_HOST: '',
      SSH_AUTH_SOCK: '',
      GIT_SSH_COMMAND: 'false',
      GIT_ASKPASS: 'echo',
      GH_PROMPT_DISABLED: '1',
      GIT_TERMINAL_PROMPT: '0',
      GH_CONFIG_DIR: join(stateDir || tmpdir(), '.empty-gh-observe'),
    };
    if (pddBin && fs.existsSync(pddBin)) {
      const intakeRes = exec(
        process.execPath,
        [pddBin, 'autopilot', 'intake', '--json'],
        { cwd: resolvedCheckout, env: offlineChildEnv },
      );
      if (intakeRes.code === 0 && intakeRes.stdout.trim()) {
        try {
          const parsed = JSON.parse(intakeRes.stdout);
          for (const entry of parsed.cards || []) {
            if (Number.isSafeInteger(entry?.issue)) {
              intakeCardsByIssue.set(entry.issue, entry.card || entry.previous || entry.native || null);
            }
          }
        } catch {
          // Ignore non-JSON output.
        }
      }

      const statusRes = exec(
        process.execPath,
        [pddBin, 'autopilot', 'status', '--json'],
        { cwd: resolvedCheckout, env: offlineChildEnv },
      );
      if (statusRes.code === 0 && statusRes.stdout.trim()) {
        try {
          const parsed = JSON.parse(statusRes.stdout);
          const cutoff = Date.now() - SEVEN_DAYS_MS;
          const recent = (parsed.runs || []).filter(
            r => String(r?.repo || '').toLowerCase() === repo.toLowerCase() && Number(r?.outcomeAt || 0) >= cutoff,
          );
          if (recent.length) {
            tokensLast7d = recent.reduce((acc, r) => acc + (Number(r.totalTokens) || 0), 0);
            const hitShares = recent.map(r => r.cacheHitShare).filter(v => typeof v === 'number');
            if (hitShares.length) {
              cacheHitPct = roundNum((hitShares.reduce((a, b) => a + b, 0) / hitShares.length) * 100, 1);
            }
          }
        } catch {
          // Ignore non-JSON output.
        }
      }
    }

    const gitRes = exec('git', ['log', '-n', '200', '--format=%s%n%b'], { cwd: resolvedCheckout, env: offlineChildEnv });
    if (gitRes.code === 0 && gitRes.stdout) {
      for (const n of extractClosingIssues(gitRes.stdout)) {
        mainFixedIssues.add(n);
      }
    }
  }

  return {
    checkoutDir: resolvedCheckout,
    intakeCardsByIssue,
    historyRows,
    mainFixedIssues,
    tokensLast7d,
    cacheHitPct,
  };
}

const HUMAN_INTERVENTION_LABELS = new Set([
  'pdd:needs-decision',
  'pdd:stuck',
  'human-edited',
  'question',
]);

function hasHumanDecisionEvent(events = []) {
  return events.some(ev => (
    ev?.event === 'labeled'
    && HUMAN_INTERVENTION_LABELS.has(String(ev?.label?.name || '').trim().toLowerCase())
  ));
}

function hasReopenedEventWithin7d(events = [], mergedAtMs = null) {
  if (!mergedAtMs || !Number.isFinite(mergedAtMs)) return false;
  return events.some(ev => {
    if (ev?.event !== 'reopened') return false;
    const reopenedMs = Date.parse(ev.created_at || '');
    return Number.isFinite(reopenedMs)
      && reopenedMs >= mergedAtMs
      && reopenedMs - mergedAtMs <= SEVEN_DAYS_MS;
  });
}

function inspectPrCommitProvenance(pr, commits = null) {
  const prLabels = labelsOf(pr);
  if (prLabels.some(l => HUMAN_INTERVENTION_LABELS.has(l))) {
    return { humanEdited: true, singleAuthorVerified: false, botVerified: false };
  }
  const prAuthor = pr?.user?.login || null;
  if (!prAuthor || !Array.isArray(commits) || commits.length === 0) {
    return { humanEdited: false, singleAuthorVerified: false, botVerified: false };
  }
  const logins = new Set();
  let allCommitsResolvedToOpener = true;
  for (const c of commits) {
    const authorLogin = c?.author?.login || null;
    const committerLogin = c?.committer?.login || null;
    if (!authorLogin) {
      allCommitsResolvedToOpener = false;
    } else {
      logins.add(authorLogin);
      if (authorLogin !== prAuthor) allCommitsResolvedToOpener = false;
    }
    if (committerLogin && committerLogin !== 'web-flow') {
      logins.add(committerLogin);
      if (committerLogin !== prAuthor) allCommitsResolvedToOpener = false;
    }
  }
  if (logins.size > 1 || (logins.size === 1 && !logins.has(prAuthor))) {
    return { humanEdited: true, singleAuthorVerified: false, botVerified: false };
  }
  const isBotPr = String(pr?.user?.type || '').toLowerCase() === 'bot' && allCommitsResolvedToOpener;
  return {
    humanEdited: false,
    singleAuthorVerified: allCommitsResolvedToOpener,
    botVerified: Boolean(isBotPr),
  };
}

export function evaluateQualityAndZeroEdit({
  historyRows = [],
  closedPulls = [],
  openIssueMap = new Map(),
  issueEventsByIssue = null,
  prCommitsByPr = null,
  unauditedReopenIssues = new Set(),
  maxEvaluatedRuns = 100,
}) {
  // Pre-pass: build canonical PR -> issue map across both ledger rows and closed PRs so row order never splits or collides.
  const prToIssue = new Map();
  const ledgerPrSet = new Set();
  for (const row of historyRows) {
    const issueNum = Number(row?.issue) || null;
    const prNum = Number(row?.pr) || null;
    if (prNum) ledgerPrSet.add(prNum);
    if (prNum && issueNum && !prToIssue.has(prNum)) {
      prToIssue.set(prNum, issueNum);
    }
  }
  for (const pr of closedPulls) {
    const headRef = String(pr?.head?.ref || pr?.headRefName || '');
    if (!ledgerPrSet.has(pr.number) && !/^pdd\/(?:core|feature|bug|small-change)-\d+/i.test(headRef)) continue;
    const linked = extractClosingIssues(`${pr.title || ''}\n${pr.body || ''}`, headRef);
    if (linked[0] && !prToIssue.has(pr.number)) {
      prToIssue.set(pr.number, linked[0]);
    }
  }

  const byRunKey = new Map();
  const prToKey = new Map();

  for (let idx = 0; idx < historyRows.length; idx++) {
    const row = historyRows[idx];
    const outcome = String(row?.outcome || '');
    if (!['merged', 'would-merge', 'needs-person', 'ended', 'abandoned', 'released'].includes(outcome)) {
      continue;
    }
    const prNum = Number(row.pr) || null;
    const issueNum = Number(row.issue) || (prNum ? prToIssue.get(prNum) : null) || null;
    const key = issueNum ? `issue:${issueNum}` : (prNum ? `pr:${prNum}` : `row:${row.at || idx}`);
    const repairCount = Number(row?.telemetry?.phases?.byPhase?.repair?.count ?? 0)
      || (String(row?.text || '').match(/after\s+(\d+)\s+repair/i) ? Number(RegExp.$1) : 0);
    const isInfraRelease = outcome === 'released' && /out of credits|quota|rate limit|no result/i.test(String(row.text || ''));
    const prev = byRunKey.get(key);

    const seenPrs = new Set(prev?.seenPrs || []);
    if (prNum) seenPrs.add(prNum);
    const multiPrOnSameIssue = seenPrs.size > 1;
    const hadHumanIntervention = Boolean(prev?.hadHumanIntervention || outcome === 'needs-person' || multiPrOnSameIssue);
    // Do not let a trailing transient infra-release overwrite an already-recorded substantive outcome.
    if (prev && !prev.isInfraRelease && isInfraRelease) {
      prev.seenPrs = seenPrs;
      if (multiPrOnSameIssue) prev.hadHumanIntervention = true;
      if (prNum) prToKey.set(prNum, key);
      continue;
    }

    const rowAtMs = Number(row.at) || null;
    const ghMergeTimesByPr = new Map(prev?.ghMergeTimesByPr || []);

    const entry = {
      source: 'ledger',
      issue: issueNum || prev?.issue || null,
      pr: prNum || prev?.pr || null,
      seenPrs,
      outcome,
      ledgerAutoMerged: Boolean(prev?.ledgerAutoMerged || outcome === 'merged'),
      hadLedgerWouldMerge: Boolean(prev?.hadLedgerWouldMerge || outcome === 'would-merge'),
      isInfraRelease,
      hadHumanIntervention,
      repairCount: Math.max(prev?.repairCount || 0, repairCount),
      mergedAtMs: rowAtMs || prev?.mergedAtMs || null,
      ghMergeTimesByPr,
      text: String(row.text || ''),
      prObject: prev?.prObject || null,
    };
    byRunKey.set(key, entry);
    if (entry.pr) prToKey.set(entry.pr, key);
  }

  for (const pr of closedPulls) {
    const headRef = String(pr?.head?.ref || pr?.headRefName || '');
    if (!prToKey.has(pr.number) && !/^pdd\/(?:core|feature|bug|small-change)-\d+/i.test(headRef)) continue;
    const linked = extractClosingIssues(`${pr.title || ''}\n${pr.body || ''}`, headRef);
    const issueNum = prToIssue.get(pr.number) || linked[0] || null;
    const mappedKey = prToKey.get(pr.number) || (issueNum ? `issue:${issueNum}` : `pr:${pr.number}`);
    const existing = byRunKey.get(mappedKey);

    if (!pr?.merged_at) {
      // Closed without merging: mark multi-PR churn on existing runs, or record unledgered rejected Autopilot PR.
      if (existing) {
        existing.seenPrs.add(pr.number);
        if (existing.seenPrs.size > 1) {
          existing.hadHumanIntervention = true;
        }
        prToKey.set(pr.number, mappedKey);
      } else {
        byRunKey.set(mappedKey, {
          source: 'github_closed_pr',
          issue: issueNum,
          pr: pr.number,
          seenPrs: new Set([pr.number]),
          outcome: 'abandoned',
          ledgerAutoMerged: false,
          hadLedgerWouldMerge: false,
          isInfraRelease: false,
          hadHumanIntervention: false,
          repairCount: 0,
          mergedAtMs: null,
          ghMergeTimesByPr: new Map(),
          text: '',
          prObject: pr,
        });
        prToKey.set(pr.number, mappedKey);
      }
      continue;
    }

    const ghMergedMs = Date.parse(pr.merged_at);
    if (existing) {
      existing.seenPrs.add(pr.number);
      if (existing.seenPrs.size > 1) {
        existing.hadHumanIntervention = true;
      }
      // Authoritative GitHub merge supersedes pre-merge ledger state (would-merge or transient infra release).
      existing.outcome = 'merged';
      existing.isInfraRelease = false;
      if (!existing.pr) existing.pr = pr.number;
      if (existing.pr === pr.number) {
        existing.prObject = pr;
        if (Number.isFinite(ghMergedMs)) existing.mergedAtMs = ghMergedMs;
      }
      if (!existing.issue && issueNum) existing.issue = issueNum;
      if (Number.isFinite(ghMergedMs)) existing.ghMergeTimesByPr.set(pr.number, ghMergedMs);
      prToKey.set(pr.number, mappedKey);
      continue;
    }

    const initialMergedMs = Number.isFinite(ghMergedMs) ? ghMergedMs : null;
    const ghMergeTimesByPr = new Map();
    if (initialMergedMs) ghMergeTimesByPr.set(pr.number, initialMergedMs);
    byRunKey.set(mappedKey, {
      source: 'github_closed_pr',
      issue: issueNum,
      pr: pr.number,
      seenPrs: new Set([pr.number]),
      outcome: 'merged',
      ledgerAutoMerged: false,
      hadLedgerWouldMerge: false,
      isInfraRelease: false,
      hadHumanIntervention: false,
      repairCount: 0,
      mergedAtMs: initialMergedMs,
      ghMergeTimesByPr,
      text: '',
      prObject: pr,
    });
    prToKey.set(pr.number, mappedKey);
  }

  let mergedPrs = 0;
  let wouldMergePrs = 0;
  let gradeA = 0;
  let gradeB = 0;
  let gradeC = 0;
  let zeroEditMergedRuns = 0;
  let observeWouldMergeRuns = 0;
  let humanInterventionRuns = 0;
  let failedOrReopenedRuns = 0;
  let unverifiedMergedRuns = 0;
  let infraReleasedRuns = 0;
  let reopened7d = 0;

  const substantiveItems = [];
  for (const item of byRunKey.values()) {
    if (item.isInfraRelease) {
      infraReleasedRuns += 1;
    } else {
      substantiveItems.push(item);
    }
  }

  const itemRecency = it => Math.max(
    it.mergedAtMs || 0,
    ...(it.ghMergeTimesByPr?.values() || []),
    it.pr ? it.pr : 0,
  );
  substantiveItems.sort((a, b) => itemRecency(b) - itemRecency(a));
  const windowItems = Number.isFinite(maxEvaluatedRuns) && maxEvaluatedRuns > 0
    ? substantiveItems.slice(0, maxEvaluatedRuns)
    : substantiveItems;

  for (const item of windowItems) {

    const events = item.issue && issueEventsByIssue?.has(item.issue)
      ? issueEventsByIssue.get(item.issue)
      : null;
    const prCommits = item.pr && prCommitsByPr?.has(item.pr)
      ? prCommitsByPr.get(item.pr)
      : null;
    const commitAudit = item.prObject
      ? inspectPrCommitProvenance(item.prObject, prCommits)
      : { humanEdited: false, singleAuthorVerified: false, botVerified: false };

    const humanTouched = item.hadHumanIntervention
      || commitAudit.humanEdited
      || (events ? hasHumanDecisionEvent(events) : false);

    let wasReopenedWithin7d = false;
    const candidateMergeTimes = item.ghMergeTimesByPr?.size
      ? [...item.ghMergeTimesByPr.values()]
      : (item.mergedAtMs ? [item.mergedAtMs] : []);
    if (item.outcome === 'merged' && item.issue && candidateMergeTimes.length > 0) {
      if (events) {
        wasReopenedWithin7d = candidateMergeTimes.some(ts => hasReopenedEventWithin7d(events, ts));
      } else {
        const openIssue = openIssueMap.get(item.issue);
        const reopenedMs = openIssue?.reopened_at ? Date.parse(openIssue.reopened_at) : NaN;
        if (
          Number.isFinite(reopenedMs)
          && candidateMergeTimes.some(ts => reopenedMs >= ts && reopenedMs - ts <= SEVEN_DAYS_MS)
        ) {
          wasReopenedWithin7d = true;
        }
      }
    }

    const reopenUnaudited = item.outcome === 'merged'
      && (!item.issue || unauditedReopenIssues.has(item.issue));

    if (item.outcome === 'merged') mergedPrs += 1;
    if (item.outcome === 'would-merge') wouldMergePrs += 1;

    if (wasReopenedWithin7d) {
      reopened7d += 1;
      failedOrReopenedRuns += 1;
      gradeC += 1;
    } else if (humanTouched || item.outcome === 'needs-person') {
      humanInterventionRuns += 1;
      gradeC += 1;
    } else if (item.outcome === 'merged') {
      const commitsAudited = Boolean(
        item.pr
        && item.prObject
        && commitAudit.singleAuthorVerified,
      );
      const eventsAudited = Boolean(item.issue && events && !reopenUnaudited);
      const provenanceConfirmed = commitsAudited
        && eventsAudited
        && (item.ledgerAutoMerged || commitAudit.botVerified);
      const observeWouldMergeConfirmed = commitsAudited
        && eventsAudited
        && !provenanceConfirmed
        && item.hadLedgerWouldMerge;
      if (provenanceConfirmed) {
        zeroEditMergedRuns += 1;
        if (item.repairCount <= 1) gradeA += 1;
        else gradeB += 1;
      } else if (observeWouldMergeConfirmed) {
        observeWouldMergeRuns += 1;
        if (item.repairCount <= 1) gradeA += 1;
        else gradeB += 1;
      } else {
        unverifiedMergedRuns += 1;
        gradeC += 1;
      }
    } else if (item.outcome === 'would-merge') {
      observeWouldMergeRuns += 1;
      if (item.repairCount <= 1) gradeA += 1;
      else gradeB += 1;
    } else {
      failedOrReopenedRuns += 1;
      gradeC += 1;
    }
  }

  const evaluatedRuns = zeroEditMergedRuns
    + observeWouldMergeRuns
    + humanInterventionRuns
    + failedOrReopenedRuns
    + unverifiedMergedRuns;
  const observeIncludedRuns = zeroEditMergedRuns + observeWouldMergeRuns;
  const zeroEditPct = evaluatedRuns > 0 ? roundNum((zeroEditMergedRuns / evaluatedRuns) * 100, 1) : null;
  const observeIncludedPct = evaluatedRuns > 0 ? roundNum((observeIncludedRuns / evaluatedRuns) * 100, 1) : null;
  const completedPrs = mergedPrs + wouldMergePrs;
  const reopen7dPct = mergedPrs > 0 ? roundNum((reopened7d / mergedPrs) * 100, 1) : 0;

  return {
    evaluated_runs: evaluatedRuns,
    evaluated_prs: completedPrs,
    merged_prs: mergedPrs,
    would_merge_prs: wouldMergePrs,
    zero_edit_merged_runs: zeroEditMergedRuns,
    observe_would_merge_runs: observeWouldMergeRuns,
    zero_edit_completed_runs: zeroEditMergedRuns,
    observe_included_completed_runs: observeIncludedRuns,
    human_intervention_runs: humanInterventionRuns,
    failed_or_reopened_runs: failedOrReopenedRuns,
    unverified_merged_runs: unverifiedMergedRuns,
    infra_released_runs: infraReleasedRuns,
    zero_edit_completion_pct: zeroEditPct,
    observe_included_completion_pct: observeIncludedPct,
    grade_a: gradeA,
    grade_b: gradeB,
    grade_c: gradeC,
    reopened_7d: reopened7d,
    reopen_7d_pct: reopen7dPct,
  };
}

export function observeRepository({
  repo,
  checkoutDir = null,
  optInLabel = null,
  skipLabels = [],
  slots = 4,
  maxIssuePages = 10,
  maxEvaluatedRuns = 100,
  ghClient,
  localContext = null,
  now = Date.now,
}) {
  if (!REPO_RE.test(String(repo || ''))) {
    throw new Error(`Invalid repository slug: ${repo}`);
  }

  const startMs = now();
  const rawIssues = ghClient.paginate(`repos/${repo}/issues?state=open&per_page=100`, { maxPages: maxIssuePages });
  const openIssues = rawIssues.filter(item => !item?.pull_request && item?.state === 'open');
  const openIssueMap = new Map(openIssues.map(i => [i.number, i]));
  const openIssueNumbers = new Set(openIssues.map(i => i.number));

  const openPulls = ghClient.paginate(`repos/${repo}/pulls?state=open&per_page=100`, { maxPages: 3 });
  const closedPulls = ghClient.paginate(
    `repos/${repo}/pulls?state=closed&sort=updated&direction=desc&per_page=100`,
    { maxPages: 2 },
  );

  const openPrIssues = new Set();
  for (const pr of openPulls) {
    const headRef = pr?.head?.ref || pr?.headRefName || '';
    for (const n of extractClosingIssues(`${pr?.title || ''}\n${pr?.body || ''}`, headRef)) {
      openPrIssues.add(n);
    }
  }

  const mergedMainIssues = new Set(localContext?.mainFixedIssues || []);
  const mergedTimeByIssue = new Map();
  for (const pr of closedPulls) {
    if (!pr?.merged_at) continue;
    const mergedMs = Date.parse(pr.merged_at) || 0;
    const headRef = pr?.head?.ref || pr?.headRefName || '';
    for (const n of extractClosingIssues(`${pr?.title || ''}\n${pr?.body || ''}`, headRef)) {
      mergedMainIssues.add(n);
      mergedTimeByIssue.set(n, Math.max(mergedTimeByIssue.get(n) || 0, mergedMs));
    }
  }

  const extraSkip = new Set(
    (Array.isArray(skipLabels) ? skipLabels : []).map(s => String(s).trim().toLowerCase()).filter(Boolean),
  );
  const intakeCardsByIssue = localContext?.intakeCardsByIssue || new Map();

  const skippedByReason = {
    label_skip: 0,
    blocked_by_graph: 0,
    already_fixed_on_main: 0,
    open_pr_in_flight: 0,
    human_owned: 0,
    needs_decision: 0,
    stuck_or_parked: 0,
  };
  const skippedSamples = {};
  const recordSkip = (reason, issueNumber) => {
    skippedByReason[reason] = (skippedByReason[reason] ?? 0) + 1;
    skippedSamples[reason] ??= [];
    if (skippedSamples[reason].length < 8) skippedSamples[reason].push(issueNumber);
  };

  const eligibleRows = [];
  for (const issue of openIssues) {
    const labels = labelsOf(issue);
    const card = intakeCardsByIssue.get(issue.number) || null;
    const cardClass = String(card?.class || card?.kind || '').toLowerCase();
    const body = String(issue.body || '');

    const hasSkipLabel = labels.some(l => EXTERNAL_SKIP_LABELS.has(l) || extraSkip.has(l))
      || cardClass === 'elsewhere';
    const missingOptIn = optInLabel && !labels.includes(String(optInLabel).toLowerCase());
    if (hasSkipLabel || missingOptIn) {
      recordSkip('label_skip', issue.number);
      continue;
    }

    const mergedMs = mergedTimeByIssue.get(issue.number) || 0;
    const createdMs = Date.parse(issue.created_at || '') || 0;
    const fixedByForensics = body.includes('<!-- pdd:autopilot-forensics:fixed:') || cardClass === 'fixed';
    const fixedOnMain = fixedByForensics || (mergedMainIssues.has(issue.number) && (!mergedMs || mergedMs >= createdMs));
    if (fixedOnMain) {
      recordSkip('already_fixed_on_main', issue.number);
      continue;
    }

    if (openPrIssues.has(issue.number)) {
      recordSkip('open_pr_in_flight', issue.number);
      continue;
    }

    const assigned = (Array.isArray(issue.assignees) && issue.assignees.length > 0) || Boolean(issue.assignee);
    if (assigned || labels.includes('pdd:working') || cardClass === 'held') {
      recordSkip('human_owned', issue.number);
      continue;
    }

    if (labels.some(l => STUCK_OR_PARKED_LABELS.has(l)) || cardClass === 'duplicate') {
      recordSkip('stuck_or_parked', issue.number);
      continue;
    }

    if (labels.some(l => DECISION_LABELS.has(l)) || cardClass === 'person' || cardClass === 'improve') {
      recordSkip('needs_decision', issue.number);
      continue;
    }

    const blockers = extractBlockerIssues(body).filter(n => n !== issue.number && openIssueNumbers.has(n));
    if (blockers.length > 0 || cardClass === 'blocked') {
      recordSkip('blocked_by_graph', issue.number);
      continue;
    }

    eligibleRows.push(issue);
  }

  const dispatchPlan = buildSpreadDispatchPlan(eligibleRows, { slots, intakeCardsByIssue });

  // Audit merged Autopilot issues/PRs via GET-only timeline events and commit authors for 7d reopens & human edits.
  const historyRows = localContext?.historyRows || [];
  const mergedIssuesByRecency = new Map();
  const mergedPrNums = new Set();

  // Fetch any ledger-referenced merged PRs absent from the recent closedPulls window BEFORE building mergedIssuesByRecency.
  const paginateWithMeta = ghClient.paginateWithMeta
    ? (ep, opts) => ghClient.paginateWithMeta(ep, opts)
    : (ep, opts) => ({ items: ghClient.paginate(ep, opts), truncated: false });

  const ledgerIssueByPr = new Map();
  const ledgerPrRecency = new Map();
  for (const row of historyRows) {
    const issueNum = Number(row?.issue) || null;
    const prNum = Number(row?.pr) || null;
    if (prNum && issueNum && !ledgerIssueByPr.has(prNum)) {
      ledgerIssueByPr.set(prNum, issueNum);
    }
    if (prNum) {
      mergedPrNums.add(prNum);
      ledgerPrRecency.set(prNum, Math.max(ledgerPrRecency.get(prNum) || 0, Number(row.at) || 0));
    }
    if (String(row?.outcome || '') === 'merged' && issueNum) {
      mergedIssuesByRecency.set(issueNum, Math.max(mergedIssuesByRecency.get(issueNum) || 0, Number(row.at) || 0));
    }
  }

  const auditLimit = Number.isFinite(maxEvaluatedRuns) && maxEvaluatedRuns > 0
    ? Math.max(100, maxEvaluatedRuns * 2)
    : 200;
  const seenPrNumbers = new Set(closedPulls.map(p => p.number));
  const sortedLedgerPrs = [...ledgerPrRecency.entries()]
    .sort((a, b) => b[1] - a[1])
    .map(([prNum]) => prNum);
  const fetchedLedgerRuns = new Set();
  for (const prNum of sortedLedgerPrs) {
    const runKey = ledgerIssueByPr.has(prNum) ? `issue:${ledgerIssueByPr.get(prNum)}` : `pr:${prNum}`;
    if (fetchedLedgerRuns.has(runKey)) continue;
    if (fetchedLedgerRuns.size >= auditLimit) break;
    fetchedLedgerRuns.add(runKey);
    if (!seenPrNumbers.has(prNum) && ghClient.getJson) {
      try {
        const fetched = ghClient.getJson(`repos/${repo}/pulls/${prNum}`);
        if (fetched?.data?.merged_at) {
          closedPulls.push(fetched.data);
          seenPrNumbers.add(prNum);
        }
      } catch {
        // Leave missing PR unverified.
      }
    }
  }

  for (const pr of closedPulls) {
    if (!pr?.merged_at) continue;
    const headRef = String(pr?.head?.ref || pr?.headRefName || '');
    if (!mergedPrNums.has(pr.number) && !/^pdd\/(?:core|feature|bug|small-change)-\d+/i.test(headRef)) continue;
    mergedPrNums.add(pr.number);
    const linked = extractClosingIssues(`${pr.title || ''}\n${pr.body || ''}`, headRef);
    const issueForAudit = ledgerIssueByPr.get(pr.number) || linked[0] || null;
    if (issueForAudit) {
      const mergedMs = Date.parse(pr.merged_at) || 0;
      mergedIssuesByRecency.set(issueForAudit, Math.max(mergedIssuesByRecency.get(issueForAudit) || 0, mergedMs));
    }
  }

  const issueEventsByIssue = new Map();
  const unauditedReopenIssues = new Set();
  const sortedMergedIssues = [...mergedIssuesByRecency.entries()]
    .sort((a, b) => b[1] - a[1])
    .map(([issueNum]) => issueNum);

  for (let idx = 0; idx < sortedMergedIssues.length; idx++) {
    const issueNum = sortedMergedIssues[idx];
    if (idx >= auditLimit) {
      unauditedReopenIssues.add(issueNum);
      continue;
    }
    try {
      const evRes = paginateWithMeta(`repos/${repo}/issues/${issueNum}/events?per_page=100`, { maxPages: 5 });
      if (evRes.truncated) {
        unauditedReopenIssues.add(issueNum);
      } else {
        issueEventsByIssue.set(issueNum, evRes.items);
      }
    } catch {
      unauditedReopenIssues.add(issueNum);
    }
  }

  const prCommitsByPr = new Map();

  const closedMergedAutopilotPrs = closedPulls
    .filter(pr => {
      if (!pr?.merged_at) return false;
      const headRef = String(pr?.head?.ref || pr?.headRefName || '');
      return mergedPrNums.has(pr.number) || /^pdd\/(?:core|feature|bug|small-change)-\d+/i.test(headRef);
    })
    .sort((a, b) => (Date.parse(b.merged_at) || 0) - (Date.parse(a.merged_at) || 0));
  const auditedCommitRuns = new Set();
  for (const pr of closedMergedAutopilotPrs) {
    const headRef = String(pr?.head?.ref || pr?.headRefName || '');
    const linked = extractClosingIssues(`${pr.title || ''}\n${pr.body || ''}`, headRef);
    const issueKey = ledgerIssueByPr.get(pr.number) || linked[0] || null;
    const runKey = issueKey ? `issue:${issueKey}` : `pr:${pr.number}`;
    if (auditedCommitRuns.has(runKey)) continue;
    if (auditedCommitRuns.size >= auditLimit) break;
    auditedCommitRuns.add(runKey);
    try {
      const cmRes = paginateWithMeta(`repos/${repo}/pulls/${pr.number}/commits?per_page=100`, { maxPages: 3 });
      if (!cmRes.truncated) {
        prCommitsByPr.set(pr.number, cmRes.items);
      }
    } catch {
      // Unaudited commits fall back to unverified_merged_runs.
    }
  }

  const quality = evaluateQualityAndZeroEdit({
    historyRows,
    closedPulls,
    openIssueMap,
    issueEventsByIssue,
    prCommitsByPr,
    unauditedReopenIssues,
    maxEvaluatedRuns,
  });
  if (localContext?.tokensLast7d !== null && localContext?.tokensLast7d !== undefined) {
    quality.tokens_last_7d = localContext.tokensLast7d;
  }
  if (localContext?.cacheHitPct !== null && localContext?.cacheHitPct !== undefined) {
    quality.cache_hit_pct = localContext.cacheHitPct;
  }

  const latencyMs = Math.max(0, now() - startMs);
  const openCount = openIssues.length;
  const eligibleCount = eligibleRows.length;
  const skippedTotal = openCount - eligibleCount;
  const takenPct = openCount > 0 ? roundNum((eligibleCount / openCount) * 100, 1) : 0;

  return {
    schema_version: 'pdd.autopilot.observe.v1',
    timestamp: new Date(now()).toISOString(),
    date: new Date(now()).toISOString().slice(0, 10),
    mode: 'observe',
    mutations: 0,
    repo,
    repo_open_issues: openCount,
    eligible_issues: eligibleCount,
    taken_pct: takenPct,
    skipped_total: skippedTotal,
    skipped_by_reason: skippedByReason,
    skipped_samples: skippedSamples,
    dispatch_plan: dispatchPlan,
    latency_ms: latencyMs,
    quality,
  };
}

export function runAutopilotObserve(options = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const exec = ports.exec ?? nativeExec;
  const now = ports.now ?? Date.now;
  const env = ports.env ?? process.env;
  const home = env.HOME || env.USERPROFILE || homedir();

  const packageRoot = resolve(options.packageRoot || DEFAULT_ROOT);
  const pddBin = resolve(options.pddBin || join(packageRoot, 'bin/pdd.mjs'));
  const stateDir = resolve(options.stateDir || join(home, '.local/state/pdd/observe'));
  const autopilotStateDir = resolve(options.autopilotStateDir || join(home, '.local/state/pdd/autopilot'));
  const outJsonl = resolve(options.outFile || join(stateDir, 'observe-runs.jsonl'));

  let repoSpecs = [];
  if (options.configFile) {
    const cfg = JSON.parse(fs.readFileSync(resolve(options.configFile), 'utf8'));
    if (Array.isArray(cfg.repos)) repoSpecs.push(...cfg.repos);
  }
  for (const r of options.repos || []) {
    if (typeof r === 'string') {
      repoSpecs.push({ repo: r, checkout: options.checkouts?.[r] || null });
    } else if (r && typeof r === 'object') {
      repoSpecs.push(r);
    }
  }
  if (repoSpecs.length === 0) {
    repoSpecs = [{ repo: 'promptdriven/pdd', checkout: options.checkouts?.['promptdriven/pdd'] || null }];
  }

  const etagCache = ports.etagCache ?? createObserveEtagCache({
    cacheFile: join(stateDir, 'observe-etags.json'),
    fs,
    now,
  });

  const records = [];
  for (const spec of repoSpecs) {
    const repoClient = ports.ghClientFactory
      ? ports.ghClientFactory(spec.repo)
      : createReadOnlyGithubClient({ exec, etagCache });

    const localContext = ports.localContextFactory
      ? ports.localContextFactory(spec.repo)
      : loadLocalAutopilotContext({
        repo: spec.repo,
        checkoutDir: spec.checkout || options.checkouts?.[spec.repo] || null,
        autopilotStateDir,
        stateDir,
        pddBin,
        fs,
        exec,
        env,
      });

    const row = observeRepository({
      repo: spec.repo,
      checkoutDir: localContext?.checkoutDir || null,
      optInLabel: spec.optInLabel || null,
      skipLabels: spec.skipLabels || [],
      slots: spec.slots ?? options.slots ?? 4,
      maxIssuePages: spec.maxIssuePages ?? options.maxIssuePages ?? 10,
      ghClient: repoClient,
      localContext,
      now,
    });

    const ghStats = repoClient.stats();
    const enriched = sanitizePublicData({
      ...row,
      ...ghStats,
    });
    records.push(enriched);
  }

  etagCache.save();

  if (options.writeJsonl !== false) {
    fs.mkdirSync(dirname(outJsonl), { recursive: true });
    const lines = records.map(r => JSON.stringify(r)).join('\n') + '\n';
    fs.appendFileSync(outJsonl, lines, 'utf8');
  }

  const northStar = computeNorthStarScorecard({ observeRuns: records });
  return sanitizePublicData({
    schema_version: 'pdd.autopilot.observe-batch.v1',
    generated_at: new Date(now()).toISOString(),
    mode: 'observe',
    mutations: 0,
    jsonl_path: outJsonl,
    runs: records,
    north_star_scorecard: northStar,
  });
}

export function formatObserveSummary(batch) {
  const ap = batch.north_star_scorecard.autopilot_zero_edit;
  const lines = [
    `Autopilot Observe Run (mode=observe · mutations=0 · repos=${batch.runs.length})`,
    `Bar 2 (Autopilot Zero-Edit Merged target ${ap.target_range_pct[0]}-${ap.target_range_pct[1]}% vs ~${ap.baseline_pct}% baseline): ${ap.zero_edit_completion_pct ?? 'n/a'}% merged (${ap.zero_edit_merged_runs}/${ap.evaluated_runs} runs; ${ap.observe_included_completion_pct ?? 'n/a'}% incl. ${ap.observe_would_merge_runs} observe would-merge; 7d reopens=${ap.reopened_7d})`,
  ];
  for (const r of batch.runs) {
    const selectedNums = r.dispatch_plan.selected.map(s => `#${s.issue}`).join(', ') || 'none';
    lines.push(
      `  ${r.repo}: open=${r.repo_open_issues}, eligible=${r.eligible_issues} (${r.taken_pct}%), dispatch=[${selectedNums}], api_calls=${r.api_calls}, etag_hit_rate=${roundNum(r.etag_hit_rate * 100, 1)}%, latency=${r.latency_ms}ms`,
    );
  }
  return sanitizePublicText(lines.join('\n'));
}

function parseCliArgs(argv) {
  const opts = { repos: [], checkouts: {}, mode: 'observe' };
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--observe') opts.mode = 'observe';
    else if (arg === '--repo') opts.repos.push(argv[++i]);
    else if (arg === '--checkout') {
      const pair = String(argv[++i] || '');
      const eq = pair.indexOf('=');
      if (eq > 0) opts.checkouts[pair.slice(0, eq)] = pair.slice(eq + 1);
    } else if (arg === '--config') opts.configFile = argv[++i];
    else if (arg === '--state-dir') opts.stateDir = argv[++i];
    else if (arg === '--autopilot-state-dir') opts.autopilotStateDir = argv[++i];
    else if (arg === '--out') opts.outFile = argv[++i];
    else if (arg === '--slots') opts.slots = Number(argv[++i]);
    else if (arg === '--no-write') opts.writeJsonl = false;
    else if (arg === '--json') opts.json = true;
    else if (arg === '--help' || arg === '-h') opts.help = true;
    else throw new Error(`Unknown argument: ${arg}`);
  }
  return opts;
}

const USAGE = `Usage: node scripts/benchmark/run-autopilot-observe.mjs [--observe] [options]
  --observe                     Run in strict read-only observe mode (default; zero GitHub writes)
  --repo OWNER/REPO             Target repository (repeatable; default: promptdriven/pdd)
  --checkout OWNER/REPO=DIR     Optional local checkout directory for intake/forensics context
  --config FILE                 JSON config file with { "repos": [{ "repo": "...", "checkout": "..." }] }
  --state-dir DIR               Directory for observe-etags.json and observe-runs.jsonl
  --out FILE                    JSONL output path (default: <state-dir>/observe-runs.jsonl)
  --slots N                     Parallel spread-first dispatch slots (default: 4)
  --json                        Print structured JSON result to stdout
`;

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const opts = parseCliArgs(process.argv.slice(2));
    if (opts.help) {
      process.stdout.write(USAGE);
      process.exit(0);
    }
    const batch = runAutopilotObserve(opts);
    if (opts.json) {
      process.stdout.write(`${JSON.stringify(batch, null, 2)}\n`);
    } else {
      process.stdout.write(`${formatObserveSummary(batch)}\n`);
    }
  } catch (err) {
    process.stderr.write(`Autopilot observe error: ${err.message}\n`);
    process.exit(2);
  }
}
