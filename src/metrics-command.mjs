// Generated from prompts/cli/metrics-command.prompt.md (sha256: f34959daef947465fcf1ee3612ed17159a23c165fe3d67b4043bc4f73701f693).
import { execFile as execFileCb, spawn } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { promisify } from 'node:util';
import {
  autopilotStateRoot,
  readAutopilotMetricsState,
  setAutopilotMetricsRecording,
} from './autopilot-metrics.mjs';
import { regressionScan } from './autopilot-regressions.mjs';
import { nativeGithubCounter } from './github-calls.mjs';
import {
  buildStandupInvestigationSummary,
  calculateAutopilotMetrics,
  formatMetricsText,
  isMetricsEnabled,
  localAnchorUtcMs,
  renderMetricsHtml,
  validateRepoName,
} from './metrics-model.mjs';

const defaultExecFile = nativeGithubCounter(promisify(execFileCb), { purpose: 'other' });
const SUBCOMMANDS = new Set(['stages', 'skills', 'full', 'on', 'off']);
const VALUE_FLAGS = new Set(['--repo', '--date', '--timezone', '--file']);
const BOOL_FLAGS = new Set(['--repos', '--json', '--html', '--standup']);
const DAY_MS = 86_400_000;
const PR_ALIAS_CHUNK = 40;
const MAX_ISSUE_PAGES = 10;

function parseMetricsArgv(argv = []) {
  const words = Array.isArray(argv) ? argv.map(String) : [];
  let index = 0;
  let subcommand = null;
  if (words.length > 0 && !words[0].startsWith('-')) {
    if (!SUBCOMMANDS.has(words[0])) {
      return { error: `Unknown metrics subcommand "${words[0]}". Use stages, skills, full, on, or off.` };
    }
    subcommand = words[0];
    index = 1;
  }

  const options = {};
  const seen = new Set();
  while (index < words.length) {
    const token = words[index++];
    if (!token.startsWith('-')) {
      return { error: `Unexpected argument "${token}" for pdd metrics.` };
    }
    if (seen.has(token)) {
      return { error: `Duplicate option "${token}".` };
    }
    seen.add(token);
    if (BOOL_FLAGS.has(token)) {
      options[token] = true;
      continue;
    }
    if (VALUE_FLAGS.has(token)) {
      const val = words[index++];
      if (val === undefined || !String(val).trim()) {
        return { error: `Option "${token}" requires a value.` };
      }
      options[token] = String(val).trim();
      continue;
    }
    return { error: `Unknown metrics option "${token}".` };
  }

  if (options['--json'] && options['--html']) {
    return { error: 'Choose either --json or --html, not both.' };
  }
  if (options['--file'] && !options['--html']) {
    return { error: 'Option "--file" requires "--html".' };
  }
  if (subcommand === 'on' || subcommand === 'off') {
    for (const forbidden of ['--repos', '--date', '--timezone', '--standup', '--html', '--file']) {
      if (options[forbidden] !== undefined) {
        return { error: `Option "${forbidden}" cannot be used with "pdd metrics ${subcommand}".` };
      }
    }
  } else if ((subcommand === 'stages' || subcommand === 'skills') && options['--repos']) {
    return { error: `Option "--repos" is only supported on "pdd metrics" and "pdd metrics full".` };
  }

  return { subcommand, options };
}

/** UTC bounds covering active windows across any IANA timezone (UTC-12 through UTC+14). */
export function computeWindowBounds(nowMs, dateOption, { standup = false, timezone = null } = {}) {
  if (typeof dateOption === 'string' && /^\d{4}-\d{2}-\d{2}$/.test(dateOption)) {
    const [year, month, day] = dateOption.split('-').map(Number);
    const probe = new Date(Date.UTC(year, month - 1, day));
    const validCal = probe.getUTCFullYear() === year && probe.getUTCMonth() === month - 1 && probe.getUTCDate() === day;
    if (standup && validCal && typeof timezone === 'string' && timezone.trim()) {
      const prev = new Date(Date.UTC(year, month - 1, day - 1));
      try {
        const sinceMs = localAnchorUtcMs(prev.getUTCFullYear(), prev.getUTCMonth() + 1, prev.getUTCDate(), 9, timezone);
        const untilMs = localAnchorUtcMs(year, month, day, 9, timezone) - 1;
        if (Number.isFinite(sinceMs) && Number.isFinite(untilMs) && untilMs >= sinceMs) {
          return { sinceIso: new Date(sinceMs).toISOString(), sinceMs, untilMs };
        }
      } catch {
        // Fall through to conservative UTC bounds when timezone validation fails later.
      }
    }
    const baseMs = Date.parse(`${dateOption}T00:00:00Z`);
    if (Number.isFinite(baseMs)) {
      const sinceMs = baseMs - 2 * DAY_MS;
      return { sinceIso: new Date(sinceMs).toISOString(), sinceMs, untilMs: baseMs + 2 * DAY_MS };
    }
  }
  const sinceMs = nowMs - 8 * DAY_MS;
  return { sinceIso: new Date(sinceMs).toISOString(), sinceMs, untilMs: nowMs };
}

/** Return true when a run's activity, merge time, or running state overlaps `[sinceMs, untilMs]`. */
function isRunInBounds(run, sinceMs, untilMs, mergedAtMs = NaN) {
  const atMs = Date.parse(run.at ?? run.startedAt ?? '');
  if (Number.isFinite(atMs) && atMs >= sinceMs - DAY_MS && atMs <= untilMs) return true;
  if (Number.isFinite(mergedAtMs) && mergedAtMs >= sinceMs - DAY_MS && mergedAtMs <= untilMs) return true;
  if (run.status === 'running') {
    const startMs = Date.parse(run.startedAt ?? run.at ?? '');
    if (Number.isFinite(startMs) && startMs <= untilMs) return true;
  }
  return false;
}

/** Collect distinct PR numbers per target repo from active-window runs. */
function collectActivePrsByRepo(runs, targetRepos, sinceMs, untilMs) {
  const allowed = new Set(targetRepos.map(r => r.toLowerCase()));
  const byRepo = new Map(targetRepos.map(r => [r.toLowerCase(), new Set()]));
  for (const run of Array.isArray(runs) ? runs : []) {
    if (!run || typeof run.repo !== 'string') continue;
    const lower = run.repo.toLowerCase();
    if (!allowed.has(lower)) continue;
    if (!Number.isSafeInteger(run.pr) || run.pr <= 0) continue;
    const mergedAtMs = Date.parse(run.mergedAt ?? '');
    if (isRunInBounds(run, sinceMs, untilMs, mergedAtMs)) {
      byRepo.get(lower).add(run.pr);
    }
  }
  return byRepo;
}

/**
 * Execute a GitHub GraphQL query via `gh api graphql`.
 * Preserves partial `data` when `gh` exits non-zero because of individual GraphQL field errors
 * (e.g. a deleted PR alias) instead of knocking the entire metrics run offline.
 */
async function execGraphql(execFile, query, env) {
  const parseData = rawStdout => {
    try {
      const parsed = JSON.parse(String(rawStdout ?? ''));
      return parsed?.data && typeof parsed.data === 'object' ? parsed.data : null;
    } catch {
      return null;
    }
  };
  try {
    const reply = await execFile('gh', ['api', 'graphql', '-f', `query=${query}`], {
      env,
      encoding: 'utf8',
      timeout: 15_000,
      maxBuffer: 16 * 1024 * 1024,
    });
    return parseData(reply?.stdout);
  } catch (err) {
    return parseData(err?.stdout);
  }
}

const REOPENED_TIMELINE_FIELDS = 'timelineItems(last: 10, itemTypes: [REOPENED_EVENT]) { nodes { ... on ReopenedEvent { createdAt actor { login } } } }';

function recordGraphqlReopenedEvents(map, repoLower, node) {
  if (!node || !Number.isSafeInteger(node.number) || node.number <= 0) return;
  const events = Array.isArray(node.timelineItems?.nodes) ? node.timelineItems.nodes : [];
  if (events.length === 0) return;
  const key = `${repoLower}#${node.number}`;
  let bucket = map.get(key);
  for (const ev of events) {
    const ms = typeof ev?.createdAt === 'string' ? Date.parse(ev.createdAt) : NaN;
    if (!Number.isFinite(ms)) continue;
    const at = new Date(ms).toISOString();
    const actor = typeof ev?.actor?.login === 'string' && ev.actor.login.trim() ? ev.actor.login.trim() : null;
    if (!bucket) {
      bucket = [];
      map.set(key, bucket);
    }
    if (!bucket.some(item => item.at === at)) {
      bucket.push({ at, actor });
    }
  }
}

/** Follow bounded `UPDATED_AT DESC` cursor pagination for a repository's open or closed issues. */
async function paginateRepoIssues({ execFile, env, owner, name, kind, sinceIso, startCursor }) {
  const collected = [];
  let cursor = startCursor;
  for (let page = 0; page < MAX_ISSUE_PAGES && cursor; page++) {
    const fieldExpr = kind === 'closed'
      ? `issues(states: CLOSED, filterBy: { since: ${JSON.stringify(sinceIso)} }, first: 100, after: ${JSON.stringify(cursor)}, orderBy: { field: UPDATED_AT, direction: DESC }) { pageInfo { hasNextPage endCursor } nodes { number closedAt ${REOPENED_TIMELINE_FIELDS} } }`
      : `issues(states: OPEN, first: 100, after: ${JSON.stringify(cursor)}, orderBy: { field: UPDATED_AT, direction: DESC }) { pageInfo { hasNextPage endCursor } nodes { number ${REOPENED_TIMELINE_FIELDS} } }`;
    const query = `query { repo: repository(owner: ${JSON.stringify(owner)}, name: ${JSON.stringify(name)}) { ${fieldExpr} } }`;
    const data = await execGraphql(execFile, query, env);
    const block = data?.repo?.issues;
    if (!Array.isArray(block?.nodes) || block.nodes.length === 0) break;
    collected.push(...block.nodes);
    cursor = block.pageInfo?.hasNextPage && typeof block.pageInfo?.endCursor === 'string'
      ? block.pageInfo.endCursor
      : null;
  }
  return collected;
}

/**
 * Fetch live open issues, closed-in-window issues, and PR merge states for enabled repos
 * in batched GitHub GraphQL requests. Returns offline fallbacks only when GraphQL yields no data.
 */
async function queryGithubMetricsBatch({ repos, prsByRepo, sinceIso, execFile, env }) {
  if (!Array.isArray(repos) || repos.length === 0) {
    return { openIssues: {}, openIssueNumbers: [], closedIssues: [], prStates: [], prMetaByKey: new Map(), reopenedEventsByIssue: new Map(), online: true };
  }
  const aliases = [];
  const fields = [];
  const remainingPrChunks = [];

  for (let i = 0; i < repos.length; i++) {
    const repo = repos[i];
    const [owner, name] = repo.split('/');
    const alias = `r${i}`;
    const lower = repo.toLowerCase();
    const prs = [...(prsByRepo.get(lower) ?? [])].sort((a, b) => a - b);
    const firstChunk = prs.slice(0, PR_ALIAS_CHUNK);
    for (let offset = PR_ALIAS_CHUNK; offset < prs.length; offset += PR_ALIAS_CHUNK) {
      remainingPrChunks.push({ repo, owner, name, prs: prs.slice(offset, offset + PR_ALIAS_CHUNK) });
    }
    const prFields = firstChunk
      .map(n => `pr_${n}: pullRequest(number: ${n}) { number state merged mergedAt title mergeCommit { oid } }`)
      .join(' ');
    aliases.push({ alias, repo, owner, name, lower, prs: firstChunk });
    fields.push(
      `${alias}: repository(owner: ${JSON.stringify(owner)}, name: ${JSON.stringify(name)}) {`
      + ` issues(states: OPEN, first: 100, orderBy: { field: UPDATED_AT, direction: DESC }) { totalCount pageInfo { hasNextPage endCursor } nodes { number ${REOPENED_TIMELINE_FIELDS} } }`
      + ` closedIssues: issues(states: CLOSED, filterBy: { since: ${JSON.stringify(sinceIso)} }, first: 100, orderBy: { field: UPDATED_AT, direction: DESC }) { pageInfo { hasNextPage endCursor } nodes { number closedAt ${REOPENED_TIMELINE_FIELDS} } }`
      + (prFields ? ` ${prFields}` : '')
      + ' }',
    );
  }

  const openIssues = {};
  const openIssueNumbers = [];
  const closedIssues = [];
  const prStates = [];
  const prMetaByKey = new Map();
  const reopenedEventsByIssue = new Map();

  const collectPrNodes = (repo, prs, repoData) => {
    if (!repoData || typeof repoData !== 'object') return;
    const lower = repo.toLowerCase();
    for (const pr of prs) {
      const node = repoData[`pr_${pr}`];
      if (!node || typeof node !== 'object') continue;
      const state = typeof node.state === 'string' ? node.state.toUpperCase() : null;
      const mergedAt = typeof node.mergedAt === 'string' && Number.isFinite(Date.parse(node.mergedAt)) ? node.mergedAt : null;
      const merged = node.merged === true || state === 'MERGED' || mergedAt !== null;
      const mergeCommit = typeof node.mergeCommit?.oid === 'string' && /^[a-f\d]{40}$/i.test(node.mergeCommit.oid)
        ? node.mergeCommit.oid.toLowerCase()
        : null;
      const title = typeof node.title === 'string' ? node.title : null;
      prStates.push({ repo, pr, merged, mergedAt, state });
      prMetaByKey.set(`${lower}#${pr}`, { merged, mergedAt, mergeCommit, title });
    }
  };

  const data = await execGraphql(execFile, `query { ${fields.join(' ')} }`, env);
  if (!data) {
    return { openIssues: null, openIssueNumbers: [], closedIssues: [], prStates: null, prMetaByKey, reopenedEventsByIssue, online: false };
  }

  for (const { alias, repo, owner, name, lower, prs } of aliases) {
    const repoData = data[alias];
    const openBlock = repoData?.issues;
    const total = openBlock?.totalCount;
    openIssues[lower] = Number.isInteger(total) && total >= 0 ? total : null;
    if (Array.isArray(openBlock?.nodes)) {
      const allOpenNodes = [...openBlock.nodes];
      if (openBlock.pageInfo?.hasNextPage && typeof openBlock.pageInfo?.endCursor === 'string') {
        const extraOpen = await paginateRepoIssues({
          execFile,
          env,
          owner,
          name,
          kind: 'open',
          sinceIso,
          startCursor: openBlock.pageInfo.endCursor,
        });
        allOpenNodes.push(...extraOpen);
      }
      const nums = [];
      for (const node of allOpenNodes) {
        if (Number.isSafeInteger(node?.number) && node.number > 0) {
          nums.push(node.number);
          recordGraphqlReopenedEvents(reopenedEventsByIssue, lower, node);
        }
      }
      openIssueNumbers.push({ repo, issues: nums });
    }
    const closedBlock = repoData?.closedIssues;
    if (Array.isArray(closedBlock?.nodes)) {
      const allClosedNodes = [...closedBlock.nodes];
      if (closedBlock.pageInfo?.hasNextPage && typeof closedBlock.pageInfo?.endCursor === 'string') {
        const extraClosed = await paginateRepoIssues({
          execFile,
          env,
          owner,
          name,
          kind: 'closed',
          sinceIso,
          startCursor: closedBlock.pageInfo.endCursor,
        });
        allClosedNodes.push(...extraClosed);
      }
      for (const node of allClosedNodes) {
        if (Number.isSafeInteger(node?.number) && node.number > 0) {
          recordGraphqlReopenedEvents(reopenedEventsByIssue, lower, node);
          if (typeof node?.closedAt === 'string') {
            closedIssues.push({ repo, issue: node.number, closedAt: node.closedAt });
          }
        }
      }
    }
    collectPrNodes(repo, prs, repoData);
  }

  for (const chunk of remainingPrChunks) {
    const prFields = chunk.prs
      .map(n => `pr_${n}: pullRequest(number: ${n}) { number state merged mergedAt title mergeCommit { oid } }`)
      .join(' ');
    const extraQuery = `query { repo: repository(owner: ${JSON.stringify(chunk.owner)}, name: ${JSON.stringify(chunk.name)}) { ${prFields} } }`;
    const extraData = await execGraphql(execFile, extraQuery, env);
    collectPrNodes(chunk.repo, chunk.prs, extraData?.repo);
  }

  return {
    openIssues,
    openIssueNumbers,
    closedIssues,
    prStates: prStates.length > 0 ? prStates : null,
    prMetaByKey,
    reopenedEventsByIssue,
    online: true,
  };
}

function makeGhPort(execFile, env) {
  return async args => {
    try {
      const res = await execFile('gh', args, {
        env,
        encoding: 'utf8',
        timeout: 30_000,
        maxBuffer: 16 * 1024 * 1024,
      });
      return { code: 0, stdout: String(res?.stdout ?? ''), stderr: String(res?.stderr ?? '') };
    } catch (err) {
      return {
        code: typeof err?.code === 'number' ? err.code : 1,
        stdout: String(err?.stdout ?? ''),
        stderr: String(err?.stderr ?? err?.message ?? ''),
      };
    }
  };
}

function extractIssueNumberFromSignal(signal) {
  const urlMatch = typeof signal?.url === 'string' ? /\/issues\/(\d+)(?:[?#]|$)/.exec(signal.url) : null;
  if (urlMatch) return Number(urlMatch[1]);
  const detailMatch = typeof signal?.detail === 'string' ? /\bIssue\s+#(\d+)\b/i.exec(signal.detail) : null;
  if (detailMatch) return Number(detailMatch[1]);
  return null;
}

/** Reuse the shared `regressionScan` engine across active merged PRs (auto, observe, and stopped). */
async function scanMergedRegressions({
  targetRepos,
  runs,
  prStates,
  prMetaByKey,
  reopenedEventsByIssue,
  coreDirs,
  fs,
  gh,
  scanner,
  nowFn,
  sinceMs,
  untilMs,
}) {
  const prStateByKey = new Map();
  for (const state of Array.isArray(prStates) ? prStates : []) {
    if (state && typeof state.repo === 'string' && Number.isSafeInteger(state.pr) && state.pr > 0) {
      prStateByKey.set(`${state.repo.toLowerCase()}#${state.pr}`, state);
    }
  }
  const candidatesByRepo = new Map(targetRepos.map(r => [r.toLowerCase(), new Map()]));
  for (const run of Array.isArray(runs) ? runs : []) {
    if (!run || typeof run.repo !== 'string' || !Number.isSafeInteger(run.pr) || run.pr <= 0) continue;
    const lower = run.repo.toLowerCase();
    const bucket = candidatesByRepo.get(lower);
    if (!bucket) continue;
    const key = `${lower}#${run.pr}`;
    const state = prStateByKey.get(key);
    const meta = prMetaByKey?.get(key) ?? null;
    const mergedAtIso = state?.mergedAt ?? meta?.mergedAt ?? run.mergedAt ?? null;
    const mergedAtMs = Date.parse(mergedAtIso ?? '');
    if (!isRunInBounds(run, sinceMs, untilMs, mergedAtMs)) continue;
    const isMerged = state
      ? state.merged === true
      : (run.status === 'merged' || run.prMerged === true || Number.isFinite(mergedAtMs));
    if (!isMerged) continue;
    if (Number.isFinite(mergedAtMs) && mergedAtMs > untilMs) continue;
    const issues = [
      ...(Number.isSafeInteger(run.issue) && run.issue > 0 ? [run.issue] : []),
      ...(Array.isArray(run.issues) ? run.issues.filter(n => Number.isSafeInteger(n) && n > 0) : []),
    ];
    const prev = bucket.get(run.pr);
    if (!prev) {
      bucket.set(run.pr, {
        pr: run.pr,
        issue: issues[0] ?? null,
        issues: [...new Set(issues)],
        outcome: run.status,
        ...(meta?.mergeCommit ? { mergeCommit: meta.mergeCommit } : {}),
        ...(mergedAtIso ? { mergedAt: mergedAtIso } : {}),
        ...(meta?.title ? { title: meta.title } : {}),
      });
    } else {
      prev.issues = [...new Set([...prev.issues, ...issues])];
      if (prev.issue === null && prev.issues.length > 0) prev.issue = prev.issues[0];
      if (!prev.mergedAt && mergedAtIso) prev.mergedAt = mergedAtIso;
      if (!prev.mergeCommit && meta?.mergeCommit) prev.mergeCommit = meta.mergeCommit;
      if (!prev.title && meta?.title) prev.title = meta.title;
    }
  }

  const earliestAt = list => {
    const valid = list
      .map(v => (typeof v === 'string' ? Date.parse(v) : NaN))
      .filter(Number.isFinite)
      .sort((a, b) => a - b);
    return valid.length > 0 ? new Date(valid[0]).toISOString() : null;
  };
  const graphqlReopensFor = (repo, lower, candidate) => {
    if (!reopenedEventsByIssue || reopenedEventsByIssue.size === 0) return [];
    const mergedAtMs = Date.parse(candidate?.mergedAt ?? '');
    if (!Number.isFinite(mergedAtMs)) return [];
    const found = [];
    for (const issueNum of candidate?.issues ?? []) {
      const events = reopenedEventsByIssue.get(`${lower}#${issueNum}`) ?? [];
      for (const ev of events) {
        const atMs = Date.parse(ev.at);
        if (Number.isFinite(atMs) && atMs > mergedAtMs && atMs <= untilMs) {
          found.push({
            kind: 'reopened',
            level: 'proven',
            at: ev.at,
            url: `https://github.com/${repo}/issues/${issueNum}`,
          });
        }
      }
    }
    return found;
  };

  const regressions = [];
  let complete = true;
  for (const repo of targetRepos) {
    const lower = repo.toLowerCase();
    const candidates = [...(candidatesByRepo.get(lower)?.values() ?? [])];
    if (candidates.length === 0) continue;
    const seenPrs = new Set();
    try {
      const scan = await scanner({
        root: coreDirs?.[lower] ?? null,
        repo,
        candidates,
        prs: candidates.map(c => c.pr),
        includeCi: false,
        boundedPulls: true,
        maxRequests: Math.max(100, candidates.length * 3 + 20),
        fs,
        gh,
        now: nowFn,
      });
      if (scan?.complete === false) complete = false;
      for (const merge of Array.isArray(scan?.merges) ? scan.merges : []) {
        seenPrs.add(merge.pr);
        const candidate = candidatesByRepo.get(lower)?.get(merge.pr) ?? null;
        const rawSignals = Array.isArray(merge?.signals) ? merge.signals : [];
        const gqlReopens = graphqlReopensFor(repo, lower, candidate);
        const reopenedSignals = [
          ...rawSignals.filter(s => s?.kind === 'reopened' && (s?.level === 'proven' || s?.level === undefined)),
          ...gqlReopens,
        ];
        const revertedSignals = rawSignals.filter(s => s?.kind === 'revert' && s?.level === 'proven');
        const referenceSignals = rawSignals.filter(s => s?.kind === 'reference' && s?.level === 'proven');
        const reopened = reopenedSignals.length > 0;
        const reverted = revertedSignals.length > 0;
        const regIssues = new Set();
        for (const signal of referenceSignals) {
          const num = extractIssueNumberFromSignal(signal);
          if (Number.isSafeInteger(num) && num > 0) regIssues.add(num);
        }
        if (reopened || reverted || regIssues.size > 0) {
          const candidateIssues = candidate?.issues ?? [];
          const normalizedSignals = [...reopenedSignals, ...revertedSignals, ...referenceSignals].map(s => ({
            kind: s.kind,
            level: s.level ?? 'proven',
            at: typeof s.at === 'string' && Number.isFinite(Date.parse(s.at)) ? new Date(Date.parse(s.at)).toISOString() : null,
            url: typeof s.url === 'string' ? s.url : null,
          }));
          const reopenedAt = earliestAt(reopenedSignals.map(s => s.at));
          const revertedAt = earliestAt(revertedSignals.map(s => s.at));
          const regressionIssueAt = earliestAt(referenceSignals.map(s => s.at));
          const detectedAt = earliestAt([reopenedAt, revertedAt, regressionIssueAt]);
          regressions.push({
            repo,
            pr: merge.pr,
            issue: merge.issue ?? candidateIssues[0] ?? null,
            issues: candidateIssues.length > 0 ? candidateIssues : (merge.issue ? [merge.issue] : []),
            reopened,
            reverted,
            regressionIssues: [...regIssues].sort((a, b) => a - b),
            ...(reopenedAt ? { reopenedAt } : {}),
            ...(revertedAt ? { revertedAt } : {}),
            ...(regressionIssueAt ? { regressionIssueAt } : {}),
            ...(detectedAt ? { detectedAt } : {}),
            ...(normalizedSignals.length > 0 ? { signals: normalizedSignals } : {}),
          });
        }
      }
    } catch {
      // Mark incomplete instead of silently reporting verified 0 (0.0%).
      complete = false;
    }
    // Preserve GraphQL REOPENED_EVENT signals for any merged candidate not returned by the REST scanner.
    for (const candidate of candidates) {
      if (seenPrs.has(candidate.pr)) continue;
      const gqlReopens = graphqlReopensFor(repo, lower, candidate);
      if (gqlReopens.length === 0) continue;
      const reopenedAt = earliestAt(gqlReopens.map(s => s.at));
      regressions.push({
        repo,
        pr: candidate.pr,
        issue: candidate.issue ?? candidate.issues[0] ?? null,
        issues: candidate.issues,
        reopened: true,
        reverted: false,
        regressionIssues: [],
        ...(reopenedAt ? { reopenedAt, detectedAt: reopenedAt } : {}),
        signals: gqlReopens,
      });
    }
  }
  return { regressions, complete };
}

function defaultOpenBrowser(filePath, platform = process.platform) {
  try {
    const cmd = platform === 'darwin' ? 'open' : platform === 'win32' ? 'cmd' : 'xdg-open';
    const args = platform === 'win32' ? ['/c', 'start', '', filePath] : [filePath];
    const child = spawn(cmd, args, { detached: true, stdio: 'ignore' });
    child.unref();
  } catch {
    // Non-fatal in headless environments.
  }
}

export async function runMetrics({ argv = [], cwd = process.cwd(), env = process.env, stdout = process.stdout, stderr = process.stderr, ports = {} } = {}) {
  const parsed = parseMetricsArgv(argv);
  if (parsed.error) {
    stderr.write(`${parsed.error}\n`);
    return 2;
  }
  const { subcommand, options } = parsed;
  const effectiveEnv = ports.env ?? env ?? process.env;
  const fs = ports.fs ?? nativeFs;
  const nowFn = ports.now ?? Date.now;
  const nowMs = nowFn();

  let validatedRepo = null;
  if (options['--repo']) {
    try {
      validatedRepo = validateRepoName(options['--repo']);
    } catch (err) {
      stderr.write(`${err.message}\n`);
      return 2;
    }
  }

  if (subcommand === 'on' || subcommand === 'off') {
    try {
      const updated = setAutopilotMetricsRecording({
        action: subcommand,
        repo: validatedRepo,
        stateDir: ports.stateDir,
        env: effectiveEnv,
        home: ports.home,
        fs,
        now: nowFn,
      });
      const repoLabel = validatedRepo;
      const effective = isMetricsEnabled(updated, repoLabel);
      if (options['--json']) {
        stdout.write(`${JSON.stringify({
          ok: true,
          action: subcommand,
          repo: repoLabel,
          enabled: effective,
          globalEnabled: updated.enabled,
          repoOverrides: updated.repos,
          updatedAt: updated.updatedAt,
        }, null, 2)}\n`);
      } else {
        const target = repoLabel ? ` for ${repoLabel}` : '';
        const msg = subcommand === 'on'
          ? `Autopilot metrics recording is ON${target}.`
          : `Autopilot metrics recording is OFF${target} (existing history preserved).`;
        stdout.write(`${msg}\n`);
      }
      return 0;
    } catch (err) {
      stderr.write(`${err.message}\n`);
      return err.code ? 2 : 1;
    }
  }

  const resolvedTz = options['--timezone']
    ?? (options['--standup'] ? 'America/Los_Angeles' : (Intl.DateTimeFormat().resolvedOptions().timeZone ?? 'UTC'));

  const localState = readAutopilotMetricsState({
    repoFilter: validatedRepo,
    stateDir: ports.stateDir,
    env: effectiveEnv,
    home: ports.home,
    fs,
    now: nowFn,
  });

  // In unified rollups, exclude repos explicitly turned off via `pdd metrics off --repo` from GitHub queries too.
  const targetRepos = validatedRepo
    ? (localState.repos.length > 0 ? localState.repos : [validatedRepo])
    : localState.repos.filter(repo => localState.config.repos[repo.toLowerCase()] !== false);

  const { sinceIso, sinceMs, untilMs } = computeWindowBounds(nowMs, options['--date'] ?? null, {
    standup: Boolean(options['--standup']),
    timezone: resolvedTz,
  });
  const execFile = ports.execFile ?? defaultExecFile;

  let openIssues = ports.openIssues;
  let openIssueNumbers = ports.openIssueNumbers;
  let closedIssues = ports.closedIssues;
  let prStates = ports.prStates;
  let prMetaByKey = new Map();
  let reopenedEventsByIssue = new Map();
  let githubOnline = ports.openIssues === undefined;

  if (ports.openIssues === undefined) {
    const prsByRepo = collectActivePrsByRepo(localState.runs, targetRepos, sinceMs, untilMs);
    const fetched = await queryGithubMetricsBatch({
      repos: targetRepos,
      prsByRepo,
      sinceIso,
      execFile,
      env: effectiveEnv,
    });
    openIssues = fetched.openIssues;
    openIssueNumbers = openIssueNumbers ?? fetched.openIssueNumbers;
    closedIssues = closedIssues ?? fetched.closedIssues;
    prStates = prStates ?? fetched.prStates;
    prMetaByKey = fetched.prMetaByKey ?? new Map();
    reopenedEventsByIssue = fetched.reopenedEventsByIssue ?? new Map();
    githubOnline = fetched.online;
  }

  let regressions = ports.regressions;
  let regressionsComplete = ports.regressionsComplete ?? true;
  if (regressions === undefined) {
    const shouldScan = Boolean(ports.regressionScan || ports.gh || githubOnline);
    if (shouldScan && targetRepos.length > 0) {
      const gh = ports.gh ?? makeGhPort(execFile, effectiveEnv);
      const scanned = await scanMergedRegressions({
        targetRepos,
        runs: localState.runs,
        prStates,
        prMetaByKey,
        reopenedEventsByIssue,
        coreDirs: localState.coreDirs,
        fs,
        gh,
        scanner: ports.regressionScan ?? regressionScan,
        nowFn,
        sinceMs,
        untilMs,
      });
      regressions = scanned.regressions;
      regressionsComplete = scanned.complete;
    } else {
      regressions = [];
      if (ports.regressionsComplete === undefined && ports.openIssues === undefined && !githubOnline && targetRepos.length > 0) {
        regressionsComplete = false;
      }
    }
  }

  const reopenedEvents = [];
  for (const [key, list] of reopenedEventsByIssue.entries()) {
    const hashIdx = key.lastIndexOf('#');
    if (hashIdx <= 0) continue;
    const repoLower = key.slice(0, hashIdx);
    const issueNum = Number(key.slice(hashIdx + 1));
    if (!Number.isSafeInteger(issueNum) || issueNum <= 0) continue;
    const repoName = targetRepos.find(r => r.toLowerCase() === repoLower) ?? repoLower;
    for (const ev of Array.isArray(list) ? list : []) {
      const reopenedAt = typeof ev === 'string' ? ev : (ev?.reopenedAt ?? ev?.createdAt ?? ev?.at ?? null);
      if (reopenedAt) reopenedEvents.push({ repo: repoName, issue: issueNum, reopenedAt });
    }
  }

  let investigation = ports.investigation;
  if (investigation === undefined) {
    const allowedRepos = new Set(targetRepos.map(r => r.toLowerCase()));
    const rawIncidents = Array.isArray(ports.investigationIncidents)
      ? ports.investigationIncidents
      : (Array.isArray(localState.incidents) ? localState.incidents : []);
    const isHistoricalDate = Boolean(options['--date']);
    const scopedIncidents = rawIncidents.filter(inc => {
      if (!inc || typeof inc !== 'object') return false;
      const repoMatch = inc.repo
        ? allowedRepos.has(String(inc.repo).trim().toLowerCase())
        : (!validatedRepo && targetRepos.length > 0);
      if (!repoMatch) return false;
      const rawAt = inc.at ?? inc.ts;
      const atMs = typeof rawAt === 'number' && Number.isFinite(rawAt)
        ? rawAt
        : (typeof rawAt === 'string' ? Date.parse(rawAt) : NaN);
      if (Number.isFinite(atMs)) {
        return atMs >= sinceMs && atMs <= untilMs;
      }
      return !isHistoricalDate;
    });
    if (scopedIncidents.length > 0) {
      try {
        const standupInv = await buildStandupInvestigationSummary({
          incidents: scopedIncidents,
          repo: validatedRepo ?? (targetRepos.length === 1 ? targetRepos[0] : null),
          date: options['--date'] ?? null,
          timezone: resolvedTz,
          now: nowFn,
        });
        if (standupInv?.report?.summary?.uniqueFindings > 0) {
          investigation = standupInv.report;
        }
      } catch {
        // Non-fatal: metrics remain usable even if investigation summary fails.
      }
    }
  }

  const view = subcommand ?? 'overview';
  let report;
  try {
    report = calculateAutopilotMetrics({
      runs: localState.runs,
      repos: localState.repos,
      openIssues,
      openIssueNumbers,
      closedIssues,
      prStates,
      regressions,
      regressionsComplete,
      reopenedEvents,
      flakeEntries: ports.flakeEntries ?? localState.flakes,
      ...(ports.recurringFlakes !== undefined ? { recurringFlakes: ports.recurringFlakes } : {}),
      ...(investigation ? { investigation } : {}),
      view,
      byRepo: Boolean(options['--repos']),
      repoFilter: validatedRepo,
      date: options['--date'] ?? null,
      standup: Boolean(options['--standup']),
      timezone: resolvedTz,
      now: new Date(nowMs).toISOString(),
      recording: localState.config,
    });
  } catch (err) {
    stderr.write(`${err.message}\n`);
    return 2;
  }

  if (options['--json']) {
    stdout.write(`${JSON.stringify(report, null, 2)}\n`);
    return 0;
  }

  if (options['--html']) {
    const outPath = options['--file']
      ? resolve(cwd, options['--file'])
      : join(autopilotStateRoot({ stateDir: ports.stateDir, env: effectiveEnv, home: ports.home }), 'metrics', 'pdd-metrics.html');
    try {
      (fs.mkdirSync ?? nativeFs.mkdirSync)(dirname(outPath), { recursive: true, mode: 0o700 });
      (fs.writeFileSync ?? nativeFs.writeFileSync)(outPath, renderMetricsHtml(report), 'utf8');
    } catch (err) {
      stderr.write(`Could not write HTML report to ${outPath}: ${err.message}\n`);
      return 1;
    }
    stdout.write(`Wrote Autopilot metrics HTML report to ${outPath}\n`);
    const shouldOpen = ports.openBrowser !== false
      && effectiveEnv?.PDD_NO_OPEN !== '1'
      && effectiveEnv?.CI !== 'true'
      && !effectiveEnv?.NODE_TEST_CONTEXT;
    if (shouldOpen) {
      (typeof ports.openBrowser === 'function' ? ports.openBrowser : defaultOpenBrowser)(outPath);
    }
    return 0;
  }

  stdout.write(`${formatMetricsText(report, { view })}\n`);
  return 0;
}
