// Generated from prompts/cli/autopilot-regressions.prompt.md (sha256: 38db0c18aadfdbda8ebfe2d98fa4ce1eda5a8cd9739440241bcb643a27335941).
import * as nativeFs from 'node:fs';
import { join, resolve } from 'node:path';
import { homedir } from 'node:os';
import { createHash } from 'node:crypto';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { githubReply } from './github-calls.mjs';
import { githubOriginRepository } from './workflow-worktree.mjs';
import { redactSecrets } from './secret-redaction.mjs';

const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const positive = value => Number.isSafeInteger(value) && value > 0;
const repository = value => typeof value === 'string' && /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(value);
const sha = value => typeof value === 'string' && /^[a-f\d]{40}$/i.test(value);
const time = value => typeof value === 'string' && Number.isFinite(Date.parse(value)) ? Date.parse(value) : null;
const iso = value => time(value) === null ? null : new Date(time(value)).toISOString();
const safe = value => redactSecrets(String(value ?? '')).replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 500);
const link = value => typeof value === 'string' && /^https:\/\//.test(value) ? safe(value) : null;
const machineMarker = value => /<!--\s*pdd:[\s\S]*?-->/.test(String(value ?? ''));
const latestTime = value => time(value.completed_at ?? value.started_at ?? value.created_at) ?? -Infinity;
const refPattern = /https:\/\/github\.com\/([\w.-]+\/[\w.-]+)\/(pull|issues)\/(\d+)\b|\b([\w.-]+\/[\w.-]+)#(\d+)\b|(?<![\w/#])#(\d+)\b/gi;
function references(text, repo) {
  return [...String(text ?? '').matchAll(refPattern)].map(m => ({ repo: (m[1] ?? m[4] ?? repo).toLowerCase(), number: Number(m[3] ?? m[5] ?? m[6]), type: m[2] ?? null }));
}
function exactTargets(text, phrase, repo) {
  const expression = new RegExp(`\\b${phrase}\\s*:?\\s*(?:PR\\s+)?(https:\\/\\/github\\.com\\/[\\w.-]+\\/[\\w.-]+\\/pull\\/\\d+\\b|[\\w.-]+\\/[\\w.-]+#\\d+\\b|#\\d+\\b)`, 'gi');
  const lower = repo.toLowerCase();
  const nums = new Set();
  for (const m of String(text ?? '').matchAll(expression)) {
    for (const r of references(m[1], repo)) {
      if (r.repo === lower && positive(r.number)) nums.add(r.number);
    }
  }
  return [...nums];
}
const BLAME_PHRASES = ['Regressed by', 'Regression from', 'Regression in', 'Broken by', 'Caused by', 'Introduced by'];

function exactReference(text, phrase, repo, pr) {
  return exactTargets(text, phrase, repo).includes(pr);
}

/** Return true if a GitHub issue carries the case-insensitive `regression` label. */
function hasRegressionLabel(issue) {
  if (!Array.isArray(issue?.labels)) return false;
  return issue.labels.some(label => {
    const name = typeof label === 'string' ? label : label?.name;
    return typeof name === 'string' && name.trim().toLowerCase() === 'regression';
  });
}

/** Return true if text explicitly attributes a regression to the merged PR. */
function blamesMergePr(text, repo, pr) {
  return BLAME_PHRASES.some(phrase => exactReference(text, phrase, repo, pr));
}

/** Extract unique positive issue numbers from a history or candidate row. */
function rowIssues(row) {
  return [...new Set([row?.issue, ...(Array.isArray(row?.issues) ? row.issues : [])].filter(positive))];
}

/**
 * Collect deduplicated PR candidates from core history JSONL and optional caller candidates.
 * Includes both auto-merged rows (`outcome === 'merged'`) and non-merged PR-bearing rows
 * (`would-merge`, `stopped`, `ended`, `needs-person`, `released`, `abandoned`).
 */
function collectCandidateRows({ history = '', candidates = null, repo, prs = null, errors = null }) {
  const repoLower = repo.toLowerCase();
  const byPr = new Map();
  const ordered = [];
  const acceptRow = (row, fromHistory) => {
    if (!object(row)) {
      if (fromHistory && errors) errors.push('Invalid core history line.');
      return;
    }
    const claimedMerged = row.outcome === 'merged';
    if (row.repo !== undefined && !repository(row.repo)) {
      if (errors) errors.push(claimedMerged ? 'Merged history row has no valid repository.' : 'History row has no valid repository.');
      return;
    }
    if (row.repo && row.repo.toLowerCase() !== repoLower) return;
    if (!positive(row.pr)) {
      if (claimedMerged && errors) errors.push('Merged history row has no valid PR.');
      return;
    }
    const issues = rowIssues(row);
    const primaryIssue = positive(row.issue) ? row.issue : (issues[0] ?? null);
    const historyAt = Number.isFinite(row.at) ? row.at : null;
    const mergeCommit = sha(row.mergeCommit) ? row.mergeCommit.toLowerCase() : null;
    const mergedAt = iso(row.mergedAt) ?? null;
    const title = typeof row.title === 'string' ? row.title : null;
    const existing = byPr.get(row.pr);
    if (existing) {
      if (claimedMerged) existing.claimedMerged = true;
      if (existing.issue === null && primaryIssue !== null) existing.issue = primaryIssue;
      existing.issues = [...new Set([...existing.issues, ...issues])];
      if (existing.historyAt === null && historyAt !== null) existing.historyAt = historyAt;
      if (existing.mergeCommit === null && mergeCommit !== null) existing.mergeCommit = mergeCommit;
      if (existing.mergedAt === null && mergedAt !== null) existing.mergedAt = mergedAt;
      if (existing.title === null && title !== null) existing.title = title;
      return;
    }
    const entry = { pr: row.pr, issue: primaryIssue, issues, claimedMerged, historyAt, mergeCommit, mergedAt, title };
    byPr.set(row.pr, entry);
    ordered.push(entry);
  };
  for (const line of String(history).split('\n').filter(item => item.trim())) {
    let row;
    try { row = JSON.parse(line); }
    catch {
      if (errors) errors.push('Invalid core history line.');
      continue;
    }
    acceptRow(row, true);
  }
  if (Array.isArray(candidates)) {
    for (const candidate of candidates) acceptRow(candidate, false);
  }
  if (Array.isArray(prs) && prs.length > 0) {
    const allowed = new Set(prs.filter(positive));
    return ordered.filter(item => allowed.has(item.pr));
  }
  return ordered;
}
const checkStates = ['queued', 'in_progress', 'completed', 'waiting', 'requested', 'pending'];
const conclusions = ['success', 'failure', 'neutral', 'cancelled', 'skipped', 'timed_out', 'action_required', 'startup_failure', 'stale'];
const validCheck = row => positive(row.id) && typeof row.name === 'string' && row.name.length > 0 && positive(row.app?.id)
  && checkStates.includes(row.status) && (row.conclusion == null ? row.status !== 'completed' : conclusions.includes(row.conclusion));
const validStatus = row => positive(row.id) && typeof row.context === 'string' && row.context.length > 0 && ['success', 'failure', 'pending', 'error'].includes(row.state);
const validIssue = row => positive(row.number) && time(row.created_at) !== null;
const validEvent = row => typeof row.event === 'string' && (!['reopened', 'cross-referenced'].includes(row.event) || time(row.created_at) !== null)
  && (row.event !== 'cross-referenced' || validIssue(row.source?.issue ?? {}));
function latest(rows, key) {
  const result = new Map();
  for (const row of rows) {
    const id = key(row), previous = result.get(id);
    if (id && (!previous || latestTime(row) > latestTime(previous) || latestTime(row) === latestTime(previous) && Number(row.id ?? 0) > Number(previous.id ?? 0))) result.set(id, row);
  }
  return result;
}

/** Return true when a page is monotonically descending in `updated_at` and reaches `<= sinceIso`. */
function isDescendingPastSince(rows, sinceIso) {
  if (rows.length === 0 || rows.some(r => time(r.updated_at) === null)) return false;
  for (let i = 1; i < rows.length; i += 1) {
    if (time(rows[i].updated_at) > time(rows[i - 1].updated_at)) return false;
  }
  return time(rows[rows.length - 1].updated_at) <= time(sinceIso);
}

function resolveNextPage(nextUrl, prefix, endpoint) {
  const u = new URL(nextUrl);
  if (u.origin !== 'https://api.github.com' || u.username || u.password || u.hash) {
    throw Error('GitHub pagination points outside this repository.');
  }
  if (u.pathname.toLowerCase().startsWith(`/${prefix.toLowerCase()}`)) {
    return prefix + u.pathname.slice(prefix.length + 1) + u.search;
  }
  // GitHub Link headers commonly use canonical /repositories/<id>/<subpath> URLs;
  // rewrite matching same-endpoint paths back onto repos/<owner>/<repo>/ so requests never leave this repo.
  const endpointPath = endpoint.split('?')[0];
  const numericRepoMatch = /^\/repositories\/[1-9]\d*\/(.+)$/.exec(u.pathname);
  if (numericRepoMatch && numericRepoMatch[1] === endpointPath) {
    return prefix + endpointPath + u.search;
  }
  throw Error('GitHub pagination points outside this repository.');
}

// All network traffic passes through a single GET-only boundary. A failed page
// remains incomplete instead of silently looking like the end of pagination.
function reader(ports, errors, maxRequests = 100) {
  const prefix = `repos/${ports.repo}/`;
  const limit = positive(maxRequests) ? maxRequests : 100;
  let requests = 0, stopped = null;
  const request = async endpoint => {
    const unavailable = () => Object.assign(Error(`GitHub read unavailable: ${endpoint.split('?')[0]}`), { scanStop: stopped });
    if (requests >= limit && !stopped) stopped = `request budget exhausted (${limit} reads)`;
    if (stopped) throw unavailable();
    requests++;
    // execFile rejects nonzero exits but retains HTTP headers on error.stdout.
    let response;
    try { response = await ports.gh(['api', '--include', '--method', 'GET', endpoint]); }
    catch (error) { response = error; }
    const parsed = githubReply(response?.stdout);
    const headers = String(response?.stdout ?? '').split(/\r?\n\r?\n/, 1)[0];
    if (parsed?.status === 429 || parsed?.rate?.remaining <= 0) stopped = 'GitHub rate limit exhausted';
    else if (parsed && /^retry-after:/im.test(headers)) stopped = 'GitHub Retry-After received';
    if ((response?.code ?? 0) !== 0 || parsed?.status !== 200) throw unavailable();
    try { return { value: JSON.parse(parsed.body), next: parsed.link?.match(/<([^>]+)>;\s*rel="next"/)?.[1] }; }
    catch { throw unavailable(); }
  };
  const one = async endpoint => (await request(prefix + endpoint)).value;
  const all = async (endpoint, field, valid = () => true, { stopAfterPage } = {}) => {
    let next = prefix + endpoint; const seen = new Set(), rows = [];
    try {
      while (next) {
        if (!next.startsWith(prefix) || seen.has(next)) throw Error('GitHub pagination is invalid or cyclic.');
        seen.add(next);
        const page = await request(next), values = field ? page.value?.[field] : page.value;
        if (!Array.isArray(values) || values.some(row => !object(row) || !valid(row))) throw Error(`Malformed GitHub list: ${endpoint.split('?')[0]}`);
        rows.push(...values); next = null;
        if (stopAfterPage?.(values)) break;
        if (page.next) {
          next = resolveNextPage(page.next, prefix, endpoint);
        }
      }
    } catch (error) { error.partial = rows; throw error; }
    return rows;
  };
  const attempt = async (label, action, fallback = null, merge = null) => {
    try { return await action(); }
    catch (error) {
      const detail = safe(`Unavailable ${label}${error.scanStop ? `: ${error.scanStop}` : ''}`); errors.push(detail);
      if (merge) merge.signals.push({ kind: 'unavailable', level: 'suspect', at: null, url: null, detail, parentUrl: null });
      return Array.isArray(fallback) && Array.isArray(error.partial) ? error.partial : fallback;
    }
  };
  return { one, all, attempt };
}

export async function regressionScan(ports) {
  if (!ports || (!ports.root && !Array.isArray(ports.candidates)) || !repository(ports.repo) || typeof ports.gh !== 'function') {
    throw Error('Regression scan requires root, repo and gh ports.');
  }
  const fs = ports.fs ?? nativeFs, now = (ports.now ?? Date.now)(), errors = [], merges = [];
  let history = '';
  if (ports.root) {
    try { history = fs.readFileSync(join(ports.root, 'history.jsonl'), 'utf8'); }
    catch (error) { if (error.code !== 'ENOENT') errors.push('Core merge history is unreadable.'); }
  }
  const candidates = collectCandidateRows({
    history,
    candidates: ports.candidates,
    repo: ports.repo,
    prs: ports.prs,
    errors,
  });
  const includeCi = ports.includeCi !== false;
  const boundedPulls = ports.boundedPulls === true;
  const api = reader(ports, errors, ports.maxRequests), titles = new Map(), mergeIssuesByPr = new Map();
  for (const candidate of candidates) {
    const preResolved = !includeCi
      && sha(candidate.mergeCommit)
      && time(candidate.mergedAt) !== null
      && time(candidate.mergedAt) <= now;
    let rawPull = null;
    let pullReadOk = false;
    if (preResolved) {
      rawPull = {
        number: candidate.pr,
        merge_commit_sha: candidate.mergeCommit,
        merged_at: candidate.mergedAt,
        title: candidate.title,
      };
      pullReadOk = true;
    } else {
      try {
        rawPull = await api.one(`pulls/${candidate.pr}`);
        pullReadOk = object(rawPull) && rawPull.number === candidate.pr;
      } catch (error) {
        const detail = safe(`Unavailable PR #${candidate.pr}${error.scanStop ? `: ${error.scanStop}` : ''}`);
        errors.push(detail);
        merges.push({
          repo: ports.repo,
          pr: candidate.pr,
          issue: candidate.issue,
          mergeCommit: null,
          parent: null,
          mergedAt: null,
          classification: 'ok',
          provenAt: null,
          signals: [{ kind: 'unavailable', level: 'suspect', at: null, url: null, detail, parentUrl: null }],
        });
        mergeIssuesByPr.set(candidate.pr, candidate.issues);
        continue;
      }
      if (!candidate.claimedMerged && pullReadOk && rawPull.merged_at == null) {
        // Unmerged observe/stopped candidate: skip cleanly with no error.
        continue;
      }
    }
    const merge = {
      repo: ports.repo,
      pr: candidate.pr,
      issue: candidate.issue,
      mergeCommit: null,
      parent: null,
      mergedAt: null,
      classification: 'ok',
      provenAt: null,
      signals: [],
    };
    merges.push(merge);
    mergeIssuesByPr.set(candidate.pr, candidate.issues);
    if (!pullReadOk || !sha(rawPull.merge_commit_sha) || time(rawPull.merged_at) === null || time(rawPull.merged_at) > now) {
      const detail = safe(`Unavailable PR #${merge.pr}`);
      errors.push(detail);
      merge.signals.push({ kind: 'unavailable', level: 'suspect', at: null, url: null, detail, parentUrl: null });
      continue;
    }
    const pull = rawPull;
    merge.mergeCommit = pull.merge_commit_sha.toLowerCase(); merge.mergedAt = iso(pull.merged_at); titles.set(merge.pr, pull.title);
    if (!includeCi) continue;
    const commit = await api.attempt(`merge parent for PR #${merge.pr}`, async () => {
      const value = await api.one(`commits/${merge.mergeCommit}`);
      if (!object(value) || value.sha?.toLowerCase() !== merge.mergeCommit || !sha(value.parents?.[0]?.sha)) throw Error();
      return value;
    }, null, merge);
    if (commit) merge.parent = commit.parents[0].sha.toLowerCase();
    const observations = new Map();
    for (const ref of [merge.mergeCommit, merge.parent].filter(Boolean)) {
      const checks = await api.attempt(`check runs at ${ref}`, () => api.all(`commits/${ref}/check-runs?filter=all&per_page=100`, 'check_runs', validCheck), [], merge);
      const statuses = await api.attempt(`commit statuses at ${ref}`, () => api.all(`commits/${ref}/statuses?per_page=100`, null, validStatus), [], merge);
      observations.set(ref, new Map([
        ...latest(checks, row => typeof row.name === 'string' && row.app?.id != null ? `check:${row.app.id}:${row.name}` : null),
        ...latest(statuses, row => typeof row.context === 'string' ? `status:${row.context}` : null),
      ]));
    }
    for (const [key, row] of observations.get(merge.mergeCommit) ?? []) {
      const state = row.state ?? row.conclusion, at = iso(row.completed_at ?? row.created_at ?? row.started_at);
      if (!['failure', 'error', 'timed_out', 'cancelled', 'action_required', 'startup_failure', 'stale'].includes(state) || at && time(at) > now) continue;
      const before = observations.get(merge.parent)?.get(key), green = (before?.state ?? before?.conclusion) === 'success';
      const proven = green && at !== null && time(at) >= time(merge.mergedAt);
      merge.signals.push({ kind: 'ci', level: proven ? 'proven' : 'suspect', at, url: link(row.html_url ?? row.target_url), detail: safe(`${row.name ?? row.context}: ${state}${proven ? '; success on first parent' : '; no matching green parent'}`), parentUrl: link(before?.html_url ?? before?.target_url) });
    }
  }
  const valid = merges.filter(m => m.mergedAt), since = valid.map(m => m.mergedAt).sort()[0];
  if (since) {
    const before = errors.length;
    const issues = await api.attempt('repository issues', () => api.all(`issues?state=all&since=${encodeURIComponent(since)}&per_page=100`, null, validIssue), []);
    const pullsEndpoint = boundedPulls ? 'pulls?state=all&sort=updated&direction=desc&per_page=100' : 'pulls?state=all&per_page=100';
    const pulls = await api.attempt(
      'repository PRs',
      () => api.all(
        pullsEndpoint,
        null,
        row => positive(row.number) && time(row.created_at) !== null && (row.merged_at == null || time(row.merged_at) !== null),
        boundedPulls ? { stopAfterPage: rows => isDescendingPastSince(rows, since) } : undefined,
      ),
      [],
    );
    const commits = await api.attempt('default branch commits', () => api.all(`commits?since=${encodeURIComponent(since)}&per_page=100`, null, row => sha(row.sha) && typeof row.commit?.message === 'string' && time(row.commit?.committer?.date) !== null), []);
    const sharedErrors = errors.slice(before);
    for (const merge of valid) {
      const later = at => time(at) !== null && time(at) > time(merge.mergedAt) && time(at) <= now;
      const allIssues = mergeIssuesByPr.get(merge.pr) ?? (merge.issue ? [merge.issue] : []);
      const add = (kind, level, at, url, detail) => merge.signals.push({ kind, level, at: iso(at), url: link(url), detail: safe(detail), parentUrl: null });
      for (const detail of sharedErrors) add('unavailable', 'suspect', null, null, detail);
      for (const commit of commits) {
        const at = commit.commit?.committer?.date, text = String(commit.commit?.message ?? '');
        if (later(at) && [...text.matchAll(/\bThis reverts commit ([a-f\d]{40})(?:\.|,\s+reversing\s+changes made to [a-f\d]{40}\.)/gi)].some(m => m[1].toLowerCase() === merge.mergeCommit)) add('revert', 'proven', at, commit.html_url, `Commit ${commit.sha} reverts merge ${merge.mergeCommit}`);
      }
      for (const pull of pulls) {
        if (pull.number === merge.pr) continue;
        const at = pull.merged_at ?? pull.created_at;
        if (!later(at)) continue;
        const exact = exactReference(pull.body, 'Reverts', ports.repo, merge.pr);
        if (exact || titles.get(merge.pr) && pull.title === `Revert "${titles.get(merge.pr)}"`) add('revert', exact && pull.merged_at ? 'proven' : 'suspect', at, pull.html_url, `PR #${pull.number} ${pull.merged_at ? 'merged' : 'proposed'} revert of #${merge.pr}`);
      }
      const inspectIssue = (issue, viaCrossRef = false, refTarget = null) => {
        if (!object(issue) || issue.pull_request || !positive(issue.number) || !later(issue.created_at)) return;
        const ownUrl = `https://github.com/${ports.repo.toLowerCase()}/issues/`;
        if (issue.html_url && !issue.html_url.toLowerCase().startsWith(ownUrl) || issue.repository_url && issue.repository_url.toLowerCase() !== `https://api.github.com/repos/${ports.repo.toLowerCase()}`) return;
        const text = `${issue.title ?? ''}\n${issue.body ?? ''}`;
        const linksMerge = viaCrossRef || references(text, ports.repo).some(r => r.repo === ports.repo.toLowerCase() && (r.number === merge.pr || allIssues.includes(r.number)));
        if (blamesMergePr(text, ports.repo, merge.pr)) {
          add('reference', 'proven', issue.created_at, issue.html_url, `Issue #${issue.number}: Regressed by #${merge.pr}`);
        } else if (hasRegressionLabel(issue) && linksMerge) {
          add('reference', 'proven', issue.created_at, issue.html_url, `Issue #${issue.number} (regression) links to #${merge.pr}`);
        } else if (linksMerge) {
          add('reference', 'suspect', issue.created_at, issue.html_url, viaCrossRef && refTarget ? `Issue #${issue.number} cross-references #${refTarget}` : `Issue #${issue.number} links to the merged PR or issue`);
        }
      };
      issues.forEach(issue => inspectIssue(issue, false));
      for (const number of new Set([merge.pr, ...allIssues].filter(Boolean))) {
        const events = await api.attempt(`timeline #${number}`, () => api.all(`issues/${number}/timeline?per_page=100`, null, validEvent), [], merge);
        for (const event of events) {
          if (!later(event.created_at)) continue;
          if (event.event === 'reopened' && allIssues.includes(number)) {
            const marked = machineMarker(event.body) || events.some(comment => comment.event === 'commented' && machineMarker(comment.body) && comment.user?.login && comment.user.login === event.actor?.login && Math.abs(time(comment.created_at) - time(event.created_at)) <= 5 * 60 * 1000);
            if (!marked) add('reopened', 'suspect', event.created_at, `https://github.com/${ports.repo}/issues/${number}#event-${event.id ?? ''}`, `Issue #${number} reopened after merge`);
          }
          if (event.event === 'cross-referenced') {
            const source = event.source?.issue;
            if (!source || source.pull_request || !later(source.created_at) || !source.html_url?.toLowerCase().startsWith(`https://github.com/${ports.repo.toLowerCase()}/issues/`)) continue;
            inspectIssue(source, true, number);
          }
        }
      }
    }
  }
  const counts = { ok: 0, suspect: 0, proven: 0 }, days = new Map();
  for (const merge of merges) {
    merge.signals = merge.signals.filter((signal, index, rows) => rows.findIndex(other => JSON.stringify(other) === JSON.stringify(signal)) === index);
    const proofs = merge.signals.filter(s => s.level === 'proven');
    merge.classification = proofs.length ? 'proven' : merge.signals.length ? 'suspect' : 'ok';
    merge.provenAt = proofs.map(s => s.at).filter(Boolean).sort()[0] ?? null;
    counts[merge.classification]++;
    if (merge.provenAt) { const date = merge.provenAt.slice(0, 10); days.set(date, (days.get(date) ?? 0) + 1); }
  }
  return { schema: 'pdd.autopilot-regressions.v1', scannedAt: new Date(now).toISOString(), complete: errors.length === 0, merges, counts, days: [...days].sort(([a], [b]) => a.localeCompare(b)).map(([date, proven]) => ({ date, proven })), errors };
}

const POST_MERGE_SCHEMA = 'pdd.autopilot-post-merge.v1';
const DEFAULT_POST_MERGE_MAX_REQUESTS = 40;
const DEFAULT_POST_MERGE_MAX_MERGES = 10;
const DEFAULT_POST_MERGE_RECHECK_MS = 15 * 60 * 1000;
const RED_STATES = ['failure', 'error', 'timed_out', 'cancelled', 'action_required', 'startup_failure', 'stale'];

function emptyPostMergeCounts(tracked = 0, pending = 0) {
  return { tracked, pending, ok: 0, reopened: 0, reverted: 0, ci: 0, regressions: 0, reopenOrRevert: 0, suspect: 0 };
}

function readSavedPostMerge(fs, file) {
  try {
    const parsed = JSON.parse(fs.readFileSync(file, 'utf8'));
    if (object(parsed) && parsed.schema === POST_MERGE_SCHEMA && object(parsed.merges)) return parsed;
  } catch { /* Missing or invalid file starts fresh. */ }
  return { schema: POST_MERGE_SCHEMA, cursor: 0, merges: {} };
}

function savePostMerge(fs, root, file, state) {
  const payload = JSON.stringify(state, null, 2) + '\n';
  fs.mkdirSync?.(root, { recursive: true, mode: 0o700 });
  if (typeof fs.renameSync === 'function' && typeof fs.writeFileSync === 'function') {
    const temp = `${file}.${process.pid}.tmp`;
    fs.writeFileSync(temp, payload, { mode: 0o600 });
    fs.renameSync(temp, file);
  } else {
    fs.writeFileSync(file, payload, { mode: 0o600 });
  }
}

const validPostMergeCheck = row => positive(row.id) && typeof row.name === 'string' && row.name.length > 0
  && (row.app == null || positive(row.app?.id))
  && checkStates.includes(row.status)
  && (row.conclusion == null ? row.status !== 'completed' : conclusions.includes(row.conclusion));

const compactCheck = row => ({
  id: row.id,
  name: row.name,
  app: row.app?.id != null ? { id: row.app.id } : null,
  status: row.status,
  conclusion: row.conclusion ?? null,
  completed_at: row.completed_at ?? null,
  started_at: row.started_at ?? null,
  created_at: row.created_at ?? null,
  html_url: link(row.html_url ?? row.details_url),
});
const compactStatus = row => ({
  id: row.id,
  context: row.context,
  state: row.state,
  created_at: row.created_at ?? null,
  target_url: link(row.target_url),
});

function incrementalReader(ports, maxRequests, initialStreams = {}) {
  const prefix = `repos/${ports.repo}/`;
  const streams = {};
  for (const [k, v] of Object.entries(object(initialStreams) ? initialStreams : {})) {
    if (object(v)) streams[k] = { ...v, ...(Array.isArray(v.items) ? { items: [...v.items] } : {}), ...(Array.isArray(v.seen) ? { seen: [...v.seen] } : {}) };
  }
  let requests = 0, stopped = null;
  const makeBudgetError = reason => Object.assign(Error(`Post-merge budget stopped: ${reason}`), { budgetStop: reason });
  const request = async fullEndpoint => {
    if (requests >= maxRequests && !stopped) stopped = `request budget exhausted (${maxRequests} reads)`;
    if (stopped) throw makeBudgetError(stopped);
    requests += 1;
    let response;
    try { response = await ports.gh(['api', '--include', '--method', 'GET', fullEndpoint]); }
    catch (error) { response = error; }
    const parsed = githubReply(response?.stdout);
    const headers = String(response?.stdout ?? '').split(/\r?\n\r?\n/, 1)[0];
    if (parsed?.status === 429 || (parsed?.rate && parsed.rate.remaining <= 0)) stopped = 'GitHub rate limit exhausted';
    else if (parsed && /^retry-after:/im.test(headers)) stopped = 'GitHub Retry-After received';
    if ((response?.code ?? 0) !== 0 || parsed?.status !== 200) {
      if (stopped) throw makeBudgetError(stopped);
      throw Object.assign(Error(`GitHub GET unavailable: ${fullEndpoint.split('?')[0]}`), { status: parsed?.status ?? 0 });
    }
    try {
      return {
        value: JSON.parse(parsed.body),
        next: parsed.link?.match(/<([^>]+)>;\s*rel="next"/)?.[1] ?? null,
      };
    } catch {
      if (stopped) throw makeBudgetError(stopped);
      throw Object.assign(Error(`Malformed GitHub JSON: ${fullEndpoint.split('?')[0]}`), { status: 200 });
    }
  };
  const get = async endpoint => (await request(prefix + endpoint)).value;
  const readOnce = async (streamKey, endpoint, validate = () => true) => {
    const existing = streams[streamKey];
    if (existing?.done && existing.value !== undefined) return existing.value;
    const value = await get(endpoint);
    if (!validate(value)) throw Error(`Invalid GitHub resource: ${endpoint.split('?')[0]}`);
    streams[streamKey] = { done: true, value };
    return value;
  };
  const readStream = async (streamKey, endpoint, { field = null, valid = () => true, mergePage = (acc, rows) => [...acc, ...rows], stopAfterPage = null, onPage = null } = {}) => {
    const existing = streams[streamKey];
    if (existing?.done && Array.isArray(existing.items)) return existing.items;
    const seen = new Set(Array.isArray(existing?.seen) ? existing.seen : []);
    let next = typeof existing?.next === 'string' && existing.next ? existing.next : prefix + endpoint;
    let items = Array.isArray(existing?.items) ? existing.items : [];
    while (next) {
      if (!next.startsWith(prefix) || seen.has(next)) throw Error('GitHub pagination is invalid or cyclic.');
      const page = await request(next);
      const values = field ? page.value?.[field] : page.value;
      if (!Array.isArray(values) || values.some(row => !object(row) || !valid(row))) {
        throw Error(`Malformed GitHub list: ${endpoint.split('?')[0]}`);
      }
      seen.add(next);
      items = mergePage(items, values);
      if (onPage) onPage(values, items);
      let resolvedNext = null;
      if (page.next && !(stopAfterPage && stopAfterPage(values))) {
        resolvedNext = resolveNextPage(page.next, prefix, endpoint);
      }
      next = resolvedNext;
      streams[streamKey] = { next, done: next === null, items, seen: [...seen] };
    }
    return items;
  };
  return {
    get,
    readOnce,
    readStream,
    streams: () => streams,
    requests: () => requests,
    remaining: () => Math.max(0, maxRequests - requests),
    stopped: () => stopped,
  };
}

function collectCiObservations(checkRows, statusRows) {
  return new Map([
    ...latest(checkRows, row => `check:${row.app?.id ?? 'app'}:${row.name}`),
    ...latest(statusRows, row => `status:${row.context}`),
  ]);
}

function mergeSignalList(existing, incoming) {
  const out = [];
  const seen = new Set();
  for (const raw of [...existing, ...incoming]) {
    if (!object(raw)) continue;
    const stripped = (({ key: _k, ...rest }) => rest)(raw);
    const id = `${stripped.kind}:${stripped.level}:${stripped.issue ?? ''}:${stripped.at ?? ''}:${stripped.detail}`;
    if (!seen.has(id)) {
      seen.add(id);
      out.push(stripped);
    }
  }
  return out;
}

function recordProvenSignals(entry, signals, newlyDetected) {
  const provenSignals = signals.filter(s => s.level === 'proven');
  if (provenSignals.length === 0) return;
  if (provenSignals.some(s => s.kind === 'reopened')) entry.reopened = true;
  if (provenSignals.some(s => s.kind === 'revert')) entry.reverted = true;
  if (provenSignals.some(s => s.kind === 'ci')) entry.ciRegression = true;
  entry.signals = mergeSignalList(entry.signals.filter(s => s.level === 'proven'), provenSignals);
  entry.classification = 'proven';
  entry.status = entry.reverted ? 'reverted' : entry.reopened ? 'reopened' : 'ci';
  const reportedSet = new Set(entry.reportedKeys);
  for (const sig of provenSignals) {
    if (reportedSet.has(sig.key)) continue;
    reportedSet.add(sig.key);
    const code = sig.kind === 'revert' ? 'post-merge-revert'
      : sig.kind === 'reopened' ? 'post-merge-reopen'
      : 'post-merge-ci';
    newlyDetected.push({
      pr: entry.pr,
      issue: sig.issue ?? entry.issue,
      issues: entry.issues,
      mergeCommit: entry.mergeCommit,
      mergedAt: entry.mergedAt,
      kind: sig.kind,
      code,
      at: sig.at,
      url: sig.url,
      detail: sig.detail,
    });
  }
  entry.reportedKeys = [...reportedSet];
}

function computePostMergeCounts(mergeRows, entries) {
  const activeRows = mergeRows.filter(row => !entries.get(row.pr)?.unmerged);
  const counts = emptyPostMergeCounts(activeRows.length, 0);
  for (const row of activeRows) {
    const entry = entries.get(row.pr);
    if (!entry || entry.status === 'pending') { counts.pending += 1; continue; }
    if (entry.reopened) counts.reopened += 1;
    if (entry.reverted) counts.reverted += 1;
    if (entry.ciRegression) counts.ci += 1;
    if (entry.reopened || entry.reverted) counts.reopenOrRevert += 1;
    if (entry.reopened || entry.reverted || entry.ciRegression) counts.regressions += 1;
    else if (entry.status === 'suspect') counts.suspect += 1;
    else counts.ok += 1;
  }
  return counts;
}

export function selectCircuitBreakerRegression(newlyDetected, options = {}) {
  if (!Array.isArray(newlyDetected) || !newlyDetected.length) return null;
  const isRevert = item => object(item) && (item.kind === 'revert' || item.kind === 'reverted' || item.code === 'post-merge-revert');
  const isCi = item => object(item) && (item.kind === 'ci' || item.kind === 'ci_broken' || item.code === 'post-merge-ci');
  const clearedAfter = Number.isFinite(options.clearedAfter) ? options.clearedAfter : time(options.clearedAfter);
  const eligible = clearedAfter === null ? newlyDetected : newlyDetected.filter(item => {
    if (!object(item)) return false;
    const atMs = time(item.at);
    const mergedAtMs = time(item.mergedAt);
    if (atMs !== null && atMs <= clearedAfter) return false;
    if (isCi(item) && mergedAtMs !== null && mergedAtMs <= clearedAfter) return false;
    if (atMs === null && mergedAtMs !== null && mergedAtMs <= clearedAfter) return false;
    return true;
  });
  const chosen = eligible.find(isRevert) ?? eligible.find(isCi);
  if (!chosen || !positive(chosen.pr)) return null;
  const kind = isRevert(chosen) ? 'reverted' : 'ci_broken';
  const code = isRevert(chosen) ? 'post-merge-revert' : 'post-merge-ci';
  const issue = positive(chosen.issue) ? chosen.issue : Array.isArray(chosen.issues) ? chosen.issues.find(positive) ?? null : null;
  const nowMs = (options.now ?? Date.now)();
  const trippedAt = new Date(Number.isFinite(nowMs) ? nowMs : Date.now()).toISOString();
  const detail = typeof chosen.detail === 'string' && chosen.detail.trim()
    ? safe(chosen.detail).slice(0, 240)
    : kind === 'reverted' ? 'merged change was reverted on the default branch' : 'default-branch CI failed after merge';
  const reason = `PR #${chosen.pr}${issue ? ` (issue #${issue})` : ''} ${kind === 'reverted' ? 'reverted' : 'broke default-branch CI'}: ${detail}`;
  return {
    active: true,
    kind,
    code,
    pr: chosen.pr,
    issue,
    trippedAt,
    url: link(chosen.url),
    reason,
  };
}

const UNIVERSAL_NON_SHARD = /\b(?:lint|typecheck|build|install|setup|format|audit)\b/i;
function parseShardFamily(name) {
  if (typeof name !== 'string') return null;
  const trimmed = name.trim();
  if (!trimmed || trimmed.length > 300) return null;
  const closeChar = trimmed[trimmed.length - 1];
  if (closeChar === ')' || closeChar === ']') {
    const openChar = closeChar === ')' ? '(' : '[';
    const openIdx = trimmed.lastIndexOf(openChar);
    if (openIdx > 0) {
      const inner = trimmed.slice(openIdx + 1, -1);
      if (!/[()\[\]]/.test(inner)) {
        const family = trimmed.slice(0, openIdx).trim().toLowerCase();
        const member = inner.trim().toLowerCase();
        if (!family || !member) return null;
        const familyNamedShard = /\b(?:shard|shards|matrix)\b/.test(family);
        if (!familyNamedShard && UNIVERSAL_NON_SHARD.test(`${family} ${member}`)) return null;
        const indexedMember = /\b(?:shard|part|slice|chunk)[-_\s]{0,4}\d+\b/.test(member)
          || /\b\d+\s{0,4}\/\s{0,4}\d+\b/.test(member)
          || member.split(',').some(part => /^\d+$/.test(part.trim()));
        return familyNamedShard || indexedMember ? family : null;
      }
    }
  }
  const suffix = /[-_/\s]{1,8}(?:shard|matrix)[-_\s]{0,8}\d+(?:[-_\s]{0,8}of[-_\s]{0,8}\d+|\s{0,4}\/\s{0,4}\d+)?$/i.exec(trimmed);
  if (suffix && suffix.index > 0) {
    const prefix = trimmed.slice(0, suffix.index).trim();
    if (prefix && !UNIVERSAL_NON_SHARD.test(prefix)) {
      return `${prefix.toLowerCase()}:shard`;
    }
  }
  return null;
}

const normCheckValue = value => typeof value === 'string' ? value.trim().toLowerCase() : '';
const PENDING_CHECK_STATUSES = new Set(['queued', 'in_progress', 'waiting', 'requested', 'pending']);
const extractRunId = row => {
  const id = row?.run_id ?? row?.runId;
  if (positive(id)) return id;
  const url = String(row?.details_url ?? row?.detailsUrl ?? row?.html_url ?? row?.htmlUrl ?? '');
  return Number(/\/actions\/runs\/(\d+)/.exec(url)?.[1] ?? 0) || null;
};
const goodConclusion = conclusion => ['success', 'neutral', 'skipped'].includes(normCheckValue(conclusion));
const isPendingCheckRun = row => PENDING_CHECK_STATUSES.has(normCheckValue(row?.status));
const isCompletedCheckRun = row => normCheckValue(row?.status) === 'completed'
  || (!isPendingCheckRun(row) && Boolean(normCheckValue(row?.conclusion)));

export function evaluateShardFlakeRerun({ checkRuns = [], statuses = [], headSha = '', flakeRerunHead = null } = {}) {
  if (typeof headSha !== 'string' || !headSha || flakeRerunHead === headSha) return { action: 'none' };
  if (!Array.isArray(checkRuns) || !checkRuns.length) return { action: 'none' };
  if (Array.isArray(statuses) && statuses.some(s => {
    if (!object(s)) return false;
    const state = normCheckValue(s.state);
    return state !== 'pending' && state !== 'success';
  })) {
    return { action: 'none' };
  }
  const validRuns = checkRuns.filter(r => object(r) && typeof r.name === 'string' && r.name.trim());
  const completed = validRuns.filter(isCompletedCheckRun);
  const pending = validRuns.filter(isPendingCheckRun);
  const failedRuns = completed.filter(r => !goodConclusion(r.conclusion));
  if (failedRuns.length < 1 || failedRuns.length > 2) return { action: 'none' };

  const familyOf = new Map();
  const groups = new Map();
  for (const run of validRuns) {
    const family = parseShardFamily(run.name);
    familyOf.set(run, family);
    if (family) {
      if (!groups.has(family)) groups.set(family, []);
      groups.get(family).push(run);
    }
  }
  const failedFamilies = new Set();
  for (const run of failedRuns) {
    const family = familyOf.get(run);
    if (!family) return { action: 'none' };
    failedFamilies.add(family);
  }
  const failedRunIds = new Set(failedRuns.map(extractRunId).filter(Boolean));
  const sameWorkflowPending = pending.some(r => {
    const id = extractRunId(r);
    return id !== null && failedRunIds.has(id);
  });

  let needsSiblingWait = sameWorkflowPending;
  for (const family of failedFamilies) {
    const members = groups.get(family) ?? [];
    const groupFailed = members.filter(r => isCompletedCheckRun(r) && !goodConclusion(r.conclusion));
    const groupSucceeded = members.filter(r => isCompletedCheckRun(r) && normCheckValue(r.conclusion) === 'success');
    const groupPending = members.filter(isPendingCheckRun);
    if (groupFailed.length > 2) return { action: 'none' };
    if (groupSucceeded.length + groupPending.length < 3) return { action: 'none' };
    if (groupPending.length > 0 || groupSucceeded.length < 3) needsSiblingWait = true;
  }

  if (completed.length + pending.length < 4) return { action: 'none' };
  if (needsSiblingWait || completed.length < 4) {
    return pending.length > 0 ? { action: 'wait-siblings' } : { action: 'none' };
  }

  const shards = failedRuns.map(r => ({
    runId: extractRunId(r),
    checkId: positive(r.id) ? r.id : null,
    name: r.name,
    staleToken: `r:${r.id ?? ''}:${r.name}:${r.conclusion}:${r.completed_at ?? r.completedAt ?? r.started_at ?? r.startedAt ?? ''}`,
  }));
  return {
    action: 'rerun',
    runIds: [...failedRunIds],
    checkIds: [...new Set(shards.map(s => s.checkId).filter(positive))],
    failedNames: [...new Set(shards.map(s => s.name))],
    staleTokens: shards.map(s => s.staleToken),
    shards,
  };
}

export const FLAKE_LEDGER_MAX_ENTRIES = 500;
export const FLAKE_REPEAT_THRESHOLD = 3;
export const FLAKE_WINDOW_DAYS = 7;

const FLAKE_OUTCOMES = new Set(['flaked-then-passed', 'reproduced-red', 'base-test-red']);
const FLAKE_DAY_MS = 86_400_000;

export function normalizeFlakeEntry(entry, { now = Date.now, requireTs = false } = {}) {
  if (!object(entry)) return null;
  const outcome = typeof entry.outcome === 'string' ? entry.outcome.trim() : '';
  if (!FLAKE_OUTCOMES.has(outcome)) return null;
  const target = safe(entry.target).slice(0, 200);
  if (!target) return null;

  let ts = null;
  if (entry.ts === undefined) {
    if (requireTs) return null;
    const nowMs = typeof now === 'function' ? now() : Number(now);
    if (!Number.isFinite(nowMs)) return null;
    ts = new Date(nowMs).toISOString();
  } else if (typeof entry.ts === 'number' && Number.isFinite(entry.ts)) {
    ts = new Date(entry.ts).toISOString();
  } else if (typeof entry.ts === 'string') {
    ts = iso(entry.ts);
  }
  if (!ts) return null;

  const repoRaw = typeof entry.repo === 'string' ? entry.repo.trim() : '';
  const repo = repository(repoRaw) ? repoRaw : null;
  const issue = positive(entry.issue) ? entry.issue : null;
  const pr = positive(entry.pr) ? entry.pr : null;

  let head = null;
  if (typeof entry.head === 'string') {
    const cleanedHead = safe(entry.head).slice(0, 40);
    if (cleanedHead) {
      head = /^[a-f0-9]{7,40}$/i.test(cleanedHead) ? cleanedHead.toLowerCase() : cleanedHead;
    }
  }

  const detail = typeof entry.detail === 'string' && entry.detail.trim()
    ? safe(entry.detail).slice(0, 300)
    : null;

  return { ts, repo, issue, pr, head, target, outcome, detail };
}

export function parseFlakeLedger(raw) {
  if (typeof raw !== 'string' || !raw.trim()) return [];
  const entries = [];
  for (const rawLine of raw.split(/\r?\n/)) {
    const trimmed = rawLine.trim();
    if (!trimmed) continue;
    let parsed;
    try { parsed = JSON.parse(trimmed); }
    catch { continue; }
    const normalized = normalizeFlakeEntry(parsed, { requireTs: true });
    if (normalized) entries.push(normalized);
  }
  return entries;
}

function flakeDedupeKey(entry) {
  const repoKey = (entry.repo ?? '').toLowerCase();
  const targetKey = entry.target.toLowerCase();
  if (entry.head) {
    return `${repoKey}\0${entry.head.toLowerCase()}\0${targetKey}\0${entry.outcome}`;
  }
  return `${repoKey}\0\0${entry.issue ?? ''}\0${entry.pr ?? ''}\0${targetKey}\0${entry.outcome}`;
}

export function appendBoundedFlakeEntries(existingRaw, newEntries, { maxEntries = FLAKE_LEDGER_MAX_ENTRIES, now = Date.now } = {}) {
  const existing = parseFlakeLedger(existingRaw);
  const incomingList = Array.isArray(newEntries) ? newEntries : (newEntries ? [newEntries] : []);
  const combined = [];
  const seen = new Set();

  for (const item of existing) {
    const key = flakeDedupeKey(item);
    if (seen.has(key)) continue;
    seen.add(key);
    combined.push(item);
  }
  for (const raw of incomingList) {
    const item = normalizeFlakeEntry(raw, { now });
    if (!item) continue;
    const key = flakeDedupeKey(item);
    if (seen.has(key)) continue;
    seen.add(key);
    combined.push(item);
  }

  const cap = positive(maxEntries) ? maxEntries : FLAKE_LEDGER_MAX_ENTRIES;
  const bounded = combined.length > cap ? combined.slice(-cap) : combined;
  return bounded.length ? `${bounded.map(item => JSON.stringify(item)).join('\n')}\n` : '';
}

export function summarizeRecurringFlakes(entries, {
  nowMs = Date.now(),
  windowDays = FLAKE_WINDOW_DAYS,
  threshold = FLAKE_REPEAT_THRESHOLD,
  repo = null,
} = {}) {
  const effectiveNow = Number.isFinite(nowMs) ? nowMs : Date.now();
  const days = typeof windowDays === 'number' && Number.isFinite(windowDays) && windowDays > 0
    ? windowDays
    : FLAKE_WINDOW_DAYS;
  const minCount = positive(threshold) ? threshold : FLAKE_REPEAT_THRESHOLD;
  const cutoffMs = effectiveNow - days * FLAKE_DAY_MS;
  const repoFilterLower = typeof repo === 'string' && repo.trim() ? repo.trim().toLowerCase() : null;

  const list = typeof entries === 'string'
    ? parseFlakeLedger(entries)
    : (Array.isArray(entries) ? entries.map(e => normalizeFlakeEntry(e, { requireTs: true })).filter(Boolean) : []);

  let totalEntries = 0;
  const groups = new Map();

  for (const entry of list) {
    const tsMs = time(entry.ts);
    if (tsMs === null || tsMs < cutoffMs || tsMs > effectiveNow) continue;
    const entryRepoLower = (entry.repo ?? '').toLowerCase();
    if (repoFilterLower && entryRepoLower !== repoFilterLower) continue;
    totalEntries += 1;

    const groupKey = `${entryRepoLower}\0${entry.target.toLowerCase()}`;
    let bucket = groups.get(groupKey);
    if (!bucket) {
      bucket = {
        repo: entry.repo,
        target: entry.target,
        count: 0,
        outcomes: { 'flaked-then-passed': 0, 'reproduced-red': 0, 'base-test-red': 0 },
        lastSeenMs: tsMs,
        lastSeen: entry.ts,
        issues: new Set(),
        prs: new Set(),
      };
      groups.set(groupKey, bucket);
    }
    bucket.count += 1;
    bucket.outcomes[entry.outcome] = (bucket.outcomes[entry.outcome] ?? 0) + 1;
    if (tsMs >= bucket.lastSeenMs) {
      bucket.lastSeenMs = tsMs;
      bucket.lastSeen = entry.ts;
    }
    if (entry.issue !== null) bucket.issues.add(entry.issue);
    if (entry.pr !== null) bucket.prs.add(entry.pr);
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

export function formatRecurringFlakesLine(summary, { includeRepo = false, maxTargets = 5 } = {}) {
  const recurring = Array.isArray(summary?.recurring) ? summary.recurring : [];
  if (!recurring.length) return null;
  const limit = positive(maxTargets) ? maxTargets : 5;
  const shown = recurring.slice(0, limit).map(item => {
    const parts = [];
    for (const key of ['flaked-then-passed', 'reproduced-red', 'base-test-red']) {
      if ((item.outcomes?.[key] ?? 0) > 0) parts.push(`${item.outcomes[key]} ${key}`);
    }
    const label = includeRepo && item.repo ? `${item.repo}:${item.target}` : item.target;
    return `${label} (${item.count}x${parts.length ? `: ${parts.join(', ')}` : ''})`;
  });
  const extra = recurring.length > limit ? `; +${recurring.length - limit} more` : '';
  return `Recurring flakes (${summary.windowDays ?? FLAKE_WINDOW_DAYS}d, >=${summary.threshold ?? FLAKE_REPEAT_THRESHOLD}): ${shown.join('; ')}${extra}`;
}

export async function checkPostMergeRegressions(ports) {
  if (!ports?.root || !repository(ports.repo) || typeof ports.gh !== 'function') {
    throw Error('Post-merge regression check requires root, repo and gh ports.');
  }
  const fs = ports.fs ?? nativeFs;
  const now = (ports.now ?? Date.now)();
  const maxRequests = positive(ports.maxRequests) ? ports.maxRequests : DEFAULT_POST_MERGE_MAX_REQUESTS;
  const maxMerges = positive(ports.maxMerges) ? ports.maxMerges : DEFAULT_POST_MERGE_MAX_MERGES;
  const minRecheckMs = Number.isSafeInteger(ports.minRecheckMs) && ports.minRecheckMs >= 0
    ? ports.minRecheckMs
    : DEFAULT_POST_MERGE_RECHECK_MS;

  let history = '';
  try { history = fs.readFileSync(join(ports.root, 'history.jsonl'), 'utf8'); }
  catch (error) {
    if (error.code !== 'ENOENT') throw Error('Core merge history is unreadable.');
  }
  const mergeRows = collectCandidateRows({ history, repo: ports.repo });

  if (mergeRows.length === 0) {
    const counts = emptyPostMergeCounts(0, 0);
    return {
      state: { schema: POST_MERGE_SCHEMA, updatedAt: new Date(now).toISOString(), cursor: 0, budgetStopped: false, stopReason: null, counts, merges: {} },
      counts,
      newlyDetected: [],
      budgetStopped: false,
      stopReason: null,
      requests: 0,
    };
  }

  const stateFile = join(ports.root, 'post-merge.json');
  const saved = readSavedPostMerge(fs, stateFile);
  const entries = new Map();
  for (const row of mergeRows) {
    const prev = object(saved.merges?.[String(row.pr)]) ? saved.merges[String(row.pr)] : null;
    const mergedIssues = [...new Set([...row.issues, ...(Array.isArray(prev?.issues) ? prev.issues.filter(positive) : [])])];
    entries.set(row.pr, {
      pr: row.pr,
      issue: row.issue ?? (positive(prev?.issue) ? prev.issue : null),
      issues: mergedIssues,
      mergeCommit: sha(prev?.mergeCommit) ? prev.mergeCommit.toLowerCase() : null,
      parent: sha(prev?.parent) ? prev.parent.toLowerCase() : null,
      parentChecked: Boolean(prev?.parentChecked),
      parentObservations: Array.isArray(prev?.parentObservations) ? prev.parentObservations : null,
      title: typeof prev?.title === 'string' ? prev.title : null,
      mergedAt: iso(prev?.mergedAt) ?? null,
      status: ['pending', 'ok', 'reopened', 'reverted', 'ci', 'suspect'].includes(prev?.status) ? prev.status : 'pending',
      classification: ['pending', 'ok', 'suspect', 'proven'].includes(prev?.classification) ? prev.classification : 'pending',
      reopened: Boolean(prev?.reopened),
      reverted: Boolean(prev?.reverted),
      ciRegression: Boolean(prev?.ciRegression),
      unmerged: Boolean(prev?.unmerged && !row.claimedMerged),
      closedUnmerged: Boolean(prev?.closedUnmerged && !row.claimedMerged),
      checkedAt: iso(prev?.checkedAt) ?? null,
      signals: Array.isArray(prev?.signals) ? prev.signals : [],
      reportedKeys: Array.isArray(prev?.reportedKeys) ? [...new Set(prev.reportedKeys.filter(k => typeof k === 'string'))] : [],
    });
  }

  const activeResume = object(saved.activeSweep) && object(saved.activeSweep.streams) ? saved.activeSweep : null;
  const api = incrementalReader(ports, maxRequests, activeResume?.streams ?? {});
  const total = mergeRows.length;
  const startCursor = Number.isSafeInteger(activeResume?.cursor) && activeResume.cursor >= 0
    ? activeResume.cursor % total
    : (Number.isSafeInteger(saved.cursor) && saved.cursor >= 0 ? saved.cursor % total : 0);
  let nextCursor = startCursor;
  let budgetStopped = false;
  let stopReason = null;
  let midMergeBudgetStopped = false;
  let sharedBudgetStopped = false;
  const newlyDetected = [];
  const drafts = [];

  const checkKey = r => `check:${r.app?.id ?? 'app'}:${r.name}`;
  const mergeLatestChecks = (acc, rows) => {
    const combined = [...acc, ...rows.map(r => ({ ...compactCheck(r), anyPending: Boolean(r.anyPending || r.status !== 'completed') }))];
    const pendingKeys = new Set(combined.filter(r => r.anyPending || r.status !== 'completed').map(checkKey));
    return [...latest(combined, checkKey).values()].map(r => ({ ...r, anyPending: pendingKeys.has(checkKey(r)) }));
  };
  const mergeLatestStatuses = (acc, rows) => [...latest([...acc, ...rows.map(compactStatus)], r => `status:${r.context}`).values()];
  const readParentCi = async (prNum, parentSha, tag = 'init') => {
    let pChecks = [], pStatuses = [], checksOk = false, statusesOk = false;
    try {
      pChecks = await api.readStream(`pr:${prNum}:${tag}-pchecks:${parentSha}`, `commits/${parentSha}/check-runs?filter=all&per_page=100`, {
        field: 'check_runs', valid: validPostMergeCheck, mergePage: mergeLatestChecks,
      });
      checksOk = true;
    } catch (err) {
      if (err.budgetStop) throw err;
    }
    try {
      pStatuses = await api.readStream(`pr:${prNum}:${tag}-pstatuses:${parentSha}`, `commits/${parentSha}/statuses?per_page=100`, {
        valid: validStatus, mergePage: mergeLatestStatuses,
      });
      statusesOk = true;
    } catch (err) {
      if (err.budgetStop) throw err;
    }
    const rawParentObs = collectCiObservations(pChecks, pStatuses);
    const hasPending = [...rawParentObs.values()].some(obs => obs.context !== undefined ? obs.state === 'pending' : Boolean(obs.anyPending || obs.status !== 'completed'));
    const map = new Map(
      [...rawParentObs.entries()].map(([k, v]) => {
        const isPending = v.context !== undefined ? v.state === 'pending' : Boolean(v.anyPending || v.status !== 'completed');
        return [k, {
          state: isPending ? (v.context !== undefined ? 'pending' : null) : (v.context !== undefined ? v.state : v.conclusion),
          status: isPending ? (v.context !== undefined ? 'pending' : 'in_progress') : 'completed',
          url: link(v.html_url ?? v.target_url),
        }];
      }),
    );
    return { map, complete: checksOk && statusesOk && !hasPending, fetchOk: checksOk && statusesOk, hasPending };
  };

  const resumingSharedOnly = activeResume?.mode === 'shared' && Array.isArray(activeResume.drafts) && activeResume.drafts.length > 0;
  if (resumingSharedOnly) {
    if (Number.isSafeInteger(activeResume.nextCursor) && activeResume.nextCursor >= 0) {
      nextCursor = activeResume.nextCursor % total;
    }
    for (const savedDraft of activeResume.drafts) {
      const entry = entries.get(savedDraft.pr);
      if (!entry) continue;
      drafts.push({
        idx: Number.isSafeInteger(savedDraft.idx) ? savedDraft.idx % total : 0,
        entry,
        mergeCommit: savedDraft.mergeCommit,
        parent: savedDraft.parent,
        parentChecked: Boolean(savedDraft.parentChecked),
        mergeComplete: Boolean(savedDraft.mergeComplete),
        parentObservations: Array.isArray(savedDraft.parentObservations) ? savedDraft.parentObservations : null,
        title: savedDraft.title ?? null,
        mergedAt: savedDraft.mergedAt,
        signals: Array.isArray(savedDraft.signals) ? [...savedDraft.signals] : [],
      });
    }
  }

  for (let offset = 0; !resumingSharedOnly && offset < total; offset += 1) {
    const idx = (startCursor + offset) % total;
    const row = mergeRows[idx];
    const entry = entries.get(row.pr);
    if (entry.closedUnmerged) {
      if (drafts.length === 0) nextCursor = (idx + 1) % total;
      continue;
    }
    if (row.historyAt !== null && row.historyAt >= now) {
      if (drafts.length === 0) nextCursor = (idx + 1) % total;
      continue;
    }
    if (entry.checkedAt && time(entry.checkedAt) !== null && now - time(entry.checkedAt) < minRecheckMs) {
      if (drafts.length === 0) nextCursor = (idx + 1) % total;
      continue;
    }
    if (drafts.length >= maxMerges) {
      nextCursor = idx;
      break;
    }
    const minReadsForMerge = (entry.mergeCommit ? 2 : 4) + entry.issues.length * 2;
    if (drafts.length > 0 && (api.stopped() || api.remaining() < minReadsForMerge + 2)) {
      budgetStopped = true;
      stopReason = api.stopped() ?? `request budget exhausted (${maxRequests} reads)`;
      nextCursor = idx;
      break;
    }

    const signals = [];
    try {
      let mergeCommit = entry.mergeCommit;
      let mergedAt = entry.mergedAt;
      let title = entry.title;
      if (!mergeCommit || !mergedAt) {
        const pull = await api.get(`pulls/${entry.pr}`);
        if (!row.claimedMerged && object(pull) && pull.number === entry.pr && pull.merged_at == null) {
          entry.unmerged = true;
          entry.closedUnmerged = pull.state === 'closed';
          entry.checkedAt = new Date(now).toISOString();
          nextCursor = (idx + 1) % total;
          continue;
        }
        const resolvedMergedAt = iso(pull?.merged_at);
        if (!object(pull) || pull.number !== entry.pr || !sha(pull.merge_commit_sha) || !resolvedMergedAt || time(resolvedMergedAt) > now) {
          throw Error(`Incomplete merged PR #${entry.pr}`);
        }
        entry.unmerged = false;
        entry.closedUnmerged = false;
        mergeCommit = pull.merge_commit_sha.toLowerCase();
        mergedAt = resolvedMergedAt;
        title = typeof pull.title === 'string' ? pull.title : null;
        entry.mergeCommit = mergeCommit;
        entry.mergedAt = resolvedMergedAt;
        entry.title = title;
      }

      let parent = entry.parent;
      let parentChecked = entry.parentChecked;
      let parentObsMap = entry.parentObservations ? new Map(entry.parentObservations) : null;
      let freshParentRead = false;
      if (!parent) {
        const commitObj = await api.get(`commits/${mergeCommit}`);
        if (!object(commitObj) || commitObj.sha?.toLowerCase() !== mergeCommit || !sha(commitObj.parents?.[0]?.sha)) {
          throw Error(`Missing merge parent for PR #${entry.pr}`);
        }
        parent = commitObj.parents[0].sha.toLowerCase();
        entry.parent = parent;
      }
      if (!parentChecked) {
        const parentRes = await readParentCi(entry.pr, parent);
        const mergedParent = new Map(parentObsMap ?? []);
        for (const [k, v] of parentRes.map) mergedParent.set(k, v);
        parentObsMap = mergedParent;
        parentChecked = parentRes.complete;
        freshParentRead = parentRes.fetchOk;
        entry.parentChecked = parentChecked;
        entry.parentObservations = [...parentObsMap.entries()];
      }

      let mergeComplete = true;
      const runPart = async fn => {
        try { await fn(); }
        catch (err) {
          if (err.budgetStop) throw err;
          mergeComplete = false;
        }
      };
      const appendCiSignals = obsMap => {
        for (const [key, obs] of obsMap.entries()) {
          const stateVal = obs.state ?? obs.conclusion;
          const at = iso(obs.completed_at ?? obs.created_at ?? obs.started_at);
          if (!RED_STATES.includes(stateVal) || (at && time(at) > now)) continue;
          const before = parentObsMap?.get(key);
          const proven = before?.state === 'success' && at !== null && time(at) >= time(mergedAt);
          const sig = {
            kind: 'ci',
            level: proven ? 'proven' : 'suspect',
            issue: entry.issue,
            at,
            url: link(obs.html_url ?? obs.target_url),
            parentUrl: before?.url ?? null,
            detail: safe(`${obs.name ?? obs.context}: ${stateVal}${proven ? '; success on first parent' : '; no matching green parent'}`),
            key: `ci:${key}:${at ?? 'undated'}`,
          };
          const existingIdx = signals.findIndex(s => s.key === sig.key);
          if (existingIdx >= 0) signals[existingIdx] = sig;
          else signals.push(sig);
        }
        recordProvenSignals(entry, signals, newlyDetected);
      };
      const ensureLateParent = async obsMap => {
        const missingRedParent = [...obsMap.entries()].some(([k, obs]) => RED_STATES.includes(obs.state ?? obs.conclusion) && (!parentObsMap?.has(k) || parentObsMap.get(k)?.status !== 'completed'));
        if (!freshParentRead && missingRedParent) {
          const parentRes = await readParentCi(entry.pr, parent, 'late');
          freshParentRead = true;
          const mergedParent = new Map(parentObsMap ?? []);
          for (const [k, v] of parentRes.map) mergedParent.set(k, v);
          parentObsMap = mergedParent;
          entry.parentObservations = [...parentObsMap.entries()];
          if (parentRes.hasPending) {
            parentChecked = false;
            entry.parentChecked = false;
          }
          if (!parentRes.fetchOk) {
            mergeComplete = false;
            return parentRes.map.size > 0;
          }
          parentChecked = parentRes.complete;
          entry.parentChecked = parentChecked;
          return true;
        }
        return false;
      };

      await runPart(async () => {
        const mChecks = await api.readStream(`pr:${entry.pr}:mchecks:${mergeCommit}`, `commits/${mergeCommit}/check-runs?filter=all&per_page=100`, {
          field: 'check_runs', valid: validPostMergeCheck, mergePage: mergeLatestChecks,
        });
        const checkObs = new Map(latest(mChecks, row => `check:${row.app?.id ?? 'app'}:${row.name}`));
        appendCiSignals(checkObs);
        if (await ensureLateParent(checkObs)) appendCiSignals(checkObs);
      });

      await runPart(async () => {
        const mStatuses = await api.readStream(`pr:${entry.pr}:mstatuses:${mergeCommit}`, `commits/${mergeCommit}/statuses?per_page=100`, {
          valid: validStatus, mergePage: mergeLatestStatuses,
        });
        const statusObs = new Map(latest(mStatuses, row => `status:${row.context}`));
        appendCiSignals(statusObs);
        if (await ensureLateParent(statusObs)) appendCiSignals(statusObs);
      });

      for (const issueNum of entry.issues) {
        await runPart(async () => {
          const issueObj = await api.readOnce(
            `pr:${entry.pr}:issue:${issueNum}`,
            `issues/${issueNum}`,
            val => object(val) && val.number === issueNum && !val.pull_request && ['open', 'closed'].includes(val.state),
          );
          const events = await api.readStream(`pr:${entry.pr}:timeline:${issueNum}`, `issues/${issueNum}/timeline?per_page=100`, {
            valid: ev => typeof ev.event === 'string' && (ev.event !== 'reopened' || time(ev.created_at) !== null),
            mergePage: (acc, rows) => [
              ...acc,
              ...rows
                .filter(ev => ev.event === 'reopened' || (ev.event === 'commented' && machineMarker(ev.body)))
                .map(ev => ({
                  id: ev.id ?? null,
                  event: ev.event,
                  created_at: ev.created_at ?? null,
                  actorLogin: ev.actor?.login ?? ev.user?.login ?? null,
                  marked: machineMarker(ev.body),
                })),
            ],
          });
          let foundTimelineReopen = false;
          let sawMachineReopen = false;
          for (const ev of events) {
            if (ev.event !== 'reopened' || time(ev.created_at) === null) continue;
            if (time(ev.created_at) <= time(mergedAt) || time(ev.created_at) > now) continue;
            const marked = ev.marked || events.some(c =>
              c.event === 'commented'
              && c.marked
              && c.actorLogin
              && c.actorLogin === ev.actorLogin
              && time(c.created_at) !== null
              && Math.abs(time(c.created_at) - time(ev.created_at)) <= 5 * 60 * 1000);
            if (marked) {
              sawMachineReopen = true;
              continue;
            }
            foundTimelineReopen = true;
            const reopenAt = iso(ev.created_at);
            signals.push({
              kind: 'reopened',
              level: 'proven',
              issue: issueNum,
              at: reopenAt,
              url: `https://github.com/${ports.repo}/issues/${issueNum}#event-${ev.id ?? ''}`,
              parentUrl: null,
              detail: safe(`Issue #${issueNum} reopened after PR #${entry.pr} merged`),
              key: `reopened:${issueNum}:${reopenAt}`,
            });
          }
          if (!foundTimelineReopen && !sawMachineReopen && issueObj.state === 'open') {
            const openAt = iso(issueObj.updated_at) && time(issueObj.updated_at) >= time(mergedAt) && time(issueObj.updated_at) <= now
              ? iso(issueObj.updated_at)
              : mergedAt;
            signals.push({
              kind: 'reopened',
              level: 'proven',
              issue: issueNum,
              at: openAt,
              url: link(issueObj.html_url) ?? `https://github.com/${ports.repo}/issues/${issueNum}`,
              parentUrl: null,
              detail: safe(`Issue #${issueNum} reopened after PR #${entry.pr} merged`),
              key: `reopened:${issueNum}:open`,
            });
          }
          recordProvenSignals(entry, signals, newlyDetected);
        });
      }

      drafts.push({
        idx,
        entry,
        mergeCommit,
        parent,
        parentChecked,
        mergeComplete,
        parentObservations: parentObsMap ? [...parentObsMap.entries()] : null,
        title,
        mergedAt,
        signals,
      });
      nextCursor = (idx + 1) % total;
    } catch (error) {
      recordProvenSignals(entry, signals, newlyDetected);
      if (error.budgetStop) {
        budgetStopped = true;
        midMergeBudgetStopped = true;
        stopReason = error.budgetStop;
        nextCursor = idx;
        break;
      }
      nextCursor = (idx + 1) % total;
    }
  }

  let sharedComplete = !midMergeBudgetStopped;
  let commits = [];
  let pulls = [];
  if (drafts.length > 0 && !midMergeBudgetStopped) {
    const since = drafts.map(d => d.mergedAt).filter(Boolean).sort()[0];
    const applyCommitPage = pageRows => {
      for (const draft of drafts) {
        const later = at => time(at) !== null && time(at) > time(draft.mergedAt) && time(at) <= now;
        for (const c of pageRows) {
          if (later(c.date) && c.targets.includes(draft.mergeCommit)) {
            const sig = {
              kind: 'revert',
              level: 'proven',
              issue: draft.entry.issue,
              at: iso(c.date),
              url: c.html_url,
              parentUrl: null,
              detail: safe(`Commit ${c.sha} reverts merge ${draft.mergeCommit}`),
              key: `revert:commit:${c.sha.toLowerCase()}`,
            };
            draft.signals.push(sig);
            recordProvenSignals(draft.entry, [sig], newlyDetected);
          }
        }
      }
    };
    const applyPullPage = pageRows => {
      for (const draft of drafts) {
        const later = at => time(at) !== null && time(at) > time(draft.mergedAt) && time(at) <= now;
        for (const p of pageRows) {
          if (p.number === draft.entry.pr || !later(p.at)) continue;
          const exact = Array.isArray(p.targets) ? p.targets.includes(draft.entry.pr) : exactReference(p.body, 'Reverts', ports.repo, draft.entry.pr);
          if (exact || (draft.title && p.title === `Revert "${draft.title}"`)) {
            const sig = {
              kind: 'revert',
              level: exact && p.merged ? 'proven' : 'suspect',
              issue: draft.entry.issue,
              at: iso(p.at),
              url: p.html_url,
              parentUrl: null,
              detail: safe(`PR #${p.number} ${p.merged ? 'merged' : 'proposed'} revert of #${draft.entry.pr}`),
              key: `revert:pr:${p.number}:${p.merged ? 'merged' : 'proposed'}`,
            };
            draft.signals.push(sig);
            if (sig.level === 'proven') recordProvenSignals(draft.entry, [sig], newlyDetected);
          }
        }
      }
    };
    const runSharedPart = async fn => {
      try { await fn(); }
      catch (error) {
        sharedComplete = false;
        if (error.budgetStop) throw error;
      }
    };
    try {
      await runSharedPart(async () => {
        const compactCommitRows = rows => rows
          .filter(c => /\bThis reverts commit [a-f\d]{40}/i.test(String(c.commit?.message ?? '')))
          .map(c => ({
            sha: c.sha,
            html_url: link(c.html_url),
            date: c.commit.committer.date,
            targets: [...String(c.commit.message).matchAll(/\bThis reverts commit ([a-f\d]{40})(?:\.|,\s+reversing\s+changes made to [a-f\d]{40}\.)/gi)].map(m => m[1].toLowerCase()),
          }));
        commits = await api.readStream(`shared:commits:${since}`, `commits?since=${encodeURIComponent(since)}&per_page=100`, {
          valid: row => sha(row.sha) && typeof row.commit?.message === 'string' && time(row.commit?.committer?.date) !== null,
          mergePage: (acc, rows) => [...acc, ...compactCommitRows(rows)],
          onPage: rows => applyCommitPage(compactCommitRows(rows)),
        });
      });
      await runSharedPart(async () => {
        const compactPullRows = rows => rows
          .map(p => {
            const rawTitle = typeof p.title === 'string' ? p.title : '';
            return {
              number: p.number,
              title: rawTitle,
              targets: exactTargets(p.body, 'Reverts', ports.repo),
              merged: Boolean(p.merged_at || p.merged === true),
              at: p.merged_at ?? p.created_at ?? null,
              html_url: link(p.html_url),
            };
          })
          .filter(p => p.targets.length > 0 || /^Revert "/.test(p.title));
        pulls = await api.readStream(`shared:pulls:${since}`, 'pulls?state=all&sort=updated&direction=desc&per_page=100', {
          valid: row => positive(row.number) && (row.created_at == null || time(row.created_at) !== null) && (row.merged_at == null || time(row.merged_at) !== null),
          mergePage: (acc, rows) => [...acc, ...compactPullRows(rows)],
          stopAfterPage: rows => isDescendingPastSince(rows, since),
          onPage: rows => applyPullPage(compactPullRows(rows)),
        });
      });
    } catch (error) {
      if (error.budgetStop) {
        budgetStopped = true;
        sharedBudgetStopped = true;
        stopReason = error.budgetStop;
      }
    }
  }
  if (!budgetStopped && api.stopped()) {
    budgetStopped = true;
    stopReason = api.stopped();
  }

  const checkedAtIso = new Date(now).toISOString();
  for (const draft of drafts) {
    const { entry } = draft;
    entry.mergeCommit = draft.mergeCommit;
    entry.parent = draft.parent;
    entry.parentChecked = draft.parentChecked;
    entry.parentObservations = draft.parentObservations;
    entry.title = draft.title;
    entry.mergedAt = draft.mergedAt;

    if (sharedComplete) {
      const later = at => time(at) !== null && time(at) > time(draft.mergedAt) && time(at) <= now;
      for (const c of commits) {
        if (later(c.date) && c.targets.includes(draft.mergeCommit)) {
          draft.signals.push({
            kind: 'revert',
            level: 'proven',
            issue: entry.issue,
            at: iso(c.date),
            url: c.html_url,
            parentUrl: null,
            detail: safe(`Commit ${c.sha} reverts merge ${draft.mergeCommit}`),
            key: `revert:commit:${c.sha.toLowerCase()}`,
          });
        }
      }
      for (const p of pulls) {
        if (p.number === entry.pr || !later(p.at)) continue;
        const exact = Array.isArray(p.targets) ? p.targets.includes(entry.pr) : exactReference(p.body, 'Reverts', ports.repo, entry.pr);
        if (exact || (draft.title && p.title === `Revert "${draft.title}"`)) {
          draft.signals.push({
            kind: 'revert',
            level: exact && p.merged ? 'proven' : 'suspect',
            issue: entry.issue,
            at: iso(p.at),
            url: p.html_url,
            parentUrl: null,
            detail: safe(`PR #${p.number} ${p.merged ? 'merged' : 'proposed'} revert of #${entry.pr}`),
            key: `revert:pr:${p.number}:${p.merged ? 'merged' : 'proposed'}`,
          });
        }
      }
    }

    recordProvenSignals(entry, draft.signals, newlyDetected);
    if (!draft.mergeComplete || !sharedComplete || !draft.parentChecked) continue;

    entry.checkedAt = checkedAtIso;
    entry.signals = mergeSignalList(entry.signals.filter(s => s.level === 'proven'), draft.signals);
    entry.classification = (entry.reopened || entry.reverted || entry.ciRegression)
      ? 'proven'
      : entry.signals.length ? 'suspect' : 'ok';
    entry.status = entry.reverted ? 'reverted'
      : entry.reopened ? 'reopened'
      : entry.ciRegression ? 'ci'
      : entry.signals.length ? 'suspect' : 'ok';
  }

  const resumeCursor = drafts.length > 0 ? drafts[0].idx : nextCursor;
  const activeSweep = midMergeBudgetStopped
    ? { mode: 'merges', cursor: resumeCursor, streams: api.streams() }
    : sharedBudgetStopped
      ? {
        mode: 'shared',
        cursor: resumeCursor,
        nextCursor,
        drafts: drafts.map(({ entry: e, ...rest }) => ({ ...rest, pr: e.pr })),
        streams: api.streams(),
      }
      : null;

  const sweepOrder = new Map(mergeRows.map((r, i) => [r.pr, (i - startCursor + total) % total]));
  newlyDetected.sort((a, b) => (sweepOrder.get(a.pr) ?? 0) - (sweepOrder.get(b.pr) ?? 0));
  const counts = computePostMergeCounts(mergeRows, entries);
  const state = {
    schema: POST_MERGE_SCHEMA,
    updatedAt: checkedAtIso,
    cursor: activeSweep ? resumeCursor : nextCursor,
    activeSweep,
    budgetStopped,
    stopReason,
    counts,
    merges: Object.fromEntries([...entries.entries()].map(([pr, entry]) => [String(pr), entry])),
  };
  savePostMerge(fs, ports.root, stateFile, state);
  return { state, counts, newlyDetected, budgetStopped, stopReason, requests: api.requests() };
}

function render(scan) {
  const { ok, suspect, proven } = scan.counts;
  return [`Autopilot regressions: ${ok} ok, ${suspect} suspect, ${proven} proven (none detected does not prove health).`,
    ...scan.merges.map(m => `${m.repo}#${m.pr} ${m.classification}${m.signals.length ? ': ' + m.signals.map(s => `${s.kind}: ${s.detail}${s.url ? ` (${s.url})` : ''}`).join('; ') : ''}`),
    ...scan.errors.map(e => `Incomplete: ${e}`)].join('\n');
}

export async function runAutopilotRegressions({ cwd, env = process.env, json = false, file }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  // Native effects stop here; regressionScan receives only read ports.
  const run = ports.run ?? promisify(execFile);
  const execute = async (command, args) => {
    const result = await run(command, args, { cwd, env, encoding: 'utf8', timeout: 30000, maxBuffer: 16 * 1024 * 1024 });
    if (!result || (result.code ?? 0) !== 0) throw Error();
    return result.stdout.trim();
  };
  try {
    let root = ports.root, repo = ports.repo;
    if (!root) {
      const checkout = await execute('git', ['rev-parse', '--show-toplevel']);
      if (!checkout) throw Error();
      const id = createHash('sha256').update(checkout).digest('hex').slice(0, 20);
      const folder = ports.stateRoot ?? join(env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
      root = join(folder, `${id}-core`);
      let state;
      try { state = JSON.parse(fs.readFileSync(join(folder, `${id}.json`), 'utf8')); }
      catch (error) { if (error.code !== 'ENOENT') throw Error(); }
      repo = state?.repo ?? githubOriginRepository(await execute('git', ['remote', 'get-url', 'origin']));
    }
    const gh = ports.gh ?? (args => run('gh', args, { cwd, env, encoding: 'utf8', timeout: 30000, maxBuffer: 16 * 1024 * 1024 }));
    const scan = await regressionScan({ root, repo, fs, gh, now: ports.now });
    const message = json ? JSON.stringify(scan, null, 2) : render(scan);
    if (file !== undefined) {
      if (typeof file !== 'string' || !file.trim()) throw Error();
      fs.writeFileSync(resolve(cwd, file), message + '\n', { flag: 'wx', mode: 0o600 });
    }
    return { exitCode: scan.complete ? 0 : 1, message };
  } catch { return { exitCode: 1, message: 'Regression scan failed: could not read repository state or create the report file.' }; }
}
