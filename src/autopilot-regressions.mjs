// Source: prompts/cli/autopilot-regressions.prompt.md.
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
function exactReference(text, phrase, repo, pr) {
  const expression = new RegExp(`\\b${phrase}\\s*:?\\s*(https:\\/\\/github\\.com\\/[\\w.-]+\\/[\\w.-]+\\/pull\\/\\d+\\b|[\\w.-]+\\/[\\w.-]+#\\d+\\b|#\\d+\\b)`, 'gi');
  return [...String(text ?? '').matchAll(expression)].some(m => references(m[1], repo).some(r => r.repo === repo.toLowerCase() && r.number === pr));
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

// All network traffic passes through a single GET-only boundary. A failed page
// remains incomplete instead of silently looking like the end of pagination.
function reader(ports, errors) {
  const prefix = `repos/${ports.repo}/`;
  const request = async endpoint => {
    try {
      const response = await ports.gh(['api', '--include', '--method', 'GET', endpoint]);
      const parsed = githubReply(response?.stdout);
      if ((response?.code ?? 0) !== 0 || parsed?.status !== 200) throw Error();
      return { value: JSON.parse(parsed.body), next: parsed.link?.match(/<([^>]+)>;\s*rel="next"/)?.[1] };
    } catch { throw Error(`GitHub read unavailable: ${endpoint.split('?')[0]}`); }
  };
  const one = async endpoint => (await request(prefix + endpoint)).value;
  const all = async (endpoint, field, valid = () => true) => {
    let next = prefix + endpoint; const seen = new Set(), rows = [];
    try {
      while (next) {
        if (!next.startsWith(prefix) || seen.has(next)) throw Error('GitHub pagination is invalid or cyclic.');
        seen.add(next);
        const page = await request(next), values = field ? page.value?.[field] : page.value;
        if (!Array.isArray(values) || values.some(row => !object(row) || !valid(row))) throw Error(`Malformed GitHub list: ${endpoint.split('?')[0]}`);
        rows.push(...values); next = null;
        if (page.next) {
          const u = new URL(page.next);
          if (u.origin !== 'https://api.github.com' || u.username || u.password || u.hash || !u.pathname.startsWith(`/${prefix}`)) throw Error('GitHub pagination points outside this repository.');
          next = u.pathname.slice(1) + u.search;
        }
      }
    } catch (error) { error.partial = rows; throw error; }
    return rows;
  };
  const attempt = async (label, action, fallback = null, merge = null) => {
    try { return await action(); }
    catch (error) {
      const detail = safe(`Unavailable ${label}`); errors.push(detail);
      if (merge) merge.signals.push({ kind: 'unavailable', level: 'suspect', at: null, url: null, detail, parentUrl: null });
      return Array.isArray(fallback) && Array.isArray(error.partial) ? error.partial : fallback;
    }
  };
  return { one, all, attempt };
}

export async function regressionScan(ports) {
  if (!ports?.root || !repository(ports.repo) || typeof ports.gh !== 'function') throw Error('Regression scan requires root, repo and gh ports.');
  const fs = ports.fs ?? nativeFs, now = (ports.now ?? Date.now)(), errors = [], merges = [], seen = new Set();
  let history = '';
  try { history = fs.readFileSync(join(ports.root, 'history.jsonl'), 'utf8'); }
  catch (error) { if (error.code !== 'ENOENT') errors.push('Core merge history is unreadable.'); }
  for (const line of history.split('\n').filter(line => line.trim())) {
    let row; try { row = JSON.parse(line); if (!object(row)) throw Error(); }
    catch { errors.push('Invalid core history line.'); continue; }
    if (row.outcome !== 'merged') continue;
    if (row.repo !== undefined && !repository(row.repo)) { errors.push('Merged history row has no valid repository.'); continue; }
    if (row.repo && row.repo.toLowerCase() !== ports.repo.toLowerCase()) continue;
    if (!positive(row.pr)) { errors.push('Merged history row has no valid PR.'); continue; }
    if (seen.has(row.pr)) continue; seen.add(row.pr);
    merges.push({ repo: ports.repo, pr: row.pr, issue: positive(row.issue) ? row.issue : null, mergeCommit: null, parent: null, mergedAt: null, classification: 'ok', provenAt: null, signals: [] });
  }
  const api = reader(ports, errors), titles = new Map();
  for (const merge of merges) {
    const pull = await api.attempt(`PR #${merge.pr}`, async () => {
      const value = await api.one(`pulls/${merge.pr}`);
      if (!object(value) || value.number !== merge.pr || !sha(value.merge_commit_sha) || time(value.merged_at) === null || time(value.merged_at) > now) throw Error();
      return value;
    }, null, merge);
    if (!pull) continue;
    merge.mergeCommit = pull.merge_commit_sha.toLowerCase(); merge.mergedAt = iso(pull.merged_at); titles.set(merge.pr, pull.title);
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
    const pulls = await api.attempt('repository PRs', () => api.all('pulls?state=all&per_page=100', null, row => positive(row.number) && time(row.created_at) !== null && (row.merged_at == null || time(row.merged_at) !== null)), []);
    const commits = await api.attempt('default branch commits', () => api.all(`commits?since=${encodeURIComponent(since)}&per_page=100`, null, row => sha(row.sha) && typeof row.commit?.message === 'string' && time(row.commit?.committer?.date) !== null), []);
    const sharedErrors = errors.slice(before);
    for (const merge of valid) {
      const later = at => time(at) !== null && time(at) > time(merge.mergedAt) && time(at) <= now;
      const add = (kind, level, at, url, detail) => merge.signals.push({ kind, level, at: iso(at), url: link(url), detail: safe(detail), parentUrl: null });
      for (const detail of sharedErrors) add('unavailable', 'suspect', null, null, detail);
      for (const commit of commits) {
        const at = commit.commit?.committer?.date, text = String(commit.commit?.message ?? '');
        if (later(at) && [...text.matchAll(/\bThis reverts commit ([a-f\d]{40})\./gi)].some(m => m[1].toLowerCase() === merge.mergeCommit)) add('revert', 'proven', at, commit.html_url, `Commit ${commit.sha} reverts merge ${merge.mergeCommit}`);
      }
      for (const pull of pulls) {
        if (pull.number === merge.pr) continue;
        const at = pull.merged_at ?? pull.created_at;
        if (!later(at)) continue;
        const exact = exactReference(pull.body, 'Reverts', ports.repo, merge.pr);
        if (exact || titles.get(merge.pr) && pull.title === `Revert "${titles.get(merge.pr)}"`) add('revert', exact && pull.merged_at ? 'proven' : 'suspect', at, pull.html_url, `PR #${pull.number} ${pull.merged_at ? 'merged' : 'proposed'} revert of #${merge.pr}`);
      }
      const inspectIssue = issue => {
        if (!object(issue) || issue.pull_request || !positive(issue.number) || !later(issue.created_at)) return;
        const ownUrl = `https://github.com/${ports.repo.toLowerCase()}/issues/`;
        if (issue.html_url && !issue.html_url.toLowerCase().startsWith(ownUrl) || issue.repository_url && issue.repository_url.toLowerCase() !== `https://api.github.com/repos/${ports.repo.toLowerCase()}`) return;
        const text = `${issue.title ?? ''}\n${issue.body ?? ''}`;
        if (exactReference(text, 'Regressed by', ports.repo, merge.pr)) add('reference', 'proven', issue.created_at, issue.html_url, `Issue #${issue.number}: Regressed by #${merge.pr}`);
        else if (references(text, ports.repo).some(r => r.repo === ports.repo.toLowerCase() && (r.number === merge.pr || r.number === merge.issue))) add('reference', 'suspect', issue.created_at, issue.html_url, `Issue #${issue.number} links to the merged PR or issue`);
      };
      issues.forEach(inspectIssue);
      for (const number of new Set([merge.pr, merge.issue].filter(Boolean))) {
        const events = await api.attempt(`timeline #${number}`, () => api.all(`issues/${number}/timeline?per_page=100`, null, validEvent), [], merge);
        for (const event of events) {
          if (!later(event.created_at)) continue;
          if (event.event === 'reopened' && number === merge.issue) {
            const marked = machineMarker(event.body) || events.some(comment => comment.event === 'commented' && machineMarker(comment.body) && comment.user?.login && comment.user.login === event.actor?.login && Math.abs(time(comment.created_at) - time(event.created_at)) <= 5 * 60 * 1000);
            if (!marked) add('reopened', 'suspect', event.created_at, `https://github.com/${ports.repo}/issues/${number}#event-${event.id ?? ''}`, `Issue #${number} reopened after merge`);
          }
          if (event.event === 'cross-referenced') {
            const source = event.source?.issue;
            if (!source || source.pull_request || !later(source.created_at) || !source.html_url?.toLowerCase().startsWith(`https://github.com/${ports.repo.toLowerCase()}/issues/`)) continue;
            const count = merge.signals.length; inspectIssue(source);
            if (merge.signals.length === count) add('reference', 'suspect', event.created_at, source.html_url, `Issue #${source.number} cross-references #${number}`);
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
