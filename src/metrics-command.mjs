// Generated from prompts/cli/metrics-command.prompt.md.
import { execFile as execFileCb, spawn } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { mkdirSync, writeFileSync } from 'node:fs';
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
  calculateAutopilotMetrics,
  formatMetricsText,
  isMetricsEnabled,
  renderMetricsHtml,
  validateRepoName,
} from './metrics-model.mjs';

const defaultExecFile = nativeGithubCounter(promisify(execFileCb), { purpose: 'other' });
const SUBCOMMANDS = new Set(['stages', 'skills', 'full', 'on', 'off']);
const VALUE_FLAGS = new Set(['--repo', '--date', '--timezone', '--file']);
const BOOL_FLAGS = new Set(['--repos', '--json', '--html']);
const DAY_MS = 86_400_000;
const PR_ALIAS_CHUNK = 40;

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
    for (const forbidden of ['--repos', '--date', '--timezone', '--html', '--file']) {
      if (options[forbidden] !== undefined) {
        return { error: `Option "${forbidden}" cannot be used with "pdd metrics ${subcommand}".` };
      }
    }
  } else if ((subcommand === 'stages' || subcommand === 'skills') && options['--repos']) {
    return { error: `Option "--repos" is only supported on "pdd metrics" and "pdd metrics full".` };
  }

  return { subcommand, options };
}

/** Conservative earliest UTC timestamp covering all active windows across any IANA timezone. */
function computeWindowFetchSinceIso(nowMs, dateOption) {
  if (typeof dateOption === 'string' && /^\d{4}-\d{2}-\d{2}$/.test(dateOption)) {
    const baseMs = Date.parse(`${dateOption}T00:00:00Z`);
    if (Number.isFinite(baseMs)) return new Date(baseMs - DAY_MS).toISOString();
  }
  return new Date(nowMs - 8 * DAY_MS).toISOString();
}

/** Collect distinct PR numbers per target repo from active-window runs. */
function collectActivePrsByRepo(runs, targetRepos, sinceMs) {
  const allowed = new Set(targetRepos.map(r => r.toLowerCase()));
  const byRepo = new Map(targetRepos.map(r => [r.toLowerCase(), new Set()]));
  for (const run of Array.isArray(runs) ? runs : []) {
    if (!run || typeof run.repo !== 'string') continue;
    const lower = run.repo.toLowerCase();
    if (!allowed.has(lower)) continue;
    if (!Number.isSafeInteger(run.pr) || run.pr <= 0) continue;
    const atMs = Date.parse(run.at ?? run.startedAt ?? '');
    if (run.status === 'running' || (Number.isFinite(atMs) && atMs >= sinceMs - DAY_MS)) {
      byRepo.get(lower).add(run.pr);
    }
  }
  return byRepo;
}

/**
 * Fetch live open issues, closed-in-window issues, and PR merge states for enabled repos
 * in batched GitHub GraphQL requests. Returns offline fallbacks on any error.
 */
async function queryGithubMetricsBatch({ repos, prsByRepo, sinceIso, execFile, env }) {
  if (!Array.isArray(repos) || repos.length === 0) {
    return { openIssues: {}, openIssueNumbers: [], closedIssues: [], prStates: [], online: true };
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
      .map(n => `pr_${n}: pullRequest(number: ${n}) { number state isDraft merged mergedAt closedAt }`)
      .join(' ');
    aliases.push({ alias, repo, lower, prs: firstChunk });
    fields.push(
      `${alias}: repository(owner: ${JSON.stringify(owner)}, name: ${JSON.stringify(name)}) {`
      + ` issues(states: OPEN, first: 100) { totalCount nodes { number } }`
      + ` closedIssues: issues(states: CLOSED, filterBy: { since: ${JSON.stringify(sinceIso)} }, first: 100) { nodes { number closedAt } }`
      + (prFields ? ` ${prFields}` : '')
      + ' }',
    );
  }

  const openIssues = {};
  const openIssueNumbers = [];
  const closedIssues = [];
  const prStates = [];

  const collectPrNodes = (repo, prs, repoData) => {
    if (!repoData || typeof repoData !== 'object') return;
    for (const pr of prs) {
      const node = repoData[`pr_${pr}`];
      if (!node || typeof node !== 'object') continue;
      const state = typeof node.state === 'string' ? node.state.toUpperCase() : null;
      const mergedAt = typeof node.mergedAt === 'string' && Number.isFinite(Date.parse(node.mergedAt)) ? node.mergedAt : null;
      const merged = node.merged === true || state === 'MERGED' || mergedAt !== null;
      prStates.push({ repo, pr, merged, mergedAt, state, isDraft: Boolean(node.isDraft) });
    }
  };

  try {
    const reply = await execFile('gh', ['api', 'graphql', '-f', `query=query { ${fields.join(' ')} }`], {
      env,
      timeout: 10_000,
    });
    const parsed = JSON.parse(String(reply?.stdout ?? ''));
    if (!parsed?.data || typeof parsed.data !== 'object') {
      return { openIssues: null, openIssueNumbers: [], closedIssues: [], prStates: null, online: false };
    }
    for (const { alias, repo, lower, prs } of aliases) {
      const repoData = parsed.data[alias];
      const openBlock = repoData?.issues;
      const total = openBlock?.totalCount;
      openIssues[lower] = Number.isInteger(total) && total >= 0 ? total : null;
      if (Array.isArray(openBlock?.nodes)) {
        const nums = openBlock.nodes
          .map(n => n?.number)
          .filter(n => Number.isSafeInteger(n) && n > 0);
        openIssueNumbers.push({ repo, issues: nums });
      }
      if (Array.isArray(repoData?.closedIssues?.nodes)) {
        for (const node of repoData.closedIssues.nodes) {
          if (Number.isSafeInteger(node?.number) && node.number > 0 && typeof node?.closedAt === 'string') {
            closedIssues.push({ repo, issue: node.number, closedAt: node.closedAt });
          }
        }
      }
      collectPrNodes(repo, prs, repoData);
    }

    for (const chunk of remainingPrChunks) {
      const prFields = chunk.prs
        .map(n => `pr_${n}: pullRequest(number: ${n}) { number state isDraft merged mergedAt closedAt }`)
        .join(' ');
      const extraQuery = `query { repo: repository(owner: ${JSON.stringify(chunk.owner)}, name: ${JSON.stringify(chunk.name)}) { ${prFields} } }`;
      try {
        const extraReply = await execFile('gh', ['api', 'graphql', '-f', `query=${extraQuery}`], {
          env,
          timeout: 10_000,
        });
        const extraParsed = JSON.parse(String(extraReply?.stdout ?? ''));
        collectPrNodes(chunk.repo, chunk.prs, extraParsed?.data?.repo);
      } catch {
        // Keep already-collected PR states if a supplemental chunk fails.
      }
    }

    return {
      openIssues,
      openIssueNumbers,
      closedIssues,
      prStates: prStates.length > 0 ? prStates : null,
      online: true,
    };
  } catch {
    return { openIssues: null, openIssueNumbers: [], closedIssues: [], prStates: null, online: false };
  }
}

function makeGhPort(execFile, env) {
  return async args => {
    try {
      const res = await execFile('gh', args, { env, timeout: 10_000 });
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
  coreDirs,
  fs,
  gh,
  scanner,
  nowFn,
  sinceMs,
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
    const atMs = Date.parse(run.at ?? run.startedAt ?? '');
    const state = prStateByKey.get(`${lower}#${run.pr}`);
    const mergedAtMs = Date.parse(state?.mergedAt ?? run.mergedAt ?? '');
    const inPeriod = (Number.isFinite(atMs) && atMs >= sinceMs - DAY_MS)
      || (Number.isFinite(mergedAtMs) && mergedAtMs >= sinceMs - DAY_MS);
    if (!inPeriod) continue;
    const isMerged = state
      ? state.merged === true
      : (run.status === 'merged' || run.prMerged === true || Number.isFinite(mergedAtMs));
    if (!isMerged) continue;
    const issues = [
      ...(Number.isSafeInteger(run.issue) && run.issue > 0 ? [run.issue] : []),
      ...(Array.isArray(run.issues) ? run.issues.filter(n => Number.isSafeInteger(n) && n > 0) : []),
    ];
    const prev = bucket.get(run.pr);
    if (!prev) {
      bucket.set(run.pr, { pr: run.pr, issue: issues[0] ?? null, issues: [...new Set(issues)], outcome: run.status });
    } else {
      prev.issues = [...new Set([...prev.issues, ...issues])];
      if (prev.issue === null && prev.issues.length > 0) prev.issue = prev.issues[0];
    }
  }

  const regressions = [];
  for (const repo of targetRepos) {
    const lower = repo.toLowerCase();
    const candidates = [...(candidatesByRepo.get(lower)?.values() ?? [])];
    if (candidates.length === 0) continue;
    try {
      const scan = await scanner({
        root: coreDirs?.[lower] ?? null,
        repo,
        candidates,
        prs: candidates.map(c => c.pr),
        maxRequests: 40,
        fs,
        gh,
        now: nowFn,
      });
      for (const merge of Array.isArray(scan?.merges) ? scan.merges : []) {
        const signals = Array.isArray(merge?.signals) ? merge.signals : [];
        const reopened = signals.some(s => s?.kind === 'reopened');
        const reverted = signals.some(s => s?.kind === 'revert' && s?.level === 'proven');
        const regIssues = new Set();
        for (const signal of signals) {
          if (signal?.kind === 'reference' && signal?.level === 'proven') {
            const num = extractIssueNumberFromSignal(signal);
            if (Number.isSafeInteger(num) && num > 0) regIssues.add(num);
          }
        }
        if (reopened || reverted || regIssues.size > 0) {
          const candidateIssues = candidatesByRepo.get(lower)?.get(merge.pr)?.issues ?? [];
          regressions.push({
            repo,
            pr: merge.pr,
            issue: merge.issue ?? candidateIssues[0] ?? null,
            issues: candidateIssues.length > 0 ? candidateIssues : (merge.issue ? [merge.issue] : []),
            reopened,
            reverted,
            regressionIssues: [...regIssues].sort((a, b) => a - b),
          });
        }
      }
    } catch {
      // Offline or unavailable regression scan degrades cleanly to local post-merge flags.
    }
  }
  return regressions;
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
    ?? Intl.DateTimeFormat().resolvedOptions().timeZone
    ?? 'UTC';

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

  const sinceIso = computeWindowFetchSinceIso(nowMs, options['--date'] ?? null);
  const sinceMs = Date.parse(sinceIso);
  const execFile = ports.execFile ?? defaultExecFile;

  let openIssues = ports.openIssues;
  let openIssueNumbers = ports.openIssueNumbers;
  let closedIssues = ports.closedIssues;
  let prStates = ports.prStates;
  let githubOnline = ports.openIssues === undefined;

  if (ports.openIssues === undefined) {
    const prsByRepo = collectActivePrsByRepo(localState.runs, targetRepos, sinceMs);
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
    githubOnline = fetched.online;
  }

  let regressions = ports.regressions;
  if (regressions === undefined) {
    const shouldScan = Boolean(ports.regressionScan || ports.gh || githubOnline);
    if (shouldScan && targetRepos.length > 0) {
      const gh = ports.gh ?? makeGhPort(execFile, effectiveEnv);
      regressions = await scanMergedRegressions({
        targetRepos,
        runs: localState.runs,
        prStates,
        coreDirs: localState.coreDirs,
        fs,
        gh,
        scanner: ports.regressionScan ?? regressionScan,
        nowFn,
        sinceMs,
      });
    } else {
      regressions = [];
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
      view,
      byRepo: Boolean(options['--repos']),
      repoFilter: validatedRepo,
      date: options['--date'] ?? null,
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
      (fs.mkdirSync ?? mkdirSync)(dirname(outPath), { recursive: true, mode: 0o700 });
      (fs.writeFileSync ?? writeFileSync)(outPath, renderMetricsHtml(report), 'utf8');
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
