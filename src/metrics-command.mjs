// Generated from prompts/cli/metrics-command.prompt.md (sha256: cd9d96c19c1dc3c9665b1dab0e27b3cbc36efcd9ffdb21794aad0bd06cb60c7d).
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

async function queryOpenIssuesBatch(repos, execFile, env) {
  if (!Array.isArray(repos) || repos.length === 0) return {};
  const aliases = [];
  const fields = [];
  for (let i = 0; i < repos.length; i++) {
    const [owner, name] = repos[i].split('/');
    const alias = `r${i}`;
    aliases.push([alias, repos[i].toLowerCase()]);
    fields.push(`${alias}: repository(owner: ${JSON.stringify(owner)}, name: ${JSON.stringify(name)}) { issues(states: OPEN) { totalCount } }`);
  }
  const query = `query { ${fields.join(' ')} }`;
  try {
    const reply = await execFile('gh', ['api', 'graphql', '-f', `query=${query}`], {
      env,
      timeout: 8000,
    });
    const parsed = JSON.parse(String(reply?.stdout ?? ''));
    if (!parsed?.data || typeof parsed.data !== 'object') return null;
    const counts = {};
    for (const [alias, lower] of aliases) {
      const total = parsed.data[alias]?.issues?.totalCount;
      counts[lower] = Number.isInteger(total) && total >= 0 ? total : null;
    }
    return counts;
  } catch {
    return null;
  }
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

  const targetRepos = validatedRepo
    ? (localState.repos.length > 0 ? localState.repos : [validatedRepo])
    : localState.repos;

  const openIssues = ports.openIssues !== undefined
    ? ports.openIssues
    : await queryOpenIssuesBatch(targetRepos, ports.execFile ?? defaultExecFile, effectiveEnv);

  const view = subcommand ?? 'overview';
  let report;
  try {
    report = calculateAutopilotMetrics({
      runs: localState.runs,
      repos: localState.repos,
      openIssues,
      view,
      byRepo: Boolean(options['--repos']),
      repoFilter: validatedRepo,
      date: options['--date'] ?? null,
      timezone: resolvedTz,
      now: new Date(nowFn()).toISOString(),
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
