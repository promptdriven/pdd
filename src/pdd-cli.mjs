// Prompt: prompts/cli/pdd-cli.prompt.md
import { spawnSync } from 'node:child_process';
import { accessSync, constants, existsSync, readFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, delimiter, join } from 'node:path';
import { CommandInputError, parseArgv } from './argument-parser.mjs';
import { NAMES, PUBLIC_COMMAND_MANIFEST, PUBLIC_COMMAND_ROUTES, PUBLIC_HELP_TEXT } from './command-catalog.mjs';
import { gitContext as defaultGitContext } from './shared/git-context.mjs';
import { PACKAGE_ROOT } from './shared/package-root.mjs';
import { causeText } from './shared/safe-read.mjs';
import { resolvePddStateBase } from './shared/state-dir.mjs';

async function maybeCheckReleaseNotice(releaseNotice, input, ports) {
  if (releaseNotice) return releaseNotice(input, ports);
  const resolvedHome = input.env?.HOME || homedir();
  const stateDir = ports?.stateHome
    ? join(ports.stateHome, 'pdd')
    : resolvePddStateBase(resolvedHome ? { ...input.env, HOME: resolvedHome } : input.env);
  if (!input.interactive && !ports?.fetchLatestRelease && !(stateDir && existsSync(join(stateDir, 'release-check.json')))) return null;
  const { checkReleaseNotice } = await import('./release-notice.mjs');
  return checkReleaseNotice(input, ports);
}

function hasExecutableOnPath(name, env) {
  return (env?.PATH ?? '').split(delimiter).filter(Boolean).some(dir => {
    try { accessSync(join(dir, name), constants.X_OK); return true; } catch { return false; }
  });
}

function checkPddAccountNonBlocking(env) {
  if (!hasExecutableOnPath('gh', env)) return { checked: false, connected: false };
  try {
    const res = spawnSync('gh', ['auth', 'token'], { env, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'], timeout: 1500 });
    return { checked: true, connected: !res.error && res.status === 0 && Boolean(res.stdout?.trim()) };
  } catch {
    return { checked: true, connected: false };
  }
}
const defaultReadPackageVersion = ({ packageRoot }) => {
  try { const { version } = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8'));
    return typeof version === 'string' && !!version ? { ok: true, version } : { ok: false, version: '' }; }
  catch { return { ok: false, version: '' }; }
};
function findInvertedNativeOnlyStory(runtime, cwd, words, options) {
  if (['--local', '--files', '--explain-bindings', '--read', '--retry', '--reconcile', '--request', '--screen', '--emit-v1', '--write', '--bind-criteria'].some(flag => options[flag])) return null;
  try {
    const found = runtime.findTests({ root: cwd });
    const { selected, unknown } = runtime.selectTests(found, words, options);
    if (unknown?.length || !selected?.length) return null;
    const { rows } = runtime.preflight({ root: cwd, found, selected, allowMissingInterfaces: true });
    for (const row of rows) {
      if (row.native_only?.length) {
        const nativePaths = new Set(row.native_only.map(item => item.path));
        const entryPath = (row.steps ?? []).map(s => s?.entry_path).find(e => typeof e === 'string' && !nativePaths.has(e));
        if (entryPath) return { test: row.test, story: row.story, entry_path: entryPath, native_only_path: row.native_only[0].path };
      }
      const isNative = p => p?.interface?.kind === 'native-only' || (p?.frontmatter ?? (typeof p?.text === 'string' ? runtime.parsePromptFrontmatter?.(p.text)?.frontmatter : null))?.kind === 'native-only';
      const entryPaths = [...new Set((row.steps ?? []).map(s => s?.entry_path).filter(p => typeof p === 'string' && p.endsWith('.prompt.md')))];
      for (const entryPath of entryPaths) {
        if (!found.visible?.has(entryPath)) continue;
        let entryPrompt;
        try { entryPrompt = runtime.readPrompt(cwd, found.visible, entryPath, found.workspace); } catch { continue; }
        if (isNative(entryPrompt)) continue;
        const visited = new Set([entryPath]), queue = [];
        const enqueue = (p, from) => {
          for (const c of Array.isArray(p?.interface?.calls) ? p.interface.calls : []) if (typeof c?.target === 'string' && !visited.has(c.target)) queue.push(c.target);
          if (typeof p?.text === 'string' && typeof runtime.promptMarkdownTargets === 'function')
            for (const t of runtime.promptMarkdownTargets(p.text, from, found.visible)) if (typeof t === 'string' && !visited.has(t)) queue.push(t);
        };
        enqueue(entryPrompt, entryPath);
        while (queue.length > 0 && visited.size < 64) {
          const depPath = queue.shift();
          if (visited.has(depPath) || !found.visible?.has(depPath)) continue;
          visited.add(depPath);
          let depPrompt;
          try { depPrompt = runtime.readPrompt(cwd, found.visible, depPath, found.workspace); } catch { continue; }
          if (isNative(depPrompt)) return { test: row.test, story: row.story, entry_path: entryPath, native_only_path: depPath };
          enqueue(depPrompt, depPath);
        }
      }
    }
  } catch {}
  return null;
}
const line = (stream, text) => stream.write(`${text}\n`);
// The real reason of an unexpected error, after the fixed safe line.
const reason = error => { const text = causeText(error?.message ?? error); return text ? ` Reason: ${text}` : ''; };
// Stdin as text: a string from tests, else the whole stream.
const readText = async input => {
  if (typeof input === 'string') return input;
  if (!input?.[Symbol.asyncIterator]) return '';
  const chunks = []; for await (const chunk of input) chunks.push(Buffer.from(chunk));
  return Buffer.concat(chunks).toString('utf8');
};
// Autopilot workers start from the default branch on GitHub, so a setting saved only in this checkout never reaches them.
async function autopilotGithub(module, name, input, ports, fallback = '') {
  try { return (await (module ?? await import('./autopilot-github.mjs'))[name](input, ports))?.message || ''; }
  catch { return fallback; }
}
const skillCount = folders => `${folders.length} PDD skill${folders.length === 1 ? '' : 's'}`;
const skillNames = folders => folders.map(folder => basename(folder)).join(', ');
// npx skills update changes only what npx skills add recorded (0.1.8 tester); add replaces any copy.
const staleLine = ({ found, stale, staleSkills = [] }, version, cwd) => {
  const details = staleSkills.map(({ name, version, state }) => state === 'older'
    ? `${name} is ${version ?? 'unknown'}` : `${name} differs (version ${version ?? 'unknown'})`).join(', ');
  return `PDD skills in ${found} ${stale === 'older' ? `are older than pdd ${version}` : `differ from the skills of pdd ${version}`}.${details ? ` ${details}.` : ''} For copies installed by pdd in user folders, run: pdd setup. For other copies, run: npx skills add promptdriven/pdd${[join(cwd, '.agents/skills'), join(cwd, '.codex/skills'), join(cwd, '.claude/skills')].includes(found) ? '' : ' -g'} -a codex -a claude-code -y`;
};
const profileOptions = plan => Object.fromEntries([['--model','model'],['--herdr-agent-name','herdrAgentName'],['--codex-threads','codexThreads']].filter(([flag]) => plan.options[flag] !== undefined).map(([flag,key]) => [key,plan.options[flag]]));
const RUNNER_ROUTES = {
  'workflow-suite': plan => ['runSuite', {command:plan.options['--command'], ...(plan.options['--timeout'] !== undefined ? {timeout:Number(plan.options['--timeout'])} : {})}],
  'workflow-request-uptake': plan => ['acknowledgeRequest', { requestId: plan.operands[0], summary: plan.options['--summary'] }],
  'workflow-run': plan => ['startRun', { name: plan.operands[0], issue: plan.operands[1], ...profileOptions(plan), agent: plan.options['--agent'] ?? 'codex', ...(plan.options['--base'] !== undefined ? { base: plan.options['--base'] } : {}), ...(plan.options['--adopt-corpus'] !== undefined ? { adoptCorpus: plan.options['--adopt-corpus'] } : {}), ...(plan.options['--draft'] !== undefined ? { draft: plan.options['--draft'] } : {}), ...(plan.options['--origin'] !== undefined ? {origin:plan.options['--origin']} : {}), ...(plan.options['--decision-id'] !== undefined ? {decisionId:plan.options['--decision-id']} : {}), ...(plan.options['--outcome'] !== undefined ? {outcome:plan.options['--outcome']} : {}), ...(plan.options['--through'] !== undefined ? {through:plan.options['--through']} : {}) }],
  'workflow-evidence-associate': plan => ['associateEvidenceWorkspace', { ref: plan.operands[0], workspace: plan.options['--workspace'], stage: plan.options['--stage'], ...(plan.options['--commit'] !== undefined ? { commit: plan.options['--commit'] } : {}), tests: plan.options['--test'] }],
  'workflow-evidence': plan => ['recordEvidence', { ref: plan.operands[0], summaryFile: plan.options['--summary'] }],
  'workflow-park': plan => ['parkAutomaticRun', { reason: plan.options['--reason'], ...(plan.options['--route'] === undefined ? {} : {route: plan.options['--route']}), step: plan.options['--step'], runtime: plan.options['--interpreter'] === true, ...(plan.options['--blocker'] === undefined ? {} : {blocker: plan.options['--blocker']}), ...(plan.options['--until'] === undefined ? {} : {until: plan.options['--until']}) }],
  'workflow-yield': plan => ['yieldAutomaticCapacity', { ref: plan.operands[0] }],
  'workflow-publish': plan => ['publishRun', { ref: plan.operands[0] }],
  'workflow-done': plan => ['stepDone', { step: plan.operands[0], ...(plan.options['--summary'] !== undefined ? { summary: plan.options['--summary'] } : {}), ...(plan.options['--skipped'] !== undefined ? { skipped: plan.options['--skipped'] } : {}), ...(plan.options['--no-publish'] ? { noPublish: true } : {}) }],
  'workflow-approve': plan => ['approveRun', { ref: plan.operands[0], ...(plan.options['--said'] !== undefined ? { said: plan.options['--said'] } : {}), ...(plan.options['--draft'] !== undefined ? { draft: plan.options['--draft'] } : {}), ...(plan.options['--through'] !== undefined ? { through: plan.options['--through'] } : {}) }],
  'workflow-resend': plan => ['resendChecks', { refs: plan.operands, ...(plan.options['--said'] !== undefined ? {said:plan.options['--said']} : {}) }],
  'workflow-card': plan => ['showStoryCard', { ref: plan.operands[0] }],
  'workflow-ask': plan => ['askPerson', { text: plan.operands.join(' ') }],
  'workflow-changes': plan => ['changeRun', { ref: plan.operands[0], text: plan.operands.slice(1).join(' ') }],
  'workflow-tidy': plan => ['tidyRuns', { dryRun: Boolean(plan.options['--dry-run']) }],
  'workflow-cancel': plan => ['cancelRun', { ref: plan.operands[0] }],
  'workflow-status': plan => ['runStatus', { ref: plan.operands[0], ...Object.fromEntries(['all', 'cancelled', 'json', 'local'].filter(name => plan.options[`--${name}`]).map(name => [name, true])) }],
  'workflow-open': plan => ['openRun', { ...profileOptions(plan), ref: plan.operands[0], ...(plan.operands[1] !== undefined ? { area: plan.operands[1] } : {}), ...(plan.options['--new'] ? { newSession: true } : {}) }],
};
const packageLines = packageRoot => PUBLIC_HELP_TEXT.learnLines.map(line => line.replace('PACKAGE_ROOT', () => packageRoot));
const renderTopic = (topic, packageRoot) => [PUBLIC_HELP_TEXT.heading, '', ...PUBLIC_HELP_TEXT.promptingLines, '', ...packageLines(packageRoot).slice(1)].join('\n');
export function renderHelp(prefix = [], packageRoot = PACKAGE_ROOT) {
  if (prefix.length > 0) {
    const rows = PUBLIC_COMMAND_MANIFEST.filter(({ form }) =>
      prefix.every((word, index) => form.slice(4).split(/\s+/)[index] === word));
    return [PUBLIC_HELP_TEXT.heading, '', ...rows.map(({ form, description }) => `  ${form}  ${description}`), '',
      ...PUBLIC_HELP_TEXT.closingLines].join('\n');
  }
  return [
    PUBLIC_HELP_TEXT.heading, '',
    PUBLIC_HELP_TEXT.usageLine, '',
    'Quick start:', ...PUBLIC_HELP_TEXT.quickStartLines, '',
    ...PUBLIC_HELP_TEXT.groups.flatMap((group, index) => [...(index ? [''] : []), `${group.title}:`, ...group.lines]), '',
    ...PUBLIC_HELP_TEXT.focusedHelpLines,
    ...packageLines(packageRoot), '',
    ...PUBLIC_HELP_TEXT.closingLines,
  ].join('\n');
}
export async function runPdd(argv, { stdout = process.stdout, stderr = process.stderr,
  cwd = process.cwd(), packageRoot = PACKAGE_ROOT, env = process.env, workflowRunner, workflowAreas,
  stdin = process.stdin, confirm, mcpServer, runtimeSlots, contracts, product, productPorts, gitContext, workflowProve, provePorts,
  autopilotRegressions, autopilotRegressionsPorts = {}, issueGraph, issueGraphPorts = {}, autopilotLauncher, autopilotLauncherPorts = {}, workflowAgents, workflowAgentPorts = {}, setupSkills,
  setupProject, initProject, projectStatus, localLint, localLintPorts = {}, proveRunner, proveRunnerPorts = {}, setupAgentMcp, autopilot, autopilotPorts = {}, autopilotLogs, autopilotLogsPorts = {}, autopilotAlerts, autopilotAlertsPorts = {}, autopilotGithub: autopilotGithubModule, autopilotGithubPorts = {}, pathDiagnostic,
  readPackageVersion = defaultReadPackageVersion, findSkills, syncOwnedUserSkills, interpreterVersion, interpreterVersionPorts = {}, releaseNotice, releaseNoticePorts = {}, accountsCli, accountsPorts = {}, cliUpgrade, cliUpgradePorts = {}, codexLint, codexLintPorts = {}, runtimeCheckReconcile, runtimeCheckReconcilePorts = {} } = {}) {
  let plan;
  try { plan = parseArgv(argv); }
  catch (error) {
    line(stderr, error instanceof CommandInputError ? error.message : 'The command could not be parsed. Run pdd --help.');
    return 2;
  }
  if (!['help', 'version', 'version-detailed', 'completion', 'workflow-list', 'project-files', 'file-owner', 'status', 'init', 'lint', 'prove', 'update-sync', 'mcp', 'setup', 'upgrade', 'autopilot-logs'].includes(plan.local)
    && !(plan.local === 'accounts' && plan.options['--quiet'] === true)
    && plan.options['--json'] !== true
    && !argv.includes('--json')) {
    try {
      const syncFn = syncOwnedUserSkills ?? (await import('./skills-install.mjs')).syncOwnedUserSkills;
      const { updated } = syncFn({
        packageRoot,
        home: env.HOME || homedir(),
        claudeConfigDir: env.CLAUDE_CONFIG_DIR,
        ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}),
        ...(env.PDD_STATE_DIR ? { stateRoot: env.PDD_STATE_DIR } : {}),
        env,
      });
      if (updated?.length > 0 && stderr?.isTTY === true) {
        const metadata = await readPackageVersion({ packageRoot });
        if (metadata?.ok && typeof metadata.version === 'string' && metadata.version)
          line(stderr, `Updated PDD skills to ${metadata.version} (${updated.join(', ')}).`);
      }
    } catch { /* Post-upgrade skill sync never blocks or fails a CLI command. */ }
  }
  if (['setup', 'version', 'workflow-run'].includes(plan.local)) {
    try {
      const mode = plan.local === 'workflow-run' ? 'workflow' : plan.local;
      const diagFn = pathDiagnostic ?? (await import('./path-diagnostic.mjs')).pathDiagnostic;
      for (const message of diagFn({ packageRoot, cwd, env, mode })) line(stderr, message);
    } catch { /* An optional PATH diagnostic never prevents the requested command. */ }
  }
  const code = await (async () => { switch (plan.local) {
    case 'issue-dependency-graph': {
      try { const module = issueGraph ?? await import('./issue-dependency-graph.mjs');
        const result = await module.runIssueGraph({cwd, repository:plan.options['--repo'], issue:plan.options['--issue'], open:!!plan.options['--open']}, issueGraphPorts);
        (result.exitCode ? stderr : stdout).write(result.message); return result.exitCode;
      } catch (error) { line(stderr, `Graph failed.${reason(error)}`); return 1; }
    }
    case 'autopilot-regressions': {
      try {
        const module = autopilotRegressions ?? await import('./autopilot-regressions.mjs');
        const result = await module.runAutopilotRegressions({ cwd, env, json: plan.options['--json'] === true, file: plan.options['--file'] }, autopilotRegressionsPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string' || !result.message.trim()) throw Error();
        line(result.exitCode === 0 ? stdout : stderr, result.message); return result.exitCode;
      } catch { line(stderr, 'Regression scan failed.'); return 1; }
    }
    case 'autopilot-logs': {
      const parseSelector = raw => {
        const text = String(raw ?? '').trim().replace(/\/$/, '');
        const plain = /^#?([1-9][0-9]*)$/.exec(text);
        if (plain) return { ok: true, issue: Number(plain[1]), repo: null };
        const qualified = /^([A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+)#([1-9][0-9]*)$/.exec(text);
        if (qualified) return { ok: true, issue: Number(qualified[2]), repo: qualified[1] };
        const url = /^https:\/\/github\.com\/([A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+)\/issues\/([1-9][0-9]*)$/.exec(text);
        if (url) return { ok: true, issue: Number(url[2]), repo: url[1] };
        return { ok: false, issue: null, repo: null };
      };
      const follow = Boolean(plan.options['--follow'] || plan.options['-f']);
      const json = plan.options['--json'] === true;
      if (follow && json) { line(stderr, '--json prints one snapshot and cannot be combined with --follow.'); return 2; }
      const posRaw = plan.operands[0], optRaw = plan.options['--issue'];
      const posParsed = posRaw !== undefined ? parseSelector(posRaw) : null;
      const optParsed = optRaw !== undefined ? parseSelector(optRaw) : null;
      if ((posParsed && !posParsed.ok) || (optParsed && !optParsed.ok)) {
        line(stderr, 'Use a valid issue number, #N, owner/repo#N or GitHub issue URL.'); return 2;
      }
      if (posParsed && optParsed && (posParsed.issue !== optParsed.issue
        || (posParsed.repo && optParsed.repo && posParsed.repo.toLowerCase() !== optParsed.repo.toLowerCase()))) {
        line(stderr, 'Pass the issue once: pdd autopilot logs ISSUE or pdd autopilot logs --issue ISSUE.'); return 2;
      }
      const issue = posParsed && optParsed ? (posParsed.repo ? posRaw : optRaw) : (posRaw ?? optRaw);
      if (follow && issue === undefined) {
        line(stderr, 'Select an issue to follow: pdd autopilot logs ISSUE --follow.'); return 2;
      }
      try {
        const input = {
          cwd,
          env,
          ...(issue !== undefined ? { issue } : {}),
          follow,
          ...(plan.options['--lines'] !== undefined ? { lines: Number(plan.options['--lines']) } : {}),
          json,
        };
        const ports = { stdout, stderr, ...autopilotLogsPorts };
        const result = autopilotLogs
          ? await autopilotLogs.runAutopilotLogs(input, ports)
          : await (await (autopilot ?? import('./autopilot.mjs'))).runAutopilotSubcommand('logs', input, ports);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string') throw Error('Invalid Autopilot logs reply');
        if (!result.streamed && result.message) line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch (error) { line(stderr, `Autopilot logs failed.${reason(error)}`); return 1; }
    }
    case 'autopilot-suite': {
      const command = plan.options['--command'];
      if (!command?.trim()) { line(stderr, 'Use pdd autopilot suite --command COMMAND [--timeout MIN].'); return 2; }
      try {
        const { runTestSuite } = await import('./test-suite-queue.mjs');
        const timeout = plan.options['--timeout'] !== undefined ? Number(plan.options['--timeout']) : undefined;
        const result = await runTestSuite(
          { cwd, env, command, ...(timeout !== undefined ? { timeout } : {}) },
          { say: text => line(stdout, text) },
        );
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string') throw Error('Invalid suite reply');
        if (result.message) line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch (error) { line(stderr, `Autopilot suite failed.${reason(error)}`); return 1; }
    }
    case 'autopilot-doctor': case 'autopilot-check-base': case 'autopilot-start': case 'autopilot-stop': case 'autopilot-status': case 'autopilot-add': case 'autopilot-release': case 'autopilot-report': case 'autopilot-intake': {
      try {
        const module = autopilotLauncher ?? await import('./autopilot-launcher.mjs');
        const result = await module.runAutopilotLauncher({ command: plan.local.slice(10), issues: [...plan.operands], ...(plan.options['--issues'] !== undefined ? { allowedIssues: plan.options['--issues'] } : {}), ...(plan.options['--issue'] !== undefined ? { issue: plan.options['--issue'] } : {}), runs: plan.options['--runs'], checks: plan.options['--checks'], ...(plan.options['--engine'] ? { engine: plan.options['--engine'] } : {}), ...(plan.options['--label'] ? { label: plan.options['--label'] } : {}), ...(plan.options['--mode'] ? { mode: plan.options['--mode'] } : {}), ...(plan.options['--report'] ? { report: plan.options['--report'] } : {}), ...(plan.options['--decisions'] ? { decisions: plan.options['--decisions'] } : {}), ...(plan.options['--intake'] ? { intake: plan.options['--intake'] } : {}), ...(plan.options['--share'] !== undefined ? { share: plan.options['--share'] } : {}), ...(plan.options['--agent'] !== undefined ? { agent: plan.options['--agent'] } : {}), ...(plan.options['--pool'] !== undefined ? { pool: plan.options['--pool'] } : {}), ...(plan.options['--auto-update'] ? { autoUpdate: plan.options['--auto-update'] } : {}), all: plan.options['--all'] === true, ...(plan.options['--json'] === true ? { json: true } : {}), cwd, packageRoot, env }, autopilotLauncherPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid Autopilot reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message);
        if (result.exitCode === 0 && ['autopilot-start', 'autopilot-status'].includes(plan.local) && plan.options['--all'] !== true && plan.options['--json'] !== true) {
          const warning = await autopilotGithub(autopilotGithubModule, 'checkAutopilotSettings', { cwd }, autopilotGithubPorts);
          if (warning) line(stderr, warning);
        }
        return result.exitCode;
      } catch (error) { line(stderr, `The Autopilot command failed.${reason(error)}`); return 1; }
    }
    case 'autopilot-alert': case 'autopilot-alerts': {
      const action = plan.local === 'autopilot-alert' ? 'alert' : plan.operands[0];
      if (action === 'alert' && plan.options['--input'] !== '-') { line(stderr, 'Use pdd autopilot alert --issue N --kind KIND --input - with the alert JSON on stdin.'); return 2; }
      const discordChannel = plan.options['--discord-channel'], tokenCommand = plan.options['--token-command'];
      if (action !== 'set' && (discordChannel !== undefined || tokenCommand !== undefined)) { line(stderr, 'Use --discord-channel and --token-command only with pdd autopilot alerts set.'); return 2; }
      try {
        const module = autopilotAlerts ?? await import('./autopilot-alerts.mjs');
        let text = '';
        // A token command replaces the stdin secret, so stdin is not read for it.
        if (action === 'alert' || action === 'set' && tokenCommand === undefined) {
          if (action === 'set' && stdin?.isTTY) line(stderr, `Paste the ${discordChannel === undefined ? 'webhook URL' : 'bot token'}, press Enter, then press Ctrl-D. pdd never prints it.`);
          text = await readText(stdin);
        }
        const result = await module.runAutopilotAlerts({ action, cwd, env, text, issue: plan.options['--issue'], kind: plan.options['--kind'], update: plan.options['--update'] === true,
          ...(plan.options['--destination'] === undefined ? {} : { destination: plan.options['--destination'] }), ...(discordChannel === undefined ? {} : { discordChannel }), ...(tokenCommand === undefined ? {} : { tokenCommand }) }, autopilotAlertsPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid alert reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message); return result.exitCode;
      } catch { line(stderr, 'The Autopilot alert command failed.'); return 1; }
    }
    case 'metrics': {
      const args = [...(plan.commandId === 'metrics' ? [] : [plan.commandId.split('.')[1]]), ...plan.operands];
      for (const [name, value] of Object.entries(plan.options)) { args.push(name); if (Array.isArray(value)) args.push(...value); else if (value !== true) args.push(value); }
      const { runMetrics } = await import('./metrics-command.mjs');
      return runMetrics({ argv: args, cwd, env, stdout, stderr });
    }
    case 'accounts': {
      try {
        const module = accountsCli ?? await import('./accounts-cli.mjs');
        const result = await module.runAccountsCli({ commandId: plan.commandId, operands: [...plan.operands], options: { ...plan.options }, cwd, env, stdin }, accountsPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string') throw Error('Invalid accounts reply');
        if (result.message) line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch (error) { line(stderr, `The accounts command failed.${reason(error)}`); return 1; }
    }
    case 'help': line(stdout, plan.topic ? renderTopic(plan.topic, packageRoot) : renderHelp(plan.helpPrefix, packageRoot));return 0;
    case 'version': case 'version-detailed': {
      let metadata;
      try { metadata = await readPackageVersion({ packageRoot });
        if (!metadata?.ok || typeof metadata.version !== 'string' || !metadata.version) throw Error('version');
      } catch { line(stderr, 'This PDD package has no readable version metadata.');return 1; }
      if (plan.local === 'version-detailed') {
        let result;
        try { const module = interpreterVersion ?? await import('./interpreter-version.mjs');
          result = await module.runDetailedVersion({ version: metadata.version, env }, interpreterVersionPorts);
        } catch { result = { exit_code: 0, stdout: `PDD CLI: ${metadata.version}\nPDD interpreter: unknown\n`, stderr: '' }; }
        stdout.write(result.stdout); stderr.write(result.stderr); return result.exit_code;
      }
      line(stdout, metadata.version);
      try {
        const findFn = findSkills ?? (await import('./skills-install.mjs')).findSkills;
        for (const result of findFn({ packageRoot, cwd, home: env.HOME || homedir(), claudeConfigDir: env.CLAUDE_CONFIG_DIR, ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}) }))
          if (result.found && (result.stale === 'older' || result.staleSkills?.some(({ state }) => state === 'older'))) line(stderr, staleLine(result, metadata.version, cwd));
      } catch { /* The skills check never changes --version. */ }
      try {
        const notice = await maybeCheckReleaseNotice(releaseNotice, { currentVersion: metadata.version, isVersionCommand: true, interactive: Boolean(stderr?.isTTY), env }, releaseNoticePorts);
        if (typeof notice === 'string' && notice.trim()) line(stderr, notice.trim());
      } catch { /* The release notice never changes --version. */ }
      return 0;
    }
    case 'autopilot.off': case 'autopilot.observe': case 'autopilot.auto': case 'autopilot-trust': case 'autopilot-untrust': {
      try {
        const module = autopilot ?? await import('./autopilot.mjs');
        const input = plan.local.startsWith('autopilot.')
          ? { action: 'mode', mode: plan.local.slice(10) }
          : { action: plan.local.slice(10), names: [...plan.operands] };
        const result = await module.runAutopilot(input, { cwd, stdin, stdout, ...autopilotPorts });
        line(result.exitCode === 0 ? stdout : stderr, result.message);
        if (result.exitCode === 0) {
          if (input.action === 'mode') {
            try {
              const launcher = autopilotLauncher ?? await import('./autopilot-launcher.mjs');
              if (typeof launcher.resetAutopilotCircuitBreaker === 'function') {
                await launcher.resetAutopilotCircuitBreaker({ cwd, env, mode: input.mode }, { ...autopilotPorts, ...autopilotLauncherPorts });
              }
            } catch { /* Local breaker reset never blocks pdd.json settings writes. */ }
          }
          const retry = ['pdd', 'autopilot', input.action === 'mode' ? input.mode : input.action, ...(input.names ?? [])].join(' ');
          const next = await autopilotGithub(autopilotGithubModule, 'publishAutopilotSettings', { cwd, action: input.action, mode: input.mode, names: input.names, retry },
            autopilotGithubPorts, `pdd.json on GitHub was not updated. To retry, run ${retry}.`);
          if (next) line(stdout, next);
        }
        return result.exitCode;
      } catch (error) { line(stderr, `Autopilot settings failed.${reason(error)}`); return 1; }
    }
    case 'product-status': case 'product-next': case 'product-start': {
      try {
        const context = await (gitContext ?? defaultGitContext)(cwd, productPorts);
        if (!context?.toplevel) throw Error('No product repository was found.');
        const module = product ?? await import('./product.mjs');
        if (typeof module.runProduct !== 'function') throw Error('Missing product export');
        const result = await module.runProduct({ command: plan.local.slice(8), run: plan.operands[0],
          noRun: plan.options['--no-run'] === true, agent: plan.options['--agent'] ?? 'codex',
          ...(plan.options['--through'] !== undefined ? { through: plan.options['--through'] } : {}),
          ...(plan.options['--base'] !== undefined ? { base: plan.options['--base'] } : {}),
          json: plan.options['--json'] === true, cwd: context.toplevel, packageRoot }, productPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255
          || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid product reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message.replace(/\n$/, ''));
        return result.exitCode;
      } catch (error) { line(stderr, `The product command failed.${reason(error)}`); return 1; }
    }
    case 'workflow-resend': case 'workflow-suite': case 'workflow-park': case 'workflow-yield': case 'workflow-request-uptake': case 'workflow-run': case 'workflow-done': case 'workflow-publish': case 'workflow-ask': case 'workflow-approve': case 'workflow-changes':
    case 'workflow-tidy': case 'workflow-cancel': case 'workflow-status': case 'workflow-open': case 'workflow-evidence': case 'workflow-evidence-associate': case 'workflow-card': {
      if (plan.local === 'workflow-suite' && !plan.options['--command']?.trim()) { line(stderr, 'Use pdd workflow suite --command COMMAND [--timeout MIN].'); return 2; }
      if (plan.local === 'workflow-evidence-associate' && (!plan.options['--workspace']?.trim() || !plan.options['--stage'] || !plan.options['--test']?.length)) {
        line(stderr, 'Use pdd workflow evidence-associate ISSUE --workspace PATH --stage current|pr1|before [--commit SHA] --test PATH... .'); return 2;
      }
      if (plan.local === 'workflow-evidence' && !plan.options['--summary']) { line(stderr, 'Use pdd workflow evidence ISSUE --summary FILE.'); return 2; }
      if (plan.local === 'workflow-request-uptake' && !plan.options['--summary']?.trim()) {
        const route = PUBLIC_COMMAND_ROUTES.find(route => route.id === 'workflow.request-uptake');
        line(stderr, `Use pdd ${route.prefix.join(' ')} REQUEST_ID --summary TEXT.`); return 2;
      }
      const [name, input] = RUNNER_ROUTES[plan.local](plan);
      if (plan.local === 'workflow-run') {
        let selected;
        try {
          const agentsMod = workflowAgents ?? await import('./workflow-agents.mjs');
          selected = await agentsMod.checkWorkflowAgents({ cwd, env, ...(plan.options['--agent'] !== undefined ? { requested: plan.options['--agent'] } : {}) }, workflowAgentPorts);
        }
        catch { line(stderr, 'Agent sign-in could not be checked. Run codex login status or claude auth status.'); return 1; }
        if (!selected?.ok) { line(stderr, selected?.message || 'Agent sign-in could not be checked. Run codex login status or claude auth status.'); return 1; }
        if (typeof selected.hint === 'string' && selected.hint) line(stderr, selected.hint);
        // A named agents.json entry goes to the runner by name; the runner resolves it again and saves it.
        input.agent = typeof selected.name === 'string' ? selected.name : selected.agent;
      }
      try {
        const runner = workflowRunner ?? await import('./workflow-runner.mjs');
        if (typeof runner[name] !== 'function') throw Error('Missing runner export');
        const result = await runner[name]({ ...input, cwd, packageRoot, ...(plan.local === 'workflow-suite' ? {env} : {}) }, { say: text => line(plan.local === 'workflow-suite' ? stdout : stderr, text), ...(['workflow-run', 'workflow-open', 'workflow-yield','workflow-tidy','workflow-resend'].includes(plan.local) ? { env } : {}), ...(plan.local === 'workflow-resend' ? {stdin} : {}) });
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255
          || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid runner reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch (error) {
        line(stderr, `The pdd workflow command failed before it could report. Check pdd workflow status; nothing was retried.${reason(error)}`);
        return 1;
      }
    }
    case 'workflow-cost': {
      let input;
      if (plan.options['--input'] !== undefined) {
        if (plan.options['--input'] !== '-') { line(stderr, 'Use --input - for cost JSON on stdin.'); return 2; }
        try { input = JSON.parse(await readText(stdin)); } catch { line(stderr, 'Invalid cost JSON.'); return 2; }
      }
      try {
        const runner = workflowRunner ?? await import('./workflow-runner.mjs');
        const result = await runner.runCosts({ ref: plan.operands[0], cwd, input }, { env });
        line(result.exitCode ? stderr : stdout, result.message); return result.exitCode;
      } catch { line(stderr, 'Local issue costs are unavailable.'); return 1; }
    }
    case 'workflow-prove': {
      if (!plan.options['--test'] || !plan.options['--expect']) {
        line(stderr, 'pdd workflow prove requires nonblank --test and --expect.'); return 2;
      }
      try {
        const module = workflowProve ?? await import('./workflow-prove.mjs');
        const result = await module.proveRun({ ref: plan.operands[0], test: plan.options['--test'], expect: plan.options['--expect'], cwd, ...(plan.options['--timeout'] !== undefined ? { timeoutMinutes: Number(plan.options['--timeout']) } : {}) }, provePorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid proof reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message); return result.exitCode;
      } catch (error) {
        line(stderr, `The pdd workflow command failed before it could report. Check pdd workflow status; nothing was retried.${reason(error)}`); return 1;
      }
    }
    case 'workflow-view': {
      try {
        const { viewRun } = await import('./workflow-view.mjs');
        const result = await viewRun({ ref: plan.operands[0], cwd });
        line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch (error) { line(stderr, `The saved run could not be read. Check pdd workflow status.${reason(error)}`); return 1; }
    }
    case 'mcp': {
      try {
        if (mcpServer) return await (mcpServer.mcp ?? mcpServer.runMcp).call(mcpServer, { cwd, env }, { stdin, stdout, stderr });
        const { mcp } = await import('./runtime-seam.mjs');
        return await mcp({ cwd, env }, { stdin, stdout, stderr });
      } catch (error) { line(stderr, `pdd mcp could not start.${reason(error)}`); return 1; }
    }
    case 'setup': {
      // Laptop-wide setup: non-blocking PDD account hint, global skills sync, optional Simulator MCP registration.
      // Never probes coding-agent logins, never edits repositories, and never prompts for Autopilot settings.
      const yes = plan.options['--yes'] === true;
      const interactive = Boolean(confirm) || Boolean(stdin?.isTTY && stdout?.isTTY);
      let code = 0;
      const account = checkPddAccountNonBlocking(env);
      if (account.connected) line(stdout, 'GitHub CLI (gh) sign-in detected (for promptdriven.ai).');
      else line(stdout, 'GitHub CLI (gh) is not signed in — run `gh auth login` or visit https://promptdriven.ai/login (continuing setup).');
      try {
        const skillsFn = setupSkills ?? (await import('./skills-install.mjs')).setupSkills;
        const skillOpts = {
          packageRoot,
          cwd,
          home: env.HOME || homedir(),
          claudeConfigDir: env.CLAUDE_CONFIG_DIR,
          env,
          ...(!setupSkills && env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}),
          ...(plan.options['--skills-dir'] !== undefined ? { skillsDir: plan.options['--skills-dir'] } : {}),
        };
        for (const result of skillsFn(skillOpts)) {
          if (result.pluginManaged) {
            line(stdout, `PDD skills for ${result.agent} are managed by an installed plugin (${result.found}). Skipping duplicate copy.`);
            continue;
          }
          if (result.updated.length) line(stdout, `Updated ${skillCount(result.updated)} in ${result.root}: ${skillNames(result.updated)}`);
          if (result.found && result.stale) {
            const version = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
            line(stdout, staleLine(result, version, cwd));
          } else if (result.found) line(stdout, `PDD skills found in ${result.found}`);
          else if (result.installed.length) line(stdout, `Installed ${skillCount(result.installed)} to ${result.root}: ${skillNames(result.installed)}`);
          if (result.error) { line(stderr, `pdd setup: the PDD skills could not be installed in ${result.root} (${result.error.code ?? result.error.message}).`); code = 1; }
        }
      } catch (error) { line(stderr, `pdd setup: skills sync failed.${reason(error)}`); code = 1; }
      try {
        const action = setupAgentMcp ?? (await import('./agent-mcp-setup.mjs')).setupAgentMcp;
        if (await action({ env, packageRoot }, { stdin, stdout, stderr, confirm: interactive ? confirm : undefined, interactive, yes })) code = 1;
      } catch (error) { line(stderr, `pdd setup: MCP registration failed.${reason(error)}`); code = 1; }
      line(stdout, 'Done! Use /pdd in Claude Code or $pdd in Codex. Run `pdd init` inside a repo to add the 4-line PDD block.');
      return code;
    }
    case 'init': {
      try {
        if (setupProject && !initProject) {
          const { file, changed } = setupProject({ cwd, packageRoot });
          line(stdout, changed ? `Wrote the PDD block in ${file}.` : `${file} already has this PDD block. No change.`);
          return 0;
        }
        const runInit = initProject ?? (await import('./project-setup.mjs')).initProject;
        const result = await runInit({ cwd, packageRoot });
        line(stdout, result.changed ? `Wrote the PDD block in ${result.file}.` : `${result.file} already has this PDD block. No change.`);
        if (result.language || result.testCommand) {
          const details = [result.language, result.testCommand ? `test: ${result.testCommand}` : null].filter(Boolean).join(' · ');
          line(stdout, `Detected project: ${details}.`);
        }
        line(stdout, 'Next: invoke /pdd (or $pdd) in your coding agent, or run `pdd status`.');
        return 0;
      } catch (error) {
        line(stderr, `pdd init: ${error.message}`);
        return 1;
      }
    }
    case 'status': {
      try {
        const mod = projectStatus ?? await import('./core/status.mjs');
        return await mod.runStatus({
          cwd,
          paths: [...plan.operands],
          changed: plan.options['--changed'] === true,
          json: plan.options['--json'] === true,
        }, { stdout, stderr });
      } catch (error) { line(stderr, `pdd status failed.${reason(error)}`); return 1; }
    }
    case 'upgrade': {
      try {
        const module = cliUpgrade ?? await import('./setup/cli-upgrade.mjs');
        const result = await module.runCliUpgrade({
          env,
          stdout,
          stderr,
          main: plan.options['--main'] === true,
          packageRoot,
          home: env.HOME || homedir(),
          cwd,
        }, cliUpgradePorts);
        if (typeof result === 'number') return result;
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255) throw Error('Invalid upgrade reply');
        if (typeof result.message === 'string' && result.message) line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch (error) { line(stderr, `pdd upgrade failed.${reason(error)}`); return 1; }
    }
    case 'runtime-jobs':
      try {
        if (runtimeSlots) return await (runtimeSlots.jobs ?? runtimeSlots.runJobs).call(runtimeSlots, { env }, { stdout, stderr });
        const { jobs } = await import('./runtime-seam.mjs');
        return await jobs({ env }, { stdout, stderr });
      }
      catch (error) { line(stderr, `Local interpreter jobs could not be read.${reason(error)}`); return 5; }
    case 'contracts': case 'contracts-sync':
      try {
        const input = { words: plan.local === 'contracts-sync' ? ['sync'] : [], options: { ...plan.options }, cwd };
        const ports = { env, stdout, stderr };
        if (contracts) return await (contracts.contracts ?? contracts.runContracts).call(contracts, input, ports);
        const { contracts: run } = await import('./runtime-seam.mjs');
        return await run(input, ports);
      } catch (error) { line(stderr, `Local contracts could not be read.${reason(error)}`); return 5; }
    case 'lint': {
      if (plan.options['--issue'] !== undefined && plan.options['--codex'] !== true) {
        line(stderr, `Use --issue only with pdd ${NAMES.lint} --codex [STORY...] [--issue N|FILE] [--json] [--timeout MIN].`);
        return 2;
      }
      if (plan.options['--codex'] === true) {
        if (Object.keys(plan.options).some(key => !['--lint', '--codex', '--issue', '--json', '--timeout'].includes(key))) {
          line(stderr, `pdd ${NAMES.lint} --codex accepts only Story or prompt paths, --json, and --timeout MIN, plus optional --issue N|FILE.`); return 2;
        }
        try {
          const module = codexLint ?? await import('./codex-lint.mjs');
          return await module.runCodexLint({
            cwd,
            words: [...plan.operands],
            ...(plan.options['--issue'] !== undefined ? { issue: plan.options['--issue'] } : {}),
            ...(plan.options['--timeout'] !== undefined ? { timeoutMinutes: Number(plan.options['--timeout']) } : {}),
            json: plan.options['--json'] === true,
            env,
          }, { stdout, stderr, ...codexLintPorts });
        } catch (error) {
          line(stderr, `Codex lint failed before completing.${reason(error)}`);
          return 1;
        }
      }
      const needsRemoteOrCompiler = Boolean(
        plan.options['--remote'] === true
        || plan.options['--emit-v1'] === true
        || plan.options['--write'] === true
        || plan.options['--bind-criteria'] === true,
      );
      if (needsRemoteOrCompiler) {
        if (plan.options['--remote'] === true && plan.options['--local'] === true) {
          line(stderr, `Use either --local or --remote with pdd ${NAMES.lint}, not both.`);
          return 2;
        }
        try {
          const runtime = await import('./runtime-seam.mjs');
          const { '--remote': _remote, '--diff': _diff, '--base': _base, ...forwardOptions } = plan.options;
          const opts = { ...forwardOptions, '--lint': true };
          const inverted = findInvertedNativeOnlyStory(runtime, cwd, [...plan.operands], opts);
          if (inverted) line(stderr, `Advisory [inverted-native-only-dependency]: Story test ${inverted.test} enters checkable prompt ${inverted.entry_path}, which links kind: native-only prompt ${inverted.native_only_path} under ## Dependencies. Invert the dependency so ${inverted.native_only_path} depends on ${inverted.entry_path} and inject a <port>.<op> port.`);
          return await runtime.lint({ words: [...plan.operands], options: opts, cwd }, { stdout, stderr, env });
        } catch (error) {
          line(stderr, `pdd stopped with an internal error. If it sent checks, read them with pdd test --read. Do not send them again.${reason(error)}`);
          return 3;
        }
      }
      try {
        const mod = localLint ?? await import('./core/lint/run-local-lint.mjs');
        const diffOpt = plan.options['--diff'];
        return await mod.runLocalLint({
          cwd,
          words: [...plan.operands],
          json: plan.options['--json'] === true,
          ...(diffOpt !== undefined ? { diff: diffOpt } : {}),
          ...(plan.options['--base'] !== undefined ? { baseRef: plan.options['--base'] } : {}),
          env,
        }, { stdout, stderr, ...localLintPorts });
      } catch (error) {
        line(stderr, `Local lint failed.${reason(error)}`);
        return 2;
      }
    }
    case 'prove': {
      try {
        const mod = proveRunner ?? await import('./core/prove.mjs');
        const res = await mod.runProve({
          cwd,
          ...(plan.options['--base'] !== undefined ? { base: plan.options['--base'] } : {}),
          ...(plan.options['--test'] !== undefined ? { test: plan.options['--test'] } : {}),
          ...(plan.options['--expect'] !== undefined ? { expect: plan.options['--expect'] } : {}),
          ...(plan.options['--overlay'] !== undefined ? { overlay: plan.options['--overlay'] } : {}),
          ...(plan.options['--setup'] !== undefined ? { setup: plan.options['--setup'] } : {}),
          ...(plan.options['--timeout'] !== undefined ? { timeoutMinutes: Number(plan.options['--timeout']) } : {}),
          json: plan.options['--json'] === true,
          env,
        }, { stdout, stderr, ...proveRunnerPorts });
        return typeof res === 'number' ? res : (Number.isInteger(res?.exitCode) ? res.exitCode : 1);
      } catch (error) {
        line(stderr, `pdd prove failed.${reason(error)}`);
        return 2;
      }
    }
    case 'runtime-check':
    case 'runtime-try':
      if (plan.local === 'runtime-check' && plan.options['--reconcile'] !== undefined) {
        if (plan.operands.length > 0 || Object.keys(plan.options).some(key => !['--reconcile', '--json'].includes(key))) {
          line(stderr, `Use pdd ${NAMES.test} --reconcile REQUEST_ID [--json] without other options or Stories.`);
          return 2;
        }
        try {
          const runtime = await import('./runtime-seam.mjs');
          return await runtime.runCheck(
            { words: [...plan.operands], options: { ...plan.options }, cwd },
            {
              env,
              stdout,
              stderr,
              ...runtimeCheckReconcilePorts,
              ...(runtimeCheckReconcile ? { reconcileCheckReceipt: runtimeCheckReconcile } : {}),
            },
          );
        } catch (error) {
          if (error?.code === 'invalid-request-id' || error?.exitCode === 2) {
            line(stderr, causeText(error.message) || 'Invalid CHECK request UUID.');
            return 2;
          }
          if (error?.code === 'reconciliation-unsupported' || error?.exitCode === 5) {
            line(stderr, causeText(error.message) || 'CHECK receipt reconciliation is unavailable.');
            return 5;
          }
          line(stderr, `CHECK receipt reconciliation failed.${reason(error)}`);
          return 3;
        }
      }
      try {
        if (plan.local === 'runtime-check' && plan.options['--target'] === 'code') {
          if (Object.keys(plan.options).some(key => !['--target', '--json'].includes(key))) { line(stderr, 'pdd test --target code accepts only --json and Story selections.'); return 2; }
          const { runCompiledTest } = await import('./compiled-test.mjs');
          return await runCompiledTest({ root: cwd, words: [...plan.operands], json: !!plan.options['--json'] }, { stdout, stderr });
        }
        const runtime = await import('./runtime-seam.mjs');
        if (plan.local === 'runtime-check') {
          const inverted = findInvertedNativeOnlyStory(runtime, cwd, [...plan.operands], { ...plan.options });
          if (inverted) line(stderr, `Advisory [inverted-native-only-dependency]: Story test ${inverted.test} enters checkable prompt ${inverted.entry_path}, which links kind: native-only prompt ${inverted.native_only_path} under ## Dependencies. Invert the dependency so ${inverted.native_only_path} depends on ${inverted.entry_path} and inject a <port>.<op> port.`);
        }
        const action = plan.local === 'runtime-try' ? 'simulate' : 'check';
        return await runtime[action]({ words: [...plan.operands], options: { ...plan.options }, cwd }, { stdout, stderr, env });
      } catch (error) {
        line(stderr, `pdd stopped with an internal error. If it sent checks, read them with pdd test --read. Do not send them again.${reason(error)}`);
        return 3;
      }
    case 'project-files': {
      const { runProjectFiles } = await import('./project-files.mjs');
      return runProjectFiles({ cwd, json: !!plan.options['--json'] }, { stdout, stderr });
    }
    case 'file-owner': {
      const { runOwner } = await import('./file-owner.mjs');
      return runOwner({ cwd, paths: [...plan.operands], json: !!plan.options['--json'] }, { stdout, stderr });
    }
    case 'update-sync': {
      try {
        const { runUpdate } = await import('./update-sync.mjs');
        return runUpdate({
          cwd,
          files: [...plan.operands],
          ...(plan.options['--from'] !== undefined ? { from: plan.options['--from'] } : {}),
          check: plan.options['--check'] === true,
          write: plan.options['--write'] === true,
          json: plan.options['--json'] === true,
        }, { stdout, stderr });
      } catch (error) { line(stderr, `pdd update failed.${reason(error)}`); return 1; }
    }
    case 'prompt-approve': {
      const { runApprove } = await import('./prompt-approve.mjs');
      return runApprove({ words: [...plan.operands], cwd, said: plan.options['--said'] }, { stdout, stderr, stdin, env });
    }
    case 'completion': {
      const { renderCompletion } = await import('./completion.mjs');
      stdout.write(renderCompletion(plan.operands[0]));
      return 0;
    }
    case 'workflow-list':
      try {
        const areas = workflowAreas ?? await import('./workflow-areas.mjs');
        const workflows = await areas.listWorkflowAreas({ packageRoot, cwd, home: env.HOME });
        if (!Array.isArray(workflows)) throw Error('Invalid workflow listing');
        line(stdout, areas.formatWorkflowList(workflows, { json: plan.options['--json'] === true }));return 0;
      } catch { line(stderr, 'The bundled workflows could not be read. Use a complete PDD package.');return 1; }
    default: line(stderr, 'Unsupported command in pdd. Run pdd --help.');return 2;
  } })();
  if (!['help', 'completion', 'version', 'version-detailed', 'mcp', 'upgrade', 'update-sync', 'project-files', 'setup', 'init', 'status', 'lint', 'prove'].includes(plan.local) && !(plan.local === 'accounts' && plan.options['--quiet'] === true) && !(plan.local === 'autopilot-logs' && (plan.options['--follow'] === true || plan.options['-f'] === true)) && plan.options['--json'] !== true && (stderr?.isTTY === true || Boolean(releaseNotice))) {
    try {
      const metadata = await readPackageVersion({ packageRoot });
      if (metadata?.ok && typeof metadata.version === 'string' && metadata.version) {
        const notice = await maybeCheckReleaseNotice(releaseNotice, { currentVersion: metadata.version, isVersionCommand: false, interactive: Boolean(stderr?.isTTY), env }, releaseNoticePorts);
        if (typeof notice === 'string' && notice.trim()) line(stderr, notice.trim());
      }
    } catch { /* An optional release notice never changes command output or exit status. */ }
  }
  return code;
}
