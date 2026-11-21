// Generated from prompts/cli/pdd-cli.prompt.md (sha256: d3f8ff2e19dd6f8d98f9351feff0b3a04c5a6c741ca58958951984df4cb32126).
import { execFileSync } from 'node:child_process';
import { existsSync, readFileSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { CommandInputError, parseArgv } from './argument-parser.mjs';
import { renderCompletion } from './completion.mjs';
import { NAMES, PUBLIC_COMMAND_MANIFEST, PUBLIC_COMMAND_ROUTES, PUBLIC_HELP_TEXT } from './command-catalog.mjs';
import { listWorkflowAreas, formatWorkflowList } from './workflow-areas.mjs';
import { ignorePddFolder, setupProject as defaultSetupProject } from './project-setup.mjs';
import { findSkills as defaultFindSkills, setupSkills as defaultSetupSkills, syncOwnedUserSkills as defaultSyncOwnedUserSkills } from './skills-install.mjs';
import { pathDiagnostic as defaultPathDiagnostic } from './path-diagnostic.mjs';
import { checkWorkflowAgents } from './workflow-agents.mjs';
import { setupMayAsk } from './setup-interaction.mjs';
import { setupWithWorkflowAgent } from './workflow-setup.mjs';
import { causeText, runtimeOutputSlice } from './runtime-seam.mjs';

runtimeOutputSlice();

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
async function maybeCheckReleaseNotice(releaseNotice, input, ports) {
  if (releaseNotice) return releaseNotice(input, ports);
  const home = input.env?.HOME || homedir();
  const stateHome = ports?.stateHome ?? (input.env?.XDG_STATE_HOME || (home ? join(home, '.local', 'state') : null));
  if (!input.interactive && !ports?.fetchLatestRelease && !(stateHome && existsSync(join(stateHome, 'pdd', 'release-check.json')))) return null;
  const { checkReleaseNotice } = await import('./release-notice.mjs');
  return checkReleaseNotice(input, ports);
}
const defaultReadPackageVersion = ({ packageRoot }) => {
  try { const { version } = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8'));
    return typeof version === 'string' && !!version ? { ok: true, version } : { ok: false, version: '' }; }
  catch { return { ok: false, version: '' }; }
};
function findInvertedNativeOnlyStory(runtime, cwd, words, options) {
  if (['--local', '--files', '--explain-bindings', '--read', '--retry', '--request', '--screen', '--emit-v1', '--write', '--bind-criteria'].some(flag => options[flag])) return null;
  try {
    const found = runtime.findTests({ root: cwd });
    const { selected, unknown } = runtime.selectTests(found, words, options);
    if (unknown?.length || !selected?.length) return null;
    const { rows } = runtime.preflight({ root: cwd, found, selected, allowMissingInterfaces: true });
    for (const row of rows) {
      if (!row.native_only?.length) continue;
      const nativePaths = new Set(row.native_only.map(item => item.path));
      const checkableEntries = (row.steps ?? [])
        .map(step => step?.entry_path)
        .filter(entry => typeof entry === 'string' && !nativePaths.has(entry));
      if (!checkableEntries.length) continue;
      const entryPath = checkableEntries[0];
      const adapter = row.native_only[0];
      return { test: row.test, story: row.story, entry_path: entryPath, native_only_path: adapter.path, native_only_reason: adapter.reason };
    }
  } catch { /* delegate workspace/selection errors to runtime[action] */ }
  return null;
}
function resolveProjectLintRoot(cwd) {
  try {
    const gitTop = execFileSync('git', ['rev-parse', '--show-toplevel'], {
      cwd,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
      timeout: 10_000,
    }).trim();
    return gitTop ? realpathSync(gitTop) : null;
  } catch { return null; }
}
async function collectProjectLintErrors(runtime, root, words, options) {
  try {
    const { lintRepoProject } = await import('./repo-hygiene-lint.mjs');
    if (!words.length) return lintRepoProject({ root }).errors;
    const found = runtime.findTests({ root });
    const { selected, unknown } = runtime.selectTests(found, words, options);
    if (unknown?.length || !selected?.length) return [];
    const { rows } = runtime.preflight({ root, found, selected, allowMissingInterfaces: true });
    const promptSet = new Set();
    for (const row of rows) {
      for (const step of row.steps ?? []) if (typeof step?.entry_path === 'string') promptSet.add(step.entry_path);
      for (const p of row.prompts ?? []) if (typeof p === 'string') promptSet.add(p);
    }
    return lintRepoProject({ root, promptPaths: [...promptSet], tests: selected }).errors;
  } catch { return []; }
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
// The autopilot value of the root pdd.json, or undefined when there is none.
function savedAutopilot(root) {
  if (!root) return undefined;
  try { const config = JSON.parse(readFileSync(join(root, 'pdd.json'), 'utf8')); return config !== null && typeof config === 'object' ? config.autopilot : undefined; }
  catch { return undefined; }
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
  'workflow-status': plan => ['runStatus', { ref: plan.operands[0], ...Object.fromEntries(['all', 'cancelled', 'json'].filter(name => plan.options[`--${name}`]).map(name => [name, true])) }],
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
  autopilotRegressions, autopilotRegressionsPorts = {}, issueGraph, issueGraphPorts = {}, dependencyIntake, dependencyIntakePorts = {}, autopilotLauncher, autopilotLauncherPorts = {}, workflowAgents = { checkWorkflowAgents }, workflowAgentPorts = {}, setupSkills = defaultSetupSkills,
  setupProject = defaultSetupProject, setupAgentMcp, autopilot, autopilotPorts = {}, autopilotLogs, autopilotLogsPorts = {}, autopilotAlerts, autopilotAlertsPorts = {}, autopilotGithub: autopilotGithubModule, autopilotGithubPorts = {}, pathDiagnostic = defaultPathDiagnostic,
  readPackageVersion = defaultReadPackageVersion, findSkills = defaultFindSkills, syncOwnedUserSkills = defaultSyncOwnedUserSkills, interpreterVersion, interpreterVersionPorts = {}, releaseNotice, releaseNoticePorts = {}, accountsCli, accountsPorts = {}, cliUpgrade, cliUpgradePorts = {}, codexLint, codexLintPorts = {} } = {}) {
  let plan;
  try { plan = parseArgv(argv); }
  catch (error) {
    line(stderr, error instanceof CommandInputError ? error.message : 'The command could not be parsed. Run pdd --help.');
    return 2;
  }
  if (!['help', 'version', 'version-detailed', 'completion', 'workflow-list', 'project-files', 'file-owner', 'update-sync', 'mcp', 'setup', 'upgrade', 'autopilot-logs'].includes(plan.local)
    && !(plan.local === 'accounts' && plan.options['--quiet'] === true)
    && plan.options['--json'] !== true
    && !argv.includes('--json')) {
    try {
      const { updated } = syncOwnedUserSkills({
        packageRoot,
        home: env.HOME || homedir(),
        claudeConfigDir: env.CLAUDE_CONFIG_DIR,
        ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}),
        ...(env.PDD_STATE_DIR ? { stateRoot: env.PDD_STATE_DIR } : {}),
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
      for (const message of pathDiagnostic({ packageRoot, cwd, env, mode })) line(stderr, message);
    } catch { /* An optional PATH diagnostic never prevents the requested command. */ }
  }
  const code = await (async () => { switch (plan.local) {
    case 'issue-dependency-graph': {
      try { const module = issueGraph ?? await import('./issue-dependency-graph.mjs');
        const result = await module.runIssueGraph({cwd, repository:plan.options['--repo'], issue:plan.options['--issue'], open:!!plan.options['--open']}, issueGraphPorts);
        (result.exitCode ? stderr : stdout).write(result.message); return result.exitCode;
      } catch (error) { line(stderr, `Graph failed.${reason(error)}`); return 1; }
    }
    case 'dependencies-prepare': case 'dependencies-complete': {
      if (plan.local === 'dependencies-complete' && plan.options['--input'] !== '-') { line(stderr, 'Use pdd dependencies complete --input -.'); return 2; }
      if (plan.local === 'dependencies-prepare' && plan.options['--issue'] !== undefined && !/^[1-9]\d*$/.test(plan.options['--issue'])) { line(stderr, 'Use pdd dependencies prepare --issue N with a positive issue number.'); return 2; }
      try { const module = dependencyIntake ?? await import('./issue-dependencies-intake.mjs');
        let payload = stdin;
        if (plan.local === 'dependencies-complete' && typeof stdin !== 'string' && stdin?.[Symbol.asyncIterator]) {
          const chunks = []; for await (const chunk of stdin) chunks.push(Buffer.from(chunk));
          payload = Buffer.concat(chunks).toString('utf8');
        }
        const result = await module.runDependencyIntake(plan.local === 'dependencies-prepare' ? {command:'prepare',cwd,issue:plan.options['--issue']} : {command:'complete',cwd,stdin:payload},dependencyIntakePorts);
        (result.exitCode ? stderr : stdout).write(result.message); return result.exitCode;
      } catch(error) { line(stderr, `Dependency intake failed.${reason(error)}`); return 1; }
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
    case 'autopilot-doctor': case 'autopilot-audit': case 'autopilot-check-base': case 'autopilot-start': case 'autopilot-stop': case 'autopilot-status': case 'autopilot-add': case 'autopilot-release': case 'autopilot-report': case 'autopilot-intake': {
      try {
        const module = autopilotLauncher ?? await import('./autopilot-launcher.mjs');
        const result = await module.runAutopilotLauncher({ command: plan.local.slice(10), issues: [...plan.operands], runs: plan.options['--runs'], checks: plan.options['--checks'], ...(plan.options['--engine'] ? { engine: plan.options['--engine'] } : {}), ...(plan.options['--label'] ? { label: plan.options['--label'] } : {}), ...(plan.options['--mode'] ? { mode: plan.options['--mode'] } : {}), ...(plan.options['--report'] ? { report: plan.options['--report'] } : {}), ...(plan.options['--decisions'] ? { decisions: plan.options['--decisions'] } : {}), ...(plan.options['--intake'] ? { intake: plan.options['--intake'] } : {}), ...(plan.options['--share'] !== undefined ? { share: plan.options['--share'] } : {}), ...(plan.options['--agent'] !== undefined ? { agent: plan.options['--agent'] } : {}), ...(plan.options['--pool'] !== undefined ? { pool: plan.options['--pool'] } : {}), ...(plan.options['--auto-update'] ? { autoUpdate: plan.options['--auto-update'] } : {}), all: plan.options['--all'] === true, ...(plan.options['--json'] === true ? { json: true } : {}), cwd, packageRoot, env }, autopilotLauncherPorts);
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
        for (const result of findSkills({ packageRoot, cwd, home: env.HOME || homedir(), claudeConfigDir: env.CLAUDE_CONFIG_DIR, ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}) }))
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
        const context = await (gitContext ?? (await import('./workflow-runs.mjs')).gitContext)(cwd, productPorts);
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
        try { selected = await workflowAgents.checkWorkflowAgents({ cwd, env, ...(plan.options['--agent'] !== undefined ? { requested: plan.options['--agent'] } : {}) }, workflowAgentPorts); }
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
      const interactive = setupMayAsk({ yes: plan.options['--yes'], stdinIsTTY: stdin.isTTY, stdoutIsTTY: stdout.isTTY });
      return setupWithWorkflowAgent({ cwd, env }, { ...workflowAgentPorts, checkWorkflowAgents: workflowAgents.checkWorkflowAgents, stderr, setup: async () => {
      let code = 0;
      for (const result of setupSkills({ packageRoot, cwd, home: env.HOME || homedir(), claudeConfigDir: env.CLAUDE_CONFIG_DIR, ...(setupSkills === defaultSetupSkills && env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}) })) {
        if (result.updated.length) line(stdout, `Updated ${skillCount(result.updated)} in ${result.root}: ${skillNames(result.updated)}`);
        if (result.found && result.stale) {
          const version = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
          line(stdout, staleLine(result, version, cwd));
        } else if (result.found) line(stdout, `PDD skills found in ${result.found}`);
        else if (result.installed.length) line(stdout, `Installed ${skillCount(result.installed)} to ${result.root}: ${skillNames(result.installed)}`);
        if (result.error) { line(stderr, `pdd setup: the PDD skills could not be installed in ${result.root} (${result.error.code ?? result.error.message}).`); code = 1; }
      }
      try {
        const { file, changed } = setupProject({ cwd, packageRoot });
        line(stdout, changed ? `Wrote the PDD block in ${file}.` : `${file} already has this PDD block. No change.`);
      } catch (error) { line(stderr, `pdd setup: ${error.message}`); code = 1; }
      // One Git context serves the .gitignore part and the Autopilot part.
      let context = null;
      try { context = await (gitContext ?? (await import('./workflow-runs.mjs')).gitContext)(cwd); }
      catch (error) { line(stderr, `pdd setup: the Git repository could not be read.${reason(error)}`); code = 1; }
      try {
        if (context?.toplevel) {
          const { file, changed, negated } = ignorePddFolder({ root: context.toplevel });
          if (changed) line(stdout, `Added .pdd/ to ${file}. pdd test keeps its local cache there.`);
          else if (negated) line(stdout, `${file} has a "!" line for .pdd/, so pdd setup did not change the file.`);
        }
      } catch (error) { line(stderr, `pdd setup: ${error.message}`); code = 1; }
      try {
        const action = setupAgentMcp ?? (await import('./agent-mcp-setup.mjs')).setupAgentMcp;
        if (await action({ env, packageRoot }, { stdin, stdout, stderr, confirm: interactive ? confirm : undefined, interactive })) code = 1;
      } catch (error) { line(stderr, `pdd setup: MCP registration failed.${reason(error)}`); code = 1; }
      try {
        const module = autopilot ?? await import('./autopilot.mjs');
        const before = savedAutopilot(context?.toplevel);
        const result = await module.runAutopilot({ action: 'setup', interactive, inRepo: !!context?.toplevel },
          { cwd: context?.toplevel ?? cwd, stdin, stdout, ...autopilotPorts });
        if (result.message) line(result.exitCode === 0 ? stdout : stderr, result.message);
        if (result.exitCode) code = result.exitCode;
        // Setup saves a first mode only in this checkout and never writes to GitHub, where the workers read it.
        const saved = savedAutopilot(context?.toplevel)?.mode;
        if (result.exitCode === 0 && before === undefined && ['off', 'observe', 'auto'].includes(saved))
          line(stdout, `Setup saved pdd.json, the PDD block and .gitignore only in this checkout. Commit and push them so that GitHub, other machines and Autopilot jobs have them, or run pdd autopilot ${saved} to put the Autopilot mode on GitHub.`);
      } catch (error) { line(stderr, `Autopilot settings failed.${reason(error)}`); code = 1; }
      return code;
      } });
    }
    case 'upgrade': {
      try {
        const module = cliUpgrade ?? await import('./autopilot-update.mjs');
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
    case 'runtime-check':
    case 'runtime-try':
      if (plan.local === 'runtime-check' && plan.options['--issue'] !== undefined && plan.options['--codex'] !== true) {
        line(stderr, `Use --issue only with pdd ${NAMES.lint} --codex [STORY...] [--issue N|FILE] [--json] [--timeout MIN].`);
        return 2;
      }
      if (plan.local === 'runtime-check' && plan.options['--codex'] === true) {
        if (plan.options['--lint'] !== true) { line(stderr, `Use pdd ${NAMES.lint} --codex [STORY...] [--issue N|FILE] [--json] [--timeout MIN].`); return 2; }
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
      try {
        if (plan.local === 'runtime-check' && plan.options['--target'] === 'code') {
          if (Object.keys(plan.options).some(key => !['--target', '--json'].includes(key))) { line(stderr, 'pdd test --target code accepts only --json and Story selections.'); return 2; }
          const { runCompiledTest } = await import('./compiled-test.mjs');
          return await runCompiledTest({ root: cwd, words: [...plan.operands], json: !!plan.options['--json'] }, { stdout, stderr });
        }
        const runtime = await import('./runtime-seam.mjs');
        if (plan.local === 'runtime-check') {
          const inverted = findInvertedNativeOnlyStory(runtime, cwd, [...plan.operands], { ...plan.options });
          if (inverted) {
            line(stderr, `Advisory [inverted-native-only-dependency]: Story test ${inverted.test} enters checkable prompt ${inverted.entry_path}, which links kind: native-only prompt ${inverted.native_only_path} under ## Dependencies. Invert the dependency so ${inverted.native_only_path} depends on ${inverted.entry_path} and inject a <port>.<op> port.`);
          }
        }
        const action = plan.local === 'runtime-try' ? 'simulate' : plan.options['--lint'] === true ? 'lint' : 'check';
        const isLintCheckMode = action === 'lint' && !['--files', '--explain-bindings', '--read', '--retry', '--request', '--screen', '--emit-v1', '--write', '--bind-criteria'].some(flag => plan.options[flag]);
        const lintRoot = isLintCheckMode ? resolveProjectLintRoot(cwd) : null;
        let seamProjectErrors = null;
        const onProjectLintResult = lintRoot && !plan.operands.length && plan.options['--local'] === true
          ? result => {
              if (!result || !Array.isArray(result.errors)) return;
              if (!seamProjectErrors) seamProjectErrors = [];
              for (const err of result.errors) {
                if (!seamProjectErrors.includes(err)) seamProjectErrors.push(err);
              }
            }
          : undefined;
        if (lintRoot && plan.options['--json'] === true) {
          let captured = '';
          const bufferedStdout = { write: chunk => { captured += String(chunk); return true; } };
          const runtimeCode = await runtime[action]({ words: [...plan.operands], options: { ...plan.options }, cwd }, { stdout: bufferedStdout, stderr, env, ...(onProjectLintResult ? { onProjectLintResult } : {}) });
          if (runtimeCode === 0 || runtimeCode === 1) {
            const projectErrors = seamProjectErrors ?? await collectProjectLintErrors(runtime, lintRoot, [...plan.operands], { ...plan.options });
            if (projectErrors.length > 0) {
              try {
                const parsed = JSON.parse(captured.trim());
                parsed.problems = [...(Array.isArray(parsed.problems) ? parsed.problems : []), ...projectErrors];
                parsed.ok = false;
                parsed.exit_code = 1;
                stdout.write(`${JSON.stringify(parsed)}\n`);
                return 1;
              } catch { /* fall through to write raw output */ }
            }
          }
          if (captured) stdout.write(captured);
          return runtimeCode;
        }
        const runtimeCode = await runtime[action]({ words: [...plan.operands], options: { ...plan.options }, cwd }, { stdout, stderr, env, ...(onProjectLintResult ? { onProjectLintResult } : {}) });
        if (lintRoot && (runtimeCode === 0 || runtimeCode === 1)) {
          const projectErrors = seamProjectErrors ?? await collectProjectLintErrors(runtime, lintRoot, [...plan.operands], { ...plan.options });
          if (projectErrors.length > 0) {
            for (const errLine of projectErrors) line(stderr, errLine);
            return 1;
          }
        }
        return runtimeCode;
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
    case 'completion': stdout.write(renderCompletion(plan.operands[0]));return 0;
    case 'workflow-list':
      try {
        const areas = workflowAreas ?? { listWorkflowAreas, formatWorkflowList };
        const workflows = await areas.listWorkflowAreas({ packageRoot, cwd, home: env.HOME });
        if (!Array.isArray(workflows)) throw Error('Invalid workflow listing');
        line(stdout, areas.formatWorkflowList(workflows, { json: plan.options['--json'] === true }));return 0;
      } catch { line(stderr, 'The bundled workflows could not be read. Use a complete PDD package.');return 1; }
    default: line(stderr, 'Unsupported command in pdd. Run pdd --help.');return 2;
  } })();
  if (!['help', 'completion', 'version', 'version-detailed', 'mcp', 'upgrade', 'update-sync'].includes(plan.local) && !(plan.local === 'accounts' && plan.options['--quiet'] === true) && !(plan.local === 'autopilot-logs' && (plan.options['--follow'] === true || plan.options['-f'] === true)) && plan.options['--json'] !== true && (stderr?.isTTY === true || Boolean(releaseNotice))) {
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
