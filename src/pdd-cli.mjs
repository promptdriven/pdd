// Generated from prompts/cli/pdd-cli.prompt.md (sha256: 7eaa21ab3eb4e350af9e644ddbe70e838d6424d95ae380d4ae6e136b83770ac0).
import { readFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { CommandInputError, parseArgv } from './argument-parser.mjs';
import { renderCompletion } from './completion.mjs';
import { NAMES, PUBLIC_COMMAND_MANIFEST, PUBLIC_COMMAND_ROUTES, PUBLIC_HELP_TEXT } from './command-catalog.mjs';
import { listWorkflowAreas, formatWorkflowList } from './workflow-areas.mjs';
import { ignorePddFolder, setupProject as defaultSetupProject } from './project-setup.mjs';
import { findSkills, setupSkills as defaultSetupSkills } from './skills-install.mjs';
import { pathDiagnostic as defaultPathDiagnostic } from './path-diagnostic.mjs';
import { checkWorkflowAgents } from './workflow-agents.mjs';
import { setupWithWorkflowAgent } from './workflow-setup.mjs';
import { causeText } from './runtime-output.mjs';

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
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
const staleLine = ({ found, stale }, version, cwd) => `PDD skills in ${found} ${stale === 'older' ? `are older than pdd ${version}` : `differ from the skills of pdd ${version}`}. To update them, run: npx skills add promptdriven/pdd${[join(cwd, '.agents/skills'), join(cwd, '.claude/skills')].includes(found) ? '' : ' -g'} -a codex -a claude-code -y`;
const RUNNER_ROUTES = {
  'workflow-suite': plan => ['runSuite', {command:plan.options['--command'], ...(plan.options['--timeout'] ? {timeout:Number(plan.options['--timeout'])} : {})}],
  'workflow-request-uptake': plan => ['acknowledgeRequest', { requestId: plan.operands[0], summary: plan.options['--summary'] }],
  'workflow-run': plan => ['startRun', { name: plan.operands[0], issue: plan.operands[1], agent: plan.options['--agent'] ?? 'codex', ...(plan.options['--base'] !== undefined ? { base: plan.options['--base'] } : {}), ...(plan.options['--adopt-corpus'] !== undefined ? { adoptCorpus: plan.options['--adopt-corpus'] } : {}), ...(plan.options['--draft'] !== undefined ? { draft: plan.options['--draft'] } : {}), ...(plan.options['--origin'] !== undefined ? {origin:plan.options['--origin']} : {}), ...(plan.options['--decision-id'] !== undefined ? {decisionId:plan.options['--decision-id']} : {}), ...(plan.options['--outcome'] !== undefined ? {outcome:plan.options['--outcome']} : {}) }],
  'workflow-evidence-associate': plan => ['associateEvidenceWorkspace', { ref: plan.operands[0], workspace: plan.options['--workspace'], stage: plan.options['--stage'], tests: plan.options['--test'] }],
  'workflow-evidence': plan => ['recordEvidence', { ref: plan.operands[0], summaryFile: plan.options['--summary'] }],
  'workflow-park': plan => ['parkAutomaticRun', { reason: plan.options['--reason'], runtime: plan.options['--interpreter'] === true }],
  'workflow-yield': plan => ['yieldAutomaticCapacity', { ref: plan.operands[0] }],
  'workflow-done': plan => ['stepDone', { step: plan.operands[0], ...(plan.options['--summary'] !== undefined ? { summary: plan.options['--summary'] } : {}), ...(plan.options['--skipped'] !== undefined ? { skipped: plan.options['--skipped'] } : {}) }],
  'workflow-approve': plan => ['approveRun', { ref: plan.operands[0], ...(plan.options['--said'] !== undefined ? { said: plan.options['--said'] } : {}), ...(plan.options['--draft'] !== undefined ? { draft: plan.options['--draft'] } : {}) }],
  'workflow-ask': plan => ['askPerson', { text: plan.operands.join(' ') }],
  'workflow-changes': plan => ['changeRun', { ref: plan.operands[0], text: plan.operands.slice(1).join(' ') }],
  'workflow-cancel': plan => ['cancelRun', { ref: plan.operands[0] }],
  'workflow-status': plan => ['runStatus', { ref: plan.operands[0], ...Object.fromEntries(['all', 'cancelled', 'json'].filter(name => plan.options[`--${name}`]).map(name => [name, true])) }],
  'workflow-open': plan => ['openRun', { ref: plan.operands[0], ...(plan.operands[1] !== undefined ? { area: plan.operands[1] } : {}), ...(plan.options['--new'] ? { newSession: true } : {}) }],
};
const packageLines = packageRoot => PUBLIC_HELP_TEXT.learnLines.map(line => line.replace('PACKAGE_ROOT', () => packageRoot));
const renderTopic = (topic, packageRoot) => [PUBLIC_HELP_TEXT.heading, '', ...PUBLIC_HELP_TEXT.promptingLines, '', ...packageLines(packageRoot).slice(1)].join('\n');
export function renderHelp(prefix = [], packageRoot = PACKAGE_ROOT) {
  const rows = PUBLIC_COMMAND_MANIFEST.filter(({ form }) => !prefix.length
    || prefix.every((word, index) => form.slice(4).split(/\s+/)[index] === word));
  return [PUBLIC_HELP_TEXT.heading, '', ...rows.map(({ form, description }) => `  ${form}  ${description}`), '',
    ...(prefix.length ? [] : [...packageLines(packageRoot), '']), ...PUBLIC_HELP_TEXT.closingLines].join('\n');
}
export async function runPdd(argv, { stdout = process.stdout, stderr = process.stderr,
  cwd = process.cwd(), packageRoot = PACKAGE_ROOT, env = process.env, workflowRunner, workflowAreas,
  stdin = process.stdin, confirm, mcpServer, runtimeSlots, contracts, product, productPorts, gitContext, workflowProve, provePorts,
  issueGraph, issueGraphPorts = {}, dependencyIntake, dependencyIntakePorts = {}, autopilotLauncher, autopilotLauncherPorts = {}, workflowAgents = { checkWorkflowAgents }, workflowAgentPorts = {}, setupSkills = defaultSetupSkills,
  setupProject = defaultSetupProject, setupAgentMcp, autopilot, autopilotPorts = {}, autopilotAlerts, autopilotAlertsPorts = {}, autopilotGithub: autopilotGithubModule, autopilotGithubPorts = {}, pathDiagnostic = defaultPathDiagnostic } = {}) {
  let plan;
  try { plan = parseArgv(argv); }
  catch (error) {
    line(stderr, error instanceof CommandInputError ? error.message : 'The command could not be parsed. Run pdd --help.');
    return 2;
  }
  if (['setup', 'version', 'workflow-run'].includes(plan.local)) {
    try {
      const mode = plan.local === 'workflow-run' ? 'workflow' : plan.local;
      for (const message of pathDiagnostic({ packageRoot, cwd, env, mode })) line(stderr, message);
    } catch { /* An optional PATH diagnostic never prevents the requested command. */ }
  }
  switch (plan.local) {
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
        if (plan.local === 'dependencies-complete' && result.exitCode === 0) {
          let state = 'unknown';
          try { const launcher = autopilotLauncher ?? await import('./autopilot-launcher.mjs');
            const wake = await launcher.requestAutopilotCompletion({cwd, env}, autopilotLauncherPorts);
            if (['reconciled', 'inactive', 'busy', 'unknown'].includes(wake?.state)) state = wake.state;
          } catch { /* Completion intake remains accepted even if the wake fails. */ }
          if (state === 'busy' || state === 'unknown') line(stderr, 'Autopilot reconciliation was not confirmed.');
        }
        (result.exitCode ? stderr : stdout).write(result.message); return result.exitCode;
      } catch(error) { line(stderr, `Dependency intake failed.${reason(error)}`); return 1; }
    }
    case 'autopilot-start': case 'autopilot-stop': case 'autopilot-status': case 'autopilot-add': {
      try {
        const module = autopilotLauncher ?? await import('./autopilot-launcher.mjs');
        const result = await module.runAutopilotLauncher({ command: plan.local.slice(10), issues: [...plan.operands], runs: plan.options['--runs'], resumeCustody: plan.options['--resume-custody'], all: plan.options['--all'] === true, cwd, packageRoot, env }, autopilotLauncherPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid Autopilot reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message);
        if (result.exitCode === 0 && ['autopilot-start', 'autopilot-status'].includes(plan.local) && plan.options['--all'] !== true) {
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
          ...(discordChannel === undefined ? {} : { discordChannel }), ...(tokenCommand === undefined ? {} : { tokenCommand }) }, autopilotAlertsPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255 || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid alert reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message); return result.exitCode;
      } catch { line(stderr, 'The Autopilot alert command failed.'); return 1; }
    }
    case 'metrics': {
      const args = [...(plan.commandId === 'metrics' ? [] : [plan.commandId.split('.')[1]]), ...plan.operands];
      for (const [name, value] of Object.entries(plan.options)) { args.push(name); if (Array.isArray(value)) args.push(...value); else if (value !== true) args.push(value); }
      const { runMetrics } = await import('./metrics-command.mjs');
      return runMetrics({ argv: args, cwd, stdout, stderr });
    }
    case 'help': line(stdout, plan.topic ? renderTopic(plan.topic, packageRoot) : renderHelp(plan.helpPrefix, packageRoot));return 0;
    case 'version':
      try { const metadata = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8'));
        if (typeof metadata.version !== 'string' || !metadata.version) throw Error('version');
        line(stdout, metadata.version);
        try {
          for (const result of findSkills({ packageRoot, cwd, home: env.HOME || homedir(), claudeConfigDir: env.CLAUDE_CONFIG_DIR }))
            if (result.found && result.stale === 'older') line(stderr, staleLine(result, metadata.version, cwd));
        } catch { /* The skills check never changes --version. */ }
        return 0;
      } catch { line(stderr, 'This PDD package has no readable version metadata.');return 1; }
    case 'autopilot.off': case 'autopilot.observe': case 'autopilot.auto': case 'autopilot-trust': case 'autopilot-untrust': {
      try {
        const module = autopilot ?? await import('./autopilot.mjs');
        const input = plan.local.startsWith('autopilot.')
          ? { action: 'mode', mode: plan.local.slice(10) }
          : { action: plan.local.slice(10), names: [...plan.operands] };
        const result = await module.runAutopilot(input, { cwd, stdin, stdout, ...autopilotPorts });
        line(result.exitCode === 0 ? stdout : stderr, result.message);
        if (result.exitCode === 0) {
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
          json: plan.options['--json'] === true, cwd: context.toplevel, packageRoot }, productPorts);
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255
          || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid product reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message.replace(/\n$/, ''));
        return result.exitCode;
      } catch (error) { line(stderr, `The product command failed.${reason(error)}`); return 1; }
    }
    case 'workflow-suite': case 'workflow-park': case 'workflow-yield': case 'workflow-request-uptake': case 'workflow-run': case 'workflow-done': case 'workflow-ask': case 'workflow-approve': case 'workflow-changes':
    case 'workflow-cancel': case 'workflow-status': case 'workflow-open': case 'workflow-evidence': case 'workflow-evidence-associate': {
      if (plan.local === 'workflow-suite' && !plan.options['--command']?.trim()) { line(stderr, 'Use pdd workflow suite --command COMMAND [--timeout MIN].'); return 2; }
      if (plan.local === 'workflow-evidence-associate' && (!plan.options['--workspace']?.trim() || !plan.options['--stage'] || !plan.options['--test']?.length)) {
        line(stderr, 'Use pdd workflow evidence-associate ISSUE --workspace PATH --stage current|pr1 --test PATH... .'); return 2;
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
        const result = await runner[name]({ ...input, cwd, packageRoot, ...(plan.local === 'workflow-suite' ? {env} : {}) }, { say: text => line(plan.local === 'workflow-suite' ? stdout : stderr, text), ...(['workflow-run', 'workflow-yield'].includes(plan.local) ? { env } : {}) });
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255
          || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid runner reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch (error) {
        line(stderr, `The pdd workflow command failed before it could report. Check pdd workflow status; nothing was retried.${reason(error)}`);
        return 1;
      }
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
        const server = mcpServer ?? await import('./try-mcp.mjs');
        return await server.runMcp({ cwd, env }, { stdin, stdout, stderr });
      } catch (error) { line(stderr, `pdd mcp could not start.${reason(error)}`); return 1; }
    }
    case 'setup': {
      return setupWithWorkflowAgent({ cwd, env }, { ...workflowAgentPorts, checkWorkflowAgents: workflowAgents.checkWorkflowAgents, stderr, setup: async () => {
      let code = 0;
      for (const result of setupSkills({ packageRoot, cwd, home: env.HOME || homedir(), claudeConfigDir: env.CLAUDE_CONFIG_DIR })) {
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
        if (await action({ env, packageRoot }, { stdin, stdout, stderr, confirm })) code = 1;
      } catch (error) { line(stderr, `pdd setup: MCP registration failed.${reason(error)}`); code = 1; }
      try {
        const module = autopilot ?? await import('./autopilot.mjs');
        const before = savedAutopilot(context?.toplevel);
        const result = await module.runAutopilot({ action: 'setup', interactive: !!stdin.isTTY, inRepo: !!context?.toplevel },
          { cwd: context?.toplevel ?? cwd, stdin, stdout, ...autopilotPorts });
        if (result.message) line(result.exitCode === 0 ? stdout : stderr, result.message);
        if (result.exitCode) code = result.exitCode;
        // Setup saves a first mode only in this checkout and never writes to GitHub, where the workers read it.
        const saved = savedAutopilot(context?.toplevel)?.mode;
        if (result.exitCode === 0 && before === undefined && ['off', 'observe', 'auto'].includes(saved))
          line(stdout, `Setup saved the Autopilot mode only in this checkout. Autopilot workers read pdd.json on GitHub; to update it there, run pdd autopilot ${saved}.`);
      } catch (error) { line(stderr, `Autopilot settings failed.${reason(error)}`); code = 1; }
      return code;
      } });
    }
    case 'runtime-jobs':
      try { const slots = runtimeSlots ?? await import('./runtime-slots.mjs'); return await slots.runJobs({ env }, { stdout, stderr }); }
      catch (error) { line(stderr, `Local interpreter jobs could not be read.${reason(error)}`); return 5; }
    case 'contracts': case 'contracts-sync':
      try {
        const commands = contracts ?? await import('./contracts.mjs');
        return await commands.runContracts({ words: plan.local === 'contracts-sync' ? ['sync'] : [], options: { ...plan.options }, cwd }, { env, stdout, stderr });
      } catch (error) { line(stderr, `Local contracts could not be read.${reason(error)}`); return 5; }
    case 'runtime-check':
    case 'runtime-try':
      try {
        const runtime = await import('./runtime-client.mjs');
        return await runtime[plan.local === 'runtime-check' ? 'runCheck' : 'runTry']({ words: [...plan.operands], options: { ...plan.options }, cwd, cache: plan.local === 'runtime-check' }, { stdout, stderr, env });
      } catch (error) {
        line(stderr, `pdd stopped with an internal error. If it sent checks, read them with pdd test --read. Do not send them again.${reason(error)}`);
        return 3;
      }
    case 'project-files': {
      const { runProjectFiles } = await import('./project-files.mjs');
      return runProjectFiles({ cwd, json: !!plan.options['--json'] }, { stdout, stderr });
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
  }
}
