// Generated from prompts/cli/pdd-cli.prompt.md (sha256: 9b2ee0fffec5fd12008fc7ad24e333daf331e02a2c3e14d89dcdb2312a389622).
import { readFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { CommandInputError, parseArgv } from './argument-parser.mjs';
import { renderCompletion } from './completion.mjs';
import { PUBLIC_COMMAND_MANIFEST } from './command-catalog.mjs';
import { listWorkflowAreas, formatWorkflowList } from './workflow-areas.mjs';
import { setupProject } from './project-setup.mjs';
import { setupSkills } from './skills-install.mjs';

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
const line = (stream, text) => stream.write(`${text}\n`);
const skillCount = folders => `${folders.length} PDD skill${folders.length === 1 ? '' : 's'}`;
const skillNames = folders => folders.map(folder => basename(folder)).join(', ');
const RUNNER_ROUTES = {
  'workflow-run': plan => ['startRun', { name: plan.operands[0], issue: plan.operands[1], agent: plan.options['--agent'] ?? 'codex' }],
  'workflow-done': plan => ['stepDone', { step: plan.operands[0], ...(plan.options['--summary'] !== undefined ? { summary: plan.options['--summary'] } : {}) }],
  'workflow-approve': plan => ['approveRun', { ref: plan.operands[0] }],
  'workflow-ask': plan => ['askPerson', { text: plan.operands.join(' ') }],
  'workflow-changes': plan => ['changeRun', { ref: plan.operands[0], text: plan.operands.slice(1).join(' ') }],
  'workflow-cancel': plan => ['cancelRun', { ref: plan.operands[0] }],
  'workflow-status': plan => ['runStatus', { ref: plan.operands[0], ...Object.fromEntries(['all', 'cancelled', 'json'].filter(name => plan.options[`--${name}`]).map(name => [name, true])) }],
  'workflow-open': plan => ['openRun', { ref: plan.operands[0] }],
};
export function renderHelp(prefix = []) {
  const rows = PUBLIC_COMMAND_MANIFEST.filter(({ form }) => !prefix.length
    || prefix.every((word, index) => form.slice(4).split(/\s+/)[index] === word));
  return ['PDD: prompt-driven development for your coding agent.', '',
    ...rows.map(({ form, description }) => `  ${form}  ${description}`), '',
    'Open Codex or Claude as usual and call a PDD skill: $pdd-feature in Codex, /pdd-feature in Claude Code (also pdd-bug, pdd-small-change, pdd-prompting).',
    'workflow run starts the first area chat in Herdr session pdd and exits. The person approves each area; after the last step pdd pushes the branch and opens a real PR.',
    'pdd never merges.'].join('\n');
}
export async function runPdd(argv, { stdout = process.stdout, stderr = process.stderr,
  cwd = process.cwd(), packageRoot = PACKAGE_ROOT, env = process.env, workflowRunner, workflowAreas } = {}) {
  let plan;
  try { plan = parseArgv(argv); }
  catch (error) {
    line(stderr, error instanceof CommandInputError ? error.message : 'The command could not be parsed. Run pdd --help.');
    return 2;
  }
  switch (plan.local) {
    case 'help': line(stdout, renderHelp(plan.helpPrefix));return 0;
    case 'version':
      try { const metadata = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8'));
        if (typeof metadata.version !== 'string' || !metadata.version) throw Error('version');
        line(stdout, metadata.version);return 0;
      } catch { line(stderr, 'This PDD package has no readable version metadata.');return 1; }
    case 'workflow-run': case 'workflow-done': case 'workflow-ask': case 'workflow-approve': case 'workflow-changes':
    case 'workflow-cancel': case 'workflow-status': case 'workflow-open': {
      const [name, input] = RUNNER_ROUTES[plan.local](plan);
      try {
        const runner = workflowRunner ?? await import('./workflow-runner.mjs');
        if (typeof runner[name] !== 'function') throw Error('Missing runner export');
        const result = await runner[name]({ ...input, cwd, packageRoot });
        if (!result || !Number.isInteger(result.exitCode) || result.exitCode < 0 || result.exitCode > 255
          || typeof result.message !== 'string' || !result.message.trim()) throw Error('Invalid runner reply');
        line(result.exitCode === 0 ? stdout : stderr, result.message);
        return result.exitCode;
      } catch {
        line(stderr, 'The pdd workflow command failed before it could report. Check pdd workflow status; nothing was retried.');
        return 1;
      }
    }
    case 'setup': {
      let code = 0;
      for (const result of setupSkills({ packageRoot, cwd, home: env.HOME || homedir(), claudeConfigDir: env.CLAUDE_CONFIG_DIR })) {
        if (result.updated.length) line(stdout, `Updated ${skillCount(result.updated)} in ${result.root}: ${skillNames(result.updated)}`);
        if (result.found) line(stdout, `PDD skills found in ${result.found}`);
        else if (result.installed.length) line(stdout, `Installed ${skillCount(result.installed)} to ${result.root}: ${skillNames(result.installed)}`);
        if (result.error) { line(stderr, `pdd setup: the PDD skills could not be installed in ${result.root} (${result.error.code ?? result.error.message}).`); code = 1; }
      }
      try {
        const { file, changed } = setupProject({ cwd, packageRoot });
        line(stdout, changed ? `Wrote the PDD block in ${file}.` : `${file} already has this PDD block. No change.`);
      } catch (error) { line(stderr, `pdd setup: ${error.message}`); code = 1; }
      return code;
    }
    case 'runtime-check':
    case 'runtime-try':
      try {
        const runtime = await import('./runtime-client.mjs');
        return await runtime[plan.local === 'runtime-check' ? 'runCheck' : 'runTry']({ words: [...plan.operands], options: { ...plan.options }, cwd }, { stdout, stderr });
      } catch {
        line(stderr, 'pdd stopped with an internal error. If it sent checks, read them with pdd check --read. Do not send them again.');
        return 3;
      }
    case 'prompt-approve': {
      const { runApprove } = await import('./prompt-approve.mjs');
      return runApprove({ words: [...plan.operands], cwd }, { stdout, stderr });
    }
    case 'completion': stdout.write(renderCompletion(plan.operands[0]));return 0;
    case 'workflow-list':
      try {
        const areas = workflowAreas ?? { listWorkflowAreas, formatWorkflowList };
        const workflows = await areas.listWorkflowAreas({ packageRoot, cwd, home: env.HOME });
        if (!Array.isArray(workflows)) throw Error('Invalid workflow listing');
        line(stdout, areas.formatWorkflowList(workflows, { json: plan.options['--json'] === true }));return 0;
      } catch { line(stderr, 'The bundled workflows could not be read. Use a complete PDD package.');return 1; }
    default: line(stderr, 'Unsupported command in PDD Alpha. Run pdd --help.');return 2;
  }
}
