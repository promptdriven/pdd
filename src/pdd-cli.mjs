// Generated from prompts/cli/pdd-cli.prompt.md (sha256: 0054f2c5d8af5362e53af4c0901e67be03e7fd7f44af94f7b28ce7fc5d8d1b5f).
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { launchNativeSession } from './native-session.mjs';
import { renderSessionIntro } from './session-intro.mjs';
import { CommandInputError, parseArgv } from './argument-parser.mjs';
import { renderCompletion } from './completion.mjs';
import { PUBLIC_COMMAND_MANIFEST } from './command-catalog.mjs';
import { listWorkflowAreas, formatWorkflowList } from './workflow-areas.mjs';

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
const line = (stream, text) => stream.write(`${text}\n`);
const RUNNER_ROUTES = {
  'workflow-run': plan => ['startRun', { name: plan.operands[0], issue: plan.operands[1], agent: plan.options['--agent'] ?? 'codex' }],
  'workflow-done': plan => ['stepDone', { step: plan.operands[0], ...(plan.options['--summary'] !== undefined ? { summary: plan.options['--summary'] } : {}) }],
  'workflow-approve': plan => ['approveRun', { ref: plan.operands[0] }],
  'workflow-changes': plan => ['changeRun', { ref: plan.operands[0], text: plan.operands.slice(1).join(' ') }],
  'workflow-cancel': plan => ['cancelRun', { ref: plan.operands[0] }],
  'workflow-status': plan => ['runStatus', { ref: plan.operands[0] }],
  'workflow-open': plan => ['openRun', { ref: plan.operands[0] }],
};
export function renderHelp(prefix = []) {
  const rows = PUBLIC_COMMAND_MANIFEST.filter(({ form }) => !prefix.length
    || prefix.every((word, index) => form.slice(4).split(/\s+/)[index] === word));
  return ['PDD: prompt-driven development for your coding agent.', '',
    ...rows.map(({ form, description }) => `  ${form}  ${description}`), '',
    'session and the named workflows open a chat in this terminal.',
    'workflow run starts the first area chat in Herdr session pdd and exits. The person approves each area; after the last step pdd pushes the branch and opens a real PR.',
    'pdd never merges.'].join('\n');
}
export async function runPdd(argv, { stdout = process.stdout, stderr = process.stderr,
  cwd = process.cwd(), packageRoot = PACKAGE_ROOT, env = process.env, nativeSession = launchNativeSession, workflowRunner, workflowAreas } = {}) {
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
    case 'workflow-run': case 'workflow-done': case 'workflow-approve': case 'workflow-changes':
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
    case 'session': {
      let message;
      try { message = renderSessionIntro({ packageRoot, cwd, request: plan.operands.join(' '), workflowName: plan.workflowName }); }
      catch { line(stderr, 'The PDD skills could not be read. Use a complete PDD package.');return 1; }
      return nativeSession({ agent: plan.options['--agent'] ?? 'codex', cwd, message, stderr });
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
