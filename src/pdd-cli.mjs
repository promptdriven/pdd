// Generated from prompts/cli/pdd-cli.prompt.md (sha256: bd47f7c8b18ae48fb93a15b795c3321f274b9fb5591474d57d5d68386ca4b32c).
import { readFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { CommandInputError, parseArgv } from './argument-parser.mjs';
import { renderCompletion } from './completion.mjs';
import { NAMES, PUBLIC_COMMAND_MANIFEST } from './command-catalog.mjs';
import { listWorkflowAreas, formatWorkflowList } from './workflow-areas.mjs';
import { setupProject } from './project-setup.mjs';
import { findSkills, setupSkills } from './skills-install.mjs';
import { pathDiagnostic } from './path-diagnostic.mjs';
import { causeText } from './runtime-output.mjs';

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
const line = (stream, text) => stream.write(`${text}\n`);
// The real reason of an unexpected error, after the fixed safe line.
const reason = error => { const text = causeText(error?.message ?? error); return text ? ` Reason: ${text}` : ''; };
const skillCount = folders => `${folders.length} PDD skill${folders.length === 1 ? '' : 's'}`;
const skillNames = folders => folders.map(folder => basename(folder)).join(', ');
// npx skills update changes only what npx skills add recorded (0.1.8 tester); add replaces any copy.
const staleLine = ({ found, stale }, version, cwd) => `PDD skills in ${found} ${stale === 'older' ? `are older than pdd ${version}` : `differ from the skills of pdd ${version}`}. To update them, run: npx skills add promptdriven/pdd${[join(cwd, '.agents/skills'), join(cwd, '.claude/skills')].includes(found) ? '' : ' -g'} -a codex -a claude-code -y`;
const RUNNER_ROUTES = {
  'workflow-run': plan => ['startRun', { name: plan.operands[0], issue: plan.operands[1], agent: plan.options['--agent'] ?? 'codex', ...(plan.options['--base'] !== undefined ? { base: plan.options['--base'] } : {}), ...(plan.options['--adopt-corpus'] !== undefined ? { adoptCorpus: plan.options['--adopt-corpus'] } : {}) }],
  'workflow-evidence': plan => ['recordEvidence', { ref: plan.operands[0], summaryFile: plan.options['--summary'] }],
  'workflow-done': plan => ['stepDone', { step: plan.operands[0], ...(plan.options['--summary'] !== undefined ? { summary: plan.options['--summary'] } : {}) }],
  'workflow-approve': plan => ['approveRun', { ref: plan.operands[0] }],
  'workflow-ask': plan => ['askPerson', { text: plan.operands.join(' ') }],
  'workflow-changes': plan => ['changeRun', { ref: plan.operands[0], text: plan.operands.slice(1).join(' ') }],
  'workflow-cancel': plan => ['cancelRun', { ref: plan.operands[0] }],
  'workflow-status': plan => ['runStatus', { ref: plan.operands[0], ...Object.fromEntries(['all', 'cancelled', 'json'].filter(name => plan.options[`--${name}`]).map(name => [name, true])) }],
  'workflow-open': plan => ['openRun', { ref: plan.operands[0] }],
};
const FIRST_HELP_LINE = 'PDD: prompt-driven development for your coding agent.';
// Learn PDD: the paths of the guide files in this package, never in the cwd. Help reads no file to print them.
const guidePaths = packageRoot => [`Prompting guide: ${join(packageRoot, 'docs', 'prompting-guide.md')}`,
  `RUNBOOK: ${join(packageRoot, 'RUNBOOK.md')}`];
const TOPICS = {
  prompting: ['In PDD, prompts are the source. Code follows the prompts.',
    '1. Prompt: prompts/NAME.prompt.md. Write what the program does in plain English, then ## Dependencies, then one Runtime interface block.',
    '2. Story: user_stories/STORY.md. Write one thing that a person can do, then a numbered ## Acceptance criteria list.',
    '3. Test: tests/STORY.json. When the repo keeps its own tests in tests/ or test/, use tests/runtime/ or test/runtime/. Write steps with an exact check for each criterion.',
    `4. Check: run pdd ${NAMES.test} --fill-hash, then pdd ${NAMES.lint} (0 AI calls), then pdd ${NAMES.test} STORY on the PDD interpreter.`,
    '5. Approve: a person reads each prompt and runs pdd approve PROMPT. An agent never approves.'],
};
const renderTopic = (topic, packageRoot) => [FIRST_HELP_LINE, '', ...TOPICS[topic], '', ...guidePaths(packageRoot)].join('\n');
export function renderHelp(prefix = [], packageRoot = PACKAGE_ROOT) {
  const rows = PUBLIC_COMMAND_MANIFEST.filter(({ form }) => !prefix.length
    || prefix.every((word, index) => form.slice(4).split(/\s+/)[index] === word));
  return [FIRST_HELP_LINE, '',
    ...rows.map(({ form, description }) => `  ${form}  ${description}`), '',
    ...(prefix.length ? [] : ['Learn PDD: run pdd help prompting, or read the Prompting guide and the RUNBOOK.', ...guidePaths(packageRoot), '']),
    'Open Codex or Claude as usual and call a PDD skill: $pdd-feature in Codex, /pdd-feature in Claude Code (also pdd-bug, pdd-small-change, pdd-prompting).',
    `workflow ${NAMES.run} opens the first area chat in Herdr session pdd and exits. The person approves each area; after the last step pdd pushes the branch and opens a real PR.`,
    'pdd never merges.'].join('\n');
}
export async function runPdd(argv, { stdout = process.stdout, stderr = process.stderr,
  cwd = process.cwd(), packageRoot = PACKAGE_ROOT, env = process.env, workflowRunner, workflowAreas,
  stdin = process.stdin, confirm, mcpServer, runtimeSlots, contracts, product, productPorts, gitContext, workflowProve, provePorts } = {}) {
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
    case 'workflow-run': case 'workflow-done': case 'workflow-ask': case 'workflow-approve': case 'workflow-changes':
    case 'workflow-cancel': case 'workflow-status': case 'workflow-open': case 'workflow-evidence': {
      if (plan.local === 'workflow-evidence' && !plan.options['--summary']) { line(stderr, 'Use pdd workflow evidence ISSUE --summary FILE.'); return 2; }
      const [name, input] = RUNNER_ROUTES[plan.local](plan);
      try {
        const runner = workflowRunner ?? await import('./workflow-runner.mjs');
        if (typeof runner[name] !== 'function') throw Error('Missing runner export');
        const result = await runner[name]({ ...input, cwd, packageRoot }, { say: text => line(stderr, text) });
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
        const result = await module.proveRun({ ref: plan.operands[0], test: plan.options['--test'], expect: plan.options['--expect'], cwd }, provePorts);
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
      try {
        const { setupAgentMcp } = await import('./agent-mcp-setup.mjs');
        if (await setupAgentMcp({ env, packageRoot }, { stdin, stdout, stderr, confirm })) code = 1;
      } catch (error) { line(stderr, `pdd setup: MCP registration failed.${reason(error)}`); code = 1; }
      return code;
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
        return await runtime[plan.local === 'runtime-check' ? 'runCheck' : 'runTry']({ words: [...plan.operands], options: { ...plan.options }, cwd }, { stdout, stderr, env });
      } catch (error) {
        line(stderr, `pdd stopped with an internal error. If it sent checks, read them with pdd test --read. Do not send them again.${reason(error)}`);
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
    default: line(stderr, 'Unsupported command in pdd. Run pdd --help.');return 2;
  }
}
