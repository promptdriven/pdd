// Generated from prompts/cli/pdd-cli.prompt.md (sha256: 8e5349a532faa8fcf0de227c1c86f76551eb7608fdc6acdcc5ab83c6cc72bb23).
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { loadGuidance } from './guidance.mjs';
import { launchNativeSession } from './native-session.mjs';
import { renderSessionIntro } from './session-intro.mjs';
import { CommandInputError, parseArgv } from './argument-parser.mjs';
import { renderCompletion } from './completion.mjs';
import { PUBLIC_COMMAND_MANIFEST } from './command-catalog.mjs';
import { formatLocalWorkflows } from './workflow-list.mjs';
import { createWorkflowProgress } from './workflow-progress.mjs';

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
const line = (stream, text) => stream.write(`${text}\n`);
export function renderHelp(prefix = []) {
  const rows = PUBLIC_COMMAND_MANIFEST.filter(({ form }) => !prefix.length
    || prefix.every((word, index) => form.slice(4).split(/\s+/)[index] === word));
  return ['PDD: prompt-driven development for your coding agent.', '',
    ...rows.map(({ form, description }) => `  ${form}  ${description}`), '',
    'Read the entire Prompting guide with pdd --skill before drafting any Story.',
    'Session and recipe shortcuts open foreground native conversations. Workflow run/resume may push branches and create real PRs.',
    'Keep the PDD controller running while its native stages work in background Herdr. After controller exit, use explicit resume to reconcile the original; no background PDD daemon continues it.',
    'Use workflow attach RUN_ID for the actual active stage; completed archives are not live sessions.'].join('\n');
}
function guidanceError(stderr) {
  line(stderr, 'The complete PDD guidance could not be read. Use a package containing the canonical guide, skill, references and manual recipes.');
  return 1;
}
export async function runPdd(argv, { stdout = process.stdout, stderr = process.stderr,
  cwd = process.cwd(), packageRoot = PACKAGE_ROOT, nativeSession = launchNativeSession, workflowRunner, workflowDefinitions, workflowStages,
  signalSource = process, exit = code => process.exit(code) } = {}) {
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
    case 'skill':
      try { line(stdout, loadGuidance({ packageRoot, cwd }));return 0; }
      catch { return guidanceError(stderr); }
    case 'workflow-run':
    case 'workflow-resume':
    case 'workflow-attach': {
      const progress = plan.local === 'workflow-attach' ? null : createWorkflowProgress({ stdout });
      const interrupted = () => { progress.interrupt(); exit(130); };
      if (progress) {
        if (plan.local === 'workflow-resume') progress.observe({ event: 'resume.requested', runId: plan.operands[0] });
        line(stdout, plan.local === 'workflow-run'
          ? `Starting ${plan.operands[0]} for issue ${/^\d+$/.test(plan.operands[1]) ? '#' : ''}${plan.operands[1]}. This terminal stays busy until the run stops at a gate.`
          : `Inspecting run ${plan.operands[0]}. With a decision, this terminal stays busy until the next gate.`);
        signalSource.once('SIGINT', interrupted);
      }
      try {
        const runner = workflowRunner ?? await import('./workflow-runner.mjs');
        const stages = workflowStages ?? await import('./workflow-stage-herdr.mjs');
        const {runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage,closeHerdrRun} = stages;
        if (![runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage].every(fn=>typeof fn==='function')) throw Error('Missing stage transport');
        const ports = {loadGuidance,launchNativeSession:nativeSession,runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage,closeHerdrRun,stdout,stderr, ...(progress ? { onProgress: progress.observe } : {})};
        const result = plan.local === 'workflow-run'
          ? await runner.runWorkflow({name:plan.operands[0],issue:plan.operands[1],
            agent:plan.options['--agent']??'codex',cwd,packageRoot},ports)
          : plan.local === 'workflow-attach'
          ? await runner.attachWorkflow({runId:plan.operands[0],cwd,packageRoot},ports)
          : await runner.resumeWorkflow({runId:plan.operands[0],cwd,packageRoot,
            ...(plan.options['--decision']!==undefined?{decision:plan.options['--decision']}:{} )},ports);
        if (!result || !['completed','waiting','failed','recovery_required'].includes(result.state)
          || !Number.isInteger(result.exitCode) || result.exitCode<0 || result.exitCode>255
          || typeof result.message!=='string' || !result.message.trim()) throw Error('Invalid local workflow reply');
        if (!(result.state === 'waiting' && progress?.gateShown?.())) line(stdout,result.message);
        return result.exitCode;
      } catch {
        line(stderr,'The local workflow runner could not confirm this operation. Inspect its saved state before repeating a mutation; no automatic retry was sent.');
        return 1;
      } finally { if (progress) signalSource.off('SIGINT', interrupted); }
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
        const definitions=workflowDefinitions??await import('./workflow-definition-loader.mjs');
        const workflows=await definitions.listWorkflowDefinitions({cwd,packageRoot});
        if (!Array.isArray(workflows)) throw Error('Invalid definition listing');
        line(stdout,formatLocalWorkflows({workflows,default:null},{json:plan.options['--json']===true}));return 0;
      } catch { line(stderr,'Workflow definitions could not be read or validated. Check the selected project definitions and bundled package.');return 1; }
    default: line(stderr, 'Unsupported command in PDD Alpha. Run pdd --help.');return 2;
  }
}
