// Generated from prompts/cli/pdd-cli.prompt.md (sha256: e0c2903f62e78560356ac090766705e77bfe5280ffb370791d404e4ccb9d4565).
import { readFileSync } from 'node:fs';
import { randomUUID } from 'node:crypto';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { loadGuidance } from './guidance.mjs';
import { launchNativeSession } from './native-session.mjs';
import { CommandInputError, parseArgv } from './argument-parser.mjs';
import { renderCompletion } from './completion.mjs';
import { PUBLIC_COMMAND_MANIFEST } from './command-catalog.mjs';
import { formatLocalWorkflows } from './workflow-list.mjs';
import { createWorkflowProgress } from './workflow-progress.mjs';
import { discoverRuns, resolveRun, formatAmbiguous, formatStatus } from './workflow-shortcuts.mjs';
import { decideWorkflow } from './workflow-decide.mjs';

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
  workflowRecords, workflowDecider, stdin = process.stdin, env = process.env, confirm, lookupPhone, clientAdapter, readApprovalEvidence,
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
    case 'workflow-attach':
    case 'workflow-decide':
    case 'workflow-approve':
    case 'workflow-changes':
    case 'workflow-skip': {
      const action = ({'workflow-approve':'approve','workflow-changes':'changes','workflow-skip':'skip'})[plan.local]
        ?? plan.options['--decision'];
      const json = plan.options['--json'] === true;
      const progress = plan.local === 'workflow-attach' ? null : createWorkflowProgress({ stdout: json ? stderr : stdout });
      const interrupted = () => { progress.interrupt(); exit(130); };
      if (progress) {
        if (plan.local === 'workflow-resume') progress.observe({event:'resume.requested',runId:plan.operands[0]});
        if (plan.local === 'workflow-run') line(stdout,
          `Starting ${plan.operands[0]} for issue ${/^\d+$/.test(plan.operands[1]) ? '#' : ''}${plan.operands[1]}. This terminal stays busy until the run stops at a gate.`);
        else if (plan.local === 'workflow-resume') line(stdout,
          `Inspecting run ${plan.operands[0] ?? 'in this repository'}. With a decision, this terminal stays busy until the next gate.`);
        signalSource.once('SIGINT', interrupted);
      }
      try {
        const runner = workflowRunner ?? await import('./workflow-runner.mjs');
        const stages = workflowStages ?? await import('./workflow-stage-herdr.mjs');
        const {runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage} = stages;
        if (![runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage].every(fn=>typeof fn==='function')) throw Error('Missing stage transport');
        const ports = {loadGuidance,launchNativeSession:nativeSession,runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage,
          stdout:json?stderr:stdout,stderr,workflowRunner:runner,stdin,env,confirm,lookupPhone,clientAdapter,readApprovalEvidence,
          ...(progress ? {onProgress:progress.observe} : {})};
        let runId = plan.operands[0], runCwd = cwd;
        if (plan.local !== 'workflow-run') {
          const found = await resolveRun(runId, {cwd,records:workflowRecords,waiting:!!action && plan.local !== 'workflow-decide' && !runId});
          if (found.run) {
            runId = found.run.runId; runCwd = found.run.root ?? cwd;
            progress?.observe({event:'resume.requested',runId,repo:found.run.repo,issue:found.run.issue?.number});
          } else if (!runId || !/^[a-f0-9]{8}-[a-f0-9]{4}-4[a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$/i.test(runId)) {
            line(stderr,found.reason === 'ambiguous' ? formatAmbiguous(found.runs,action ?? plan.local.slice(9)) : `No saved workflow matches ${runId ?? 'this repository'}.`);return 2;
          }
        }
        let result;
        if (action) {
          let stage = plan.options['--expect-stage'], seq = Number(plan.options['--expect-seq']);
          if (plan.local !== 'workflow-decide') {
            const gate = await runner.readWorkflowDecision({runId,cwd:runCwd},ports);
            if (gate.state !== 'ready') { line(json?stderr:stdout,gate.message);return 1; }
            stage = gate.stage; seq = gate.journalSeq;
          }
          const decider = workflowDecider ?? {decideWorkflow};
          result = await decider.decideWorkflow({runId,decision:action,decisionId:plan.options['--id'] ?? randomUUID(),
            expectStage:stage,expectSeq:seq,cwd:runCwd,packageRoot,yes:plan.options['--yes']===true,
            ...(action==='changes'?{text:plan.options['--text'] ?? plan.operands.slice(1).join(' ')}:{}),
            ...(plan.options['--via']?{via:plan.options['--via'],phoneId:plan.options['--phone'],approval:plan.options['--approval']}:{})},ports);
          if (!result || !['recorded','started','refused','uncertain','failed'].includes(result.state)) throw Error('Invalid decision reply');
        } else {
          result = plan.local === 'workflow-run'
            ? await runner.runWorkflow({name:plan.operands[0],issue:plan.operands[1],agent:plan.options['--agent']??'codex',cwd,packageRoot},ports)
            : plan.local === 'workflow-attach'
            ? await runner.attachWorkflow({runId,cwd:runCwd,packageRoot},ports)
            : await runner.resumeWorkflow({runId,cwd:runCwd,packageRoot},ports);
          if (!result || !['completed','waiting','failed','recovery_required'].includes(result.state)) throw Error('Invalid workflow reply');
        }
        if (!Number.isInteger(result.exitCode) || result.exitCode<0 || result.exitCode>255 || typeof result.message!=='string' || !result.message.trim()) throw Error('Invalid reply');
        const {exitCode,...body} = result;
        line(stdout,json?JSON.stringify({v:1,...body}):body.message);return exitCode;
      } catch {
        line(stderr,'The local workflow runner could not confirm this operation. Inspect its saved state before repeating a mutation; no automatic retry was sent.');return 1;
      } finally { if (progress) signalSource.off('SIGINT',interrupted); }
    }
    case 'workflow-status':
    case 'workflow-watch': {
      try {
        const all = plan.options['--all'] === true;
        const found = plan.local === 'workflow-watch'
          ? await resolveRun(plan.operands[0], {cwd,records:workflowRecords})
          : {runs:await discoverRuns({cwd,all,records:workflowRecords})};
        if (plan.local === 'workflow-watch' && !found.run) {
          line(stderr,found.reason === 'ambiguous' ? formatAmbiguous(found.runs,'watch') : 'No saved workflow run matches.');return 2;
        }
        line(stdout,formatStatus(found.run?[found.run]:found.runs,{all}));return 0;
      } catch { line(stderr,'Saved workflow runs are unavailable. Retry after checking local records.');return 1; }
    }
    case 'session': {
      let context;
      try { context = loadGuidance({ packageRoot, cwd, workflows: true, workflowName: plan.workflowName }); }
      catch { return guidanceError(stderr); }
      return nativeSession({ agent: plan.options['--agent'] ?? 'codex', cwd, context,
        request: plan.operands.join(' '), stderr });
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
