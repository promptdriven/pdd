// Generated from prompts/cli/pdd-cli.prompt.md (sha256: ea2e0aac6cdfb3fd99a575ce807fab3a0fc3394015c09aaf7c012e8808b4f9d1).
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
function validDecisionResult(value) {
  return value&&['recorded','started','refused','uncertain','failed'].includes(value.state)
    &&Number.isInteger(value.exitCode)&&value.exitCode>=0&&value.exitCode<=255
    &&typeof value.message==='string'&&value.message.trim()&&!/[\r\n]/.test(value.message);
}
export function renderHelp(prefix = []) {
  const rows = PUBLIC_COMMAND_MANIFEST.filter(({ form }) => !prefix.length
    || prefix.every((word, index) => form.slice(4).split(/\s+/)[index] === word));
  return ['PDD: prompt-driven development for your coding agent.', '',
    ...rows.map(({ form, description }) => `  ${form}  ${description}`), '',
    'Read the entire Prompting guide with pdd --skill before drafting any Story.',
    'Session and recipe shortcuts open foreground native conversations. Workflow run/resume may push branches and create real PRs.',
    'Default stage mode keeps the PDD controller running. --chat returns after delivery; native area chats continue in Herdr. No background PDD controller or keeper is started. Use explicit resume to reconcile a saved run.',
    'Use workflow attach RUN_ID for the actual active stage; completed archives are not live sessions.'].join('\n');
}
function guidanceError(stderr) {
  line(stderr, 'The complete PDD guidance could not be read. Use a package containing the canonical guide, skill, references and manual recipes.');
  return 1;
}
export async function runPdd(argv, { stdout = process.stdout, stderr = process.stderr,
  cwd = process.cwd(), packageRoot = PACKAGE_ROOT, nativeSession = launchNativeSession, workflowRunner, workflowDefinitions, workflowStages,
  workflowRecords, workflowDecider, lookupPhone, clientAdapter, confirm, approvalEvidence, stdin = process.stdin, stdinIsTTY, input, env = process.env,
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
    case 'workflow-decide': {
      try {
        const decider=workflowDecider??await import('./workflow-decide.mjs');
        const stages=workflowStages??await import('./workflow-stage-herdr.mjs');
        const json=plan.options['--json']===true;
        const result=await decider.decideWorkflow({runId:plan.operands[0],decision:plan.options['--decision'],
          decisionId:plan.options['--id'],expectStage:plan.options['--expect-stage'],expectSeq:Number(plan.options['--expect-seq']),
          ...(plan.options['--text']!==undefined?{text:plan.options['--text']}:{}),yes:plan.options['--yes']===true,via:plan.options['--via'],phoneId:plan.options['--phone'],approval:plan.options['--approval'],cwd,packageRoot},
          {...stages,loadGuidance,workflowRunner,stdin,env,confirm,lookupPhone,clientAdapter,stdout:json?stderr:stdout,stderr});
        if(!validDecisionResult(result))throw Error('Invalid decision reply');
        const {exitCode,...body}=result;
        line(stdout,json?JSON.stringify({v:1,...body}):body.message);return exitCode;
      } catch {line(stderr,'The decision could not be confirmed. Inspect the saved run before retrying.');return 1;}
    }
    case 'workflow-run':
    case 'workflow-resume':
    case 'workflow-attach': {
      const progress = plan.local === 'workflow-attach' ? null : createWorkflowProgress({ stdout });
      const interrupted = () => { progress.interrupt(); exit(130); };
      if (progress) {
        if (plan.local === 'workflow-resume') progress.observe({ event: 'resume.requested', runId: plan.operands[0] });
        line(stdout, plan.local === 'workflow-run'
          ? plan.options['--chat'] ? `Starting area chat for issue ${plan.operands[1]}. This command returns after delivery; the chat continues in Herdr.` : `Starting ${plan.operands[0]} for issue ${/^\d+$/.test(plan.operands[1]) ? '#' : ''}${plan.operands[1]}. This terminal stays busy until the run stops at a gate.`
          : `Inspecting run ${plan.operands[0]}. With a decision, this terminal stays busy until the next gate.`);
        signalSource.once('SIGINT', interrupted);
      }
      try {
        const runner = workflowRunner ?? await import('./workflow-runner.mjs');
        const stages = workflowStages ?? await import('./workflow-stage-herdr.mjs');
        const {runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage,closeHerdrRun,inspectHerdrChat} = stages;
        if (![runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage].every(fn=>typeof fn==='function')) throw Error('Missing stage transport');
        const ports = {loadGuidance,launchNativeSession:nativeSession,runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage,...(closeHerdrRun?{closeHerdrRun}:{}),...(inspectHerdrChat?{inspectHerdrChat}:{}),stdout,stderr, ...(progress ? { onProgress: progress.observe } : {})};
        let runId = plan.operands[0];
        if (plan.local !== 'workflow-run' && runId && !/^[a-f0-9]{8}-[a-f0-9]{4}-4[a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$/i.test(runId)) {
          const found = await resolveRun(runId, { cwd, records: workflowRecords, fs: undefined });
          if (!found.run) { line(stderr, found.reason === 'ambiguous' ? formatAmbiguous(found.runs, plan.local === 'workflow-attach' ? 'attach' : 'resume') : `No saved workflow matches ${runId}.`); return 2; }
          runId = found.run.runId;
        } else if (plan.local !== 'workflow-run' && !runId) {
          const found = await resolveRun(null, { cwd, records: workflowRecords });
          if (!found.run) { line(stderr, found.reason === 'ambiguous' ? formatAmbiguous(found.runs, 'resume') : 'No saved workflow run was found in this repository.'); return 2; }
          runId = found.run.runId;
        }
        if(plan.local==='workflow-resume' && plan.options['--decision']) {
          const gate=await runner.readWorkflowDecision({runId,cwd},ports);
          if(gate.state!=='ready'){line(stderr,gate.message);return 1;}
          const result=await (workflowDecider??{decideWorkflow}).decideWorkflow({runId,decision:plan.options['--decision'],decisionId:randomUUID(),expectStage:gate.stage,expectSeq:gate.journalSeq,cwd,packageRoot},
            {...ports,workflowRunner:runner,stdin,env,confirm:input?async question=>/^(y|yes)$/i.test(String(await input(question)).trim()):confirm});
          if(!validDecisionResult(result))throw Error('Invalid decision reply');
          line(stdout,result.message);return result.exitCode;
        }
        const result = plan.local === 'workflow-run'
          ? await runner.runWorkflow({name:plan.operands[0],issue:plan.operands[1],
            agent:plan.options['--agent']??'codex',...(plan.options['--chat']?{chat:true}:{}),cwd,packageRoot},ports)
          : plan.local === 'workflow-attach'
          ? await runner.attachWorkflow({runId,cwd,packageRoot},ports)
          : await runner.resumeWorkflow({runId,cwd,packageRoot,
            ...(plan.options['--decision']!==undefined?{decision:plan.options['--decision']}:{} )},ports);
        if (!result || !['completed','waiting','running','failed','recovery_required'].includes(result.state)
          || !Number.isInteger(result.exitCode) || result.exitCode<0 || result.exitCode>255
          || typeof result.message!=='string' || !result.message.trim()) throw Error('Invalid local workflow reply');
        line(stdout,result.message);
        return result.exitCode;
      } catch {
        line(stderr,'The local workflow runner could not confirm this operation. Inspect its saved state before repeating a mutation; no automatic retry was sent.');
        return 1;
      } finally { if (progress) signalSource.off('SIGINT', interrupted); }
    }
    case 'workflow-status':
    case 'workflow-watch': {
      try {
        const all = plan.options['--all'] === true;
        const found = plan.local === 'workflow-watch' && plan.operands[0]
          ? await resolveRun(plan.operands[0], { cwd, records: workflowRecords })
          : { runs: await discoverRuns({ cwd, all, records: workflowRecords }) };
        if (plan.local === 'workflow-watch' && !found.run) {
          line(stderr, found.reason === 'ambiguous' ? formatAmbiguous(found.runs, 'watch') : `No saved workflow matches ${plan.operands[0]}.`); return 2;
        }
        const runs = found.run ? [found.run] : found.runs;
        line(stdout, formatStatus(runs, { all, repository: runs.length === 1 ? runs[0].repo : null })); return 0;
      } catch { line(stderr, 'Saved workflow runs are unavailable. Retry after checking local records.'); return 1; }
    }
    case 'workflow-approve':
    case 'workflow-skip':
    case 'workflow-changes': {
      const action = plan.local === 'workflow-approve' ? 'approve' : plan.local === 'workflow-skip' ? 'skip' : 'changes';
      const ref = plan.operands[0];
      const found = await resolveRun(ref, { cwd, records: workflowRecords, waiting: true });
      if (!found.run) { line(stderr, found.reason === 'ambiguous' ? formatAmbiguous(found.runs, action) : `No saved workflow waiting for a decision${ref ? ` matches ${ref}` : ''}.`); return 2; }
      try {
        const runner=workflowRunner??await import('./workflow-runner.mjs');
        const stages=workflowStages??await import('./workflow-stage-herdr.mjs');
        const gate=await runner.readWorkflowDecision({runId:found.run.runId,cwd},{loadGuidance,...stages});
        if(gate.state!=='ready'){line(stderr,gate.message);return 1;}
        const terminal=stdinIsTTY===undefined?stdin:{isTTY:stdinIsTTY};
        const result=await decideWorkflow({runId:found.run.runId,decision:action,decisionId:randomUUID(),
          expectStage:gate.stage,expectSeq:gate.journalSeq,cwd,packageRoot,via:plan.options['--via'],phoneId:plan.options['--phone'],approval:plan.options['--approval'],yes:plan.options['--yes']===true,
          ...(action==='changes'?{text:plan.operands.slice(1).join(' ')}:{})},
          {workflowRunner:runner,...stages,loadGuidance,stdout,stderr,stdin:terminal,env,lookupPhone,clientAdapter,
            ...(input?{confirm:async question=>/^(y|yes)$/i.test(String(await input(question)).trim())}:{}),
            ...(approvalEvidence?{readApprovalEvidence:approvalEvidence}:{})});
        if(!validDecisionResult(result))throw Error('Invalid decision reply');
        line(result.state==='refused'?stderr:stdout,result.message);return result.exitCode;
      }catch{line(stderr,'The shared decision could not be confirmed. Inspect the saved run before retrying.');return 1;}
    }
    case 'workflow-report': {
      try {
        const runner=workflowRunner??await import('./workflow-runner.mjs');
        const stages=workflowStages??await import('./workflow-stage-herdr.mjs');
        const result=await runner.reportWorkflowStage({runId:plan.operands[plan.commandId==='step.done'?1:0],stageId:plan.operands[plan.commandId==='step.done'?0:1],attemptId:plan.operands[2],cwd,packageRoot},
          {...stages,loadGuidance,stdout:stderr,stderr});
        line(stdout,JSON.stringify(result));return result.exitCode;
      }catch{line(stderr,'The area stage report could not be confirmed. Inspect the saved attempt.');return 1;}
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
