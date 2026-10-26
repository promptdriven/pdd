// Generated from prompts/cli/pdd-cli.prompt.md (sha256: 3bd47f7c3f777a7d966352136c1eee6602d1ebcd03e09827473d5e3af170391d).
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { loadGuidance } from './guidance.mjs';
import { launchNativeSession } from './native-session.mjs';
import { CommandInputError, parseArgv } from './argument-parser.mjs';
import { renderCompletion } from './completion.mjs';
import { PUBLIC_COMMAND_MANIFEST } from './command-catalog.mjs';
import { formatLocalWorkflows } from './workflow-list.mjs';

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
  cwd = process.cwd(), packageRoot = PACKAGE_ROOT, nativeSession = launchNativeSession, workflowRunner, workflowDefinitions, workflowStages, workflowRecords } = {}) {
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
      try {
        const runner = workflowRunner ?? await import('./workflow-runner.mjs');
        const stages = workflowStages ?? await import('./workflow-stage-herdr.mjs');
        const {runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage} = stages;
        if (![runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage].every(fn=>typeof fn==='function')) throw Error('Missing stage transport');
        const ports = {loadGuidance,launchNativeSession:nativeSession,runHerdrStage,inspectHerdrStage,attachHerdrStage,closeHerdrStage,stdout,stderr};
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
        line(stdout,result.message);
        return result.exitCode;
      } catch {
        line(stderr,'The local workflow runner could not confirm this operation. Inspect its saved state before repeating a mutation; no automatic retry was sent.');
        return 1;
      }
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
    case 'workflow-runs': {
      try {
        const records = workflowRecords ?? await import('./workflow-run-records.mjs');
        const index = await records.readRunIndex({ cwd });
        const requested = plan.operands[0];
        const entries = requested ? index.entries.filter(entry => entry.runId === requested) : index.entries;
        const runs = [];
        for (const entry of entries) {
          const journal = await records.readJournalLast(entry.runDir);
          if (!journal.value?.state) continue;
          runs.push({ ...entry, ...(await records.runStatusFromState(journal.value.state, { now: Date.now() }, { cwd })), runId: entry.runId });
        }
        const localTime = value => Number.isFinite(value) ? new Intl.DateTimeFormat(undefined, { hour: '2-digit', minute: '2-digit', second: '2-digit', hour12: false }).format(new Date(value)) : 'unknown';
        const age = value => {
          if (!Number.isFinite(value)) return 'unknown';
          const seconds = Math.max(0, Math.floor((Date.now() - value) / 1000));
          if (seconds < 60) return `${seconds}s`;
          const minutes = Math.floor(seconds / 60); if (minutes < 60) return `${minutes}m`;
          const hours = Math.floor(minutes / 60); return hours < 48 ? `${hours}h` : `${Math.floor(hours / 24)}d`;
        };
        const duration = (start, end) => {
          if (!Number.isFinite(start) || !Number.isFinite(end) || end < start) return 'unknown';
          let seconds = Math.floor((end - start) / 1000), hours = Math.floor(seconds / 3600); seconds %= 3600;
          const minutes = Math.floor(seconds / 60); seconds %= 60;
          return `${hours ? `${hours}h` : ''}${minutes ? `${minutes}m` : ''}${seconds}s`;
        };
        const stateLabel = run => run.state === 'completed' ? 'done' : run.state === 'waiting' ? 'waiting for you' : run.state === 'running' ? `working: ${run.stage?.id ?? 'unknown'}` : run.state;
        const stageJson = stage => { const { startedAt, endedAt, ...rest } = stage; return { ...rest, start: localTime(startedAt), end: localTime(endedAt), duration: duration(startedAt, endedAt) }; };
        if (requested && !runs.length) { line(stdout, plan.options['--json'] ? JSON.stringify({ v: 1, runId: requested, state: 'unknown', message: 'Run not found' }) : 'Run not found'); return 1; }
        if (!requested) {
          runs.sort((a, b) => (b.startedAt ?? 0) - (a.startedAt ?? 0));
          if (plan.options['--json']) { line(stdout, JSON.stringify({ v: 1, runs: runs.map(run => ({ v: 1, runId: run.runId, workflow: run.workflow, repo: run.repo, issue: run.issue, state: stateLabel(run), age: age(run.startedAt), open: `pdd workflow runs ${run.runId}` })) })); return 0; }
          for (const run of runs) line(stdout, `${run.repo && run.issue?.number ? `${run.repo}#${run.issue.number}` : `run#${run.issue?.number ?? '?'}`}${run.issue?.title ? ` ${run.issue.title}` : ''} · ${run.workflow ?? 'unknown'} · ${stateLabel(run)} · age ${age(run.startedAt)} · open: pdd workflow runs ${run.runId}`);
          if (!runs.length) line(stdout, 'No saved runs.');
          return 0;
        }
        const run = runs[0];
        if (plan.options['--json']) { line(stdout, JSON.stringify({ v: 1, runId: run.runId, workflow: run.workflow, repo: run.repo, issue: run.issue, root: run.root, state: stateLabel(run), stages: (run.steps ?? []).map(stageJson) })); return 0; }
        line(stdout, `${run.repo && run.issue?.number ? `${run.repo}#${run.issue.number}` : `run#${run.issue?.number ?? '?'}`} · ${run.workflow ?? 'unknown'} · ${stateLabel(run)} · worktree ${run.root ?? 'unknown'}`);
        for (const stage of run.steps ?? []) {
          const session = stage.session ? ` · ${stage.session.agent} session ${stage.session.id}` : '';
          const reopen = stage.reopen ? ` · reopen: ${stage.reopen}` : '';
          const reason = !stage.session && stage.sessionReason ? ` · ${stage.sessionReason}` : '';
          line(stdout, `${stage.id ?? 'unknown'} · ${stage.state ?? 'unknown'} · start ${localTime(stage.startedAt)} · end ${localTime(stage.endedAt)} · duration ${duration(stage.startedAt, stage.endedAt)} · agent ${stage.agent ?? 'unknown'}${session}${reopen}${reason}`);
        }
        return 0;
      } catch { line(stderr, 'Saved workflow runs are unavailable. Retry after checking local records.'); return 1; }
    }
    default: line(stderr, 'Unsupported command in PDD Alpha. Run pdd --help.');return 2;
  }
}
