// Generated from prompts/cli/product.prompt.md.
// Layer 1 core: workflow-free product status, wave readiness, scoped GitHub issue creation, and /pdd handoff (ZERO legacy workflow imports).
import { loadAgentDefinitions } from '../../agent-config.mjs';
import { causeText } from '../../shared/safe-read.mjs';
import { command, portsFor } from './github-state.mjs';
import { canonicalGithubUrl, marker, validBase, validThrough } from './pr-matching.mjs';
import { invalid } from './markdown-utils.mjs';
import { auditProductPlan } from './plan-audit.mjs';
import { collectSafePromptFiles, comparisonBases, counts, documents, progress, readProduct, rulesForRun, storyEvidence, trimFolderSlashes, warnings } from './progress.mjs';

const BUILTIN_AGENTS = ['codex', 'claude', 'gemini', 'agy'];
const AGENT_CHOICES = '--agent codex, --agent claude, --agent gemini or --agent agy';
const SHELL_RESERVED_NAMES = new Set([
  'BASHOPTS', 'BASHPID', 'BASH_ALIASES', 'BASH_ARGC', 'BASH_ARGV', 'BASH_CMDS', 'BASH_COMMAND',
  'BASH_LINENO', 'BASH_SOURCE', 'BASH_SUBSHELL', 'BASH_VERSINFO', 'DIRSTACK', 'EGID', 'EPOCHREALTIME', 'EPOCHSECONDS', 'EUID', 'FUNCNAME', 'GID',
  'GROUPS', 'HISTCMD', 'KSH_VERSION', 'LINENO', 'OPTIND', 'PIPESTATUS', 'PPID', 'RANDOM', 'SECONDS', 'SHELLOPTS', 'SHLVL', 'SRANDOM', 'TTYIDLE',
  'UID', 'ZSH_EVAL_CONTEXT', 'ZSH_SUBSHELL', '_', 'signals',
]);

export function validateProductAgent(requested, { cwd, env = process.env } = {}, load = loadAgentDefinitions) {
  if (requested === undefined || BUILTIN_AGENTS.includes(requested)) return { ok: true, agent: requested, definition: null };
  let definitions;
  try { definitions = load({ cwd, env }); }
  catch (error) { return { ok: false, agent: null, message: `${error.message} Fix ~/.config/pdd/agents.json, or choose ${AGENT_CHOICES}.` }; }
  const found = definitions.find(item => item.name === requested);
  if (found && BUILTIN_AGENTS.includes(found.id)) return { ok: true, agent: found.kind, definition: null };
  if (found) {
    const reserved = Object.keys(found.env ?? {}).filter(key => SHELL_RESERVED_NAMES.has(key));
    if (reserved.length) {
      return {
        ok: false,
        agent: null,
        message: `The agents.json entry ${JSON.stringify(String(found.name))} sets names in env that the shell controls: ${reserved.join(', ')}. pdd cannot give them to the chat. Remove them from that entry's env, then run the command again.`,
      };
    }
    return { ok: true, agent: found.kind, definition: found };
  }
  const names = definitions.filter(item => !BUILTIN_AGENTS.includes(item.id)).map(item => JSON.stringify(item.name));
  return {
    ok: false,
    agent: null,
    message: `Unknown agent ${JSON.stringify(String(requested))}. Choose ${AGENT_CHOICES}${names.length ? `, or a name from ~/.config/pdd/agents.json: ${names.join(', ')}.` : '. ~/.config/pdd/agents.json has no agent with that name.'}`,
  };
}

export async function productStatus(input, given = {}) {
  const { p, docs, product, details, ready, warning, bases, waves, baseBranch, baseSha } = await progress(input, given);
  const allWarnings = [...warning];
  if (!p._customReadFile && docs.planText && (docs.prompts.length > 0 || docs.boundaryOperations.length > 0)) {
    const trackedFolders = [
      ...product.parts.map(part => trimFolderSlashes(part.folder)),
      ...docs.prompts.map(item => item.path.includes('/') ? item.path.slice(0, item.path.lastIndexOf('/')) : ''),
    ].filter(Boolean);
    const promptFiles = collectSafePromptFiles(input.cwd, trackedFolders);
    if (promptFiles !== null) {
      const audit = auditProductPlan({ mapText: docs.mapText, planText: docs.planText, promptFiles });
      for (const msg of audit.warnings) if (!allWarnings.includes(msg)) allWarnings.push(msg);
    }
  }
  const core = product.stories.filter(story => story.tag === 'CORE' && product.runs.some(run => run.stories.includes(story.id)));
  const parts = product.parts.map(part => ({ part: part.part, ...counts(core.filter(story => story.part === part.part).map(story => story.id), details) }));
  const journeyIds = product.runs
    .filter(run => run.part === 'all')
    .flatMap(run => run.stories)
    .filter(id => product.journeys.some(j => j.id === id));
  if (journeyIds.length) parts.push({ part: 'journeys', ...counts(journeyIds, details) });
  const result = {
    name: product.name,
    size: product.size,
    parts,
    slices: [...new Set(product.runs.map(run => run.slice))].map(slice => ({
      slice,
      ...counts(product.runs.filter(run => run.slice === slice).flatMap(run => run.stories).filter(id => journeyIds.includes(id) || core.some(story => story.id === id)), details),
    })),
    waves,
    ...(baseBranch ? { base: baseBranch } : {}),
    ...(baseSha ? { baseSha } : {}),
    runs: details.map(detail => {
      const prSummary = detail.prs.map(pr => `PR #${pr.number} (${pr.isDraft ? 'draft' : pr.state.toLowerCase()})`).join(', ');
      const hasMergedDisplayPr = detail.prs.some(pr => pr.state === 'MERGED');
      return {
        run: detail.run.run,
        issue: detail.issue?.number ?? null,
        state: detail.unverified ? 'unverified'
          : detail.done ? 'merged'
          : detail.closedUnbuilt ? `issue closed (${detail.storyCounts.pass} of ${detail.storyCounts.total} pass)`
          : detail.local ? `${detail.local.state}${detail.local.stage?.id ? ` (step: ${detail.local.stage.id})` : ''}`
          : hasMergedDisplayPr ? prSummary
          : detail.prs.length ? prSummary
          : detail.issue ? 'issue ready'
          : 'planned',
        prs: detail.prs.map(pr => pr.number),
        fromPr: detail.fromPr,
        ...(detail.run.sharedSurfaces?.length ? { sharedSurfaces: detail.run.sharedSurfaces } : {}),
      };
    }),
    ready,
    questions: product.questions,
    ...(allWarnings.length ? { warnings: allWarnings } : {}),
  };
  Object.defineProperty(result, comparisonBases, { value: bases });
  return result;
}

export async function productNext(input, given = {}) {
  const { product, details, ready, needsFor, warning, waves, baseBranch, baseSha } = await progress(input, given);
  return {
    ready,
    waiting: details.filter(detail => !detail.unverified && (!detail.issue || detail.closedUnbuilt) && needsFor(detail.run).length).map(detail => ({
      run: detail.run.run,
      needs: needsFor(detail.run),
      ...(detail.run.sharedSurfaces?.length ? { sharedSurfaces: detail.run.sharedSurfaces } : {}),
    })),
    waves,
    ...(baseBranch ? { base: baseBranch } : {}),
    ...(baseSha ? { baseSha } : {}),
    guidance: product.size === 'small' ? 'run one feature run' : ready.length >= 2 ? 'These can run in parallel, or one person can start them in order.' : '',
    ...(warning.length ? { warnings: warning } : {}),
  };
}

function issueTitle(product, run, warning) {
  const full = `${product.name}: ${run.run} (${run.stories.join(', ')})`;
  if ([...full].length <= 256) return full;
  warning.push(`Warning: ${run.run}'s issue title was shortened; all ${run.stories.length} Stories remain in its body.`);
  const suffix = ` (${run.stories.length} Stories)`;
  const label = [...`${product.name}: ${run.run}`];
  const room = 256 - [...suffix].length;
  return `${label.length > room ? label.slice(0, room - 1).join('') + '…' : label.join('')}${suffix}`;
}

export async function productStart({ cwd, run, noRun = false, agent = 'codex', through, base, packageRoot }, given = {}) {
  let issue = null, created = false;
  try {
    const explicitThrough = validThrough(through), explicitBase = validBase(base);
    const p = portsFor(given, { defaultStoryEvidence: storyEvidence });
    const { product, boundaries } = await documents({ cwd }, p), planned = product.runs.find(row => row.run === run);
    if (!planned) invalid(`Unknown planned run ${run}.`);
    const chosen = validateProductAgent(agent, { cwd, env: given.env ?? process.env });
    if (!chosen.ok) invalid(chosen.message);
    const effectiveThrough = explicitThrough ?? (product.through === 'prompt-pr' ? 'prompt-pr' : undefined);
    const state = await progress({
      cwd,
      ...(explicitThrough !== undefined ? { through: explicitThrough } : {}),
      ...(explicitBase !== undefined ? { base: explicitBase } : {}),
    }, given, run);
    const { repo, localRuns, baseBranch, baseSha, waves } = state;
    const selected = state.details.find(detail => detail.run.run === run);
    issue = selected.issue;
    if (selected.unverified) {
      throw Error(`Saved issue #${issue.number} for ${run} is unverified: ${selected.reason}. Run pdd product start ${run} to link it again.`);
    }
    const parent = localRuns.find(record => record.workflow === 'product');
    const parentIssueNumber = parent?.number ?? product.issue ?? null;
    if (!issue) {
      const activeParts = [planned.part, ...(planned.sharedSurfaces ?? [])];
      const contractFiles = product.size === 'small' ? [] : [...new Set([
        ...boundaries.filter(row => planned.part === 'all' || activeParts.includes(row.From) || activeParts.includes(row.To)).map(row => row.Contract),
        'contracts/world.md',
      ])];
      const sharedSurfaceDescriptions = (planned.sharedSurfaces ?? []).map(surface => {
        const partInfo = product.parts.find(part => part.part === surface);
        const surfacePrompts = (product.prompts ?? []).filter(item => item.part === surface).map(item => item.path);
        const label = partInfo?.folder ? `${surface} (${partInfo.folder})` : surface;
        return surfacePrompts.length ? `${label} [${surfacePrompts.join(', ')}]` : label;
      });
      const matchingRules = rulesForRun(product, planned);
      const rulesBlock = matchingRules.length
        ? ['', '## Rules to check', ...matchingRules.map(entry => {
          const verified = entry.verifiedBy ? ` (Verified by: ${entry.verifiedBy})` : '';
          return entry.id ? `- ${entry.id} (${entry.owner}): ${entry.rule}${verified}` : `- ${entry.rule}${verified}`;
        })]
        : [];
      // #3328 mechanical fix: only single-part slices mock other parts from contracts; `all`/journey runs test real unmocked cross-part integration while still protecting contracts/.
      const integrationGuidance = planned.part === 'all'
        ? `Integration run across all parts: verify real unmocked cross-part journeys (no fake parts) and run \`pdd --product\`.${contractFiles.length ? ' Do not change contracts/ in this run.' : ''}`
        : (contractFiles.length ? 'Other parts are fakes from their contracts. Do not change contracts/ in this run.' : '');
      const body = [
        parentIssueNumber ? `Part of #${parentIssueNumber} (product).` : '',
        `Plan: product/${product.size === 'small' ? 'map' : 'plan'}.md, run ${run}, slice ${planned.slice}.`,
        `Stories: ${planned.stories.join(', ')}.`,
        `Name each Story file with its map id first${planned.stories[0] ? `, for example ${planned.stories[0]}-story.md` : ''}.`,
        ...planned.stories.map(id => `${id}: ${(product.stories.find(story => story.id === id)?.story ?? product.journeys.find(story => story.id === id)?.journey)}`),
        `Folder: ${product.parts.find(part => part.part === planned.part)?.folder ?? 'user_stories/journeys'}.${contractFiles.length ? ` Contracts: ${contractFiles.join(', ')}.` : ''}`,
        sharedSurfaceDescriptions.length ? `Shared surfaces to update: ${sharedSurfaceDescriptions.join(', ')}.` : '',
        integrationGuidance,
        ...rulesBlock,
        marker(run),
      ].filter((line, idx, arr) => line !== '' || (idx > 0 && arr[idx + 1] === '## Rules to check')).join('\n');
      const payload = { repository: repo.repository, title: issueTitle(product, planned, state.warning), body };
      const response = p.createIssue ? await p.createIssue(payload) : { url: await command(p, cwd, 'gh',
        ['issue', 'create', '--repo', payload.repository, '--title', payload.title, '--body', payload.body]) };
      const createdNumber = canonicalGithubUrl(typeof response?.url === 'string' ? response.url.trim() : '', repo.repository, 'issues');
      if (!createdNumber) invalid('Issue creation was not confirmed. Inspect GitHub before trying again.');
      issue = { number: createdNumber }; created = true;
      await state.lookup.bind(run, issue.number);
    } else if (selected.closedUnbuilt) {
      await p.reopenIssue({ cwd, repository: repo.repository, number: issue.number });
      issue = { ...issue, state: 'OPEN' };
    }
    const warning = [
      ...state.warning,
      ...warnings(product).filter(text => text.startsWith(`Warning: ${run} `)),
      ...(state.needsFor(planned).length ? [`Advice: ${run} still needs ${state.needsFor(planned).join(', ')}.`] : []),
    ].join('\n');
    if (noRun) {
      return { exitCode: 0, message: [warning, `Issue #${issue.number} ready for ${run}.`].filter(Boolean).join('\n'), issue: issue.number, created, started: false };
    }
    if (typeof p.startRun === 'function') {
      const reply = await p.startRun({
        name: 'feature',
        issue: issue.number,
        agent,
        cwd,
        ...(effectiveThrough !== undefined ? { through: effectiveThrough } : {}),
        ...(explicitBase !== undefined ? { base: explicitBase } : {}),
        ...(packageRoot === undefined ? {} : { packageRoot }),
      });
      if (!reply || !Number.isInteger(reply.exitCode) || typeof reply.message !== 'string') throw Error('Invalid feature workflow reply.');
      return { ...reply, message: [warning, reply.message].filter(Boolean).join('\n'), issue: issue.number, created, started: reply.exitCode === 0 };
    }
    // Workflow-free default handoff: print crisp /pdd instruction with wave + SHA-pinned base context.
    const waveEntry = waves.find(w => w.runs.includes(run));
    const meta = [
      waveEntry ? `Wave ${waveEntry.wave}` : null,
      baseBranch ? `base ${baseBranch}${baseSha ? ` @ ${baseSha.slice(0, 7)}` : ''}` : null,
    ].filter(Boolean).join(', ');
    const handoffLines = [
      warning,
      `Issue #${issue.number} ready for ${run}${meta ? ` (${meta})` : ''}.`,
      `Next: open your coding agent and run /pdd for issue #${issue.number} (or queue it with pdd autopilot start --issue ${issue.number}).`,
    ].filter(Boolean).join('\n');
    return { exitCode: 0, message: handoffLines, issue: issue.number, created, started: false, handoff: '/pdd' };
  } catch (error) {
    return { exitCode: 1, message: causeText(error.message) || 'The planned run could not start.', issue: issue?.number ?? null, created, started: false };
  }
}

export async function runProduct(input, given = {}) {
  try {
    if (input.command === 'start') return productStart(input, given);
    const product = await readProduct(input, given), warning = warnings(product);
    if (input.command === 'next') {
      const next = await productNext(input, given);
      const readySharedLines = next.ready.flatMap(runName => {
        const planned = product.runs.find(row => row.run === runName);
        return planned?.sharedSurfaces?.length ? [`${runName}: shared surfaces: ${planned.sharedSurfaces.join(', ')}.`] : [];
      });
      const waveLines = (next.waves ?? []).map(w => `Wave ${w.wave}${w.cyclic ? ' (cycle)' : ''}: ${w.runs.join(', ')}.`);
      return {
        exitCode: 0,
        message: [
          ...warning,
          ...(next.warnings ?? []),
          next.guidance,
          ...waveLines,
          next.ready.length ? `Can start now: ${next.ready.join(', ')}.` : 'Can start now: none.',
          ...next.ready.map(run => `pdd product start ${run}${input.through ? ` --through ${input.through}` : ''}`),
          ...readySharedLines,
          ...next.waiting.map(row => `${row.run}: waits for ${row.needs.join(', ')}${row.sharedSurfaces?.length ? ` (shared surfaces: ${row.sharedSurfaces.join(', ')})` : ''}.`),
        ].filter(Boolean).join('\n'),
      };
    }
    if (input.command !== 'status') invalid('Unknown product command.');
    const status = await productStatus(input, given);
    return {
      exitCode: 0,
      message: input.json ? JSON.stringify(status) : [
        `${status.name} (${status.size}, ${product.parts.length} parts). Plan: product/${product.size === 'small' ? 'map' : 'plan'}.md${status.base ? ` · Base: ${status.base}${status.baseSha ? ` (${status.baseSha.slice(0, 7)})` : ''}` : ''}`,
        ...warning,
        ...(status.warnings ?? []),
        'Part  Stories pass  Stale  Not run',
        ...status.parts.map(part => `${part.part}  ${part.pass} of ${part.total}  ${part.stale}  ${part.notRun}`),
        ...(status.waves ?? []).map(w => `Wave ${w.wave}${w.cyclic ? ' (cycle)' : ''}: ${w.runs.join(', ')}.`),
        ...status.runs.map(run => `${run.run}: ${run.state}${run.sharedSurfaces?.length ? ` · shared surfaces: ${run.sharedSurfaces.join(', ')}` : ''}${run.issue ? ` · issue #${run.issue}` : ''}${run.fromPr ? ` · from PR #${run.fromPr}` : ''}`),
        ...status.slices.map(slice => `Slice ${slice.slice}: ${slice.pass} of ${slice.total} pass.`),
        `Can start now: ${status.ready.join(', ') || 'none'}. Questions open: ${status.questions.join(', ') || 'none'}.`,
        ...(status[comparisonBases] ?? []).map(base => `Compared with your local ${base}. Run git pull to see changes merged on GitHub.`),
        'Stale = passed on older files; a contract or prompt changed since.',
      ].join('\n'),
    };
  } catch (error) {
    return { exitCode: 1, message: causeText(error.message) || 'The product could not be read.' };
  }
}
