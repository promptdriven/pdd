// Contract: prompts/cli/workflow-shortcuts.prompt.md.
import * as defaultRecords from './workflow-run-records.mjs';

const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
const PREFIX = /^[0-9a-f]{8,}$/i;
const clean = value => String(value ?? '').replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').replace(/\s+/g, ' ').trim();
const issueNumber = value => {
  const text = String(value ?? '').trim();
  const match = text.match(/(?:^#?|\/issues\/)([1-9][0-9]*)\/?$/) ?? text.match(/#([1-9][0-9]*)$/);
  return match ? Number(match[1]) : null;
};
const issueRepo = value => {
  const text = String(value ?? '').trim().replace(/\/$/, '');
  const url = text.match(/^https:\/\/github\.com\/([^/]+\/[^/]+)\/issues\/[1-9][0-9]*$/);
  if (url) return url[1];
  const hash = text.match(/^([^#]+)#[1-9][0-9]*$/);
  return hash ? hash[1] : null;
};
const repoName = repo => typeof repo === 'string' ? repo.split('/').at(-1) : null;
const issueRef = entry => entry?.repo && entry?.issue?.number ? `${entry.repo}#${entry.issue.number}` : `#${entry?.issue?.number ?? '?'}`;
const issueLabel = (entry, runs = []) => `${displayRef(entry, runs)}${entry?.issue?.title ? ` "${clean(entry.issue.title)}"` : ''}`;
const displayRef = (entry, runs) => {
  const name = repoName(entry.repo);
  const collision = runs.some(run => repoName(run.repo) === name && run.repo !== entry.repo);
  return `${collision ? entry.repo : name ?? '?'}#${entry.issue?.number ?? '?'}`;
};
const stateLabel = status => status?.state === 'completed' ? 'done'
  : status?.state === 'waiting' ? 'waiting for you'
  : status?.state === 'running' ? `working: ${status.stage?.id ?? 'unknown'}`
  : status?.state ?? 'unknown';

async function inRepository(cwd, ports = {}) {
  try { return Boolean(await defaultRecords.gitCommonDir(cwd, ports)); } catch { return false; }
}
function runInCommonDir(run, common) {
  if (!common || !run) return false;
  const root = `${String(common).replace(/\/$/, '')}/`;
  return typeof run.commonDir === 'string' && (run.commonDir === common || run.commonDir.startsWith(root))
    || typeof run.runDir === 'string' && (run.runDir === common || run.runDir.startsWith(`${root}pdd/workflows/`)
      || run.runDir.startsWith(`${root}worktrees/`) && run.runDir.includes('/pdd/workflows/'));
}
function sameRepo(a, b) {
  if (!a || !b) return false;
  return a === b || repoName(a) === b || repoName(b) === a;
}
async function statusFor(entry, records, ports = {}) {
  if (!records.readJournalLast || !records.runStatusFromState) return { ...entry, state: 'unknown', steps: [] };
  const journal = await records.readJournalLast(entry.runDir, ports);
  if (!journal?.value?.state) return { ...entry, state: 'unknown', steps: [] };
  return { ...entry, ...(await records.runStatusFromState(journal.value.state, { now: Date.now() }, ports)), runId: entry.runId,
    repo: entry.repo ?? journal.value.state.repo ?? null, issue: entry.issue ?? journal.value.state.issue ?? null };
}
export async function discoverRuns({ cwd, all = false, records = defaultRecords, fs: io } = {}) {
  const ports = { cwd, ...(io ? { fs: io } : {}) };
  const index = await records.readRunIndex({ ...ports, ...(all ? { all: true } : {}) });
  const runs = [];
  for (const entry of index?.entries ?? []) runs.push(await statusFor(entry, records, ports));
  return runs;
}
function matchesReference(run, ref, { repository, local } = {}) {
  if (!ref) return false;
  if (UUID.test(ref)) return run.runId?.toLowerCase() === ref.toLowerCase();
  if (!/^#?[1-9][0-9]*$/.test(ref) && PREFIX.test(ref)) return run.runId?.toLowerCase().startsWith(ref.toLowerCase());
  const number = issueNumber(ref); if (!number || run.issue?.number !== number) return false;
  const wanted = issueRepo(ref);
  if (wanted) return sameRepo(run.repo, wanted);
  return local || !repository ? true : sameRepo(run.repo, repository);
}
function nextCommand(run, command, { repository, runs = [] } = {}) {
  const ref = repository && sameRepo(run.repo, repository) ? String(run.issue?.number ?? '') : displayRef(run, runs);
  return `pdd workflow ${command}${ref ? ` ${ref}` : ''}`;
}
export async function resolveRun(ref, { cwd, records = defaultRecords, all = false, repository, waiting = false, fs: io } = {}) {
  const local = !all && await inRepository(cwd, { fs: io });
  const qualified = !!ref && (UUID.test(ref) || issueRepo(ref) || (!/^#?[1-9][0-9]*$/.test(ref) && PREFIX.test(ref)));
  let runs = await discoverRuns({ cwd, all: all || !local, records, fs: io });
  if (local && qualified) {
    const indexed = await discoverRuns({cwd, all:true, records, fs:io});
    runs = [...new Map([...runs,...indexed].map(run=>[run.runId,run])).values()];
  }
  let candidates = runs;
  const common = local ? await defaultRecords.gitCommonDir(cwd, { fs: io }) : null;
  if (local && common && !qualified) {
    const scoped = candidates.filter(run => runInCommonDir(run, common));
    candidates = scoped;
  }
  if (waiting) candidates = candidates.filter(run => run.state === 'waiting' && (!run.waitingFor || run.waitingFor.decisions?.length));
  if (ref) {
    const matches = candidates.filter(run => matchesReference(run, ref, { repository, local }));
    candidates = matches.length || !PREFIX.test(ref) ? matches : candidates.filter(run=>run.runId?.toLowerCase().startsWith(ref.toLowerCase()));
  }
  if (!ref && !all && local && candidates.length) {
    // A command without an operand is scoped to the current checkout.
    candidates = candidates.filter(run => !repository || sameRepo(run.repo, repository));
  }
  if (candidates.length === 1) return { run: candidates[0], runs, local };
  return { run: null, runs: candidates, local, reason: candidates.length ? 'ambiguous' : 'not_found' };
}
export function formatAmbiguous(runs, command) {
  const lines = [`More than one saved run matches. Choose one:`];
  for (const run of runs) lines.push(`  ${issueLabel(run, runs)} — ${nextCommand(run, command, {runs})}`);
  return lines.join('\n');
}
export function formatStatus(runs, { repository, all = false } = {}) {
  if (all) runs = runs.filter(run=>['waiting','running'].includes(run.state));
  if (!runs.length) return 'No saved workflow runs.';
  return runs.map(run => {
    const state = stateLabel(run), stage = run.stage?.id ? ` · stage ${run.stage.id}` : '';
    let next = '';
    if (state === 'waiting for you') next = ` · next: ${nextCommand(run, run.waitingFor?.decisions?.length === 0 ? 'resume' : 'approve', { repository, runs })}`;
    else if (state.startsWith('working:')) next = ` · next: ${nextCommand(run, 'watch', { repository, runs })}`;
    else if (state === 'failed' || state === 'recovery_required') next = ` · next: ${nextCommand(run, 'resume', { repository, runs })}`;
    return `${issueLabel(run, runs)} · ${run.workflow ?? 'unknown'} · ${state}${stage}${next}`;
  }).join('\n');
}
