import { promises as fs } from 'node:fs';
import { createInterface } from 'node:readline';
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
const issueLabel = entry => `${issueRef(entry)}${entry?.issue?.title ? ` "${clean(entry.issue.title)}"` : ''}`;
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
  if (PREFIX.test(ref)) return run.runId?.toLowerCase().startsWith(ref.toLowerCase());
  const number = issueNumber(ref); if (!number || run.issue?.number !== number) return false;
  const wanted = issueRepo(ref);
  if (wanted) return sameRepo(run.repo, wanted);
  return local || !repository ? true : sameRepo(run.repo, repository);
}
function nextCommand(run, command, { repository } = {}) {
  const ref = repository && sameRepo(run.repo, repository) ? String(run.issue?.number ?? '') : issueRef(run);
  return `pdd workflow ${command}${ref ? ` ${ref}` : ''}`;
}
export async function resolveRun(ref, { cwd, records = defaultRecords, all = false, repository, waiting = false, fs: io } = {}) {
  const local = !all && await inRepository(cwd, { fs: io });
  const runs = await discoverRuns({ cwd, all: all || !local, records, fs: io });
  let candidates = runs;
  const common = local ? await defaultRecords.gitCommonDir(cwd, { fs: io }) : null;
  if (local && common) {
    const scoped = candidates.filter(run => runInCommonDir(run, common));
    if (scoped.length) candidates = scoped;
  }
  if (waiting) candidates = candidates.filter(run => run.state === 'waiting');
  if (ref) candidates = candidates.filter(run => matchesReference(run, ref, { repository, local }));
  if (!ref && !all && local && candidates.length) {
    // A command without an operand is scoped to the current checkout.
    candidates = candidates.filter(run => !repository || sameRepo(run.repo, repository));
  }
  if (candidates.length === 1) return { run: candidates[0], runs, local };
  return { run: null, runs: candidates, local, reason: candidates.length ? 'ambiguous' : 'not_found' };
}
export function formatAmbiguous(runs, command) {
  const lines = [`More than one saved run matches. Choose one:`];
  for (const run of runs) lines.push(`  ${issueLabel(run)} — ${nextCommand(run, command)}`);
  return lines.join('\n');
}
export function formatStatus(runs, { repository, all = false } = {}) {
  if (!runs.length) return 'No saved workflow runs.';
  return runs.map(run => {
    const state = stateLabel(run), stage = run.stage?.id ? ` · stage ${run.stage.id}` : '';
    let next = '';
    if (state === 'waiting for you') next = ` · next: ${nextCommand(run, 'approve', { repository })}`;
    else if (state.startsWith('working:')) next = ` · next: ${nextCommand(run, 'watch', { repository })}`;
    else if (state === 'failed' || state === 'recovery_required') next = ` · next: ${nextCommand(run, 'resume', { repository })}`;
    return `${issueLabel(run)} · ${run.workflow ?? 'unknown'} · ${state}${stage}${next}`;
  }).join('\n');
}
async function answer(input, output, prompt) {
  if (typeof input === 'function') { output.write(prompt); return String(await input(prompt)); }
  const rl = createInterface({ input, output, terminal: true });
  try { return await new Promise(resolve => rl.question(prompt, resolve)); } finally { rl.close(); }
}
export async function requireDecisionTerminal({ stdin = process.stdin, stdinIsTTY, env = process.env, yes = false, input, stdout, stderr, action, run, records, cwd } = {}) {
  const tty = stdinIsTTY ?? Boolean(stdin?.isTTY);
  // A person at a terminal must answer here. An agent relay is allowed to
  // continue without a TTY only after decideWorkflow proves its USER message.
  if (!tty && !env.PDD_AGENT_SESSION) { stderr.write('Decision commands require a real TTY; scripts cannot approve or skip runs.\n'); return false; }
  if (!yes && tty) {
    const reply = (await answer(input, stdout, `${action[0].toUpperCase()}${action.slice(1)} the plan for ${issueLabel(run)}? (y/N) `)).trim().toLowerCase();
    if (reply !== 'y' && reply !== 'yes') { stdout.write('No decision recorded.\n'); return false; }
  }
  return true;
}
