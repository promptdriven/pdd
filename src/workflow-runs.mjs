// Generated from prompts/cli/workflow-runs.prompt.md (sha256: bf6f85408a269d1d48b01fe4657d0cf467a542c1487d55210f673785590668a8).
import { execFile as execFileCallback } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { mkdirSync, readFileSync, readdirSync, realpathSync, renameSync, writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { promisify } from 'node:util';

const ordinary = promisify(execFileCallback);
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const sameRepo = (a, b) => typeof a === 'string' && typeof b === 'string' && a.toLowerCase() === b.toLowerCase();
const ended = run => ['cancelled', 'completed'].includes(run.state);

export const runDirFor = (commonDir, number) => join(commonDir, 'pdd', 'runs', String(number));
export const stateDirFor = (ports = {}) => ports.stateDir ?? join((ports.env ?? process.env).HOME || homedir(), '.local', 'state', 'pdd');
export const currentChat = run => [...(run.chats ?? [])].reverse().find(chat => chat.area === run.areas?.[run.area]?.name) ?? null;

export async function gitContext(cwd, ports = {}) {
  const exec = ports.execFile ?? ((file, args, options) => ordinary(file, args, { ...options, encoding: 'utf8' }));
  try {
    const read = async args => String((await exec('git', args, { cwd })).stdout ?? '').trim();
    return { toplevel: realpathSync(await read(['rev-parse', '--show-toplevel'])),
      commonDir: realpathSync(await read(['rev-parse', '--path-format=absolute', '--git-common-dir'])) };
  } catch { return null; }
}

export function readRun(runDir) {
  try {
    const run = JSON.parse(readFileSync(join(runDir, 'status.json'), 'utf8'));
    return object(run) && run.v === 1 && Number.isSafeInteger(run.number) ? run : null;
  } catch { return null; }
}

function runsIn(commonDir, { cancelled = false } = {}) {
  let names;
  try { names = readdirSync(join(commonDir, 'pdd', 'runs')); } catch { return []; }
  const folder = cancelled ? /^[1-9][0-9]*(?:-cancelled-[0-9a-f]+)?$/ : /^[1-9][0-9]*$/;
  return names.filter(name => folder.test(name)).map(name => readRun(runDirFor(commonDir, name))).filter(Boolean)
    .sort((a, b) => a.number - b.number);
}

// Every run on this machine: repositories come from the run index and the Herdr layout registry.
export function allRuns({ cancelled = false } = {}, ports = {}) {
  const commonDirs = new Set(readIndex(ports).map(entry => typeof entry.runDir === 'string' ? join(entry.runDir, '..', '..', '..') : null).filter(Boolean));
  try {
    const registry = JSON.parse(readFileSync(join(ports.layoutDirectory ?? join(stateDirFor(ports), 'herdr-layout'), 'registry.json'), 'utf8'));
    for (const repository of Array.isArray(registry?.repositories) ? registry.repositories : []) if (typeof repository?.commonDir === 'string') commonDirs.add(repository.commonDir);
  } catch { /* No registry yet. */ }
  const seen = new Set();
  return [...commonDirs].flatMap(commonDir => runsIn(commonDir, { cancelled }))
    .filter(run => !seen.has(run.runDir) && seen.add(run.runDir));
}

function readIndex(ports) {
  try {
    const index = JSON.parse(readFileSync(join(stateDirFor(ports), 'runs.json'), 'utf8'));
    return Array.isArray(index?.runs) ? index.runs.filter(entry => object(entry) && Number.isSafeInteger(entry.number)) : [];
  } catch { return []; }
}

function updateIndex(run, ports) {
  const directory = stateDirFor(ports);
  mkdirSync(directory, { recursive: true, mode: 0o700 });
  const entry = { repo: run.repo, number: run.number, workflow: run.workflow, state: run.state, runDir: run.runDir, root: run.root, updatedAt: run.updatedAt };
  const runs = [...readIndex(ports).filter(item => item.runDir !== run.runDir), entry].slice(-200);
  const temporary = join(directory, `.runs.json.${randomBytes(6).toString('hex')}.tmp`);
  writeFileSync(temporary, JSON.stringify({ version: 1, runs }, null, 2) + '\n', { mode: 0o600 });
  renameSync(temporary, join(directory, 'runs.json'));
}

// The C3 view (v:1) that phone clients read; it is derived from the saved run fields on every write.
export function statusView(run) {
  const areas = Array.isArray(run.areas) ? run.areas : [], area = areas[run.area] ?? null, done = object(run.done) ? run.done : {};
  const flat = areas.flatMap((item, index) => item.steps.map(step => ({ step, area: item.name, index, optional: item.optional.includes(step) })));
  const chatFor = name => [...(run.chats ?? [])].reverse().find(chat => chat.area === name) ?? null;
  const lastPr = (run.pr ?? []).some(pr => pr.stage === areas.at(-1)?.name);
  const gate = run.gate && run.state !== 'cancelled' && (run.state !== 'completed' || run.gate.kind === 'ask-code');
  const current = gate ? 'approve' : ended(run) ? null : lastPr ? 'merge' : area?.steps.find(step => !done[step]) ?? null;
  const total = flat.length;
  const stage = !current ? null : current === 'merge' ? { id: 'merge', kind: 'merge', index: total, total }
    : current === 'approve' ? { id: 'approve', kind: 'human', index: flat.filter(item => item.index <= run.area).length, total }
    : { id: current, kind: 'agent', index: flat.findIndex(item => item.index === run.area && item.step === current), total };
  const steps = flat.map((item, position) => {
    const record = done[item.step], chat = chatFor(item.area), previous = flat[position - 1];
    const state = record ? (/^skipped\b/i.test(record.summary ?? '') ? 'skipped' : 'done')
      : item.index < run.area ? (item.optional ? 'skipped' : 'unknown')
      : item.index === run.area && item.step === current ? 'current' : 'next';
    const startedAt = previous?.area === item.area ? done[previous.step]?.at ?? null : chat?.startedAt ?? null;
    return { id: item.step, kind: 'agent', area: item.area, optional: item.optional, state, startedAt: state === 'next' ? null : startedAt,
      endedAt: record?.at ?? null, agent: run.agent ?? null, session: chat?.session ?? null, summary: record?.summary ?? null };
  });
  const asked = run.question && !ended(run);
  const failure = !ended(run) && run.chatFailure?.area === area?.name ? run.chatFailure : null;
  const waitingFor = failure ? { decisions: [], what: `Chat ${failure.phase} not confirmed (${failure.code}): ${failure.message}. Run pdd workflow open ${run.number}.` } : asked ? { decisions: ['changes'], what: run.question.text.split('\n')[0].slice(0, 200) } : gate ? { decisions: ['approve', 'changes'], what: run.gate.kind === 'ask-code' ? 'Make the code PR now, or stop here and merge PR 1'
      : run.gate.kind === 'approve-pr' ? 'Try it, then approve to open the PR, or ask for changes' : `Approve the ${run.gate.area} area or ask for changes` }
    : run.state === 'waiting' && lastPr ? { decisions: [], what: 'Review and merge the PR on GitHub' } : { decisions: [], what: null };
  const chat = ended(run) ? null : currentChat(run);
  return { v: 1, stage, steps, waitingFor, resumeDecisions: gate ? ['approve', 'changes'] : [],
    waitingDecision: gate ? { ...(run.gate.id ? { id: run.gate.id } : {}), ...(Object.hasOwn(run.gate, 'promptSnapshot') ? { promptSnapshot: run.gate.promptSnapshot } : {}), stage: 'approve', area: run.gate.area, kind: run.gate.kind ?? 'approve', at: run.gate.at, decisions: ['approve', 'changes'] } : null,
    ...(chat?.workspaceId ? { herdr: { session: 'pdd', workspaceId: chat.workspaceId, label: `${String(run.repo).split('/')[1]}#${run.number} ${run.workflow}` } } : {}),
    stageAgent: chat && !failure && !chat.startUnconfirmed ? { kind: run.agent, nativeSessionId: chat.session?.id ?? null, herdrSession: 'pdd', paneId: chat.paneId ?? null } : null,
    links: Array.isArray(run.links) ? run.links : [], controller: null, message: run.message ?? null, cancelled: run.cancelled ?? null };
}

export function writeRun(run, ports = {}) {
  run.journalSeq = (Number.isSafeInteger(run.journalSeq) ? run.journalSeq : 0) + 1;
  run.updatedAt = (ports.now ?? Date.now)();
  Object.assign(run, statusView(run));
  mkdirSync(run.runDir, { recursive: true });
  const temporary = join(run.runDir, `.status.json.${randomBytes(6).toString('hex')}.tmp`);
  writeFileSync(temporary, JSON.stringify(run, null, 2) + '\n', { mode: 0o600 });
  renameSync(temporary, join(run.runDir, 'status.json'));
  try { updateIndex(run, ports); } catch { /* The index only helps selection outside a repository. */ }
  return run;
}

export async function runForWorktree(cwd, ports = {}) {
  const context = await gitContext(cwd, ports);
  return context ? runsIn(context.commonDir).find(run => run.root === context.toplevel) ?? null : null;
}

export async function listRuns({ cwd, cancelled = false }, ports = {}) {
  const context = await gitContext(cwd, ports);
  if (context) return runsIn(context.commonDir, { cancelled });
  return readIndex(ports).map(entry => readRun(entry.runDir)).filter(Boolean);
}

function parseRef(ref) {
  const text = String(ref).trim().replace(/\/$/, '');
  const match = /^#?([1-9][0-9]*)$/.exec(text) ?? /^([^/\s#]+\/[^/\s#]+)#([1-9][0-9]*)$/.exec(text)
    ?? /^https:\/\/github\.com\/([^/]+\/[^/]+)\/issues\/([1-9][0-9]*)$/.exec(text);
  if (!match) return null;
  return match.length === 2 ? { number: Number(match[1]) } : { repo: match[1], number: Number(match[2]) };
}

const choices = runs => runs.map(run => `  ${run.repo}#${run.number} ${run.workflow ?? ''} (${run.state ?? 'unknown'})`).join('\n');

export async function resolveRun(ref, { cwd }, ports = {}) {
  const context = await gitContext(cwd, ports);
  if (ref === undefined || ref === null || ref === '') {
    const runs = context ? runsIn(context.commonDir) : readIndex(ports).map(entry => readRun(entry.runDir)).filter(Boolean);
    const own = context && runs.find(run => run.root === context.toplevel);
    if (own) return { run: own };
    const active = runs.filter(run => !ended(run)), waiting = active.filter(run => run.gate);
    const pick = waiting.length === 1 ? waiting[0] : active.length === 1 ? active[0] : null;
    if (pick) return { run: pick };
    return { error: active.length ? `More than one run is active. Name the issue:\n${choices(active)}` : 'No active pdd run here. Start one with: pdd workflow run NAME ISSUE' };
  }
  const wanted = parseRef(ref);
  if (!wanted) return { error: `"${String(ref).slice(0, 80)}" is not an issue number, owner/repo#N or issue URL.` };
  if (context) {
    const run = readRun(runDirFor(context.commonDir, wanted.number));
    if (run && (!wanted.repo || sameRepo(run.repo, wanted.repo))) return { run };
    if (!wanted.repo) return { error: `This repository has no pdd run for #${wanted.number}. See the runs: pdd workflow status` };
  }
  const entries = readIndex(ports).filter(entry => entry.number === wanted.number && (!wanted.repo || sameRepo(entry.repo, wanted.repo)));
  const repos = [...new Map(entries.map(entry => [String(entry.repo).toLowerCase(), entry])).values()];
  if (repos.length > 1) return { error: `More than one repository has a run for #${wanted.number}. Use owner/repo#${wanted.number}:\n${repos.map(entry => `  ${entry.repo}#${entry.number}`).join('\n')}` };
  if (!repos.length) return { error: `No pdd run found for ${wanted.repo ? `${wanted.repo}#` : '#'}${wanted.number}.` };
  const run = readRun(repos[0].runDir);
  return run ? { run } : { error: `The run record for ${repos[0].repo}#${wanted.number} is missing at ${repos[0].runDir}.` };
}
