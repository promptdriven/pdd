// Generated from prompts/cli/autopilot-retire.prompt.md (sha256: 93aa7aa7f4bdc5c1dc37a934451f948f9aff35a75245cf916a93b3a3bb32f69e).
import { sep, join } from 'node:path';

// The move of a machine from the removed full engine to the core engine. Each step is idempotent and saved in the
// state's step journal (`retiredFull`), so a failed step goes on at the next tick and a done step never runs again.
export const RETIRED_NOTE = 'Autopilot moved this machine to the core engine; this PR is not worked on. A person can merge or close it.';
const NOTE_MARK = '<!-- pdd:autopilot-retired-full -->';
export const FULL_ENGINE_REMOVED = 'The full Autopilot engine is removed; Autopilot runs only the core engine. Run pdd autopilot start without --engine.';
export const MOVE_STEPS = Object.freeze(['pane', 'runs', 'claims', 'notes', 'slots', 'workers']);
export const MAX_DEFERS = 6;
// Top-level state keys of the full engine. The core never reads them; the move drops them.
const FULL_KEYS = ['acknowledged', 'auditHolds', 'checkCapacity', 'commentCache', 'contextBinding', 'contextPane', 'currentMode',
  'deliveryIntent', 'dependencyPending', 'fullEngineNoticeAt', 'githubIntake', 'health', 'interpreterPattern', 'ownerLaunch', 'paneId',
  'parkedNumbers', 'parking', 'parkingAlerts', 'pullCache', 'recipeDelivered', 'reconciliationIntent', 'relaunchHeld', 'relaunchPending',
  'relaunchTargets', 'retryAt', 'routeQuestions', 'runtime', 'seen', 'timeSeen', 'uncertainDeliveryHistory', 'workspaceId'];
const TERM_WAIT_MS = 5000;
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const named = value => typeof value === 'string' && value.trim().length > 0;
const sameRepo = (a, b) => named(a) && named(b) && a.toLowerCase() === b.toLowerCase();
const ended = run => ['cancelled', 'completed'].includes(run?.state);
const oneLine = value => String(value ?? '').replace(/\s+/g, ' ').trim().slice(0, 300);
const labelsOf = row => (row?.labels ?? []).map(label => typeof label === 'string' ? label : label?.name).filter(Boolean);

// The engine that a saved state ran before 0.1.29: its saved engine, else pdd.json's autopilot.engine, else full.
export function engineBefore(state, repoEngine = null) {
  if (['core', 'full'].includes(state?.engine)) return state.engine;
  return repoEngine === 'core' ? 'core' : 'full';
}
// A saved state has moved when its journal is complete.
export const moved = state => Number.isFinite(state?.retiredFull?.done);

// The saved state after the move: engine core, the journal, and no full-engine key. The coordinator's launch profile
// stays as the core's launch profile, so a later start verifies the same agent sign-in.
export function movedState(state, journal) {
  const next = { ...state, engine: 'core', retiredFull: journal };
  if (next.ownerLaunch?.profile && !next.launchProfile) next.launchProfile = next.ownerLaunch.profile;
  for (const key of FULL_KEYS) delete next[key];
  return next;
}

// GitHub REST through gh with the HTTP status; the same parse as the core's GitHub port.
function github(gh) {
  const call = async (method, endpoint, body) => {
    const r = await gh(['api', '--include', '--method', method, endpoint, ...(body === undefined ? [] : ['--input', '-'])], body === undefined ? {} : { input: JSON.stringify(body) });
    const text = String(r?.stdout ?? ''), cut = text.search(/\r?\n\r?\n/);
    const status = Number(/^HTTP\/\S+\s+(\d+)/.exec(text)?.[1] ?? 0), raw = cut >= 0 ? text.slice(cut).trim() : '';
    let value = null; try { value = raw ? JSON.parse(raw) : null; } catch { /* No JSON body. */ }
    return { status, value, next: /<https:\/\/api\.github\.com\/([^>]+)>;\s*rel="next"/.exec(cut >= 0 ? text.slice(0, cut) : '')?.[1] };
  };
  const ok = async (method, endpoint, body, also = []) => {
    const r = await call(method, endpoint, body);
    if ((r.status < 200 || r.status >= 300) && !also.includes(r.status)) throw Error(`GitHub ${method} ${endpoint.split('?')[0]} returned ${r.status || 'no reply'}`);
    return r;
  };
  const all = async endpoint => {
    const rows = [];
    for (let page = 0; endpoint && page < 20; page++) { const r = await ok('GET', endpoint); if (!Array.isArray(r.value)) throw Error(`GitHub GET ${endpoint.split('?')[0]} returned no list`); rows.push(...r.value); endpoint = r.next; }
    return rows;
  };
  return { call, ok, all };
}

// A claim comment holds one JSON record, in a code block or as the whole body.
export function claimRecord(body) {
  const source = String(body ?? ''), blocks = [...source.matchAll(/```(?:json)?\s*\n([\s\S]*?)\n```/g)].map(m => m[1]);
  blocks.push(source.trim());
  for (const text of blocks) try {
    const value = JSON.parse(text);
    if (object(value) && ['repository', 'coordinatorId', 'machine', 'labelEventId'].every(key => named(value[key]))) return value;
  } catch { /* Not a claim record. */ }
  return null;
}

// The identity of a stoppable old process of this repository, read from its command line, or null.
// A completion worker names its run folder; a coordinator idle helper names this repository's state file.
export function oldProcessOf(args, { runsRoot, stateFile }) {
  const text = String(args ?? '');
  const json = after => { const at = text.indexOf(after); if (at < 0) return null; try { return JSON.parse(text.slice(at + after.length).trim()); } catch { return null; } };
  if (/[\\/]workflow-worker-completion\.mjs /.test(text)) {
    const identity = json('workflow-worker-completion.mjs ');
    return identity && named(identity.runDir) && identity.runDir.startsWith(runsRoot + sep) ? 'worker' : null;
  }
  if (/[\\/]autopilot-launcher\.mjs --coordinator-idle /.test(text)) {
    const identity = json('--coordinator-idle ');
    return identity && identity.stateFile === stateFile ? 'coordinator-idle' : null;
  }
  return null;
}

// The same rows from Linux /proc, for a machine without ps (a small container image): pid, ppid, pgid, rss (KiB), args.
export function procTable(fs, root = '/proc') {
  const rows = [];
  for (const name of fs.readdirSync(root).filter(name => /^\d+$/.test(name))) {
    try {
      const args = fs.readFileSync(`${root}/${name}/cmdline`, 'utf8').split('\0').filter(Boolean).join(' ');
      const stat = fs.readFileSync(`${root}/${name}/stat`, 'utf8'), fields = stat.slice(stat.lastIndexOf(')') + 2).split(' ');
      if (args) rows.push(`${name} ${fields[1]} ${fields[2]} ${Number(fields[21]) * 4} ${args}`);
    } catch { /* The process ended while it was read. */ }
  }
  return rows.join('\n');
}
// ps rows: pid, ppid, pgid, rss (KiB) and the command line.
export function parseProcesses(text) {
  return String(text ?? '').split('\n').map(row => /^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(.*)$/.exec(row)).filter(Boolean)
    .map(m => ({ pid: Number(m[1]), ppid: Number(m[2]), pgid: Number(m[3]), rss: Number(m[4]), args: m[5] }));
}

// Stop the old completion workers and coordinator helpers of this repository: look at each process first, then TERM
// (its whole group when it leads one, so its waits end too), then KILL what is still the same process.
async function stopOldProcesses(ctx) {
  const { ports, self } = ctx, list = async () => parseProcesses(await ports.processes());
  const mine = rows => rows.filter(row => !self.has(row.pid) && oldProcessOf(row.args, ctx.match));
  const found = mine(await list());
  const target = row => row.pgid === row.pid && !self.has(row.pgid) ? -row.pid : row.pid;
  for (const row of found) ports.signal(target(row), 'SIGTERM');
  let left = found;
  for (let waited = 0; left.length && waited < TERM_WAIT_MS; waited += 250) {
    await ports.sleep(250);
    const now = new Map((await list()).map(row => [row.pid, row]));
    left = left.filter(row => now.get(row.pid)?.args === row.args);
  }
  for (const row of left) ports.signal(target(row), 'SIGKILL');
  return { stopped: found.length, killed: left.length, rssKb: found.reduce((sum, row) => sum + row.rss, 0) };
}

// Close the old coordinator chat when Herdr shows that its pane is still this repository's coordinator.
async function closeCoordinator(ctx) {
  const { state, ports } = ctx;
  if (!named(state.paneId)) return { closed: 0, kept: 0 };
  const gone = error => ['agent_not_found', 'pane_not_found', 'server_not_running', 'herdr_missing'].includes(error?.code);
  let agent;
  try { agent = (await ports.herdr(['agent', 'get', state.paneId]))?.result?.agent; }
  catch (error) { if (gone(error)) return { closed: 0, kept: 0 }; throw Error(`Herdr could not read the old coordinator pane (${error?.code ?? 'unavailable'})`); }
  const ours = agent && agent.pane_id === state.paneId && (!state.workspaceId || agent.workspace_id === state.workspaceId)
    && (!agent.cwd || ports.samePath(agent.cwd, state.cwd)) && (!state.agent?.kind || !agent.agent || agent.agent === state.agent.kind);
  if (!ours) return { closed: 0, kept: agent ? 1 : 0 };
  try { await ports.herdr(['pane', 'close', state.paneId]); } catch (error) { if (!gone(error)) throw Error(`Herdr could not close the old coordinator pane (${error?.code ?? 'unavailable'})`); }
  try { await ports.herdr(['pane', 'get', state.paneId]); } catch (error) { if (gone(error)) return { closed: 1, kept: 0 }; throw error; }
  throw Error('the old coordinator pane is still open');
}

// This machine's runs of the full engine in this repository (every coordinator of this machine).
const ownRuns = (runs, state) => runs.filter(run => object(run?.automaticOrigin) && run.automaticOrigin.machine === state.machine
  && sameRepo(run.repo, state.repo));

// A run in the middle of a merge: a PR of a live run is merged, but the run is not completed.
async function mergeStage(ctx) {
  const busy = [];
  for (const run of ownRuns(await ctx.ports.listRuns(), ctx.state).filter(run => !ended(run))) {
    for (const pr of Array.isArray(run.pr) ? run.pr : []) {
      if (!Number.isSafeInteger(Number(pr?.number))) continue;
      const r = await ctx.gh.ok('GET', `repos/${ctx.state.repo}/pulls/${pr.number}`);
      if (r.value?.merged) { busy.push(`run #${run.number} (PR #${pr.number} is merged, the run is not done)`); break; }
    }
  }
  if (named(ctx.state.paneId)) {
    try { const agent = (await ctx.ports.herdr(['agent', 'get', ctx.state.paneId]))?.result?.agent; if (agent?.pane_id === ctx.state.paneId && agent.agent_status === 'working') busy.push('the old coordinator chat (it is working)'); }
    catch { /* A pane that cannot be read is not busy; the pane step decides. */ }
  }
  return busy;
}

async function cancelRuns(ctx, journal) {
  const { state, ports } = ctx, live = ownRuns(await ports.listRuns(), state).filter(run => !ended(run));
  const claims = [], warnings = [];
  for (const run of live) {
    const result = await ports.cancelRun(run);
    if (result?.exitCode !== 0) throw Error(`run #${run.number} could not be cancelled: ${oneLine(result?.message)}`);
    const local = await ports.releaseLocal(run).catch(() => ({ state: 'recovery_required' }));
    if (local?.state !== 'released') warnings.push(`run #${run.number}: the local issue allocation stays`);
    const claim = run.automaticOrigin?.claim;
    if (named(claim?.commentId) && named(claim?.labelEventId)) claims.push({ issue: run.number, commentId: String(claim.commentId), labelEventId: String(claim.labelEventId) });
  }
  journal.claims = [...(journal.claims ?? []), ...claims];
  return { runs: live.length, warnings };
}

// Release the claims of this machine's full engine: its claim comments go; pdd:working goes only when the winning
// label event is this machine's claim. Every other label stays (a person's decision stays).
async function releaseClaims(ctx, journal) {
  const { state, gh, ports } = ctx, repo = state.repo;
  const ours = record => record && record.coordinatorId === state.coordinatorId && record.machine === state.machine;
  const exact = new Map((journal.claims ?? []).map(claim => [String(claim.commentId), claim]));
  const issues = new Set((journal.claims ?? []).map(claim => Number(claim.issue)));
  if (journal.wasFull) {
    for (const claim of Array.isArray(state.githubIntake?.claims) ? state.githubIntake.claims : []) {
      const n = Number(/\/issues\/(\d+)$/.exec(String(claim?.issue ?? ''))?.[1]);
      if (Number.isSafeInteger(n) && claim.machine === state.machine && (claim.coordinatorId ?? claim.owner) === state.coordinatorId) issues.add(n);
    }
    for (const row of await gh.all(`repos/${repo}/issues?state=open&labels=${encodeURIComponent('pdd:working')}&per_page=100`)) if (!row.pull_request) issues.add(row.number);
  }
  const core = ports.coreJobs();
  let released = 0;
  for (const n of [...issues].filter(n => Number.isSafeInteger(n) && !core.has(n)).sort((a, b) => a - b)) {
    const comments = await gh.all(`repos/${repo}/issues/${n}/comments?per_page=100`);
    const mine = comments.filter(c => exact.has(String(c.id)) || ours(claimRecord(c.body)));
    if (!mine.length) continue;
    let winner = null;
    for (const event of await gh.all(`repos/${repo}/issues/${n}/timeline?per_page=100`)) {
      if (event?.label?.name !== 'pdd:working') continue;
      if (event.event === 'unlabeled') winner = null; else if (event.event === 'labeled' && !winner) winner = event;
    }
    const winning = winner ? comments.filter(c => String(claimRecord(c.body)?.labelEventId) === String(winner.id)) : [];
    const ownLabel = winning.length > 0 && winning.every(c => mine.includes(c));
    for (const c of mine) await gh.ok('DELETE', `repos/${repo}/issues/comments/${c.id}`, undefined, [404]);
    if (ownLabel) {
      const issue = (await gh.ok('GET', `repos/${repo}/issues/${n}`)).value;
      if (labelsOf(issue).includes('pdd:working')) await gh.ok('DELETE', `repos/${repo}/issues/${n}/labels/${encodeURIComponent('pdd:working')}`, undefined, [404]);
    }
    released++;
  }
  return { claims: released };
}

// One note on each open PR of this machine's old runs, never twice (a hidden marker).
async function notePrs(ctx) {
  const { state, gh, ports } = ctx, numbers = new Set();
  for (const run of ownRuns(await ports.listRuns(true), state).filter(run => run.state !== 'completed'))
    for (const pr of Array.isArray(run.pr) ? run.pr : []) if (Number.isSafeInteger(Number(pr?.number))) numbers.add(Number(pr.number));
  let notes = 0;
  for (const n of [...numbers].sort((a, b) => a - b)) {
    const pr = (await gh.ok('GET', `repos/${state.repo}/pulls/${n}`, undefined, [404])).value;
    if (pr?.state !== 'open') continue;
    if ((await gh.all(`repos/${state.repo}/issues/${n}/comments?per_page=100`)).some(c => String(c.body ?? '').includes(NOTE_MARK))) continue;
    await gh.ok('POST', `repos/${state.repo}/issues/${n}/comments`, { body: `${RETIRED_NOTE}\n\n${NOTE_MARK}` });
    notes++;
  }
  return { notes };
}

// The words of the one line that the move prints.
export function moveLine(state, journal) {
  const c = journal.counts ?? {}, mb = Math.round((c.rssKb ?? 0) / 1024);
  return `Autopilot moved this machine to the core engine for ${state.repo}: closed ${c.panes ?? 0} coordinator chat(s), cancelled ${c.runs ?? 0} old run(s), released ${c.claims ?? 0} claim(s), left ${c.notes ?? 0} PR note(s), stopped ${c.workers ?? 0} old worker process(es) (${mb} MB)${journal.forced?.length ? `; it waited ${journal.defers} tick(s) for ${journal.forced.join(', ')}` : ''}.`;
}

// One step of the move per call site; returns {done, message}. `save(journal)` keeps the journal in the state file.
export async function moveToCore({ state, stateFile, repoEngine = null }, ports) {
  const now = ports.now ?? Date.now;
  const journal = object(state.retiredFull) ? structuredClone(state.retiredFull) : {};
  journal.startedAt ??= now();
  journal.wasFull ??= engineBefore(state, repoEngine) === 'full';
  journal.steps ??= {}; journal.counts ??= {}; journal.defers ??= 0;
  if (moved({ retiredFull: journal })) return { done: true, journal, message: '' };
  const ctx = { state, ports, gh: github(ports.gh), self: new Set([process.pid, process.ppid]),
    match: { runsRoot: join(ports.commonDir ?? '/nonexistent', 'pdd', 'runs'), stateFile } };
  const save = () => ports.save(journal);
  // A run in a merge, or a busy coordinator chat, holds the move for up to 6 ticks; then it moves with the reason.
  if (journal.wasFull && !Object.keys(journal.steps).length) {
    let busy = [];
    try { busy = await mergeStage(ctx); } catch (error) { journal.lastError = oneLine(error.message); save(); return { done: false, journal, message: `Autopilot waits to move this machine to the core engine: ${journal.lastError}; the next tick retries.` }; }
    if (busy.length && journal.defers < MAX_DEFERS) {
      journal.defers++; save();
      return { done: false, journal, message: `Autopilot waits to move this machine to the core engine: ${busy.join(', ')} (tick ${journal.defers} of ${MAX_DEFERS}); no new work starts.` };
    }
    if (busy.length) journal.forced = busy;
  }
  const run = {
    pane: async () => { const r = await closeCoordinator(ctx); journal.counts.panes = r.closed; journal.counts.keptPanes = r.kept; },
    runs: async () => { const r = await cancelRuns(ctx, journal); journal.counts.runs = r.runs; if (r.warnings.length) journal.warnings = r.warnings; },
    claims: async () => { journal.counts.claims = (await releaseClaims(ctx, journal)).claims; },
    notes: async () => { journal.counts.notes = (await notePrs(ctx)).notes; },
    slots: async () => { journal.counts.slots = (await ports.releaseSlots()) ? 1 : 0; },
    workers: async () => { const r = await stopOldProcesses(ctx); journal.counts.workers = r.stopped; journal.counts.killed = r.killed; journal.counts.rssKb = r.rssKb; },
  };
  for (const step of MOVE_STEPS) {
    if (journal.steps[step]) continue;
    try { await run[step](); }
    catch (error) { journal.lastError = `${step}: ${oneLine(error.message)}`; save(); return { done: false, journal, message: `Autopilot could not finish the move to the core engine (${journal.lastError}); the next tick goes on from this step. No new work starts.` }; }
    journal.steps[step] = now(); delete journal.lastError; save();
  }
  journal.done = now();
  const quiet = !journal.wasFull && !['panes', 'runs', 'claims', 'notes', 'workers'].some(key => journal.counts[key]);
  return { done: true, journal, message: quiet ? '' : moveLine(state, journal) };
}
