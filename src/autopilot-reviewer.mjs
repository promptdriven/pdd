import { autopilotStateFiles, readAutopilotState } from './autopilot-store.mjs';
import { createHash, randomUUID } from 'node:crypto';
import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { runAgentProcess } from './agent-adapters.mjs';
import { githubReply } from './github-calls.mjs';
import { gitContext, stateDirFor } from './workflow-runs.mjs';

const BRANCH = 'pdd/autopilot-reviewer', FILE = '.pdd-reviewer.json';
const LIFE = 90 * 60 * 1000, RENEW = 30 * 60 * 1000;
const pair = (a, b) => !!a && !!b && a.machine === b.machine && a.coordinatorId === b.coordinatorId;
const validIdentity = x => x && ['machine', 'coordinatorId'].every(k => typeof x[k] === 'string' && x[k].trim());
const unknown = () => ({ state: 'unknown', held: false, lease: null });
function validLease(x, repository, now) {
  return x && x.repository === repository && validIdentity(x) && typeof x.login === 'string' && x.login
    && typeof x.generation === 'string' && x.generation && Number.isFinite(Date.parse(x.lastSeen))
    && Date.parse(x.lastSeen) <= now && Date.parse(x.expiresAt) === Date.parse(x.lastSeen) + LIFE;
}
async function api(endpoint, method, body, ports) {
  const args = ['api', '--include', '--method', method, endpoint, ...(body ? ['--input', '-'] : [])];
  let result;
  try { result = await (ports.execFile ?? ((file, args, options) => runAgentProcess(file, args, { ...options, timeoutMs: 10000 })))('gh', args, { cwd: ports.cwd, encoding: 'utf8', timeout: 10000, ...(body ? { input: JSON.stringify(body) } : {}) }); }
  catch (error) { result = error; }
  const reply = githubReply(result.stdout);
  if (!reply) throw Error('Reviewer observation unavailable');
  return { ...reply, value: reply.body ? JSON.parse(reply.body) : null };
}

export async function reviewerIdentity({ cwd, repository }, ports = {}) {
  if (ports.reviewerIdentity) return ports.reviewerIdentity({ cwd, repository });
  const carried = (ports.env ?? process.env).PDD_AUTOPILOT_CONTEXT;
  if (carried) {
    let owner;
    try { owner = JSON.parse(carried); } catch { throw Error('Reviewer identity unavailable'); }
    if (owner.repository?.toLowerCase() !== repository.toLowerCase() || !validIdentity(owner)) throw Error('Reviewer identity unavailable');
    const folder = ports.autopilotStateRoot ?? join(stateDirFor(ports), 'autopilot');
    for (const name of autopilotStateFiles(folder, ports)) {
      const state = readAutopilotState(join(folder, name), null, ports);
      if (!state) continue;
      if (state.repo?.toLowerCase() === repository.toLowerCase() && pair(state, owner) && state.activatedAt === owner.activation)
        return { machine: state.machine, coordinatorId: state.coordinatorId, login: state.reviewerLogin ?? state.githubBot ?? '', enabled: state.enabled === true };
    }
    throw Error('Reviewer identity unavailable');
  }
  const context = await gitContext(cwd, ports);
  if (!context) throw Error('Reviewer identity unavailable');
  const folder = ports.autopilotStateRoot ?? join(stateDirFor(ports), 'autopilot');
  const hash = createHash('sha256').update(context.toplevel).digest('hex').slice(0, 20);
  let state;
  try { state = readAutopilotState(join(folder, `${hash}.json`), null, ports); }
  catch (error) { if (error.code === 'ENOENT') return null; throw Error('Reviewer identity unavailable'); }
  if (!state) return null;
  if (state.repo?.toLowerCase() !== repository.toLowerCase() || state.cwd !== context.toplevel || !validIdentity(state)) throw Error('Reviewer identity unavailable');
  // A stopped coordinator is still managed. It must not fall through to manual authority.
  return { machine: state.machine, coordinatorId: state.coordinatorId, login: state.reviewerLogin ?? state.githubBot ?? '', enabled: state.enabled === true };
}

export async function reviewerLease({ repository, identity, acquire = false }, ports = {}) {
  try {
    if (!/^[\w.-]+\/[\w.-]+$/.test(repository)) return unknown();
    repository = repository.toLowerCase();
    let now = (ports.now ?? Date.now)();
    if (!Number.isFinite(now)) return unknown();
    const endpoint = `repos/${repository}/contents/${FILE}`;
    const observe = async () => {
      const r = await api(`${endpoint}?ref=${encodeURIComponent(BRANCH)}`, 'GET', null, ports);
      now = (ports.now ?? Date.now)();
      if (!Number.isFinite(now)) return unknown();
      if (r.status === 404) return { state: 'absent', held: false, lease: null, sha: null };
      if (r.status !== 200 || typeof r.value?.sha !== 'string' || r.value.encoding !== 'base64') return unknown();
      const lease = JSON.parse(Buffer.from(r.value.content, 'base64').toString('utf8'));
      if (!validLease(lease, repository, now)) return unknown();
      const held = Date.parse(lease.expiresAt) > now && pair(lease, identity);
      return { state: held ? 'held' : 'other', held, lease, sha: r.value.sha };
    };
    const clean = ({ sha, ...result }) => result;
    const mutate = action => {
      const guarded = () => {
        if (ports.githubFloor?.blocked('core')) throw Error('Reviewer reserve blocked');
        return action();
      };
      return ports.admitMutation ? ports.admitMutation(guarded) : guarded();
    };
    const observed = await observe();
    if (!acquire || !validIdentity(identity) || identity.enabled === false || observed.state === 'unknown') return clean(observed);
    if (observed.lease && Date.parse(observed.lease.expiresAt) > now && (!observed.held || now - Date.parse(observed.lease.lastSeen) < RENEW)) return clean(observed);
    if (!observed.lease) {
      const ref = await api(`repos/${repository}/git/ref/heads/${BRANCH}`, 'GET', null, ports);
      if (ref.status === 404) {
        const repo = await api(`repos/${repository}`, 'GET', null, ports);
        if (repo.status !== 200 || !repo.value.default_branch) return unknown();
        const head = await api(`repos/${repository}/git/ref/heads/${encodeURIComponent(repo.value.default_branch)}`, 'GET', null, ports);
        if (head.status !== 200 || !head.value.object?.sha) return unknown();
        const createBranch = () => api(`repos/${repository}/git/refs`, 'POST', { ref: `refs/heads/${BRANCH}`, sha: head.value.object.sha }, ports);
        const made = await mutate(createBranch);
        if (![201, 422, 409].includes(made.status)) return unknown();
      } else if (ref.status !== 200) return unknown();
    }
    let login = identity.login;
    if (!login) { const user = await api('user', 'GET', null, ports); if (user.status !== 200 || !user.value?.login) return unknown(); login = user.value.login; }
    const lease = { repository, machine: identity.machine, coordinatorId: identity.coordinatorId, login,
      generation: observed.held ? observed.lease.generation : (ports.uuid ?? randomUUID)(),
      lastSeen: new Date(now).toISOString(), expiresAt: new Date(now + LIFE).toISOString() };
    const writeLease = () => {
      const admittedAt = (ports.now ?? Date.now)();
      if (!Number.isFinite(admittedAt) || observed.held && Date.parse(observed.lease.expiresAt) <= admittedAt)
        throw Error('Reviewer renewal expired');
      return api(endpoint, 'PUT', { branch: BRANCH, message: 'Renew Autopilot reviewer lease',
        content: Buffer.from(JSON.stringify(lease)).toString('base64'), ...(observed.sha ? { sha: observed.sha } : {}) }, ports);
    };
    const written = await mutate(writeLease);
    if (written.status === 409 || written.status === 422) return clean(await observe());
    if (![200, 201].includes(written.status) || typeof written.value?.content?.sha !== 'string') return unknown();
    if (!(Date.parse(lease.expiresAt) > (ports.now ?? Date.now)())) return { state: 'other', held: false, lease };
    return { state: 'held', held: true, lease };
  } catch { return unknown(); }
}

export function repositoryMachines({ lease, claims = [] }, now = Date.now()) {
  const machines = new Map();
  const add = (record, issue, reviewer = false) => {
    if (!validIdentity(record)) return;
    const key = JSON.stringify([record.machine, record.coordinatorId]);
    const row = machines.get(key) ?? { machine: record.machine, coordinatorId: record.coordinatorId, login: record.login ?? '', issues: [], reviewer: false, lastSeen: '' };
    if (issue && !row.issues.includes(issue)) row.issues.push(issue);
    row.reviewer ||= reviewer;
    if (record.login) row.login = record.login;
    if (Date.parse(record.lastSeen) > (Date.parse(row.lastSeen) || 0)) row.lastSeen = record.lastSeen;
    machines.set(key, row);
  };
  for (const claim of claims) if (claim.active === true) add(claim, claim.issue);
  const reviewer = lease && validLease(lease, lease.repository, now) && Date.parse(lease.expiresAt) > now ? lease : null;
  if (reviewer) add(reviewer, null, true);
  const rows = [...machines.values()].sort((a, b) => a.machine.localeCompare(b.machine) || a.coordinatorId.localeCompare(b.coordinatorId));
  for (const row of rows) row.issues.sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
  const accounts = new Map();
  for (const row of rows) if (row.login) { const login = row.login.toLowerCase(); accounts.set(login, (accounts.get(login) ?? 0) + 1); }
  return { reviewer, machines: rows, sharedLogins: [...accounts].filter(([, n]) => n > 1).map(([login]) => login).sort() };
}

export function repositoryMachineLines(view) {
  return [`Reviewer: ${view.reviewer ? `${view.reviewer.machine} / ${view.reviewer.coordinatorId} (expires ${view.reviewer.expiresAt})` : 'none'}`,
    ...view.machines.map(row => `Machine ${row.machine} / ${row.coordinatorId}: issues ${row.issues.map(url => '#' + url.split('/').at(-1)).join(', ') || 'none'}; login ${row.login || 'unknown'}; last seen ${row.lastSeen || 'unknown'}${row.reviewer ? '; reviewer' : ''}`)].join('\n');
}
