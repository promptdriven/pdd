import {runAutopilotDoctor, resolveAutopilotAgent} from './autopilot-doctor.mjs';
import { loadAgentDefinitions } from './agent-config.mjs';
import {releaseRunClaim, cancelRun, acquireRunLock} from './workflow-runner.mjs';
import { releaseCheckCapacity } from './test-suite-queue.mjs';
import { readCodexLimits } from './codex-limits.mjs';
import { loadLoginPool, selectPoolLogin, markLoginExhausted, clearPoolCooldowns, loginEnvironment } from './login-pool.mjs';
import { spawn, execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { createHash, randomUUID } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, readdirSync, statSync, writeFileSync, renameSync, unlinkSync, linkSync, watch, realpathSync } from 'node:fs';
import { homedir, hostname } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runAgentProcess } from './agent-adapters.mjs';
import { pathDiagnostic } from './path-diagnostic.mjs';
import { runAutopilot } from './autopilot.mjs';
import { allRuns, updateRunCosts, listRuns, resolveRun } from './workflow-runs.mjs';
import { auditMerge } from './autopilot-audit.mjs';
import { releaseIssueClaim } from './workflow-worktree.mjs';
import { samePath } from './workflow-herdr-layout.mjs';
import { alertStatusLine, runAutopilotAlerts } from './autopilot-alerts.mjs';
import { countGithubCalls, githubBudget, githubBudgetSettings, githubEtagCache, githubFullLastPage, githubLedger, githubMachineEntries, githubReply, githubStateRoot, githubUsage } from './github-calls.mjs';
import { costReport, costStatusLines } from './cost-ledger.mjs';
import { selectAutopilotBase, checkAutopilotBase } from './autopilot-base.mjs';
import { readCoreSettings, tickCore, coreStatus, busySlots } from './autopilot-core.mjs';
import { readMachineGuard, timerPriority, validShare } from './machine-guard.mjs';
import { listReportDrafts, sendReportDraft } from './autopilot-reports.mjs';
import { INTAKE_MODES, intakeMode, readIntake, intakeText, stopCardJobs } from './autopilot-intake.mjs';
import { moveToCore, moved, movedState, engineBefore, procTable, MAX_DEFERS, FULL_ENGINE_REMOVED } from './autopilot-retire.mjs';
import * as nativeFs from 'node:fs';

const validAutoUpdateMode = mode => ['release', 'main', 'off'].includes(mode);

const INTERVAL = 30 * 60 * 1000;
// The core tick has no AI call and each job phase needs a tick, so the core engine's timer fires every 10 minutes.
const CORE_INTERVAL = 10 * 60 * 1000;
// The issue list reads only changed issues; the whole open list is read again after this time.
const FULL_ISSUE_LIST_EVERY = 6 * 60 * 60 * 1000;
// The Herdr session of the removed full engine's coordinator chat; only the move reads it.
const COORDINATOR_SESSION = 'pdd-autopilot';
const self = fileURLToPath(import.meta.url);
const line = value => String(value).split(/[\r\n]/)[0].replace(/[\x00-\x1f\x7f]/g, ' ');
const read = (file, fallback = null) => { try { return JSON.parse(readFileSync(file, 'utf8')); } catch (e) { if (e.code === 'ENOENT') return fallback; throw e; } };
function save(file, value) {
  mkdirSync(dirname(file), { recursive: true, mode: 0o700 });
  const temp = `${file}.${randomUUID()}.tmp`;
  try { writeFileSync(temp, JSON.stringify(value), { mode: 0o600 }); renameSync(temp, file); }
  finally { try { unlinkSync(temp); } catch (e) { if (e.code !== 'ENOENT') throw e; } }
}
async function settings(state, p) {
  const result = await runAutopilot({ action: 'setup', interactive: false, inRepo: true }, {
    cwd: state.cwd,
    execFile: async (command, args) => ({ stdout: await p.checked(command, args) }),
  });
  if (result.exitCode !== 0) throw Error(result.message);
  return result;
}
async function automaticBase(state, p) {
  if (!state.defaultBranch) {
    const repo = JSON.parse(await p.checked('gh', ['repo', 'view', '--json', 'nameWithOwner,defaultBranchRef']));
    if (state.repo && state.repo.toLowerCase() !== repo.nameWithOwner?.toLowerCase()) throw Error('Automatic base repository does not match.');
    state.repo = repo.nameWithOwner;
    state.defaultBranch = repo.defaultBranchRef?.name;
  }
  state.baseBranch = await selectAutopilotBase({ cwd: state.cwd, defaultBranch: state.defaultBranch }, {
    execFile: async (file, args) => ({ stdout: await p.checked(file, args) }),
    ...(p.readConfig ? { readConfig: p.readConfig } : {}),
  });
}
const ok = message => ({ exitCode: 0, message });
const bad = message => ({ exitCode: 1, message: line(message) });
function portsFor(state, ports) {
  const env = { ...process.env, ...state?.environment, ...ports.env };
  const run = ports.run ?? runAgentProcess, now = ports.now ?? Date.now;
  // Each gh call goes to this repository's GitHub ledger on this machine; options.purpose names its purpose.
  // The ledgers sit beside the launcher state files.
  const githubRoot = ports.githubRoot ?? (typeof state?.stateFile === 'string' ? dirname(state.stateFile) : githubStateRoot(env, ports.stateRoot)), ledgers = new Map();
  const ledger = () => { const repo = state?.repo; if (typeof repo !== 'string' || !repo) return null; if (!ledgers.has(repo)) ledgers.set(repo, githubLedger({ root: githubRoot, repository: repo })); return ledgers.get(repo); };
  const execute = countGithubCalls(async (command, args, options = {}) => run(command, args, { cwd: state.cwd, env, timeoutMs: 10000, maxBytes: 8 * 1024 * 1024, ...options }), { ledger, now });
  const checked = async (command, args, options) => { const result = await execute(command, args, options); if (result.code !== 0) throw Error(`${command} failed; check its sign-in and retry.`); return result.stdout; };
  return { ...ports, env, run, execute, checked, githubRoot, warn: ports.warn ?? (text => process.stderr.write(`${text}\n`)), now };
}
const AGENT_KINDS = ['codex', 'claude', 'gemini', 'agy'];
const AGENT_CONFIG_VARS = { codex: 'CODEX_HOME', claude: 'CLAUDE_CONFIG_DIR', gemini: 'GEMINI_CLI_HOME', agy: 'ANTIGRAVITY_APP_DATA_DIR' };
const keepEnv = env => Object.fromEntries(['HOME', 'PATH', 'CODEX_HOME', 'CLAUDE_CONFIG_DIR', 'GEMINI_CLI_HOME', 'ANTIGRAVITY_APP_DATA_DIR', 'XDG_CONFIG_HOME', 'XDG_RUNTIME_DIR', 'DBUS_SESSION_BUS_ADDRESS', 'PDD_SUITE_QUEUE', 'PDD_VM_SUITE_LOCK'].filter(k => typeof env[k] === 'string').map(k => [k, env[k]]));
function explicitConfigOverride(previous, env) {
  const kind = previous?.agent?.kind, variable = kind ? AGENT_CONFIG_VARS[kind] : null;
  if (!variable || typeof env?.[variable] !== 'string' || !env[variable].trim()) return false;
  return env[variable] !== (previous?.environment?.[variable] || null);
}
function describeProfile(agent, env) {
  if (!agent) return 'none';
  const variable = AGENT_CONFIG_VARS[agent.kind], folder = variable ? env?.[variable] : null;
  return folder ? `${agent.id} (${folder})` : String(agent.id ?? agent.kind);
}
const NOT_GIT = 'This folder is not a Git repository. cd into the repo you want Autopilot to work on, then run the command again.';
// Git translates its messages; pdd reads the "not a git repository" text only in the C locale.
const gitRootIn = p => p.execute('git', ['rev-parse', '--show-toplevel'], { env: { ...p.env, LC_ALL: 'C', LANG: 'C' } });
const stateFolder = (ports, env) => ports.stateRoot ?? join(env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
async function gitRoot(p) {
  const result = await gitRootIn(p);
  if (result.code === 0 && result.stdout.trim()) return result.stdout.trim();
  throw Object.assign(Error(/not a git repository/i.test(result.stderr ?? '') ? NOT_GIT : 'Autopilot could not read this Git repository; retry.'), { exact: true });
}
// Read-only: can `pdd workflow run` make an issue worktree in this checkout? The allocator alone decides;
async function selectAgent(state, p, saved = null) {
  const selected = await resolveAutopilotAgent({cwd:state.cwd,env:p.env,profile:saved}, {
    ...p, run:(command,args,options)=>p.execute(command,args,options), selectAgent:undefined,
  });
  if (selected.configurationError) throw selected.configurationError;
  return selected.agent;
}
function xml(value) { return String(value).replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;').replaceAll("'", '&apos;'); }
// Timers execute this file directly. Neither platform needs a shell or a daemon owned by pdd.
async function userTimer(action, state, p) {
  const platform = p.platform ?? process.platform, minutes = intervalOf(state) / 60000;
  const name = `pdd-autopilot-${state.id}`;
  const home = p.env.HOME || homedir();
  if (platform === 'darwin') {
    const folder = join(home, 'Library', 'LaunchAgents'), file = join(folder, `${name}.plist`);
    const domain = `gui/${p.uid ?? process.getuid()}`;
    if (action === 'status') return (await p.execute('launchctl', ['print', `${domain}/${name}`])).code === 0;
    if (action === 'stop') { if ((await p.execute('launchctl', ['print', `${domain}/${name}`])).code === 0) await p.checked('launchctl', ['bootout', `${domain}/${name}`]); try { unlinkSync(file); } catch (e) { if (e.code !== 'ENOENT') throw e; } return false; }
    mkdirSync(folder, { recursive: true });
    const args = [process.execPath, self, state.stateFile].map(x => `<string>${xml(x)}</string>`).join('');
    const vars = Object.entries(state.environment).map(([k, v]) => `<key>${xml(k)}</key><string>${xml(v)}</string>`).join('');
    writeFileSync(file, `<?xml version="1.0" encoding="UTF-8"?><!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd"><plist version="1.0"><dict><key>Label</key><string>${name}</string><key>ProgramArguments</key><array>${args}</array><key>EnvironmentVariables</key><dict>${vars}</dict><key>StartInterval</key><integer>${minutes * 60}</integer>${timerPriority('darwin').plist}<key>StandardErrorPath</key><string>${xml(state.stateFile + '.log')}</string></dict></plist>`, { mode: 0o600 });
    await p.execute('launchctl', ['bootout', `${domain}/${name}`]);
    await p.checked('launchctl', ['bootstrap', domain, file]);
    return true;
  }
  if (platform !== 'linux') throw Error('Autopilot user timers need macOS or Linux.');
  const folder = join(p.env.XDG_CONFIG_HOME || join(home, '.config'), 'systemd', 'user');
  if (action === 'status') return (await p.execute('systemctl', ['--user', 'is-active', `${name}.timer`])).code === 0;
  if (action === 'stop') {
    if ((await p.execute('systemctl', ['--user', 'is-active', `${name}.timer`])).code === 0) await p.checked('systemctl', ['--user', 'stop', `${name}.timer`]);
    if (existsSync(join(folder, `${name}.timer`))) await p.checked('systemctl', ['--user', 'disable', `${name}.timer`]);
    for (const suffix of ['timer', 'service']) { try { unlinkSync(join(folder, `${name}.${suffix}`)); } catch (e) { if (e.code !== 'ENOENT') throw e; } }
    await p.checked('systemctl', ['--user', 'daemon-reload']); return false;
  }
  mkdirSync(folder, { recursive: true });
  const unit = value => JSON.stringify(String(value).replaceAll('%', '%%'));
  // #3231: Linux shares CPU between cgroups by weight before nice counts; the detached jobs stay in this cgroup.
  writeFileSync(join(folder, `${name}.service`), `[Unit]\nDescription=PDD Autopilot tick\n[Service]\nType=oneshot\nKillMode=process\n${timerPriority('linux', state.share).unit}ExecStart=${[process.execPath, self, state.stateFile].map(unit).join(' ')}\n${Object.entries(state.environment).map(([k, v]) => `Environment=${unit(k + '=' + v)}\n`).join('')}`, { mode: 0o600 });
  writeFileSync(join(folder, `${name}.timer`), `[Unit]\nDescription=PDD Autopilot every ${minutes} minutes\n[Timer]\nOnActiveSec=${minutes}min\nOnUnitActiveSec=${minutes}min\nAccuracySec=1s\n[Install]\nWantedBy=timers.target\n`, { mode: 0o600 });
  await p.checked('systemctl', ['--user', 'daemon-reload']);
  await p.checked('systemctl', ['--user', 'enable', `${name}.timer`]);
  await p.checked('systemctl', ['--user', 'restart', `${name}.timer`]);
  return true;
}
async function timer(action, state, p) { return p.timer ? p.timer(action, state) : userTimer(action, state, p); }
function response(text) {
  const boundary = text.search(/\r?\n\r?\n/);
  if (boundary < 0) throw Error('GitHub returned no HTTP headers.');
  const headers = text.slice(0, boundary), body = text.slice(boundary).trim();
  const header = name => headers.match(new RegExp(`^${name}:\\s*(.+)$`, 'im'))?.[1]?.trim();
  const status = Number(headers.match(/^HTTP\/\S+\s+(\d+)/)?.[1]);
  const rateLimited = status === 429 || status === 403 && (header('x-ratelimit-remaining') === '0' || /rate.?limit/i.test(body));
  return { status, etag: header('etag'), link: header('link'), resetAt: Number(header('x-ratelimit-reset')) * 1000, rateLimited, body };
}
// Each page is a conditional request with its saved ETag; a 304 reuses the saved page.
async function issuePages(endpoint, state, p) {
  const rows = [], pages = {}; let first = true, etag, changed = false;
  while (endpoint) {
    if (p.githubFloor?.blocked('core')) return { reserveBlocked: true };
    const old = state.pages?.[endpoint];
    const args = ['api', '--include', '--method', 'GET', endpoint];
    if (old?.etag) args.push('-H', `If-None-Match: ${old.etag}`);
    const r = response((await p.execute('gh', args, { purpose: 'issues' })).stdout);
    if (r.rateLimited) return { status: r.status, rateLimited: true, resetAt: r.resetAt || p.now() + INTERVAL };
    let page;
    if (r.status === 304 && old) page = old;
    else {
      if (r.status !== 200) throw Error('GitHub issue check failed; check gh auth status.');
      const list = JSON.parse(r.body); if (!Array.isArray(list)) throw Error('GitHub returned no issue list.');
      page = { etag: r.etag, rows: list, next: r.link?.match(/<https:\/\/api\.github\.com\/([^>]+)>; rel="next"/)?.[1] }; changed = true;
    }
    if (first) { etag = page.etag; first = false; }
    pages[endpoint] = page; rows.push(...page.rows); endpoint = page.next;
  }
  return { status: 200, etag, rows, pages, changed };
}
const newestUpdate = rows => rows.map(row => row?.updated_at).filter(value => typeof value === 'string' && Number.isFinite(Date.parse(value))).sort((a, b) => Date.parse(b) - Date.parse(a))[0];
async function queryIssues(state, p) {
  // A list of more than one page is read in full only every 6 hours. Between, the tick reads the issues and PRs
  // changed since the newest update of that full read (open and closed) and applies them to the cached open list:
  // a closed row leaves it. The URL stays the same until the next full read, so an unchanged list is a 304.
  const fullPages = Object.keys(state.pages ?? {}).filter(key => !key.includes('&since=')).length;
  if (fullPages > 1 && typeof state.issuesSince === 'string' && Array.isArray(state.cachedIssues) && Number.isFinite(state.issuesFullAt) && p.now() - state.issuesFullAt < FULL_ISSUE_LIST_EVERY) {
    const read = await issuePages(`repos/${state.repo}/issues?state=all&sort=updated&direction=desc&since=${encodeURIComponent(state.issuesSince)}&per_page=100`, state, p);
    if (read.rateLimited || read.reserveBlocked) return read;
    const pages = { ...Object.fromEntries(Object.entries(state.pages).filter(([key]) => !key.includes('&since='))), ...read.pages };
    if (!read.changed) return { status: 304, pages };
    const byNumber = new Map(state.cachedIssues.map(row => [row.number, row]));
    for (const row of read.rows) { if (row?.state === 'open') byNumber.set(row.number, row); else byNumber.delete(row?.number); }
    const issues = [...byNumber.values()].sort((a, b) => (Date.parse(b.updated_at) || 0) - (Date.parse(a.updated_at) || 0));
    return { status: 200, etag: state.etag, issues, pages };
  }
  const read = await issuePages(`repos/${state.repo}/issues?state=open&sort=updated&direction=desc&per_page=100`, state, p);
  if (read.rateLimited || read.reserveBlocked) return read;
  return { status: 200, etag: read.etag, issues: read.rows, pages: read.pages, since: newestUpdate(read.rows), fullAt: p.now() };
}
// A GET of the tick. With an explicit ETag the caller keeps the page. Without one, the tick's ETag cache (p.etags) makes
// the read conditional, except for a full last page; a 304 then returns the saved body and next page.
async function githubGet(endpoint, p, etag, safety = false) {
  if (!safety && p.githubFloor?.blocked('core')) throw Error('GitHub limit is below the floor; retry after reset.');
  const saved = etag === undefined ? p.etags?.get(endpoint) : undefined;
  let cached;
  if (saved) try { cached = { value: JSON.parse(saved.body), next: saved.next ?? '' }; if (githubFullLastPage(endpoint, cached.value, cached.next)) cached = undefined; } catch { cached = undefined; }
  const tag = etag ?? (cached ? saved.etag : undefined);
  const args = ['api', '--include', '--method', 'GET', endpoint];
  if (tag) args.push('-H', `If-None-Match: ${tag}`);
  const result = await p.execute('gh', args);
  p.githubFloor?.observe(githubReply(result.stdout));
  const r = response(result.stdout);
  if (r.rateLimited) throw Object.assign(Error('GitHub rate limited; waiting until reset.'), { resetAt: r.resetAt || p.now() + INTERVAL });
  if (r.status === 304 && etag) return r;
  if (r.status === 304 && cached) return { ...r, status: 200, value: cached.value, link: cached.next ? `<https://api.github.com/${cached.next}>; rel="next"` : undefined };
  if (r.status === 404) return { ...r, value: null };
  if (r.status !== 200) throw Error('GitHub lookup unavailable; eligible work will be retried next tick.');
  const value = JSON.parse(r.body);
  if (etag === undefined && r.etag) p.etags?.set(endpoint, { etag: r.etag, body: r.body, next: r.link?.match(/<https:\/\/api\.github\.com\/([^>]+)>; rel="next"/)?.[1] ?? '' });
  return { ...r, value };
}
async function trusted(row, state, config, p) {
  const login = row.user?.login;
  if (!login) return false;
  if ([state.repo.split('/')[0], ...config.trust].some(name => name.toLowerCase() === login.toLowerCase())) return true;
  p.permissions ??= new Map();
  if (!p.permissions.has(login)) {
    const result = await githubGet(`repos/${state.repo}/collaborators/${encodeURIComponent(login)}/permission`, p, undefined, true);
    p.permissions.set(login, ['admin', 'maintain', 'write'].includes(result.value?.permission));
  }
  return p.permissions.get(login);
}
// A trusted claim comment that carries a lastSeen heartbeat.
function profileBinding(state, p) {
  const variable = AGENT_CONFIG_VARS[state.agent.kind];
  return {
    agent: { id: state.agent.id, kind: state.agent.kind },
    home: state.environment?.HOME ?? p.env.HOME ?? null,
    definitionHome: state.definitionHome ?? state.environment?.HOME ?? p.env.HOME ?? null,
    configHome: variable ? state.environment?.[variable] || null : null,
  };
}
function clearPauseState(stateFile) {
  const root = coreRoot(stateFile);
  clearPoolCooldowns({ stateRoot: root });
  const coreFile = join(root, 'core.json'), current = read(coreFile);
  if (current && typeof current === 'object' && !Array.isArray(current)) {
    delete current.pausedUntil; delete current.pausedHours; delete current.poolOut;
    current.streak = 0; current.hours = 1;
    save(coreFile, current);
  }
}
function claimTickLock(file) {
  const owner = `${file}.${randomUUID()}.owner`;
  writeFileSync(owner, String(process.pid), { flag: 'wx', mode: 0o600 });
  try {
    for (;;) {
      try { linkSync(owner, file); return true; }
      catch (e) { if (e.code !== 'EEXIST') throw e; }
      let text;
      try { text = readFileSync(file, 'utf8'); } catch (e) { if (e.code === 'ENOENT') continue; throw e; }
      const pid = Number(text);
      if (/^[1-9][0-9]*$/.test(text) && Number.isSafeInteger(pid)) {
        try { process.kill(pid, 0); return false; }
        catch (e) { if (e.code !== 'ESRCH' && !(e instanceof RangeError)) return false; }
      }
      // A new lock is linked only after its owner is complete; an empty file is stale.
      try { if (readFileSync(file, 'utf8') === text) unlinkSync(file); }
      catch (e) { if (e.code !== 'ENOENT') throw e; }
    }
  } finally { unlinkSync(owner); }
}
function lockWait(p) {
  const elapsed = p.elapsedNow ?? (() => Number(process.hrtime.bigint() / 1_000_000n));
  return { elapsed, began: elapsed(), sleep: p.sleep ?? (ms => new Promise(resolve => setTimeout(resolve, ms))), warned: false };
}
async function waitForLock(attempt, p, wait) {
  for (;;) {
    if (wait.elapsed() - wait.began >= 5000) return null;
    try { const release = attempt(); if (release) return release; }
    catch (error) { if (error.code !== 'run_busy') throw error; }
    if (!wait.warned) { p.warn('Waiting for the current Autopilot operation to finish...'); wait.warned = true; }
    const remaining = 5000 - Math.max(0, wait.elapsed() - wait.began);
    if (remaining <= 0) return null;
    await wait.sleep(Math.min(100, remaining));
    if (wait.elapsed() - wait.began >= 5000) return null;
  }
}
async function admissionDirectory(state, p) {
  const common = (await p.checked('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'])).trim();
  const dir = resolve(state.cwd, common, 'pdd'); mkdirSync(dir, { recursive: true }); return dir;
}
async function claimAdmission(state, p, wait = lockWait(p)) {
  const dir = await admissionDirectory(state, p);
  return waitForLock(() => acquireRunLock(dir, 'autopilot-admission.lock'), p, wait);
}
async function claimMachineAdmission(stateFile, p, wait = lockWait(p)) {
  const dir = dirname(stateFile);
  return waitForLock(() => acquireRunLock(dir, 'autopilot-machine-admission.lock'), p, wait);
}

export async function tickAutopilot(stateFile, ports = {}) { return runTick(stateFile, ports); }

function workflowCleanupPorts(p, ports) {
  return {...p, execFile: p.execFile ?? (async (file, args, options) => {
    const result = await p.execute(file, args, options);
    if (result.code !== 0) throw Object.assign(Error(`${file} failed`), result);
    return result;
  }), herdr: ports.workflowHerdr ?? ports.herdr ?? (async args => {
    const result = await p.execute('herdr', ['--session','pdd',...args]);
    if (result.code === 0 && args[0] === 'pane' && args[1] === 'read') return result.stdout;
    let reply; try { reply = JSON.parse(result.code === 0 ? result.stdout : result.stderr || result.stdout); } catch {}
    if (result.code !== 0 || reply?.error) throw Object.assign(Error('Workflow Herdr inventory unavailable'), {code:reply?.error?.code ?? 'herdr_failed'});
    return reply;
  })};
}
// Autopilot has one engine, the core: headless jobs with no coordinator chat, Herdr, parking or AI scheduling.
// pdd.json's autopilot.engine when it names one, else null. Only the move of a machine from the removed full engine
// reads it, to know which engine the machine ran before.
const engineAt = cwd => { try { const engine = JSON.parse(readFileSync(join(cwd, 'pdd.json'), 'utf8'))?.autopilot?.engine; return ['core', 'full'].includes(engine) ? engine : null; } catch { return null; } };
// The core timer fires every 10 minutes. Start writes the interval into the timer; a tick never reloads its own timer.
const intervalOf = () => CORE_INTERVAL;
// The installed timer's interval in minutes; a timer installed before this was saved fires every 30 minutes.
const timerMinutes = state => Number.isSafeInteger(state?.timerMinutes) && state.timerMinutes > 0 ? state.timerMinutes : INTERVAL / 60000;
function timerLine(state, active) {
  if (!active) return 'inactive';
  const installed = timerMinutes(state), wanted = intervalOf(state) / 60000;
  return `active, every ${installed} minutes${installed === wanted ? '' : ` (run pdd autopilot start to use ${wanted} minutes)`}`;
}
const machineLabel = state => typeof state?.label === 'string' && state.label.trim() ? state.label.trim() : null;
// The machine's saved core mode (pdd autopilot start --mode) wins over pdd.json for the core engine.
const machineMode = state => ['auto', 'observe', 'off'].includes(state?.mode) ? state.mode : null;
// The machine's saved core report mode (pdd autopilot start --report) wins over pdd.json for the core engine.
const machineReport = state => ['file', 'draft', 'off'].includes(state?.report) ? state.report : null;
// The machine's saved core decision mode (pdd autopilot start --decisions) wins over pdd.json for the core engine.
const machineDecisions = state => ['ask', 'decide'].includes(state?.decisions) ? state.decisions : null;
// The machine's intake mode (pdd autopilot start --intake): active selects from ready cards, shadow writes cards only, off writes none.
const savedIntake = state => INTAKE_MODES.includes(state?.intake) ? state.intake : null;
const effectiveIntake = (state, core = null) => savedIntake(state) ?? intakeMode(core?.intake);
// A start with no opt-in label (the machine's --label or pdd.json autopilot.label) asks for one and starts nothing unless intake is active.
const NO_LABEL = 'Autopilot did not start: it works only on the issues that you mark with an opt-in label. Run pdd autopilot start --label pdd:autopilot, then mark issues with pdd autopilot add N (or add the label on GitHub). Nothing was started or claimed.';
// The status line of the move from the full engine: pending or waiting, or done in the last 7 days.
function moveStatus(state, now) {
  if (!state) return '';
  const journal = state.retiredFull;
  if (moved(state)) return journal.line && now - journal.done < 7 * 24 * 60 * 60 * 1000 ? `\nMoved from the full engine at ${new Date(journal.done).toISOString()}: ${line(journal.line)}` : '';
  if (engineBefore(state, engineAt(state.cwd)) !== 'full') return '';
  return `\nThis machine moves from the full engine to the core engine at its next tick${journal?.lastError ? ` (last try: ${line(journal.lastError)})` : journal?.defers ? ` (it waited ${journal.defers} of ${MAX_DEFERS} ticks)` : ''}; no new work starts before that.`;
}
// The status line of an alert that was not delivered, from local files only; an error adds nothing.
function alertLine(state, p, ports) {
  try { const text = (ports.alertStatusLine ?? alertStatusLine)({ repo: state.repo, env: p.env }, { stateRoot: ports.stateRoot }); return text ? `\n${text}` : ''; }
  catch { return ''; }
}
async function updateLine(stateFile, ports) {
  try {
    const stateRoot = dirname(stateFile);
    if (!ports.autoUpdateStatusLine && !existsSync(join(stateRoot, 'autopilot-update.json'))) return '';
    const render = ports.autoUpdateStatusLine ?? (await import('./autopilot-update.mjs')).autoUpdateStatusLine;
    const text = render({ stateRoot });
    return text ? `\n${text}` : '';
  } catch { return ''; }
}
const coreRoot = stateFile => stateFile.replace(/\.json$/, '-core');
const coreReports = (ports, env) => join(stateFolder(ports, env), 'core-reports');
// #3231: the machine guard reads this machine once: Autopilot's share of it (start --share, default 50%), the slots
// (this machine's --runs wins), the room for new work and the priority of each job.
async function coreGuard(state, p, ports, stateFile) {
  const repoRuns = read(join(state.cwd, 'pdd.json'), {})?.autopilot?.runs;
  return (ports.machineGuard ?? readMachineGuard)({ cwd: state.cwd, runs: state.runs, repoRuns, share: state.share, jobs: machineJobs(stateFile) }, { env: p.env });
}
// The jobs that hold a slot now in every enabled repository of this machine (the core folders beside the state files).
function machineJobs(stateFile) {
  const folder = dirname(stateFile);
  let names = [];
  try { names = readdirSync(folder); } catch { return 0; }
  return names.filter(name => name.endsWith('.json') && read(join(folder, name), null)?.enabled === true)
    .reduce((sum, name) => sum + busySlots(coreRoot(join(folder, name))), 0);
}
// pdd autopilot start --share N: the percent of this machine's CPU and memory that Autopilot may use, saved for this
// repository on this machine; a later start without it keeps it.
function shareOption(command, input, state) {
  if (command !== 'start' || input.share === undefined) return null;
  const value = Number(input.share);
  if (!/^[0-9]+$/.test(String(input.share)) || !validShare(value)) return { exitCode: 2, message: 'Use --share with a whole percent from 1 to 100, for example --share 70 (the default is 50).' };
  if (state) state.share = value;
  return null;
}
async function coreTick(stateFile, state, p, ports) {
  return runCoreTick(stateFile, state, p, ports);
}
async function runCoreTick(stateFile, state, p, ports) {
  const guard = await coreGuard(state, p, ports, stateFile);
  const machine = { ...guard };
  const reserveMachine = async () => {
    const release = await claimMachineAdmission(stateFile, p);
    if (!release) return null;
    try { Object.assign(machine, await coreGuard(state, p, ports, stateFile)); machine.reserve = reserveMachine; return release; }
    catch (error) { release(); throw error; }
  };
  machine.reserve = reserveMachine;
  const core = readCoreSettings(state.cwd, undefined, { auto: guard.auto, runs: state.runs });
  if (machineLabel(state)) core.label = machineLabel(state);
  if (machineMode(state)) core.mode = machineMode(state);
  if (machineReport(state)) core.report = machineReport(state);
  if (machineDecisions(state)) core.decisions = machineDecisions(state);
  core.intake = effectiveIntake(state, core);
  core.labelRequired = true;
  // Card jobs never outlive the core: mode off stops them (a tick that ends here does not reach the core's hook).
  if (core.mode === 'off') { try { stopCardJobs({ root: coreRoot(stateFile), ...(p.corePorts?.jobs ? { jobs: p.corePorts.jobs } : {}) }); } catch { /* Next tick. */ } return ok('Autopilot is off.'); }
  await automaticBase(state, p);
  let budget = { state: 'normal' };
  try { budget = githubBudget({ usage: githubUsage(githubMachineEntries({ root: p.githubRoot }), p.now()), ...githubBudgetSettings(read(join(state.cwd, 'pdd.json'), {})?.autopilot?.github) }); }
  catch { /* An unreadable ledger leaves the budget normal. */ }
  p.etags = githubEtagCache({ root: p.githubRoot, repository: state.repo, now: p.now });
  const listIssues = async () => {
    const result = p.queryIssues ? await p.queryIssues(state) : await queryIssues(state, p);
    if (result.reserveBlocked || result.rateLimited) throw Error('GitHub limit is low; the issue list waits for the reset.');
    if (result.status !== 304) { state.cachedIssues = result.issues; state.etag = result.etag; }
    if (result.pages) state.pages = result.pages;
    if (typeof result.since === 'string') state.issuesSince = result.since; else if (Number.isFinite(result.fullAt)) delete state.issuesSince;
    if (Number.isFinite(result.fullAt)) state.issuesFullAt = result.fullAt;
    return state.cachedIssues ?? [];
  };
  const agent = state.agent ?? {}, cRoot = coreRoot(stateFile);
  let pool = { configured: false, poolPath: null, weeklyStopPercent: 97, logins: [] };
  if (state.poolPath !== 'off') {
    try { pool = loadLoginPool({ cwd: state.cwd, env: p.env, poolPath: state.poolPath || undefined, fallbackAgent: agent }); }
    catch (error) { if (state.poolPath) throw error; }
  }
  const selectPool = () => selectPoolLogin({ cwd: state.cwd, env: p.env, poolPath: pool.poolPath, fallbackAgent: agent, stateRoot: cRoot },
    { run: p.run, readCodexLimits: p.codexLimits ?? readCodexLimits, now: p.now });
  const exhaustPool = async ({ loginId, resetAt = null, reason = 'quota' } = {}) => {
    if (loginId) markLoginExhausted({ stateRoot: cRoot, loginId, resetAt, reason, now: p.now() });
    return selectPool();
  };
  const alertPorts = { ...p.alertPorts, repository: async () => ({ nameWithOwner: state.repo }), stateRoot: dirname(stateFile), now: p.now, hostname: () => state.machine };
  if (!p.sendAlert) {
    try { await runAutopilotAlerts({ action: 'retry', cwd: state.cwd, env: p.env }, alertPorts); }
    catch { /* Alert retry never stops the tick. */ }
  }
  const result = await tickCore({ state, settings: core, budget }, {
    gh: (args, options = {}) => p.execute('gh', args, { timeoutMs: 120000, ...options }),
    git: (args, options = {}) => p.execute('git', args, { timeoutMs: 300000, ...options }),
    now: p.now, env: p.env, warn: p.warn, root: cRoot, reportRoot: coreReports(ports, p.env), tickMinutes: timerMinutes(state),
    version: read(join(state.packageRoot ?? dirname(dirname(self)), 'package.json'), {})?.version, listIssues,
    trusted: row => trusted(row, state, { trust: core.trust }, p),
    agentReady: async () => pool.configured ? (await selectPool()).state === 'ready'
      : agent.kind !== 'codex' || (await (p.codexLimits ?? readCodexLimits)({ command: agent.command ?? 'codex', cwd: state.cwd, env: p.env, weeklyStopPercent: pool.weeklyStopPercent })).state !== 'limited',
    ...(pool.configured ? { selectLogin: selectPool, exhaustLogin: exhaustPool } : {}),
    // One alert through this machine's alert destination; the core gives each alert its own cause, tried and need.
    alert: ({ issue, kind, text, tried, need, update }) => (p.sendAlert ?? runAutopilotAlerts)({ action: 'alert', cwd: state.cwd, env: p.env, issue: String(issue), kind, ...(update ? { update: true } : {}),
      text: JSON.stringify({ cause: text, tried: tried ?? 'The Autopilot core engine could not go on with this issue.', need: need ?? 'Check the issue and this machine.' }) },
      alertPorts),
    machine,
    ...p.corePorts,
  });
  const release = await claimAdmission(state, p);
  if (release) try {
    const latest = read(stateFile);
    if (latest?.enabled) {
      for (const key of ['defaultBranch', 'baseBranch', 'cachedIssues', 'etag', 'pages', 'issuesSince', 'issuesFullAt']) if (Object.hasOwn(state, key)) latest[key] = state[key]; else delete latest[key];
      latest.core = { at: p.now(), message: result.message }; latest.nextTick = p.now() + timerMinutes(latest) * 60000; save(stateFile, latest);
    }
  } finally { release(); }
  return result;
}
// The Herdr reply of the old coordinator session, for the move only. A missing Herdr has nothing to close.
async function coordinatorHerdr(args, p) {
  if (p.herdr) return p.herdr(args);
  let result;
  try { result = await p.execute('herdr', ['--session', COORDINATOR_SESSION, ...args]); }
  catch (error) { if (error.code === 'ENOENT') throw Object.assign(Error('Herdr is not installed'), { code: 'herdr_missing' }); throw error; }
  let reply; try { reply = JSON.parse(result.code === 0 ? result.stdout : result.stderr || result.stdout); } catch { reply = {}; }
  if (result.code !== 0 || reply.error) throw Object.assign(Error(reply.error?.message || 'Herdr did not answer'), { code: reply.error?.code });
  return reply;
}
const coreJobs = stateFile => { try { return new Set(readdirSync(join(coreRoot(stateFile), 'jobs')).map(name => Number(/^(\d+)\.json$/.exec(name)?.[1])).filter(Number.isSafeInteger)); } catch { return new Set(); } };
// The move of this machine from the removed full engine, in steps (autopilot-retire). The tick lock is held for the
// whole move, and the core starts no job until the move is complete. It never stops or reloads the timer.
async function moveTick(stateFile, state, p, ports) {
  const saveJournal = async journal => {
    const release = await claimAdmission(state, p);
    if (!release) throw Error('Timed out waiting for automatic admission; retry.');
    try { const latest = read(stateFile); if (latest) { latest.retiredFull = journal; save(stateFile, latest); } } finally { release(); }
  };
  let commonDir = null;
  try { const dir = (await p.checked('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'])).trim(); commonDir = realpathSync(resolve(state.cwd, dir)); }
  catch { return { done: false, message: 'Autopilot could not read this Git repository to move it to the core engine; the next tick retries.' }; }
  const cleanup = workflowCleanupPorts(p, ports);
  const result = await (ports.moveToCore ?? moveToCore)({ state, stateFile, repoEngine: engineAt(state.cwd) }, {
    now: p.now, commonDir, samePath, coreJobs: () => coreJobs(stateFile), save: saveJournal,
    gh: (args, options = {}) => p.execute('gh', args, { timeoutMs: 120000, purpose: 'claims', ...options }),
    herdr: args => coordinatorHerdr(args, p),
    listRuns: (cancelled = false) => (p.listRuns ?? listRuns)({ cwd: state.cwd, cancelled }, p),
    cancelRun: run => (p.cancelRun ?? cancelRun)({ ref: String(run.number), cwd: state.cwd }, { ...cleanup, claimReleased: true, isTTY: false, skipMetricsDelivery: true }),
    releaseLocal: run => (p.releaseIssueClaim ?? releaseIssueClaim)({ cwd: run.sourceRoot, runId: run.runId, issueNumber: run.number }, cleanup.commandPorts ?? {}),
    releaseSlots: () => releaseCheckCapacity({ env: p.env, owner: stateFile }, p.checkCapacityPorts ?? p),
    // A local read of this machine's process table (no agent, Git or GitHub call); Linux without ps reads /proc.
    processes: async () => {
      try { return (await promisify(execFile)('ps', ['-A', '-ww', '-o', 'pid=', '-o', 'ppid=', '-o', 'pgid=', '-o', 'rss=', '-o', 'uid=', '-o', 'lstart=', '-o', 'args='], { encoding: 'utf8', maxBuffer: 64 * 1024 * 1024, timeout: 30000, env: { ...process.env, LC_ALL: 'C' } })).stdout; }
      catch (error) { if (error.code === 'ENOENT' && process.platform === 'linux') return procTable(nativeFs); throw error; }
    },
    uid: typeof process.getuid === 'function' ? process.getuid() : null,
    cwdOf: async pid => {
      if (process.platform === 'linux') try { return realpathSync(`/proc/${pid}/cwd`); } catch { return null; }
      if (process.platform === 'darwin') {
        const text = (await promisify(execFile)('lsof', ['-a', '-p', String(pid), '-d', 'cwd', '-Fn'], { encoding: 'utf8', timeout: 5000 })).stdout;
        return /^n(.+)$/m.exec(text)?.[1] ?? null;
      }
      return null;
    },
    signal: (pid, name) => { try { process.kill(pid, name); } catch { /* It ended already. */ } },
    sleep: ms => new Promise(done => setTimeout(done, ms)),
    ...p.movePorts,
  });
  if (!result.done) return result;
  const release = await claimAdmission(state, p);
  if (!release) return { done: false, message: 'Timed out waiting for automatic admission; the move is saved and the next tick goes on.' };
  try { const latest = read(stateFile); if (latest) save(stateFile, movedState(latest, { ...result.journal, ...(result.message ? { line: result.message } : {}) })); }
  finally { release(); }
  if (result.message) (ports.notice ?? (text => process.stderr.write(`${text}\n`)))(result.message);
  return result;
}
// One tick: first the move of a machine that ran the removed full engine (once, in steps), then the core engine.
async function runTick(stateFile, ports) {
  let state = read(stateFile), p; if (!state?.enabled) return ok('Autopilot stopped.');
  const lock = stateFile + '.lock';
  if (!claimTickLock(lock)) { ports.tickBusy?.(); return ok('Autopilot tick already running.'); }
  try {
    state = read(stateFile);
    if (!state?.enabled) return ok('Autopilot stopped.');
    if (ports.expectedStart && !['cwd','repo','coordinatorId','machine','controlRevision'].every(key => state[key] === ports.expectedStart[key])) return ok('Autopilot start was superseded.');
    p = portsFor(state, { ...ports, githubRoot: dirname(stateFile) });
    if (!state.coordinatorId || !state.machine) {
      const release = await claimAdmission(state, p);
      if (!release) throw Error('Timed out waiting for automatic admission; retry.');
      try { state = read(stateFile); if (!state?.enabled) return ok('Autopilot stopped.'); state.coordinatorId ??= randomUUID(); state.machine ??= hostname(); save(stateFile, state); }
      finally { release(); }
    }
    if (!moved(state)) {
      const move = await moveTick(stateFile, state, p, ports);
      if (!move.done) return ok(line(move.message));
      state = read(stateFile);
      if (!state?.enabled) return ok('Autopilot stopped.');
    }
    const tickResult = await coreTick(stateFile, state, p, ports);
    try {
      const latest = read(stateFile);
      if (latest?.enabled) {
        const update = ports.maybeAutoUpdate ?? (await import('./autopilot-update.mjs')).maybeAutoUpdateAutopilot;
        await update({
          state: latest,
          packageRoot: latest.packageRoot ?? dirname(dirname(self)),
          coreRoot: coreRoot(stateFile),
          stateRoot: dirname(stateFile),
          env: p.env,
        }, {
          now: p.now,
          execute: (file, args, options) => p.execute(file, args, options),
          claimUpdateLock: () => claimMachineAdmission(stateFile, p),
          ...ports.autoUpdatePorts,
        });
      }
    } catch { /* Post-tick self-update never fails a completed tick. */ }
    return tickResult;
  } finally {
    // The tick's own conditional reads keep their ETags.
    try { p?.etags?.save(); } catch { /* A lost cache only costs counted reads. */ }
    // Keep the ledger small: entries older than 2 hours go.
    if (p && state?.repo) githubLedger({ root: p.githubRoot, repository: state.repo }).compact(p.now());
    unlinkSync(lock);
  }
}
function savedProfile(state, env) {
  if (!state?.agent) return null;
  const profile=profileBinding(state,{env});
  const launched=state.ownerLaunch?.profile ?? state.launchProfile;
  // The core engine launches no coordinator; a state saved before its launch profile selects the agent again.
  if (!launched && state.cwd) return null;
  if (!launched || JSON.stringify(launched)!==JSON.stringify(profile) || !profile.home || !profile.definitionHome)
    throw Error('The saved coordinator profile cannot be verified. Inspect the existing coordinator before retrying.');
  return profile;
}

function armStartScan(identity, { env }) {
  const child = spawn(process.execPath, [self, '--start-scan-wait', JSON.stringify(identity)], { detached:true, stdio:'ignore', env });
  child.on('error', () => {}); child.unref();
}
async function waitStartScan(identity, ports = {}) {
  const wait = ports.waitForScan ?? (() => new Promise((resolveWait, reject) => {
    let watcher;
    const check = () => { if (!existsSync(`${identity.stateFile}.lock`)) { watcher.close(); resolveWait(); } };
    try { watcher = watch(dirname(identity.stateFile), check); watcher.on('error', reject); check(); } catch (error) { reject(error); }
  }));
  try {
    for (;;) {
      await wait();
      const state = read(identity.stateFile);
      if (!state?.enabled || !['cwd','repo','coordinatorId','machine','controlRevision'].every(key => state[key] === identity[key])) return;
      let busy = false;
      await runTick(identity.stateFile, { ...ports, expectedStart:identity, tickBusy:() => { busy = true; } });
      if (!busy) return;
    }
  } catch { /* A later supported start or timer can reconcile. */ }
}

export async function withAutopilotModeLock({ cwd, env }, action, ports = {}) {
  let state = { cwd, environment: keepEnv(env ?? process.env) };
  const run = ports.execFile ? async (command, args, options) => {
    try { const value = await ports.execFile(command, args, { cwd: options.cwd, env: options.env, encoding: 'utf8' }); return { code: value.code ?? 0, stdout: value.stdout ?? '', stderr: value.stderr ?? '' }; }
    catch (error) { return { code: error.code === 'ENOENT' ? -1 : 1, stdout: error.stdout ?? '', stderr: error.stderr ?? '' }; }
  } : ports.run;
  const p = portsFor(state, { ...ports, ...(run ? { run } : {}), env });
  const root = await gitRootIn(p);
  if (root.code !== 0) {
    if (/not a git repository/i.test(root.stderr)) return action();
    return bad('Autopilot settings could not verify the Git repository; retry.');
  }
  state.cwd = root.stdout.trim();
  const folder = ports.stateRoot ?? join(p.env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
  const id = createHash('sha256').update(state.cwd).digest('hex').slice(0, 20), stateFile = join(folder, `${id}.json`);
  let releaseAdmission;
  try {
    mkdirSync(folder, { recursive: true, mode: 0o700 });
    const wait = lockWait(p);
    releaseAdmission = await claimAdmission(state, p, wait);
    if (!releaseAdmission) return bad('Timed out waiting for the current Autopilot operation; retry.');
    const result = await action();
    if (result?.exitCode === 0) { const latest = read(stateFile); if (latest) { latest.controlRevision = randomUUID(); save(stateFile, latest); } }
    return result;
  } finally { releaseAdmission?.(); }
}

const isFolder = path => { try { return typeof path === 'string' && path !== '' && statSync(path).isDirectory(); } catch { return false; } };
// The mode of one saved folder, read only when that folder exists and is its own Git root.
async function savedMode(state, ports, env) {
  if (typeof state.cwd !== 'string' || !state.cwd) return 'unknown (no folder saved)';
  if (!isFolder(state.cwd)) return 'unknown (folder missing)';
  const p = portsFor(state, { ...ports, env });
  try {
    const root = await p.execute('git', ['rev-parse', '--show-toplevel']);
    if (root.code !== 0 || !samePath(root.stdout.trim(), state.cwd)) return 'unknown (not a Git repository)';
    return (await settings(state, p)).mode;
  } catch { return 'unknown (settings unreadable)'; }
}
const GONE = Symbol('gone');
// Every saved launcher state on this machine, read-only: local files and timer status only.
// Each line is independent. Timer reads run from the caller's folder, never from a saved folder.
async function machineStatus(folder, ports, env, cwd) {
  let names = [];
  try { names = readdirSync(folder).filter(name => /^[0-9a-f]{20}\.json$/.test(name)).sort(); }
  catch (error) { if (error.code !== 'ENOENT') throw error; }
  const here = isFolder(cwd) ? cwd : env?.HOME || homedir();
  const rows = [];
  for (const name of names) {
    let saved;
    try { saved = read(join(folder, name), GONE); } catch { saved = null; }
    if (saved === GONE) continue;
    if (!saved || typeof saved !== 'object' || Array.isArray(saved)) { rows.push(`${name}: saved state unreadable`); continue; }
    const state = { ...saved, id: name.slice(0, -5), stateFile: join(folder, name) };
    const p = portsFor({ ...state, cwd: here }, { ...ports, env });
    const mode = machineMode(state) ? `${machineMode(state)} (this machine)` : await savedMode(state, ports, env);
    let timerState = 'unknown';
    try { timerState = await timer('status', state, p) ? 'active' : 'inactive'; } catch { /* Report unknown. */ }
    rows.push(`${typeof state.repo === 'string' ? line(state.repo) : 'repository unknown'} in ${typeof state.cwd === 'string' ? line(state.cwd) : 'an unknown folder'} · base ${line(state.baseBranch ?? 'unavailable (start Autopilot)')} · mode ${mode} · Autopilot ${state.enabled ? 'enabled' : 'disabled'} · timer ${timerState}${moved(state) ? '' : ' · moves from the full engine to the core engine at its next tick'}`);
  }
  return ok(rows.length ? [`Autopilot on this machine (${rows.length}):`, ...rows].join('\n') : 'No Autopilot on this machine.');
}

async function localCosts(input, ports, state = {}) {
  const options = { ...ports, env: input.env ?? ports.env };
  const runs = await (ports.costRuns ?? (async () => input.all ? allRuns({ cancelled: true }, options) : listRuns({ cwd: state.cwd ?? input.cwd, cancelled: true }, options)))();
  const measured = runs.map(run => {
    try { return updateRunCosts(run.runDir, latest => {
      if (latest.runId !== run.runId || latest.startedAt !== run.startedAt) throw Error('Cost attempt changed');
      return latest;
    }, options); } catch { return run; }
  });
  return costReport(measured, (ports.now ?? Date.now)());
}
export async function runAutopilotLauncher(input, ports = {}) {
  const { command, packageRoot, runs, checks, issues = [] } = input;
  // Autopilot has one engine: --engine core is accepted and changes nothing; the full engine is refused.
  if (input.engine !== undefined && input.engine !== 'core') return { exitCode: 2, message: input.engine === 'full' ? FULL_ENGINE_REMOVED : 'Leave out --engine: Autopilot runs only the core engine.' };
  if (input.label !== undefined && !(typeof input.label === 'string' && input.label.trim())) return { exitCode: 2, message: 'Use --label with a GitHub label name.' };
  if (input.mode !== undefined && !['auto', 'observe', 'off'].includes(input.mode)) return { exitCode: 2, message: 'Use --mode auto, --mode observe or --mode off.' };
  if (input.report !== undefined && !['file', 'draft', 'off'].includes(input.report)) return { exitCode: 2, message: 'Use --report file, --report draft or --report off.' };
  if (input.intake !== undefined && !INTAKE_MODES.includes(input.intake)) return { exitCode: 2, message: 'Use --intake off, --intake shadow or --intake active.' };
  if (input.decisions !== undefined && !['ask', 'decide'].includes(input.decisions)) return { exitCode: 2, message: 'Use --decisions ask or --decisions decide.' };
  if (input.agent !== undefined && !AGENT_KINDS.includes(input.agent)) return { exitCode: 2, message: 'Use --agent codex, claude, gemini or agy.' };
  if (input.pool !== undefined) {
    try { loadLoginPool({ cwd: input.cwd ?? process.cwd(), env: input.env ?? ports.env ?? process.env, poolPath: input.pool }); }
    catch (error) { return { exitCode: 2, message: line(error.message) }; }
  }
  if (input.autoUpdate !== undefined && !validAutoUpdateMode(input.autoUpdate)) return { exitCode: 2, message: 'Use --auto-update release, --auto-update main or --auto-update off.' };
  const shareRefusal = shareOption(command, input, null); if (shareRefusal) return shareRefusal;
  let startSelection, startWarnings = [], accountOverride = false, activePool = null, chosenPoolLogin = null;
  if (command === 'doctor' || command === 'start') {
    const baseDoctorPorts = typeof ports.doctorPorts === 'function' ? ports.doctorPorts(input,ports) : ports.doctorPorts ?? ports;
    const env = input.env ?? ports.env ?? process.env;
    let doctorInput = input, extraDoctorPorts = {};
    try {
      // Resolve identity without creating state, admission locks or GitHub ledgers.
      const cwd=await gitRoot({env,execute:(file,args,options)=>
        (baseDoctorPorts.run??runAgentProcess)(file,args,{cwd:input.cwd,env,timeoutMs:10000,...options})});
      const id=createHash('sha256').update(cwd).digest('hex').slice(0,20);
      const previous=read(join(stateFolder(ports,env),`${id}.json`));
      // Autopilot takes only the issues that a person marks unless active intake evaluates open issues.
      const saved={...previous,...(input.label?{label:input.label.trim()}:{}),...(input.mode?{mode:input.mode}:{}),...(input.intake?{intake:input.intake}:{})};
      const repoSettings=readCoreSettings(cwd);
      if (command==='start' && !(machineLabel(saved) ?? repoSettings.label) && effectiveIntake(saved, repoSettings)!=='active' && (machineMode(saved) ?? repoSettings.mode)!=='off') throw Error(NO_LABEL);
      const callerPoolOff = typeof input.pool === 'string' && ['off', 'none'].includes(input.pool.trim());
      const effectivePoolOption = callerPoolOff ? 'off' : input.pool !== undefined ? input.pool : input.agent !== undefined ? 'off' : previous?.poolPath;
      if (effectivePoolOption !== 'off') {
        try {
          const loaded = loadLoginPool({ cwd, env, poolPath: effectivePoolOption, fallbackAgent: previous?.agent });
          if (loaded.configured) activePool = loaded;
        } catch (error) {
          if (input.pool !== undefined || previous?.poolPath) throw error;
        }
      }
      accountOverride = command === 'start' && (input.agent !== undefined || input.pool !== undefined || explicitConfigOverride(previous, env) || Boolean(activePool?.configured && !previous?.poolPath));
      if (activePool?.configured) {
        const picked = await selectPoolLogin(
          { cwd, env, poolPath: activePool.poolPath, pool: activePool, stateRoot: null, allowLimited: true },
          { fs: baseDoctorPorts.files ?? nativeFs, run: baseDoctorPorts.run, readCodexLimits: baseDoctorPorts.codexLimits, codexLimitPorts: { spawn: baseDoctorPorts.spawn } },
        );
        chosenPoolLogin = picked.state === 'ready' ? picked.login : (activePool.logins.find(item => !item.paused) ?? activePool.logins[0]);
        const doctorEnv = picked.state === 'ready' ? picked.env : loginEnvironment(env, chosenPoolLogin);
        const profile = {
          agent: { id: chosenPoolLogin.id, kind: chosenPoolLogin.kind },
          home: doctorEnv.HOME ?? homedir(),
          definitionHome: env.HOME ?? homedir(),
          configHome: chosenPoolLogin.configDir,
        };
        doctorInput = { ...input, cwd, env: doctorEnv, profile };
        extraDoctorPorts = {
          selectAgent: undefined,
          agentDefinitions: async () => [{ id: chosenPoolLogin.id, kind: chosenPoolLogin.kind, command: chosenPoolLogin.command, ...(chosenPoolLogin.model ? { model: chosenPoolLogin.model } : {}), env: chosenPoolLogin.env }],
          codexLimits: (opts, limitPorts) => (baseDoctorPorts.codexLimits ?? readCodexLimits)({ weeklyStopPercent: activePool.weeklyStopPercent, ...opts }, limitPorts),
        };
      } else if (command === 'start' && input.agent !== undefined) {
        let defs = [];
        try { defs = await ((ports.selectAgent ? undefined : baseDoctorPorts.agentDefinitions) ?? loadAgentDefinitions)({ cwd, env }); } catch {}
        const match = Array.isArray(defs) ? defs.find(def => def?.kind === input.agent) : null;
        const targetId = input.agent === 'agy' ? 'agy' : match?.id || input.agent;
        const ownVar = AGENT_CONFIG_VARS[input.agent];
        const doctorEnv = loginEnvironment(env, { kind: input.agent, configVar: ownVar, configDir: ownVar && env[ownVar] ? env[ownVar] : null, env: {} });
        const profile = {
          agent: { id: targetId, kind: input.agent },
          home: env.HOME ?? homedir(),
          definitionHome: env.HOME ?? homedir(),
          configHome: ownVar && env[ownVar] ? env[ownVar] : null,
        };
        doctorInput = { ...input, cwd, env: doctorEnv, profile };
        extraDoctorPorts = {
          ...(ports.selectAgent ? { selectAgent: undefined } : {}),
          ...(input.agent !== 'agy' && (ports.selectAgent || !match)
            ? { agentDefinitions: async () => [match ?? { id: targetId, kind: input.agent, command: input.agent, env: {} }] }
            : {}),
        };
      } else if (command === 'start' && explicitConfigOverride(previous, env)) {
        const kind = previous.agent.kind, ownVar = AGENT_CONFIG_VARS[kind];
        const doctorEnv = loginEnvironment(env, { kind, configVar: ownVar, configDir: env[ownVar], env: {} });
        const profile = {
          agent: { id: previous.agent.id, kind },
          home: env.HOME ?? homedir(),
          definitionHome: env.HOME ?? homedir(),
          configHome: env[ownVar],
        };
        doctorInput = { ...input, cwd, env: doctorEnv, profile };
        if (ports.selectAgent) {
          extraDoctorPorts = {
            selectAgent: undefined,
            agentDefinitions: async () => [{ ...previous.agent, env: {} }],
          };
        }
      } else {
        const profile = savedProfile(previous, env);
        doctorInput = { ...input, cwd, env, profile };
      }
    } catch (error) {
      if (command==='start') return bad(error.message);
      // Doctor still reports repository failures in its complete report.
      if (!error.exact) return bad(error.message);
    }
    const doctorPorts = typeof ports.doctorPorts === 'function' ? ports.doctorPorts(doctorInput, ports) : baseDoctorPorts;
    const diagnostics = await runAutopilotDoctor(doctorInput, {...doctorPorts, ...extraDoctorPorts,
      onSelection:selection=>{startSelection=selection;}});
    if (command === 'doctor' || diagnostics.exitCode !== 0) return diagnostics;
    startWarnings = diagnostics.message.split('\n').filter(line=>line.startsWith('WARN '));
  }
  let state = { cwd: input.cwd, environment: keepEnv(input.env ?? process.env) };
  let p = portsFor(state, { ...ports, env: input.env });
  let controlLock, releaseAdmission;
  try {
    if (command === 'report') {
      const root = coreReports(ports, p.env);
      if (issues[0] === 'send' && issues[1]) return await sendReportDraft({ root, fingerprint: issues[1], machine: hostname() }, { gh: (args, options) => p.execute('gh', args, { timeoutMs: 60000, ...options }), now: p.now });
      if (issues.length) return { exitCode: 2, message: 'Use pdd autopilot report, or pdd autopilot report send FINGERPRINT.' };
      const drafts = listReportDrafts({ root });
      return ok(drafts.length ? [...drafts.map(d => `${d.fingerprint}: ${d.title}; seen ${d.count} time(s), last ${new Date(d.lastAt).toISOString()}`), 'Send one with pdd autopilot report send FINGERPRINT.'].join('\n') : 'No local Autopilot report drafts.');
    }
    // The post-merge audit of a saved run's merge (kept for #3182: the core will reuse it after its own merges).
    if (command === 'audit') {
      const found = await resolveRun(issues[0], {cwd:input.cwd}, {...ports,env:p.env,execFile:async(file,args,options)=>({stdout:await p.checked(file,args,options)})});
      if(found.error) return bad(found.error);
      state.repo=found.run.repo;
      return auditMerge({run:found.run,pr:issues[1]},{...ports,env:p.env,execFile:(file,args,options)=>p.execute(file,args,{...options,purpose:'audit'})});
    }
    if (command === 'check-base') {
      const found = await resolveRun(issues[0], { cwd: input.cwd }, { ...ports, env: p.env, execFile: async (file, args, options) => ({ stdout: await p.checked(file, args, options) }) });
      if (found.error) return bad(found.error);
      state.repo = found.run.repo;
      return checkAutopilotBase({ run: found.run, pr: issues[1] }, { execFile: (file, args, options) => p.execute(file, args, options) });
    }
    if (command === 'status' && input.json) return ok(JSON.stringify(await localCosts(input, ports), null, 2));
    if (command === 'status' && input.all) {
      const status = await machineStatus(stateFolder(ports, p.env), ports, input.env, input.cwd);
      try { status.message += '\n' + costStatusLines(await localCosts(input, ports)); } catch {}
      return status;
    }
    state.cwd = await gitRoot(p);
    const id = createHash('sha256').update(state.cwd).digest('hex').slice(0, 20);
    const folder = stateFolder(ports, p.env);
    const stateFile = join(folder, `${id}.json`);
    if (command === 'start' || command === 'stop') {
      mkdirSync(folder, { recursive: true, mode: 0o700 });
      const wait = lockWait(p);
      releaseAdmission = await claimAdmission(state, p, wait);
      if (!releaseAdmission) return bad('Timed out waiting for the current Autopilot operation; retry.');
    }
    const previous = read(stateFile);
    state = { ...state, ...previous, cwd: state.cwd, id, stateFile };
    if (command === 'start') { if (input.label) state.label = input.label.trim(); if (input.mode) state.mode = input.mode; if (input.report) state.report = input.report; if (input.decisions) state.decisions = input.decisions; if (input.intake) state.intake = input.intake; if (input.autoUpdate) state.autoUpdate = input.autoUpdate; }
    shareOption(command, input, state);
    let initialRevision = previous?.controlRevision ?? null;
    // A new state is a core state: only a state that an older pdd saved can need the move from the full engine.
    if (command === 'start' && !previous) { initialRevision = randomUUID(); state.controlRevision = initialRevision; state.engine = 'core'; state.enabled = false; state.timerInstalled = false; state.nextTick = null; save(stateFile, state); }
    // Explicit undefined values mask unrelated ambient provider directories in portsFor.
    const invocationEnv=startSelection ? {...startSelection.env,
      CODEX_HOME:startSelection.env.CODEX_HOME,CLAUDE_CONFIG_DIR:startSelection.env.CLAUDE_CONFIG_DIR,GEMINI_CLI_HOME:startSelection.env.GEMINI_CLI_HOME,ANTIGRAVITY_APP_DATA_DIR:startSelection.env.ANTIGRAVITY_APP_DATA_DIR} : input.env;
    p = portsFor(state, { ...ports, env: invocationEnv });
    if (command === 'start') { releaseAdmission(); releaseAdmission = null; }
    if (command === 'intake') {
      const mode = effectiveIntake(state, readCoreSettings(state.cwd));
      const report = readIntake({ root: coreRoot(stateFile), now: p.now() });
      return ok(input.json ? JSON.stringify({ repository: state.repo ?? null, intake: mode, ...report }, null, 2) : `Intake: ${mode} on this machine.\n${intakeText(report, { mode })}`);
    }
    if (command === 'status') {
      const timerActive = Boolean(await timer('status', state, p)), guard = await coreGuard(state, p, ports, stateFile);
      const settingsNow = readCoreSettings(state.cwd, undefined, { auto: guard.auto, runs: state.runs });
      const label = machineLabel(state) ?? settingsNow.label;
      if (machineMode(state)) settingsNow.mode = machineMode(state);
      if (machineReport(state)) settingsNow.report = machineReport(state);
      if (machineDecisions(state)) settingsNow.decisions = machineDecisions(state);
      const intakeNow = effectiveIntake(state, settingsNow);
      if (intakeNow !== 'off') settingsNow.intake = intakeNow;
      return ok(`Autopilot ${state.enabled ? 'enabled' : 'disabled'}; timer ${timerLine(state, timerActive)}; next tick: ${timerActive && state.nextTick ? new Date(state.nextTick).toISOString() : 'none'}\n`
        + coreStatus({ state, guard: guard.line, settings: { ...settingsNow, label }, sources: { label: machineLabel(state) ? 'machine' : label ? 'pdd.json' : null, mode: machineMode(state) ? 'machine' : 'pdd.json', report: machineReport(state) ? 'machine' : 'pdd.json', decisions: machineDecisions(state) ? 'machine' : 'pdd.json' } },
          { root: coreRoot(stateFile), reportRoot: coreReports(ports, p.env), now: p.now })
        + (label || intakeNow === 'active' ? '' : '\nNo opt-in label: Autopilot takes no issue. Run pdd autopilot start --label pdd:autopilot, then mark issues with pdd autopilot add N.')
        + alertLine(state, p, ports)
        + (await updateLine(stateFile, ports))
        + moveStatus(previous, p.now())
        + (state.core?.message ? `\nLast tick ${new Date(state.core.at).toISOString()}: ${line(state.core.message)}` : ''));
    }
    if (command === 'stop') {
      if (previous) { state.enabled = false; state.nextTick = null; state.controlRevision = randomUUID(); save(stateFile, state); }
      await timer('stop', state, p);
      try { stopCardJobs({ root: coreRoot(stateFile), ...(p.corePorts?.jobs ? { jobs: p.corePorts.jobs } : {}) }); } catch { /* The card jobs end by themselves. */ }
      await releaseCheckCapacity({env:p.env,owner:stateFile}, p.checkCapacityPorts ?? p);
      if (previous) { state.timerInstalled = false; save(stateFile, state); }
      return ok('Autopilot stopped on this machine; the current step can finish.');
    }
    for (const [name,value] of [['runs',runs],['checks',checks]]) if (command === 'start' && value !== undefined && (!/^[1-9][0-9]*$/.test(value) || !Number.isSafeInteger(Number(value)))) return {exitCode:2,message:`Use --${name} with a positive safe integer, or omit it for machine capacity.`};
    if (command === 'start') {
      const config = await settings(state, p);
      if (config.mode === 'off') return ok(`${line(config.message)} Choose observe or auto with pdd autopilot observe or pdd autopilot auto.`);
      state.packageRoot = packageRoot;
    }
    if (!state.repo || command === 'start') {
      const metadata = JSON.parse(await p.checked('gh', ['repo', 'view', '--json', 'nameWithOwner,defaultBranchRef']));
      if (state.repo && state.repo.toLowerCase() !== metadata.nameWithOwner?.toLowerCase()) throw Error('Automatic base repository does not match.');
      state.repo = metadata.nameWithOwner; state.defaultBranch = metadata.defaultBranchRef?.name;
    }
    if (command === 'add') {
      const numbers = [];
      for (const ref of issues) {
        const match = String(ref).match(/^(?:([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)#|https:\/\/github\.com\/([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)\/issues\/)?([1-9][0-9]*)\/?$/);
        if (!match || (match[1] || match[2] || state.repo).toLowerCase() !== state.repo.toLowerCase()) return { exitCode: 2, message: `Use issue numbers or references to ${state.repo} with pdd autopilot add.` };
        numbers.push(match[3]);
      }
      const label = await p.execute('gh', ['api', '--method', 'POST', `repos/${state.repo}/labels`, '-f', 'name=pdd:autopilot', '-f', 'color=5319e7', '-f', 'description=Autopilot may take this old issue']);
      if (label.code !== 0 && !/already_exists/.test(label.stdout + label.stderr)) throw Error('Could not create pdd:autopilot; check gh auth status.');
      for (const number of numbers) await p.checked('gh', ['api', '--method', 'POST', `repos/${state.repo}/issues/${number}/labels`, '-f', 'labels[]=pdd:autopilot']);
      return ok(`Marked ${issues.length} issue(s) with pdd:autopilot.`);
    }
    if (command === 'release') {
      const result = await releaseRunClaim({
        ref: issues[0], cwd: state.cwd, repository: state.repo,
        machine: state.machine, coordinatorId: state.coordinatorId,
      }, { ...workflowCleanupPorts(p, ports), execFile: async (file, args, options) => {
        const reply = await p.execute(file, args, { purpose: 'claims', ...options });
        if (reply.code !== 0) throw Object.assign(Error(reply.stderr || reply.stdout || `${file} failed`), reply);
        return reply;
      } });
      return { exitCode: result.exitCode, message: result.message };
    }
    if (command !== 'start') return { exitCode: 2, message: 'Use pdd autopilot start, stop, status, add or release.' };
    // The no-progress period must be at least 2 ticks of the core timer, or a working job could look quiet.
    const quiet = readCoreSettings(state.cwd).quietMinutes, floor = 2 * CORE_INTERVAL / 60000;
    if (quiet < floor) return bad(`Autopilot did not start: autopilot.quietMinutes is ${quiet}; it must be at least ${floor} (2 times the ${CORE_INTERVAL / 60000}-minute core timer). Nothing was started or claimed.`);
    await automaticBase(state, p);
    if ((await p.execute('gh', ['auth', 'status'])).code !== 0) return bad('GitHub is not signed in; run gh auth login.');
    const previousProfile = accountOverride || activePool?.configured ? null : savedProfile(previous,p.env);
    let probe = p, saved = null;
    if (previousProfile) {
      const configVariable = AGENT_CONFIG_VARS[previous.agent.kind];
      const env = { ...p.env, HOME:previousProfile.definitionHome };
      for (const variable of Object.values(AGENT_CONFIG_VARS)) {
        if (variable === configVariable && previousProfile.configHome) env[variable] = previousProfile.configHome; else delete env[variable];
      }
      saved = { ...previousProfile, configVariable }; probe = { ...p, env };
    }
    const rawAgent = ports.selectAgent && !accountOverride && !activePool?.configured
      ? await ports.selectAgent(state, probe)
      : saved ? await selectAgent(state, probe, saved) : startSelection.agent;
    const agent = chosenPoolLogin && rawAgent ? { ...rawAgent, ...(chosenPoolLogin.model ? { model: chosenPoolLogin.model } : {}) } : rawAgent;
    if (!agent || saved && (agent.id !== saved.agent.id || agent.kind !== saved.agent.kind)) return bad(saved ? 'The saved coordinator profile is unavailable. Restore its sign-in and retry.' : 'Sign in to Codex, Claude Code, agy or Gemini at your terminal, then run pdd autopilot start.');
    const version = read(join(packageRoot, 'package.json')).version;
    const warnings = (ports.pathDiagnostic ?? pathDiagnostic)({ cwd: state.cwd, packageRoot, env: p.env, mode: 'workflow' });
    const oldAccountLabel = previous?.agent ? describeProfile(previous.agent, previous.environment) : null;
    if (!previousProfile) {
      state.agent = { id: agent.id, kind: agent.kind, command: agent.command, ...(agent.model ? { model: agent.model } : {}) };
      state.definitionHome = (input.env ?? ports.env ?? process.env).HOME;
      state.environment = keepEnv({ ...p.env, ...agent.env });
      delete state.ownerLaunch;
      state.launchProfile = profileBinding(state, p);
    }
    // The core engine has no coordinator launch to record its profile: save it here so a later start can verify it.
    if (state.agent) state.launchProfile ??= profileBinding(state, p);
    if (input.pool !== undefined) state.poolPath = ['off', 'none'].includes(input.pool.trim()) ? 'off' : activePool?.poolPath ?? 'off';
    else if (activePool?.configured && !state.poolPath) state.poolPath = activePool.poolPath;
    if (input.agent !== undefined && input.pool === undefined && state.poolPath && state.poolPath !== 'off') state.poolPath = 'off';
    const accountNotices = [];
    const newAccountLabel = describeProfile(state.agent, state.environment);
    if (accountOverride && oldAccountLabel && oldAccountLabel !== newAccountLabel) accountNotices.push(`Account changed from ${oldAccountLabel} to ${newAccountLabel}.`);
    if (activePool?.configured) {
      const ids = activePool.logins.filter(item => !item.paused).map(item => item.id);
      accountNotices.push(`Login pool: ${ids.join(' -> ')} (${ids.length} login(s)).`);
    } else if (input.pool !== undefined && previous?.poolPath && previous.poolPath !== 'off') {
      accountNotices.push('Login pool disabled.');
    }
    // The time of this start: in auto mode it is the operator action that approves the core jobs' prompt changes.
    state.startedAt = new Date(p.now()).toISOString();
    state.activatedAt ??= new Date(p.now()).toISOString();
    state.coordinatorId ??= randomUUID(); state.machine ??= hostname();
    state.enabled = true; state.timerInstalled = true; state.nextTick = p.now() + intervalOf(state);
    state.controlRevision = randomUUID();
    if (runs !== undefined) state.runs = Number(runs); else delete state.runs;
    if (checks !== undefined) state.checks = Number(checks); else delete state.checks;
    const priorRevision = initialRevision;
    releaseAdmission = await claimAdmission(state, p);
    if (!releaseAdmission) return bad('Timed out waiting for the current Autopilot operation; retry.');
    if ((read(stateFile)?.controlRevision ?? null) !== priorRevision) return bad('Autopilot changed while starting; retry.');
    const currentConfig = await settings(state, p);
    if (machineMode(state)) currentConfig.mode = machineMode(state);
    // A machine mode off is saved, and the timer stops: no tick runs until a start with --mode auto or observe.
    if (machineMode(state) === 'off') {
      Object.assign(state, { enabled: false, timerInstalled: false, nextTick: null, controlRevision: randomUUID() }); save(stateFile, state);
      let stopped = '';
      try { await timer('stop', state, p); } catch (error) { stopped = ` The timer could not stop (${line(error.message)}); its ticks do nothing while the mode is off.`; }
      return ok(`Autopilot core is off on this machine for ${state.repo}: mode off is saved and the timer is stopped.${stopped} To turn it on, run pdd autopilot start --mode auto or --mode observe.`);
    }
    if (currentConfig.mode === 'off') return ok(`${line(currentConfig.message)} Choose observe or auto with pdd autopilot observe or pdd autopilot auto.`);
    await automaticBase(state, p);
    try { await timer('start', state, p); state.timerMinutes = intervalOf(state) / 60000; }
    catch {
      if (!previous) { state.enabled = false; state.nextTick = null; state.controlRevision = initialRevision; delete state.activatedAt; delete state.runs; save(stateFile, state); }
      return bad('Autopilot timer could not start; enable your systemd user session on Linux or launchctl user session on macOS, then retry.');
    }
    if (accountOverride && previous) clearPauseState(stateFile);
    state.startAction = { command: 'pdd autopilot start', repository: state.repo, mode: currentConfig.mode };
    save(stateFile, state);
    let warning = '';
    if ((p.platform ?? process.platform) === 'linux') {
      let linger = '';
      try { const result = await p.execute('loginctl', ['show-user', String(p.uid ?? process.getuid()), '--property=Linger', '--value']); if (result.code === 0) linger = result.stdout.trim(); } catch { /* Optional session diagnostic. */ }
      if (linger !== 'yes') warning = ' To keep Autopilot running after logout, enable lingering: loginctl enable-linger.';
    }
    releaseAdmission(); releaseAdmission = null;
    const moveLines = [];
    try {
      let busy = false;
      await runTick(stateFile, { ...ports, env: p.env, notice: text => moveLines.push(line(text)), tickBusy: () => { busy = true; } });
      if (busy) {
        const identity = { stateFile, cwd:state.cwd, repo:state.repo, coordinatorId:state.coordinatorId, machine:state.machine, controlRevision:state.controlRevision };
        (ports.armStartScan ?? armStartScan)(identity, { env:p.env, resume: () => waitStartScan(identity, { ...ports, env:p.env }) });
      }
    }
    catch (e) { warning += ` Warning: ${line(e.message)}; next tick will retry.`; }
    const startCore = readCoreSettings(state.cwd);
    const startLabel = machineLabel(state) ?? startCore.label;
    const scopeSummary = startLabel ? `issues with ${startLabel}` : 'ready issues from active intake';
    return ok(`${startWarnings.length ? startWarnings.join('\n')+'\n' : ''}${moveLines.length ? moveLines.join('\n')+'\n' : ''}Autopilot started for ${state.repo} in ${state.cwd}. Base ${state.baseBranch}. Mode ${currentConfig.mode}${machineMode(state) ? ' (this machine)' : ''} · ${scopeSummary} · agent ${state.agent.id} · pdd ${version} · next tick: ${new Date(state.nextTick).toISOString()}. See: pdd autopilot status.${accountNotices.length ? ' ' + accountNotices.join(' ') : ''}${warning}${warnings.length ? ' ' + warnings.map(line).join(' ') : ''}`);
  } catch (e) { return bad(e.exact ? e.message : `Autopilot: ${e.code === 'ENOENT' ? 'install git, gh and Herdr, and sign in to your agent, then retry.' : line(e.message)}`); }
  finally { releaseAdmission?.(); controlLock?.(); }
}

if (process.argv[1] && resolve(process.argv[1]) === self) {
  if (process.argv[2] === '--start-scan-wait') { try { await waitStartScan(JSON.parse(process.argv[3])); } catch { process.exitCode = 1; } }
  else tickAutopilot(process.argv[2]).catch(error => { process.stderr.write(`Autopilot: ${line(error.message)}\n`); process.exitCode = 1; });
}
