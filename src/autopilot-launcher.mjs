import {blockerFor, interpreterWaitFor, reconcileParking, parkingSummary, parkingWords} from './autopilot-parking.mjs';
import {currentChat} from './workflow-runs.mjs';
import {chatHealth, chatSession} from './workflow-chat.mjs';
import {WORKFLOW_CAPABILITIES, parkBlockedRun, wakeParkedRun, releaseParkedRun, changeRun, hasParkedReply} from './workflow-runner.mjs';
import { readMachineResources } from './machine-resources.mjs';
import { configureCheckCapacity, releaseCheckCapacity, readCheckStatus, readSuiteProgress } from './test-suite-queue.mjs';
import { readCodexLimits } from './codex-limits.mjs';
import { cleanupWorktrees } from './autopilot-cleanup.mjs';
import { environmentRecovery, environmentWakeTag, environmentHealthy, machineHealth, ENVIRONMENT_BACKOFF } from './autopilot-environment.mjs';
import { readInterpreterProgress, configureInterpreterTestMode } from './interpreter-queue.mjs';
// Generated from prompts/cli/autopilot-launcher.prompt.md (sha256: a78d4c223909be57dcbcac181947990143ae03811f7ff64566994490df41a90b).
import { spawn } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, readdirSync, statSync, writeFileSync, renameSync, unlinkSync, linkSync, chmodSync, openSync, closeSync, fchmodSync, fstatSync, constants, watch, realpathSync } from 'node:fs';
import { homedir, hostname } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runAgentProcess, parseAgentAuthStatus } from './agent-adapters.mjs';
import { loadAgentDefinitions } from './agent-config.mjs';
import { pathDiagnostic } from './path-diagnostic.mjs';
import { runAutopilot } from './autopilot.mjs';
import { checkWorkflowAgents } from './workflow-agents.mjs';
import { gitContext, metricsSource, allRuns, updateRunCosts, listRuns, readRun, updateRun, resolveRun } from './workflow-runs.mjs';
import { appendEvents } from './metrics-store.mjs';
import { recordCaptureGap } from './metrics-gap.mjs';
import * as nativeFiles from 'node:fs';
import { tidyRuns } from './workflow-runner.mjs';
import { paneUsage, ensurePaneBudget } from './workflow-chat.mjs';
import { reconcileDependencyIntake } from './issue-dependencies-intake.mjs';
import { issueKey } from './issue-dependencies.mjs';
import { createDependencyReadPorts, dependencySnapshotStore, issueRowVersion, recordLongRunningAlert, releaseParkedClaim, recoverCoordinatorClaim, refreshClaimHeartbeat, takeoverLimited, withoutClaimHeartbeat } from './issue-dependencies-github.mjs';
import { sendToChat, START_GRACE_MS } from './workflow-chat.mjs';
import { acquireRunLock, runtimeWakeTag, isRetryRequest, automaticAttention, resumeStoppedRun, nudgeIdleRun } from './workflow-runner.mjs';
import { checkCause, readRunResults, checkVerdictSince, latestCheckVerdict, savedLostCheck, savedCheckCause } from './workflow-results.mjs';
import { armSavedWorkerCompletion } from './workflow-worker-completion.mjs';
import { samePath } from './workflow-herdr-layout.mjs';
import { tomlString } from './toml-string.mjs';
import { alertStatusLine, runAutopilotAlerts } from './autopilot-alerts.mjs';
import { countGithubCalls, githubBudget, githubBudgetSettings, githubEtagCache, githubFloorGuard, githubFullLastPage, githubLedger, githubMachineEntries, githubReply, githubStateRoot, githubStatusLine, githubUsage } from './github-calls.mjs';
import { lookupRepositoryParent, githubOriginRepository } from './workflow-worktree.mjs';
import { costReport, costStatusLines } from './cost-ledger.mjs';

import { selectAutopilotBase, checkAutopilotBase } from './autopilot-base.mjs';

const INTERVAL = 30 * 60 * 1000;
const STUCK_AFTER = 60 * 60 * 1000;
const CLAIM_IDLE_AFTER = 60 * 60 * 1000;
const STUCK_CLAIM_AFTER = 4 * 60 * 60 * 1000;
const LONG_RUNNING_AFTER = 24 * 60 * 60 * 1000;
const HEARTBEAT_SLACK = 5 * 1000;
// With a low GitHub budget the dependency re-sync runs at most once in this time.
const LOW_BUDGET_INTAKE_EVERY = 60 * 60 * 1000;
// The issue list reads only changed issues; the whole open list is read again after this time.
const FULL_ISSUE_LIST_EVERY = 6 * 60 * 60 * 1000;
const SESSION = 'pdd-autopilot';
const ACK = '<!-- pdd:autopilot:thanks -->';
const ACK_TEXT = `thanks, a maintainer will look\n\n${ACK}`;
const self = fileURLToPath(import.meta.url);
const quote = value => `'${String(value).replaceAll("'", "'\\''")}'`;
// The launch line starts in the repository: a `cd` in the person's shell startup file can move a new pane's shell elsewhere.
const startIn = cwd => ['cd', quote(cwd), '&&'];
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
const keepEnv = env => Object.fromEntries(['HOME', 'PATH', 'CODEX_HOME', 'CLAUDE_CONFIG_DIR', 'GEMINI_CLI_HOME', 'XDG_CONFIG_HOME', 'XDG_RUNTIME_DIR', 'DBUS_SESSION_BUS_ADDRESS', 'PDD_SUITE_QUEUE', 'PDD_VM_SUITE_LOCK', 'PDD_INTERPRETER_QUEUE', 'PDD_INTERPRETER_CONCURRENCY'].filter(k => typeof env[k] === 'string').map(k => [k, env[k]]));
function checkCapacityWords(state, p) {
  try {
    const c = readCheckStatus({env:p.env}, p.checkCapacityPorts ?? p);
    return `check slots: ${c.busyChecks} busy of ${c.checks}, ${c.waitingChecks} waiting, cores per check ${c.coresPerCheck}\nchecks: calculated ${c.calculatedChecks}, chosen ${c.checks}; runs: calculated ${c.calculatedRuns}, chosen ${c.runs}\nrepository overrides: checks ${state.checks ?? 'automatic'}, runs ${state.runs ?? 'automatic'}`;
  } catch (error) { return `check capacity unavailable: ${line(error.message)}`; }
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
// local Git reads only name the cause after it refuses.
async function workflowReadiness(state, p) {
  if (p.allocationCheck) return p.allocationCheck({ cwd: state.cwd, repository: state.repo });
  let unreadable = false;
  const execute = async (file, args, cwd) => { try { return await p.execute(file, args, { cwd }); } catch (error) { unreadable = true; throw error; } };
  const git = async args => { try { return await execute('git', args, state.cwd); } catch { return { code: 1, stdout: '', stderr: '' }; } };
  const origin = await git(['remote', 'get-url', 'origin']);
  const named = origin.code === 0 ? githubOriginRepository(origin.stdout) : null;
  const repository = state.repo ?? named;
  const common = await git(['rev-parse', '--path-format=absolute', '--git-common-dir']);
  let commonDir = null;
  if (common.code === 0 && common.stdout.trim()) { try { commonDir = realpathSync(resolve(state.cwd, common.stdout.trim())); } catch { /* Not verifiable. */ } }
  if (repository && commonDir) {
    const parent = await lookupRepositoryParent({ cwd: state.cwd, repository, commonDir }, {
      execFile: async (file, args, { cwd }) => { const result = await execute(file, args, cwd); return { stdout: result.stdout, stderr: result.stderr, code: result.code }; },
    });
    if (parent.state === 'ready') return { state: 'ready', message: '' };
  }
  if (unreadable) return { state: 'refused', message: 'pdd could not read Git in this checkout. Try again.' };
  const refused = cause => ({ state: 'refused', message: `${cause} Run Autopilot from a normal clone of ${repository ?? 'the GitHub repository'}.` });
  if (origin.code !== 0 || !origin.stdout.trim()) return refused('This checkout has no origin remote.');
  if (!named) return refused('Its origin remote is not a GitHub repository address.');
  if (state.repo && named.toLowerCase() !== state.repo.toLowerCase()) return refused(`Its origin remote names ${named}, not ${state.repo}.`);
  return refused('pdd cannot verify the Git layout of this checkout, so it cannot make issue worktrees here.');
}
async function selectAgent(state, p, saved = null) {
  let definitions = loadAgentDefinitions({ cwd: state.cwd, env: p.env });
  definitions.push({ id: 'agy', kind: 'agy', command: 'agy', env: {} });
  if (saved) definitions = definitions.filter(def => def.id === saved.agent.id && def.kind === saved.agent.kind);
  const current = p.env.CODEX_THREAD_ID ? 'codex' : p.env.CLAUDECODE ? 'claude' : null;
  const rank = def => def.kind === current ? -1 : ['codex', 'claude', 'agy', 'gemini'].indexOf(def.kind);
  definitions = definitions.map((def, index) => ({ def, index })).sort((a, b) => rank(a.def) - rank(b.def) || a.index - b.index).map(x => x.def);
  for (const def of definitions) {
    const agentEnv = { ...p.env, ...def.env };
    if (saved) {
      agentEnv.HOME = saved.home;
      for (const variable of ['CODEX_HOME','CLAUDE_CONFIG_DIR','GEMINI_CLI_HOME']) {
        if (saved.configVariable === variable && saved.configHome) agentEnv[variable] = saved.configHome;
        else delete agentEnv[variable];
      }
    }
    try {
      if (def.kind === 'gemini') {
        const help = await p.execute(def.command, ['--version'], { env: agentEnv });
        const credentials = read(join(agentEnv.GEMINI_CLI_HOME || agentEnv.HOME || homedir(), '.gemini', 'oauth_creds.json'), {});
        if (help.code === 0 && typeof credentials.refresh_token === 'string' && credentials.refresh_token) return def;
      } else if (def.kind === 'agy') {
        const result = await checkWorkflowAgents({ cwd: state.cwd, env: agentEnv, requested: 'agy' }, {
          run: (_command, args, options) => p.execute(def.command, args, options),
        });
        if (result.ok) return def;
      } else {
        const result = await p.execute(def.command, def.kind === 'codex' ? ['login', 'status'] : ['auth', 'status', '--json'], { env: agentEnv });
        if (parseAgentAuthStatus({ agent: def.kind, result }) === 'ready') return def;
      }
    } catch { /* Try another installed sign-in; never make a model call to test it. */ }
  }
  return null;
}
function xml(value) { return String(value).replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;').replaceAll("'", '&apos;'); }
// Timers execute this file directly. Neither platform needs a shell or a daemon owned by pdd.
async function userTimer(action, state, p) {
  const platform = p.platform ?? process.platform;
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
    writeFileSync(file, `<?xml version="1.0" encoding="UTF-8"?><!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd"><plist version="1.0"><dict><key>Label</key><string>${name}</string><key>ProgramArguments</key><array>${args}</array><key>EnvironmentVariables</key><dict>${vars}</dict><key>StartInterval</key><integer>1800</integer><key>StandardErrorPath</key><string>${xml(state.stateFile + '.log')}</string></dict></plist>`, { mode: 0o600 });
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
  writeFileSync(join(folder, `${name}.service`), `[Unit]\nDescription=PDD Autopilot tick\n[Service]\nType=oneshot\nKillMode=process\nExecStart=${[process.execPath, self, state.stateFile].map(unit).join(' ')}\n${Object.entries(state.environment).map(([k, v]) => `Environment=${unit(k + '=' + v)}\n`).join('')}`, { mode: 0o600 });
  writeFileSync(join(folder, `${name}.timer`), `[Unit]\nDescription=PDD Autopilot every 30 minutes\n[Timer]\nOnActiveSec=30min\nOnUnitActiveSec=30min\nAccuracySec=1s\n[Install]\nWantedBy=timers.target\n`, { mode: 0o600 });
  await p.checked('systemctl', ['--user', 'daemon-reload']);
  await p.checked('systemctl', ['--user', 'enable', `${name}.timer`]);
  await p.checked('systemctl', ['--user', 'restart', `${name}.timer`]);
  return true;
}
async function timer(action, state, p) { return p.timer ? p.timer(action, state) : userTimer(action, state, p); }
async function herdr(args, p) {
  if (p.herdr) return p.herdr(args);
  const result = await p.execute('herdr', ['--session', SESSION, ...args]);
  if (result.code === 0 && args[0] === 'pane' && args[1] === 'read') return result.stdout;
  let reply; try { reply = JSON.parse(result.code === 0 ? result.stdout : result.stderr || result.stdout); } catch { reply = {}; }
  if (result.code !== 0 || reply.error) throw Object.assign(Error(reply.error?.message || 'Herdr could not deliver; run herdr --help.'), { code: reply.error?.code, confirmedRejection: Boolean(reply.error && typeof reply.error === 'object') });
  return reply;
}
async function coordinatorHealth(state, p) {
  if (!state.paneId || !state.workspaceId || !state.agent?.kind) return { state: 'unavailable', reason: 'not recorded' };
  let agent;
  try {
    const reply = await herdr(['agent', 'get', state.paneId], p);
    if (reply?.result?.type !== 'agent_info') return { state: 'unavailable', reason: 'status unreadable' };
    agent = reply.result.agent;
  } catch (error) {
    if (['agent_not_found', 'pane_not_found'].includes(error.code)) return { state: 'unavailable', reason: 'missing' };
    if (error.code === 'server_not_running') return { state: 'unavailable', reason: 'Herdr is not running' };
    return { state: 'unavailable', reason: 'status unreadable' };
  }
  if (!agent || agent.pane_id !== state.paneId || agent.workspace_id !== state.workspaceId
    || !samePath(agent.cwd, state.cwd) || agent.agent !== state.agent.kind
    || state.ownerLaunch?.paneId === state.paneId && otherTerminal(state.ownerLaunch, agent)) {
    return { state: 'unavailable', reason: 'saved target does not match' };
  }
  if (!['working', 'starting', 'idle', 'blocked', 'done'].includes(agent.agent_status)) {
    return { state: 'unavailable', reason: 'state unknown' };
  }
  return { state: agent.agent_status };
}
async function openWorkspace(state, p) {
  if (!p.herdr) {
    const status = await herdr(['status', 'server', '--json'], p);
    if (!status.running) {
      const childEnv = Object.fromEntries(Object.entries(p.env).filter(([k]) => !/^(?:HERDR_|CLAUDECODE$|CLAUDE_CODE_|CODEX_THREAD_ID$|PDD_AGENT_SESSION$)/.test(k)));
      const startServer = () => new Promise((resolve, reject) => {
        const child = spawn('herdr', ['--session', SESSION, 'server'], { env: childEnv, cwd: state.cwd, detached: true, stdio: 'ignore' });
        child.once('error', reject); child.once('spawn', () => { child.unref(); resolve(); });
      });
      if (p.scanAction) await p.scanAction(startServer); else await startServer();
      for (let i = 0; i < 50; i++) {
        try { if ((await herdr(['status', 'server', '--json'], p)).running) break; } catch { /* startup */ }
        await new Promise(resolve => setTimeout(resolve, 100));
      }
    }
  }
  if (!state.paneId) {
    const create = () => herdr(['workspace', 'create', '--cwd', state.cwd, '--label', `${state.repo} Autopilot`, '--no-focus'], p);
    const reply = p.scanAction ? await p.scanAction(create) : await create();
    state.paneId = reply.result?.root_pane?.pane_id;
    state.workspaceId = reply.result?.workspace?.workspace_id;
    if (!state.paneId) throw Error('Herdr returned no pane; run herdr --help.');
    if (p.scanGuard && !await p.scanGuard(latest => { latest.paneId = state.paneId; latest.workspaceId = state.workspaceId; delete latest.ownerLaunch; })) throw Object.assign(Error('Autopilot control changed'), { code: 'agent_blocked' });
    delete state.ownerLaunch;
  }
}
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
async function comments(number, state, p, issue) {
  if (p.comments) return p.comments(number);
  // The intake of this tick, or a command just before it, read the same comments into the saved snapshot: when the
  // saved read has the change facts of this issue row, it is the current answer.
  const saved = issue && p.dependencySnapshot?.issues?.[number], version = issue ? issueRowVersion(issue) : null;
  if (saved && version !== null && saved.version === version && Array.isArray(saved.kinds?.comments) && saved.kinds.comments.length === issue.comments) return saved.kinds.comments;
  let endpoint = `repos/${state.repo}/issues/${number}/comments?per_page=100`; const rows = [];
  while (endpoint) {
    const r = await githubGet(endpoint, p);
    if (!Array.isArray(r.value)) throw Error('GitHub comments unavailable; retry next tick.');
    rows.push(...r.value); endpoint = r.link?.match(/<https:\/\/api\.github\.com\/([^>]+)>; rel="next"/)?.[1];
  }
  return rows;
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
const heartbeat = row => typeof row?.body === 'string' && withoutClaimHeartbeat(row.body) !== row.body;
const latestTime = values => values.map(value => Date.parse(value)).filter(Number.isFinite).reduce((last, at) => Math.max(last, at), -Infinity);
function parkingPorts(state, p, {localOnly = false} = {}) {
  const worker = {...p, isTTY: false, execFile: p.execFile ?? (async (file, args, options) => {
    const result = await p.execute(file, args, options);
    if (result.code !== 0) throw Object.assign(Error(`${file} failed`), result);
    return result;
  })};
  const args = run => ({ref: String(run.number), cwd: state.cwd, packageRoot: state.packageRoot,
    coordinatorId: state.coordinatorId, machine: state.machine});
  const parking = {
    now: p.now,
    list: () => listRuns({cwd: state.cwd}, worker),
    checkProgress: async run => {
      const busy = progress => ['waiting', 'running', 'unavailable'].includes(progress?.state);
      return busy((p.readSuiteProgress ?? readSuiteProgress)({cwd: run.root, env: p.env}, p))
        || busy((p.readInterpreterProgress ?? readInterpreterProgress)({cwd: run.root, env: p.env}, {now: p.now, ...p.interpreterQueuePorts}));
    },
    observeBlocker: async run => {
      if (run.blockedOn) return null;
      if (run.state === 'waiting' && run.gate?.kind === 'approve-pr' && !run.question && run.done?.check) {
        let checks;
        try {checks = (p.readRunResults ?? readRunResults)({root: run.root, runDir: run.runDir, runId: run.runId, since: run.startedAt ?? 0}, {env: p.env});}
        catch {return {kind: 'interpreter', until: null};}
        const check = checks.find(row => row.kind === 'pdd test');
        if (!check || ['none', 'unknown', 'service'].includes(checkCause(check.states)))
          return {kind: 'interpreter', until: null};
      }
      if (run.parking) return null;
      if (run.agent === state.agent.kind && state.health?.usage?.state === 'limited')
        return {kind: 'account', until: Number.isFinite(state.health.usage.resetAt) ? new Date(state.health.usage.resetAt).toISOString() : null};
      const chat = currentChat(run);
      if (!chat) return null;
      const health = await (p.chatHealth ?? chatHealth)({run, chat, live: await chatSession(chat, worker)}, worker);
      const reset = health?.until ?? health?.resetsAt;
      return health?.kind === 'usage-limit' ? {kind: 'account', until: Number.isFinite(reset) ? new Date(reset).toISOString() : null} : null;
    },
    park: async (run, blocker) => {
      let interpreterBatch = null, interpreterCheck;
      if (blocker.kind === 'interpreter' && !interpreterWaitFor({...run, parking: null})) {
        let check;
        try {check = (p.readRunResults ?? readRunResults)({root: run.root, runDir: run.runDir, runId: run.runId, since: run.startedAt ?? 0}, {env: p.env}).find(row => row.kind === 'pdd test');}
        catch { /* Unknown saved reads must never cause a blind resend. */ }
        interpreterBatch = check?.batch ?? null;
        interpreterCheck = {step: run.done?.check ?? null,
          result: check ? {batch: interpreterBatch, at: check.at ?? null, states: check.states ?? null} : null};
      }
      return p.scanAction(() => parkBlockedRun({...args(run), blocker, expected: run, interpreterBatch, interpreterCheck}, worker));
    },
    wake: (run, rule) => p.scanAction(() => wakeParkedRun({...args(run), at: run.parking.at,
      text: rule?.text ?? (run.parking.blocker.kind === 'pdd'
        ? `The installed PDD contains ${run.parking.blocker.until}. ${run.parking.blocker.until === '#2897' ? 'The PR 1 re-entry and current-main integration route now exists.' : 'The required fix is available.'} Continue this saved run from its retained work. Preserve approval gates and independent questions.` : undefined), expectedBlocker: run.parking.blocker},
      {...worker, parkingBlockerCleared: fresh => parking.blockerCleared(fresh, rule)})),
    blockerCleared: async (run, rule) => {
      const blocker = run.parking.blocker;
      if (['interpreter', 'environment'].includes(blocker.kind)) return Boolean(rule);
      if (blocker.kind === 'person') return Boolean(run.parking.personWait) && (hasParkedReply(run, worker) || !run.gate && (!run.question || Boolean(run.question.answeredAt)));
      if (['account', 'github'].includes(blocker.kind)) return Number.isFinite(Date.parse(blocker.until)) && p.now() >= Date.parse(blocker.until);
      if (blocker.kind === 'pdd') {
        const required = blocker.until === '#2897' ? 'capability:prompt-reentry' : /^#[1-9][0-9]*$/.test(blocker.until) ? `capability:issue-${blocker.until.slice(1)}` : blocker.until;
        if (typeof required !== 'string') return false;
        if (required.startsWith('capability:')) return (p.installedPddCapabilities ?? WORKFLOW_CAPABILITIES).includes(required.slice(11));
        if (/^commit:[a-f0-9]{7,40}$/.test(required)) {
          try {
            const result = await p.execute('git', ['merge-base', '--is-ancestor', required.slice(7), 'HEAD'], {cwd: dirname(dirname(self))});
            return result.code === 0;
          } catch {return false;}
        }
        return false;
      }
      if (localOnly) return false;
      if (p.blockerCleared) return await p.blockerCleared(run, blocker) === true;
      if (blocker.kind === 'dependency') {
        // A closed issue alone is not proof of a merge.
        const issue = await p.execute('gh', ['api', `repos/${state.repo}/issues/${blocker.until}`], {purpose: 'dependencies'});
        if (issue.code !== 0 || JSON.parse(issue.stdout).state !== 'closed') return false;
        const result = await p.execute('gh', ['api', `repos/${state.repo}/issues/${blocker.until}/timeline?per_page=100`, '--paginate', '--slurp'], {purpose: 'dependencies'});
        if (result.code !== 0) return false;
        const pages = JSON.parse(result.stdout);
        for (const event of pages.flat()) {
          const pull = event.source?.issue;
          if (event.event !== 'cross-referenced' || !pull?.pull_request?.url || !pull.pull_request.url.startsWith(`https://api.github.com/repos/${state.repo}/pulls/`)) continue;
          const reply = await p.execute('gh', ['api', pull.pull_request.url], {purpose: 'dependencies'});
          if (reply.code === 0) {const pr = JSON.parse(reply.stdout); if (pr.merged === true && closingIssues(pr.body, state.repo).includes(Number(blocker.until))) return true;}
        }
        return false;
      }
      if (['ci', 'review'].includes(blocker.kind)) {
        const pr = run.pr?.at(-1);
        if (!pr?.url) return false;
        const result = await p.execute('gh', ['pr', 'view', pr.url, '--json', 'state,statusCheckRollup,reviewDecision'], {purpose: 'reviews'});
        if (result.code !== 0) return false;
        const row = JSON.parse(result.stdout);
        return row.state === 'MERGED' || (blocker.kind === 'review' ? ['APPROVED', 'CHANGES_REQUESTED'].includes(row.reviewDecision)
          : row.statusCheckRollup?.length > 0 && row.statusCheckRollup.every(check => check.status === 'COMPLETED' || ['SUCCESS', 'FAILURE', 'ERROR'].includes(check.state)));
      }
      return false;
    },
    alertUnknown: async run => {
      const send = p.sendAlert ?? (input => runAutopilotAlerts({action: 'alert', cwd: state.cwd, env: p.env, ...input},
        {...p.alertPorts, repository: async () => ({nameWithOwner: state.repo}), stateRoot: dirname(state.stateFile), now: p.now}));
      try {return (await send({issue: String(run.number), kind: 'stuck', text: JSON.stringify({
        cause: run.parkReason ?? 'No named blocker is saved.', tried: 'Kept the run, claim and saved work.', need: 'Identify the blocker before continuing.'})}))?.exitCode === 0;}
      catch {return false;}
    },
    release: async run => p.scanAction(async () => {
      const result = await releaseParkedRun({...args(run), runId: run.runId, at: run.parking.at}, {
        ...worker, releaseParkedClaim: fresh => {
          const claim = {...fresh.automaticOrigin.claim, issue: fresh.issue.url, coordinatorId: state.coordinatorId, machine: state.machine};
          return (p.releaseParkedClaim ?? releaseParkedClaim)({cwd: state.cwd, repository: state.repo, claim,
            coordinatorId: state.coordinatorId, machine: state.machine, runId: fresh.runId, branch: fresh.branch},
            {...worker, execFile: async (file, args, options) => p.execute(file, args, {...options, purpose: 'claims'})});
        },
      });
      return result.recovery === 'released';
    }),
  };
  return parking;
}
async function parkingTick(state, p, config, options = {}) {
  try {
    const ports = parkingPorts(state, p, options);
    state.parking = await reconcileParking(state, ports, {...options, policy: config.parking, release: !options.localOnly});
    state.parkedNumbers = (await ports.list()).filter(run => run.parking && !['completed', 'cancelled'].includes(run.state)).map(run => run.number);
    await p.scanGuard(latest => {latest.parking = state.parking; latest.parkedNumbers = state.parkedNumbers; latest.parkingAlerts = state.parkingAlerts;});
  } catch (error) { p.warn(`Parking reconciliation held: ${line(error.message)}`); }
}

async function resumeStoppedWorkers(state, p, recoveredRuns = null) {
  const execFile = p.execFile ?? (async (file, args, options) => {
    const result = await p.execute(file, args, options);
    if (result.code !== 0) throw Object.assign(Error(`${file} failed`), result);
    return result;
  });
  const workerPorts = {...p, execFile, isTTY: false};
  let runs;
  try { runs = await listRuns({cwd: state.cwd}, workerPorts); }
  catch (error) { p.warn(`Stopped-chat inspection unavailable: ${line(error.message)}`); return; }
  for (const run of runs) {
    if (recoveredRuns && !recoveredRuns.has(run.runDir)) continue;
    if (run.repo?.toLowerCase() !== state.repo.toLowerCase() || !samePath(run.sourceRoot, state.cwd)
      || run.automaticOrigin?.coordinatorId !== state.coordinatorId || run.automaticOrigin?.machine !== state.machine) continue;
    if (run.parking) continue;
    try {
      const result = await p.scanAction(() => resumeStoppedRun({ref: String(run.number), cwd: state.cwd,
        packageRoot: state.packageRoot, coordinatorId: state.coordinatorId, machine: state.machine}, workerPorts));
      if (result.recovery === 'stuck') {
        const send = p.sendAlert ?? (input => runAutopilotAlerts({action: 'alert', cwd: state.cwd, env: p.env, ...input},
          {...p.alertPorts, repository: async () => ({nameWithOwner: state.repo}), stateRoot: dirname(state.stateFile), now: p.now}));
        await send({issue: String(run.number), kind: 'stuck', text: JSON.stringify({cause: result.message,
          tried: 'Three automatic resumes through workflow open in one hour.', need: 'Inspect the stopped chat and resume the run manually.'})});
      } else if (result.exitCode !== 0) p.warn(`Stopped-chat recovery held for #${run.number}: ${line(result.message)}`);
      const idle = await p.scanAction(() => nudgeIdleRun({ref: String(run.number), cwd: state.cwd,
        packageRoot: state.packageRoot, coordinatorId: state.coordinatorId, machine: state.machine}, workerPorts));
      if (idle.recovery === 'stuck') {
        const send = p.sendAlert ?? (input => runAutopilotAlerts({action: 'alert', cwd: state.cwd, env: p.env, ...input},
          {...p.alertPorts, repository: async () => ({nameWithOwner: state.repo}), stateRoot: dirname(state.stateFile), now: p.now}));
        await send({issue: String(run.number), kind: 'stuck', text: JSON.stringify({cause: idle.message,
          tried: 'Three continue prompts without recorded step progress.', need: 'Inspect the idle agent and continue the run manually.'})});
      } else if (idle.exitCode !== 0) p.warn(`Idle-agent recovery held for #${run.number}: ${line(idle.message)}`);
    } catch (error) { p.warn(`Stopped-chat recovery held for #${run.number}: ${line(error.message)}`); }
  }
}

async function readRunProgress(state, p) {
  const commonDir = (await p.checked('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'])).trim();
  const folder = join(commonDir, 'pdd', 'runs');
  let names;
  try { names = readdirSync(folder); } catch { return []; }
  const progress = [];
  for (const name of names) {
    if (!/^[1-9][0-9]*$/.test(name)) continue;
    try {
      const file = join(folder, name, 'status.json'), run = read(file);
      if (run?.v === 1 && run.number === Number(name) && run.repo?.toLowerCase() === state.repo.toLowerCase() && ['running', 'waiting'].includes(run.state)) {
        const changedAt = Number.isFinite(run.progressAt) ? run.progressAt : statSync(file).mtimeMs;
        const suite = (p.readSuiteProgress ?? readSuiteProgress)({cwd:run.root, since:changedAt, env:p.env}, p);
        if (suite?.state === 'unavailable') p.warn(`Run #${run.number} full test suite queue unavailable: ${suite.reason}`);
        const interpreter = typeof run.root === 'string' ? (p.readInterpreterProgress ?? readInterpreterProgress)({ cwd: run.root, since: changedAt, env: p.env }, { now: p.now, ...p.interpreterQueuePorts }) : null;
        progress.push({ number: run.number, changedAt: changedAt + (suite?.pausedMs ?? 0) + (interpreter?.pausedMs ?? 0), ...(suite ? {suite} : {}), ...(interpreter ? {interpreter} : {}) });
      }
    } catch { /* Missing or unreadable records supply no progress fact. */ }
  }
  return progress;
}
// Whether this checkout's run of the issue stopped at the Autopilot repair limit (#3041).
async function readRepairLimited(state, number, p) {
  try {
    const commonDir = (await p.checked('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'])).trim();
    const run = read(join(commonDir, 'pdd', 'runs', String(number), 'status.json'));
    return run?.v === 1 && run.number === number && run.repo?.toLowerCase() === state.repo.toLowerCase() && run.state === 'stuck' && Boolean(run.repairLimit);
  } catch { return false; }
}
// Runs that wait for the interpreter (pdd workflow park --interpreter), from the same local run records.
async function readRuntimeWaits(state, p) {
  const commonDir = (await p.checked('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'])).trim();
  const folder = join(commonDir, 'pdd', 'runs');
  let names;
  try { names = readdirSync(folder); } catch { return []; }
  const waits = [];
  for (const name of names) {
    if (!/^[1-9][0-9]*$/.test(name)) continue;
    try {
      const run = read(join(folder, name, 'status.json')), wait = run && interpreterWaitFor(run);
      if (run?.v === 1 && run.number === Number(name) && run.repo?.toLowerCase() === state.repo.toLowerCase()
        && (run.runtimeWait || run.automaticOrigin?.coordinatorId === state.coordinatorId && run.automaticOrigin?.machine === state.machine)
        && blockerFor(run)?.kind === 'interpreter' && Number.isFinite(wait?.at))
        {
          let batch = typeof wait.batch === 'string' ? wait.batch : null, resend = null, held = false;
          const seen = new Set();
          while (batch) {
            const next = (run.checkResends ?? []).findLast(row=>row.oldBatch===batch && row.state!=='authorized');
            if (!next) break;
            if (seen.has(batch) || !next.newBatch) {held=true;break;}
            seen.add(batch);resend=next;batch=next.newBatch;
          }
          // The retained park belongs to the old attempt; follow its recorded replacement receipts.
          if (held) continue;
          const cause = resend ? resend.state==='verdict' && ['passed','issue'].includes(savedCheckCause(batch,{env:p.env})) ? 'verdict' : 'unknown' : wait.cause ?? 'unknown';
          waits.push({number:run.number,at:wait.at,batch,cause,cost:savedLostCheck(batch,{env:p.env,root:run.root})?.cost ?? null,mark:`${run.area}:${Object.keys(run.done ?? {}).length}`});
        }
    } catch { /* Missing or unreadable records supply no wait. */ }
  }
  return waits;
}
// Only this coordinator's own automatic environment stops are retry candidates.
async function readEnvironmentWaits(state, p) {
  const commonDir = (await p.checked('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'])).trim();
  const folder = join(commonDir, 'pdd', 'runs');
  let names;
  try { names = readdirSync(folder); } catch { return []; }
  const waits = [];
  for (const name of names.filter(name => /^[1-9][0-9]*$/.test(name))) {
    try {
      const run = read(join(folder, name, 'status.json')), origin = run?.automaticOrigin;
      if (run?.v !== 1 || run.number !== Number(name) || run.repo?.toLowerCase() !== state.repo.toLowerCase()
        || origin?.coordinatorId !== state.coordinatorId || origin.machine !== state.machine) continue;
      const retry = environmentRecovery(run);
      if (retry) waits.push({ number: run.number, ...retry });
    } catch { /* Unavailable records cannot authorize a retry. */ }
  }
  return waits;
}
async function environmentTick(state, p, waits, timeRules, pendingTimes, stateRoot) {
  for (const retry of waits.sort((a, b) => a.at - b.at || a.number - b.number)) {
    if (retry.attempts >= ENVIRONMENT_BACKOFF.length) {
      const send = p.sendAlert ?? (input => runAutopilotAlerts({ action: 'alert', cwd: state.cwd, env: p.env, ...input },
        { ...p.alertPorts, repository: async () => ({ nameWithOwner: state.repo }), stateRoot, now: p.now }));
      try {
        await send({ issue: String(retry.number), kind: 'stuck', text: JSON.stringify({
          cause: `Environment validation failure: ${retry.reason}`,
          tried: `${ENVIRONMENT_BACKOFF.length} bounded retries of ${retry.step}; the run and evidence are preserved.`,
          need: `Restore the environment before resuming validation ${retry.step}. No product decision is required.` }) });
      } catch { /* Alert custody owns failed/unconfirmed delivery; retry on a later tick. */ }
      continue;
    }
    const tag = environmentWakeTag(retry), key = `environment:${retry.number}`, offer = `${tag}:${Math.floor(p.now() / INTERVAL)}`;
    if (p.now() < retry.nextAt || state.timeSeen[key] === offer) continue;
    let healthy = false;
    try {
      healthy = await (p.environmentHealthy ?? (input => environmentHealthy(input, {
        ...p, suiteLimit:state.checkCapacity?.checks, machineResources: async () => state.health?.resource?.resources,
      })))({ env: p.env, reason: retry.reason, cwd: state.cwd });
    } catch { /* Unknown health blocks. */ }
    if (!healthy) continue;
    const text = `${tag} Rerun only the failed validation step ${retry.step}, using its original command and retained evidence. Preserve completed work, area, gates, branch and claim. Do not restart the run or replay build, approvals, publication or any external operation with an unknown outcome. If it fails again, classify its actual cause and park it with --step ${retry.step}.`;
    timeRules.push({ kind: 'environment-ready', text, number: retry.number, step: retry.step, attempt: retry.attempts + 1, limit: ENVIRONMENT_BACKOFF.length, nextAt: retry.nextAt,
      reason: `Host health and suite capacity permit validation retry. As worker room allows, deliver this exact text with pdd workflow changes ${retry.number}: ${JSON.stringify(text)}` });
    pendingTimes[key] = offer;
  }
}
function healthLine(health) {
  if (!health || !Number.isFinite(health.at) || Math.abs(health.at) > 8.64e15 || typeof health.paused !== 'boolean'
    || typeof health.resource?.healthy !== 'boolean' || !['healthy', 'limited', 'unknown', 'not-applicable'].includes(health.usage?.state)
    || !Array.isArray(health.resource?.causes) || health.resource.causes.some(cause => typeof cause !== 'string')
    || health.usage?.resetAt != null && (!Number.isFinite(health.usage.resetAt) || Math.abs(health.usage.resetAt) > 8.64e15)) return 'Health: unknown (no observation)';
  const usage = health.usage;
  return `Health: ${health.paused ? 'paused' : 'healthy'} at ${new Date(health.at).toISOString()}; ${(health.resource?.causes ?? []).join('; ') || 'memory and disk healthy'}; Codex ${usage?.state ?? 'unknown'}${usage?.usedPercent == null ? '' : ` ${usage.usedPercent}%`}${usage?.resetAt == null ? '' : `; reset ${new Date(usage.resetAt).toISOString()}`}`;
}
async function observeHealth(state, p) {
  const old = state.health;
  let resource, usage = { state: 'not-applicable', resetAt: null, usedPercent: null };
  try { resource = await (p.machineHealth ?? (input => machineHealth(input, { machineResources: p.machineResources ?? (input => readMachineResources(input, {includeChecks:true,env:p.env})) })))({ cwd: state.cwd }); }
  catch { resource = { healthy: false, causes: ['Machine resources cannot be read'], resources: null }; }
  if (state.agent.kind === 'codex') {
    const definition = launchDefinition(state, p), profile = profileBinding(state, p);
    const env = { ...p.env, ...definition.env, HOME: profile.home };
    if (profile.configHome) env.CODEX_HOME = profile.configHome; else delete env.CODEX_HOME;
    try { usage = await (p.codexLimits ?? readCodexLimits)({ command: definition.command, cwd: state.cwd, env }); }
    catch { usage = { state: 'unknown', resetAt: null, usedPercent: null }; }
  }
  const paused = resource?.healthy !== true || !['healthy', 'not-applicable'].includes(usage?.state);
  state.health = { at: p.now(), paused, resource, usage, incidents: old?.incidents ?? {},
    recoveryPending: paused ? null : old?.recoveryPending ?? (old?.paused ? p.now() : null) };
}
async function healthAlerts(state, p, stateRoot) {
  const health = state.health, issues = [...new Set([
    ...Object.values(health.incidents), ...(state.githubIntake?.claims ?? []).map(claim => Number(/\/issues\/(\d+)$/.exec(claim.issue)?.[1])),
    ...(state.cachedIssues ?? []).filter(issue => !issue.pull_request).map(issue => issue.number),
  ].filter(number => Number.isSafeInteger(number) && number > 0))];
  const send = p.sendAlert ?? (input => runAutopilotAlerts({ action: 'alert', cwd: state.cwd, env: p.env, ...input },
    { ...p.alertPorts, repository: async () => ({ nameWithOwner: state.repo }), stateRoot, now: p.now }));
  const alert = async (issue, kind, fields) => {
    try { const reply = await send({ issue: String(issue), kind, text: JSON.stringify(fields) }); return reply?.exitCode === 0; }
    catch { return false; }
  };
  for (const kind of ['resource', 'usage-limit']) {
    const healthy = kind === 'resource' ? health.resource?.healthy === true : ['healthy', 'not-applicable'].includes(health.usage?.state);
    if (healthy) {
      if (health.incidents[kind] && await alert(health.incidents[kind], 'recovered', { kind, cause: kind === 'resource' ? 'Memory and disk are available again' : 'The Codex limit read permits work again' })) delete health.incidents[kind];
    } else if (issues.length) {
      health.incidents[kind] ??= issues[0];
      const cause = kind === 'resource' ? (health.resource?.causes ?? ['Machine resources cannot be read']).join('; ')
        : `Codex usage ${health.usage?.state === 'limited' ? 'limit reached' : 'cannot be read'}${health.usage?.resetAt == null ? '' : `; resets ${new Date(health.usage.resetAt).toISOString()}`}`;
      for (const number of issues) await alert(number, kind, { cause, tried: 'Paused new admissions; kept claims, progress and heartbeats',
        need: kind === 'resource' ? 'Free disk space or memory; the tick checks again' : 'Wait for the ordinary usage window; the tick reads the limit again' });
    }
  }
}

// The proof of a test wake is a verdict saved after the wake was offered.
async function readRuntimeProbe(state, p, probe) {
  const commonDir = (await p.checked('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'])).trim();
  let run = null;
  try { run = read(join(commonDir, 'pdd', 'runs', String(probe.number), 'status.json')); } catch { /* No fact at this tick. */ }
  if (run?.v !== 1 || run.number !== probe.number || run.repo?.toLowerCase() !== state.repo.toLowerCase()) return 'pending';
  if (typeof run.root === 'string' && checkVerdictSince({ root: run.root, since: probe.offeredAt }, { env: p.env })) return 'verdict';
  if (run.state === 'paused' && run.runtimeWait?.at > probe.at) return 'failed';
  if (run.parking?.blocker.kind === 'interpreter' && interpreterWaitFor(run)?.at === probe.at) return 'pending';
  return ['running', 'waiting', 'paused'].includes(run.state) ? 'pending' : 'failed';
}
const RUNTIME_KEEP = 24 * 60 * 60 * 1000, RUNTIME_ACCESS_LIMIT = 4 * 60 * 60 * 1000, RUNTIME_PROBE_LIMIT = 60 * 60 * 1000;
const RUNTIME_TRIED = 'pdd retried each call up to 3 times. The runs wait for the interpreter and keep their claims, branches and progress; other work goes on.';
const RUNTIME_NEED = 'No action now. Autopilot checks the interpreter at each tick without AI. When it answers again, Autopilot wakes the oldest waiting run as a test and wakes the others after its check reaches a verdict. Look at the PDD interpreter if this lasts.';
const ACCESS_TRIED = 'Autopilot checks the interpreter at each tick without AI. The runs wait for the interpreter, keep their claims, branches and progress, and resend nothing; other work goes on.';
function runtimeWake(wait, kind) {
  const read = `pdd test --read${wait.batch ? ` ${wait.batch}` : ''}`;
  const why = kind === 'retry' ? 'The interpreter answers its health check and no outage is open, so this is a problem of this issue only: this wake is its one retry. If the same step waits for the interpreter again, it follows the stuck rule.'
    : kind === 'probe' ? 'The interpreter answers again after an outage. This oldest run is the test: the other waiting runs wake only after its check reaches a verdict.'
    : 'The interpreter is back.';
  // pdd test --retry resends only the checks that pdd names it for (busy or held); a fresh check of the Story sends the others.
  const again = 'check that Story once again with pdd test STORY --max-calls N';
  if (wait.cause === 'verdict') return `Run #${wait.number} has its person-authorized resend verdict. When a worker slot is free (oldest first), wake it with pdd workflow changes ${wait.number} and this text: "${runtimeWakeTag(wait.at)} First run ${read} once. Continue from that saved verdict. Send no new check."`;
  const resend = wait.cause === 'unknown' ? `Its last check has an unknown outcome: never send it again blind. If the read now shows not run (nothing was sent), ${again}; if it is still unknown, follow the stuck rule.`
    : wait.cause === 'none' ? 'No check result was saved, so no check ran: send the check again once.'
    : `Resend only a check that surely gave no verdict: pdd test --retry ${wait.batch ?? 'BATCH'} only when pdd names it (busy or held checks); for another not run check or an AI-service refusal, ${again}. Never resend a failed (✗) check.`;
  return `Run #${wait.number} waits for the interpreter. ${why} When a worker slot is free (oldest first), wake it with pdd workflow changes ${wait.number} and this text: "${runtimeWakeTag(wait.at)} ${kind === 'retry' ? 'The interpreter answers again.' : 'The interpreter is back.'} First run ${read} once and read each Story line. ${resend} Keep --max-calls."`;
}
// The no-AI interpreter part of a tick: one free health check while a run waits for the interpreter, or an outage or a
// interpreter access problem is open. Every run resends its check at most once per wait, and every path ends in a
// wake or in the stuck rule.
async function runtimeTick(state, p, completion, timeRules, pendingTimes, stateRoot) {
  const allWaits = (await (p.readRuntimeWaits ?? readRuntimeWaits)(state, p)).sort((a, b) => a.at - b.at || a.number - b.number);
  const lostWaits = allWaits.filter(wait=>wait.cause === 'unknown');
  const waits = allWaits.filter(wait=>wait.cause !== 'unknown');
  const saved = state.runtime ?? {}, now = p.now();
  let lostDecision = lostWaits.length ? saved.lostDecision : null;
  const pattern = state.interpreterPattern ?? {streak: 0, seen: {}};
  const hadTestMode = Boolean(pattern.testMode);
  let verdictAt = null;
  if (p.readInterpreterVerdict) {
    const verdict = await p.readInterpreterVerdict(pattern.verdictAt ?? 0);
    verdictAt = verdict === true ? now : Number.isFinite(verdict) ? verdict : null;
  } else if (!p.readRuntimeWaits) {
    const runs = await parkingPorts(state, p).list();
    for (const run of runs) {
      if (typeof run.root !== 'string' || !run.root.trim()) continue;
      const at = latestCheckVerdict({root: run.root, since: pattern.verdictAt ?? 0}, {env: p.env});
      if (at !== null) verdictAt = Math.max(verdictAt ?? at, at);
    }
  }
  pattern.observedAt = now;
  if (verdictAt === null && pattern.testMode && saved.outage?.probe
    && await (p.readRuntimeProbe ?? readRuntimeProbe)(state, p, saved.outage.probe) === 'verdict') verdictAt = now;
  if (verdictAt !== null && verdictAt > (pattern.verdictAt ?? -Infinity)) {
    pattern.verdictAt = verdictAt;
    pattern.streak = Object.keys(pattern.seen).filter(key => Number(key.slice(key.lastIndexOf(':') + 1)) > verdictAt).length;
    pattern.testMode = pattern.streak >= 3;
  }
  for (const wait of allWaits) {
    const key = `${wait.number}:${wait.at}`;
    if (wait.at <= (pattern.verdictAt ?? -Infinity)) continue;
    if (!pattern.seen[key] && !(saved.retried?.[wait.number]?.mark === wait.mark && saved.retried[wait.number].at < wait.at) && ['service', 'none', 'unknown'].includes(wait.cause)) {pattern.seen[key] = now; pattern.streak++;}
  }
  pattern.seen = Object.fromEntries(Object.entries(pattern.seen).filter(([, at]) => now - at < RUNTIME_KEEP));
  if (pattern.streak >= 3) pattern.testMode = true;
  state.interpreterPattern = pattern;
  if (pattern.testMode || hadTestMode) await (p.configureInterpreterTestMode ?? configureInterpreterTestMode)({env: p.env, owner: state.stateFile, enabled: Boolean(pattern.testMode)}, {now: p.now, ...p.interpreterQueuePorts});
  // A wake is kept while its run works on it, so a second wait of the same step is seen; a recovery keeps it too.
  const retried = Object.fromEntries(Object.entries(saved.retried ?? {}).filter(([, value]) => now - value.at < RUNTIME_KEEP));
  let outage = saved.outage ? structuredClone(saved.outage) : null, access = saved.access ? structuredClone(saved.access) : null;
  const keep = () => {
    state.runtime = { ...(lostDecision ? {lostDecision} : {}), ...(outage ? { outage } : {}), ...(access ? { access } : {}), ...(Object.keys(retried).length ? { retried } : {}) };
    if (!Object.keys(state.runtime).length) delete state.runtime;
  };
  if (!allWaits.length && !outage && !access) return keep();
  const health = await (p.runtimeHealth ?? (async input => (await import('./runtime-client.mjs')).checkRuntimeHealth(input)))({ env: p.env });
  const send = p.sendAlert ?? (input => runAutopilotAlerts({ action: 'alert', cwd: state.cwd, env: p.env, ...input },
    { ...p.alertPorts, repository: async () => ({ nameWithOwner: state.repo }), stateRoot, now: p.now }));
  const alert = async (number, kind, fields) => { try { await send({ issue: String(number), kind, text: JSON.stringify(fields) }); } catch { /* The alert record is best effort; work goes on. */ } };
  if (health.state === 'healthy' && lostWaits.length) {
    const identity = JSON.stringify(lostWaits.map(w=>[w.number,w.batch]).sort((a,b)=>a[0]-b[0]));
    if (lostDecision !== identity) {
      const details = lostWaits.map(w=>`#${w.number}: ${w.batch ?? 'batch unknown'}; AI calls: ${w.cost?.calls ?? `unknown (at least ${w.cost?.knownCalls ?? 0})`}`).join('; ');
      try {
        const result = await send({issue:String(lostWaits[0].number),kind:'decision',update:true,text:JSON.stringify({
          cause:`The interpreter answers again. Lost check verdicts: ${details}.`,
          tried:'The saved receipts are retained. No lost check was resent.',
          need:`One person decision for all listed runs: pdd workflow resend ${lostWaits.map(w=>w.number).join(' ')} --said - with the person's words. Each decision permits one resend; another no-verdict stops immediately.`})});
        if (result?.exitCode === 0) lostDecision = identity;
      } catch { /* A failed alert can be retried. It grants no send authority. */ }
    }
  }
  // The first call opens the one incident of this repository and machine; later calls join it or resend a failed alert.
  const incident = async (record, kind, fields) => {
    for (const number of [record.first, ...allWaits.map(w => w.number).filter(n => n !== record.first && !record.issues.includes(n))]) {
      await alert(number, kind, fields);
      if (!record.issues.includes(number)) record.issues.push(number);
    }
  };
  // A wake (retry, test or recovery) is used when the same step waits again after it, unless that wait began while
  // the interpreter was down: then the outage, not the issue, explains it.
  const used = w => retried[w.number]?.mark === w.mark && retried[w.number].at < w.at && outage?.down?.[w.number] !== w.at;
  const wake = [], stuck = [];
  const offer = (w, kind) => { wake.push([w, kind]); retried[w.number] = { mark: w.mark, at: w.at, kind }; };
  if (health.state === 'access') {
    // Not healthy and not down: a sign-in or setup problem that a person must fix. Wake nothing and resend nothing.
    access ??= { since: now, issues: [] };
    access.first ??= allWaits[0]?.number ?? outage?.first;
    Object.assign(access, { detail: health.detail, fix: health.fix });
    if (access.first) await incident(access, 'interpreter-access', { cause: `The free interpreter health check cannot be read (${health.detail}). This is a sign-in or setup problem on this machine, not an interpreter outage.`, tried: ACCESS_TRIED, need: `${health.fix} After 4 hours other waiting runs follow the stuck rule; lost-verdict runs stay parked for a person decision.` });
    for (const w of waits) if (now - Math.max(w.at, access.since) >= RUNTIME_ACCESS_LIMIT)
      stuck.push([w, `Run #${w.number} has waited 4 hours for the interpreter, and the free health check still cannot be read (${health.detail}).`]);
  } else if (access && health.state === 'healthy') {
    // A down answer does not show that the sign-in works again; only a healthy answer ends the access problem.
    if (access.first) await alert(access.first, 'recovered', { cause: `The free interpreter health check answers again (${health.detail}).`, kind: 'interpreter-access' });
    access = null;
  }
  if (pattern.testMode && !outage && allWaits.length) outage = {since: now, first: allWaits[0].number, issues: [], probed: [], detail: 'Three consecutive checks gave no verdict.'};
  // Only a failed health check opens an outage. Waits of several issues while the interpreter is healthy are not one.
  if (health.state === 'unavailable' && !outage && allWaits.length)
    outage = { since: now, first: allWaits[0].number, issues: [], probed: [], detail: `The free interpreter health check failed (${health.detail}).` };
  if (outage) await incident(outage, 'interpreter', { cause: outage.detail, tried: RUNTIME_TRIED, need: RUNTIME_NEED });
  // A wait first seen while the interpreter is down began in the outage; a wait already found used while healthy stays used.
  if (outage && health.state === 'unavailable') outage.down = { ...outage.down, ...Object.fromEntries(waits.filter(w => retried[w.number]?.again !== w.at).map(w => [w.number, w.at])) };
  if (health.state === 'healthy') {
    let recovered = null;
    if (outage) {
      // One test wake at a time, at most one for each run in this outage. It passes only with a new verdict.
      outage.probed ??= [];
      const probe = outage.probe;
      if (probe) {
        const result = await (p.readRuntimeProbe ?? readRuntimeProbe)(state, p, probe);
        const again = waits.some(w => w.number === probe.number && w.at > probe.at);
        if (result === 'verdict') recovered = 'verdict';
        // A test run that waits again, ends or goes stuck failed; one that gives no verdict within an hour of its wake
        // failed too, also when the wake was never delivered and the run still waits.
        else if (result === 'failed' || again || now - probe.offeredAt >= RUNTIME_PROBE_LIMIT) delete outage.probe;
      }
      if (!recovered && !outage.probe) {
        const open = waits.filter(w => !used(w) && !outage.probed.includes(w.number)), next = open.find(w => w.cause !== 'unknown') ?? open[0];
        if (next) { outage.probe = { number: next.number, at: next.at, offeredAt: now }; outage.probed.push(next.number); }
        else if (!pattern.testMode) recovered = 'untested';
      }
      const current = !recovered && outage.probe && waits.find(w => w.number === outage.probe.number && w.at === outage.probe.at);
      if (current) offer(current, 'probe');
    }
    for (const w of waits) {
      if (wake.some(([item]) => item === w)) continue;
      if (used(w)) { retried[w.number].again = w.at; stuck.push([w, `Run #${w.number} waits for the interpreter again at the same step after its one resend, and the interpreter is healthy.`]); }
      else if (recovered) offer(w, 'recovered');
      else if (!outage) offer(w, retried[w.number]?.at === w.at ? retried[w.number].kind : 'retry');
    }
    if (recovered) {
      const count = wake.length;
      const woken = `Autopilot wakes ${count} waiting run${count === 1 ? '' : 's'}, oldest first`;
      await alert(outage.first, 'recovered', { kind: 'interpreter', cause: recovered === 'verdict'
        ? `The interpreter is back: the free health check passed and a test check reached a verdict again. ${woken}.`
        : `The free health check passes again, and no waiting run is left to test. ${woken}; a run that failed its test follows the stuck rule.` });
      outage = null;
    }
  }
  for (const [w, kind] of wake) {
    const key = `runtime:${w.number}`, value = `${w.at}:${kind}`;
    // A capacity handoff frees a slot: offer a still-waiting run again. pdd delivers one wake per park.
    if (state.timeSeen[key] === value && !completion) continue;
    timeRules.push({ kind: 'runtime-ready', number: w.number, reason: runtimeWake(w, kind), text: runtimeWake(w, kind).split('and this text: \"')[1]?.slice(0, -1) });
    pendingTimes[key] = value;
  }
  for (const [w, why] of stuck) {
    const key = `runtime:${w.number}`, value = `${w.at}:stuck`;
    if (state.timeSeen[key] === value) continue;
    timeRules.push({ kind: 'runtime-stuck', number: w.number, reason: `${why} Follow the pdd:stuck rule: the label, one comment with the cause, one stuck alert, and pdd workflow park --reason TEXT in its worktree.` });
    pendingTimes[key] = value;
  }
  keep();
}
// The packet's interpreter fact while an outage or an access problem is open.
function runtimePacket(runtime) {
  const { outage, access } = runtime ?? {};
  const problem = access ? `The interpreter cannot be checked (${access.detail}): a sign-in or setup problem that a person must fix. ${access.fix} Autopilot sent one interpreter-access alert. Waiting runs stay parked and resend nothing; after 4 hours each follows the stuck rule.` : '';
  if (outage) return { state: outage.probe ? 'testing' : 'unavailable', since: new Date(outage.since).toISOString(),
    note: `${outage.probe ? `The interpreter answers again; run #${outage.probe.number} is the test, and the other waiting runs wake after its check reaches a verdict.` : 'The interpreter is unavailable.'} Keep other work moving: code, native tests, CI, merges, dependency reviews and claims. New issues may start; a worker parks only at its interpreter check with pdd workflow park --interpreter.${problem ? ` ${problem}` : ''}` };
  if (access) return { state: 'access', since: new Date(access.since).toISOString(), detail: access.detail, note: `${problem} Keep other work moving.` };
  return null;
}
function message(state, issues, timeRules = []) {
  const skillPath = resolve(state.packageRoot ?? dirname(dirname(self)), 'skills', 'pdd-autopilot', 'SKILL.md');
  const variable = { codex: 'CODEX_HOME', claude: 'CLAUDE_CONFIG_DIR', gemini: 'GEMINI_CLI_HOME' }[state.agent.kind];
  const path = variable && state.environment?.[variable] || null;
  const workflow = { baseBranch: state.baseBranch, pddBin: join(state.packageRoot ?? dirname(dirname(self)), 'bin', 'pdd.mjs'), agent: state.agent.kind, home: state.environment?.HOME, configHome: path ? { variable, path } : null };
  const start = state.startAction?.mode === state.currentMode && state.startAction?.repository === state.repo ? state.startAction : null;
  const authority = start ? `The operator invoked pdd autopilot start for ${state.repo} in ${state.currentMode} mode. ${state.currentMode === 'auto' ? 'This action establishes scope for ordinary eligible work and automatic merge under the repository review, testing, strict approval and other rules.' : 'Follow observe mode limits.'} This is an operator action, not a quoted person reply or checker approval. Use the existing supported approval routes for the actual action where applicable; never treat it as a later person reply.\n` : '';
  return `Read and follow the bundled skill at ${JSON.stringify(skillPath)} and its relative supporting files. ${authority}When recipeFirst is true, follow its bounded startup readiness, then dependency review, room, pdd:working claim and stuck-run rules. Inspect claimed issues for progress and stale claims; do not treat them as unclaimed work. An item with expiredClaim has an expired claim; take it over only under the skill's expired-claim rule. For an item with retry, continue the existing run: pass retry.text unchanged through pdd workflow changes N as worker room allows and resume only the failed step from retained evidence. Preserve gates, questions, completed work and repair ceilings; never start another run for that signal. The packet contains only trusted text; further issue/comment reads must preserve that boundary. Use the skill's pdd-check and pdd-merge handoffs for review and merge work. Run each repository's full-suite validation through ${quote(process.execPath)} ${quote(workflow.pddBin)} workflow suite --command COMMAND, with its actual command. Use the same queue for full builds. Claim new issues only within the packet working-runs cap. Parked runs use no working slot. Resume parking.wakePending in order before new issues. Same files are fine; update each PR from its base before merge. A same-root-cause-group issue joins the existing group's run, including a parked run. Wait for the shared queue result; slot waiting is not stuck. A suite-failed rule needs diagnosis and one test-suite alert with its specific cause, not pdd:stuck. The automatic base is ${JSON.stringify(state.baseBranch)}. Use it for every automatic start; never select a base from repository documents. For an issue you start, pass its decisionId with --origin autopilot --decision-id TOKEN to pdd workflow run; pass --outcome code or prompt-only when the required outcome is known.\n${JSON.stringify({ repository: state.repo, baseBranch: state.baseBranch, coordinatorId: state.coordinatorId, machine: state.machine, activatedAt: state.activatedAt, ...(start ? { startAction: start } : {}), currentMode: state.currentMode, recipeFirst: !state.recipeDelivered, workflow, ...(state.parking ? {parking: state.parking} : {}), runs: state.runs ?? state.checkCapacity?.runs, ...(state.checkCapacity ? {checkCapacity:state.checkCapacity} : {}), health: state.health ? { paused: state.health.paused, recoveredAt: state.health.recoveryPending } : null, issues, ...(timeRules.length ? { timeRules } : {}), ...(runtimePacket(state.runtime) ? { runtime: runtimePacket(state.runtime) } : {}) })}\n`;
}
function coordinatorEnvelope(state) {
  return { version: 'pdd.autopilot-coordinator.v1', repository: state.repo, coordinatorId: state.coordinatorId, machine: state.machine, activation: state.activatedAt, ...(state.runs === undefined ? {} : { runs: state.runs }) };
}
function profileBinding(state, p) {
  const variable = { codex: 'CODEX_HOME', claude: 'CLAUDE_CONFIG_DIR', gemini: 'GEMINI_CLI_HOME' }[state.agent.kind];
  return {
    agent: { id: state.agent.id, kind: state.agent.kind },
    home: state.environment?.HOME ?? p.env.HOME ?? null,
    definitionHome: state.definitionHome ?? state.environment?.HOME ?? p.env.HOME ?? null,
    configHome: variable ? state.environment?.[variable] || null : null,
  };
}
// Codex builds each chat command's environment from shell_environment_policy; `set` applies after `inherit`.
// An explicit saved CODEX_HOME also reaches the commands, so a pdd workflow run from the chat keeps the profile.
function providerArgs(kind, cwd, context, codexHome, queueEnv = {}) {
  if (kind === 'codex') return ['--no-daemon', '--dangerously-bypass-approvals-and-sandbox',
    '-c', quote(`projects={${tomlString(cwd)}={trust_level="trusted"}}`), '-c', quote('check_for_update_on_startup=false'),
    '-c', quote(`shell_environment_policy.set.PDD_AUTOPILOT_CONTEXT=${tomlString(context)}`),
    ...(codexHome ? ['-c', quote(`shell_environment_policy.set.CODEX_HOME=${tomlString(codexHome)}`)] : []),
    ...['PDD_SUITE_QUEUE', 'PDD_VM_SUITE_LOCK'].filter(name => typeof queueEnv[name] === 'string')
      .flatMap(name => ['-c', quote(`shell_environment_policy.set.${name}=${tomlString(queueEnv[name])}`)])];
  return [kind === 'gemini' ? '--yolo' : '--dangerously-skip-permissions'];
}
function launchDefinition(state, p) {
  let definition;
  const selectedEnv = { ...p.env, HOME: state.definitionHome ?? state.environment?.HOME ?? p.env.HOME };
  try { definition = loadAgentDefinitions({ cwd: state.cwd, env: selectedEnv }).find(x => x.id === state.agent.id); } catch { /* Fall back to the saved command. */ }
  return definition ?? state.agent;
}
// The invoked package and the arguments it builds. The coordinator envelope and profile bind the
// context and account values; caller PATH and reloaded definitions can differ between a start and a timer tick.
export function autopilotLaunchFingerprint(state) {
  const root = resolve(state.packageRoot ?? dirname(dirname(self)));
  let version = null;
  try { version = read(join(root, 'package.json'))?.version ?? null; } catch { /* An unreadable package has no version. */ }
  return digest({ version: 'pdd.autopilot-launch.v1', package: { root, version }, kind: state.agent.kind, start: startIn(state.cwd), args: providerArgs(state.agent.kind, state.cwd, '', state.environment?.CODEX_HOME, state.environment) });
}
function ownerLaunchMatches(state, p) {
  const launch = state.ownerLaunch;
  return !!state.paneId && launch?.paneId === state.paneId && JSON.stringify(launch.coordinator) === JSON.stringify(coordinatorEnvelope(state)) && JSON.stringify(launch.profile) === JSON.stringify(profileBinding(state, p));
}
// A matching owner chat that this package would launch differently is relaunched at an idle moment.
// Returns the fingerprint that the fresh chat would get, or null.
function relaunchTarget(state, p) {
  if (!state.agent || state.deliveryIntent || state.reconciliationIntent || !ownerLaunchMatches(state, p)) return null;
  const target = autopilotLaunchFingerprint(state);
  return state.ownerLaunch.fingerprint !== target && launchDefinition(state, p).kind === state.agent.kind ? target : null;
}
// A second relaunch for one fingerprint means that the fingerprint is not stable; the current chat stays.
const relaunchHeld = (state, target) => (state.relaunchTargets ?? []).includes(target);
function relaunchDue(state, p) { const target = relaunchTarget(state, p); return !!target && !relaunchHeld(state, target); }
// Saved values that name the coordinator pane and its launch; the coordinator identity stays.
function forgetPane(target) {
  if (target.ownerLaunch?.profile) target.launchProfile = target.ownerLaunch.profile;
  for (const key of ['paneId', 'workspaceId', 'ownerLaunch', 'contextPane', 'contextBinding', 'relaunchPending', 'relaunchHeld']) delete target[key];
  target.recipeDelivered = false;
}
// Herdr gives each terminal a new terminal_id; after a server restart a pane id can name another terminal.
const otherTerminal = (launch, observed) => typeof launch?.terminalId === 'string' && typeof observed?.terminal_id === 'string' && observed.terminal_id !== launch.terminalId;
// Herdr also answers agent_not_found for a closed pane, so only pane get shows that the saved pane is gone.
async function paneGone(state, p) {
  let pane;
  try { pane = (await herdr(['pane', 'get', state.paneId], p)).result?.pane; }
  catch (error) { if (error.code === 'pane_not_found') return true; throw error; }
  return state.ownerLaunch?.paneId === state.paneId && otherTerminal(state.ownerLaunch, pane);
}
function rearmWorkerCompletion(state, p) {
  let armed = 0, unavailable = 0;
  for (const run of (p.allRuns ?? allRuns)({}, p)) {
    const origin = run.automaticOrigin;
    if (!origin || ['cancelled', 'completed'].includes(run.state) || origin.coordinatorId !== state.coordinatorId || origin.machine !== state.machine || typeof origin.repository !== 'string' || origin.repository.toLowerCase() !== String(state.repo).toLowerCase() || !samePath(run.sourceRoot, state.cwd)) continue;
    if (armSavedWorkerCompletion(run, state.paneId, p)) armed++; else unavailable++;
  }
  return { armed, unavailable };
}
// End only the saved idle coordinator pane, then forget it in the same admission hold.
// A failure after the close leaves a gone pane, which a later wake replaces.
async function closeStaleCoordinator(state, agent, p) {
  const pane = state.paneId, workspace = state.workspaceId, ownerLaunch = state.ownerLaunch, launch = JSON.stringify(ownerLaunch), session = JSON.stringify(agent.agent_session ?? null);
  const fingerprint = autopilotLaunchFingerprint(state);
  const gone = async () => { try { await herdr(['pane', 'get', pane], p); return false; } catch (error) { if (error.code === 'pane_not_found') return true; throw error; } };
  let forgotten = null;
  try {
    forgotten = await p.scanAction(async () => {
      const saved = read(state.stateFile);
      if (!saved?.enabled || saved.paneId !== pane || saved.workspaceId !== workspace || JSON.stringify(saved.ownerLaunch) !== launch || saved.deliveryIntent || saved.reconciliationIntent) return null;
      const current = (await herdr(['agent', 'get', pane], p)).result?.agent;
      if (!current || current.pane_id !== pane) return null;
      // Another terminal has this pane id: the saved chat is gone and the other pane stays open.
      // A saved terminal id is the proof, and then the live folder is not compared: a chat that an older launch started
      // without the `cd` is in the shell startup folder. Without a saved terminal id, only the folder ties the pane to this repository.
      if (!otherTerminal(ownerLaunch, current)) {
        if (current.workspace_id !== workspace || current.agent !== state.agent.kind
          || (typeof ownerLaunch.terminalId === 'string' ? current.terminal_id !== ownerLaunch.terminalId : !samePath(current.cwd, state.cwd))
          || !['idle', 'done'].includes(current.agent_status) || JSON.stringify(current.agent_session ?? null) !== session) return null;
        try { await herdr(['pane', 'close', pane], p); } catch { /* The pane inventory below decides. */ }
        if (!await gone()) return null;
        saved.relaunchTargets = [...(saved.relaunchTargets ?? []), fingerprint].slice(-8);
      }
      forgetPane(saved);
      save(state.stateFile, saved);
      return { relaunchTargets: saved.relaunchTargets };
    });
  } catch { forgotten = null; }
  if (!forgotten) { p.warn('Autopilot work remains pending: the old coordinator chat could not be closed safely; the next tick retries.'); return false; }
  forgetPane(state);
  if (forgotten.relaunchTargets) state.relaunchTargets = forgotten.relaunchTargets;
  return true;
}
// A published request remains available while a submitted wake may still read it.
function requestArtifact(state, requestJson, repository, p, again = null) {
  const request = JSON.parse(requestJson);
  const canonicalRepo = value => typeof value === 'string' && /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(value) ? value.toLowerCase() : null;
  const repo = canonicalRepo(repository);
  if (!request || !repo || typeof request.id !== 'string' || !request.id || canonicalRepo(request.repository) !== repo ||
      !Array.isArray(request.issues) || !request.issues.every(x => typeof x === 'string') ||
      new Set(request.issues).size !== request.issues.length || typeof request.snapshotJson !== 'string' ||
      typeof request.contextJson !== 'string' || Object.keys(request).sort().join(',') !== 'contextJson,id,issues,repository,snapshotJson') throw Error('invalid request');
  const snapshot = JSON.parse(request.snapshotJson), context = JSON.parse(request.contextJson);
  if (!snapshot || canonicalRepo(snapshot.repository) !== repo || !context || !Array.isArray(context.source) || !Array.isArray(context.requirements)) throw Error('invalid request');
  const artifact = byteArtifact(state, Buffer.from(requestJson, 'utf8'), p);
  // A repeated request names its attempt and the reason of the last completion.
  const rows = again?.rows ?? [], shown = rows.slice(0, 5).map(x => x.key).join(', ') + (rows.length > 5 ? ` and ${rows.length - 5} more` : '');
  const repeat = again ? `Repeated request ${Number(again.attempt)} of ${Number(again.cap)}: the last delivery of these issues did not finish. Last reason: ${line(again.reason)}${shown ? ` (${line(shown)})` : ''}. Follow the dependency review step for this reason.\n` : '';
  return {
    text: () => `${message(state, [])}Dependency analysis request artifact (trusted data):\nArtifact path: ${JSON.stringify(artifact.path)}\nSHA-256: ${artifact.digest}\nRequest ID: ${JSON.stringify(request.id)}\nRepository: ${JSON.stringify(repository)}\n${repeat}Read and verify the exact artifact before analysis; follow the dependency review step and complete this request.\n`,
    close: artifact.close, prepare: artifact.prepare,
  };
}
function byteArtifact(state, bytes, p) {
  const digest = createHash('sha256').update(bytes).digest('hex');
  const dir = resolve(`${state.stateFile}.requests`), path = join(dir, randomUUID());
  const safe = (st, directory) => {
    if ((directory ? !st.isDirectory() : !st.isFile()) || st.uid !== process.getuid() || (st.mode & 0o7777) !== (directory ? 0o700 : 0o600)) throw Error('unsafe request artifact');
  };
  const sameIdentity = (a, b) => a.dev === b.dev && a.ino === b.ino;
  let directoryIdentity, fileIdentity, publishedFd;
  const checkDirectory = () => {
    const fd = openSync(dir, constants.O_RDONLY | constants.O_NOFOLLOW | constants.O_DIRECTORY);
    try {
      const st = fstatSync(fd); safe(st, true);
      if (directoryIdentity && !sameIdentity(st, directoryIdentity)) throw Error('request directory changed');
      directoryIdentity ??= st;
    } finally { closeSync(fd); }
  };
  const native = {
    create() {
      try { mkdirSync(dir, {mode: 0o700}); chmodSync(dir, 0o700); } catch (e) { if (e.code !== 'EEXIST') throw e; }
      checkDirectory();
      const temp = join(dir, `${randomUUID()}.tmp`);
      let fd;
      try {
        fd = openSync(temp, 'wx', 0o600); fchmodSync(fd, 0o600); writeFileSync(fd, bytes);
        fileIdentity = fstatSync(fd); safe(fileIdentity, false);
        linkSync(temp, path); publishedFd = fd; fd = null;
      } finally { if (fd !== undefined) { if (fd !== null) closeSync(fd); try { unlinkSync(temp); } catch (e) { if (e.code !== 'ENOENT') throw e; } } }
    },
    close() { if (publishedFd !== undefined) { closeSync(publishedFd); publishedFd = undefined; } },
    verify() {
      checkDirectory();
      const fd = openSync(path, constants.O_RDONLY | constants.O_NOFOLLOW);
      try {
        const st = fstatSync(fd); safe(st, false);
        if (!sameIdentity(st, fileIdentity) || !readFileSync(fd).equals(bytes)) throw Error('request artifact mismatch');
      } finally { closeSync(fd); }
    },
  };
  const io = p.requestArtifact ?? native;
  let created = false;
  return {
    path, digest,
    close: () => native.close(),
    prepare: async () => { if (!created) { await io.create({dir,path,bytes}); created = true; } await io.verify({dir,path,bytes,digest}); },
  };
}
function legacyDeliveryIntent(intent) {
  return !!intent && typeof intent === 'object' && !Array.isArray(intent)
    && Object.keys(intent).sort().join(',') === 'at,paneId,workspaceId'
    && Number.isFinite(intent.at) && typeof intent.paneId === 'string' && !!intent.paneId
    && typeof intent.workspaceId === 'string' && !!intent.workspaceId;
}
function deliveryTargetMatches(state, intent, p) {
  const launch = state.ownerLaunch;
  return !!intent && typeof intent === 'object' && !Array.isArray(intent)
    && intent.paneId === state.paneId && intent.workspaceId === state.workspaceId
    && typeof state.paneId === 'string' && !!state.paneId && typeof state.workspaceId === 'string' && !!state.workspaceId
    && !!state.agent && launch?.paneId === state.paneId
    && JSON.stringify({ ...launch.coordinator, runs: undefined }) === JSON.stringify({ ...coordinatorEnvelope(state), runs: undefined })
    && JSON.stringify(launch.profile) === JSON.stringify(profileBinding(state, p));
}
function recoveryTargetMatches(state, intent, p) {
  return (legacyDeliveryIntent(intent) || intent?.version === 2) && deliveryTargetMatches(state, intent, p);
}
async function repositoryRoot(cwd, p) {
  if (typeof cwd !== 'string' || !cwd) return null;
  try {
    const result = await p.execute('git', ['rev-parse', '--path-format=absolute', '--show-toplevel'], { cwd });
    return result.code === 0 && result.stdout.trim() ? result.stdout.trim() : null;
  } catch { return null; }
}
async function currentRecoveryTargetMatches(state, p, verifyRepository = true, session = undefined) {
  try {
    const [paneReply, workspaceReply, agentReply] = await Promise.all([
      herdr(['pane', 'get', state.paneId], p),
      herdr(['workspace', 'get', state.workspaceId], p),
      herdr(['agent', 'get', state.paneId], p),
    ]);
    const pane = paneReply?.result?.pane, workspace = workspaceReply?.result?.workspace, agent = agentReply?.result?.agent;
    if (session !== undefined && JSON.stringify(agent?.agent_session ?? null) !== session) return false;
    if (paneReply?.result?.type !== 'pane_info' || workspaceReply?.result?.type !== 'workspace_info' || agentReply?.result?.type !== 'agent_info'
      || pane?.pane_id !== state.paneId || pane.workspace_id !== state.workspaceId || !samePath(pane.cwd, state.cwd)
      || workspace?.workspace_id !== state.workspaceId || agent?.pane_id !== state.paneId || agent.workspace_id !== state.workspaceId
      || !samePath(agent.cwd, state.cwd) || pane.tab_id !== agent.tab_id || pane.terminal_id !== agent.terminal_id
      || pane.agent !== state.agent?.kind || agent.agent !== state.agent?.kind
      || pane.agent_status !== agent.agent_status || !['idle', 'done'].includes(agent.agent_status)
      || !samePath(pane.foreground_cwd, agent.foreground_cwd)) return false;
    const [savedRoot, paneRoot, agentRoot] = await Promise.all([
      repositoryRoot(state.cwd, p), repositoryRoot(pane.foreground_cwd, p), repositoryRoot(agent.foreground_cwd, p),
    ]);
    if (!savedRoot || !paneRoot || !agentRoot || !samePath(savedRoot, paneRoot) || !samePath(savedRoot, agentRoot)) return false;
    if (verifyRepository) {
      // The saved repository path, never the pane's live folder.
      const result = await p.execute('gh', ['repo', 'view', '--json', 'nameWithOwner,url'], { cwd: state.cwd });
      if (result.code !== 0) return false;
      const actual = JSON.parse(result.stdout);
      if (typeof actual?.nameWithOwner !== 'string' || actual.nameWithOwner.toLowerCase() !== state.repo.toLowerCase()
        || actual.url !== `https://github.com/${actual.nameWithOwner}`) return false;
    }
    return true;
  } catch { return false; }
}
async function wake(state, makeText, p, prepare = async () => {}, explicitStartReconcile = false, semanticIdentity = null, capture = async () => {}) {
  if (p.githubFloor?.blocked('core') || p.githubFloor?.blocked('graphql')) return false;
  if (p.scanGuard && !await p.scanGuard()) return false;
  const oldDelivery = state.deliveryIntent, oldReconciliation = state.reconciliationIntent;
  const oldIntent = oldReconciliation ?? oldDelivery;
  const recovering = !!oldIntent && recoveryTargetMatches(state, oldIntent, p);
  const recoveryCustodyMatches = saved => JSON.stringify(saved?.deliveryIntent) === JSON.stringify(oldDelivery) && JSON.stringify(saved?.reconciliationIntent) === JSON.stringify(oldReconciliation) && recoveryTargetMatches(saved, oldIntent, p);
  if (oldIntent || state.reconciliationIntent) {
    if (!recovering || !recoveryTargetMatches(state, oldIntent, p)) {
      p.warn('Autopilot work remains pending: a previous submission has uncertain custody.');
      return false;
    }
  } else await openWorkspace(state, p);
  if (p.scanGuard && !await p.scanGuard()) return false;
  // Forget a gone coordinator pane, leave any pane that now has its id alone and open a fresh pane for the same coordinator.
  const replaceGonePane = async () => {
    const pane = state.paneId, launch = JSON.stringify(state.ownerLaunch ?? null);
    if (!await p.scanGuard(latest => {
      if (latest.paneId !== pane || JSON.stringify(latest.ownerLaunch ?? null) !== launch || latest.deliveryIntent || latest.reconciliationIntent) return false;
      forgetPane(latest);
    })) return false;
    forgetPane(state);
    await openWorkspace(state, p);
    try { rearmWorkerCompletion(state, p); } catch { /* A later explicit start rearms worker completion. */ }
    return true;
  };
  let agent;
  try { agent = (await herdr(['agent', 'get', state.paneId], p)).result?.agent; }
  catch (e) {
    if (recovering) { p.warn('Autopilot recovery waits: the saved agent could not be verified.'); return false; }
    if (!['agent_not_found', 'pane_not_found', 'server_not_running'].includes(e.code)) throw e;
    if ((e.code !== 'agent_not_found' || await paneGone(state, p)) && !await replaceGonePane()) return false;
  }
  if (!recovering && agent && state.ownerLaunch?.paneId === state.paneId && otherTerminal(state.ownerLaunch, agent)) {
    if (!await replaceGonePane()) return false;
    agent = undefined;
  }
  const recoverySession = JSON.stringify(agent?.agent_session ?? null);
  const envelope = () => coordinatorEnvelope(state);
  if (recovering) {
    if (!agent || !recoveryTargetMatches(state, oldIntent, p) || !['idle', 'done'].includes(agent.agent_status)
      || state.ownerLaunch?.paneId === state.paneId && otherTerminal(state.ownerLaunch, agent) || !await currentRecoveryTargetMatches(state, p, true, recoverySession)) {
      p.warn('Autopilot recovery waits: the saved target is not safely idle and unchanged.');
      return false;
    }
  }
  if (!recovering && agent && !ownerLaunchMatches(state, p)) {
    const oldPane = state.paneId;
    if (!await p.scanGuard(latest => {
      delete latest.paneId; delete latest.workspaceId; delete latest.ownerLaunch;
      delete latest.contextPane; delete latest.contextBinding;
    })) return false;
    delete state.paneId; delete state.workspaceId; delete state.ownerLaunch;
    delete state.contextPane; delete state.contextBinding;
    await openWorkspace(state, p);
    if (state.paneId === oldPane) { delete state.paneId; delete state.workspaceId; throw Error('Herdr did not create a fresh pane; retry next tick.'); }
    if (!await p.scanGuard(latest => { latest.paneId = state.paneId; latest.workspaceId = state.workspaceId; })) return false;
    try {
      if ((await herdr(['agent', 'get', state.paneId], p)).result?.agent) return false;
    } catch (error) { if (error.code !== 'agent_not_found') throw error; }
    agent = null;
  }
  const deliver = async (initial, withinLaunch = () => true, readinessClock = p.now) => {
    const pane = state.paneId, workspace = state.workspaceId, launch = state.ownerLaunch;
    let identity = initial ? JSON.stringify(initial.agent_session ?? null) : undefined;
    let changed = false, expired = false, submittedIntent = null, transportError;
    const observeIdentity = agent => {
      const session = JSON.stringify(agent?.agent_session ?? null);
      if (identity === undefined && (recovering || session !== 'null')) identity = session;
      else if (identity !== undefined && identity !== session) changed = true;
      return !changed && (identity === undefined || JSON.stringify(agent?.agent_session ?? null) === identity);
    };
    if (!withinLaunch()) { p.warn('Autopilot work remains pending: the chat startup window expired.'); return false; }
    const text = (recovering ? 'This is a fresh current-state reconciliation. Do not repeat any earlier unknown request.\n' : '') + makeText(), payloadDigest = digest(text), fingerprint = semanticIdentity ? digest(semanticIdentity) : null;
    if (!fingerprint && (oldReconciliation || (state.uncertainDeliveryHistory ?? []).some(intent => intent?.kind === 'fresh-reconciliation'))) {
      p.warn('Autopilot work remains pending: the current update has no semantic identity.');
      return false;
    }
    const artifact = semanticIdentity?.kind === 'work' ? byteArtifact(state, Buffer.from(text, 'utf8'), p) : null;
    const instruction = artifact ? `Current-work artifact (trusted data):\nArtifact path: ${JSON.stringify(artifact.path)}\nSHA-256: ${artifact.digest}\nRead the complete artifact once as bytes; verify its SHA-256 against the stated digest before decoding UTF-8 and following those same bytes as the work message. If the artifact is missing, unreadable, invalid UTF-8 or does not match, leave the work pending; do not substitute another packet. This artifact does not grant authority to start work; apply current mode, trust, ownership, graph and admission checks.\n` : text;
    if (artifact && Buffer.byteLength(instruction, 'utf8') > 16384) return false;
    let result;
    try { result = await sendToChat({ paneId: pane, startedAt: launch?.startedAt }, instruction, {
      herdr: async args => {
        if (args[0] === 'agent' && args[1] === 'prompt' && !withinLaunch()) { expired = true; throw Object.assign(Error('Startup window expired'), { code: 'agent_blocked' }); }
        if (args[0] === 'agent' && args[1] === 'prompt' && recovering && !await currentRecoveryTargetMatches(state, p, false, recoverySession)) {
          p.warn('Autopilot recovery waits: the live workspace, pane, repo path or agent changed before submission.');
          throw Object.assign(Error('Autopilot target changed'), { code: 'agent_blocked' });
        }
        const submitting = args[0] === 'agent' && args[1] === 'prompt';
        const observe = async status => { try { await capture(status); } catch {} };
        let reply;
        if (submitting) {
          await observe('attempted');
          try { reply = await p.scanTransport(async () => {
            try { return await herdr(args, p); } catch (error) { transportError = error; throw error; }
          }); }
          catch (error) { await observe(['agent_not_found','pane_not_found','agent_blocked'].includes(error?.code) ? 'failed' : 'uncertain'); throw error; }
          await observe('confirmed');
        } else reply = await herdr(args, p);
        if (args[0] === 'agent' && args[1] === 'get' && reply.result?.agent) {
          const observed = reply.result.agent;
          observeIdentity(observed);
          if (changed) return { ...reply, result: { ...reply.result, agent: { ...observed, agent_status: 'blocked' } } };
          if (!['idle', 'done', 'blocked'].includes(observed.agent_status))
            return { ...reply, result: { ...reply.result, agent: { ...observed, agent_status: 'starting' } } };
        }
        return reply;
      }, now: readinessClock, elapsedNow: p.elapsedNow, sleep: p.sleep,
      beforeSubmit: async () => {
        const saved = read(state.stateFile);
        const custodyMatches = recovering
          ? recoveryCustodyMatches(saved)
          : (!saved?.deliveryIntent || JSON.stringify(saved.deliveryIntent) === JSON.stringify(submittedIntent)) && !saved?.reconciliationIntent;
        if (changed || !custodyMatches || !saved?.enabled || saved.paneId !== pane || saved.workspaceId !== workspace || JSON.stringify(saved.ownerLaunch) !== JSON.stringify(launch)) return false;
        const current = (await herdr(['agent', 'get', pane], p)).result?.agent;
        if (!withinLaunch()) { expired = true; return false; }
        if (!current || !['idle', 'done'].includes(current.agent_status) || !observeIdentity(current)) return false;
        try { await prepare(); if (artifact) await artifact.prepare(); } catch { return false; }
        const finalState = read(state.stateFile);
        const finalCustodyMatches = recovering
          ? recoveryCustodyMatches(finalState)
          : (!finalState?.deliveryIntent || JSON.stringify(finalState.deliveryIntent) === JSON.stringify(submittedIntent)) && !finalState?.reconciliationIntent;
        const finalAgent = (await herdr(['agent', 'get', pane], p)).result?.agent;
        if (!withinLaunch()) { expired = true; return false; }
        if (!finalCustodyMatches || !finalState?.enabled || finalState.paneId !== pane || finalState.workspaceId !== workspace || JSON.stringify(finalState.ownerLaunch) !== JSON.stringify(launch) || !finalAgent || !['idle', 'done'].includes(finalAgent.agent_status) || !observeIdentity(finalAgent)) return false;
        const intent = { version: 2, paneId: pane, workspaceId: workspace, at: p.now(), fingerprint, payloadDigest, ...(recovering ? { reconciliationOf: digest(oldIntent) } : {}) };
        const committed = await p.scanGuard(latest => {
          if (latest.paneId !== pane || latest.workspaceId !== workspace || JSON.stringify(latest.ownerLaunch) !== JSON.stringify(launch)) return false;
          if (recovering) {
            if (!recoveryCustodyMatches(latest)) return false;
            latest.uncertainDeliveryHistory ??= [];
            for (const [prior, kind] of [[oldDelivery, 'ordinary-delivery'], [oldReconciliation, 'fresh-reconciliation']].filter(([value]) => value)) {
              if (!latest.uncertainDeliveryHistory.some(value => value?.at === prior.at && value?.paneId === prior.paneId && value?.workspaceId === prior.workspaceId && value?.payloadDigest === prior.payloadDigest)) latest.uncertainDeliveryHistory.push({ ...prior, kind: legacyDeliveryIntent(prior) ? 'legacy-uncertain' : kind, historicalMode: 'unknown', historicalAgentSession: 'unknown' });
            }
            delete latest.deliveryIntent;
            latest.reconciliationIntent = intent;
          } else {
            if (latest.reconciliationIntent || (latest.deliveryIntent && JSON.stringify(latest.deliveryIntent) !== JSON.stringify(submittedIntent))) return false;
            latest.deliveryIntent = intent;
          }
        });
        if (committed) {
          submittedIntent = intent;
          if (recovering) state.reconciliationIntent = intent;
          else state.deliveryIntent = intent;
        }
        return committed;
      },
    }); } finally { artifact?.close(); }
    if (recovering) {
      if (submittedIntent) {
        const committed = read(state.stateFile);
        state.uncertainDeliveryHistory = committed?.uncertainDeliveryHistory ?? state.uncertainDeliveryHistory;
        delete state.deliveryIntent;
        if (result.uncertain) state.reconciliationIntent = submittedIntent;
        else delete state.reconciliationIntent;
      }
    } else if (result.ok || !result.uncertain) delete state.deliveryIntent;
    if (!result.ok) { try { p.warn(`Autopilot work remains pending: ${expired ? 'the chat startup window expired' : changed ? 'the chat target changed' : result.reason ?? result.code.replaceAll('_', ' ')}.`); } catch { /* A failed warning must not replace the transport result. */ } }
    if (!result.ok && transportError) p[transportFailure]?.(transportError);
    return result.ok;
  };
  if (agent) {
    const relaunch = !recovering && relaunchDue(state, p);
    if (!['idle', 'done'].includes(agent.agent_status)) {
      if (['working', 'starting'].includes(agent.agent_status)) p.coordinatorDeferred?.(state, agent);
      if (relaunch) {
        const mark = { paneId: state.paneId, startedAt: state.ownerLaunch.startedAt };
        if (JSON.stringify(state.relaunchPending) !== JSON.stringify(mark) && await p.scanGuard(latest => {
          if (latest.paneId !== mark.paneId || latest.ownerLaunch?.startedAt !== mark.startedAt) return false;
          latest.relaunchPending = mark;
        })) state.relaunchPending = mark;
      }
      p.warn(relaunch ? 'Autopilot work remains pending: the coordinator relaunch waits until the chat is idle.' : 'Autopilot work remains pending: the chat is not idle.');
      return false;
    }
    if (!relaunch) return deliver(agent);
    const oldPane = state.paneId;
    if (!await closeStaleCoordinator(state, agent, p)) return false;
    await openWorkspace(state, p);
    if (state.paneId === oldPane) { delete state.paneId; delete state.workspaceId; throw Error('Herdr did not create a fresh pane; retry next tick.'); }
    try { rearmWorkerCompletion(state, p); } catch { /* A later explicit start rearms worker completion. */ }
    try {
      if ((await herdr(['agent', 'get', state.paneId], p)).result?.agent) return false;
    } catch (error) { if (error.code !== 'agent_not_found') throw error; }
    agent = null;
  }
  if (state.ownerLaunch?.paneId === state.paneId) { p.warn('Autopilot work remains pending: the launched chat is unavailable.'); return false; }
  const definition = launchDefinition(state, p);
  if (definition.kind !== state.agent.kind) { p.warn('Run pdd autopilot start to select the changed agent profile.'); return false; }
  const context = JSON.stringify(envelope());
  const childEnv = { ...keepEnv(p.env), ...definition.env, HOME: state.environment?.HOME ?? p.env.HOME, PDD_AUTOPILOT_CONTEXT: context };
  for (const variable of ['CODEX_HOME', 'CLAUDE_CONFIG_DIR', 'GEMINI_CLI_HOME']) {
    if (state.environment?.[variable]) childEnv[variable] = state.environment?.[variable]; else delete childEnv[variable];
  }
  const args = providerArgs(definition.kind, state.cwd, context, state.environment?.CODEX_HOME, childEnv);
  const env = Object.entries(childEnv).map(([k, v]) => `${k}=${quote(v)}`);
  const unset = ['CODEX_HOME', 'CLAUDE_CONFIG_DIR', 'GEMINI_CLI_HOME'].filter(k => !state.environment?.[k])
    .concat(['PDD_SUITE_QUEUE', 'PDD_VM_SUITE_LOCK'].filter(k => !Object.hasOwn(childEnv, k))).flatMap(k => ['-u', k]);
  let terminal;
  try { terminal = (await herdr(['pane', 'get', state.paneId], p)).result?.pane?.terminal_id; }
  catch (error) { if (error.code !== 'pane_not_found') throw error; p.warn('Autopilot work remains pending: the coordinator pane closed before the launch; the next tick opens a fresh pane.'); return false; }
  state.ownerLaunch = { paneId: state.paneId, startedAt: p.now(), coordinator: envelope(), profile: profileBinding(state, p), fingerprint: autopilotLaunchFingerprint(state), terminalId: typeof terminal === 'string' ? terminal : null };
  const elapsedNow = p.elapsedNow ?? (() => Number(process.hrtime.bigint() / 1_000_000n));
  const began = elapsedNow(), deadline = state.ownerLaunch.startedAt + START_GRACE_MS;
  const withinLaunch = () => Math.min(deadline - p.now(), START_GRACE_MS - Math.max(0, elapsedNow() - began)) > 0;
  if (!await p.scanGuard(latest => { latest.ownerLaunch = state.ownerLaunch; latest.launchProfile = state.ownerLaunch.profile; delete latest.relaunchPending; delete latest.relaunchHeld; })) { delete state.ownerLaunch; return false; }
  state.launchProfile = state.ownerLaunch.profile;
  delete state.relaunchPending; delete state.relaunchHeld;
  try { await p.scanAction(() => herdr(['pane', 'run', state.paneId, [...startIn(state.cwd), 'env', ...unset, ...env, quote(definition.command), ...args].join(' ')], p), 'launch'); }
  catch (error) { if (error.confirmedRejection || error.code === 'agent_not_found' || error.code === 'pane_not_found') delete state.ownerLaunch; throw error; }
  return deliver(undefined, withinLaunch, () => Math.max(p.now(), state.ownerLaunch.startedAt + Math.max(0, elapsedNow() - began)));
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

function closingIssues(body, repo) {
  const refs = [];
  const pattern = /\b(?:fix(?:es|ed)?|close[sd]?|resolve[sd]?)\s+(?:(?:https:\/\/github\.com\/)?([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)(?:\/issues\/|#)|#)([1-9][0-9]*)/gi;
  for (const match of String(body ?? '').matchAll(pattern)) if (!match[1] || match[1].toLowerCase() === repo.toLowerCase()) refs.push(Number(match[2]));
  return refs;
}
function cachePullRequests(state) {
  state.pullCache ??= {};
  for (const saved of Object.values(state.pullCache)) saved.present = false;
  for (const row of state.cachedIssues ?? []) if (row.pull_request) {
    const refs = closingIssues(row.body, state.repo);
    if (refs.length || state.pullCache[row.number]) state.pullCache[row.number] = { ...state.pullCache[row.number], row, refs, present: true };
  }
}
async function reviewSubmissions(pull, state, p) {
  p.reviewReads ??= new Map();
  if (!p.reviewReads.has(pull.row.number)) p.reviewReads.set(pull.row.number, (async () => {
    let endpoint = `repos/${state.repo}/pulls/${pull.row.number}/reviews?per_page=100`;
    const pages = {}, rows = [];
    while (endpoint) {
      // Reviews come in ascending order: a full last page keeps its ETag when review 101 arrives, so it is read in full.
      const old = pull.reviewPages?.[endpoint], r = await githubGet(endpoint, p, old && !githubFullLastPage(endpoint, old.rows, old.next) ? old.etag : undefined);
      const page = r.status === 304 ? old : { etag: r.etag, rows: r.value, next: r.link?.match(/<https:\/\/api\.github\.com\/([^>]+)>; rel="next"/)?.[1] };
      if (!Array.isArray(page?.rows)) throw Error('GitHub reviews unavailable; retry next tick.');
      pages[endpoint] = page; rows.push(...page.rows); endpoint = page.next;
    }
    pull.reviewPages = pages;
    pull.reviews ??= {};
    // A review ID names one submission. Later edits or dismissals are not new work.
    for (const row of rows) if (row.submitted_at && !Object.hasOwn(pull.reviews, row.id)) {
      pull.reviews[row.id] = { id: row.id, user: row.user, submitted_at: row.submitted_at, state: row.state, body: row.body, commit_id: row.commit_id };
    }
  })());
  await p.reviewReads.get(pull.row.number);
}
async function relatedPullRequests(number, state, config, p) {
  const result = [];
  for (const saved of Object.values(state.pullCache)) {
    if (!saved.refs.includes(number) || !await trusted(saved.row, state, config, p)) continue;
    const version = `${saved.row.updated_at}:${saved.row.comments}`;
    if (!saved.snapshot || saved.present && saved.version !== version || !saved.present && saved.snapshot.state === 'open') {
      const detail = p.pullRequest ? await p.pullRequest(saved.row.number) : (await githubGet(`repos/${state.repo}/pulls/${saved.row.number}`, p)).value;
      if (!['open', 'closed'].includes(detail?.state)) throw Error('Related PR state unavailable; retry next tick.');
      saved.discussion = saved.row.comments ? await comments(saved.row.number, state, p) : [];
      saved.snapshot = { number: saved.row.number, state: detail.state, draft: detail.draft === true, merged: detail.merged === true || Boolean(detail.merged_at), head: detail.head?.sha ?? null };
      saved.version = version;
    }
    const discussion = [];
    for (const row of saved.discussion ?? []) {
      if (row.body !== ACK_TEXT && await trusted(row, state, config, p)) discussion.push({ id: row.id, updatedAt: row.updated_at, author: row.user.login, body: row.body });
    }
    const reviews = [];
    for (const row of Object.values(saved.reviews ?? {})) if (await trusted(row, state, config, p)) {
      reviews.push({ id: row.id, author: row.user.login, submittedAt: row.submitted_at, state: row.state, body: row.body, commit: row.commit_id });
    }
    result.push({ ...saved.snapshot, comments: discussion, reviews });
  }
  return result.sort((a, b) => a.number - b.number);
}

const digest = value => createHash('sha256').update(JSON.stringify(value)).digest('hex');
async function revalidateView(view, state, config, p) {
  const allowed = author => trusted({ user: { login: author } }, state, config, p);
  const retain = async rows => {
    const result = [];
    for (const row of rows) if (await allowed(row.author)) result.push(row);
    return result;
  };
  const pulls = [];
  for (const pull of view.pulls) if (await allowed(pull.author)) pulls.push({ ...pull, comments: await retain(pull.comments), reviews: await retain(pull.reviews ?? []) });
  return { ...view, text: view.text && await allowed(view.text.author) ? view.text : undefined, comments: await retain(view.comments), pulls };
}

const transportFailure = Symbol();

export async function tickAutopilot(stateFile, ports = {}) {
  let transportError;
  const result = await runTick(stateFile, { ...ports, [transportFailure]: error => { transportError = error; } }, false);
  if (transportError) throw transportError;
  return result;
}

function workflowCleanupPorts(p, ports) {
  return {...p, herdr: ports.workflowHerdr ?? (async args => {
    const result = await p.execute('herdr', ['--session','pdd',...args]);
    if (result.code === 0 && args[0] === 'pane' && args[1] === 'read') return result.stdout;
    let reply; try { reply = JSON.parse(result.code === 0 ? result.stdout : result.stderr || result.stdout); } catch {}
    if (result.code !== 0 || reply?.error) throw Object.assign(Error('Workflow Herdr inventory unavailable'), {code:reply?.error?.code ?? 'herdr_failed'});
    return reply;
  })};
}
async function runTick(stateFile, ports, completion) {
  let deferredWakes = null;
  const outcome = async (status, message) => {await deferredWakes?.(); return completion ? {state: status} : ok(message);};
  let state = read(stateFile), p, scanGuard; if (!state?.enabled) return await outcome('inactive', 'Autopilot stopped.');
  const lock = stateFile + '.lock';
  if (!claimTickLock(lock)) { ports.tickBusy?.(); return await outcome('busy', 'Autopilot tick already running.'); }
  try {
    state = read(stateFile);
    if (!state?.enabled) return await outcome('inactive', 'Autopilot stopped.');
    if (ports.expectedStart && !['cwd','repo','coordinatorId','machine','controlRevision'].every(key => state[key] === ports.expectedStart[key])) return await outcome('inactive', 'Autopilot start was superseded.');
    p = portsFor(state, { ...ports, githubRoot: dirname(stateFile) });
    if (!state.coordinatorId || !state.machine) {
      const release = await claimAdmission(state, p);
      if (!release) throw Error('Timed out waiting for automatic admission; retry.');
      try { state = read(stateFile); if (!state?.enabled) return await outcome('inactive', 'Autopilot stopped.'); state.coordinatorId ??= randomUUID(); state.machine ??= hostname(); save(stateFile, state); }
      finally { release(); }
    }
    try { await (ports.tidyRuns ?? tidyRuns)({timeBudgetMs:5000}, workflowCleanupPorts(p, ports)); }
    catch (error) { p.warn(`Finished chat cleanup waits (${error.code ?? 'unavailable'}).`); }
    const config = await settings(state, p);
    if (config.mode === 'off') return await outcome('inactive', line(config.message));
    const priorBase = state.baseBranch;
    await automaticBase(state, p);
    if (priorBase !== state.baseBranch) state.recipeDelivered = false;
    state.currentMode = config.mode;
    let accepted = JSON.stringify([state.controlRevision ?? null, state.coordinatorId, state.machine, state.activatedAt, state.runs ?? null, profileBinding(state, p)]);
    scanGuard = async (mutate = null) => {
      const release = await claimAdmission(state, p);
      if (!release) return false;
      try {
        const latest = read(stateFile);
        if (!latest?.enabled || JSON.stringify([latest.controlRevision ?? null, latest.coordinatorId, latest.machine, latest.activatedAt, latest.runs ?? null, profileBinding(latest, p)]) !== accepted) return false;
        const current = await settings(latest, p);
        if (current.mode !== config.mode || current.mode === 'off') return false;
        if (mutate) { if (await mutate(latest) === false) return false; save(stateFile, latest); accepted = JSON.stringify([latest.controlRevision ?? null, latest.coordinatorId, latest.machine, latest.activatedAt, latest.runs ?? null, profileBinding(latest, p)]); }
        return true;
      } finally { release(); }
    };
    p.scanGuard = scanGuard;
    await observeHealth(state, p);
    if (!await scanGuard(latest => { latest.health = state.health; })) return await outcome('inactive', 'Autopilot changed.');
    let capacity;
    if (!await scanGuard(async latest => { capacity = await configureCheckCapacity({env:p.env,checks:state.checks,runs:state.runs,owner:stateFile,resources:state.health?.resource?.resources}, p.checkCapacityPorts ?? p); latest.checkCapacity = capacity; })) return await outcome('inactive', 'Autopilot control changed.');
    state.checkCapacity = capacity;
    p.scanAction = async (action, cleanup = '') => {
      const release = await claimAdmission(state, p);
      if (!release) throw Object.assign(Error('Autopilot admission unavailable'), {code:'agent_blocked'});
      try {
        const latest = read(stateFile);
        const identity = latest && JSON.stringify([latest.controlRevision ?? null, latest.coordinatorId, latest.machine, latest.activatedAt, latest.runs ?? null, profileBinding(latest, p)]);
        const current = latest?.enabled ? await settings(latest, p) : null;
        if (!latest?.enabled || identity !== accepted || current?.mode !== config.mode || current.mode === 'off') {
          if (cleanup === 'intent' && latest && state.deliveryIntent && JSON.stringify(latest.deliveryIntent) === JSON.stringify(state.deliveryIntent)) { delete latest.deliveryIntent; save(stateFile, latest); }
          if (cleanup === 'reconciliation' && latest && state.reconciliationIntent && JSON.stringify(latest.reconciliationIntent) === JSON.stringify(state.reconciliationIntent)) { delete latest.reconciliationIntent; save(stateFile, latest); }
          if (cleanup === 'launch' && latest && state.ownerLaunch && JSON.stringify(latest.ownerLaunch) === JSON.stringify(state.ownerLaunch)) { delete latest.ownerLaunch; save(stateFile, latest); }
          throw Object.assign(Error('Autopilot control changed'), {code:'agent_blocked'});
        }
        return await action();
      } finally { release(); }
    };
    p.scanTransport = action => p.scanAction(action, state.reconciliationIntent ? 'reconciliation' : 'intent');
    await healthAlerts(state, p, dirname(stateFile));
    // Native attention summary remains independent of GitHub budgets and AI coordinator activity.
    try {
      const attention = await (p.readAttention ?? ((state, p) => automaticAttention({ repo: state.repo, machine: state.machine }, { env: p.env })))(state, p);
      const input = { action: 'digest', cwd: state.cwd, env: p.env, attention };
      const alertPorts = { ...p.alertPorts, repository: async () => ({ nameWithOwner: state.repo }), stateRoot: dirname(stateFile), now: p.now,
        hostname: () => state.machine };
      await (p.sendDigest ?? runAutopilotAlerts)(input, alertPorts);
    } catch { /* Digest failures never stop feasible work. */ }
    if (config.mode === 'auto') {
      await parkingTick(state, p, config, {localOnly: true});
      deferredWakes = async () => {
        deferredWakes = null;
        if (state.health.paused) return;
        state.timeSeen ??= {};
        const rules = [], pending = {}, local = parkingPorts(state, p, {localOnly: true});
        // Preserve ordinary interpreter observation timing when no local wake
        // competes for capacity. A ready local wait must consider older waits.
        for (const run of await local.list()) if (run.parking?.phase === 'parked' && await local.blockerCleared(run)) {
          const waits = await (p.readEnvironmentWaits ?? readEnvironmentWaits)(state, p);
          await environmentTick(state, p, waits, rules, pending, dirname(stateFile));
          await runtimeTick(state, p, completion, rules, pending, dirname(stateFile));
          break;
        }
        await parkingTick(state, p, config, {wake: true, localOnly: true, wakeRules: rules});
      };
      await resumeStoppedWorkers(state, p);
    }
    if (state.retryAt > p.now()) return await outcome('unknown', `GitHub rate limited; next attempt after ${new Date(state.retryAt).toISOString()}.`);
    // The GitHub budget of the tick on this machine, from the local ledgers and the newest limit that GitHub reported.
    let budget = { state: 'normal' }, restLeft;
    try {
      const usage = githubUsage(githubMachineEntries({ root: p.githubRoot }), p.now());
      restLeft = usage.rate.core?.remaining;
      budget = githubBudget({ usage, ...githubBudgetSettings(config.github) });
    } catch { /* An unreadable ledger leaves the budget normal. */ }
    // Heartbeats of this coordinator's own live claims (no AI call). A saved claim can have expired since it was
    // observed: expiry is final, so it gets no heartbeat.
    const ownClaimsOf = claims => claims.filter(claim => claim && typeof claim.issue === 'string' && claim.active === true && claim.coordinatorId === state.coordinatorId
      && claim.machine === state.machine && claim.commentId && claim.labelEventId);
    const environmentWaits = await (p.readEnvironmentWaits ?? readEnvironmentWaits)(state, p);
    const environmentNumbers = new Set(environmentWaits.map(wait => wait.number));
    const environmentPending = new Set(environmentWaits.filter(wait => wait.attempts < ENVIRONMENT_BACKOFF.length).map(wait => wait.number));
    const stuckFor = claim => p.now() - (typeof claim.stuckSince === 'string' ? Date.parse(claim.stuckSince) : NaN);
    const sendHeartbeats = async (claims, saved) => {
      for (const claim of claims) {
        // After 4 hours stuck the owner stops refreshing, so the claim expires unless the issue leaves pdd:stuck.
        if (stuckFor(claim) >= STUCK_CLAIM_AFTER && !state.parkedNumbers?.includes(Number(/\/issues\/(\d+)$/.exec(claim.issue)?.[1])) && !environmentPending.has(Number(/\/issues\/(\d+)$/.exec(claim.issue)?.[1]))) continue;
        if (saved && !(Date.parse(claim.lastSeen) + STUCK_CLAIM_AFTER > p.now())) continue;
        try {
          const beat = await (p.refreshClaimHeartbeat ?? refreshClaimHeartbeat)({ cwd: state.cwd, repository: state.repo, claim, coordinatorId: state.coordinatorId, machine: state.machine, at: new Date(p.now()).toISOString() },
            { execFile: async (file, args, options) => p.execute(file, args, { purpose: 'claims', ...options }), admitMutation: action => p.scanAction(action) });
          if (beat?.state === 'refreshed' && typeof beat.lastSeen === 'string') claim.lastSeen = beat.lastSeen;
        } catch (error) { p.warn(`Claim heartbeat deferred for ${claim.issue}: ${line(error.message)}`); }
      }
    };
    if (budget.state === 'reserve' && budget.resetAt > p.now()) {
      // Below the floor: no GitHub call until the reset, except the heartbeats of the own live claims of the last intake
      // (2 REST calls each), so a claim does not expire while its chat works when reserve comes back after each reset.
      // No rate-limit wait is saved: each tick until the reset computes the budget again and sends the heartbeats again.
      const claims = ownClaimsOf(Array.isArray(state.githubIntake?.claims) ? state.githubIntake.claims : []);
      if (!(Number.isFinite(restLeft) && restLeft < 2 * claims.length)) await sendHeartbeats(claims, true);
      return await outcome('unknown', `GitHub limit low: ${budget.remaining} ${budget.resource === 'graphql' ? 'GraphQL points' : 'REST calls'} left, below the floor of ${budget.floor}; Autopilot waits until ${new Date(budget.resetAt).toISOString()}, except the heartbeats of this machine's claims.`);
    }
    // A due relaunch wakes even without new work; the fresh chat starts with the recipe.
    const relaunch = relaunchTarget(state, p);
    if (relaunch && relaunchHeld(state, relaunch)) {
      const mark = { paneId: state.paneId, startedAt: state.ownerLaunch.startedAt, fingerprint: relaunch };
      if (JSON.stringify(state.relaunchHeld) !== JSON.stringify(mark)) {
        state.relaunchHeld = mark; delete state.relaunchPending;
        p.warn('Autopilot did not relaunch the coordinator chat again: it already relaunched it for these launch settings. The current chat stays.');
      }
    } else {
      delete state.relaunchHeld;
      if (relaunch && state.recipeDelivered) state.recipeDelivered = false;
    }
    const dependencyPending = {
      read: async () => ({ json: JSON.stringify(state.dependencyPending ?? {}) }),
      save: async ({ json }) => { const value = JSON.parse(json); const ok = await scanGuard(latest => { latest.dependencyPending = value; }); if (ok) state.dependencyPending = value; return { ok }; },
      deliver: async ({ requestJson }) => {
        if (!read(stateFile)?.enabled || state.health?.paused) return { state: 'busy' };
        // Intake marks a repeated request in its pending state. It is never sent while an earlier submission has uncertain custody.
        const again = state.dependencyPending?.redelivery ?? null;
        if (again && (state.deliveryIntent || state.reconciliationIntent)) { p.warn('Autopilot dependency review waits: a previous submission has uncertain custody.'); return { state: 'busy' }; }
        let artifact;
        try { artifact = requestArtifact(state, requestJson, state.repo, p, again); } catch { return { state: 'busy' }; }
        const instruction = artifact.text();
        if (Buffer.byteLength(instruction, 'utf8') > 16384) return { state: 'busy' };
        try {
          const delivered = await wake(state, () => instruction, p, artifact.prepare, false, state.dependencyPending?.requested ? { kind: 'dependency', requested: state.dependencyPending.requested, ...(again ? { again: again.attempt } : {}) } : null);
          if (delivered && !state.recipeDelivered && await scanGuard(latest => { latest.recipeDelivered = true; })) state.recipeDelivered = true;
          return { state: delivered ? 'delivered' : 'busy' };
        }
        finally { artifact.close(); }
      },
    };
    // With a low budget, the dependency re-sync of all issues runs at most once an hour; between, the tick
    // uses the last eligible list and claims. Heartbeats of live claims keep their priority.
    const savedIntake = state.githubIntake;
    // One ETag cache for the reads of this tick: the intake's and the tick's own comment, PR and permission reads.
    const etags = githubEtagCache({ root: p.githubRoot, repository: state.repo, now: p.now }); p.etags = etags;
    let githubFloor;
    try { githubFloor = githubFloorGuard({ floor: githubBudgetSettings(config.github).floor, entries: githubMachineEntries({ root: p.githubRoot }), now: p.now }); } catch { githubFloor = undefined; }
    p.githubFloor = githubFloor;
    if (githubFloor) {
      const execute = p.execute;
      p.execute = async (...args) => {
        try { const result = await execute(...args); githubFloor.observe(githubReply(result.stdout)); return result; }
        catch (error) { githubFloor.observe(githubReply(error.stdout)); throw error; }
      };
    }
    const deferIntake = budget.state === 'low' && savedIntake && Number.isFinite(savedIntake.at) && p.now() - savedIntake.at < LOW_BUDGET_INTAKE_EVERY
      && Array.isArray(savedIntake.eligible) && Array.isArray(savedIntake.claims);
    let paneHold = null;
    try { await ensurePaneBudget(3, {...workflowCleanupPorts(p, ports), sweepFinished: options => (ports.tidyRuns ?? tidyRuns)({...options,timeBudgetMs:5000}, workflowCleanupPorts(p, ports))}); }
    catch (error) { if (error.code === 'herdr_pane_budget') paneHold = error.message.split('\n')[0]; }
    let intake;
    if (deferIntake) {
      intake = { eligible: savedIntake.eligible, claims: savedIntake.claims, groups: savedIntake.groups ?? [], queued: [], skipped: [] };
      p.warn(`GitHub budget low: Autopilot on this machine used ${budget.used} of ${budget.allowed} calls (${budget.share}%) in the last hour; the dependency re-sync waits until ${new Date(savedIntake.at + LOW_BUDGET_INTAKE_EVERY).toISOString()}.`);
    } else {
      // The saved dependency snapshot of this repository and the floor guard go to the intake with the ETag cache.
      const snapshotStore = dependencySnapshotStore({ root: p.githubRoot, repository: state.repo });
      try {
        intake = await (ports.reconcileDependencyIntake ?? reconcileDependencyIntake)(
          { cwd: state.cwd, repository: state.repo, trigger: completion ? 'completion' : 'tick', mode: config.mode },
          { ...ports, env: p.env, now: p.now, execFile: async (file, args, options) => p.execute(file, args, { purpose: 'dependencies', ...options }), githubCache: etags, snapshotStore, ...(githubFloor ? { githubFloor } : {}), clock: ports.clock ?? { now: async () => ({ iso: new Date(p.now()).toISOString() }) }, pending: dependencyPending, admitEffect: scanGuard, sortBudget: async () => githubBudget({ usage: githubUsage(githubMachineEntries({ root: p.githubRoot }), p.now()), ...githubBudgetSettings(config.github) }).state === 'normal', admitMutation: action => p.scanAction(action) });
      } finally { etags.save(); }
      try { p.dependencySnapshot = snapshotStore.load(); } catch { p.dependencySnapshot = null; }
      if (githubFloor?.blocked('core') || githubFloor?.blocked('graphql')) {
        const claims = ownClaimsOf(Array.isArray(savedIntake?.claims) ? savedIntake.claims : []);
        await sendHeartbeats(claims, true);
        return await outcome('unknown', 'GitHub limit is below the floor; dependency progress is saved until reset.');
      }
      if (Array.isArray(intake.eligible)) state.githubIntake = { at: p.now(), eligible: intake.eligible, claims: Array.isArray(intake.claims) ? intake.claims : [], groups: Array.isArray(intake.groups) ? intake.groups : [] };
      else delete state.githubIntake;
    }
    if (paneHold) { intake.eligible = []; state.githubIntake = {...state.githubIntake,eligible:[]}; p.warn(`Autopilot waits: panes. ${paneHold}`); }
    // Claims observed by the intake: refresh this coordinator's own live claims
    // (no AI call) and let expired claims of any owner become selectable work.
    const observedClaims = (Array.isArray(intake.claims) ? intake.claims : []).filter(claim => claim && typeof claim.issue === 'string');
    const recoveredRuns = new Set();
    // Adopt only admitted claims backed by this checkout's unfinished local runs.
    // Remote proof permits retry if the process died before the local custody write.
    for (const candidate of await (p.listRuns ?? listRuns)({ cwd: state.cwd }, { ...p, execFile: async (file, args, options) => p.execute(file, args, options) })) {
      const origin = candidate.automaticOrigin;
      if (!origin || ['completed', 'cancelled'].includes(candidate.state) || origin.machine !== state.machine
        || origin.coordinatorId === state.coordinatorId || origin.repository?.toLowerCase() !== state.repo.toLowerCase()
        || candidate.repo?.toLowerCase() !== state.repo.toLowerCase() || !samePath(candidate.sourceRoot, state.cwd)
        || !candidate.runDir || !candidate.root || !existsSync(candidate.runDir) || !existsSync(candidate.root)) continue;
      const index = observedClaims.findIndex(claim => claim.issue === candidate.issue?.url && claim.machine === state.machine
        && claim.commentId === origin.claim?.commentId && claim.labelEventId === origin.claim?.labelEventId);
      if (index < 0) continue;
      try {
        await p.scanAction(async () => {
          const release = acquireRunLock(candidate.runDir);
          try {
            const run = readRun(candidate.runDir);
            if (!run || ['completed', 'cancelled'].includes(run.state) || JSON.stringify(run.automaticOrigin) !== JSON.stringify(origin)) return;
            const recovery = await (p.recoverCoordinatorClaim ?? recoverCoordinatorClaim)({ cwd: state.cwd, repository: state.repo,
              claim: { ...observedClaims[index], coordinatorId: origin.coordinatorId, machine: origin.machine }, coordinatorId: state.coordinatorId, machine: state.machine, at: new Date(p.now()).toISOString() },
              { ...ports, now: p.now, env: p.env, execFile: async (file, args, options) => p.execute(file, args, { ...options, purpose: 'claims' }) });
            if (recovery.state !== 'recovered') return;
            updateRun(run.runDir, latest => {
              if (['completed', 'cancelled'].includes(latest.state) || JSON.stringify(latest.automaticOrigin) !== JSON.stringify(origin)) throw Error('Run custody changed during claim recovery');
              latest.automaticOrigin = { ...latest.automaticOrigin, coordinatorId: state.coordinatorId };
              return latest;
            }, p);
            observedClaims[index] = recovery.claim;
            recoveredRuns.add(run.runDir);
          } finally { release(); }
        });
      } catch (error) { p.warn(`Claim recovery deferred for ${candidate.issue?.url}: ${line(error.message)}`); }
    }
    if (config.mode === 'auto' && recoveredRuns.size) await resumeStoppedWorkers(state, p, recoveredRuns);
    // After 3 takeovers an expired claim is not offered for a 4th: it stays a hold (#3041).
    // Taking back this coordinator's own expired claim is a re-claim, not a takeover.
    const self = { coordinatorId: state.coordinatorId, machine: state.machine }, limitedFor = claim => takeoverLimited(claim, self);
    const limitedClaims = new Map(observedClaims.filter(limitedFor).map(claim => [claim.issue.toLowerCase(), claim]));
    const expiredClaims = new Map(observedClaims.filter(claim => claim.expired === true && claim.active === false && !limitedFor(claim)).map(claim => [claim.issue.toLowerCase(), claim]));
    if (state.githubIntake) state.githubIntake.claims = observedClaims;
    const ownClaims = ownClaimsOf(observedClaims);
    await sendHeartbeats(ownClaims, deferIntake);

    try { await (p.cleanupWorktrees ?? (input => cleanupWorktrees(input, { execute: p.execute })))({ cwd: state.cwd, repository: state.repo }); } catch { /* Retain unknown worktrees. */ }
    const result = p.queryIssues ? await p.queryIssues(state) : await queryIssues(state, p);
    if (result.reserveBlocked) return await outcome('unknown', 'GitHub limit is below the floor; retry after reset.');
    if (result.status === 429 || result.rateLimited) { state.retryAt = result.resetAt || p.now() + INTERVAL; return await outcome('unknown', 'GitHub rate limited; waiting until reset.'); }
    if (![200, 304].includes(result.status)) throw Error('GitHub issue check failed; check gh auth status.');
    delete state.retryAt;
    if (result.status !== 304) { state.cachedIssues = result.issues; state.etag = result.etag; }
    if (result.pages) state.pages = result.pages;
    if (typeof result.since === 'string') state.issuesSince = result.since; else if (Number.isFinite(result.fullAt)) delete state.issuesSince;
    if (Number.isFinite(result.fullAt)) state.issuesFullAt = result.fullAt;
    state.acknowledged ??= {}; state.commentCache ??= {}; state.seen ??= {}; state.timeSeen ??= {};
    cachePullRequests(state);
    const work = [], pending = {}, warnings = [], selections = [], held = new Set();
    const timeRules = [], pendingTimes = {};
    for (const claim of ownClaims) {
      const number = Number(/\/issues\/([1-9][0-9]*)$/.exec(claim.issue)?.[1]), key = `stuck:${number}`;
      if (!state.parkedNumbers?.includes(number) && !environmentNumbers.has(number) && Number.isSafeInteger(number) && stuckFor(claim) >= STUCK_CLAIM_AFTER && state.timeSeen[key] !== claim.stuckSince) {
        // After a ceiling (the repair limit of this checkout's run, or the takeover limit), a
        // retry is refused or not allowed: the rule asks for no retry and no further comment.
        // Both ceilings can hold at once: name each one, and the cancel step whenever this checkout's run has the repair limit.
        const takeover = limitedFor(claim), repair = await (p.readRepairLimited ?? readRepairLimited)(state, number, p);
        const ceiling = takeover && repair ? 'takeover limit and the repair limit' : takeover ? 'takeover limit' : repair ? 'repair limit' : null;
        timeRules.push({ kind: 'stuck-claim', number, reason: ceiling
          ? `Issue #${number} has been stuck for 4 hours after the ${ceiling}. Do not retry it, do not remove pdd:stuck and write no new comment; send the one stuck alert only if this stop has none yet. ${repair ? `To let Autopilot try again, a person removes pdd:stuck and pdd:working, then runs pdd workflow cancel ${number} in the checkout that holds the stuck run; the next tick starts a new run with a fresh repair count.` : 'A person removes pdd:stuck and pdd:working to let Autopilot try again.'} Its claim is no longer refreshed and expires in 4 hours.`
          : `Issue #${number} has been stuck for 4 hours; retry it with a changed approach or ask in the configured alert channel. Send no new alert if the cause and required decision are unchanged; another review alone is not a material change. Its claim is no longer refreshed and expires in 4 hours unless the issue leaves pdd:stuck.` });
        pendingTimes[key] = claim.stuckSince;
      }
    }
    // Per-issue ceilings (#3041), each sent once per issue. Only open issues count: a merge closes the issue.
    const openIssues = new Map((state.cachedIssues ?? []).filter(issue => !issue.pull_request && issue.state === 'open').map(issue => [String(issue.html_url).toLowerCase(), issue]));
    const issueNumber = claim => Number(/\/issues\/([1-9][0-9]*)$/.exec(claim.issue)?.[1]);
    // The 24-hour alert is once per issue across machines: a claim record of the chain
    // carries longRunningAlertedAt once it was sent. A stuck issue already has its alert.
    const longRunning = [];
    for (const claim of ownClaims) {
      const number = issueNumber(claim), key = `long:${number}`, since = Date.parse(claim.claimedAt);
      if (openIssues.has(claim.issue.toLowerCase()) && Number.isFinite(since) && p.now() - since >= LONG_RUNNING_AFTER && state.timeSeen[key] === undefined
        && claim.longRunningAlertedAt === undefined && claim.stuckSince === undefined) {
        timeRules.push({ kind: 'long-running', number, reason: `Issue #${number} was claimed 24 hours ago and has no merge yet. Send one informational alert for it, then keep working; this is not a stop.` });
        pendingTimes[key] = claim.claimedAt; longRunning.push(claim);
      }
    }
    // One coordinator acts on the takeover limit: the owner of a live claim, else the
    // coordinator that held the claim before its expired owner (when GitHub shows one).
    const actsOnLimit = claim => {
      const by = claim.active === true ? claim : claim.previousOwner;
      return !by?.coordinatorId || by.coordinatorId === state.coordinatorId && by.machine === state.machine;
    };
    for (const claim of limitedClaims.values()) {
      const number = issueNumber(claim), key = `takeover:${number}`, issue = openIssues.get(claim.issue.toLowerCase());
      const stuck = issue?.labels?.some(label => (typeof label === 'string' ? label : label.name) === 'pdd:stuck');
      if (issue && !stuck && actsOnLimit(claim) && state.timeSeen[key] === undefined) {
        timeRules.push({ kind: 'takeover-limit', number, reason: `Issue #${number} has been taken over ${claim.takeovers} times. Do not take it over again: take the stuck path (pdd:stuck, one comment with the cause, one stuck alert) and keep its claim and progress. Read the issue again first and skip it if it already has pdd:stuck. A person removes pdd:stuck to reset the count.` });
        pendingTimes[key] = claim.takeovers;
      }
    }
    const runProgress = await (p.readRunProgress ?? readRunProgress)(state, p);
    const suiteByNumber = new Map(runProgress.filter(row => row.suite).map(row => [row.number, row.suite]));
    for (const { number, changedAt, suite, interpreter } of runProgress) {
      if (suite?.state === 'unavailable') continue;
      if (suite && (suite.state !== 'finished' || suite.reason)) {
        const key = `suite:${number}:${suite.ticket ?? suite.queuedAt}`;
        if (suite.reason && state.timeSeen[key] === undefined) {
          timeRules.push({kind:'suite-failed', number, reason:`Run #${number} full test suite failed: ${suite.reason} Diagnose the suite failure and send one test-suite alert. Do not mark the issue stuck for this validation result.`});
          pendingTimes[key] = suite.finishedAt ?? suite.queuedAt;
        }
        continue;
      }
      if (['waiting', 'unavailable'].includes(interpreter?.state)) continue;
      const key = `run:${number}`;
      if (!environmentNumbers.has(number) && p.now() - changedAt >= STUCK_AFTER && state.timeSeen[key] !== changedAt) {
        timeRules.push({ kind: 'stuck-run', number, reason: `Run #${number} has had no progress for 60 minutes; follow the pdd:stuck rule.` });
        pendingTimes[key] = changedAt;
      }
    }
    await healthAlerts(state, p, dirname(stateFile));
    deferredWakes = null;
    if (!state.health.paused) {
      await environmentTick(state, p, environmentWaits, timeRules, pendingTimes, dirname(stateFile));
      await runtimeTick(state, p, completion, timeRules, pendingTimes, dirname(stateFile));
      if (config.mode === 'auto') await parkingTick(state, p, config, {wake: true, wakeRules: timeRules});
    }
    for (const issue of state.cachedIssues ?? []) {
      const labels = issue.labels?.map(x => typeof x === 'string' ? x : x.name) ?? [];
      if (issue.pull_request || issue.state !== 'open') continue;
      const selection = {number:issue.number, inScope:true, state:'unknown', reasons:['readiness-unknown']};
      selections.push(selection);
      try {
        const version = `${issue.updated_at}:${issue.comments}`;
        let rows = [];
        if (issue.comments) {
          const cached = state.commentCache[issue.number];
          rows = cached?.version === version ? cached.rows : await comments(issue.number, state, p, issue);
          state.commentCache[issue.number] = { version, rows };
        }
        const related = Object.values(state.pullCache).filter(pull => pull.refs.includes(issue.number)).sort((a, b) => a.row.number - b.row.number);
        for (const pull of related) await reviewSubmissions(pull, state, p);
        const source = digest({ issue: [issue.title, issue.body, issue.updated_at, issue.comments, [...labels].sort()], comments: rows.map(row => [row.id, row.updated_at, row.user?.login, row.body]), pulls: related.map(pull => [pull.row.number, pull.present, pull.row.updated_at, pull.row.comments, pull.row.title, pull.row.body, Object.values(pull.reviews ?? {})]) });
        const previous = state.seen[issue.number];
        const stuck = labels.includes('pdd:stuck');
        const wasStuck = previous?.stuck ?? previous?.selectionReasons?.includes('pdd:stuck') ?? false;
        const removedStuck = wasStuck && !stuck;
        // GitHub spells html_url with the owner's capitals; graph keys are canonical lowercase.
        const issueIdentity = issueKey(issue.html_url) ?? issue.html_url;
        const graphEligible = paneHold ? false : Array.isArray(intake.eligible) ? intake.eligible.some(key => (issueKey(key) ?? key) === issueIdentity) : undefined;
        const becameGraphEligible = graphEligible === true && previous && previous.graphEligible !== true;
        const expiredClaim = labels.includes('pdd:working') ? expiredClaims.get(String(issue.html_url).toLowerCase()) : undefined;
        const holdLabels = labels.filter(name => name === 'pdd:working' ? !expiredClaim : ['pdd:stuck', 'pdd:code-pending'].includes(name));
        const limitedClaim = limitedClaims.get(String(issue.html_url).toLowerCase()), limited = Boolean(limitedClaim);
        const blocked = holdLabels.length > 0, claimNote = limited ? ['takeover-limit'] : expiredClaim ? ['expired-claim'] : [];
        // A heartbeat edit of a claim comment is not issue activity. GitHub moves the issue
        // update time to the time of a comment edit, so the issue update time counts only
        // when it is later than the newest heartbeat edit.
        const heartbeatEdit = latestTime(rows.filter(heartbeat).map(row => row.updated_at)), issueUpdate = Date.parse(issue.updated_at);
        const observedClaimActivity = latestTime([...(issueUpdate > heartbeatEdit + HEARTBEAT_SLACK ? [issue.updated_at] : []), ...rows.flatMap(row => heartbeat(row) ? [row.created_at] : [row.created_at, row.updated_at])]);
        const suite = suiteByNumber.get(issue.number);
        const suiteHolds = suite && (suite.state !== 'finished' || suite.reason);
        const claimActivity = Math.max(observedClaimActivity, suite?.finishedAt ?? -Infinity);
        const claimKey = `claim:${issue.number}`;
        const claimDue = !suiteHolds && labels.includes('pdd:working') && !expiredClaim && limitedClaim?.expired !== true && Number.isFinite(claimActivity) && p.now() - claimActivity >= CLAIM_IDLE_AFTER && state.timeSeen[claimKey] !== claimActivity;
        const recheckReadyBaseline = previous?.waiting === true && graphEligible === true && !blocked;
        const unassigned = !issue.assignee && (!Array.isArray(issue.assignees) || issue.assignees.length === 0);
        const reconsiderReady = config.mode === 'auto' && graphEligible === true && !blocked && unassigned;
        const sameLimit = Boolean(previous?.selectionReasons?.includes('takeover-limit')) === limited;
        if (previous?.source === source && previous.mode === config.mode && sameLimit && !becameGraphEligible && !claimDue && !recheckReadyBaseline && !reconsiderReady) {
          if (graphEligible === false) previous.graphEligible = false;
          if (previous.view) { selection.state=previous.selectionState ?? (previous.waiting ? 'waiting' : 'ready'); selection.reasons=previous.selectionReasons ?? (previous.waiting ? ['previously-observed-wait'] : []); }
          continue;
        }
        const trustedComments = []; let acknowledged = false;
        for (const row of rows) {
          if (await trusted(row, state, config, p)) {
            if (row.body === ACK_TEXT) acknowledged = true;
            else trustedComments.push(row);
          }
        }
        const retryComment = (stuck || labels.includes('pdd:working') || wasStuck) && trustedComments.findLast(row => isRetryRequest(row.body)
          && !(previous?.view?.comments ?? []).some(old => old.id === row.id && old.updatedAt === row.updated_at && old.body === row.body)
          && (previous?.view || latestTime([row.created_at, row.updated_at]) >= Date.parse(state.activatedAt)));
        const retry = retryComment ? { source: 'comment', text: retryComment.body }
          : removedStuck ? { source: 'stuck-label-removed', text: 'Retry the failed step from retained evidence. The pdd:stuck label was removed. Preserve completed work, gates, questions, branch and claim.' } : null;
        const authorTrusted = await trusted(issue, state, config, p);
        if (!authorTrusted && !trustedComments.length) {
          selection.state='excluded'; selection.reasons=['no-trusted-issue-or-comment'];
          if (!state.acknowledged[issue.number] && !acknowledged) {
            const reply = await p.execute('gh', ['api', '--include', '--method', 'POST', `repos/${state.repo}/issues/${issue.number}/comments`, '-f', `body=${ACK_TEXT}`]);
            if (reply.code !== 0) {
              const failure = response(reply.stdout);
              if (failure.rateLimited) throw Object.assign(Error('GitHub rate limited; waiting until reset.'), { resetAt: failure.resetAt || p.now() + INTERVAL });
              throw Error('GitHub reply could not be sent; retry next tick.');
            }
          }
          state.acknowledged[issue.number] = true;
          continue;
        }
        const pulls = await relatedPullRequests(issue.number, state, config, p);
        const item = { number: issue.number, url: issue.html_url, eligible: graphEligible === true, ...(retry ? { retry } : {}), ...(labels.includes('pdd:working') ? { claimed: true } : {}), ...(expiredClaim ? { expiredClaim: { lastSeen: expiredClaim.lastSeen } } : {}), ...(authorTrusted ? { title: issue.title, body: issue.body } : {}), comments: trustedComments.map(row => ({ author: row.user.login, body: row.body })), ...(pulls.length ? { pullRequests: pulls } : {}) };
        const view = { text: authorTrusted ? { author: issue.user.login, title: item.title, body: item.body } : undefined, comments: trustedComments.map(row => heartbeat(row) ? { id: row.id, updatedAt: row.created_at, author: row.user.login, body: withoutClaimHeartbeat(row.body) } : { id: row.id, updatedAt: row.updated_at, author: row.user.login, body: row.body }), labels: labels.filter(name => !['pdd:working', 'pdd:stuck', 'pdd:code-pending'].includes(name)).sort(), ...(expiredClaim ? { expiredClaim: true } : {}), pulls: pulls.map(pull => ({ ...pull, author: state.pullCache[pull.number].row.user.login })) };
        const event = digest(view);
        const waiting = blocked || graphEligible !== true;
        if (!waiting) { selection.state='ready'; selection.reasons=[...claimNote]; }
        if (waiting && (blocked || graphEligible === false)) { selection.state='waiting'; selection.reasons=[...(blocked ? holdLabels : ['dependency-not-ready']), ...claimNote]; }
        const observed = { event, view, source, stuck, mode: config.mode, waiting, blocked, selectionState:selection.state, selectionReasons:selection.reasons, ...(graphEligible === undefined ? {} : { graphEligible }) };
        const sameTrustedWork = previous?.view && digest(await revalidateView(previous.view, state, config, p)) === event;
        const becameReady = previous && !waiting && (previous.waiting || previous.blocked && !blocked || previous.mode === 'observe' && config.mode === 'auto');
        if (!retry && !claimDue && (!previous && waiting || sameTrustedWork && !becameReady && !becameGraphEligible && !reconsiderReady)) {
          state.seen[issue.number] = observed; continue;
        }
        if (!retry && graphEligible !== true && !labels.includes('pdd:working') && !claimDue) {
          state.seen[issue.number] = observed; continue;
        }
        work.push(item); pending[issue.number] = observed;
        if (blocked || retry) held.add(item);
        if (claimDue) {
          timeRules.push({ kind: 'idle-claim', number: issue.number, reason: `Issue #${issue.number} has a pdd:working claim idle for about 1 hour; review stalled work under the skill's claim rule. Age alone does not authorize takeover or release the claim.` });
          pendingTimes[claimKey] = claimActivity;
        }
      } catch (error) {
        if (error.resetAt) throw error;
        warnings.push(`Deferred #${issue.number}: ${line(error.message)}`);
        p.warn(warnings.at(-1));
      }
    }
    // Fresh work leads to a claim and a workflow start, so offer it only where workflows can start.
    // A held issue (pdd:stuck, pdd:code-pending) is not fresh: its reviews and trusted comments still go out.
    const fresh = work.filter(item => item.eligible && !held.has(item) && (!item.claimed || item.expiredClaim));
    if (config.mode === 'auto' && fresh.length) {
      const existing = await parkingPorts(state, p).list();
      for (const item of [...fresh]) {
        const group = (state.githubIntake?.groups ?? []).find(group => group.members?.some(key => Number(/\/issues\/(\d+)$/.exec(key)?.[1]) === item.number));
        const retained = group && existing.find(run => !['completed', 'cancelled'].includes(run.state) && group.members.includes(run.issue?.url));
        if (!retained && !state.parking?.wakePending?.length) continue;
        if (retained) {
          const request = `Issue #${item.number} belongs to this run's root-cause group. Keep it with this run and its saved work.\n${JSON.stringify(item)}`;
          await p.scanAction(() => changeRun({ref: String(retained.number), cwd: state.cwd, packageRoot: state.packageRoot, text: request}, {...p, queueOnly: Boolean(retained.parking), requestKey: `group:${retained.runId}:${item.number}`, execFile: p.execFile ?? (async (file, args, options) => p.execute(file, args, options))}));
        }
        work.splice(work.indexOf(item), 1); delete pending[item.number];
        const selected = selections.find(row => row.number === item.number);
        if (selected) {selected.state = 'waiting'; selected.reasons = [retained ? 'group-run' : 'parked-wake-first'];}
      }
    }
    if (fresh.some(item => work.includes(item))) {
      const readiness = await workflowReadiness(state, p);
      if (readiness.state !== 'ready') {
        warnings.push(`Autopilot held ${fresh.length} issue(s): pdd workflows cannot start in ${state.cwd}. ${line(readiness.message)}`);
        p.warn(warnings.at(-1));
        for (const item of fresh) {
          work.splice(work.indexOf(item), 1); delete pending[item.number];
          const selection = selections.find(row => row.number === item.number);
          if (selection) { selection.state = 'waiting'; selection.reasons = ['workflows-unavailable']; }
        }
      }
    }
    if (!await scanGuard()) return await outcome('inactive', 'Autopilot changed.');
    let delivered = false;
    const metricsContext=p.metricsContext ?? (cwd=>gitContext(cwd,{execFile:(file,args,options)=>p.execute(file,args,options)}));
    const metricsFiles={...nativeFiles,...p.metricsFiles};
    const metricsWarn=message=>{try{p.warn(message);}catch{}};
    const metricsGap=input=>(p.metricsGap ?? recordCaptureGap)(input,metricsFiles);
    {
      try {
        const context=await metricsContext(state.cwd), source=metricsSource({commonDir:context.commonDir},metricsFiles,p.now);
        const folder=join(context.commonDir,'pdd','metrics','decisions'); metricsFiles.mkdirSync(folder,{recursive:true,mode:0o700});
        const at=new Date(p.now()).toISOString(), snapshotId=`snapshot:${randomUUID()}`, events=[];
        for (const selection of selections) {
          const item=work.find(row => row.number===selection.number);
          const id=randomUUID(), file=join(folder,`${id}.json`), temp=join(folder,`.${id}.tmp`), fd=metricsFiles.openSync(temp,'wx',0o600);
          const base={schema:'pdd.metrics.event.v1',repo:state.repo.toLowerCase(),issue:selection.number,at,observedAt:at,source};
          const facts=[{...base,id:`${id}:selection`,type:'selection',data:{snapshotId,inScope:selection.inScope,state:selection.state,reasons:selection.reasons}}];
          try { metricsFiles.writeFileSync(fd,JSON.stringify({id,repo:state.repo.toLowerCase(),issue:selection.number,snapshotId,at,offered:!!item,pendingSnapshot:true,events:facts})); metricsFiles.fsyncSync(fd); } finally { metricsFiles.closeSync(fd); }
          metricsFiles.renameSync(temp,file);
          if (item) item.decisionId=id; events.push(...facts);
        }
        const fd=metricsFiles.openSync(folder,'r'); try { metricsFiles.fsyncSync(fd); } finally { metricsFiles.closeSync(fd); }
        // Publish the complete issue membership only after all decisions are durable.
        const snapshots=join(context.commonDir,'pdd','metrics','snapshots'); metricsFiles.mkdirSync(snapshots,{recursive:true,mode:0o700});
        const snapshotFile=join(snapshots,`${snapshotId.slice(9)}.json`), snapshotTemp=`${snapshotFile}.tmp`;
        const snapshotFd=metricsFiles.openSync(snapshotTemp,'wx',0o600);
        try { metricsFiles.writeFileSync(snapshotFd,JSON.stringify({snapshotId,repo:state.repo.toLowerCase(),observedAt:at,source,events})); metricsFiles.fsyncSync(snapshotFd); } finally { metricsFiles.closeSync(snapshotFd); }
        metricsFiles.renameSync(snapshotTemp,snapshotFile);
        const snapshotDirFd=metricsFiles.openSync(snapshots,'r'); try {metricsFiles.fsyncSync(snapshotDirFd);} finally {metricsFiles.closeSync(snapshotDirFd);}
        try { await (p.metricsAppendEvents ?? (input=>appendEvents(input,{commonDir:async()=>context.commonDir})))({root:state.cwd,events}); } catch { for (const selection of selections) try {metricsGap({commonDir:context.commonDir,repo:state.repo,issue:selection.number,at:p.now()});} catch {} metricsWarn('Metrics selection capture incomplete.'); }
      } catch {
        try { const context=await metricsContext(state.cwd); for (const selection of selections) metricsGap({commonDir:context.commonDir,repo:state.repo,issue:selection.number,at:p.now()}); } catch { /* No writable storage remains; the warning is the available evidence. */ }
        if (selections.length) metricsWarn('Metrics decision capture incomplete; workflow origin remains unknown.');
      }
    }
    if (!state.health.paused && (work.length || timeRules.length || !state.recipeDelivered || state.health.recoveryPending != null)) {
      const capture = async status => {
        try {
          const context=await metricsContext(state.cwd), at=new Date(p.now()).toISOString(), source=metricsSource({commonDir:context.commonDir},metricsFiles,p.now);
          const events=work.filter(item=>item.decisionId).map(item=>({schema:'pdd.metrics.event.v1',id:`${item.decisionId}:launch:${status}`,repo:state.repo.toLowerCase(),issue:item.number,type:'launch',at,observedAt:at,source,data:{origin:'autopilot',decisionId:item.decisionId,status}}));
          for (const event of events) {
            const file=join(context.commonDir,'pdd','metrics','decisions',`${event.data.decisionId}.json`);
            const record=JSON.parse(metricsFiles.readFileSync(file,'utf8'));
            if (!record.events.some(row=>row.id===event.id)) record.events.push(event);
            const temp=`${file}.${randomUUID()}.tmp`, fd=metricsFiles.openSync(temp,'wx',0o600);
            try { metricsFiles.writeFileSync(fd,JSON.stringify(record)); metricsFiles.fsyncSync(fd); } finally { metricsFiles.closeSync(fd); }
            metricsFiles.renameSync(temp,file);
            const dirfd=metricsFiles.openSync(dirname(file),'r'); try { metricsFiles.fsyncSync(dirfd); } finally { metricsFiles.closeSync(dirfd); }
          }
          if(events.length) await (p.metricsAppendEvents ?? (input=>appendEvents(input,{commonDir:async()=>context.commonDir})))({root:state.cwd,events});
        } catch { try { const context=await metricsContext(state.cwd); for(const item of work) metricsGap({commonDir:context.commonDir,repo:state.repo,issue:item.number,at:p.now()}); } catch {} if (work.length) metricsWarn('Metrics launch capture incomplete.'); }
      };
      delivered = await wake(state, () => message(state, work, timeRules), p, async () => {}, ports.explicitStartReconcile === true, { kind: 'work', events: Object.fromEntries(Object.entries(pending).map(([key, value]) => [key, value.event])), times: pendingTimes, recipe: !state.recipeDelivered }, capture);
      if (delivered) { state.recipeDelivered = true; state.health.recoveryPending = null; Object.assign(state.seen, pending); Object.assign(state.timeSeen, pendingTimes); }
      // Record the delivered 24-hour alert in the own claim comment, so that no machine sends it again.
      if (delivered) for (const claim of longRunning) {
        try {
          await (p.recordLongRunningAlert ?? recordLongRunningAlert)({ cwd: state.cwd, repository: state.repo, claim, coordinatorId: state.coordinatorId, machine: state.machine, at: new Date(p.now()).toISOString() },
            { execFile: async (file, args, options) => p.execute(file, args, options), admitMutation: action => p.scanAction(action) });
        } catch (error) { p.warn(`Long-running alert record deferred for ${claim.issue}: ${line(error.message)}`); }
      }
    }
    return await outcome('reconciled', [delivered ? `Autopilot offered ${work.length} issue(s).` : 'Autopilot tick complete.', ...warnings].join(' '));
  } catch (e) {
    if (e.resetAt) { state.retryAt = e.resetAt; return await outcome('unknown', 'GitHub rate limited; waiting until reset.'); }
    throw e;
  } finally {
    try {
      if (state && scanGuard) await scanGuard(latest => {
        for (const key of ['defaultBranch','baseBranch','retryAt','cachedIssues','etag','pages','issuesSince','issuesFullAt','githubIntake','acknowledged','commentCache','seen','timeSeen','pullCache','recipeDelivered','dependencyPending','deliveryIntent','reconciliationIntent','uncertainDeliveryHistory','paneId','workspaceId','ownerLaunch','contextPane','contextBinding','relaunchPending','relaunchHeld','runtime','health','parking','parkedNumbers','interpreterPattern']) {
          if (Object.hasOwn(state, key)) latest[key] = state[key]; else delete latest[key];
        }
        latest.nextTick = (ports.now ?? Date.now)() + INTERVAL;
      });
    } finally {
      // The tick's own conditional reads after the intake keep their ETags too.
      try { p?.etags?.save(); } catch { /* A lost cache only costs counted reads. */ }
      // Keep the ledger small: entries older than 2 hours go.
      if (p && state?.repo) githubLedger({ root: p.githubRoot, repository: state.repo }).compact(p.now());
      unlinkSync(lock);
    }
  }
}

async function verifiedCustody(state, path, p, runs) {
  const projection = read(path);
  const keys = ['repository','sourceRoot','coordinatorId','machine','activation','paneId','workspaceId','agent','home','definitionHome','configHome','launchStartedAt'];
  if (!projection || typeof projection !== 'object' || Array.isArray(projection) || Object.keys(projection).length !== keys.length || !keys.every(key => Object.hasOwn(projection,key))) throw Error('Invalid original coordinator custody projection.');
  if (!projection.agent || typeof projection.agent.id !== 'string' || !projection.agent.id || !['codex','claude','gemini','agy'].includes(projection.agent.kind)
      || !['repository','sourceRoot','coordinatorId','machine','activation','paneId','workspaceId','home','definitionHome'].every(key => typeof projection[key] === 'string' && projection[key])
      || !(projection.configHome === null || typeof projection.configHome === 'string' && projection.configHome) || !Number.isFinite(projection.launchStartedAt)
      || !samePath(projection.sourceRoot,state.cwd) || projection.repository.toLowerCase() !== state.repo.toLowerCase()) throw Error('Original coordinator custody does not match this repository.');
  const variable = {codex:'CODEX_HOME',claude:'CLAUDE_CONFIG_DIR',gemini:'GEMINI_CLI_HOME'}[projection.agent.kind];
  const environment = { ...state.environment, HOME:projection.home };
  for (const name of ['CODEX_HOME','CLAUDE_CONFIG_DIR','GEMINI_CLI_HOME']) { if (name === variable && projection.configHome) environment[name] = projection.configHome; else delete environment[name]; }
  const coordinator = {version:'pdd.autopilot-coordinator.v1',repository:state.repo,coordinatorId:projection.coordinatorId,machine:projection.machine,activation:projection.activation,...(runs === undefined ? {} : {runs:Number(runs)})};
  const profile = {agent:projection.agent,home:projection.home,definitionHome:projection.definitionHome,configHome:projection.configHome};
  const candidate = {...state,coordinatorId:projection.coordinatorId,machine:projection.machine,activatedAt:projection.activation,paneId:projection.paneId,workspaceId:projection.workspaceId,agent:{...projection.agent,command:projection.agent.id},definitionHome:projection.definitionHome,environment,ownerLaunch:{paneId:projection.paneId,startedAt:projection.launchStartedAt,coordinator,profile}};
  const probeEnv = {...p.env,HOME:projection.definitionHome};
  for (const name of ['CODEX_HOME','CLAUDE_CONFIG_DIR','GEMINI_CLI_HOME']) { if (name === variable && projection.configHome) probeEnv[name]=projection.configHome; else delete probeEnv[name]; }
  const saved = {...profile,configVariable:variable}, probe = {...p,env:probeEnv};
  const selected = p.selectAgent ? await p.selectAgent(candidate,probe) : await selectAgent(candidate,probe,saved);
  if (!selected || selected.id !== projection.agent.id || selected.kind !== projection.agent.kind) throw Error('The original coordinator profile is unavailable.');
  candidate.agent.command = selected.command;
  if (!await currentRecoveryTargetMatches(candidate,p,true)) throw Error('The original coordinator target cannot be verified.');
  const records = await (p.listRuns ?? listRuns)({cwd:state.cwd},p);
  const affected = records.filter(run => !['cancelled','completed'].includes(run.state) && run.automaticOrigin?.coordinatorId === projection.coordinatorId && run.repo?.toLowerCase() === state.repo.toLowerCase());
  if (affected.length) {
    const issues=affected.map(run=>run.issue?.url ?? `https://github.com/${run.repo}/issues/${run.number}`);
    const result=await createDependencyReadPorts({cwd:state.cwd},p).owners.read({repository:state.repo,issues});
    const observation=typeof result.json === 'string' ? JSON.parse(result.json) : result.json;
    for (const [index,run] of affected.entries()) {
      const origin=run.automaticOrigin, claims=observation?.claims?.filter(claim=>claim.issue===issues[index] && claim.active===true) ?? [];
      if (origin.repository?.toLowerCase() !== state.repo.toLowerCase() || origin.machine !== projection.machine || claims.length !== 1 || !['commentId','labelEventId'].every(key => typeof origin.claim?.[key] === 'string' && origin.claim[key].trim() && typeof claims[0][key] === 'string' && claims[0][key].trim()) || claims[0].owner !== projection.coordinatorId || claims[0].coordinatorId !== projection.coordinatorId || claims[0].machine !== projection.machine || claims[0].commentId !== origin.claim.commentId || claims[0].labelEventId !== origin.claim.labelEventId) throw Error('Original coordinator claim cannot be verified.');
    }
  }
  const intent=state.reconciliationIntent ?? state.deliveryIntent;
  if (intent && !recoveryTargetMatches(candidate,intent,p)) throw Error('Existing delivery custody does not match the original coordinator.');
  return candidate;
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
      await runTick(identity.stateFile, { ...ports, expectedStart:identity, explicitStartReconcile:true, tickBusy:() => { busy = true; } }, false);
      if (!busy) return;
    }
  } catch { /* A later supported start or timer can reconcile. */ }
}

function armCoordinatorIdle(identity, { env }) {
  const child = spawn(process.execPath, [self, '--coordinator-idle', JSON.stringify(identity)], { detached:true, stdio:'ignore', env });
  child.on('error', () => {}); child.unref();
}
async function waitCoordinatorIdle(identity, ports = {}) {
  const wait = ports.wait ?? (() => new Promise((resolveWait, reject) => {
    const child = spawn('herdr', ['--session', SESSION, 'agent', 'wait', identity.paneId, '--until', 'idle', '--until', 'done'], { stdio:'ignore', env:ports.env ?? process.env });
    child.once('error', reject); child.once('close', code => code === 0 ? resolveWait() : reject(Error('Coordinator wait failed')));
  }));
  try {
    await wait();
    const state = read(identity.stateFile);
    if (!state?.enabled || !['cwd','repo','paneId','workspaceId','coordinatorId','machine','controlRevision'].every(key => state[key] === identity[key])) return;
    if (!await currentRecoveryTargetMatches(state, portsFor(state, ports), true, identity.session)) return;
    await runTick(identity.stateFile, { ...ports, env:ports.env }, true);
  } catch { /* The next supported start or timer can reconcile. */ }
}

export async function requestAutopilotCompletion({ cwd, env }, ports = {}) {
  try {
    const initial = { cwd, environment: keepEnv(env ?? process.env) };
    const p = portsFor(initial, { ...ports, env });
    const root = (await p.checked('git', ['rev-parse', '--show-toplevel'])).trim();
    if (!root) return { state: 'unknown' };
    const id = createHash('sha256').update(root).digest('hex').slice(0, 20);
    const folder = ports.stateRoot ?? join(p.env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
    const stateFile = join(folder, `${id}.json`); let deferred;
    const result = await runTick(stateFile, { ...ports, env, coordinatorDeferred: (state, agent) => { deferred = { session:JSON.stringify(agent?.agent_session ?? null), stateFile, cwd:state.cwd, repo:state.repo, paneId:state.paneId, workspaceId:state.workspaceId, coordinatorId:state.coordinatorId, machine:state.machine, controlRevision:state.controlRevision }; } }, true);
    if (deferred && result.state === 'reconciled') {
      try { (ports.armCoordinatorIdle ?? armCoordinatorIdle)(deferred, { env:p.env, resume: () => waitCoordinatorIdle(deferred, { ...ports, env:p.env }) }); } catch { return {state:'unknown'}; }
    }
    return result;
  } catch { return { state: 'unknown' }; }
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
// Every saved launcher state on this machine, read-only: local files, timer status and Herdr only.
// Each line is independent. Timer and Herdr reads run from the caller's folder, never from a saved folder.
async function machineStatus(folder, ports, env, cwd) {
  let names = [];
  try { names = readdirSync(folder).filter(name => /^[0-9a-f]{20}\.json$/.test(name)).sort(); }
  catch (error) { if (error.code !== 'ENOENT') throw error; }
  const here = isFolder(cwd) ? cwd : env?.HOME || homedir();
  let serverRunning = false;
  if (names.length) { try { serverRunning = (await herdr(['status', 'server', '--json'], portsFor({ cwd: here }, { ...ports, env }))).running === true; } catch { /* Herdr is not running. */ } }
  const rows = [];
  for (const name of names) {
    let saved;
    try { saved = read(join(folder, name), GONE); } catch { saved = null; }
    if (saved === GONE) continue;
    if (!saved || typeof saved !== 'object' || Array.isArray(saved)) { rows.push(`${name}: saved state unreadable`); continue; }
    const state = { ...saved, id: name.slice(0, -5), stateFile: join(folder, name) };
    const p = portsFor({ ...state, cwd: here }, { ...ports, env });
    const mode = await savedMode(state, ports, env);
    let timerState = 'unknown';
    try { timerState = await timer('status', state, p) ? 'active' : 'inactive'; } catch { /* Report unknown. */ }
    let coordinator = { state: 'unavailable', reason: 'Herdr is not running' };
    if (serverRunning) { try { coordinator = await coordinatorHealth(state, p); } catch { coordinator = { state: 'unavailable', reason: 'status unreadable' }; } }
    rows.push(`${typeof state.repo === 'string' ? line(state.repo) : 'repository unknown'} in ${typeof state.cwd === 'string' ? line(state.cwd) : 'an unknown folder'} · base ${line(state.baseBranch ?? 'unavailable (start Autopilot)')} · mode ${mode} · Autopilot ${state.enabled ? 'enabled' : 'disabled'} · timer ${timerState} · coordinator ${coordinator.state === 'unavailable' ? `unavailable (${coordinator.reason})` : coordinator.state} · ${healthLine(state.health)} · ${parkingWords(state.parking, state.interpreterPattern)}`);
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
  const { command, packageRoot, runs, checks, resumeCustody, issues = [] } = input;
  let state = { cwd: input.cwd, environment: keepEnv(input.env ?? process.env) };
  let p = portsFor(state, { ...ports, env: input.env });
  let controlLock, releaseAdmission;
  try {
    if (command === 'check-base') {
      const found = await resolveRun(issues[0], { cwd: input.cwd }, { ...ports, env: p.env, execFile: async (file, args, options) => ({ stdout: await p.checked(file, args, options) }) });
      if (found.error) return bad(found.error);
      state.repo = found.run.repo;
      return checkAutopilotBase({ run: found.run, pr: issues[1] }, { execFile: async (file, args, options) => ({ stdout: await p.checked(file, args, options) }) });
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
    let initialRevision = previous?.controlRevision ?? null;
    if (command === 'start' && !previous) { initialRevision = randomUUID(); state.controlRevision = initialRevision; state.enabled = false; state.timerInstalled = false; state.nextTick = null; save(stateFile, state); }
    p = portsFor(state, { ...ports, env: input.env });
    if (command === 'start') { releaseAdmission(); releaseAdmission = null; }
    if (command === 'status') {
      const timerActive = Boolean(await timer('status', state, p));
      let serverRunning = false;
      try { serverRunning = (await herdr(['status', 'server', '--json'], p)).running === true; } catch { /* Report unavailable below. */ }
      const coordinator = serverRunning
        ? await coordinatorHealth(state, p)
        : { state: 'unavailable', reason: 'Herdr is not running' };
      const coordinatorState = coordinator.state === 'unavailable'
        ? `unavailable (${coordinator.reason})` : coordinator.state;
      const marked = mark => mark && mark.paneId === state.paneId && mark.startedAt === state.ownerLaunch?.startedAt;
      const relaunch = (marked(state.relaunchPending)
        ? '\nCoordinator relaunch pending after upgrade: the old chat ends when it is idle, then a fresh chat starts with the current launch settings.' : '')
        + (marked(state.relaunchHeld)
          ? '\nCoordinator relaunch held: the launch settings changed again after a relaunch for the same settings, so the current chat stays and gets work. Close the coordinator pane in Herdr to start a fresh chat with the current settings.' : '');
      let alerts = '';
      try { alerts = (ports.alertStatusLine ?? alertStatusLine)({ repo: state.repo, env: p.env }, { stateRoot: ports.stateRoot }); } catch { /* Alerts never change status. */ }
      // The GitHub calls of the last hour, from the local ledgers only: status makes no GitHub call.
      let github = '';
      try {
        if (state.repo) {
          const now = p.now(), usage = githubUsage(githubLedger({ root: p.githubRoot, repository: state.repo }).read(), now);
          const machine = githubUsage(githubMachineEntries({ root: p.githubRoot }), now);
          if (usage.calls || machine.calls) {
            let setting;
            try { setting = (await settings(state, p)).github; } catch { /* The defaults apply. */ }
            github = githubStatusLine({ usage, machine, budget: githubBudget({ usage: machine, ...githubBudgetSettings(setting) }) });
          }
        }
      } catch { /* The GitHub line never changes status. */ }
      const groups = (state.githubIntake?.groups ?? []).map(g => `Group: ${g.members.length} issues; ${g.rootCause}; umbrella ${g.umbrella || 'pending'}`).join('\n');
      let costs = '';
      try { costs = '\n' + costStatusLines(await localCosts(input, ports, state)); } catch {}
      const readiness = await workflowReadiness(state, p);
      const local = parkingPorts(state, p);
      const runs = (await local.list()).filter(run => run.automaticOrigin?.coordinatorId === state.coordinatorId);
      const observed = await Promise.all(runs.map(async run => ({...run, checkHeld: await local.checkProgress(run)})));
      const capacityLine = checkCapacityWords(state, p) + '\n' + parkingWords(parkingSummary(observed, state.runs ?? state.checkCapacity?.runs ?? 1), state.interpreterPattern);
      const workflows = readiness.state === 'ready' ? '' : `\nWorkflows cannot start in this folder: ${line(readiness.message)}`;
      return ok(`Autopilot ${state.enabled ? 'enabled' : 'disabled'}; timer ${timerActive ? 'active' : 'inactive'}; Herdr ${serverRunning ? 'running' : 'unavailable'}; coordinator ${coordinatorState}: ${state.repo ? `${state.repo} in ${state.cwd}` : state.cwd} · base ${line(state.baseBranch ?? 'unavailable (start Autopilot)')} · ${state.agent?.id ?? 'no agent'} · next tick: ${timerActive && state.nextTick ? new Date(state.nextTick).toISOString() : 'none'}${workflows}\n${capacityLine}${relaunch}\n${healthLine(state.health)}${alerts ? `\n${alerts}` : ''}${github ? `\n${github}` : ''}${costs}${groups ? `\n${groups}` : ''}`);
    }
    if (command === 'stop') {
      if (previous) { state.enabled = false; state.nextTick = null; state.controlRevision = randomUUID(); save(stateFile, state); }
      await timer('stop', state, p);
      await releaseCheckCapacity({env:p.env,owner:stateFile}, p.checkCapacityPorts ?? p);
      if (previous) { state.timerInstalled = false; save(stateFile, state); }
      return ok('Autopilot stopped on this machine; the current step can finish.');
    }
    for (const [name,value] of [['runs',runs],['checks',checks]]) if (command === 'start' && value !== undefined && (!/^[1-9][0-9]*$/.test(value) || !Number.isSafeInteger(Number(value)))) return {exitCode:2,message:`Use --${name} with a positive safe integer, or omit it for machine capacity.`};
    if (command === 'start') {
      const config = await settings(state, p);
      if (config.mode === 'off') return ok(`${line(config.message)} Choose observe or auto with pdd autopilot observe or pdd autopilot auto.`);
      if (previous && resolve(previous.packageRoot ?? dirname(dirname(self))) !== resolve(packageRoot)) state.recipeDelivered = false;
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
    if (command !== 'start') return { exitCode: 2, message: 'Use pdd autopilot start, stop, status or add.' };
    const readiness = await workflowReadiness(state, p);
    if (readiness.state !== 'ready') return bad(`Autopilot did not start: pdd workflows cannot start in ${state.cwd}. ${readiness.message} Nothing was started or claimed, and every timer is unchanged.`);
    const priorBase = state.baseBranch;
    await automaticBase(state, p);
    if (priorBase !== state.baseBranch) state.recipeDelivered = false;
    if ((await p.execute('gh', ['auth', 'status'])).code !== 0) return bad('GitHub is not signed in; run gh auth login.');
    try { if ((await p.execute('herdr', ['--version'])).code !== 0) throw Error(); }
    catch { return bad('Herdr is missing or unavailable; install Herdr, then run herdr --help.'); }
    if (resumeCustody && !previous) return bad('Original coordinator recovery needs saved local state.');
    const previousProfile = previous?.agent && !resumeCustody ? profileBinding(previous, p) : null;
    let probe = p, saved = null;
    if (previousProfile) {
      const launchedProfile = previous.ownerLaunch?.profile ?? previous.launchProfile;
      if (!launchedProfile || JSON.stringify(launchedProfile) !== JSON.stringify(previousProfile) || !previousProfile.home || !previousProfile.definitionHome) return bad('The saved coordinator profile cannot be verified. Inspect the existing coordinator before retrying.');
      const configVariable = { codex:'CODEX_HOME', claude:'CLAUDE_CONFIG_DIR', gemini:'GEMINI_CLI_HOME' }[previous.agent.kind];
      const env = { ...p.env, HOME:previousProfile.definitionHome };
      for (const variable of ['CODEX_HOME','CLAUDE_CONFIG_DIR','GEMINI_CLI_HOME']) {
        if (variable === configVariable && previousProfile.configHome) env[variable] = previousProfile.configHome; else delete env[variable];
      }
      saved = { ...previousProfile, configVariable }; probe = { ...p, env };
    }
    const agent = resumeCustody ? {id:previous?.agent?.id,kind:previous?.agent?.kind} : ports.selectAgent ? await ports.selectAgent(state, probe) : await selectAgent(state, probe, saved);
    if (!agent || saved && (agent.id !== saved.agent.id || agent.kind !== saved.agent.kind)) return bad(saved ? 'The saved coordinator profile is unavailable. Restore its sign-in and retry.' : 'Sign in to Codex, Claude Code, agy or Gemini at your terminal, then run pdd autopilot start.');
    const version = read(join(packageRoot, 'package.json')).version;
    const warnings = (ports.pathDiagnostic ?? pathDiagnostic)({ cwd: state.cwd, packageRoot, env: p.env, mode: 'workflow' });
    const pendingCustody = Boolean(previous?.deliveryIntent || previous?.reconciliationIntent);
    if (!pendingCustody && !previousProfile && !resumeCustody) {
      state.agent = { id: agent.id, kind: agent.kind, command: agent.command };
      state.definitionHome = p.env.HOME;
      state.environment = keepEnv({ ...p.env, ...agent.env });
    }
    state.activatedAt ??= new Date(p.now()).toISOString();
    state.coordinatorId ??= randomUUID(); state.machine ??= hostname();
    state.enabled = true; state.timerInstalled = true; state.nextTick = p.now() + INTERVAL;
    state.controlRevision = randomUUID();
    if (runs !== undefined) state.runs = Number(runs); else if (!pendingCustody) delete state.runs;
    if (checks !== undefined) state.checks = Number(checks); else if (!pendingCustody) delete state.checks;
    const priorRevision = initialRevision;
    if (!pendingCustody && !resumeCustody) await openWorkspace(state, p);
    releaseAdmission = await claimAdmission(state, p);
    if (!releaseAdmission) return bad('Timed out waiting for the current Autopilot operation; retry.');
    if ((read(stateFile)?.controlRevision ?? null) !== priorRevision) return bad('Autopilot changed while starting; retry.');
    const currentConfig = await settings(state, p);
    if (currentConfig.mode === 'off') return ok(`${line(currentConfig.message)} Choose observe or auto with pdd autopilot observe or pdd autopilot auto.`);
    if (resumeCustody) {
      state = await verifiedCustody(state, resolve(input.cwd, resumeCustody), p, runs);
      const recoveredEnv = {...p.env,...state.environment};
      for (const name of ['CODEX_HOME','CLAUDE_CONFIG_DIR','GEMINI_CLI_HOME']) if (!Object.hasOwn(state.environment,name)) delete recoveredEnv[name];
      p = portsFor(state, {...ports,env:recoveredEnv});
      state.enabled = true; state.timerInstalled = true; state.nextTick = p.now() + INTERVAL; state.controlRevision = randomUUID(); state.packageRoot = packageRoot; state.recipeDelivered = false;
      if (runs === undefined) delete state.runs; else state.runs = Number(runs);
      if (checks === undefined) delete state.checks; else state.checks = Number(checks);
    }
    await automaticBase(state, p);
    try { await timer('start', state, p); }
    catch {
      if (!previous) { state.enabled = false; state.nextTick = null; state.controlRevision = initialRevision; delete state.activatedAt; delete state.runs; save(stateFile, state); }
      return bad('Autopilot timer could not start; enable your systemd user session on Linux or launchctl user session on macOS, then retry.');
    }
    if (!previous?.startAction || previous.startAction.repository !== state.repo || previous.startAction.mode !== currentConfig.mode) state.recipeDelivered = false;
    state.startAction = { command: 'pdd autopilot start', repository: state.repo, mode: currentConfig.mode };
    save(stateFile, state);
    let warning = '';
    if ((p.platform ?? process.platform) === 'linux') {
      let linger = '';
      try { const result = await p.execute('loginctl', ['show-user', String(p.uid ?? process.getuid()), '--property=Linger', '--value']); if (result.code === 0) linger = result.stdout.trim(); } catch { /* Optional session diagnostic. */ }
      if (linger !== 'yes') warning = ' To keep Autopilot running after logout, enable lingering: loginctl enable-linger.';
    }
    releaseAdmission(); releaseAdmission = null;
    const { armed: recoveryCount, unavailable: recoveryUnavailable } = rearmWorkerCompletion(state, p);
    if (recoveryCount || recoveryUnavailable) warning += ` Worker completion observation ${recoveryUnavailable ? 'is unavailable for some saved workers' : 'was rearmed'}. If unavailable, inspect the worker and run pdd workflow yield ISSUE after positive completion evidence.`;
    try {
      let busy = false;
      await runTick(stateFile, { ...ports, env: p.env, explicitStartReconcile: true, tickBusy: () => { busy = true; } }, false);
      if (busy) {
        const identity = { stateFile, cwd:state.cwd, repo:state.repo, coordinatorId:state.coordinatorId, machine:state.machine, controlRevision:state.controlRevision };
        (ports.armStartScan ?? armStartScan)(identity, { env:p.env, resume: () => waitStartScan(identity, { ...ports, env:p.env }) });
      }
    }
    catch (e) { warning += ` Warning: ${line(e.message)}; next tick will retry.`; }
    return ok(`Autopilot started for ${state.repo} in ${state.cwd}. Base ${state.baseBranch}. Agent ${state.agent.id} · pdd ${version} · next tick: ${new Date(state.nextTick).toISOString()}. See: herdr session attach ${SESSION}.${warning}${warnings.length ? ' ' + warnings.map(line).join(' ') : ''}`);
  } catch (e) { return bad(e.exact ? e.message : `Autopilot: ${e.code === 'ENOENT' ? 'install git, gh and Herdr, and sign in to your agent, then retry.' : line(e.message)}`); }
  finally { releaseAdmission?.(); controlLock?.(); }
}

if (process.argv[1] && resolve(process.argv[1]) === self) {
  if (process.argv[2] === '--start-scan-wait') { try { await waitStartScan(JSON.parse(process.argv[3])); } catch { process.exitCode = 1; } }
  else if (process.argv[2] === '--coordinator-idle') { try { await waitCoordinatorIdle(JSON.parse(process.argv[3])); } catch { process.exitCode = 1; } }
  else tickAutopilot(process.argv[2]).catch(error => { process.stderr.write(`Autopilot: ${line(error.message)}\n`); process.exitCode = 1; });
}
