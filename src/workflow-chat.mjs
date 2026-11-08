// Generated from prompts/cli/workflow-chat.prompt.md (sha256: 3054665c11cc91f58c5c2c1c04a4c025ca151265b8778065b4aa4a7c51597fb9).
import { execFile as execFileCallback, spawn } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { statSync, lstatSync, readdirSync, writeFileSync, readFileSync, mkdirSync, rmSync } from 'node:fs';
import { homedir } from 'node:os';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
const PACKAGE_BIN = join(dirname(dirname(fileURLToPath(import.meta.url))), 'bin/pdd.mjs');
import { promisify } from 'node:util';
import { PDD_HERDR_SESSION, withHerdrLayoutLock, openHerdrRunLayout, closeHerdrRunLayout, closeHerdrRepoLayoutIfIdle, samePath } from './workflow-herdr-layout.mjs';
import { findNativeSessions } from './approval-evidence.mjs';
import { tomlString } from './toml-string.mjs';
import { lookupIssueWorktree } from './workflow-worktree.mjs';
import { LOGIN_VARIABLES, reservedEnvMessage } from './workflow-agents.mjs';
import { loadAgentDefinitions } from './agent-config.mjs';

// The one shared startup grace: Herdr sees a new agent only after it starts.
export const START_GRACE_MS = 30_000;
const SHELLS = new Set(['bash','zsh','sh','dash','fish','ksh','tcsh']);
const ordinary = promisify(execFileCallback);
const quote = value => `'${String(value).replace(/'/g, `'\\''`)}'`;
const problem = (code, message) => Object.assign(Error(message ?? code), { code });
// Native session ids (Claude --session-id, Codex rollouts) are UUIDs; anything else never reaches a shell line.
export const validSessionId = id => typeof id === 'string' && /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(id);
// Markers that make a native agent think it runs inside another agent session (Claude then stops saving transcripts).
const AGENT_MARKER = /^(?:CLAUDECODE|CLAUDE_CODE_(?:CHILD_SESSION|SESSION_ID|SESSION_ATTENDED|ENTRYPOINT|MESSAGING_SOCKET|MESSAGING_TOKEN|EXECPATH)|CLAUDE_PID|CODEX_THREAD_ID|CODEX_SANDBOX[A-Z_]*|HERDR_[A-Z_]+|PDD_AGENT_SESSION)$/;

// The variable that names the agent's config folder (the run keeps its value as configDir).
// Antigravity CLI has no config-folder variable: it uses the person's home, so its runs keep no configDir.
export const homeVariable = agent => agent === 'claude' ? 'CLAUDE_CONFIG_DIR' : agent === 'gemini' ? 'GEMINI_CLI_HOME' : agent === 'agy' ? null : 'CODEX_HOME';
// The folders outside the run worktree that an Antigravity or Gemini chat reads with its file tools: pdd's runs
// folder (`<clone>/.git/pdd/runs`) and the folder that holds the run worktree (`<clone>.pdd-worktrees`). A run from
// a linked checkout has its worktree beside the primary repository, not beside that checkout.
export const agentDirs = run => run?.commonDir && run?.root ? [join(run.commonDir, 'pdd/runs'), dirname(run.root)] : [];
// A leading "~" or "~/" is the home folder: zsh leaves "~" as text in "env CODEX_HOME=~/x pdd …" (0.1.6 tester), and the
// agent then refuses the folder.
export function expandHome(dir, env = process.env) {
  if (typeof dir !== 'string' || !dir) return null;
  const home = env.HOME || homedir();
  return dir === '~' ? home : dir.startsWith('~/') ? join(home, dir.slice(2)) : dir;
}
export const isFolder = dir => { try { return statSync(dir).isDirectory(); } catch { return false; } };

// The run record owns chat.state. A legacy chat without one is starting when its launch was not confirmed, else unknown.
const CHAT_STATES = ['starting', 'running', 'ended', 'failed', 'unknown'];
const ABSENT = new Set(['agent_not_found', 'server_not_running']);
export const chatLifecycle = chat => CHAT_STATES.includes(chat?.state) ? chat.state : chat?.startUnconfirmed ? 'starting' : 'unknown';
// The latest launch or resume request time; no finite time means no grace can expire.
export const launchAnchor = chat => { const times = [chat?.startedAt, chat?.resumedAt].filter(Number.isFinite); return times.length ? Math.max(...times) : null; };
// One Herdr observation of the saved pane as lifecycle facts. Absence (Herdr's definite answer that no agent runs in the
// saved pane) is end evidence only together with proof that the agent ran: it was seen running, or, after the shared grace,
// its own native session is known (`ran` from a lookup, or a saved id that observedSession accepts). Elapsed time alone is
// never evidence; an unconfirmed launch stays starting.
export function observeLifecycle(chat, live, at, agent = chat?.agent, ran = null) {
  const state = chatLifecycle(chat);
  // Running is the live agent in the saved pane; it is exact unless it shows another session than the saved one.
  if (live.alive) return { state: 'running', exact: !validSessionId(chat.session?.id) || !live.sessionId || live.sessionId === chat.session.id,
    ...(live.sessionId ? { session: { agent, id: live.sessionId } } : {}) };
  if (!ABSENT.has(live.code)) return { state: state === 'running' ? 'unknown' : state };
  if (state === 'ended' || state === 'failed') return { state };
  if (chat.startUnconfirmed) return { state: 'starting' };
  const sessionId = state === 'running' ? (validSessionId(chat.session?.id) ? chat.session.id : null) : ran ?? observedSession(chat, agent);
  if (state !== 'running' && (!sessionEvidenceDue(chat, live, at) || !sessionId)) return { state: 'starting' };
  return { state: 'ended', evidence: { kind: 'pane-exit', at, paneId: chat.paneId, observed: live.code, ...(sessionId ? { sessionId } : {}) } };
}
// A saved session id that proves the agent ran: a Codex id is saved only after it was observed, and a resumed chat was
// resumed from its own known session. A Claude id chosen before the first launch proves nothing alone.
export const observedSession = (chat, agent = chat?.agent) => validSessionId(chat?.session?.id) && (agent === 'codex' || Number.isFinite(chat.resumedAt)) ? chat.session.id : null;
// Only an acknowledged, never-seen chat after the grace needs its own session as evidence.
export function sessionEvidenceDue(chat, live, at) {
  const state = chatLifecycle(chat), anchor = launchAnchor(chat);
  return !live.alive && ABSENT.has(live.code) && !chat.startUnconfirmed && !['ended', 'failed', 'running'].includes(state)
    && anchor !== null && at >= anchor + START_GRACE_MS;
}
// The native session of one chat or attempt: Claude by its saved id, Codex by the worktree and the window since the latest
// launch or resume request. An unreadable, ambiguous or unrelated result is never evidence and never authorizes a launch.
export async function ownSession({ run, chat, since, ports = {} }) {
  const env = ports.env ?? process.env, kind = chat.agent ?? run.agent, folder = expandHome(chat.configDir, env);
  if (kind === 'gemini' || kind === 'agy') return { kind: 'unknown' };
  const saved = kind === 'claude' && validSessionId(chat.session?.id) ? chat.session.id : null;
  let sessions;
  try {
    sessions = await (ports.findNativeSessions ?? findNativeSessions)({ agent: kind, root: run.root, startedAt: since, endedAt: (ports.now ?? Date.now)(), ...(saved ? { sessionId: saved } : {}) },
      { env, ...(folder ? (kind === 'claude' ? { claudeConfigDir: folder } : { codexHome: folder }) : {}) });
  } catch { return { kind: 'unknown' }; }
  if (!Array.isArray(sessions)) return { kind: 'unknown' };
  if (!sessions.length) return { kind: 'none' };
  if (sessions.length !== 1 || !validSessionId(sessions[0]?.id) || kind === 'claude' && sessions[0].id !== saved) return { kind: 'unknown' };
  return { kind: 'match', id: sessions[0].id };
}
export function applyLifecycle(chat, observed) {
  chat.state = observed.state;
  if (observed.session) chat.session = observed.session;
  if (observed.evidence) chat.evidence = observed.evidence;
  else if (observed.state !== 'ended') delete chat.evidence;
  if (observed.state !== 'failed') delete chat.code;
  return chat;
}

export function herdrCommand(ports = {}) {
  if (ports.herdr) return ports.herdr;
  return async args => {
    let stdout;
    try { ({ stdout } = await ordinary('herdr', ['--session', PDD_HERDR_SESSION, ...args], { encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 })); }
    catch (error) {
      let reply; try { reply = JSON.parse(error.stderr || error.stdout); } catch { /* Not a Herdr JSON error. */ }
      throw problem(reply?.error?.code ?? (error.code === 'ENOENT' ? 'herdr_not_installed' : 'herdr_failed'), reply?.error?.message);
    }
    // `pane read` prints the screen as plain text, not JSON.
    if (args[0] === 'pane' && args[1] === 'read') return String(stdout);
    if (!String(stdout).trim()) return {};
    const reply = JSON.parse(stdout);
    if (reply?.error) throw problem(reply.error.code ?? 'herdr_failed', reply.error.message);
    return reply;
  };
}

// `unset`, `loginFile` and `program` come from chatLaunch: the caller's login and the run's agents.json command.
export function chatCommand({ agent, cwd, messageFile, sessionId, resumeId, configDir, commonDir, sourceRoot, addDirs = [], unset = [], loginFile = null, program = null }) {
  if (resumeId !== undefined && !validSessionId(resumeId)) throw problem('invalid_session_id', 'The saved native session id is not a UUID, so pdd will not resume it.');
  if (typeof cwd !== 'string' || !cwd) throw problem('invalid_worktree', 'The chat has no worktree folder, so pdd will not start it.');
  if (resumeId !== undefined) resumeId = quote(resumeId);
  if (unset.some(name => !ENV_NAME.test(name))) throw problem('invalid_login_variable', 'A login variable name is not a plain name, so pdd will not start the chat.');
  // Gemini asks a hidden "trust this folder?" question in a new worktree; trust the run worktree for this session.
  const env = ['cd', quote(cwd), '&&', 'env', ...unset.flatMap(name => ['-u', name]), 'PDD_AGENT_SESSION=1', `PDD_BIN=${quote(PACKAGE_BIN)}`, ...(configDir && homeVariable(agent) ? [`${homeVariable(agent)}=${quote(configDir)}`] : []), ...(agent === 'gemini' ? ['GEMINI_CLI_TRUST_WORKSPACE=true'] : [])];
  const message = messageFile ? [`"$(cat ${quote(messageFile)})"`] : [];
  // A child sh opens the private login file, deletes it, then reads the values and becomes the agent: no login value is
  // in this line, and no value from the file can keep the file. Any failed step stops the sh before the agent starts.
  const start = [...(loginFile ? ['sh', '-c', quote(LOGIN_SCRIPT), quote(loginFile)] : []), program ? quote(program) : agent];
  // agy asks "Do you trust the contents of this project?" in a new worktree; --settings trusts it for this session only.
  if (agent === 'agy') return [...env, ...start, '--dangerously-skip-permissions', '--settings', quote(JSON.stringify({ trustedWorkspaces: [cwd] })),
    ...[...new Set(addDirs)].flatMap(dir => ['--add-dir', quote(dir)]),
    ...(resumeId ? ['--conversation', resumeId] : []), ...(messageFile ? ['--prompt-interactive', ...message] : [])].join(' ');
  const included = addDirs.length ? [...new Set(addDirs)] : commonDir && sourceRoot ? [join(commonDir, 'pdd/runs'), `${sourceRoot}.pdd-worktrees`] : [];
  if (agent === 'gemini') return [...env, ...start, '--yolo', ...included.flatMap(dir => ['--include-directories', quote(dir)]), ...(resumeId ? ['--resume', resumeId] : []), ...(messageFile ? ['--prompt-interactive', ...message] : [])].join(' ');
  if (agent === 'claude') return [...env, ...start, '--dangerously-skip-permissions', ...(resumeId ? ['--resume', resumeId] : ['--session-id', sessionId]), ...message].join(' ');
  // Codex builds each command's environment from shell_environment_policy; `set` applies after `inherit`.
  return [...env, ...start, ...(resumeId ? ['resume', resumeId] : []), '--no-daemon', '--dangerously-bypass-approvals-and-sandbox',
    '-c', quote(`projects={${tomlString(cwd)}={trust_level="trusted"}}`),
    '-c', quote(`shell_environment_policy.set.PDD_BIN=${tomlString(PACKAGE_BIN)}`), '-c', quote(`shell_environment_policy.set.PDD_AGENT_SESSION=${tomlString('1')}`), ...message].join(' ');
}

const ENV_NAME = /^[A-Za-z_][A-Za-z0-9_]*$/;
// `command -p` finds rm whatever PATH is; plain rm (the pane's PATH, before any value is set) serves a shell whose
// `command -p` does not work (ksh93). Disable shell tracing before reading values. The agent does not get descriptor 3.
const LOGIN_SCRIPT = 'set +xv && exec 3<"$0" && { command -p rm -f -- "$0" 2>/dev/null || rm -f -- "$0"; } && . /dev/fd/3 && exec "$@" 3<&-';
const LOGIN_FILE = /^login-[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\.env$/;
// Far longer than a pane needs to run a line: an older login file belongs to a launch that never ran.
export const LOGIN_FILE_MAX_AGE_MS = 5 * 60_000;
// Delete the run folder's login files that are maxAgeMs or more old (0: all of them): only `login-<uuid>.env` regular
// files directly in the folder, at most 100 per call. It never throws.
export function removeStaleLoginFiles(runDir, { maxAgeMs = LOGIN_FILE_MAX_AGE_MS } = {}) {
  let names;
  try { names = readdirSync(runDir).filter(name => LOGIN_FILE.test(name)).slice(0, 100); } catch { return; }
  for (const name of names) {
    try {
      const path = join(runDir, name), stat = lstatSync(path);
      if (stat.isFile() && (maxAgeMs <= 0 || Date.now() - stat.mtimeMs >= maxAgeMs)) rmSync(path, { force: true });
    } catch { /* already gone or not removable: skip */ }
  }
}
// The run's saved agents.json entry for this agent kind, with its env values read again from agents.json now: the run
// record keeps only the entry's name, kind, command and env names. Null for a built-in agent.
export function savedAgentEntry(run, agent, env = process.env) {
  const saved = run?.agentDefinition;
  if (!saved || saved.kind !== agent) return null;
  let found;
  try { found = loadAgentDefinitions({ cwd: run.root, env }).find(item => item.name === saved.name); }
  catch (error) { throw problem('agent_definition_unavailable', `${error.message} The run uses the agents.json entry ${JSON.stringify(saved.name)}. Fix ~/.config/pdd/agents.json, then retry.`); }
  if (!found || found.kind !== saved.kind) throw problem('agent_definition_unavailable', `This run uses the agents.json entry ${JSON.stringify(saved.name)} (${saved.kind}), but ~/.config/pdd/agents.json has no such ${saved.kind} entry now. Add it again, then retry.`);
  const reserved = reservedEnvMessage(found);
  if (reserved) throw problem('agent_definition_unavailable', reserved);
  return { command: saved.command, env: found.env };
}
// The login of one launch: the caller's own login variables for this agent kind, then the entry's env (the entry wins).
// Each listed name that gets no value is unset, and so is the config-folder variable when the run saves none, so the
// Herdr server's old environment never decides the login. Values go only in a new private file that the chat reads once.
export function chatLaunch({ run, agent, configDir, env = process.env }) {
  const entry = savedAgentEntry(run, agent, env), names = LOGIN_VARIABLES[agent] ?? [], home = homeVariable(agent), values = {};
  for (const name of names) if (typeof env[name] === 'string' && env[name] !== '') values[name] = env[name];
  for (const [name, value] of Object.entries(entry?.env ?? {})) if (name !== home && ENV_NAME.test(name)) values[name] = value;
  const unset = [...names.filter(name => !Object.hasOwn(values, name)), ...(home && !configDir ? [home] : [])];
  let loginFile = null;
  if (Object.keys(values).length) {
    loginFile = join(run.runDir, `login-${randomUUID()}.env`);
    writeFileSync(loginFile, Object.entries(values).map(([name, value]) => `export ${name}=${quote(value)}\n`).join(''), { mode: 0o600, flag: 'wx' });
  }
  return { unset, loginFile, program: entry?.command ?? null };
}
// One native launch or resume in a pane with the caller's login; a failed request deletes the login file at once.
async function launchInPane(herdr, paneId, options, { run, env }) {
  removeStaleLoginFiles(run.runDir);
  const launch = chatLaunch({ run, agent: options.agent, configDir: options.configDir, env });
  try { return await herdr(['pane', 'run', paneId, chatCommand({ ...options, ...launch })]); }
  catch (error) { if (launch.loginFile) rmSync(launch.loginFile, { force: true }); throw error; }
}

function spawnServer(env) {
  return new Promise((resolve, reject) => {
    const child = spawn('herdr', ['--session', PDD_HERDR_SESSION, 'server'], { cwd: env.HOME || homedir(), env, detached: true, stdio: 'ignore' });
    child.once('error', reject);
    child.once('spawn', () => { child.unref(); resolve(child); });
  });
}

async function ensureServer(herdr, ports) {
  if ((await herdr(['status', 'server', '--json'])).running === true) return;
  const env = Object.fromEntries(Object.entries(ports.env ?? process.env).filter(([name]) => !AGENT_MARKER.test(name)));
  const child = await (ports.spawnServer ?? spawnServer)(env);
  let exited = false;
  child?.once?.('exit', () => { exited = true; });
  // Wait for the new server only while its process lives; a server that exits is a startup failure.
  while (!exited) {
    try { if ((await herdr(['status', 'server', '--json'])).running === true) return; } catch { /* Not listening yet. */ }
    await new Promise(resolve => setTimeout(resolve, 100));
  }
  throw problem('herdr_server_exited', 'The Herdr server for session pdd stopped while it started.');
}

export async function startChat({ run, area, message }, ports = {}) {
  const herdr = herdrCommand(ports), now = ports.now ?? Date.now, env = ports.env ?? process.env;
  // A missing agents.json entry refuses before any Herdr effect.
  savedAgentEntry(run, run.agent, env);
  await ensureServer(herdr, ports);
  const messageFile = join(run.runDir, `${area}-start.md`);
  const sessionId = run.agent === 'claude' ? randomUUID() : null;
  const configDir = expandHome(run.configDir !== undefined ? run.configDir : env[homeVariable(run.agent)], env);
  let startedAt;
  const identity = layout => {
    if (startedAt === undefined) { writeFileSync(messageFile, message); startedAt = now(); }
    return { area, agent: run.agent, tabId: layout.tabId, paneId: layout.paneId, terminalId: layout.terminalId, workspaceId: layout.workspaceId, repoWorkspaceId: layout.repoWorkspaceId,
    label: `${run.repo.split('/')[1]}#${run.number} ${run.workflow} › ${area}`, startedAt, session: sessionId ? { agent: 'claude', id: sessionId } : null, configDir, messageFile, state: 'starting' };
  };
  const checkpoint = async layout => {
    if (!ports.checkpoint) return;
    const custody = layout.root ? {repoWorkspaceId: layout.repoWorkspaceId,
      ...(Object.hasOwn(layout, 'repoRoot') ? {repoRoot: layout.repoRoot} : {}),
      ...(Object.hasOwn(layout, 'repoCreateIntent') ? {repoCreateIntent: layout.repoCreateIntent} : {}),
      workspaceId: layout.workspaceId, ...layout.root} : layout;
    await ports.checkpoint(layout.tabId ? identity(layout) : null, custody);
  };
  const {layout, chat} = await withHerdrLayoutLock(async () => {
    const layout = await openHerdrRunLayout({ repository: run.repo, issueNumber: run.number, runId: run.runId,
      workflowName: run.workflow, stageId: area, sourceRoot: run.sourceRoot, cwd: run.root, commonDir: run.commonDir, run },
    { command: herdr, checkpoint, directory: ports.layoutDirectory, ...(ports.execFile?{execFile:ports.execFile}:{}) });
    const chat = identity(layout);
    // Keep exact starting-chat custody durable under the same find/create lock.
    await checkpoint(layout);
    return {layout, chat};
  }, { directory: ports.layoutDirectory });
  try { await launchInPane(herdr, layout.paneId, { commonDir: run.commonDir, sourceRoot: run.sourceRoot, agent: run.agent, cwd: run.root, addDirs: agentDirs(run), messageFile, sessionId, configDir }, { run, env }); }
  catch (error) {
    const failed = problem(error.code ?? 'herdr_failed', error.message);
    failed.chat = { ...chat, startUnconfirmed: true };
    throw failed;
  }
  return chat;
}

// A live dialog footer holds only key hints: Codex "Press enter to confirm or esc to go back", Claude
// "Enter to confirm · Esc to cancel", Gemini "(Use Enter to select)". Agent text that quotes a hint has other words on its
// line, or the agent's input line follows it. Gemini's working line "(esc to cancel, 5s)" is not a footer.
const KEY_HINT = String.raw`[^\s·,|()]+ to [a-z]+(?: [a-z]+){0,2}`, HINT_JOIN = /\s+or\s+|\s*[·,|]\s*/i;
const FOOTER = new RegExp(String.raw`^\(?(?:(?:press|use) )?${KEY_HINT}(?:(?:\s+or\s+|\s*[·,|]\s*)${KEY_HINT})*\)?$`, 'i');
const DIALOG_HINTS = new Set(['enter to confirm', 'enter to select', 'esc to go back', 'esc to cancel']);
const INPUT_LINE = /^\s*[›>❯](?:\s|$)/;
const RULE_LINE = /^[\s\u2500-\u259f\-_=]+$/, EDGES = /^[\s\u2500-\u259f]+|[\s\u2500-\u259f]+$/g;
const footerLine = line => {
  const text = line.replace(EDGES, '').replace(/\s+/g, ' ');
  if (text.toLowerCase() === 'enter select · esc back') return true;
  return FOOTER.test(text) && text.replace(/^\(|\)$/g, '').replace(/^(?:press|use) /i, '').split(HINT_JOIN).some(hint => DIALOG_HINTS.has(hint.toLowerCase()));
};
// The first line of the dialog that the screen shows, or null when no live dialog footer is in its last 3 nonblank lines.
export function screenDialog(screen) {
  const lines = String(screen).split(/\r?\n/), blank = i => !lines[i]?.trim();
  let hint = -1;
  for (let i = lines.length - 1, seen = 0; i >= 0 && seen < 3; i--) {
    if (blank(i)) continue;
    seen++;
    // The agent shows its input line, so no dialog is open above it.
    if (INPUT_LINE.test(lines[i])) break;
    if (footerLine(lines[i])) { hint = i; break; }
  }
  if (hint < 0) return null;
  let start = hint;
  for (let i = hint - 1; i >= 0 && hint - i <= 15; i--) {
    if (!blank(i) && RULE_LINE.test(lines[i]) || blank(i) && blank(i - 1)) break;
    start = i;
  }
  return lines.slice(start, hint + 1).find(line => line.trim()).replace(EDGES, '').slice(0, 160);
}
const dialogReason = line => line ? `the chat shows a dialog: ${line}` : 'the chat shows a dialog';

export async function sendToChat(chat, text, ports = {}) {
  const now = ports.now ?? Date.now, elapsedNow = ports.elapsedNow ?? (() => Number(process.hrtime.bigint() / 1_000_000n));
  const sleep = ports.sleep ?? (ms => new Promise(resolve => setTimeout(resolve, ms)));
  const starts = [chat.startedAt, chat.resumedAt].filter(Number.isFinite);
  const deadline = starts.length ? Math.max(...starts) + START_GRACE_MS : -Infinity;
  const budget = Math.min(START_GRACE_MS, Math.max(0, deadline - now())), began = elapsedNow();
  const remaining = () => Math.min(deadline - now(), budget - Math.max(0, elapsedNow() - began));
  const herdr = herdrCommand(ports);
  // One read of the screen bottom; a failed read or a reply that is not text is never proof that no dialog shows.
  const readScreen = async () => {
    try {
      const screen = await herdr(['pane', 'read', chat.paneId, '--source', 'detection']);
      return typeof screen === 'string' ? { dialog: screenDialog(screen) } : { error: 'herdr_reply_not_text' };
    } catch (error) { return { error: error.code ?? 'herdr_failed' }; }
  };
  let retry = false;
  const wait = async () => {
    const left = remaining();
    if (left <= 0) return false;
    await sleep(Math.min(250, left));
    return remaining() > 0;
  };
  while (true) {
    if (retry && remaining() <= 0) return { ok: false, code: 'chat_still_starting' };
    const live = await chatSession(chat, ports);
    if (live.status === 'blocked' && live.alive) return { ok: false, code: 'agent_blocked', reason: dialogReason((await readScreen()).dialog) };
    const ready = live.alive && (['idle', 'working', 'done'].includes(live.status) || !retry && budget <= 0);
    if (!ready) {
      if (!live.alive && live.code !== 'agent_not_found') return { ok: false, code: live.code ?? 'herdr_status_unknown' };
      if (remaining() <= 0) return { ok: false, code: retry ? 'chat_still_starting' : live.alive ? 'herdr_status_unknown' : 'agent_not_found' };
      if (!await wait()) return { ok: false, code: 'chat_still_starting' };
      retry = true; continue;
    }
    if (retry && remaining() <= 0) return { ok: false, code: 'chat_still_starting' };
    // Text and Enter that reach an open dialog answer it, so a dialog or an unread screen sends nothing.
    const screen = await readScreen();
    if (screen.error) return { ok: false, code: 'pane_unreadable', reason: `pdd could not read the chat screen (${screen.error})` };
    if (screen.dialog) return { ok: false, code: 'agent_dialog', reason: dialogReason(screen.dialog) };
    try {
      if (ports.beforeSubmit && !await ports.beforeSubmit()) return { ok: false, code: 'chat_target_changed' };
    } catch { return { ok: false, code: 'chat_target_changed' }; }
    if (retry && remaining() <= 0) return { ok: false, code: 'chat_still_starting' };
    const withinStartup = remaining() > 0;
    try { await herdr(['agent', 'prompt', chat.paneId, text]); return { ok: true }; }
    catch (error) {
      const code = error.code ?? 'herdr_failed';
      if (code === 'agent_not_found') {
        if (!await wait()) return { ok: false, code: withinStartup || retry ? 'chat_still_starting' : code };
        retry = true; continue;
      }
      return { ok: false, code, ...(code === 'agent_blocked' ? { reason: dialogReason() } : { uncertain: true }) };
    }
  }
}

export async function chatSession(chat, ports = {}) {
  try {
    const agent = (await herdrCommand(ports)(['agent', 'get', chat.paneId])).result?.agent;
    const value = agent?.agent_session?.kind === 'id' ? agent.agent_session.value : null;
    return { alive: Boolean(agent), status: agent?.agent_status ?? null, sessionId: validSessionId(value) ? value : null };
  } catch (error) {
    const missing = { alive: false, status: null, sessionId: null, code: error.code ?? 'herdr_failed', message: error.message };
    if (['agent_not_found', 'pane_not_found'].includes(error.code) && chat.workspaceId) {
      try { if (!(await workspaceInventory(herdrCommand(ports))).some(row => row.workspace_id === chat.workspaceId)) missing.workspaceClosed = true; }
      catch { /* Unavailable inventory cannot prove closure. */ }
    }
    return missing;
  }
}

async function workspaceInventory(herdr) {
  const reply = await herdr(['workspace', 'list']), rows = reply?.result?.workspaces;
  if (reply?.result?.type !== 'workspace_list' || !Array.isArray(rows)
    || rows.some(row => typeof row?.workspace_id !== 'string' || !row.workspace_id)
    || new Set(rows.map(row => row.workspace_id)).size !== rows.length) throw problem('invalid_workspace_inventory');
  return rows;
}

export async function rebuildClosedChat({ run, chat, message }, ports = {}) {
  const herdr = herdrCommand(ports), now = ports.now ?? Date.now;
  await ensureServer(herdr, ports);
  const present = async () => {
    const workspace = (await workspaceInventory(herdr)).find(row => row.workspace_id === chat.workspaceId);
    if (workspace) {
      if (!samePath(workspace.worktree?.checkout_path, run.root) || !samePath(workspace.worktree?.repo_key, run.commonDir)
        || workspace.worktree?.is_linked_worktree !== true) throw problem('chat_identity_changed', 'The saved workspace belongs to another checkout or repository. Inspect it in Herdr.');
    }
    return Boolean(workspace);
  };
  if (await present()) return false;
  return withHerdrLayoutLock(async () => {
    if (await present()) return false;
    if (typeof ports.checkpoint !== 'function') throw problem('checkpoint_required');
    if (!isFolder(run.root)) throw problem('invalid_worktree', `The saved worktree folder "${run.root}" is missing. Restore that folder before running pdd workflow open ${run.number}.`);
    const verified = await lookupIssueWorktree({cwd: run.sourceRoot, runId: run.runId, branch: run.branch}, ports);
    const a = verified.assignment;
    if (verified.state !== 'ready' || !samePath(a?.worktreePath, run.root) || !samePath(a?.commonDir, run.commonDir)
      || a?.repository?.toLowerCase() !== run.repo.toLowerCase() || a?.runId !== run.runId)
      throw problem('invalid_worktree', 'The saved worktree assignment cannot be verified. Inspect this run before reopening it.');
    const agent = chat.agent ?? run.agent, configDir = expandHome(chat.configDir, ports.env ?? process.env);
    let resumeId = validSessionId(chat.session?.id) ? chat.session.id : null;
    if (chat.startUnconfirmed) {
      const own = await ownSession({run, chat, since: launchAnchor(chat), ports});
      if (own.kind !== 'match' || resumeId && own.id !== resumeId) throw problem('chat_start_unconfirmed', 'Inspect the saved unconfirmed session before rebuilding its workspace.');
      resumeId = own.id;
    }
    const custody = layout => layout.root ? {repoWorkspaceId: layout.repoWorkspaceId,
      ...(Object.hasOwn(layout, 'repoRoot') ? {repoRoot: layout.repoRoot} : {}),
      ...(Object.hasOwn(layout, 'repoCreateIntent') ? {repoCreateIntent: layout.repoCreateIntent} : {}), workspaceId: layout.workspaceId, ...layout.root} : layout;
    const layout = await openHerdrRunLayout({repository: run.repo, issueNumber: run.number, runId: run.runId,
      workflowName: run.workflow, stageId: chat.area, sourceRoot: run.sourceRoot, cwd: run.root, commonDir: run.commonDir, run},
    {command: herdr, directory: ports.layoutDirectory, execFile: ports.execFile,
      checkpoint: async value => ports.checkpoint(null, custody(value))});
    const live = await chatSession({...chat, paneId: layout.paneId, workspaceId: layout.workspaceId}, ports);
    if (live.alive || live.code !== 'agent_not_found') throw problem('chat_identity_changed', 'The rebuilt area pane is occupied or cannot be inspected. No chat was started.');
    Object.assign(chat, {workspaceId: layout.workspaceId, repoWorkspaceId: layout.repoWorkspaceId,
      tabId: layout.tabId, paneId: layout.paneId, terminalId: layout.terminalId, state: 'starting', startUnconfirmed: true});
    delete chat.evidence; delete chat.code;
    if (resumeId) { chat.session = {agent, id: resumeId}; chat.resumedAt = now(); }
    else {
      chat.startedAt = now(); delete chat.resumedAt;
      chat.session = agent === 'claude' ? {agent, id: (ports.randomUUID ?? randomUUID)()} : null;
      chat.messageFile = join(run.runDir, `${chat.area}-start.md`);
      writeFileSync(chat.messageFile, message);
    }
    await ports.checkpoint(chat, custody(layout));
    await herdr(['pane', 'run', chat.paneId, chatCommand({commonDir: run.commonDir, sourceRoot: run.sourceRoot,
      agent, cwd: run.root, addDirs: agentDirs(run), configDir, ...(resumeId ? {resumeId} : {messageFile: chat.messageFile, sessionId: chat.session?.id})})]);
    delete chat.startUnconfirmed;
    await ports.checkpoint(chat, custody(layout));
    return true;
  }, {directory: ports.layoutDirectory});
}

function attachSession() {
  return new Promise(resolve => {
    const child = spawn('herdr', ['session', 'attach', PDD_HERDR_SESSION], { stdio: 'inherit' });
    child.once('error', () => resolve(1));
    child.once('close', code => resolve(Number.isInteger(code) ? code : 1));
  });
}

// Returns {resumed, attached}; it may change chat.tabId/paneId/terminalId/session/resumedAt, and the caller saves the run.
export async function openChat({ run, chat }, ports = {}) {
  const herdr = herdrCommand(ports), env = ports.env ?? process.env, now = ports.now ?? Date.now, configDir = expandHome(chat.configDir, env);
  const sleep = ports.sleep ?? (ms => new Promise(resolve => setTimeout(resolve, ms)));
  const elapsedNow = ports.elapsedNow ?? (() => Number(process.hrtime.bigint() / 1_000_000n));
  const agent = chat.agent ?? run.agent;
  await ensureServer(herdr, ports);
  try { await herdr(['tab', 'get', chat.tabId]); }
  catch (error) {
    if (error.code !== 'tab_not_found') throw error;
    if (chat.startUnconfirmed) {
      const observed = await chatSession(chat, ports);
      if (!observed.alive && ['agent_not_found', 'pane_not_found'].includes(observed.code)) return { restartAvailable: true };
      throw problem('chat_start_unconfirmed', 'The earlier launch was not confirmed and its saved tab is unavailable. Inspect the original Herdr tab and pane before starting another agent.');
    }
    const created = await herdr(['tab', 'create', '--workspace', chat.workspaceId, '--cwd', run.root, '--label', chat.area, '--no-focus']);
    const terminalId = created.result?.root_pane?.terminal_id;
    if (!created.result?.tab?.tab_id || !created.result?.root_pane?.pane_id || typeof terminalId !== 'string' || !terminalId) throw problem('herdr_tab_failed', 'Herdr did not make a new tab for the chat.');
    chat.tabId = created.result.tab.tab_id; chat.paneId = created.result.root_pane.pane_id; chat.terminalId = terminalId;
  }
  let live = await chatSession(chat, ports);
  const inspect = () => {
    if (!live.alive && live.code !== 'agent_not_found') throw problem(live.code ?? 'herdr_status_unknown', live.message ?? 'Herdr could not confirm this chat; no native launch or resume was sent.');
    return observeLifecycle(chat, live, now(), agent);
  };
  let observed = inspect();
  // A starting chat: wait only the rest of the shared grace for positive confirmation. Nothing is launched or resumed meanwhile.
  const anchor = launchAnchor(chat);
  if (observed.state === 'starting' && anchor !== null) {
    // The wait is the grace left at entry; the wall clock and the elapsed clock can only shorten it, never extend it.
    const deadline = anchor + START_GRACE_MS, began = elapsedNow();
    let left = Math.max(0, deadline - now());
    const budget = left;
    while (observed.state === 'starting' && left > 0) {
      const step = Math.min(1000, left);
      await sleep(step);
      left = Math.min(left - step, deadline - now(), budget - Math.max(0, elapsedNow() - began));
      live = await chatSession(chat, ports);
      observed = inspect();
    }
  }
  if (sessionEvidenceDue(chat, live, now()) && !observedSession(chat, agent)) {
    const own = await ownSession({ run, chat, since: launchAnchor(chat), ports });
    observed = observeLifecycle(chat, live, now(), agent, own.kind === 'match' ? own.id : null);
  }
  applyLifecycle(chat, observed);
  if (live.alive) delete chat.startUnconfirmed;
  if (observed.state === 'starting') throw problem('chat_start_unconfirmed', `The ${chat.area} chat is starting, not confirmed: Herdr shows no agent in its tab, and pdd sent no new launch or resume. Look at the "${chat.area}" tab in Herdr session pdd, then run pdd workflow open ${run.number} again.`);
  if (observed.state === 'failed') throw problem('chat_start_failed', `The ${chat.area} chat did not start (${chat.code ?? 'error'}). Start a fresh session with: pdd workflow open ${run.number} --new`);
  let resumed = false;
  if (observed.state === 'ended') {
    let id = validSessionId(chat.session?.id) ? chat.session.id : null;
    if (!id) {
      const found = await (ports.findNativeSessions ?? findNativeSessions)({ agent: run.agent, root: run.root, startedAt: chat.startedAt, endedAt: now() },
        { env, ...(configDir ? (run.agent === 'claude' ? { claudeConfigDir: configDir } : { codexHome: configDir }) : {}) });
      if (found.length !== 1 || !validSessionId(found[0].id)) throw problem('native_session_unknown', `The ${chat.area} chat ended and pdd cannot tell which ${run.agent} session it was. Start ${run.agent} in the tab yourself.`);
      id = found[0].id; chat.session = { agent: run.agent, id };
    }
    // A missing agents.json entry refuses before the resume request.
    savedAgentEntry(run, run.agent, env);
    // Herdr sees the agent only after it starts; the shared grace counts from this resume request.
    chat.resumedAt = now(); applyLifecycle(chat, { state: 'starting' });
    try { await launchInPane(herdr, chat.paneId, { commonDir: run.commonDir, sourceRoot: run.sourceRoot, agent: run.agent, cwd: run.root, addDirs: agentDirs(run), resumeId: id, configDir }, { run, env }); }
    catch (error) { chat.startUnconfirmed = true; throw error; }
    resumed = true;
  }
  await herdr(['tab', 'focus', chat.tabId]);
  const attach = (ports.isTTY ?? Boolean(process.stdin.isTTY && process.stdout.isTTY)) && env.HERDR_ENV !== '1';
  if (ports.beforeAttach) await ports.beforeAttach(chat);
  if (attach) await (ports.attach ?? attachSession)();
  return { resumed, attached: attach };
}

// A cleanup failure as its code, or `code: first message line` with the code once (a layout identity refusal says what changed).
const warningReason = error => {
  const code = error?.code ?? 'error', text = String(error?.message ?? '').split('\n')[0].trim(), rest = text.startsWith(`${code}: `) ? text.slice(code.length + 2) : text;
  return !rest || rest === code ? code : `${code}: ${rest}`;
};
export async function closeChats(run, ports = {}) {
  const herdr = herdrCommand(ports), warnings = [];
  const chats = run.chats ?? [];
  for (const chat of chats) {
    try { await herdr(['tab', 'close', chat.tabId]); }
    catch (error) { if (error.code !== 'tab_not_found') warnings.push(`warning: Herdr did not close tab ${chat.tabId} (${error.code ?? 'error'}).`); }
  }
  const last = chats.at(-1);
  if (last?.workspaceId) {
    try {
      const custody = run.layout;
      const layoutPorts = { command: herdr, checkpoint: async () => {if (ports.checkpoint) await ports.checkpoint(null, custody);}, directory: ports.layoutDirectory };
      await withHerdrLayoutLock(async () => {
        await closeHerdrRunLayout({ runId: run.runId, cwd: run.root, commonDir: run.commonDir, layout: custody }, layoutPorts);
        try { await closeHerdrRepoLayoutIfIdle({ repository: run.repo, commonDir: run.commonDir }, layoutPorts); }
        catch (error) { warnings.push(`warning: the empty "${run.repo.split('/')[1]}" workspace stays open in Herdr (${warningReason(error)}).`); }
      }, { directory: ports.layoutDirectory });
    } catch (error) { warnings.push(`warning: the run workspace "${run.repo.split('/')[1]}#${run.number} ${run.workflow}" stays open in Herdr (${warningReason(error)}).`); }
  }
  return { warnings };
}


export function assertRestartCaller({chat, pending}, ports = {}) {
  const env = ports.env ?? process.env;
  const session = /[\\/]sessions[\\/]([^\\/]+)[\\/][^\\/]+$/.exec(String(env.HERDR_SOCKET_PATH ?? ''))?.[1];
  if (env.PDD_AGENT_SESSION) throw problem('agent_caller', 'Use another terminal outside the agent session to replace this chat.');
  if ((env.HERDR_ENV === '1' || env.HERDR_SOCKET_PATH) && (!session || !env.HERDR_PANE_ID)) throw problem('caller_pane_unknown', 'Use another terminal with a known Herdr session and pane.');
  if (session === PDD_HERDR_SESSION && [chat.paneId,pending?.original?.paneId,pending?.replacement?.paneId].includes(env.HERDR_PANE_ID)) throw problem('own_chat', 'Use another terminal to replace this chat.');
}

// Replacement effects are authorized only by durable, awaited caller checkpoints.
export async function restartChat({ run, chat, message, pending }, ports = {}) {
  if (typeof ports.checkpoint !== 'function') throw problem('checkpoint_required', 'Replacement requires durable checkpoints.');
  const herdr = herdrCommand(ports), env = ports.env ?? process.env;
  const fs = { readFileSync, writeFileSync, mkdirSync, ...ports.fs };
  const uuid = ports.randomUUID ?? randomUUID, now = ports.now ?? Date.now;
  const invalid = () => problem('chat_identity_changed', 'The saved chat ownership cannot be confirmed. Inspect its workspace, tab and pane.');
  const uncertain = () => problem('replacement_pending', `Chat replacement is pending at ${record?.phase ?? 'unknown'}. Retry: pdd workflow open ${run.number} --new. End the run with pdd workflow cancel ${run.number}.`);
  const inventory = async (kind, workspace) => {
    const reply = await herdr([kind, 'list', ...(workspace ? ['--workspace', workspace] : [])]);
    const rows = reply?.result?.[`${kind}s`];
    if (reply?.result?.type !== `${kind}_list` || !Array.isArray(rows) || rows.some(row => !row || typeof row[`${kind}_id`] !== 'string' || !row[`${kind}_id`]) || new Set(rows.map(row => row[`${kind}_id`])).size !== rows.length) throw invalid();
    if (kind !== 'workspace' && rows.some(row => typeof row.workspace_id !== 'string' || !row.workspace_id || kind === 'pane' && ['tab_id', 'terminal_id', 'cwd'].some(key => typeof row[key] !== 'string' || !row[key]))) throw invalid();
    return rows;
  };
  assertRestartCaller({chat, pending}, ports);
  // A missing agents.json entry refuses before intent or any Herdr effect.
  savedAgentEntry(run, pending?.original?.agent ?? chat.agent ?? run.agent, env);
  let record = pending ? JSON.parse(JSON.stringify(pending)) : undefined;
  const savedConfig = original => expandHome(run.configDir !== undefined ? run.configDir : original.configDir, env);
  const validConfig = value => value === null || typeof value === 'string' && value.length > 0;
  const legacyConfig = record && !Object.hasOwn(record, 'configDir');
  if (record) {
    if (legacyConfig) {
      record.configDir = record.replacement?.configDir !== undefined ? expandHome(record.replacement.configDir, env) : savedConfig(record.original);
      if (record.replacement) record.replacement.configDir = record.configDir;
    }
    if (!validConfig(record.configDir) || record.replacement && record.replacement.configDir !== record.configDir)
      throw problem('invalid_replacement_configuration', 'The saved replacement configuration is malformed or inconsistent. Inspect it before replacing a chat.');
  }
  const requireHome = target => {
    const dir = expandHome(target.configDir, env), variable = homeVariable(target.agent ?? run.agent);
    if (dir && !isFolder(dir)) throw problem('replacement_home_missing', `This run uses ${variable} "${dir}", but that folder does not exist. Make that folder, or cancel the run (pdd workflow cancel ${run.number}) and start it again with the right ${variable}.`);
  };
  const save = async phase => { record.phase = phase; await ports.checkpoint(JSON.parse(JSON.stringify(record))); };
  try {
  return await withHerdrLayoutLock(async () => {
    let original = record?.original ?? chat;
    // Older envelopes acquire the same immutable snapshot before any native effect.
    if (legacyConfig) await save(record.phase);
    const workspace = (await inventory('workspace')).find(row => row.workspace_id === original.workspaceId);
    if (!workspace || !samePath(workspace.worktree?.checkout_path, run.root) || !samePath(workspace.worktree?.repo_key, run.commonDir) || workspace.worktree?.is_linked_worktree !== true) throw invalid();
    let tabs = await inventory('tab',original.workspaceId), panes = await inventory('pane',original.workspaceId);
    const owned = target => {
      const tab = tabs.find(row => row.tab_id === target.tabId), rows = panes.filter(row => row.tab_id === target.tabId);
      if (!tab && !rows.length) return false;
      if (!tab || tab.workspace_id !== target.workspaceId || rows.length !== 1 || rows[0].pane_id !== target.paneId || rows[0].workspace_id !== target.workspaceId || target.terminalId && rows[0].terminal_id !== target.terminalId) throw invalid();
      return true;
    };
    const observe = async target => {
      let native;
      try { native=(await herdr(['agent','get',target.paneId])).result?.agent; }
      catch(error) { if(error.code==='agent_not_found' || error.code==='pane_not_found' && !panes.some(row=>row.pane_id===target.paneId)) return null; throw error; }
      const descriptor=native?.agent_session;
      if (!native || native.pane_id!==target.paneId || native.agent!==(target.agent??run.agent) || !['unknown','working','idle','blocked','done'].includes(native.agent_status) || descriptor!=null && (descriptor.kind!=='id' || !validSessionId(descriptor.value) || descriptor.agent!==undefined && descriptor.agent!==native.agent)) throw invalid();
      if(descriptor?.value && validSessionId(target.session?.id) && descriptor.value!==target.session.id) throw invalid();
      return native;
    };
    const confirmsResume = (native,target) => !record?.recovery?.resumeRequested || validSessionId(target.session?.id) && native?.agent_session?.value===target.session.id;
    const shellProof = async target => {
      let reply;
      try { reply = await herdr(['pane','process-info','--pane',target.paneId]); } catch { return null; }
      const info=reply?.result?.process_info, rows=info?.foreground_processes;
      if(reply?.result?.type!=='pane_process_info' || info?.pane_id!==target.paneId || !Number.isSafeInteger(info.shell_pid) || info.shell_pid<=0 ||
        info.foreground_process_group_id!==info.shell_pid || !Array.isArray(rows) || rows.length!==1 || rows[0]?.pid!==info.shell_pid || !SHELLS.has(rows[0]?.name)) return null;
      return {paneId:target.paneId,shellPid:info.shell_pid,foregroundProcessGroupId:info.foreground_process_group_id,shellName:rows[0].name};
    };
    const attemptAnchor = target => {
      const times=[target.startedAt,target.resumedAt,record.recovery?.latestLaunchRequest?.at].filter(Number.isFinite);
      return times.length ? Math.max(...times) : null;
    };
    // The native session of THIS attempt, from the latest launch request; see ownSession.
    const attemptSession = target => { requireHome(target); return ownSession({run,chat:target,since:record.recovery?.latestLaunchRequest?.at??target.startedAt,ports:{...ports,env,now}}); };
    const requestIntent = () => {
      const id=uuid(),at=now();
      if(!validSessionId(id)||!Number.isFinite(at))throw problem('invalid_replacement_identity');
      record.recovery={...record.recovery,latestLaunchRequest:{id,at}};
    };
    const unexplainedAllocation = () => {
      const added=tabs.filter(row=>!record.recovery.tabIdsBefore.includes(row.tab_id));
      // Only a saved, completely verified other-area chat explains an added peer.
      // An unmatched tab alone may be this attempt's allocation after relabelling.
      return added.filter(tab=>{
        if(tab.label===record.recovery.allocationLabel) return true;
        const chats=run.chats??[];
        const peers=chats.filter(target=>typeof target.area==='string' && target.area && target.area!==record.area && target.tabId===tab.tab_id &&
          chats.filter(saved=>saved.area===target.area).at(-1)===target);
        if(peers.length!==1) return true;
        const peer=peers[0],rows=panes.filter(row=>row.tab_id===tab.tab_id);
        return peer.workspaceId!==original.workspaceId || tab.workspace_id!==peer.workspaceId || rows.length!==1 ||
          rows[0].workspace_id!==peer.workspaceId || rows[0].pane_id!==peer.paneId ||
          peer.terminalId && rows[0].terminal_id!==peer.terminalId;
      });
    };
    const historical = () => record && record.area !== run.areas[run.area]?.name;
    const reconcileHistorical = async (freshDispatchNotSent = false) => {
      if (!historical()) return;
      tabs=await inventory('tab',original.workspaceId);panes=await inventory('pane',original.workspaceId);
      const present=owned(original), native=await observe(original);
      if (present && native && ['intent','closeRequested'].includes(record.phase)) {
        if(!confirmsResume(native,original))throw uncertain();
        await save('rolledBack');throw {historicalChat:{...original,messageFile:original.originalMessageFile}};
      }
      if (native || record.recovery?.resumeRequested && ['intent','closeRequested'].includes(record.phase)) throw uncertain();
      if (!present && ['intent','closeRequested'].includes(record.phase) && !record.recovery?.closeAcknowledged) {
        if (!validSessionId(original.session?.id)) throw uncertain();
        requireHome(original);
        const sessions=await (ports.findNativeSessions??findNativeSessions)({agent:original.agent??run.agent,root:run.root,startedAt:original.startedAt??0,endedAt:now()},
          {env,...(original.agent==='claude'?{claudeConfigDir:expandHome(original.configDir,env)}:{codexHome:expandHome(original.configDir,env)})});
        if (!sessions.some(item=>item.id===original.session.id)) throw uncertain();
      }
      if(record.phase==='createRequested') {
        if(!record.recovery?.allocationLabel || !Array.isArray(record.recovery.tabIdsBefore))throw uncertain();
        const unexplained=unexplainedAllocation();
        if(unexplained.length) {
          if(unexplained.length!==1 || unexplained[0].label!==record.recovery.allocationLabel)throw uncertain();
          const rows=panes.filter(row=>row.tab_id===unexplained[0].tab_id);
          if(rows.length!==1 || rows[0].workspace_id!==original.workspaceId)throw invalid();
          const native=await observe({...original,tabId:unexplained[0].tab_id,paneId:rows[0].pane_id,session:null});
          if(native)throw uncertain();
        }
      }
      if(record.replacement) {
        const replacementPresent=owned(record.replacement);
        const live=await observe(record.replacement);
        if(live) {
          if(!confirmsResume(live,record.replacement))throw uncertain();
          if(record.phase!=='launchRequested') throw invalid();
          if(live.agent_session?.value)record.replacement.session={agent:record.replacement.agent,id:live.agent_session.value};
          delete record.replacement.startUnconfirmed;await save('launched');throw {historicalChat:record.replacement};
        }
        if(record.recovery?.resumeRequested) throw uncertain();
        if((record.phase==='prepared' || freshDispatchNotSent) && replacementPresent) {
          if(!await shellProof(record.replacement))throw uncertain();
          const closed=await herdr(['tab','close',record.replacement.tabId]);
          if(closed?.result?.type!=='ok')throw uncertain();
        }
        if(record.phase==='launchRequested' && !freshDispatchNotSent) {
          const target=record.replacement;
          const anchor=attemptAnchor(target);
          if(anchor===null || now()-anchor<START_GRACE_MS)throw uncertain();
          if((await attemptSession(target)).kind!=='match')throw uncertain();
        }
      }
      await save('ended');throw {historicalChat:original};
    };
    if(record?.recovery?.resumeRequested && !['intent','closeRequested','launchRequested'].includes(record.phase))throw uncertain();
    await reconcileHistorical();
    if (!record) {
      const configDir = savedConfig(chat);
      if (!validConfig(configDir)) throw problem('invalid_replacement_configuration');
      requireHome({ agent: run.agent, configDir });
      if(!owned(chat)) throw invalid();
      const native=await observe(chat);
      if(chat.startUnconfirmed && !native) throw problem('chat_start_unconfirmed','Inspect the same saved agent before replacing it.');
      const id=uuid(),at=now(),archive=join(run.runDir,'abandoned-chats',`${id}-start.md`);
      if(!validSessionId(id)||!Number.isSafeInteger(at)||at<0) throw problem('invalid_replacement_identity');
      const bytes=fs.readFileSync(chat.messageFile);
      fs.mkdirSync(join(run.runDir,'abandoned-chats'),{recursive:true,mode:0o700});
      fs.writeFileSync(archive,bytes,{flag:'wx',mode:0o600});
      const messageFile=join(run.runDir,`${chat.area}-restart-${id}-start.md`);
      fs.writeFileSync(messageFile,message,{flag:'wx',mode:0o600});
      record={id,area:chat.area,phase:'intent',at,configDir,original:{...chat,...(native?.agent_session?.value?{session:{agent:chat.agent??run.agent,id:native.agent_session.value}}:{}),originalMessageFile:chat.messageFile,messageFile:archive}};
      original=record.original;
      await save('intent');await reconcileHistorical(); await save('closeRequested');await reconcileHistorical();
      const closed=await herdr(['tab','close',chat.tabId]);
      if(closed?.result?.type!=='ok') throw problem('chat_close_unconfirmed','The tab close reply was not confirmed.');
      record.recovery={closeAcknowledged:true}; await save('closeRequested');
      tabs=await inventory('tab',chat.workspaceId);panes=await inventory('pane',chat.workspaceId);
      if(tabs.some(row=>row.tab_id===chat.tabId)||panes.some(row=>row.pane_id===chat.paneId||row.tab_id===chat.tabId)) throw problem('chat_close_unconfirmed','The selected tab or pane still exists.');
      await save('closed');
    } else if(['intent','closeRequested'].includes(record.phase)) {
      if(owned(original)) {
        const native=await observe(original);
        if(native && !confirmsResume(native,original))throw uncertain();
        if(!native) {
          if(record.recovery?.resumeRequested) throw uncertain();
          if(!validSessionId(original.session?.id)) throw uncertain();
          requireHome(original);
          record.recovery={...record.recovery,resumeRequested:true};
          await save(record.phase);await reconcileHistorical();
          await launchInPane(herdr,original.paneId,{commonDir:run.commonDir,sourceRoot:run.sourceRoot,agent:original.agent??run.agent,cwd:run.root,addDirs:agentDirs(run),resumeId:original.session.id,configDir:expandHome(original.configDir,env)},{run,env});
        }
        await save('rolledBack');return {...original,messageFile:original.originalMessageFile};
      }
      if(record.phase==='intent') throw uncertain();
      if(!record.recovery?.closeAcknowledged) {
        // A missing pane alone cannot establish that the old native process stopped.
        const native=await observe(original); if(native) throw uncertain();
        if(!validSessionId(original.session?.id)) throw uncertain();
        requireHome(original);
        const sessions=await (ports.findNativeSessions??findNativeSessions)({agent:original.agent??run.agent,root:run.root,startedAt:original.startedAt??0,endedAt:now()},
          {env,...(original.agent==='claude'?{claudeConfigDir:expandHome(original.configDir,env)}:{codexHome:expandHome(original.configDir,env)})});
        if(!sessions.some(item=>item.id===original.session.id)) throw uncertain();
      }
      await save('closed');
    }
    const configDir=record.configDir,agent=original.agent??run.agent;
    const allocate=async()=>{
      requireHome({ agent, configDir });
      await reconcileHistorical();
      const layout=await openHerdrRunLayout({repository:run.repo,issueNumber:run.number,runId:run.runId,workflowName:run.workflow,stageId:record.recovery.allocationLabel,sourceRoot:run.sourceRoot,cwd:run.root,commonDir:run.commonDir,run},
        {command:herdr,checkpoint:async()=>{await save(record.phase);await reconcileHistorical();},directory:ports.layoutDirectory,...(ports.execFile?{execFile:ports.execFile}:{})});
      record.replacement={...record.replacement,area:record.area,agent,tabId:layout.tabId,paneId:layout.paneId,terminalId:layout.terminalId,workspaceId:layout.workspaceId,repoWorkspaceId:layout.repoWorkspaceId,label:original.label,startedAt:record.replacement?.startedAt??now(),session:record.replacement?.session??(agent==='claude'?{agent,id:uuid()}:null),configDir,messageFile:join(run.runDir,`${record.area}-restart-${record.id}-start.md`),state:'starting'};
    };
    if(record.phase==='closed') {
      requireHome({ agent, configDir });
      record.recovery={...record.recovery,allocationLabel:record.area,tabIdsBefore:(await inventory('tab',original.workspaceId)).map(row=>row.tab_id)};
      await save('createRequested');await allocate();await save('prepared');
    } else if(record.phase==='createRequested') {
      if(!record.recovery?.allocationLabel || !Array.isArray(record.recovery.tabIdsBefore)) throw uncertain();
      const unexplained=unexplainedAllocation();
      if(!unexplained.length) {await save('createRequested');await allocate();}
      else {
        const matching=unexplained.filter(row=>row.label===record.recovery.allocationLabel);
        if(unexplained.length!==1 || matching.length!==1) throw uncertain();
        const rows=panes.filter(row=>row.tab_id===matching[0].tab_id);
        if(rows.length!==1||rows[0].workspace_id!==original.workspaceId) throw invalid();
        record.replacement={area:record.area,agent,tabId:matching[0].tab_id,paneId:rows[0].pane_id,terminalId:rows[0].terminal_id,workspaceId:original.workspaceId,repoWorkspaceId:original.repoWorkspaceId,label:original.label,startedAt:now(),session:agent==='claude'?{agent,id:uuid()}:null,configDir,messageFile:join(run.runDir,`${record.area}-restart-${record.id}-start.md`),state:'starting'};
      }
      await save('prepared');
    }
    await reconcileHistorical();
    if(record.phase==='launchRequested') {
      const containerPresent=owned(record.replacement);
      const native=await observe(record.replacement);
      if(native && !confirmsResume(native,record.replacement))throw uncertain();
      if(!native) {
        if(record.recovery?.resumeRequested) throw uncertain();
        const target=record.replacement;
        const anchor=attemptAnchor(target);
        if(anchor===null || now()-anchor<START_GRACE_MS) throw uncertain();
        // A shell in front proves only that no agent runs now, not that none ever ran. Look for this attempt's session first.
        const found=await attemptSession(target);
        if(found.kind==='unknown') throw uncertain();
        if(found.kind==='none') {
          const proof=containerPresent ? await shellProof(target) : null;
          // Without a container, or without authoritative process information, nothing proves the launch never ran.
          if(!proof) throw uncertain();
          const request=record.recovery?.latestLaunchRequest ?? {id:record.id,at:Math.max(...[target.startedAt,target.resumedAt].filter(Number.isFinite))};
          record.recovery={...record.recovery,unsentProof:{requestId:request.id,requestAt:request.at,observedAt:now(),...proof}};
          requestIntent();
          requireHome(target);
          await save('launchRequested');await reconcileHistorical();
          try {await launchInPane(herdr,target.paneId,{commonDir:run.commonDir,sourceRoot:run.sourceRoot,agent,cwd:run.root,addDirs:agentDirs(run),messageFile:target.messageFile,sessionId:target.session?.id,configDir},{run,env});}
          catch(error){error.chat={...target};throw error;}
          delete record.replacement.startUnconfirmed;await save('launched');return record.replacement;
        }
        // This attempt ran: resume its exact session in a verified owned container; never send a second first message.
        if(containerPresent && !await shellProof(target)) throw uncertain();
        record.replacement.session={agent,id:found.id};
        if(!containerPresent) {await save('launchRequested');await allocate();}
        record.recovery={...record.recovery,resumeRequested:true};
        requireHome(record.replacement);
        record.replacement.resumedAt=now();
        await save('launchRequested');await reconcileHistorical();
        try { await launchInPane(herdr,record.replacement.paneId,{commonDir:run.commonDir,sourceRoot:run.sourceRoot,agent,cwd:run.root,addDirs:agentDirs(run),resumeId:found.id,configDir},{run,env}); }
        catch(error) {error.chat={...record.replacement};throw error;}
      }
      if(native?.agent_session?.value) record.replacement.session={agent,id:native.agent_session.value};
      delete record.replacement.startUnconfirmed;await save('launched');return record.replacement;
    }
    if(record.phase!=='prepared') throw uncertain();
    tabs=await inventory('tab',original.workspaceId);panes=await inventory('pane',original.workspaceId);
    if(!owned(record.replacement)) {await save('prepared');await allocate();await save('prepared');}
    if(await observe(record.replacement)) throw invalid();
    // The checkpoint rereads cancellation. Legacy cancel may still arrive after that check.
    requireHome(record.replacement);
    record.replacement.startUnconfirmed=true;requestIntent();await save('launchRequested');await reconcileHistorical(true);
    try {await launchInPane(herdr,record.replacement.paneId,{commonDir:run.commonDir,sourceRoot:run.sourceRoot,agent,cwd:run.root,addDirs:agentDirs(run),messageFile:record.replacement.messageFile,sessionId:record.replacement.session?.id,configDir},{run,env});}
    catch(error){error.chat={...record.replacement};throw error;}
    delete record.replacement.startUnconfirmed;await save('launched');return record.replacement;
  },{directory:ports.layoutDirectory});
  } catch(error) {if(error.historicalChat)return error.historicalChat;throw error;}
}
