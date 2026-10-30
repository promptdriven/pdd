// Generated from prompts/cli/workflow-chat.prompt.md (sha256: 166d5f42b6c95f41f350f0156d4bf9de15d7863cc1f7700124fb99ccf73849e6).
import { execFile as execFileCallback, spawn } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { statSync, writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { PDD_HERDR_SESSION, withHerdrLayoutLock, openHerdrRunLayout, closeHerdrRunLayout, closeHerdrRepoLayoutIfIdle } from './workflow-herdr-layout.mjs';
import { findNativeSessions } from './approval-evidence.mjs';

const ordinary = promisify(execFileCallback);
const quote = value => `'${String(value).replace(/'/g, `'\\''`)}'`;
const problem = (code, message) => Object.assign(Error(message ?? code), { code });
// Native session ids (Claude --session-id, Codex rollouts) are UUIDs; anything else never reaches a shell line.
export const validSessionId = id => typeof id === 'string' && /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(id);
// Markers that make a native agent think it runs inside another agent session (Claude then stops saving transcripts).
const AGENT_MARKER = /^(?:CLAUDECODE|CLAUDE_CODE_(?:CHILD_SESSION|SESSION_ID|SESSION_ATTENDED|ENTRYPOINT|MESSAGING_SOCKET|MESSAGING_TOKEN|EXECPATH)|CLAUDE_PID|CODEX_THREAD_ID|CODEX_SANDBOX[A-Z_]*|HERDR_[A-Z_]+|PDD_AGENT_SESSION)$/;

// The variable that names the agent's config folder (the run keeps its value as configDir).
export const homeVariable = agent => agent === 'claude' ? 'CLAUDE_CONFIG_DIR' : 'CODEX_HOME';
// A leading "~" or "~/" is the home folder: zsh leaves "~" as text in "env CODEX_HOME=~/x pdd …" (0.1.6 tester), and the
// agent then refuses the folder.
export function expandHome(dir, env = process.env) {
  if (typeof dir !== 'string' || !dir) return null;
  const home = env.HOME || homedir();
  return dir === '~' ? home : dir.startsWith('~/') ? join(home, dir.slice(2)) : dir;
}
export const isFolder = dir => { try { return statSync(dir).isDirectory(); } catch { return false; } };

export function herdrCommand(ports = {}) {
  if (ports.herdr) return ports.herdr;
  return async args => {
    let stdout;
    try { ({ stdout } = await ordinary('herdr', ['--session', PDD_HERDR_SESSION, ...args], { encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 })); }
    catch (error) {
      let reply; try { reply = JSON.parse(error.stderr || error.stdout); } catch { /* Not a Herdr JSON error. */ }
      throw problem(reply?.error?.code ?? (error.code === 'ENOENT' ? 'herdr_not_installed' : 'herdr_failed'), reply?.error?.message);
    }
    if (!String(stdout).trim()) return {};
    const reply = JSON.parse(stdout);
    if (reply?.error) throw problem(reply.error.code ?? 'herdr_failed', reply.error.message);
    return reply;
  };
}

export function chatCommand({ agent, cwd, messageFile, sessionId, resumeId, configDir }) {
  if (resumeId !== undefined && !validSessionId(resumeId)) throw problem('invalid_session_id', 'The saved native session id is not a UUID, so pdd will not resume it.');
  if (resumeId !== undefined) resumeId = quote(resumeId);
  const env = ['env', 'PDD_AGENT_SESSION=1', ...(configDir ? [`${agent === 'claude' ? 'CLAUDE_CONFIG_DIR' : 'CODEX_HOME'}=${quote(configDir)}`] : [])];
  const message = messageFile ? [`"$(cat ${quote(messageFile)})"`] : [];
  if (agent === 'claude') return [...env, 'claude', '--dangerously-skip-permissions', ...(resumeId ? ['--resume', resumeId] : ['--session-id', sessionId]), ...message].join(' ');
  return [...env, 'codex', ...(resumeId ? ['resume', resumeId] : []), '--no-daemon', '--dangerously-bypass-approvals-and-sandbox',
    '-c', quote(`projects={${JSON.stringify(cwd)}={trust_level="trusted"}}`), ...message].join(' ');
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
  await ensureServer(herdr, ports);
  const layout = await withHerdrLayoutLock(() => openHerdrRunLayout({ repository: run.repo, issueNumber: run.number, runId: run.runId,
    workflowName: run.workflow, stageId: area, sourceRoot: run.sourceRoot, cwd: run.root, commonDir: run.commonDir,
    preAgentRefusal: !(run.chats?.length || Object.keys(run.done??{}).length || run.pr?.length) &&
      (run.chatFailure?.code==='linked_worktree_source' || run.warnings?.includes(`The ${area} chat startup was not confirmed (linked_worktree_source).`)) ? 'linked_worktree_source':undefined },
  { command: herdr, checkpoint: async () => {}, directory: ports.layoutDirectory, ...(ports.execFile?{execFile:ports.execFile}:{}) }), { directory: ports.layoutDirectory });
  const messageFile = join(run.runDir, `${area}-start.md`);
  writeFileSync(messageFile, message);
  const sessionId = run.agent === 'claude' ? randomUUID() : null;
  const configDir = expandHome(run.configDir !== undefined ? run.configDir : env[homeVariable(run.agent)], env);
  const startedAt = now();
  const chat = { area, agent: run.agent, tabId: layout.tabId, paneId: layout.paneId, workspaceId: layout.workspaceId, repoWorkspaceId: layout.repoWorkspaceId,
    label: `${run.repo.split('/')[1]}#${run.number} ${run.workflow} › ${area}`, startedAt, session: sessionId ? { agent: 'claude', id: sessionId } : null, configDir, messageFile };
  try { await herdr(['pane', 'run', layout.paneId, chatCommand({ agent: run.agent, cwd: run.root, messageFile, sessionId, configDir })]); }
  catch (error) {
    const failed = problem(error.code ?? 'herdr_failed', error.message);
    failed.chat = { ...chat, startUnconfirmed: true };
    throw failed;
  }
  return chat;
}

export async function sendToChat(chat, text, ports = {}) {
  try { await herdrCommand(ports)(['agent', 'prompt', chat.paneId, text]); return { ok: true }; }
  catch (error) { return { ok: false, code: error.code ?? 'herdr_failed' }; }
}

export async function chatSession(chat, ports = {}) {
  try {
    const agent = (await herdrCommand(ports)(['agent', 'get', chat.paneId])).result?.agent;
    const value = agent?.agent_session?.kind === 'id' ? agent.agent_session.value : null;
    return { alive: Boolean(agent), status: agent?.agent_status ?? null, sessionId: validSessionId(value) ? value : null };
  } catch (error) { return { alive: false, status: null, sessionId: null, code: error.code ?? 'herdr_failed', message: error.message }; }
}

function attachSession() {
  return new Promise(resolve => {
    const child = spawn('herdr', ['session', 'attach', PDD_HERDR_SESSION], { stdio: 'inherit' });
    child.once('error', () => resolve(1));
    child.once('close', code => resolve(Number.isInteger(code) ? code : 1));
  });
}

// Returns {resumed, attached}; it may change chat.tabId/paneId/session/resumedAt, and the caller saves the run.
export async function openChat({ run, chat }, ports = {}) {
  const herdr = herdrCommand(ports), env = ports.env ?? process.env, now = ports.now ?? Date.now, configDir = expandHome(chat.configDir, env);
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
    if (!created.result?.tab?.tab_id || !created.result?.root_pane?.pane_id) throw problem('herdr_tab_failed', 'Herdr did not make a new tab for the chat.');
    chat.tabId = created.result.tab.tab_id; chat.paneId = created.result.root_pane.pane_id;
  }
  const live = await chatSession(chat, ports);
  if (!live.alive && live.code !== 'agent_not_found') throw problem(live.code ?? 'herdr_status_unknown', live.message ?? 'Herdr could not confirm this chat; no native launch or resume was sent.');
  if (!live.alive && chat.startUnconfirmed) throw problem('chat_start_unconfirmed', 'The earlier launch was not confirmed. Inspect this same Herdr tab before starting another agent.');
  if (live.alive) delete chat.startUnconfirmed;
  if (live.sessionId) chat.session = { agent: chat.agent ?? run.agent, id: live.sessionId };
  let resumed = false;
  if (!live.alive) {
    let id = validSessionId(chat.session?.id) ? chat.session.id : null;
    if (!id) {
      const found = await (ports.findNativeSessions ?? findNativeSessions)({ agent: run.agent, root: run.root, startedAt: chat.startedAt, endedAt: now() },
        { env, ...(configDir ? (run.agent === 'claude' ? { claudeConfigDir: configDir } : { codexHome: configDir }) : {}) });
      if (found.length !== 1 || !validSessionId(found[0].id)) throw problem('native_session_unknown', `The ${chat.area} chat ended and pdd cannot tell which ${run.agent} session it was. Start ${run.agent} in the tab yourself.`);
      id = found[0].id; chat.session = { agent: run.agent, id };
    }
    try { await herdr(['pane', 'run', chat.paneId, chatCommand({ agent: run.agent, cwd: run.root, resumeId: id, configDir })]); }
    catch (error) { chat.startUnconfirmed = true; throw error; }
    // Herdr sees the agent only after it starts; status counts the start from here.
    chat.resumedAt = now(); resumed = true;
  }
  await herdr(['tab', 'focus', chat.tabId]);
  const attach = (ports.isTTY ?? Boolean(process.stdin.isTTY && process.stdout.isTTY)) && env.HERDR_ENV !== '1';
  if (attach) await (ports.attach ?? attachSession)();
  return { resumed, attached: attach };
}

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
      const layoutPorts = { command: herdr, checkpoint: async () => {}, directory: ports.layoutDirectory };
      await withHerdrLayoutLock(async () => {
        await closeHerdrRunLayout({ runId: run.runId, cwd: run.root, layout: { workspaceId: last.workspaceId, repoWorkspaceId: last.repoWorkspaceId } }, layoutPorts);
        try { await closeHerdrRepoLayoutIfIdle({ repository: run.repo, commonDir: run.commonDir }, layoutPorts); }
        catch (error) { warnings.push(`warning: the empty "${run.repo.split('/')[1]}" workspace stays open in Herdr (${error.code ?? 'error'}).`); }
      }, { directory: ports.layoutDirectory });
    } catch (error) { warnings.push(`warning: the run workspace "${run.repo.split('/')[1]}#${run.number} ${run.workflow}" stays open in Herdr (${error.code ?? 'error'}).`); }
  }
  return { warnings };
}
