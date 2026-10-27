// Generated from prompts/cli/workflow-chat.prompt.md (sha256: 48b7994b7361690ac8b053d719f6f5f8214be396c3299533c8000e1225a998d6).
import { execFile as execFileCallback, spawn } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { PDD_HERDR_SESSION, withHerdrLayoutLock, openHerdrRunLayout, closeHerdrRunLayout } from './workflow-herdr-layout.mjs';
import { findNativeSessions } from './approval-evidence.mjs';

const ordinary = promisify(execFileCallback);
const quote = value => `'${String(value).replace(/'/g, `'\\''`)}'`;
const problem = (code, message) => Object.assign(Error(message ?? code), { code });
// Markers that make a native agent think it runs inside another agent session (Claude then stops saving transcripts).
const AGENT_MARKER = /^(?:CLAUDECODE|CLAUDE_CODE_(?:CHILD_SESSION|SESSION_ID|SESSION_ATTENDED|ENTRYPOINT|MESSAGING_SOCKET|MESSAGING_TOKEN|EXECPATH)|CLAUDE_PID|CODEX_THREAD_ID|CODEX_SANDBOX[A-Z_]*|HERDR_[A-Z_]+|PDD_AGENT_SESSION)$/;

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
    workflowName: run.workflow, stageId: area, sourceRoot: run.sourceRoot, cwd: run.root, commonDir: run.commonDir },
  { command: herdr, checkpoint: async () => {}, directory: ports.layoutDirectory }), { directory: ports.layoutDirectory });
  const messageFile = join(run.runDir, `${area}-start.md`);
  writeFileSync(messageFile, message);
  const sessionId = run.agent === 'claude' ? randomUUID() : null;
  const configDir = (run.agent === 'claude' ? env.CLAUDE_CONFIG_DIR : env.CODEX_HOME) || null;
  const startedAt = now();
  await herdr(['pane', 'run', layout.paneId, chatCommand({ agent: run.agent, cwd: run.root, messageFile, sessionId, configDir })]);
  return { area, agent: run.agent, tabId: layout.tabId, paneId: layout.paneId, workspaceId: layout.workspaceId, repoWorkspaceId: layout.repoWorkspaceId,
    label: `#${run.number} ${run.workflow} › ${area}`, startedAt, session: sessionId ? { agent: 'claude', id: sessionId } : null, configDir, messageFile };
}

export async function sendToChat(chat, text, ports = {}) {
  try { await herdrCommand(ports)(['agent', 'prompt', chat.paneId, text]); return { ok: true }; }
  catch (error) { return { ok: false, code: error.code ?? 'herdr_failed' }; }
}

export async function chatSession(chat, ports = {}) {
  try {
    const agent = (await herdrCommand(ports)(['agent', 'get', chat.paneId])).result?.agent;
    const value = agent?.agent_session?.kind === 'id' ? agent.agent_session.value : null;
    return { alive: Boolean(agent), status: agent?.agent_status ?? null, sessionId: typeof value === 'string' && value ? value : null };
  } catch { return { alive: false, status: null, sessionId: null }; }
}

function attachSession() {
  return new Promise(resolve => {
    const child = spawn('herdr', ['session', 'attach', PDD_HERDR_SESSION], { stdio: 'inherit' });
    child.once('error', () => resolve(1));
    child.once('close', code => resolve(Number.isInteger(code) ? code : 1));
  });
}

// Returns {resumed, attached}; it may change chat.tabId/paneId/session, and the caller saves the run.
export async function openChat({ run, chat }, ports = {}) {
  const herdr = herdrCommand(ports), env = ports.env ?? process.env, now = ports.now ?? Date.now;
  await ensureServer(herdr, ports);
  try { await herdr(['tab', 'get', chat.tabId]); }
  catch (error) {
    if (error.code !== 'tab_not_found') throw error;
    const created = await herdr(['tab', 'create', '--workspace', chat.workspaceId, '--cwd', run.root, '--label', chat.area, '--no-focus']);
    if (!created.result?.tab?.tab_id || !created.result?.root_pane?.pane_id) throw problem('herdr_tab_failed', 'Herdr did not make a new tab for the chat.');
    chat.tabId = created.result.tab.tab_id; chat.paneId = created.result.root_pane.pane_id;
  }
  const live = await chatSession(chat, ports);
  if (live.sessionId) chat.session = { agent: chat.agent ?? run.agent, id: live.sessionId };
  let resumed = false;
  if (!live.alive) {
    let id = chat.session?.id;
    if (!id) {
      const found = await (ports.findNativeSessions ?? findNativeSessions)({ agent: run.agent, root: run.root, startedAt: chat.startedAt, endedAt: now() },
        { env, ...(chat.configDir ? (run.agent === 'claude' ? { claudeConfigDir: chat.configDir } : { codexHome: chat.configDir }) : {}) });
      if (found.length !== 1) throw problem('native_session_unknown', `The ${chat.area} chat ended and pdd cannot tell which ${run.agent} session it was. Start ${run.agent} in the tab yourself.`);
      id = found[0].id; chat.session = { agent: run.agent, id };
    }
    await herdr(['pane', 'run', chat.paneId, chatCommand({ agent: run.agent, cwd: run.root, resumeId: id, configDir: chat.configDir })]);
    resumed = true;
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
      await withHerdrLayoutLock(() => closeHerdrRunLayout({ runId: run.runId, cwd: run.root, layout: { workspaceId: last.workspaceId, repoWorkspaceId: last.repoWorkspaceId } },
        { command: herdr, checkpoint: async () => {}, directory: ports.layoutDirectory }), { directory: ports.layoutDirectory });
    } catch (error) { warnings.push(`warning: the run workspace "#${run.number} ${run.workflow}" stays open in Herdr (${error.code ?? 'error'}).`); }
  }
  return { warnings };
}
