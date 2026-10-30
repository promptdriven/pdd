// Generated from prompts/cli/workflow-chat.prompt.md (sha256: 50247df36027215ec76c6a8f42c0d22bab79e1fe5377c8bd27407d97c7b37194).
import { execFile as execFileCallback, spawn } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { readFileSync, readlinkSync, realpathSync, statSync, writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, join, relative, isAbsolute, sep } from 'node:path';
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

// A PID alone is reusable. Keep its native birth identity and treat zombies as stopped.
async function nativeIdentity(pid) {
  if (process.platform === 'linux') {
    try {
      const stat = readFileSync(`/proc/${pid}/stat`, 'utf8');
      const fields = stat.slice(stat.lastIndexOf(')') + 2).split(' ');
      return ['Z', 'X'].includes(fields[0]) ? null : { birth: fields[19], group: Number(fields[2]) };
    } catch (error) { if (error.code === 'ENOENT' || error.code === 'ESRCH') return null; throw error; }
  }
  try {
    const { stdout } = await ordinary('ps', ['-p', String(pid), '-o', 'pgid=,lstart=,stat=']);
    const match = stdout.trim().match(/^(\d+)\s+(.+?)\s+(\S+)$/);
    if (!match) throw problem('native_identity_unknown');
    return match[3].startsWith('Z') ? null : { group: Number(match[1]), birth: match[2] };
  } catch (error) { if (error.code === 1 && !error.stdout?.trim() && !error.stderr?.trim()) return null; throw error; }
}

async function nativeProcesses() {
  const { stdout } = await ordinary('ps', ['-axo', 'pid=,ppid=,pgid=,uid=']);
  if (process.platform !== 'linux' && (!stdout.trim() || stdout.trim().split('\n').some(line => !/^\s*\d+\s+\d+\s+\d+\s+\d+\s*$/.test(line))))
    throw problem('native_processes_unknown', 'Native process inspection returned invalid data; the issue claim stays.');
  const processes = stdout.trim().split('\n').map(line => line.trim().split(/\s+/).map(Number))
    .filter(fields => fields.length === 4 && fields.every(Number.isSafeInteger))
    .filter(([, , , uid]) => typeof process.getuid !== 'function' || uid === process.getuid())
    .map(([pid, parent, group]) => ({ pid, parent, group, cwd: null }));
  if (process.platform === 'linux') {
    for (const item of processes) {
      try { item.cwd = readlinkSync(`/proc/${item.pid}/cwd`); }
      catch (error) { if (!['ENOENT', 'ESRCH', 'EACCES', 'EPERM'].includes(error.code)) throw error; }
    }
  } else if (processes.length) {
    // Select by user rather than a snapshot-sized PID argument: unrelated short-lived
    // processes must not turn lsof's valid partial output into a failed stop.
    let directories;
    try {
      if (typeof process.getuid !== 'function') throw problem('native_cwd_unknown', 'Cannot select this user for native cwd inspection.');
      const output = await ordinary('lsof', ['-a', '-u', String(process.getuid()), '-d', 'cwd', '-Fpfn']);
      if (String(output.stderr ?? '').trim()) throw problem('native_cwd_unknown');
      directories = output.stdout;
    } catch (error) {
      if (error.code !== 1 || String(error.stderr ?? '').trim())
        throw problem('native_cwd_unknown', 'Native cwd inspection failed; the issue claim stays.');
      directories = error.stdout;
    }
    const byPid = new Map(processes.map(item => [item.pid, item]));
    let item, cwdField = false;
    const malformed = () => problem('native_cwd_unknown', 'Native cwd inspection returned incomplete or invalid data; the issue claim stays.');
    if (typeof directories !== 'string') throw malformed();
    for (const line of directories.split('\n')) {
      if (!line) continue;
      if (/^p[1-9][0-9]*$/.test(line)) {
        if (item && item.cwd === null) throw malformed();
        const pid = Number(line.slice(1));
        if (!Number.isSafeInteger(pid)) throw malformed();
        item = byPid.get(pid); cwdField = false;
        // A process may start between ps and lsof; keep its cwd in the whole-worktree scan.
        if (!item) { item = { pid, parent: null, group: null, cwd: null }; byPid.set(pid, item); processes.push(item); }
        if (item.cwd !== null) throw malformed();
      } else if (line === 'fcwd' && item && !cwdField) cwdField = true;
      else if (line.startsWith('n') && cwdField && item?.cwd === null && isAbsolute(line.slice(1))) item.cwd = line.slice(1);
      else throw malformed();
    }
    if (item && item.cwd === null) throw malformed();
    // An omitted PID may have exited during inspection. Only positive native
    // absence permits omission; a live process with unreadable cwd stays unknown.
    for (const candidate of processes) if (candidate.cwd === null && await nativeIdentity(candidate.pid))
      throw problem('native_cwd_unknown', `Cannot inspect the cwd of live process ${candidate.pid}; the issue claim stays.`);
    return processes.filter(candidate => candidate.cwd !== null);
  }
  return processes;
}

// The fallback observes the OS independently of saved pane identities. The
// system dependency supplies command/file observations; it never decides quiescence.
async function inspectMachineProcesses({ root }, system = {}) {
  const platform = system.platform ?? process.platform;
  const execute = system.execFile ?? ((file, args) => ordinary(file, args, { encoding: 'utf8', maxBuffer: 16 * 1024 * 1024 }));
  const read = system.readFile ?? (path => readFileSync(path, 'utf8'));
  const link = system.readlink ?? readlinkSync, physical = system.realpath ?? realpathSync;
  const reasons = [], processes = [];
  let currentUid = null, physicalRoot = root;
  const cause = error => `${error.code ?? 'inspection_error'}: ${error.message ?? 'inspection failed'}`;
  const absent = error => ['ENOENT', 'ESRCH'].includes(error.code);
  const uidValid = uid => Number.isSafeInteger(uid) && uid >= 0;
  try {
    currentUid = (system.getuid ?? (() => process.getuid()))();
    if (!uidValid(currentUid)) throw Error('Current user UID is unavailable');
    if (!['linux', 'darwin'].includes(platform)) throw Error(`Unsupported OS ${platform}`);
    physicalRoot = physical(root); // A missing or inaccessible physical worktree cannot prove absence.
    const list = async () => {
      const reply = await execute('ps', ['-axo', 'pid=,uid=,comm=', '-ww']);
      if (String(reply.stderr ?? '').trim()) throw Error(`ps: ${reply.stderr}`);
      const stdout = reply.stdout;
      if (typeof stdout !== 'string' || !stdout.trim() || !stdout.endsWith('\n')) throw Error('Incomplete ps process inventory');
      const result = new Map();
      for (const line of stdout.trimEnd().split('\n')) {
        const match = /^\s*([1-9][0-9]*)\s+(\S+)(?:\s+(.*?))?\s*$/.exec(line);
        if (!match || !Number.isSafeInteger(+match[1]) || result.has(+match[1])) throw Error('Malformed ps PID inventory');
        const uid = /^\d+$/.test(match[2]) && uidValid(+match[2]) ? +match[2] : null;
        result.set(+match[1], { pid: +match[1], uid, command: match[3]?.trim() || null });
      }
      return result;
    };
    const identity = async pid => {
      try {
        if (platform === 'linux') {
          const stat = read(`/proc/${pid}/stat`), match = /^(\d+) \(.*\) ([\s\S]*)$/.exec(stat.trim());
          const fields = match?.[2].split(/\s+/);
          if (+match?.[1] !== pid || fields?.length < 20 || !/^[RSDZTtXxKWPI]$/.test(fields[0]) || !/^\d+$/.test(fields[19])) throw Error('Malformed /proc process identity');
          if (['Z', 'X', 'x'].includes(fields[0])) return null;
          const uid = /^Uid:\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s*$/m.exec(read(`/proc/${pid}/status`));
          if (!uid || !uidValid(+uid[1])) throw Error('Unreadable process UID');
          return { birth: fields[19], uid: +uid[1] };
        }
        const { stdout, stderr } = await execute('ps', ['-p', String(pid), '-o', 'uid=,lstart=,stat=']);
        if (String(stderr ?? '').trim()) throw Error(`ps identity: ${stderr}`);
        const match = /^\s*(\d+)\s+(\w{3}\s+\w{3}\s+\d{1,2}\s+\d{2}:\d{2}:\d{2}\s+\d{4})\s+(\S+)\s*$/.exec(stdout);
        if (!match || !uidValid(+match[1]) || !/^[IRUSTZX]/.test(match[3])) throw Error('Malformed native process birth/UID/state');
        return /^[ZX]/.test(match[3]) ? null : { uid: +match[1], birth: match[2].replace(/\s+/g, ' ') };
      } catch (error) {
        if (platform === 'linux' && absent(error) || platform === 'darwin' && error.code === 1 && !String(error.stdout ?? '').trim() && !String(error.stderr ?? '').trim()) return null;
        throw error;
      }
    };
    const first = await list(), pending = new Map();
    const callerPid = (system.getpid ?? (() => process.pid))();
    if (!Number.isSafeInteger(callerPid) || first.get(callerPid)?.uid !== currentUid) reasons.push('Native process inventory hides the calling process or its UID');
    for (const row of first.values()) {
      // Do not access foreign-user metadata, even if that metadata is unreadable.
      if (uidValid(row.uid) && row.uid !== currentUid) continue;
      const item = { ...row, birth: null, cwd: null }; processes.push(item);
      if (!uidValid(row.uid)) { reasons.push(`PID ${row.pid} ${row.command ?? ''}: ps process UID unavailable`); continue; }
      try {
        const before = await identity(row.pid);
        if (!before) { processes.pop(); continue; }
        if (!row.command) reasons.push(`PID ${row.pid}: ps process command unavailable`);
        if (before.uid !== row.uid) throw Error('Process UID changed during inspection');
        item.birth = before.birth; pending.set(row.pid, { item, before });
      } catch (error) { reasons.push(`PID ${row.pid} ${row.command}: ${cause(error)}`); }
    }
    let directories = new Map();
    if (platform === 'darwin' && pending.size) {
      try {
        let stdout;
        try {
          const reply = await execute('lsof', ['-a', '-u', String(currentUid), '-d', 'cwd', '-Fpfn']);
          if (String(reply.stderr ?? '').trim()) throw Error(`lsof: ${reply.stderr}`);
          stdout = reply.stdout;
        } catch (error) {
          if (error.code !== 1 || String(error.stderr ?? '').trim()) throw error;
          stdout = error.stdout;
        }
        if (typeof stdout !== 'string' || stdout && !stdout.endsWith('\n')) throw Error('Incomplete lsof cwd output');
        let pid = null, field = false, foreign = false;
        for (const line of stdout.split('\n').filter(Boolean)) {
          if (/^p[1-9][0-9]*$/.test(line)) {
            if (pid !== null && !foreign && !directories.has(pid)) throw Error('Incomplete lsof cwd record');
            pid = +line.slice(1); field = false;
            if (!Number.isSafeInteger(pid) || directories.has(pid)) throw Error('Duplicate or invalid lsof PID');
            if (!first.has(pid)) throw Error(`New PID ${pid} appeared in lsof inventory`);
            foreign = uidValid(first.get(pid).uid) && first.get(pid).uid !== currentUid;
          } else if (foreign) continue;
          else if (line === 'fcwd' && pid !== null && !field) field = true;
          else if (line.startsWith('n') && field && !directories.has(pid) && isAbsolute(line.slice(1))) directories.set(pid, line.slice(1));
          else throw Error('Malformed lsof cwd output');
        }
        if (pid !== null && !foreign && !directories.has(pid)) throw Error('Incomplete lsof cwd record');
      } catch (error) { reasons.push(cause(error)); }
    }
    for (const { item, before } of pending.values()) {
      let cwdError;
      try {
        const cwd = platform === 'linux' ? link(`/proc/${item.pid}/cwd`) : directories.get(item.pid);
        if (typeof cwd !== 'string' || !isAbsolute(cwd)) throw Error('Live process cwd unavailable');
        item.cwd = physical(cwd);
      } catch (error) { cwdError = error; }
      try {
        const after = await identity(item.pid);
        if (!after) { processes.splice(processes.indexOf(item), 1); continue; }
        if (after.birth !== before.birth || after.uid !== before.uid) { item.birth = null; throw Error('Process birth/UID changed (PID reuse or unstable identity)'); }
        if (cwdError) throw cwdError;
      } catch (error) { reasons.push(`PID ${item.pid} ${item.command}: ${cause(error)}`); }
    }
    const last = await list();
    if (last.get(callerPid)?.uid !== currentUid) reasons.push('Native process inventory lost the calling process or its UID');
    for (const row of last.values()) {
      const earlier = first.get(row.pid), item = processes.find(item => item.pid === row.pid);
      if (!uidValid(row.uid)) {
        reasons.push(`PID ${row.pid} ${row.command ?? ''}: final process UID unavailable`);
        if (!item) processes.push({ ...row, birth: null, cwd: null });
        continue;
      }
      if (row.uid !== currentUid) {
        if (earlier?.uid === currentUid) reasons.push(`PID ${row.pid}: process UID changed during inspection`);
        continue; // Positively foreign: no further metadata inspection.
      }
      const finalIdentity = await identity(row.pid);
      if (!finalIdentity) { if (item) processes.splice(processes.indexOf(item), 1); continue; }
      if (!earlier || earlier.uid !== row.uid || earlier.command !== row.command || !item
        || finalIdentity.uid !== currentUid || finalIdentity.birth !== item.birth) {
        reasons.push(`PID ${row.pid} ${row.command ?? ''}: process inventory, UID or birth changed during inspection`);
        if (!item) processes.push({ ...row, birth: null, cwd: null });
      }
    }
    if ((system.getuid ?? (() => process.getuid()))() !== currentUid) reasons.push('Current user UID changed during inspection');
  } catch (error) { reasons.push(cause(error)); }
  return { root: physicalRoot, observation: { currentUid, complete: reasons.length === 0, processes, reason: reasons.join('; ') } };
}

function requireMachineQuiescence(run, observed) {
  const validUid = uid => Number.isSafeInteger(uid) && uid >= 0;
  const reasons = [], blockers = [], unknown = [];
  if (!validUid(observed?.currentUid)) reasons.push('Current user UID is unknown');
  if (observed?.complete !== true || observed?.reason) reasons.push(observed?.reason || 'Incomplete native process inventory');
  if (!Array.isArray(observed?.processes)) reasons.push('Malformed native process inventory');
  const root = run.root;
  const seen = new Set();
  for (const item of Array.isArray(observed?.processes) ? observed.processes : []) {
    if (validUid(observed.currentUid) && validUid(item?.uid) && item.uid !== observed.currentUid) continue;
    const pid = item?.pid, command = typeof item?.command === 'string' && item.command.trim() ? item.command : null;
    const label = `PID ${Number.isSafeInteger(pid) ? pid : 'unknown'}${command ? ` (${command})` : ''}`;
    if (!Number.isSafeInteger(pid) || pid <= 0 || seen.has(pid)) reasons.push(`${label}: malformed or duplicate process identity`);
    seen.add(pid);
    const uidKnown = validUid(observed.currentUid) && validUid(item?.uid);
    if (!uidKnown) reasons.push(`${label}: process UID is unknown`);
    if (!command || typeof item?.birth !== 'string' || !item.birth.trim()) reasons.push(`${label}: command or birth identity unavailable`);
    if (typeof item?.cwd !== 'string' || !isAbsolute(item.cwd)) unknown.push(`${label}: cwd is unreadable`);
    else {
      const path = relative(root, item.cwd);
      if (uidKnown && path !== '..' && !path.startsWith(`..${sep}`) && !isAbsolute(path)) blockers.push(`${label}${pid !== process.pid && command && typeof item.birth === 'string' && item.birth.trim() && observed.complete === true && !observed.reason && observed.processes.filter(row => row?.pid === pid).length === 1 && !/^(?:.*\/)?(?:ba|z|fi|da|k)?sh(?:\s|$)|\bpdd(?:\.mjs)?(?:\s|$)/.test(command) ? `; after rechecking its command and identity, use kill -TERM ${pid} if appropriate` : ''}`);
    }
  }
  if (blockers.length || unknown.length || reasons.length) {
    const recovery = 'Stop each named blocker in its owning terminal after inspecting its current command and identity. For an idle or calling shell, cd to the source repository or exit that shell and retry from outside the worktree; do not kill the cancellation request. Restore missing inspection tools/permissions or restore Herdr and inspect the original pane, then retry. Keep the run records and issue claim.';
    throw problem('native_quiescence_unknown', [...blockers.map(label => `${label} is live inside the worktree.`), ...unknown, ...reasons, recovery].filter(Boolean).join(' '));
  }
}

const unavailableHerdr = error => ['pane_not_found', 'tab_not_found', 'server_not_running', 'server_unavailable', 'session_not_found', 'herdr_not_installed', 'herdr_failed', 'ECONNREFUSED', 'ECONNRESET', 'EPIPE', 'ETIMEDOUT'].includes(error.code);

function assertNoUnownedWriters(run, processes, infos, stopped = false) {
  const ignored = new Set(infos.map(info => info.shell_pid));
  let ancestor = process.pid;
  while (ancestor && !ignored.has(ancestor)) { ignored.add(ancestor); ancestor = processes.find(item => item.pid === ancestor)?.parent; }
  const groups = new Set(stopped ? [] : infos.map(info => info.foreground_process_group_id));
  const descendants = new Set(infos.flatMap(info => info.foreground_processes.map(item => item.pid)).filter(pid => !ignored.has(pid)));
  let previous;
  do { previous = descendants.size; for (const item of processes) if (descendants.has(item.parent)) descendants.add(item.pid); } while (descendants.size !== previous);
  for (const item of processes) {
    const path = typeof item.cwd === 'string' ? relative(run.root, item.cwd) : null;
    const inWorktree = path !== null && path !== '..' && !path.startsWith(`..${sep}`) && !isAbsolute(path);
    if (!ignored.has(item.pid) && !groups.has(item.group) && (inWorktree || descendants.has(item.pid)))
      throw problem('native_descendants_unconfirmed', `A process outside the saved stage groups may still write this worktree (pid ${item.pid}). Stop or inspect it before cancelling; the issue claim stays.`);
  }
}

function isAgentProcess(item, agent) {
  if (!['codex', 'claude'].includes(agent)) return false;
  const argv = Array.isArray(item.argv) ? item.argv : [];
  const executable = basename(typeof argv[0] === 'string' ? argv[0] : item.name ?? '');
  if (executable === agent || executable === `${agent}.exe`) return true;
  // Node launchers identify their program in the script position, never in user arguments.
  if (!/^node(?:js)?(?:\.exe)?$/.test(executable) || typeof argv[1] !== 'string') return false;
  return [agent, `${agent}.js`, `${agent}.mjs`, `${agent}.cjs`].includes(basename(argv[1]))
    || agent === 'claude' && /(?:^|\/)@anthropic-ai\/claude-code\/cli\.js$/.test(argv[1]);
}

export async function stopChats(run, ports = {}) {
  const herdr = herdrCommand(ports), identity = ports.nativeIdentity ?? nativeIdentity;
  const stopGroup = ports.stopProcessGroup ?? (group => process.kill(-group, 'SIGKILL'));
  const seen = new Set();
  const finishStopped = async () => {
    try { return { stopped: true, warnings: (await (ports.closeChats ?? closeChats)(run, ports)).warnings ?? [] }; }
    catch (error) { return { stopped: true, warnings: [`warning: The run tabs could not be closed (${error.code ?? 'error'}: ${error.message}).`] }; }
  };
  try {
    const fallback = async unavailable => {
      let observed, proofRun = run;
      try {
        if (ports.inspectMachineProcesses) observed = await ports.inspectMachineProcesses({ root: run.root });
        else {
          const native = await inspectMachineProcesses({ root: run.root }, ports.machineSystem);
          observed = native.observation; proofRun = { ...run, root: native.root };
        }
      }
      catch (error) { observed = { currentUid: null, complete: false, processes: [], reason: `${error.code ?? 'inspection_error'}: ${error.message}` }; }
      try { requireMachineQuiescence(proofRun, observed); }
      catch (error) { if (unavailable) error.message = `Herdr ${unavailable.code} (${unavailable.message}). ${error.message}`; throw error; }
      return finishStopped();
    };
    if (!(run.chats ?? []).length && !['completed', 'cancelled'].includes(run.state) || (run.chats ?? []).some(chat => !chat.paneId)) return await fallback();
    const infos = new Map();
    try {
    for (const chat of run.chats ?? []) {
      if (!chat.paneId) throw problem('native_identity_unknown', 'A saved chat has no pane identity.');
      const info = (await herdr(['pane', 'process-info', '--pane', chat.paneId])).result?.process_info;
      if (!info || !Array.isArray(info.foreground_processes)) throw problem('native_identity_unknown', 'Native process information is unavailable.');
      infos.set(chat.paneId, info);
    }
    // The layout may retain an unused initial shell in the run workspace.
    // Recognize only positively idle shells; another foreground job stays a refusal.
    for (const workspace of new Set((run.chats ?? []).map(chat => chat.workspaceId).filter(Boolean))) {
      const panes = (await herdr(['pane', 'list', '--workspace', workspace])).result?.panes;
      if (!Array.isArray(panes)) throw problem('native_identity_unknown', 'The run workspace panes cannot be inspected.');
      for (const pane of panes) if (!infos.has(pane.pane_id)) {
        const info = (await herdr(['pane', 'process-info', '--pane', pane.pane_id])).result?.process_info;
        if (info?.foreground_process_group_id === info?.shell_pid && Array.isArray(info?.foreground_processes)
          && info.foreground_processes.every(item => item.pid === info.shell_pid)) infos.set(pane.pane_id, info);
      }
    }
    } catch (error) { if (unavailableHerdr(error)) return await fallback(error); throw error; }
    assertNoUnownedWriters(run, await (ports.nativeProcesses ?? nativeProcesses)(), [...infos.values()]);
    for (const chat of run.chats ?? []) {
      if (!chat.paneId || seen.has(chat.paneId)) continue;
      seen.add(chat.paneId);
      // Missing UI topology cannot establish that a detached writer died.
      const info = infos.get(chat.paneId);
      const group = info?.foreground_process_group_id, shellPid = info?.shell_pid;
      if (!Number.isSafeInteger(group) || group <= 1 || !Number.isSafeInteger(shellPid) || !Array.isArray(info.foreground_processes))
        throw problem('native_identity_unknown', `No positive native process information for ${chat.paneId}.`);
      const foreground = info.foreground_processes.filter(item => item.pid !== shellPid);
      if (group === shellPid && foreground.length === 0 && !chat.startUnconfirmed) continue;
      if (group === shellPid || !foreground.length) throw problem('chat_start_unconfirmed', `The launch in ${chat.paneId} remains unconfirmed.`);
      const belongs = item => {
        const path = typeof item.cwd === 'string' ? relative(run.root, item.cwd) : '..';
        return Number.isSafeInteger(item.pid) && item.pid > 1 && path !== '..' && !path.startsWith(`..${sep}`) && !isAbsolute(path);
      };
      const agent = chat.agent ?? run.agent;
      if (!foreground.every(belongs) || !foreground.some(item => isAgentProcess(item, agent)))
        throw problem('native_identity_mismatch', `The foreground process in ${chat.paneId} is not this run's ${agent} agent.`);
      const observed = await Promise.all(foreground.map(async item => ({ pid: item.pid, identity: await identity(item.pid) })));
      if (observed.some(item => !item.identity || item.identity.group !== group)) throw problem('native_identity_changed', 'The native process group changed during inspection.');
      // Recheck birth and group immediately before signalling, never a PID from an old receipt.
      for (const item of observed) {
        const current = await identity(item.pid);
        if (!current || current.birth !== item.identity.birth || current.group !== group) throw problem('native_identity_changed');
      }
      await stopGroup(group);
      for (let attempt = 0; ; attempt++) {
        const live = await Promise.all(observed.map(async item => {
          const current = await identity(item.pid);
          return current && current.birth === item.identity.birth;
        }));
        if (!live.some(Boolean)) break;
        if (attempt >= 20) throw problem('native_stop_unconfirmed', 'The native process still exists after the stop request.');
        await new Promise(resolve => setTimeout(resolve, 25));
      }
      for (let attempt = 0; ; attempt++) {
        const after = (await herdr(['pane', 'process-info', '--pane', chat.paneId])).result?.process_info;
        if (after?.foreground_process_group_id === shellPid && Array.isArray(after.foreground_processes)
          && after.foreground_processes.every(item => item.pid === shellPid)) break;
        if (attempt >= 20) throw problem('native_stop_unconfirmed', `The pane ${chat.paneId} is not confirmed at its shell.`);
        await new Promise(resolve => setTimeout(resolve, 25));
      }
    }
    assertNoUnownedWriters(run, await (ports.nativeProcesses ?? nativeProcesses)(), [...infos.values()], true);
  } catch (error) {
    return { stopped: false, warnings: [`Cannot confirm this run's agents stopped (${error.code ?? 'error'}: ${error.message}).`] };
  }
  return finishStopped();
}
