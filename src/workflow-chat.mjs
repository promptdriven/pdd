// Generated from prompts/cli/workflow-chat.prompt.md (sha256: 789b531e5e37ae9e10641c4b5adb03b7b9a4df1872b038a2e9f912b7036f6cbb).
import { execFile as execFileCallback, spawn } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { statSync, writeFileSync, readFileSync, mkdirSync } from 'node:fs';
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
  const chat = { area, agent: run.agent, tabId: layout.tabId, paneId: layout.paneId, terminalId: layout.terminalId, workspaceId: layout.workspaceId, repoWorkspaceId: layout.repoWorkspaceId,
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
  const now = ports.now ?? Date.now, elapsedNow = ports.elapsedNow ?? (() => Number(process.hrtime.bigint() / 1_000_000n));
  const sleep = ports.sleep ?? (ms => new Promise(resolve => setTimeout(resolve, ms)));
  const starts = [chat.startedAt, chat.resumedAt].filter(Number.isFinite);
  const deadline = starts.length ? Math.max(...starts) + 30_000 : -Infinity;
  const budget = Math.min(30_000, Math.max(0, deadline - now())), began = elapsedNow();
  const remaining = () => Math.min(deadline - now(), budget - Math.max(0, elapsedNow() - began));
  const herdr = herdrCommand(ports);
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
    if (live.status === 'blocked' && live.alive) return { ok: false, code: 'agent_blocked' };
    const ready = live.alive && ['idle', 'working', 'done'].includes(live.status);
    if (!ready) {
      if (!live.alive && live.code !== 'agent_not_found') return { ok: false, code: live.code ?? 'herdr_status_unknown' };
      if (remaining() <= 0) return { ok: false, code: retry ? 'chat_still_starting' : live.alive ? 'herdr_status_unknown' : 'agent_not_found' };
      if (!await wait()) return { ok: false, code: 'chat_still_starting' };
      retry = true; continue;
    }
    if (retry && remaining() <= 0) return { ok: false, code: 'chat_still_starting' };
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
      return { ok: false, code, ...(code === 'agent_blocked' ? {} : { uncertain: true }) };
    }
  }
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

// Returns {resumed, attached}; it may change chat.tabId/paneId/terminalId/session/resumedAt, and the caller saves the run.
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
    const terminalId = created.result?.root_pane?.terminal_id;
    if (!created.result?.tab?.tab_id || !created.result?.root_pane?.pane_id || typeof terminalId !== 'string' || !terminalId) throw problem('herdr_tab_failed', 'Herdr did not make a new tab for the chat.');
    chat.tabId = created.result.tab.tab_id; chat.paneId = created.result.root_pane.pane_id; chat.terminalId = terminalId;
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


// Replacement effects are authorized only by durable, awaited caller checkpoints.
export async function restartChat({ run, chat, message, pending }, ports = {}) {
  if (typeof ports.checkpoint !== 'function') throw problem('checkpoint_required', 'Replacement requires durable checkpoints.');
  const herdr = herdrCommand(ports), env = ports.env ?? process.env;
  const fs = { readFileSync, writeFileSync, mkdirSync, ...ports.fs };
  const uuid = ports.randomUUID ?? randomUUID, now = ports.now ?? Date.now;
  const invalid = () => problem('chat_identity_changed', 'The saved chat ownership cannot be confirmed. Inspect its workspace, tab and pane.');
  const uncertain = () => problem('replacement_pending', `Chat replacement is pending at ${record?.phase ?? 'unknown'}. Retry: pdd workflow open ${run.number} --new`);
  const inventory = async (kind, workspace) => {
    const reply = await herdr([kind, 'list', ...(workspace ? ['--workspace', workspace] : [])]);
    const rows = reply?.result?.[`${kind}s`];
    if (reply?.result?.type !== `${kind}_list` || !Array.isArray(rows) || rows.some(row => !row || typeof row[`${kind}_id`] !== 'string' || !row[`${kind}_id`]) || new Set(rows.map(row => row[`${kind}_id`])).size !== rows.length) throw invalid();
    if (kind !== 'workspace' && rows.some(row => typeof row.workspace_id !== 'string' || !row.workspace_id || kind === 'pane' && ['tab_id', 'terminal_id', 'cwd'].some(key => typeof row[key] !== 'string' || !row[key]))) throw invalid();
    return rows;
  };
  const session = /[\\/]sessions[\\/]([^\\/]+)[\\/][^\\/]+$/.exec(String(env.HERDR_SOCKET_PATH ?? ''))?.[1];
  if (env.PDD_AGENT_SESSION) throw problem('agent_caller', 'Use another terminal outside the agent session to replace this chat.');
  if ((env.HERDR_ENV === '1' || env.HERDR_SOCKET_PATH) && (!session || !env.HERDR_PANE_ID)) throw problem('caller_pane_unknown', 'Use another terminal with a known Herdr session and pane.');
  if (session === PDD_HERDR_SESSION && [chat.paneId,pending?.original?.paneId,pending?.replacement?.paneId].includes(env.HERDR_PANE_ID)) throw problem('own_chat', 'Use another terminal to replace this chat.');
  let record = pending ? JSON.parse(JSON.stringify(pending)) : undefined;
  const save = async phase => { record.phase = phase; await ports.checkpoint(JSON.parse(JSON.stringify(record))); };
  return withHerdrLayoutLock(async () => {
    const original = record?.original ?? chat;
    const workspace = (await inventory('workspace')).find(row => row.workspace_id === original.workspaceId);
    if (!workspace || workspace.worktree?.checkout_path !== run.root || workspace.worktree?.repo_key !== run.commonDir || workspace.worktree?.is_linked_worktree !== true) throw invalid();
    let tabs = await inventory('tab',original.workspaceId), panes = await inventory('pane',original.workspaceId);
    const owned = target => {
      const tab = tabs.find(row => row.tab_id === target.tabId), rows = panes.filter(row => row.tab_id === target.tabId);
      if (!tab && !rows.length) return false;
      if (!tab || tab.workspace_id !== target.workspaceId || rows.length !== 1 || rows[0].pane_id !== target.paneId || rows[0].workspace_id !== target.workspaceId || rows[0].cwd !== run.root || target.terminalId && rows[0].terminal_id !== target.terminalId) throw invalid();
      return true;
    };
    const observe = async target => {
      let native;
      try { native=(await herdr(['agent','get',target.paneId])).result?.agent; }
      catch(error) { if(error.code==='agent_not_found') return null; throw error; }
      const descriptor=native?.agent_session;
      if (!native || native.pane_id!==target.paneId || native.agent!==(target.agent??run.agent) || !['unknown','working','idle','blocked','done'].includes(native.agent_status) || descriptor!=null && (descriptor.kind!=='id' || !validSessionId(descriptor.value) || descriptor.agent!==undefined && descriptor.agent!==native.agent)) throw invalid();
      if(descriptor?.value && validSessionId(target.session?.id) && descriptor.value!==target.session.id) throw invalid();
      return native;
    };
    if (!record) {
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
      record={id,area:chat.area,phase:'intent',at,original:{...chat,...(native?.agent_session?.value?{session:{agent:chat.agent??run.agent,id:native.agent_session.value}}:{}),originalMessageFile:chat.messageFile,messageFile:archive}};
      await save('intent'); await save('closeRequested');
      const closed=await herdr(['tab','close',chat.tabId]);
      if(closed?.result?.type!=='ok') throw problem('chat_close_unconfirmed','The tab close reply was not confirmed.');
      record.recovery={closeAcknowledged:true}; await save('closeRequested');
      tabs=await inventory('tab',chat.workspaceId);panes=await inventory('pane',chat.workspaceId);
      if(tabs.some(row=>row.tab_id===chat.tabId)||panes.some(row=>row.pane_id===chat.paneId||row.tab_id===chat.tabId)) throw problem('chat_close_unconfirmed','The selected tab or pane still exists.');
      await save('closed');
    } else if(['intent','closeRequested'].includes(record.phase)) {
      if(owned(original)) {
        const native=await observe(original);
        if(!native) {
          if(record.recovery?.resumeRequested) throw uncertain();
          if(!validSessionId(original.session?.id)) throw uncertain();
          record.recovery={...record.recovery,resumeRequested:true};
          await save(record.phase);
          await herdr(['pane','run',original.paneId,chatCommand({agent:original.agent??run.agent,cwd:run.root,resumeId:original.session.id,configDir:expandHome(original.configDir,env)})]);
        }
        await save('rolledBack');return {...original,messageFile:original.originalMessageFile};
      }
      if(record.phase==='intent') throw uncertain();
      if(!record.recovery?.closeAcknowledged) {
        // A missing pane alone cannot establish that the old native process stopped.
        const native=await observe(original); if(native) throw uncertain();
        if(!validSessionId(original.session?.id)) throw uncertain();
        const sessions=await (ports.findNativeSessions??findNativeSessions)({agent:original.agent??run.agent,root:run.root,startedAt:original.startedAt??0,endedAt:now()},
          {env,...(original.agent==='claude'?{claudeConfigDir:expandHome(original.configDir,env)}:{codexHome:expandHome(original.configDir,env)})});
        if(!sessions.some(item=>item.id===original.session.id)) throw uncertain();
      }
      await save('closed');
    }
    const configDir=expandHome(run.configDir!==undefined?run.configDir:original.configDir,env),agent=original.agent??run.agent;
    const allocate=async()=>{
      const layout=await openHerdrRunLayout({repository:run.repo,issueNumber:run.number,runId:run.runId,workflowName:run.workflow,stageId:record.recovery.allocationLabel,sourceRoot:run.sourceRoot,cwd:run.root,commonDir:run.commonDir},
        {command:herdr,checkpoint:async()=>{},directory:ports.layoutDirectory,...(ports.execFile?{execFile:ports.execFile}:{})});
      record.replacement={...record.replacement,area:record.area,agent,tabId:layout.tabId,paneId:layout.paneId,terminalId:layout.terminalId,workspaceId:layout.workspaceId,repoWorkspaceId:layout.repoWorkspaceId,label:original.label,startedAt:record.replacement?.startedAt??now(),session:record.replacement?.session??(agent==='claude'?{agent,id:uuid()}:null),configDir,messageFile:join(run.runDir,`${record.area}-restart-${record.id}-start.md`)};
    };
    if(record.phase==='closed') {
      record.recovery={...record.recovery,allocationLabel:`${record.area}-${record.id}`,tabIdsBefore:(await inventory('tab',original.workspaceId)).map(row=>row.tab_id)};
      await save('createRequested');await allocate();await save('prepared');
    } else if(record.phase==='createRequested') {
      if(!record.recovery?.allocationLabel || !Array.isArray(record.recovery.tabIdsBefore)) throw uncertain();
      const added=tabs.filter(row=>!record.recovery.tabIdsBefore.includes(row.tab_id));
      if(!added.length) {await save('createRequested');await allocate();}
      else {
        if(added.length!==1||added[0].label!==record.recovery.allocationLabel) throw uncertain();
        const rows=panes.filter(row=>row.tab_id===added[0].tab_id);
        if(rows.length!==1||rows[0].cwd!==run.root||rows[0].workspace_id!==original.workspaceId) throw invalid();
        record.replacement={area:record.area,agent,tabId:added[0].tab_id,paneId:rows[0].pane_id,terminalId:rows[0].terminal_id,workspaceId:original.workspaceId,repoWorkspaceId:original.repoWorkspaceId,label:original.label,startedAt:now(),session:agent==='claude'?{agent,id:uuid()}:null,configDir,messageFile:join(run.runDir,`${record.area}-restart-${record.id}-start.md`)};
      }
      await save('prepared');
    }
    if(record.phase==='launchRequested') {
      const containerPresent=owned(record.replacement);
      const native=await observe(record.replacement);
      if(!native) {
        if(record.recovery?.resumeRequested) throw uncertain();
        const target=record.replacement;
        if(!validSessionId(target.session?.id)) throw uncertain();
        const sessions=await (ports.findNativeSessions??findNativeSessions)({agent,root:run.root,startedAt:target.startedAt,endedAt:now()},
          {env,...(agent==='claude'?{claudeConfigDir:configDir}:{codexHome:configDir})});
        if(!sessions.some(item=>item.id===target.session.id)) throw uncertain();
        if(!containerPresent) {await save('launchRequested');await allocate();}
        record.recovery={...record.recovery,resumeRequested:true};
        await save('launchRequested');
        try { await herdr(['pane','run',record.replacement.paneId,chatCommand({agent,cwd:run.root,resumeId:target.session.id,configDir})]); }
        catch(error) {error.chat={...record.replacement};throw error;}
      }
      if(native?.agent_session?.value) record.replacement.session={agent,id:native.agent_session.value};
      delete record.replacement.startUnconfirmed;await save('launched');return record.replacement;
    }
    if(record.phase!=='prepared') throw uncertain();
    tabs=await inventory('tab',original.workspaceId);panes=await inventory('pane',original.workspaceId);
    if(!owned(record.replacement)) {await save('prepared');await allocate();await save('prepared');}
    if(await observe(record.replacement)) throw invalid();
    record.replacement.startUnconfirmed=true;await save('launchRequested');
    try {await herdr(['pane','run',record.replacement.paneId,chatCommand({agent,cwd:run.root,messageFile:record.replacement.messageFile,sessionId:record.replacement.session?.id,configDir})]);}
    catch(error){error.chat={...record.replacement};throw error;}
    delete record.replacement.startUnconfirmed;await save('launched');return record.replacement;
  },{directory:ports.layoutDirectory});
}
