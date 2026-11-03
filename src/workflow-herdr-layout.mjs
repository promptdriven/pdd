// Generated from prompts/cli/workflow-herdr-layout.prompt.md (sha256: f7bef4bac43ac00e9a9d95b6272efebd8955ddae3c5faa51bbd196653069d211).
import { mkdir, lstat, realpath } from 'node:fs/promises';
import { openSync, closeSync, readFileSync, writeFileSync, fsyncSync, unlinkSync, lstatSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { lookupRepositoryParent } from './workflow-worktree.mjs';

export const PDD_HERDR_SESSION = 'pdd';
const problem = code => Object.assign(new Error(code), {code});
const directoryFor = ports => ports.directory ?? join(homedir(), '.local', 'state', 'pdd', 'herdr-layout');
const id = value => typeof value === 'string' && value.length > 0;
// One filesystem identity for both operands of every path comparison: realpath when both
// resolve. A symlink alias equals its target in either direction; an unresolvable path is never equal by name.
export function samePath(a, b) {
  if (!id(a) || !id(b)) return false;
  try { return realpathSync(a) === realpathSync(b); } catch { return false; }
}
// A readable value: quotes, controls and invisible or direction characters are escaped.
const shown = value => JSON.stringify(value ?? null).replace(/[\u0080-\u009f\u00ad\u200b-\u200f\u2028-\u202e\u2060-\u206f\ufeff]/g, c => `\\u${c.charCodeAt(0).toString(16).padStart(4, '0')}`);
// The run expected one value and live Herdr shows another. Name both; repair never closes or deletes anything.
function identityChanged(workspaceId, field, expected, found) {
  // The message starts with the code, as every other layout error does (callers and tests match on it).
  return Object.assign(new Error(`herdr_layout_identity_changed: Herdr session ${PDD_HERDR_SESSION} workspace ${shown(workspaceId)} has ${field} ${shown(found)}, but the run expects ${shown(expected)}. Inspect that workspace in Herdr, restore it, then retry.`),
    { code: 'herdr_layout_identity_changed', field, expected, found });
}
async function ensureDirectory(directory) {
  await mkdir(directory, {recursive:true,mode:0o700});
  if (!(await lstat(directory)).isDirectory()) throw problem('invalid_layout_directory');
}
function claimLock(directory) {
  const claim=join(directory,'claim'),lock=join(directory,'lock');let handle;
  try {handle=openSync(claim,'wx',0o600);} catch(error) {if(error.code==='EEXIST')return false;throw error;}
  try {
    try {
      if(!lstatSync(lock).isFile())throw problem('invalid_layout_lock');
      const pid=Number(readFileSync(lock,'utf8'));
      if(!Number.isSafeInteger(pid)||pid<1)throw problem('invalid_layout_lock');
      try {process.kill(pid,0);return false;} catch(error) {if(error.code!=='ESRCH')throw error;}
      unlinkSync(lock);
    } catch(error) {if(error.code!=='ENOENT')throw error;}
    const owner=openSync(lock,'wx',0o600);
    try {writeFileSync(owner,String(process.pid));fsyncSync(owner);} finally {closeSync(owner);}
    return true;
  } finally {closeSync(handle);unlinkSync(claim);}
}
export async function withHerdrLayoutLock(action, ports = {}) {
  const directory=directoryFor(ports);await ensureDirectory(directory);
  if(!claimLock(directory))throw problem('herdr_layout_busy');
  try {return await action();} finally {unlinkSync(join(directory,'lock'));}
}
async function inventory(command) {
  const reply=await command(['workspace','list']),rows=reply.result?.workspaces;
  if(reply.id!=='cli:workspace:list'||reply.result?.type!=='workspace_list'||!Array.isArray(rows)
    ||rows.some(w=>!id(w?.workspace_id))||new Set(rows.map(w=>w.workspace_id)).size!==rows.length)throw problem('invalid_workspace_inventory');
  return rows;
}
function ownedWorkspace(rows, saved, cwd) {
  const row=rows.find(w=>w.workspace_id===saved.workspaceId);
  if(!row)throw identityChanged(saved.workspaceId,'workspace_id',saved.workspaceId,null);
  if(!row.worktree)throw identityChanged(saved.workspaceId,'worktree',{checkout_path:cwd,repo_key:saved.commonDir},null);
  if(!samePath(row.worktree.checkout_path,cwd))throw identityChanged(saved.workspaceId,'checkout_path',cwd,row.worktree.checkout_path);
  if(!samePath(row.worktree.repo_key,saved.commonDir))throw identityChanged(saved.workspaceId,'repo_key',saved.commonDir,row.worktree.repo_key);
  if(saved.runId && row.worktree.is_linked_worktree!==true)throw identityChanged(saved.workspaceId,'is_linked_worktree',true,row.worktree.is_linked_worktree);
  return row;
}
// A live workspace that is this run's linked worktree of this clone.
const runWorkspace = (row, cwd, commonDir) => samePath(row.worktree?.checkout_path, cwd) && samePath(row.worktree?.repo_key, commonDir) && row.worktree?.is_linked_worktree === true;
async function paneRows(command, workspaceId) {
  const response=await command(['pane','list','--workspace',workspaceId]),panes=response.result?.panes;
  if(response.id!=='cli:pane:list'||response.result?.type!=='pane_list'||!Array.isArray(panes)||panes.some(p=>![p?.tab_id,p?.pane_id,p?.terminal_id].every(id)||p.workspace_id!==workspaceId)||new Set(panes.map(p=>p.pane_id)).size!==panes.length)throw identityChanged(workspaceId,'pane_list',{type:'pane_list'},response.result?.type);
  return panes;
}
async function assertRunRoot(command, run, closing = false) {
  const panes=await paneRows(command,run.workspaceId);
  const expected={workspace_id:run.workspaceId,tab_id:run.rootTabId,pane_id:run.rootPaneId,terminal_id:run.rootTerminalId,cwd:run.cwd};
  const differs=(p,key)=>key==='cwd'?!samePath(p.cwd,run.cwd):p[key]!==expected[key];
  if(!panes.some(p=>Object.keys(expected).every(key=>!differs(p,key)))) {
    const near=panes.find(p=>p.pane_id===run.rootPaneId),field=near?Object.keys(expected).find(key=>differs(near,key)):'pane_id';
    throw identityChanged(run.workspaceId,field,expected[field],near?near[field]:null);
  }
  if(closing) {
    if(panes.length!==1)throw problem('herdr_layout_identity_changed');
    const tabs = await tabsFor(command, run.workspaceId);
    if (tabs.length !== 1 || tabs[0].tab_id !== run.rootTabId) throw problem('run_has_open_tabs');
  }
}
async function tabsFor(command, workspaceId) {
  const reply = await command(['tab', 'list', '--workspace', workspaceId]);
  if (reply.id !== 'cli:tab:list' || reply.result?.type !== 'tab_list' || !Array.isArray(reply.result.tabs)
    || reply.result.tabs.some(t => !id(t?.tab_id) || t.workspace_id !== workspaceId)
    || new Set(reply.result.tabs.map(t => t.tab_id)).size !== reply.result.tabs.length)
    throw identityChanged(workspaceId, 'tab_list', 'valid unique tabs', reply.result?.type);
  return reply.result.tabs;
}
const rootFields = pane => ({tabId: pane.tab_id, paneId: pane.pane_id, terminalId: pane.terminal_id});
async function runRoot(command, workspaceId, cwd, owner, opened, stageId) {
  const panes = await paneRows(command, workspaceId), tabs = await tabsFor(command, workspaceId);
  const saved = owner?.layout?.workspaceId === workspaceId ? owner.layout : null;
  const root = saved ?? (opened?.tab && opened?.root_pane ? {tabId: opened.tab.tab_id, paneId: opened.root_pane.pane_id, terminalId: opened.root_pane.terminal_id} : null);
  let pane;
  if (root) pane = panes.find(p => p.tab_id === root.tabId && p.pane_id === root.paneId && p.terminal_id === root.terminalId);
  else {
    // Without saved root custody, only one remaining shell can identify the root.
    const chatTabs = new Set((owner?.chats ?? []).map(chat => chat.tabId));
    const roots = panes.filter(p => !chatTabs.has(p.tab_id) && tabs.some(t => t.tab_id === p.tab_id && t.label !== stageId));
    if (roots.length === 1) pane = roots[0];
  }
  if (!pane || ![pane.tab_id, pane.pane_id, pane.terminal_id].every(id) || !samePath(pane.cwd, cwd))
    throw identityChanged(workspaceId, 'root_pane', root ?? {cwd}, pane ?? null);
  return rootFields(pane);
}

export async function openHerdrRunLayout(input, ports) {
  const {command, checkpoint} = ports;
  if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(input.repository ?? '') || !Number.isSafeInteger(input.issueNumber) || input.issueNumber < 1
    || ![input.runId, input.workflowName, input.stageId, input.commonDir].every(id) || typeof checkpoint !== 'function') throw problem('invalid_herdr_layout_input');
  const owner = input.run;
  if (owner !== undefined && (!owner || typeof owner !== 'object' || owner.runId !== input.runId)
    || input.repair !== undefined && (input.repair !== true || !owner)) throw problem('invalid_herdr_layout_input');
  if (owner?.layout?.phase === 'closed') throw problem('herdr_run_binding_changed');
  let rows = await inventory(command);
  const sourceRoot = await realpath(input.sourceRoot), cwd = await realpath(input.cwd);
  let commonDir;
  try {commonDir = await realpath(input.commonDir);} catch {throw problem('repository_parent_unverified');}
  if (owner && ((owner.root !== undefined && !samePath(owner.root, cwd)) || (owner.commonDir !== undefined && !samePath(owner.commonDir, commonDir))
    || (owner.repo !== undefined && owner.repo.toLowerCase() !== input.repository.toLowerCase()) || (owner.number !== undefined && owner.number !== input.issueNumber)
    || (owner.workflow !== undefined && owner.workflow !== input.workflowName))) throw problem('herdr_run_binding_changed');
  const parent = await lookupRepositoryParent({cwd: sourceRoot, repository: input.repository, commonDir}, ports);
  if (parent.state !== 'ready') throw problem('repository_parent_unverified');
  let matches = rows.filter(row => runWorkspace(row, cwd, commonDir));
  if (matches.length > 1) throw identityChanged(null, 'workspace_id', 'one run workspace', matches.map(w => w.workspace_id));
  const conflict = rows.find(row => samePath(row.worktree?.checkout_path, cwd) && !runWorkspace(row, cwd, commonDir));
  if (conflict) throw identityChanged(conflict.workspace_id, 'worktree', {checkout_path: cwd, repo_key: commonDir, is_linked_worktree: true}, conflict.worktree);
  const hint = owner?.layout?.workspaceId ?? owner?.chats?.at(-1)?.workspaceId;
  if (!matches.length && id(hint) && rows.some(w => w.workspace_id === hint))
    ownedWorkspace(rows, {workspaceId: hint, commonDir, runId: input.runId}, cwd);
  let workspace = matches[0], opened;
  let custody = {};
  const save = () => checkpoint(structuredClone(custody));
  const parents = rows.filter(w => w.worktree?.is_linked_worktree === false && samePath(w.worktree.checkout_path, parent.root) && samePath(w.worktree.repo_key, commonDir));
  let repo = parents[0];
  if (!workspace) {
    if (id(hint)) throw identityChanged(hint, 'workspace_id', hint, null);
    if (!repo) {
      const name = input.repository.split('/')[1];
      const labels = [name, input.repository, `${input.repository}@${createHash('sha256').update(commonDir).digest('hex').slice(0, 12)}`];
      const label = labels.find(label => !rows.some(w => w.label === label));
      if (!label) throw problem('repository_label_unavailable');
      await save();
      const created = await command(['workspace', 'create', '--cwd', parent.root, '--label', label, '--no-focus']);
      const repoId = created.result?.workspace?.workspace_id;
      if (created.id !== 'cli:workspace:create' || !id(repoId)) throw problem('invalid_workspace_reply');
      rows = await inventory(command);
      repo = rows.find(w => w.workspace_id === repoId);
      if (!repo || repo.worktree?.is_linked_worktree !== false || !samePath(repo.worktree.checkout_path, parent.root) || !samePath(repo.worktree.repo_key, commonDir))
        throw identityChanged(repoId, 'worktree', {checkout_path: parent.root, repo_key: commonDir}, repo?.worktree);
      custody = {repoWorkspaceId: repo.workspace_id};
      await save();
    }
    custody = {repoWorkspaceId: repo.workspace_id};
    await save();
    opened = await command(['worktree', 'open', '--workspace', repo.workspace_id, '--path', cwd, '--label', `${input.repository.split('/')[1]}#${input.issueNumber} ${input.workflowName}`, '--no-focus']);
    if (opened.id !== 'cli:worktree:open' || !id(opened.result?.workspace?.workspace_id)) throw problem('invalid_worktree_reply');
    rows = await inventory(command);
    matches = rows.filter(row => runWorkspace(row, cwd, commonDir));
    if (matches.length !== 1 || matches[0].workspace_id !== opened.result.workspace.workspace_id)
      throw identityChanged(opened.result.workspace.workspace_id, 'worktree', {checkout_path: cwd, repo_key: commonDir}, matches.map(w => w.worktree));
    workspace = matches[0];
  }
  const workspaceId = workspace.workspace_id;
  const root = await runRoot(command, workspaceId, cwd, owner, opened?.result, input.stageId);
  custody = {repoWorkspaceId: repo?.workspace_id ?? null, workspaceId, root};
  await save();
  const tabs = await tabsFor(command, workspaceId), panes = await paneRows(command, workspaceId);
  const candidates = tabs.filter(t => t.label === input.stageId).filter(t => {
    const group = panes.filter(p => p.tab_id === t.tab_id);
    if (group.length !== 1) throw identityChanged(workspaceId, 'area_panes', 1, group.length);
    return group.length === 1 && samePath(group[0].cwd, cwd);
  });
  if (candidates.length > 1) throw identityChanged(workspaceId, 'area_tab', input.stageId, candidates.map(t => t.tab_id));
  const owned = {repoWorkspaceId: repo?.workspace_id ?? null, workspaceId, root};
  if (candidates.length) {
    const pane = panes.find(p => p.tab_id === candidates[0].tab_id);
    if (![pane.pane_id, pane.terminal_id].every(id)) throw identityChanged(workspaceId, 'pane', 'complete identity', pane);
    custody = {...owned, ...rootFields(pane)};
    await save();
    return custody;
  }
  const created = await command(['tab', 'create', '--workspace', workspaceId, '--cwd', cwd, '--label', input.stageId, '--no-focus']);
  const pane = created.result?.root_pane, tabId = created.result?.tab?.tab_id;
  if (created.id !== 'cli:tab:create' || ![tabId, pane?.pane_id, pane?.terminal_id].every(id)) throw problem('invalid_tab_reply');
  const actual = (await paneRows(command, workspaceId)).filter(p => p.tab_id === tabId);
  if (actual.length !== 1 || actual[0].pane_id !== pane.pane_id || actual[0].terminal_id !== pane.terminal_id || !samePath(actual[0].cwd, cwd))
    throw identityChanged(workspaceId, 'area_pane', pane, actual);
  custody = {...owned, tabId, paneId: pane.pane_id, terminalId: pane.terminal_id};
  await save();
  return custody;
}
export async function closeHerdrRunLayout({runId, cwd, layout, commonDir}, ports) {
  if (!id(runId) || !layout || ![layout.workspaceId, layout.tabId, layout.paneId, layout.terminalId, commonDir].every(id)) throw problem('layout_cleanup_uncertain');
  if (layout.phase === 'closed') return;
  if (layout.phase === 'close_intent') throw problem('layout_cleanup_uncertain');
  const {command, checkpoint} = ports, root = layout.root ?? layout;
  const run = {runId, cwd, commonDir, workspaceId: layout.workspaceId, rootTabId: root.tabId, rootPaneId: root.paneId, rootTerminalId: root.terminalId};
  ownedWorkspace(await inventory(command), run, cwd);
  await assertRunRoot(command, run, true);
  layout.phase = 'close_intent';
  await checkpoint();
  const closed = await command(['workspace', 'close', run.workspaceId]);
  if (closed.id !== 'cli:workspace:close' || closed.result?.type !== 'ok' || (await inventory(command)).some(w => w.workspace_id === run.workspaceId)) throw problem('workspace_close_unconfirmed');
  layout.phase = 'closed';
  await checkpoint();
}

// No existing run-record field proves creation of a parent and its original roots.
// Adopting a live parent never gives this module permission to close it.
export async function closeHerdrRepoLayoutIfIdle({repository, commonDir}, ports) {
  return false;
}
