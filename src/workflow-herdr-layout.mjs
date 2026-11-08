// Generated from prompts/cli/workflow-herdr-layout.prompt.md (sha256: 9646f6f9761b11af5adbe7eadd4d73577d208d540b5a0ad36f3971703fc6a550).
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
// What changed, in plain words, for each failed identity field.
const ROOT_CHANGED = 'its first tab (the run\'s own shell tab) is gone or has other Herdr IDs';
const CHANGES = {
  worktree: 'it does not show the expected Git worktree', checkout_path: 'it shows another checkout folder',
  repo_key: 'it shows another Git clone', is_linked_worktree: 'it is not a linked Git worktree',
  workspace_create: 'a new workspace appeared, but pdd cannot prove that it is the repository workspace',
  pane_list: 'Herdr gave a pane list that pdd cannot read', tab_list: 'Herdr gave a tab list that pdd cannot read',
  root_pane: ROOT_CHANGED, tab_id: ROOT_CHANGED, pane_id: ROOT_CHANGED, terminal_id: ROOT_CHANGED,
  parent_root: 'its first shell tab is gone or has other Herdr IDs, or it has other tabs or panes',
  root_tab: 'pdd has no saved first tab for this run, and the workspace does not have exactly one shell tab',
  parent_custody: 'pdd has no complete saved first tab for this repository workspace, or that saved tab names another folder',
  root_panes: 'it has other panes besides its first shell pane', area_panes: 'an area tab does not have exactly one pane',
  area_tab: 'more than one tab has this area name', pane: 'an area tab pane has no complete Herdr IDs',
  area_pane: 'the new area tab does not show the pane that Herdr made'};
// Herdr screen fields that say nothing about identity. Pane rows also leave out the shell's folder (`cwd`):
// it is not identity, so neither the Expected nor the Found line may suggest that it caused the refusal.
const NOISE = new Set(['agent_status', 'focused', 'revision', 'scroll', 'foreground_cwd']);
const LIVE_NOISE = new Set([...NOISE, 'cwd']);
// A value as readable `name value` pairs: no JSON dump, but every string stays escaped.
function readable(value, prefix = '', noise = NOISE) {
  if (value === null || value === undefined) return prefix ? [] : ['nothing'];
  if (Array.isArray(value)) return value.length ? [value.map(item => readable(item, '', noise).join(', ')).join('; ')] : ['nothing'];
  if (typeof value !== 'object') return [prefix ? `${prefix} ${shown(value)}` : shown(value)];
  return Object.entries(value).filter(([key]) => !noise.has(key)).flatMap(([key, item]) => item !== null && typeof item === 'object' && !Array.isArray(item)
    ? readable(item, `${prefix}${key}.`, noise) : item === null || item === undefined ? [`${prefix}${key} nothing`] : [`${prefix}${key} ${readable(item, '', noise).join('')}`]);
}
const detail = (name, value, noise) => { const text = `${name}: ${readable(value, '', noise).join(', ') || 'nothing'}`; return text.length > 500 ? `${text.slice(0, 499)}…` : text; };
// The run expected one value and live Herdr shows another. The first line says what changed and what to do;
// the escaped values follow on later lines. Repair never closes or deletes anything.
// Both lines leave out the same fields; only a refusal of pdd's saved folder (`parent_custody`) passes NOISE to show it.
function identityChanged(workspaceId, field, expected, found, noise = LIVE_NOISE) {
  const what = field === 'workspace_id' ? (Array.isArray(found) || workspaceId === null ? 'more than one workspace shows this run worktree' : 'the saved workspace is gone')
    : CHANGES[field] ?? `its ${field} changed`;
  const where = id(workspaceId) ? `Herdr session ${PDD_HERDR_SESSION}, workspace ${shown(workspaceId)}` : `Herdr session ${PDD_HERDR_SESSION}`;
  // The message starts with the code, as every other layout error does (callers show it once; tests match on it).
  return Object.assign(new Error([`herdr_layout_identity_changed: ${where}: ${what}. Look at ${id(workspaceId) ? 'that workspace' : 'its workspaces'} in Herdr, undo the change, then try again.`,
    detail(`Expected ${field}`, expected, noise), detail(`Found ${field}`, found, noise)].join('\n')), { code: 'herdr_layout_identity_changed', field, expected, found });
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
  // Herdr IDs only: the root shell's live folder is not identity (a shell startup file can move it).
  const expected={workspace_id:run.workspaceId,tab_id:run.rootTabId,pane_id:run.rootPaneId,terminal_id:run.rootTerminalId};
  const differs=(p,key)=>p[key]!==expected[key];
  if(!panes.some(p=>Object.keys(expected).every(key=>!differs(p,key)))) {
    const near=panes.find(p=>p.pane_id===run.rootPaneId),field=near?Object.keys(expected).find(key=>differs(near,key)):'pane_id';
    throw identityChanged(run.workspaceId,field,expected[field],near?near[field]:null);
  }
  if(closing) {
    if(panes.length!==1)throw identityChanged(run.workspaceId,'root_panes',1,panes.length);
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
function completeParentRoot(root, cwd) {
  return root && [root.tabId, root.paneId, root.terminalId].every(id) && samePath(root.cwd, cwd);
}
async function assertParentRoot(command, workspaceId, root, cwd) {
  const tabs = await tabsFor(command, workspaceId), panes = await paneRows(command, workspaceId);
  const pane = panes.find(p => p.tab_id === root?.tabId && p.pane_id === root?.paneId && p.terminal_id === root?.terminalId);
  const tab = tabs.find(t => t.tab_id === root?.tabId);
  // pdd's saved record of the first tab must name the repository root; then only the Herdr IDs are compared.
  if (!completeParentRoot(root, cwd)) throw identityChanged(workspaceId, 'parent_custody', {cwd}, root ?? null, NOISE);
  if (tabs.length !== 1 || panes.length !== 1 || !tab || !pane)
    throw identityChanged(workspaceId, 'parent_root', root, {tabCount: tabs.length, paneCount: panes.length, pane: pane ?? null});
  return {tab, pane};
}
// A create intent for this parent and clone, with the checked pre-create inventory.
function validCreateIntent(intent, parentRoot, commonDir) {
  return id(intent.label) && samePath(intent.parentRoot, parentRoot) && samePath(intent.commonDir, commonDir) && Array.isArray(intent.workspaceIdsBefore)
    && intent.workspaceIdsBefore.every(id) && new Set(intent.workspaceIdsBefore).size === intent.workspaceIdsBefore.length;
}
function parentIdentity(row, parentRoot, commonDir) {
  return row?.worktree?.is_linked_worktree === false
    && samePath(row.worktree.checkout_path, parentRoot) && samePath(row.worktree.repo_key, commonDir);
}
async function attachCreatedParent(command, workspaceId, parentRoot, commonDir, root) {
  await assertParentRoot(command, workspaceId, root, parentRoot);
  let failure;
  try { await command(['worktree', 'open', '--workspace', workspaceId, '--path', parentRoot, '--no-focus']); }
  catch (error) { failure = error; }
  const rows = await inventory(command), row = rows.find(w => w.workspace_id === workspaceId);
  if (!parentIdentity(row, parentRoot, commonDir)) {
    if (failure) throw failure;
    throw identityChanged(workspaceId, 'worktree', {checkout_path: parentRoot, repo_key: commonDir, is_linked_worktree: false}, row?.worktree ?? null);
  }
  await assertParentRoot(command, workspaceId, root, parentRoot);
  return row;
}
async function runRoot(command, workspaceId, owner, opened, stageId) {
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
  if (!pane || ![pane.tab_id, pane.pane_id, pane.terminal_id].every(id))
    throw identityChanged(workspaceId, root ? 'root_pane' : 'root_tab', root ? {tabId: root.tabId, paneId: root.paneId, terminalId: root.terminalId} : 'one shell tab',
      pane ?? panes.find(p => p.pane_id === root?.paneId) ?? null);
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
  if (id(hint) && rows.some(w => w.workspace_id === hint))
    ownedWorkspace(rows, {workspaceId: hint, commonDir, runId: input.runId}, cwd);
  let workspace = matches[0], opened;
  let custody = {};
  const save = () => checkpoint(structuredClone(custody));
  const parents = rows.filter(w => w.worktree?.is_linked_worktree === false && samePath(w.worktree.checkout_path, parent.root) && samePath(w.worktree.repo_key, commonDir));
  const parentHint = owner?.layout?.repoCreateIntent
    ? owner.layout.repoWorkspaceId : owner?.layout?.repoWorkspaceId ?? owner?.chats?.at(-1)?.repoWorkspaceId;
  const savedRepoRoot = owner?.layout?.repoRoot;
  const createIntent = owner?.layout?.repoCreateIntent;
  let repo = parents.find(w => w.workspace_id === parentHint) ?? parents[0];
  if (!workspace) {
    await ports.beforeCreate?.(repo || owner?.layout?.repoCreateIntent ? 2 : 3);
    let pendingParent;
    if (createIntent) {
      if (!validCreateIntent(createIntent, parent.root, commonDir)) throw problem('repository_parent_unverified');
      const before = new Set(createIntent.workspaceIdsBefore), appeared = rows.filter(row => !before.has(row.workspace_id));
      pendingParent = appeared.find(row => row.workspace_id === parentHint);
      if (id(parentHint) && !before.has(parentHint) && !rows.some(row => row.workspace_id === parentHint))
        throw identityChanged(parentHint, 'workspace_id', parentHint, null);
      if (!repo && appeared.length && !pendingParent)
        throw identityChanged(null, 'workspace_create', {parentRoot: parent.root}, appeared.map(row => ({workspace_id: row.workspace_id, worktree: row.worktree ?? null})));
    }
    if (pendingParent) {
      if (parents.some(w => w.workspace_id === pendingParent.workspace_id)) {
        if (parent.bare && !completeParentRoot(savedRepoRoot, parent.root))
        throw identityChanged(parentHint, 'root', 'complete saved parent root', savedRepoRoot ?? null);
      if (savedRepoRoot && [savedRepoRoot.tabId, savedRepoRoot.paneId, savedRepoRoot.terminalId, savedRepoRoot.cwd].every(id))
          await assertParentRoot(command, parentHint, savedRepoRoot, parent.root);
        repo = pendingParent;
      } else {
        if (!savedRepoRoot || !completeParentRoot(savedRepoRoot, parent.root))
          throw identityChanged(parentHint, 'parent_custody', {cwd: parent.root}, savedRepoRoot ?? null, NOISE);
        await assertParentRoot(command, parentHint, savedRepoRoot, parent.root);
        if (pendingParent.worktree)
          throw identityChanged(parentHint, 'worktree', {checkout_path: parent.root, repo_key: commonDir, is_linked_worktree: false}, pendingParent.worktree);
        custody = {repoWorkspaceId: parentHint, repoRoot: savedRepoRoot, repoCreateIntent: createIntent};
        await save();
        if (parent.bare) repo = pendingParent;
        else {
          repo = await attachCreatedParent(command, parentHint, parent.root, commonDir, savedRepoRoot);
          rows = await inventory(command);
          custody = {repoWorkspaceId: repo.workspace_id, repoRoot: savedRepoRoot, repoCreateIntent: null};
          await save();
        }
      }
    }
    if (!repo) {
      if (createIntent) {
        custody = {repoCreateIntent: null};
        await save();
      }
      const name = input.repository.split('/')[1];
      const labels = [name, input.repository, `${input.repository}@${createHash('sha256').update(commonDir).digest('hex').slice(0, 12)}`];
      const label = labels.find(label => !rows.some(w => w.label === label));
      if (!label) throw problem('repository_label_unavailable');
      const intent = {label, parentRoot: parent.root, commonDir, workspaceIdsBefore: rows.map(row => row.workspace_id)};
      custody = {repoWorkspaceId: null, repoRoot: null, repoCreateIntent: intent};
      await save();
      const created = await command(['workspace', 'create', '--cwd', parent.root, '--label', label, '--no-focus']);
      const repoId = created.result?.workspace?.workspace_id;
      if (!id(repoId)) throw problem('invalid_workspace_reply');
      const createdTab = created.result?.tab, createdPane = created.result?.root_pane;
      const repoRoot = {tabId: createdTab?.tab_id ?? null, paneId: createdPane?.pane_id ?? null,
        terminalId: createdPane?.terminal_id ?? null, cwd: createdPane?.cwd ?? null};
      custody = {repoWorkspaceId: repoId, repoRoot, repoCreateIntent: intent};
      await save();
      if (created.id !== 'cli:workspace:create' || created.result?.workspace?.workspace_id !== repoId
        || createdTab?.workspace_id !== repoId || createdPane?.workspace_id !== repoId
        || !completeParentRoot(repoRoot, parent.root)) throw problem('invalid_workspace_reply');
      rows = await inventory(command);
      repo = rows.find(w => w.workspace_id === repoId);
      if (!repo) throw identityChanged(repoId, 'workspace_id', repoId, null);
      await assertParentRoot(command, repoId, repoRoot, parent.root);
      if (repo.worktree) {
        if (!parentIdentity(repo, parent.root, commonDir))
          throw identityChanged(repoId, 'worktree', {checkout_path: parent.root, repo_key: commonDir, is_linked_worktree: false}, repo.worktree);
      } else if (!parent.bare) {
        repo = await attachCreatedParent(command, repoId, parent.root, commonDir, repoRoot);
        rows = await inventory(command);
      }
      custody = {repoWorkspaceId: repoId, repoRoot, repoCreateIntent: repo.worktree ? null : intent};
      await save();
    }
    // Herdr refuses `worktree open --path` on a bare repository folder. A bare parent gets its identity when it
    // opens the run worktree, so its create intent and saved root stay pending until then.
    const pendingBare = !repo.worktree;
    const repoRoot = (completeParentRoot(custody.repoRoot, parent.root) ? custody.repoRoot : undefined)
      ?? (owner?.layout?.repoWorkspaceId === repo.workspace_id && completeParentRoot(owner.layout.repoRoot, parent.root) ? owner.layout.repoRoot : undefined);
    if (pendingBare && (!parent.bare || !repoRoot)) throw identityChanged(repo.workspace_id, 'worktree', {checkout_path: parent.root, repo_key: commonDir, is_linked_worktree: false}, null);
    custody = {repoWorkspaceId: repo.workspace_id, ...(repoRoot ? {repoRoot} : {}),
      ...(Object.hasOwn(custody, 'repoCreateIntent') || createIntent ? {repoCreateIntent: pendingBare ? custody.repoCreateIntent ?? createIntent : null} : {})};
    await save();
    opened = await command(['worktree', 'open', '--workspace', repo.workspace_id, '--path', cwd, '--label', `${input.repository.split('/')[1]}#${input.issueNumber} ${input.workflowName}`, '--no-focus']);
    if (opened.id !== 'cli:worktree:open' || !id(opened.result?.workspace?.workspace_id)) throw problem('invalid_worktree_reply');
    rows = await inventory(command);
    matches = rows.filter(row => runWorkspace(row, cwd, commonDir));
    if (matches.length !== 1 || matches[0].workspace_id !== opened.result.workspace.workspace_id)
      throw identityChanged(opened.result.workspace.workspace_id, 'worktree', {checkout_path: cwd, repo_key: commonDir}, matches.map(w => w.worktree));
    workspace = matches[0];
    if (pendingBare) {
      const row = rows.find(w => w.workspace_id === repo.workspace_id);
      if (!parentIdentity(row, parent.root, commonDir))
        throw identityChanged(repo.workspace_id, 'worktree', {checkout_path: parent.root, repo_key: commonDir, is_linked_worktree: false}, row?.worktree ?? null);
      await assertParentRoot(command, repo.workspace_id, repoRoot, parent.root);
      repo = row; custody = {...custody, repoCreateIntent: null};
      await save();
    }
  } else if (createIntent) {
    // The run workspace exists, but the parent that opened it is still pending (a refused parent check or a lost
    // run-open reply). Check that live parent again on every open; clear the intent only when identity and root pass.
    if (!validCreateIntent(createIntent, parent.root, commonDir)) throw problem('repository_parent_unverified');
    const pending = rows.find(row => row.workspace_id === parentHint && !createIntent.workspaceIdsBefore.includes(row.workspace_id));
    if (pending) {
      if (!parentIdentity(pending, parent.root, commonDir))
        throw identityChanged(parentHint, 'worktree', {checkout_path: parent.root, repo_key: commonDir, is_linked_worktree: false}, pending.worktree ?? null);
      if (parent.bare && !completeParentRoot(savedRepoRoot, parent.root))
        throw identityChanged(parentHint, 'root', 'complete saved parent root', savedRepoRoot ?? null);
      if (savedRepoRoot && [savedRepoRoot.tabId, savedRepoRoot.paneId, savedRepoRoot.terminalId, savedRepoRoot.cwd].every(id))
        await assertParentRoot(command, parentHint, savedRepoRoot, parent.root);
      repo = pending;
      custody = {repoWorkspaceId: parentHint, ...(savedRepoRoot ? {repoRoot: savedRepoRoot} : {}), repoCreateIntent: null};
      await save();
    }
  }
  const workspaceId = workspace.workspace_id;
  const root = await runRoot(command, workspaceId, owner, opened?.result, input.stageId);
  custody = {repoWorkspaceId: repo?.workspace_id ?? null, ...(custody.repoRoot ? {repoRoot: custody.repoRoot} : {}),
    ...(Object.hasOwn(custody, 'repoCreateIntent') ? {repoCreateIntent: custody.repoCreateIntent} : {}), workspaceId, root};
  await save();
  const tabs = await tabsFor(command, workspaceId), panes = await paneRows(command, workspaceId);
  // Inside the verified run workspace the label selects the area tab; its pane's live folder takes no part.
  const candidates = tabs.filter(t => t.label === input.stageId);
  for (const t of candidates) {
    const group = panes.filter(p => p.tab_id === t.tab_id);
    if (group.length !== 1) throw identityChanged(workspaceId, 'area_panes', 1, group.length);
  }
  if (candidates.length > 1) throw identityChanged(workspaceId, 'area_tab', input.stageId, candidates.map(t => t.tab_id));
  const owned = {repoWorkspaceId: repo?.workspace_id ?? null, ...(custody.repoRoot ? {repoRoot: custody.repoRoot} : {}),
    ...(Object.hasOwn(custody, 'repoCreateIntent') ? {repoCreateIntent: custody.repoCreateIntent} : {}), workspaceId, root};
  if (candidates.length) {
    const pane = panes.find(p => p.tab_id === candidates[0].tab_id);
    if (![pane.pane_id, pane.terminal_id].every(id)) throw identityChanged(workspaceId, 'pane', 'complete identity', pane);
    custody = {...owned, ...rootFields(pane)};
    await save();
    return custody;
  }
  if (!opened) await ports.beforeCreate?.(1);
  const created = await command(['tab', 'create', '--workspace', workspaceId, '--cwd', cwd, '--label', input.stageId, '--no-focus']);
  const pane = created.result?.root_pane, tabId = created.result?.tab?.tab_id;
  if (created.id !== 'cli:tab:create' || ![tabId, pane?.pane_id, pane?.terminal_id].every(id)) throw problem('invalid_tab_reply');
  const actual = (await paneRows(command, workspaceId)).filter(p => p.tab_id === tabId);
  if (actual.length !== 1 || actual[0].pane_id !== pane.pane_id || actual[0].terminal_id !== pane.terminal_id)
    throw identityChanged(workspaceId, 'area_pane', pane, actual);
  custody = {...owned, tabId, paneId: pane.pane_id, terminalId: pane.terminal_id};
  await save();
  return custody;
}
async function assertRunShell(command, run, ports) {
  if (run.rootPaneId === (ports.env ?? process.env).HERDR_PANE_ID) throw problem('run_shell_caller');
  if (ports.force) return;
  let native;
  try {
    native = (await command(['agent', 'get', run.rootPaneId]))?.result?.agent;
    if (!native || native.pane_id !== run.rootPaneId || !id(native.agent)) throw problem('run_shell_unknown');
  } catch (error) {
    if (error.code !== 'agent_not_found') throw problem('run_shell_unknown');
  }
  if (native) {
    if (['idle', 'done'].includes(native.agent_status)) return;
    throw problem(['working', 'blocked'].includes(native.agent_status) ? 'run_shell_busy' : 'run_shell_unknown');
  }
  let reply;
  try { reply = await command(['pane', 'process-info', '--pane', run.rootPaneId]); }
  catch { throw problem('run_shell_unknown'); }
  const info = reply?.result?.process_info, rows = info?.foreground_processes;
  if (reply?.result?.type !== 'pane_process_info' || info?.pane_id !== run.rootPaneId ||
      !Number.isSafeInteger(info.shell_pid) || info.shell_pid <= 0 || !Number.isSafeInteger(info.foreground_process_group_id) ||
      info.foreground_process_group_id <= 0 || !Array.isArray(rows) || !rows.length ||
      rows.some(row => !Number.isSafeInteger(row?.pid) || row.pid <= 0 || !id(row.name))) throw problem('run_shell_unknown');
  if (info.foreground_process_group_id !== info.shell_pid || rows.length !== 1 || rows[0].pid !== info.shell_pid)
    throw problem('run_shell_busy');
  if (!['bash', 'zsh', 'sh', 'dash', 'fish', 'ksh', 'tcsh'].includes(rows[0].name)) throw problem('run_shell_unknown');
}

export async function closeHerdrRunLayout({runId, cwd, layout, commonDir}, ports) {
  if (!id(runId) || !layout || ![layout.workspaceId, layout.tabId, layout.paneId, layout.terminalId, commonDir].every(id)) throw problem('layout_cleanup_uncertain');
  if (layout.phase === 'closed') return;
  const {command, checkpoint} = ports, root = layout.root ?? layout;
  if (![root.tabId, root.paneId, root.terminalId].every(id)) throw problem('layout_cleanup_uncertain');
  const run = {runId, cwd, commonDir, workspaceId: layout.workspaceId, rootTabId: root.tabId, rootPaneId: root.paneId, rootTerminalId: root.terminalId};
  const inspect = async () => {
    const rows = await inventory(command);
    if (layout.phase === 'close_intent' && !rows.some(w => w.workspace_id === run.workspaceId)) {
      layout.phase = 'closed';
      await checkpoint();
      return false;
    }
    ownedWorkspace(rows, run, cwd);
    await assertRunRoot(command, run, true);
    await assertRunShell(command, run, ports);
    return true;
  };
  if (!await inspect()) return;
  layout.phase = 'close_intent';
  await checkpoint();
  if (!await inspect()) return;
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
