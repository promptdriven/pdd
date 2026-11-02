// Generated from prompts/cli/workflow-herdr-layout.prompt.md (sha256: 1991c2b432c9c2647f8cd9abf633b8ea649a4854aa64225a16768496b0bf4cd2).
import { mkdir, open, readFile, rename, rm, lstat, realpath } from 'node:fs/promises';
import { constants, openSync, closeSync, readFileSync, writeFileSync, fsyncSync, unlinkSync, lstatSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { createHash, randomUUID } from 'node:crypto';
import { lookupRepositoryParent } from './workflow-worktree.mjs';

export const PDD_HERDR_SESSION = 'pdd';
const problem = code => Object.assign(new Error(code), {code});
const directoryFor = ports => ports.directory ?? join(homedir(), '.local', 'state', 'pdd', 'herdr-layout');
const id = value => typeof value === 'string' && value.length > 0;
// One filesystem identity for both operands of every path comparison: the same string, or the same realpath when both
// resolve. A symlink alias equals its target in either direction; an unresolvable path is never equal by name.
export function samePath(a, b) {
  if (!id(a) || !id(b)) return false;
  if (a === b) return true;
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
function repositoryEntry(registry, key, commonDir) {
  const matches=registry.repositories.filter(r=>r.key===key&&r.commonDir===commonDir);
  if(matches.length>1)throw problem('layout_allocation_uncertain');
  // An entry whose repository disagrees with its key cannot prove ownership of either.
  if(matches[0]&&String(matches[0].repository??'').toLowerCase()!==key)throw problem('invalid_layout_registry');
  return matches[0];
}
const checkoutLabel = repo => `${repo.repository}@${createHash('sha256').update(repo.commonDir).digest('hex').slice(0,12)}`;
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
async function readRegistry(directory) {
  try {
    const handle=await open(join(directory,'registry.json'),constants.O_RDONLY|constants.O_NOFOLLOW);
    try {
      const value=JSON.parse(await handle.readFile('utf8'));
      if(value.version!==1||!Array.isArray(value.repositories)||!Array.isArray(value.runs))throw problem('invalid_layout_registry');
      return value;
    } finally {await handle.close();}
  } catch(error) {if(error.code!=='ENOENT')throw error;return {version:1,repositories:[],runs:[]};}
}
async function persist(directory, registry) {
  const temporary=join(directory,`${randomUUID()}.tmp`),handle=await open(temporary,'wx',0o600);
  try {await handle.writeFile(JSON.stringify(registry)+'\n');await handle.sync();} finally {await handle.close();}
  await rename(temporary,join(directory,'registry.json'));
  const parent=await open(directory,'r');try {await parent.sync();} finally {await parent.close();}
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
  if(response.id!=='cli:pane:list'||response.result?.type!=='pane_list'||!Array.isArray(panes))throw identityChanged(workspaceId,'pane_list',{type:'pane_list'},response.result?.type);
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
    const reply=await command(['tab','list','--workspace',run.workspaceId]),tabs=reply.result?.tabs;
    if(reply.id!=='cli:tab:list'||reply.result?.type!=='tab_list'||!Array.isArray(tabs)||tabs.length!==1||tabs[0].tab_id!==run.rootTabId)
      throw problem('run_has_open_tabs');
  }
}
// The selected stage tab of a run when it is live: one pane with the saved identity in the run's checkout.
async function liveStageTab(command, run, saved) {
  if(!id(saved?.tabId)||!id(saved?.paneId))return false;
  const panes=(await paneRows(command,run.workspaceId)).filter(p=>p.tab_id===saved.tabId);
  if(!panes.length)return false;
  if(panes.length!==1||panes[0].pane_id!==saved.paneId)throw identityChanged(run.workspaceId,'pane_id',saved.paneId,panes.map(p=>p.pane_id));
  if(id(saved.terminalId)&&panes[0].terminal_id!==saved.terminalId)throw identityChanged(run.workspaceId,'terminal_id',saved.terminalId,panes[0].terminal_id);
  if(!samePath(panes[0].cwd,run.cwd))throw identityChanged(run.workspaceId,'cwd',run.cwd,panes[0].cwd);
  return true;
}
// The registry is a cache of the durable run record plus live Herdr. A missing or stale entry of this run is rebuilt
// from both facts when exactly one live workspace is this run's checkout; anything else refuses before a mutation.
async function reconcileOwner({registry,rows,command,checkpoint,directory,owner,key,repository,sourceRoot,commonDir,cwd,runLabel}) {
  const chats=(owner.chats??[]).filter(chat=>id(chat?.workspaceId)),layout=owner.layout??{};
  const workspaceId=layout.workspaceId??chats.at(-1)?.workspaceId,repoWorkspaceId=layout.repoWorkspaceId??chats.at(-1)?.repoWorkspaceId;
  if(!id(workspaceId))return;
  let entry=registry.runs.find(r=>r.runId===owner.runId),repo=repositoryEntry(registry,key,commonDir);
  const verified=async(check)=>{try{await check();return true;}catch{return false;}};
  const runCached=entry?.phase==='ready'&&entry.workspaceId===workspaceId&&await verified(async()=>{ownedWorkspace(rows,entry,cwd);await assertRunRoot(command,entry);});
  const repoCached=repo?.phase==='ready'&&(!id(repoWorkspaceId)||repo.workspaceId===repoWorkspaceId)&&await verified(()=>ownedRepository(rows,repo,command));
  if(runCached&&repoCached)return;
  if(!runCached) {
    const candidates=rows.filter(row=>runWorkspace(row,cwd,commonDir));
    if(candidates.length>1)throw identityChanged(workspaceId,'workspace_id',workspaceId,candidates.map(row=>row.workspace_id));
    ownedWorkspace(rows,{workspaceId,commonDir,runId:owner.runId},cwd);
    let root=[layout.tabId,layout.paneId,layout.terminalId].every(id)?{rootTabId:layout.tabId,rootPaneId:layout.paneId,rootTerminalId:layout.terminalId}:null;
    if(!root) {
      const panes=(await paneRows(command,workspaceId)).filter(p=>!chats.some(chat=>chat.tabId===p.tab_id));
      if(panes.length!==1)throw identityChanged(workspaceId,'root_panes',1,panes.length);
      root={rootTabId:panes[0].tab_id,rootPaneId:panes[0].pane_id,rootTerminalId:panes[0].terminal_id};
    }
    entry={runId:owner.runId,repoWorkspaceId:id(repoWorkspaceId)?repoWorkspaceId:repo?.workspaceId,commonDir,cwd,
      label:[runLabel,`#${owner.number} ${owner.workflow}`].includes(entry?.label)?entry.label:runLabel,workspaceId,...root,phase:'ready',...(entry?.stageTabs?{stageTabs:entry.stageTabs}:{})};
    await assertRunRoot(command,entry);
  }
  if(!repoCached) {
    const repoId=id(repoWorkspaceId)?repoWorkspaceId:entry.repoWorkspaceId,row=rows.find(w=>w.workspace_id===repoId);
    if(!row)throw identityChanged(repoId,'workspace_id',repoId,null);
    const rebuilt={key,repository,sourceRoot,commonDir,workspaceId:repoId,phase:'ready'};
    ownedWorkspace(rows,rebuilt,sourceRoot);
    if(row.worktree.is_linked_worktree!==false)throw identityChanged(repoId,'is_linked_worktree',false,row.worktree.is_linked_worktree);
    registry.repositories=[...registry.repositories.filter(r=>r!==repo),rebuilt];
  }
  if(!entry.repoWorkspaceId)throw identityChanged(workspaceId,'repo_workspace_id',repoWorkspaceId??null,null);
  registry.runs=[...registry.runs.filter(r=>r.runId!==owner.runId),entry];
  await checkpoint();await persist(directory,registry);
}
async function ownedRepository(rows,repo,command) {
  const row=rows.find(w=>w.workspace_id===repo.workspaceId);
  if(row?.worktree){
    ownedWorkspace(rows,repo,repo.sourceRoot);
    if(row.worktree.is_linked_worktree!==false)throw problem('herdr_layout_identity_changed');
  } else {
    if(!row||![repo.rootTabId,repo.rootPaneId,repo.rootTerminalId].every(id))throw problem('herdr_layout_identity_changed');
    await assertRunRoot(command,{...repo,cwd:repo.sourceRoot},true);
  }
  return row;
}

export async function openHerdrRunLayout(input, ports) {
  const {command,checkpoint}=ports,directory=directoryFor(ports);
  if(!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(input.repository??'')||!Number.isSafeInteger(input.issueNumber)||input.issueNumber<1
    ||!id(input.runId)||!id(input.workflowName)||!id(input.stageId)||typeof checkpoint!=='function')throw problem('invalid_herdr_layout_input');
  const invokingSource=await realpath(input.sourceRoot),cwd=await realpath(input.cwd),commonDir=input.commonDir,owner=input.run;
  if(!id(commonDir))throw problem('invalid_herdr_layout_input');
  if(owner!==undefined&&(!owner||typeof owner!=='object'||owner.runId!==input.runId)||input.repair!==undefined&&(input.repair!==true||!owner))throw problem('invalid_herdr_layout_input');
  const registry=await readRegistry(directory),rows=await inventory(command);
  const parent=await lookupRepositoryParent({cwd:invokingSource,repository:input.repository,commonDir},ports);
  if(parent.state!=='ready')throw problem('repository_parent_unverified');
  const sourceRoot=parent.root,key=input.repository.toLowerCase(),name=input.repository.split('/')[1];
  const runLabel=`${name}#${input.issueNumber} ${input.workflowName}`;
  if(owner)await reconcileOwner({registry,rows,command,checkpoint,directory,owner,key,repository:input.repository,sourceRoot,commonDir,cwd,runLabel});
  let repo=repositoryEntry(registry,key,commonDir);
  const pending=registry.runs.find(r=>r.runId===input.runId);
  if(pending && (!samePath(pending.commonDir,commonDir) || !samePath(pending.cwd,cwd) ||
    ![runLabel,`#${input.issueNumber} ${input.workflowName}`].includes(pending.label)))throw problem('herdr_run_binding_changed');
  const refused=pending && !pending.workspaceId && !pending.rootPaneId && !pending.rootTabId && !pending.rootTerminalId &&
    (pending.phase==='refused'&&pending.refusal==='linked_worktree_source' ||
     pending.phase==='intent'&&!pending.retriedRefusal&&input.preAgentRefusal==='linked_worktree_source');
  // A saved run keeps its repository workspace binding: a missing or different namespace refuses before any allocation.
  if(pending && (!repo || pending.repoWorkspaceId!==repo.workspaceId))throw problem('herdr_run_binding_changed');
  if(refused){
    if(!samePath(pending.cwd,cwd) || rows.some(w=>samePath(w.worktree?.checkout_path,cwd)))throw problem('layout_allocation_uncertain');
    pending.phase='refused';pending.refusal='linked_worktree_source';
    await persist(directory,registry);
  }
  if(repo && !samePath(repo.sourceRoot,sourceRoot)){
    if(!refused || repo.phase!=='ready' || !samePath(repo.commonDir,commonDir) || !samePath(repo.sourceRoot,invokingSource) ||
      pending.repoWorkspaceId!==repo.workspaceId || registry.runs.some(r=>r!==pending&&r.repoWorkspaceId===repo.workspaceId))
      throw problem('herdr_layout_identity_changed');
    const row=rows.find(w=>w.workspace_id===repo.workspaceId);
    if(!row)throw problem('herdr_layout_identity_changed');
    if(row.worktree)ownedWorkspace(rows,repo,invokingSource);
    else {
      const reply=await command(['pane','list','--workspace',repo.workspaceId]),panes=reply.result?.panes;
      if(reply.id!=='cli:pane:list'||reply.result?.type!=='pane_list'||!Array.isArray(panes)||panes.length!==1||
        panes[0].workspace_id!==repo.workspaceId||!samePath(panes[0].cwd,invokingSource))throw problem('herdr_layout_identity_changed');
    }
    registry.archivedRepositories=[...(registry.archivedRepositories??[]),{...repo,reason:'linked-source-pre-agent-refusal'}];
    registry.repositories=registry.repositories.filter(r=>r!==repo);repo=null;
    await persist(directory,registry);
  }
  if(repo) {
    if(repo.phase!=='ready')throw problem('layout_allocation_uncertain');
    await ownedRepository(rows,repo,command);
  } else {
    const clashes=registry.repositories.filter(r=>r.repository.split('/')[1].toLowerCase()===name.toLowerCase());
    let label=rows.some(w=>w.label?.toLowerCase()===name.toLowerCase())?input.repository:name;
    if(rows.some(w=>w.label===label)&&registry.repositories.some(r=>r.key===key&&r.commonDir!==commonDir))
      label=checkoutLabel({repository:input.repository,commonDir});
    if(rows.some(w=>w.label===label))throw problem('repository_label_unavailable');
    for(const other of clashes.filter(r=>r.key!==key)) {
      if(other.phase!=='ready')throw problem('layout_allocation_uncertain');
      const existing=await ownedRepository(rows,other,command);
      if(existing.label!==other.repository) {
        const qualified=rows.some(w=>w.workspace_id!==other.workspaceId&&w.label===other.repository)?checkoutLabel(other):other.repository;
        if(existing.label===qualified)continue;
        if(rows.some(w=>w.workspace_id!==other.workspaceId&&w.label===qualified))throw problem('repository_label_unavailable');
        await checkpoint();
        const renamed=await command(['workspace','rename',other.workspaceId,qualified]);
        if(renamed.id!=='cli:workspace:rename'||renamed.result?.type!=='workspace_info'||renamed.result?.workspace?.workspace_id!==other.workspaceId||renamed.result?.workspace?.label!==qualified)throw problem('repository_rename_unconfirmed');
        existing.label=qualified;
      }
    }
    repo={key,repository:input.repository,sourceRoot,commonDir,phase:'intent'};registry.repositories.push(repo);
    await checkpoint();await persist(directory,registry);
    const created=await command(['workspace','create','--cwd',sourceRoot,'--label',label,'--no-focus']);
    repo.workspaceId=created.result?.workspace?.workspace_id;
    repo.rootTabId=created.result?.tab?.tab_id;repo.rootPaneId=created.result?.root_pane?.pane_id;repo.rootTerminalId=created.result?.root_pane?.terminal_id;
    if(created.id!=='cli:workspace:create'||!id(repo.workspaceId))throw problem('invalid_workspace_reply');
    repo.phase='ready';await persist(directory,registry);
  }
  let run=registry.runs.find(r=>r.runId===input.runId);
  if(run && run.phase!=='refused') {
    if(run.phase!=='ready')throw problem('layout_allocation_uncertain');
    // Runs from 0.1.3 and older carry the label without the repository name.
    if(run.repoWorkspaceId!==repo.workspaceId||!samePath(run.cwd,cwd)||![runLabel,`#${input.issueNumber} ${input.workflowName}`].includes(run.label))throw problem('herdr_run_binding_changed');
    ownedWorkspace(rows,run,cwd);
    await assertRunRoot(command,run);
  } else {
    if(run){
      if(!refused)throw problem('layout_allocation_uncertain');
      run.repoWorkspaceId=repo.workspaceId;run.phase='intent';run.retriedRefusal=true;
    } else {
      run={runId:input.runId,repoWorkspaceId:repo.workspaceId,commonDir,cwd,label:runLabel,phase:'intent'};
      registry.runs.push(run);
    }
    await checkpoint();await persist(directory,registry);
    let opened;
    try {opened=await command(['worktree','open','--workspace',repo.workspaceId,'--path',cwd,'--label',run.label,'--no-focus']);}
    catch(error){
      if(error.code==='linked_worktree_source'){run.phase='refused';run.refusal=error.code;await persist(directory,registry);}
      throw error;
    }
    run.workspaceId=opened.result?.workspace?.workspace_id;
    if(opened.id!=='cli:worktree:open'||opened.result?.already_open===true||!id(run.workspaceId))throw problem('invalid_worktree_reply');
    run.rootTabId=opened.result?.tab?.tab_id;run.rootPaneId=opened.result?.root_pane?.pane_id;run.rootTerminalId=opened.result?.root_pane?.terminal_id;
    if(![run.rootTabId,run.rootPaneId,run.rootTerminalId].every(id))throw problem('invalid_worktree_reply');
    ownedWorkspace(await inventory(command),run,cwd);await assertRunRoot(command,run);
    run.phase='ready';await persist(directory,registry);
  }
  const root={tabId:run.rootTabId,paneId:run.rootPaneId,terminalId:run.rootTerminalId},owned={repoWorkspaceId:repo.workspaceId,workspaceId:run.workspaceId};
  // Repair reconciles the selected stage tab idempotently: a live saved tab is returned; a missing one gets one new tab.
  const repaired=run.stageTabs?.[input.stageId];
  if(input.repair===true) {
    const chat=[...(owner.chats??[])].reverse().find(item=>item.area===input.stageId&&item.workspaceId===run.workspaceId);
    for(const saved of [chat,repaired])if(saved&&saved.phase!=='intent'&&await liveStageTab(command,run,saved))return {...owned,tabId:saved.tabId,paneId:saved.paneId,terminalId:saved.terminalId,root};
    if(repaired?.phase==='intent')throw problem('layout_allocation_uncertain');
    run.stageTabs={...run.stageTabs,[input.stageId]:{phase:'intent'}};
  }
  await checkpoint();
  if(input.repair===true)await persist(directory,registry);
  const created=await command(['tab','create','--workspace',run.workspaceId,'--cwd',cwd,'--label',input.stageId,'--no-focus']);
  const tabId=created.result?.tab?.tab_id,paneId=created.result?.root_pane?.pane_id,terminalId=created.result?.root_pane?.terminal_id;
  if(created.id!=='cli:tab:create'||![tabId,paneId,terminalId].every(id))throw problem('invalid_tab_reply');
  if(input.repair===true){run.stageTabs[input.stageId]={tabId,paneId,terminalId};await persist(directory,registry);}
  return {...owned,tabId,paneId,terminalId,root};
}
export async function closeHerdrRunLayout({runId,cwd,layout}, ports) {
  const directory=directoryFor(ports),registry=await readRegistry(directory),{command,checkpoint}=ports;
  const run=registry.runs.find(r=>r.runId===runId);
  if(!run||run.cwd!==cwd||run.workspaceId!==layout.workspaceId||run.repoWorkspaceId!==layout.repoWorkspaceId)throw problem('herdr_run_binding_changed');
  if(run.phase==='closed')return;
  if(run.phase!=='ready')throw problem('layout_cleanup_uncertain');
  ownedWorkspace(await inventory(command),run,cwd);
  await assertRunRoot(command,run,true);
  await checkpoint();run.phase='close_intent';await persist(directory,registry);
  const closed=await command(['workspace','close',run.workspaceId]);
  if(closed.id!=='cli:workspace:close'||closed.result?.type!=='ok'||(await inventory(command)).some(w=>w.workspace_id===run.workspaceId))throw problem('workspace_close_unconfirmed');
  run.phase='closed';await persist(directory,registry);
}

// After the last open run of a repository is closed, close the repository's own workspace too (it only holds a shell).
// Returns true when it closed or was already gone; a workspace still in use (more tabs or panes, or open runs) stays.
export async function closeHerdrRepoLayoutIfIdle({repository,commonDir}, ports) {
  const directory=directoryFor(ports),registry=await readRegistry(directory),{command,checkpoint}=ports;
  const repo=repositoryEntry(registry,String(repository).toLowerCase(),commonDir);
  if(!repo||repo.phase!=='ready')return false;
  if(registry.runs.some(r=>r.repoWorkspaceId===repo.workspaceId&&r.phase!=='closed'))return false;
  const rows=await inventory(command);
  if(rows.some(w=>w.workspace_id===repo.workspaceId)) {
    await ownedRepository(rows,repo,command);
    const tabs=(await command(['tab','list','--workspace',repo.workspaceId])).result?.tabs,panes=(await command(['pane','list','--workspace',repo.workspaceId])).result?.panes;
    if(!Array.isArray(tabs)||tabs.length!==1||!Array.isArray(panes)||panes.length!==1)return false;
    await checkpoint?.();repo.phase='close_intent';await persist(directory,registry);
    const closed=await command(['workspace','close',repo.workspaceId]);
    if(closed.id!=='cli:workspace:close'||closed.result?.type!=='ok'||(await inventory(command)).some(w=>w.workspace_id===repo.workspaceId))throw problem('workspace_close_unconfirmed');
  }
  registry.repositories=registry.repositories.filter(r=>r!==repo);await persist(directory,registry);
  return true;
}
