// Generated from prompts/cli/workflow-herdr-layout.prompt.md (sha256: de3bc9fcb8c7088dad9fb3b92770230af758659a6ecc45831bd5ad53c6117731).
import { mkdir, open, readFile, rename, rm, lstat, realpath } from 'node:fs/promises';
import { constants, openSync, closeSync, readFileSync, writeFileSync, fsyncSync, unlinkSync, lstatSync } from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { createHash, randomUUID } from 'node:crypto';
import { lookupRepositoryParent } from './workflow-worktree.mjs';

export const PDD_HERDR_SESSION = 'pdd';
const problem = code => Object.assign(new Error(code), {code});
const directoryFor = ports => ports.directory ?? join(homedir(), '.local', 'state', 'pdd', 'herdr-layout');
const id = value => typeof value === 'string' && value.length > 0;
function repositoryEntry(registry, key, commonDir) {
  const matches=registry.repositories.filter(r=>r.key===key&&r.commonDir===commonDir);
  if(matches.length>1)throw problem('layout_allocation_uncertain');
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
// Limit before quoting so even hostile inventory values remain finite and on one line.
function literal(value) {
  if(value===undefined||value===null)return 'missing';
  const text=String(value),bounded=text.length>240?`${text.slice(0,240)}…[truncated]`:text;
  return JSON.stringify(bounded).replace(/[\u007f-\u009f\u2028\u2029]/g,c=>`\\u${c.charCodeAt(0).toString(16).padStart(4,'0')}`);
}
function identityChanged(saved,field,expected,found) {
  const message=`herdr_layout_identity_changed: Herdr workspace ${literal(saved.workspaceId)}: ${field} expected ${literal(expected)}, found ${literal(found)}. Inspect this workspace in Herdr session pdd; restore its expected identity, then retry your command. If the original identity is missing, manually inspect ownership and layout before restoring it.`;
  return Object.assign(new Error(message),{code:'herdr_layout_identity_changed'});
}
function sameIdentity(saved,field,expected,found) {
  if(expected!==found)throw identityChanged(saved,field,expected,found);
}
function ownedWorkspace(rows, saved, cwd) {
  const row=rows.find(w=>w.workspace_id===saved.workspaceId);
  if(!row)throw identityChanged(saved,'workspace',saved.workspaceId,undefined);
  if(!row.worktree)throw identityChanged(saved,'worktree','present',undefined);
  sameIdentity(saved,'checkout_path',cwd,row.worktree.checkout_path);
  sameIdentity(saved,'repo_key',saved.commonDir,row.worktree.repo_key);
  if(saved.runId)sameIdentity(saved,'is_linked_worktree',true,row.worktree.is_linked_worktree);
  return row;
}
function rootPanes(response,saved) {
  sameIdentity(saved,'pane_list.id','cli:pane:list',response?.id);
  sameIdentity(saved,'pane_list.type','pane_list',response?.result?.type);
  const panes=response?.result?.panes;
  if(!Array.isArray(panes))throw identityChanged(saved,'panes','present',panes);
  return panes;
}
async function assertRunRoot(command, run, closing = false) {
  const panes=rootPanes(await command(['pane','list','--workspace',run.workspaceId]),run);
  const fields=[['workspace_id',run.workspaceId],['tab_id',run.rootTabId],['pane_id',run.rootPaneId],['terminal_id',run.rootTerminalId],['cwd',run.cwd]];
  if(!panes.length)throw identityChanged(run,'panes count',1,0);
  // Narrow by saved identities in stable order, without choosing a replacement root.
  let candidates=panes;
  for(const [field,expected] of fields) {
    const matches=candidates.filter(p=>p?.[field]===expected);
    if(!id(expected))throw identityChanged(run,field,undefined,candidates[0]?.[field]);
    if(!matches.length)throw identityChanged(run,field,expected,candidates[0]?.[field]);
    candidates=matches;
  }
  if(closing) {
    if(panes.length!==1)throw identityChanged(run,'panes count',1,panes.length);
    const reply=await command(['tab','list','--workspace',run.workspaceId]),tabs=reply.result?.tabs;
    if(reply.id!=='cli:tab:list'||reply.result?.type!=='tab_list'||!Array.isArray(tabs)||tabs.length!==1||tabs[0].tab_id!==run.rootTabId)
      throw problem('run_has_open_tabs');
  }
}
async function ownedRepository(rows,repo,command) {
  const row=rows.find(w=>w.workspace_id===repo.workspaceId);
  if(row?.worktree){
    ownedWorkspace(rows,repo,repo.sourceRoot);
    sameIdentity(repo,'is_linked_worktree',false,row.worktree.is_linked_worktree);
  } else {
    if(!row)throw identityChanged(repo,'workspace',repo.workspaceId,undefined);
    for(const [field,value] of [['tab_id',repo.rootTabId],['pane_id',repo.rootPaneId],['terminal_id',repo.rootTerminalId]])
      if(!id(value))throw identityChanged(repo,field,undefined,undefined);
    await assertRunRoot(command,{...repo,cwd:repo.sourceRoot},true);
  }
  return row;
}

export async function openHerdrRunLayout(input, ports) {
  const {command,checkpoint}=ports,directory=directoryFor(ports);
  if(!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(input.repository??'')||!Number.isSafeInteger(input.issueNumber)||input.issueNumber<1
    ||!id(input.runId)||!id(input.workflowName)||!id(input.stageId)||typeof checkpoint!=='function')throw problem('invalid_herdr_layout_input');
  const invokingSource=await realpath(input.sourceRoot),cwd=await realpath(input.cwd),commonDir=input.commonDir;
  if(!id(commonDir))throw problem('invalid_herdr_layout_input');
  const registry=await readRegistry(directory),rows=await inventory(command);
  const parent=await lookupRepositoryParent({cwd:invokingSource,repository:input.repository,commonDir},ports);
  if(parent.state!=='ready')throw problem('repository_parent_unverified');
  const sourceRoot=parent.root,key=input.repository.toLowerCase(),name=input.repository.split('/')[1];
  let repo=repositoryEntry(registry,key,commonDir);
  const pending=registry.runs.find(r=>r.runId===input.runId);
  const runLabel=`${name}#${input.issueNumber} ${input.workflowName}`;
  if(pending && (pending.commonDir!==commonDir || pending.cwd!==cwd ||
    ![runLabel,`#${input.issueNumber} ${input.workflowName}`].includes(pending.label)))throw problem('herdr_run_binding_changed');
  const refused=pending && !pending.workspaceId && !pending.rootPaneId && !pending.rootTabId && !pending.rootTerminalId &&
    (pending.phase==='refused'&&pending.refusal==='linked_worktree_source' ||
     pending.phase==='intent'&&!pending.retriedRefusal&&input.preAgentRefusal==='linked_worktree_source');
  if(refused){
    if(pending.cwd!==cwd || rows.some(w=>w.worktree?.checkout_path===cwd))throw problem('layout_allocation_uncertain');
    pending.phase='refused';pending.refusal='linked_worktree_source';
    await persist(directory,registry);
  }
  if(repo && repo.sourceRoot!==sourceRoot){
    if(!refused || repo.phase!=='ready' || repo.commonDir!==commonDir || repo.sourceRoot!==invokingSource ||
      pending.repoWorkspaceId!==repo.workspaceId || registry.runs.some(r=>r!==pending&&r.repoWorkspaceId===repo.workspaceId))
      throw identityChanged(repo,'sourceRoot',repo.sourceRoot,sourceRoot);
    const row=rows.find(w=>w.workspace_id===repo.workspaceId);
    if(!row)throw identityChanged(repo,'workspace',repo.workspaceId,undefined);
    if(row.worktree)ownedWorkspace(rows,repo,invokingSource);
    else {
      const panes=rootPanes(await command(['pane','list','--workspace',repo.workspaceId]),repo);
      if(panes.length!==1)throw identityChanged(repo,'panes count',1,panes.length);
      sameIdentity(repo,'workspace_id',repo.workspaceId,panes[0]?.workspace_id);
      sameIdentity(repo,'cwd',invokingSource,panes[0]?.cwd);
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
    if(run.repoWorkspaceId!==repo.workspaceId||run.cwd!==cwd||![runLabel,`#${input.issueNumber} ${input.workflowName}`].includes(run.label))throw problem('herdr_run_binding_changed');
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
  await checkpoint();
  const created=await command(['tab','create','--workspace',run.workspaceId,'--cwd',cwd,'--label',input.stageId,'--no-focus']);
  const tabId=created.result?.tab?.tab_id,paneId=created.result?.root_pane?.pane_id,terminalId=created.result?.root_pane?.terminal_id;
  if(created.id!=='cli:tab:create'||![tabId,paneId,terminalId].every(id))throw problem('invalid_tab_reply');
  return {repoWorkspaceId:repo.workspaceId,workspaceId:run.workspaceId,tabId,paneId,terminalId};
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
