// Generated from prompts/cli/workflow-herdr-layout.prompt.md (sha256: 0eee98f339cf7498e45105e49ce16288ee07672e0f2a52f82f0ae47e0d777ea0).
import { mkdir, open, readFile, rename, rm, lstat, realpath } from 'node:fs/promises';
import { constants, openSync, closeSync, readFileSync, writeFileSync, fsyncSync, unlinkSync, lstatSync } from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { randomUUID } from 'node:crypto';

export const PDD_HERDR_SESSION = 'pdd';
const problem = code => Object.assign(new Error(code), {code});
const directoryFor = ports => ports.directory ?? join(homedir(), '.local', 'state', 'pdd', 'herdr-layout');
const id = value => typeof value === 'string' && value.length > 0;
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
  const deadline=Date.now()+30000;
  while(!claimLock(directory)) {
    if(Date.now()>=deadline)throw problem('herdr_layout_busy');
    await new Promise(r=>setTimeout(r,25));
  }
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
  if(!row || !row.worktree || row.worktree.checkout_path!==cwd || row.worktree.repo_key!==saved.commonDir
    || (saved.runId && row.worktree.is_linked_worktree!==true))throw problem('herdr_layout_identity_changed');
  return row;
}
async function assertRunRoot(command, run, closing = false) {
  const response=await command(['pane','list','--workspace',run.workspaceId]),panes=response.result?.panes;
  if(response.id!=='cli:pane:list'||response.result?.type!=='pane_list'||!Array.isArray(panes)
    ||!panes.some(p=>p.workspace_id===run.workspaceId&&p.tab_id===run.rootTabId&&p.pane_id===run.rootPaneId
      &&p.terminal_id===run.rootTerminalId&&p.cwd===run.cwd))throw problem('herdr_layout_identity_changed');
  if(closing) {
    if(panes.length!==1)throw problem('herdr_layout_identity_changed');
    const reply=await command(['tab','list','--workspace',run.workspaceId]),tabs=reply.result?.tabs;
    if(reply.id!=='cli:tab:list'||reply.result?.type!=='tab_list'||!Array.isArray(tabs)||tabs.length!==1||tabs[0].tab_id!==run.rootTabId)
      throw problem('run_has_open_tabs');
  }
}
export async function openHerdrRunLayout(input, ports) {
  const {command,checkpoint}=ports,directory=directoryFor(ports);
  if(!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(input.repository??'')||!Number.isSafeInteger(input.issueNumber)||input.issueNumber<1
    ||!id(input.runId)||!id(input.workflowName)||!id(input.stageId)||typeof checkpoint!=='function')throw problem('invalid_herdr_layout_input');
  const sourceRoot=await realpath(input.sourceRoot),cwd=await realpath(input.cwd),commonDir=input.commonDir;
  if(!id(commonDir))throw problem('invalid_herdr_layout_input');
  const registry=await readRegistry(directory),rows=await inventory(command);
  const key=input.repository.toLowerCase(),name=input.repository.split('/')[1];
  let repo=registry.repositories.find(r=>r.key===key);
  if(repo) {
    if(repo.phase!=='ready')throw problem('layout_allocation_uncertain');
    if(repo.commonDir!==commonDir)throw problem('repository_checkout_changed');
    ownedWorkspace(rows,repo,repo.sourceRoot);
  } else {
    const clashes=registry.repositories.filter(r=>r.repository.split('/')[1].toLowerCase()===name.toLowerCase());
    const label=clashes.length||rows.some(w=>w.label?.toLowerCase()===name.toLowerCase())?input.repository:name;
    if(rows.some(w=>w.label===label))throw problem('repository_label_unavailable');
    for(const other of clashes) {
      if(other.phase!=='ready')throw problem('layout_allocation_uncertain');
      const existing=ownedWorkspace(rows,other,other.sourceRoot);
      if(existing.label!==other.repository) {
        if(rows.some(w=>w.workspace_id!==other.workspaceId&&w.label===other.repository))throw problem('repository_label_unavailable');
        await checkpoint();
        const renamed=await command(['workspace','rename',other.workspaceId,other.repository]);
        if(renamed.id!=='cli:workspace:rename'||renamed.result?.type!=='workspace_info'||renamed.result?.workspace?.workspace_id!==other.workspaceId||renamed.result?.workspace?.label!==other.repository)throw problem('repository_rename_unconfirmed');
      }
    }
    repo={key,repository:input.repository,sourceRoot,commonDir,phase:'intent'};registry.repositories.push(repo);
    await checkpoint();await persist(directory,registry);
    const created=await command(['workspace','create','--cwd',sourceRoot,'--label',label,'--no-focus']);
    repo.workspaceId=created.result?.workspace?.workspace_id;
    if(created.id!=='cli:workspace:create'||!id(repo.workspaceId))throw problem('invalid_workspace_reply');
    repo.phase='ready';await persist(directory,registry);
  }
  let run=registry.runs.find(r=>r.runId===input.runId);
  if(run) {
    if(run.phase!=='ready')throw problem('layout_allocation_uncertain');
    if(run.repoWorkspaceId!==repo.workspaceId||run.cwd!==cwd||run.label!==`#${input.issueNumber} ${input.workflowName}`)throw problem('herdr_run_binding_changed');
    ownedWorkspace(rows,run,cwd);
    await assertRunRoot(command,run);
  } else {
    run={runId:input.runId,repoWorkspaceId:repo.workspaceId,commonDir,cwd,label:`#${input.issueNumber} ${input.workflowName}`,phase:'intent'};
    registry.runs.push(run);await checkpoint();await persist(directory,registry);
    const opened=await command(['worktree','open','--workspace',repo.workspaceId,'--path',cwd,'--label',run.label,'--no-focus']);
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
