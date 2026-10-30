import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, rm, mkdir, stat, realpath } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { randomUUID } from 'node:crypto';
import { allocateIssueWorktree } from '../src/workflow-worktree.mjs';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';

async function fixture(t){
 const root=await realpath(await mkdtemp(join(tmpdir(),'pdd-layout-')));t.after(()=>rm(root,{recursive:true,force:true}));
 const sourceRoot=join(root,'coffee'),cwd=join(root,'run');await mkdir(sourceRoot);await mkdir(cwd);
 const git=async(root,...args)=>promisify(execFile)('git',args,{cwd:root});
 const init=async(root,repository)=>{await git(root,'init','-q','-b','main');await git(root,'-c','user.name=Test','-c','user.email=test@example.invalid','commit','--allow-empty','-qm','Base');await git(root,'remote','add','origin','https://github.com/'+repository+'.git');};
 await init(sourceRoot,'alice/coffee');
 const input={runId:randomUUID(),repository:'alice/coffee',sourceRoot,commonDir:join(sourceRoot,'.git'),cwd,issueNumber:2,workflowName:'small-change',stageId:'scope'};
 const calls=[],workspaces=[];let id=0;
 const command=async args=>{
  calls.push(args);const [group,verb]=args,val=flag=>args[args.indexOf(flag)+1];
  if(group==='workspace'&&verb==='list')return {id:'cli:workspace:list',result:{type:'workspace_list',workspaces:structuredClone(workspaces)}};
  if(group==='workspace'&&verb==='rename'){workspaces.find(w=>w.workspace_id===args[2]).label=args[3];return {id:'cli:workspace:rename',result:{type:'workspace_info',workspace:workspaces.find(w=>w.workspace_id===args[2])}};}
  if(group==='workspace'&&verb==='create'||group==='worktree'&&verb==='open'){
   const parent=workspaces.find(w=>w.workspace_id===val('--workspace'));
   const path=group==='workspace'?val('--cwd'):val('--path');
   const workspace={workspace_id:`w${++id}`,label:val('--label'),worktree:{checkout_path:path,repo_key:parent?.worktree.repo_key??join(path,'.git'),is_linked_worktree:group==='worktree'}};workspaces.push(workspace);
   return {id:`cli:${group}:${verb}`,result:{type:group==='workspace'?'workspace_created':'worktree_opened',workspace,
    tab:{tab_id:`${workspace.workspace_id}:t1`},root_pane:{pane_id:`${workspace.workspace_id}:p1`,terminal_id:`term${id}`}}};
  }
  if(group==='workspace'&&verb==='close'){workspaces.splice(workspaces.findIndex(w=>w.workspace_id===args[2]),1);return {id:'cli:workspace:close',result:{type:'ok'}};}
  if(group==='pane'&&verb==='list'){const w=workspaces.find(w=>w.workspace_id===val('--workspace'));return {id:'cli:pane:list',result:{type:'pane_list',panes:[{workspace_id:w.workspace_id,tab_id:w.workspace_id+':t1',pane_id:w.workspace_id+':p1',terminal_id:'term'+w.workspace_id.slice(1),cwd:w.worktree?.checkout_path}]}};}
  if(group==='tab'&&verb==='list')return {id:'cli:tab:list',result:{type:'tab_list',tabs:[{tab_id:val('--workspace')+':t1'}]}};
  if(group==='tab'&&verb==='create')return {id:'cli:tab:create',result:{type:'tab_created',tab:{tab_id:`${val('--workspace')}:t${++id}`},root_pane:{pane_id:`${val('--workspace')}:p${id}`,terminal_id:`term${id}`}}};
  throw Error(`Unexpected command ${JSON.stringify(args)}`);
 };
 const ports={command,directory:join(root,'state'),checkpoint:async()=>{}};
 const module=await import('../src/workflow-herdr-layout.mjs');
 const open=(extra={})=>module.withHerdrLayoutLock(()=>module.openHerdrRunLayout({...input,...extra},ports),ports);
 return {module,root,input,ports,calls,workspaces,open,init};
}
test('repository reuse, one worktree per run, issue/workflow label and stage tabs',async t=>{
 const f=await fixture(t),a=await f.open(),b=await f.open({stageId:'change'});
 assert.equal(a.repoWorkspaceId,b.repoWorkspaceId);assert.equal(a.workspaceId,b.workspaceId);assert.notEqual(a.tabId,b.tabId);
 assert.deepEqual(f.workspaces.map(w=>w.label),['coffee','coffee#2 small-change']);
 assert.deepEqual(f.calls.find(a=>a[0]==='worktree'),['worktree','open','--workspace',a.repoWorkspaceId,'--path',f.input.cwd,'--label','coffee#2 small-change','--no-focus']);
 assert.equal(f.calls.filter(a=>a[0]==='worktree').length,1);
 assert(f.calls.filter(c=>c[0]==='tab').every(c=>c[c.indexOf('--workspace')+1]===a.workspaceId));
});
test('a busy layout lock fails at once instead of waiting; a later run shares the repository workspace',async t=>{
 const f=await fixture(t),cwd=join(f.root,'run2');await mkdir(cwd);
 const command=f.ports.command;let release,entered;const held=new Promise(r=>{release=r;}),inside=new Promise(r=>{entered=r;});
 f.ports.command=async args=>{if(args[0]==='worktree'){entered();await held;}return command(args);};
 const first=f.open();await inside;
 await assert.rejects(f.open({runId:randomUUID(),cwd,issueNumber:3}),error=>error.code==='herdr_layout_busy');
 release();const a=await first;f.ports.command=command;
 const b=await f.open({runId:randomUUID(),cwd,issueNumber:3});
 assert.equal(a.repoWorkspaceId,b.repoWorkspaceId);assert.notEqual(a.workspaceId,b.workspaceId);
 assert.deepEqual(f.workspaces.map(w=>w.label),['coffee','coffee#2 small-change','coffee#3 small-change']);
});
test('repo-name clash qualifies both owned labels and preserves existing run',async t=>{
 const f=await fixture(t),a=await f.open(),other=join(f.root,'other');await mkdir(other);await f.init(other,'bob/coffee');
 await f.open({runId:randomUUID(),repository:'bob/coffee',sourceRoot:other,commonDir:join(other,'.git'),cwd:other});
 assert.deepEqual(f.workspaces.map(w=>w.label),['alice/coffee','coffee#2 small-change','bob/coffee','coffee#2 small-change']);assert.equal(f.workspaces[1].workspace_id,a.workspaceId);
});
test('run cleanup closes only run workspace, retaining repository and git checkout',async t=>{
 const f=await fixture(t),layout=await f.open();
 await f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRunLayout({...f.input,layout},f.ports),f.ports);
 assert.deepEqual(f.workspaces.map(w=>w.label),['coffee']);assert.deepEqual(f.calls.filter(a=>a[1]==='close'),[['workspace','close',layout.workspaceId]]);
 assert(!f.calls.some(a=>a[0]==='worktree'&&a[1]==='remove'));assert((await stat(f.input.cwd)).isDirectory());
});
test('unrelated workspace untouched, allocation reply loss never repeats creation',async t=>{
 const f=await fixture(t);f.workspaces.push({workspace_id:'personal',label:'notes'});const command=f.ports.command;
 f.ports.command=async args=>{const response=await command(args);if(args[0]==='worktree')throw Error('reply lost');return response;};
 await assert.rejects(f.open(),/reply lost/);f.ports.command=command;await assert.rejects(f.open(),/layout_allocation_uncertain/);
 assert.deepEqual(f.workspaces[0],{workspace_id:'personal',label:'notes'});assert.equal(f.calls.filter(a=>a[0]==='worktree').length,1);
});

test('missing or changed worktree identity cannot authorize run reuse or close',async t=>{
 for(const patch of [null,{checkout_path:'/other',repo_key:'/other/.git',is_linked_worktree:true}]) {
  const f=await fixture(t),layout=await f.open();
  const row=f.workspaces.find(w=>w.workspace_id===layout.workspaceId);row.worktree=patch;
  await assert.rejects(f.open(),/herdr_layout_identity_changed/);
  await assert.rejects(f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRunLayout({...f.input,layout},f.ports),f.ports),/herdr_layout_identity_changed/);
  assert(!f.calls.some(a=>a[1]==='close'));
 }
});
test('changed root terminal or an extra tab prevents run cleanup',async t=>{
 for(const kind of ['terminal','tab','pane']) {
  const f=await fixture(t),layout=await f.open();const original=f.ports.command;
  f.ports.command=async args=>{const response=await original(args);if(kind==='terminal'&&args[0]==='pane')response.result.panes[0].terminal_id='replacement';if(kind==='pane'&&args[0]==='pane')response.result.panes.push({pane_id:'person-pane'});if(kind==='tab'&&args[0]==='tab'&&args[1]==='list')response.result.tabs.push({tab_id:'user-tab'});return response;};
  await assert.rejects(f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRunLayout({...f.input,layout},f.ports),f.ports),/herdr_layout_identity_changed|run_has_open_tabs/);
  assert(!f.calls.some(a=>a[1]==='close'));
 }
});
test('Ctrl+C leaves a proved-dead layout owner recoverable by the next process',async t=>{
 const {spawn}=await import('node:child_process');const f=await fixture(t);
 const script=`const {withHerdrLayoutLock}=await import(process.argv[1]);process.on('SIGINT',()=>process.exit(130));await withHerdrLayoutLock(async()=>{console.log('LOCKED');await new Promise(()=>{setInterval(()=>{},1000);});},{directory:process.argv[2]});`;
 const child=spawn(process.execPath,['--input-type=module','-e',script,new URL('../src/workflow-herdr-layout.mjs',import.meta.url).href,f.ports.directory],{stdio:['ignore','pipe','pipe']});
 t.after(()=>child.kill('SIGKILL'));
 const ready=new Promise(resolve=>child.stdout.once('data',resolve));const ended=new Promise(resolve=>child.once('exit',resolve));
 await ready;child.kill('SIGINT');assert.equal(await ended,130);
 let acquired=false;await f.module.withHerdrLayoutLock(()=>{acquired=true;},f.ports);assert.equal(acquired,true);
});

for (const origin of ['https://github.com/Acme/Project.git',
  'git@github.com:Acme/Project.git', 'ssh://git@github.com/Acme/Project.git']) {
 test(`HD2: different-folder workspace collision uses owner/repo from ${origin}`,async t=>{
  const f=await fixture(t),sourceRoot=join(f.root,'local-checkout'),otherFolder=join(f.root,'different-folder');
  await mkdir(sourceRoot);await mkdir(otherFolder);
  const execute=promisify(execFile),git=(...args)=>execute('git',args,{cwd:sourceRoot});
  await git('init','-b','main');
  await git('-c','user.name=Layout test','-c','user.email=test@example.invalid','commit','--allow-empty','-m','Base');
  await git('remote','add','origin',origin);
  const existing={workspace_id:'personal',label:'Project',
   worktree:{checkout_path:otherFolder,repo_key:join(otherFolder,'.git'),is_linked_worktree:false}};
  f.workspaces.push(structuredClone(existing));
  // The real allocator checks origin and creates the real assigned Git worktree.
  // Only the external Herdr transport is captured; no fake setup or runner.
  const allocated=await allocateIssueWorktree({cwd:sourceRoot,repository:'Acme/Project',
   issueNumber:2,runId:f.input.runId,workflowName:'small-change',baseRef:'main'});
  assert.equal(allocated.state,'ready',allocated.message);
  const a=allocated.assignment;
  const layout=await f.open({repository:a.repository,sourceRoot:a.sourceRoot,commonDir:a.commonDir,cwd:a.worktreePath});
  assert.equal(f.workspaces.find(w=>w.workspace_id===layout.repoWorkspaceId).label,'Acme/Project');
  assert.deepEqual(f.workspaces.find(w=>w.workspace_id==='personal'),existing);
  assert(!f.calls.some(args=>args[0]==='workspace'&&['rename','close'].includes(args[1])));
  const again=await f.open({repository:a.repository,sourceRoot:a.sourceRoot,commonDir:a.commonDir,cwd:a.worktreePath,stageId:'change'});
  assert.equal(again.repoWorkspaceId,layout.repoWorkspaceId);
  assert.equal(f.calls.filter(args=>args[0]==='workspace'&&args[1]==='create').length,1);
  const foreign=await allocateIssueWorktree({cwd:sourceRoot,repository:'WrongOwner/Project',
   issueNumber:3,runId:randomUUID(),workflowName:'small-change',baseRef:'main'});
  assert.notEqual(foreign.state,'ready','a supplied owner cannot override origin identity');
 });
}
test('HD2: an occupied owner/repo label refuses without adopting or renaming another folder',async t=>{
 const f=await fixture(t),other=join(f.root,'another-folder');await mkdir(other);
 f.workspaces.push({workspace_id:'short',label:'coffee',worktree:{checkout_path:other}},
  {workspace_id:'qualified',label:'alice/coffee',worktree:{checkout_path:other}});
 const before=structuredClone(f.workspaces);
 await assert.rejects(f.open(),/repository_label_unavailable/);
 assert.deepEqual(f.workspaces,before);
 assert(f.calls.every(args=>args[0]==='workspace'&&args[1]==='list'));
});
test('the repository workspace closes only when no run of it is open and it holds just its one shell',async t=>{
 const f=await fixture(t),layout=await f.open(),idle=()=>f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir:f.input.commonDir},f.ports),f.ports);
 assert.equal(await idle(),false,'a run is still open');
 await f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRunLayout({...f.input,layout},f.ports),f.ports);
 const command=f.ports.command;
 f.ports.command=async args=>{const reply=await command(args);if(args[0]==='tab'&&args[1]==='list'&&args[3]===layout.repoWorkspaceId)reply.result.tabs.push({tab_id:'person-tab'});return reply;};
 assert.equal(await idle(),false,'the person opened another tab there');assert.deepEqual(f.workspaces.map(w=>w.label),['coffee']);
 f.ports.command=command;
 assert.equal(await idle(),true);assert.deepEqual(f.workspaces,[]);
 assert.equal(await idle(),false,'nothing left to close');
});

test('2531: a pinned parent without Git metadata supports safe reuse and idle cleanup',async t=>{
 const f=await fixture(t),layout=await f.open();
 f.workspaces.find(w=>w.workspace_id===layout.repoWorkspaceId).worktree=null;
 // Pane cwd remains the pinned parent even before Herdr has populated worktree metadata.
 const original=f.ports.command;f.ports.command=async args=>{
  const reply=await original(args);
  if(args[0]==='pane'&&args[1]==='list'&&args[3]===layout.repoWorkspaceId)reply.result.panes[0].cwd=f.input.sourceRoot;
  return reply;
 };
 await f.open({stageId:'change'});
 await f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRunLayout({...f.input,layout},f.ports),f.ports);
 const closed=await f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir:f.input.commonDir},f.ports),f.ports);
 assert.equal(closed,true);assert.deepEqual(f.workspaces,[]);
});

test('2531: a pinned null-metadata parent can be qualified on a repository-name clash',async t=>{
 const f=await fixture(t),layout=await f.open(),other=join(f.root,'other-repo');await mkdir(other);await f.init(other,'bob/coffee');
 f.workspaces.find(w=>w.workspace_id===layout.repoWorkspaceId).worktree=null;
 const original=f.ports.command;f.ports.command=async args=>{
  const reply=await original(args);if(args[0]==='pane'&&args[1]==='list'&&args[3]===layout.repoWorkspaceId)reply.result.panes[0].cwd=f.input.sourceRoot;
  return reply;
 };
 await f.open({runId:randomUUID(),repository:'bob/coffee',sourceRoot:other,commonDir:join(other,'.git'),cwd:other});
 assert.equal(f.workspaces.find(w=>w.workspace_id===layout.repoWorkspaceId).label,'alice/coffee');
});

test('2531: missing parent Git metadata never permits changed root identities',async t=>{
 for(const kind of ['terminal','cwd','tab','pane','linked-metadata']){
  const f=await fixture(t),layout=await f.open(),row=f.workspaces.find(w=>w.workspace_id===layout.repoWorkspaceId);
  if(kind==='linked-metadata')row.worktree.is_linked_worktree=true;else row.worktree=null;
  const original=f.ports.command;f.ports.command=async args=>{
   const reply=await original(args);
   if(args[3]===layout.repoWorkspaceId&&args[0]==='pane'&&args[1]==='list'){
    reply.result.panes[0].cwd=kind==='cwd'?f.input.cwd:f.input.sourceRoot;
    if(kind==='terminal')reply.result.panes[0].terminal_id='replacement';
    if(kind==='pane')reply.result.panes.push({...reply.result.panes[0],pane_id:'unknown'});
   }
   if(kind==='tab'&&args[0]==='tab'&&args[1]==='list'&&args[3]===layout.repoWorkspaceId)reply.result.tabs.push({tab_id:'unknown'});
   return reply;
  };
  await assert.rejects(f.open({stageId:'change'}),/herdr_layout_identity_changed|run_has_open_tabs/,kind);
 }
});

// A shared Herdr session can already contain a workflow from another clone of
// this exact origin. IDs and Git common directories must stay checkout-scoped.
test('2615: independent clones start, reopen and cancel without rebinding peer workspaces', async t => {
 const f=await fixture(t),first=await f.open(),original=structuredClone(f.workspaces);
 const secondSource=join(f.root,'second-clone'),secondCwd=join(f.root,'second-run');
 await mkdir(secondSource);await mkdir(secondCwd);await f.init(secondSource,'alice/coffee');
 const second={runId:randomUUID(),sourceRoot:secondSource,commonDir:join(secondSource,'.git'),cwd:secondCwd};
 let layout;
 await assert.doesNotReject(async()=>{layout=await f.open(second);},'another clone must not be mistaken for changed ownership');
 assert.notEqual(layout.repoWorkspaceId,first.repoWorkspaceId);
 assert.deepEqual(f.workspaces.slice(0,original.length),original,'peer labels and Git identities stay unchanged');
 assert.equal(f.workspaces.find(w=>w.workspace_id===layout.repoWorkspaceId).label,'alice/coffee');
 assert.equal(f.workspaces.find(w=>w.workspace_id===layout.workspaceId).worktree.repo_key,second.commonDir);
 const reopened=await f.open({...second,stageId:'change'});
 assert.equal(reopened.workspaceId,layout.workspaceId);assert.notEqual(reopened.tabId,layout.tabId);
 const thirdSource=join(f.root,'third-clone'),thirdCwd=join(f.root,'third-run');
 await mkdir(thirdSource);await mkdir(thirdCwd);await f.init(thirdSource,'alice/coffee');
 const third={runId:randomUUID(),sourceRoot:thirdSource,commonDir:join(thirdSource,'.git'),cwd:thirdCwd};
 const thirdLayout=await f.open(third);
 const thirdLabel=f.workspaces.find(w=>w.workspace_id===thirdLayout.repoWorkspaceId).label;
 assert(thirdLabel.startsWith('alice/coffee@'));
 assert(!original.some(w=>w.label===thirdLabel));
 assert.notEqual(thirdLabel,'alice/coffee');
 await f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRunLayout({...f.input,...second,layout},f.ports),f.ports);
 assert.equal(await f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir:second.commonDir},f.ports),true);
 assert(!f.workspaces.some(w=>w.workspace_id===layout.repoWorkspaceId));
 assert.deepEqual(f.workspaces.slice(0,original.length),original);
 assert(f.workspaces.some(w=>w.workspace_id===thirdLayout.repoWorkspaceId));
 const restart={...second,runId:randomUUID()},restarted=await f.open(restart);
 assert.notEqual(restarted.workspaceId,layout.workspaceId);
 assert.equal((await f.open({...restart,stageId:'change'})).workspaceId,restarted.workspaceId);
 const peer=f.workspaces.find(w=>w.workspace_id===first.workspaceId);peer.worktree.checkout_path='/changed';
 await assert.rejects(f.open(),/herdr_layout_identity_changed/,'multiple checkouts must not weaken identity checks');
 assert(!f.calls.some(args=>args[0]==='workspace'&&args[1]==='rename'));
});

test('2615: a hand-edited repeated repository key selects the matching clone and refuses ambiguity', async t => {
 const f=await fixture(t),first=await f.open();
 const sourceRoot=join(f.root,'legacy-clone'),cwd=join(f.root,'legacy-run');
 await mkdir(sourceRoot);await mkdir(cwd);await f.init(sourceRoot,'alice/coffee');
 const commonDir=join(sourceRoot,'.git');
 const made=await f.ports.command(['workspace','create','--cwd',sourceRoot,'--label','alice/coffee','--no-focus']);
 const {readFile,writeFile}=await import('node:fs/promises'),file=join(f.ports.directory,'registry.json');
 const registry=JSON.parse(await readFile(file,'utf8'));
 registry.repositories.push({key:'alice/coffee',repository:'alice/coffee',sourceRoot,commonDir,phase:'ready',
  workspaceId:made.result.workspace.workspace_id,rootTabId:made.result.tab.tab_id,
  rootPaneId:made.result.root_pane.pane_id,rootTerminalId:made.result.root_pane.terminal_id});
 await writeFile(file,JSON.stringify(registry));
 const input={runId:randomUUID(),sourceRoot,commonDir,cwd};let layout;
 await assert.doesNotReject(async()=>{layout=await f.open(input);},'find the matching clone even when its repository key repeats');
 assert.equal(layout.repoWorkspaceId,made.result.workspace.workspace_id);
 assert.notEqual(layout.repoWorkspaceId,first.repoWorkspaceId);
 assert.equal(f.calls.filter(args=>args[0]==='workspace'&&args[1]==='create').length,2,'reuse the matching parent');
 const updated=JSON.parse(await readFile(file,'utf8'));
 updated.repositories.push({...updated.repositories.at(-1),workspaceId:'ambiguous-parent'});
 await writeFile(file,JSON.stringify(updated));
 const mutations=f.calls.filter(args=>['create','open','rename','close'].includes(args[1])).length;
 await assert.rejects(f.open({...input,stageId:'change'}),/layout_allocation_uncertain/);
 await assert.rejects(f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir},f.ports),/layout_allocation_uncertain/);
 assert.equal(f.calls.filter(args=>['create','open','rename','close'].includes(args[1])).length,mutations);
});


test('2615: a new clone uses the free short label despite a closed peer workspace in the registry', async t => {
 const f=await fixture(t),first=await f.open();
 f.workspaces.splice(f.workspaces.findIndex(w=>w.workspace_id===first.repoWorkspaceId),1);
 const peers=structuredClone(f.workspaces),sourceRoot=join(f.root,'fresh-clone'),cwd=join(f.root,'fresh-run');
 await mkdir(sourceRoot);await mkdir(cwd);await f.init(sourceRoot,'alice/coffee');
 const next=await f.open({runId:randomUUID(),sourceRoot,commonDir:join(sourceRoot,'.git'),cwd});
 assert.equal(f.workspaces.find(w=>w.workspace_id===next.repoWorkspaceId).label,'coffee');
 assert.deepEqual(f.workspaces.slice(0,peers.length),peers);
 assert(!f.calls.some(args=>args[0]==='workspace'&&args[1]==='rename'));
});

test('2615: canceling the short-label clone makes that label available while another clone stays open', async t => {
 const f=await fixture(t),first=await f.open(),sourceRoot=join(f.root,'peer'),cwd=join(f.root,'peer-run');
 await mkdir(sourceRoot);await mkdir(cwd);await f.init(sourceRoot,'alice/coffee');
 const peer=await f.open({runId:randomUUID(),sourceRoot,commonDir:join(sourceRoot,'.git'),cwd});
 await f.module.withHerdrLayoutLock(async()=>{
  await f.module.closeHerdrRunLayout({...f.input,layout:first},f.ports);
  assert.equal(await f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir:f.input.commonDir},f.ports),true);
 },f.ports);
 const peerRows=structuredClone(f.workspaces),newCwd=join(f.root,'restart');await mkdir(newCwd);
 const restarted=await f.open({runId:randomUUID(),cwd:newCwd});
 assert.equal(f.workspaces.find(w=>w.workspace_id===restarted.repoWorkspaceId).label,'coffee');
 assert.deepEqual(f.workspaces.slice(0,peerRows.length),peerRows);
 assert(f.workspaces.some(w=>w.workspace_id===peer.repoWorkspaceId));
});

for(const holder of ['free owner/repo label','unrelated workspace']) {
 test(`2615: different-repository qualification preserves stable peer labels with ${holder}`, async t => {
  const f=await fixture(t),first=await f.open();
  const clone=async name=>{
   const sourceRoot=join(f.root,name),cwd=join(f.root,name+'-run');
   await mkdir(sourceRoot);await mkdir(cwd);await f.init(sourceRoot,'alice/coffee');
   const input={runId:randomUUID(),sourceRoot,commonDir:join(sourceRoot,'.git'),cwd};
   return {input,layout:await f.open(input)};
  };
  const second=await clone('second'),third=await clone('third');
  const stable=f.workspaces.find(w=>w.workspace_id===third.layout.repoWorkspaceId).label;
  assert(stable.startsWith('alice/coffee@'));
  // Leave two active alice/coffee clones: the short name and a stable qualified name.
  await f.module.withHerdrLayoutLock(async()=>{
   await f.module.closeHerdrRunLayout({...f.input,...second.input,layout:second.layout},f.ports);
   assert.equal(await f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir:second.input.commonDir},f.ports),true);
  },f.ports);
  let unrelated;
  if(holder==='unrelated workspace') {
   unrelated={workspace_id:'personal',label:'alice/coffee',worktree:{checkout_path:'/personal'}};
   f.workspaces.push(structuredClone(unrelated));
  }
  const before=f.calls.length,sourceRoot=join(f.root,'bob'),cwd=join(f.root,'bob-run');
  await mkdir(sourceRoot);await mkdir(cwd);await f.init(sourceRoot,'bob/coffee');
  const bob=await f.open({runId:randomUUID(),repository:'bob/coffee',sourceRoot,commonDir:join(sourceRoot,'.git'),cwd});
  const label=f.workspaces.find(w=>w.workspace_id===first.repoWorkspaceId).label;
  if(unrelated) {
   assert(label.startsWith('alice/coffee@'));assert.notEqual(label,stable);
   assert.deepEqual(f.workspaces.find(w=>w.workspace_id===unrelated.workspace_id),unrelated);
  } else assert.equal(label,'alice/coffee');
  assert.equal(f.workspaces.find(w=>w.workspace_id===third.layout.repoWorkspaceId).label,stable,'qualification uses the common directory and does not replace a stable peer label');
  assert.equal(f.workspaces.find(w=>w.workspace_id===bob.repoWorkspaceId).label,'bob/coffee');
  assert.deepEqual(f.calls.slice(before).filter(args=>args[0]==='workspace'&&args[1]==='rename'),
   [['workspace','rename',first.repoWorkspaceId,label]],'only the short-label owned workspace needs a rename');
 });
}
