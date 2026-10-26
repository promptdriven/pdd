import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, rm, mkdir, stat } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { randomUUID } from 'node:crypto';
import { runHerdrStage } from '../src/workflow-stage-herdr.mjs';

// The production adapter chooses the target; only the subprocess boundary is captured.
test('new production stage selects shared pdd, never a run hash or default', async t => {
 const cwd=await mkdtemp(join(tmpdir(),'pdd-layout-repro-'));t.after(()=>rm(cwd,{recursive:true,force:true}));const calls=[];
 await runHerdrStage({runId:randomUUID(),attemptId:randomUUID(),stageId:'scope',agent:'codex',cwd,
 repository:'Serhan-Asad/harbor-coffee',sourceRoot:cwd,commonDir:join(cwd,'.git'),issueNumber:2,workflowName:'small-change',
 context:'Guide',instructions:'Scope',checkpoint:async()=>{}},{layoutDirectory:join(cwd,'state'),withStageGuard:async(_b,fn)=>fn(),
 execFile:async(_exe,args)=>{calls.push(args);throw Object.assign(Error('stop after target'),{code:'STOP'});}});
 assert.equal(calls[0][1],'pdd');
});
async function fixture(t){
 const root=await mkdtemp(join(tmpdir(),'pdd-layout-'));t.after(()=>rm(root,{recursive:true,force:true}));
 const sourceRoot=join(root,'coffee'),cwd=join(root,'run');await mkdir(sourceRoot);await mkdir(cwd);
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
 return {module,root,input,ports,calls,workspaces,open};
}
test('repository reuse, one worktree per run, issue/workflow label and stage tabs',async t=>{
 const f=await fixture(t),a=await f.open(),b=await f.open({stageId:'change'});
 assert.equal(a.repoWorkspaceId,b.repoWorkspaceId);assert.equal(a.workspaceId,b.workspaceId);assert.notEqual(a.tabId,b.tabId);
 assert.deepEqual(f.workspaces.map(w=>w.label),['coffee','#2 small-change']);
 assert.deepEqual(f.calls.find(a=>a[0]==='worktree'),['worktree','open','--workspace',a.repoWorkspaceId,'--path',f.input.cwd,'--label','#2 small-change','--no-focus']);
 assert.equal(f.calls.filter(a=>a[0]==='worktree').length,1);
 assert(f.calls.filter(c=>c[0]==='tab').every(c=>c[c.indexOf('--workspace')+1]===a.workspaceId));
});
test('concurrent runs share repository but have separate worktree workspaces',async t=>{
 const f=await fixture(t),cwd=join(f.root,'run2');await mkdir(cwd);
 const [a,b]=await Promise.all([f.open(),f.open({runId:randomUUID(),cwd,issueNumber:3})]);
 assert.equal(a.repoWorkspaceId,b.repoWorkspaceId);assert.notEqual(a.workspaceId,b.workspaceId);
 assert.deepEqual(f.workspaces.map(w=>w.label),['coffee','#2 small-change','#3 small-change']);
});
test('repo-name clash qualifies both owned labels and preserves existing run',async t=>{
 const f=await fixture(t),a=await f.open(),other=join(f.root,'other');await mkdir(other);
 await f.open({runId:randomUUID(),repository:'bob/coffee',sourceRoot:other,commonDir:join(other,'.git'),cwd:other});
 assert.deepEqual(f.workspaces.map(w=>w.label),['alice/coffee','#2 small-change','bob/coffee','#2 small-change']);assert.equal(f.workspaces[1].workspace_id,a.workspaceId);
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
 const script=`import {withHerdrLayoutLock} from ${JSON.stringify(new URL('../src/workflow-herdr-layout.mjs',import.meta.url).href)};process.on('SIGINT',()=>process.exit(130));await withHerdrLayoutLock(async()=>{console.log('LOCKED');await new Promise(()=>{setInterval(()=>{},1000);});},{directory:${JSON.stringify(f.ports.directory)}});`;
 const child=spawn(process.execPath,['--input-type=module','-e',script],{stdio:['ignore','pipe','pipe']});
 t.after(()=>child.kill('SIGKILL'));
 const ready=new Promise(resolve=>child.stdout.once('data',resolve));const ended=new Promise(resolve=>child.once('exit',resolve));
 await ready;child.kill('SIGINT');assert.equal(await ended,130);
 let acquired=false;await f.module.withHerdrLayoutLock(()=>{acquired=true;},f.ports);assert.equal(acquired,true);
});
