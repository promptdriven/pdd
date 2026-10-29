import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, rm, mkdir, stat, realpath, readFile, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { randomUUID, createHash } from 'node:crypto';
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
 return {module,root,input,ports,calls,workspaces,open,init,git};
}

// Native replay of the approved Story's case plans. There is no Runtime JSON
// for this native owner: these assertions are ordinary public-API evidence.
const registry=async f=>JSON.parse(await readFile(join(f.ports.directory,'registry.json'),'utf8'));
const save=async(f,value)=>writeFile(join(f.ports.directory,'registry.json'),JSON.stringify(value)+'\n');
const mutations=f=>f.calls.filter(a=>['create','open','rename','close'].includes(a[1]));
const token=path=>createHash('sha256').update(path,'utf8').digest('hex').slice(0,12);
async function second(f,repository='alice/coffee') {
 const sourceRoot=join(f.root,'second');await mkdir(sourceRoot);await f.init(sourceRoot,repository);
 const cwd=join(f.root,'second-run');await mkdir(cwd);
 return {...f.input,sourceRoot,commonDir:join(sourceRoot,'.git'),cwd,repository,runId:randomUUID()};
}
async function pair(t) {
 const f=await fixture(t),a=await f.open(),bInput=await second(f);
 const before=await registry(f),peerWorld=structuredClone(f.workspaces);
 // Version 1, no schema rewrite: the first row is precisely legacy clone A.
 assert.equal(before.version,1);
 let b;await assert.doesNotReject(async()=>{b=await f.open(bInput);},'a separately verified checkout must allocate its own layout');
 assert.deepEqual((await registry(f)).repositories[0],before.repositories[0]);
 assert.deepEqual((await registry(f)).runs[0],before.runs[0]);
 assert.deepEqual(f.workspaces.slice(0,2),peerWorld);
 return {f,a,b,bInput};
}
const idle=(f,input)=>f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRepoLayoutIfIdle(input,f.ports),f.ports);
const close=(f,input,layout)=>f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRunLayout({...input,layout},f.ports),f.ports);

test('2531B AC1,2,6: legacy A first, independent B allocation, stable digest, and exact pair reuse',async t=>{
 const {f,a,b,bInput}=await pair(t);
 assert.notEqual(a.repoWorkspaceId,b.repoWorkspaceId);assert.notEqual(a.workspaceId,b.workspaceId);
 assert.equal(f.workspaces.find(w=>w.workspace_id===b.repoWorkspaceId).label,`alice/coffee@${token(bInput.commonDir)}`);
 assert.deepEqual(f.calls.filter(a=>a[0]==='workspace'&&a[1]==='create').map(a=>a.slice(2)),[
  ['--cwd',f.input.sourceRoot,'--label','coffee','--no-focus'],
  ['--cwd',bInput.sourceRoot,'--label',`alice/coffee@${token(bInput.commonDir)}`,'--no-focus']]);
 const saved=await registry(f),world=structuredClone(f.workspaces);f.calls.length=0;
 assert.equal((await f.open({stageId:'next'})).repoWorkspaceId,a.repoWorkspaceId);
 assert.equal((await f.open({...bInput,repository:'ALICE/coffee',stageId:'next'})).repoWorkspaceId,b.repoWorkspaceId);
 assert.deepEqual(await registry(f),saved);assert.deepEqual(f.workspaces,world);
 assert.deepEqual(mutations(f).map(a=>a.slice(0,2)),[['tab','create'],['tab','create']]);
});

for(const kind of ['linked','bare'])test(`2531B AC2: ${kind} caller uses its verified parent in the same namespace`,async t=>{
 const f=await fixture(t);let primary=f.input.sourceRoot;
 if(kind==='bare'){
  primary=join(f.root,'primary.git');await f.git(f.root,'clone','--bare',f.input.sourceRoot,primary);
  await f.git(primary,'remote','set-url','origin','https://github.com/alice/coffee.git');
 }
 const linked=join(f.root,'linked');await f.git(primary,'worktree','add','-b','linked',linked);
 const commonDir=kind==='bare'?primary:f.input.commonDir;
 const original=f.ports.command;
 f.ports.command=async args=>{const reply=await original(args);if(args[0]==='workspace'&&args[1]==='create'){
  f.workspaces.find(w=>w.workspace_id===reply.result.workspace.workspace_id).worktree.repo_key=commonDir;
 }return reply;};
 const a=await f.open({sourceRoot:linked,commonDir});
 assert.equal(f.calls.find(a=>a[0]==='workspace'&&a[1]==='create')[3],primary);
 const b=await f.open({sourceRoot:kind==='bare'?linked:primary,commonDir,stageId:'again'});
 assert.equal(b.repoWorkspaceId,a.repoWorkspaceId);
 assert.equal(f.calls.filter(a=>a[0]==='workspace'&&a[1]==='create').length,1);
});

for(const target of ['A','B'])test(`2531B AC5: cleanup ${target} selects the exact pair and preserves the active peer`,async t=>{
 const {f,a,b,bInput}=await pair(t),input=target==='A'?f.input:bInput,layout=target==='A'?a:b,peer=target==='A'?b:a;
 const saved=await registry(f),peerRepo=saved.repositories.find(r=>r.workspaceId===peer.repoWorkspaceId),peerRun=saved.runs.find(r=>r.workspaceId===peer.workspaceId);
 const world=f.workspaces.filter(w=>[peer.repoWorkspaceId,peer.workspaceId].includes(w.workspace_id));f.calls.length=0;
 await close(f,input,layout);assert.equal(await idle(f,input),true);
 assert.deepEqual(f.calls.filter(a=>a[1]==='close'),[['workspace','close',layout.workspaceId],['workspace','close',layout.repoWorkspaceId]]);
 const after=await registry(f);assert.deepEqual(after.repositories,[peerRepo]);assert.deepEqual(after.runs.find(r=>r.workspaceId===peer.workspaceId),peerRun);
 assert.deepEqual(f.workspaces,world);
});

for(const field of ['commonDir','cwd','repoWorkspaceId','label','missing-namespace'])test(`2531B AC3: saved ${field} refuses before allocation or rebinding`,async t=>{
 const {f,bInput}=await pair(t),state=await registry(f),saved=state.runs[1];
 if(field==='missing-namespace')state.repositories=state.repositories.filter(r=>r.commonDir!==bInput.commonDir);
 else saved[field]=field==='cwd'?f.input.cwd:field==='commonDir'?f.input.commonDir:'changed';
 await save(f,state);const bytes=await readFile(join(f.ports.directory,'registry.json'),'utf8'),world=structuredClone(f.workspaces);f.calls.length=0;
 await assert.rejects(f.open(bInput),{code:'herdr_run_binding_changed'});
 assert.deepEqual(mutations(f),[]);assert.equal(await readFile(join(f.ports.directory,'registry.json'),'utf8'),bytes);assert.deepEqual(f.workspaces,world);
});
test('2531B AC3: legacy run label remains reusable',async t=>{
 const f=await fixture(t),a=await f.open(),state=await registry(f);state.runs[0].label='#2 small-change';await save(f,state);f.calls.length=0;
 assert.equal((await f.open()).workspaceId,a.workspaceId);assert.deepEqual(mutations(f).map(a=>a.slice(0,2)),[['tab','create']]);
});

for(const kind of ['parent-intent','run-intent','parent-lost','run-lost'])test(`2531B AC3,4: ${kind} cannot duplicate allocation on explicit retry`,async t=>{
 const f=await fixture(t);await f.open();const bInput=await second(f),original=f.ports.command;
 if(kind.endsWith('lost'))f.ports.command=async args=>{const reply=await original(args);if(args[0]===(kind==='parent-lost'?'workspace':'worktree')&&args[1]===(kind==='parent-lost'?'create':'open'))throw Error('reply lost');return reply;};
 if(kind.endsWith('intent')){
  const state=await registry(f);
  if(kind==='parent-intent')state.repositories.push({key:'alice/coffee',repository:'alice/coffee',sourceRoot:bInput.sourceRoot,commonDir:bInput.commonDir,phase:'intent'});
  else {const b=await f.open(bInput),ready=await registry(f);ready.runs.find(r=>r.runId===bInput.runId).phase='intent';await save(f,ready);}
  if(kind==='parent-intent')await save(f,state);
 }else await assert.rejects(f.open(bInput),/reply lost/);
 f.ports.command=original;const count=mutations(f).length,bytes=await readFile(join(f.ports.directory,'registry.json'),'utf8');
 await assert.rejects(f.open(bInput),{code:'layout_allocation_uncertain'});
 assert.equal(mutations(f).length,count);assert.equal(await readFile(join(f.ports.directory,'registry.json'),'utf8'),bytes);
});

test('2531B AC3,4: confirmed refusal permits one explicit retry; lost retry ignores stale evidence',async t=>{
 const f=await fixture(t),original=f.ports.command;let refuse=true;
 f.ports.command=async args=>{if(args[0]==='worktree'&&refuse){f.calls.push(args);refuse=false;throw Object.assign(Error('refused'),{code:'linked_worktree_source'});}return original(args);};
 await assert.rejects(f.open(),{code:'linked_worktree_source'});
 assert.equal((await registry(f)).runs[0].phase,'refused');
 f.ports.command=async args=>{const reply=await original(args);if(args[0]==='worktree')throw Error('retry lost');return reply;};
 await assert.rejects(f.open(),/retry lost/);f.ports.command=original;
 const before=mutations(f).length;
 await assert.rejects(f.open({preAgentRefusal:'linked_worktree_source'}),{code:'layout_allocation_uncertain'});
 assert.equal(mutations(f).length,before);assert.equal(f.calls.filter(a=>a[0]==='worktree').length,2);
});

for(const kind of ['duplicate','occupied','parent-path','parent-metadata','run-cwd','run-common','run-root','inventory'])test(`2531B AC4: ${kind} refuses without peer mutation or adoption`,async t=>{
 const {f,b,bInput}=await pair(t),state=await registry(f);
 if(kind==='duplicate')state.repositories.push(structuredClone(state.repositories[1]));
 if(kind==='occupied'){
  state.repositories.pop();state.runs.pop();f.workspaces.splice(2);
  f.workspaces.push({workspace_id:'stranger',label:`alice/coffee@${token(bInput.commonDir)}`});
 }
 if(kind==='parent-path')state.repositories[1].sourceRoot=f.input.sourceRoot;
 if(kind==='parent-metadata')f.workspaces.find(w=>w.workspace_id===b.repoWorkspaceId).worktree.repo_key=f.input.commonDir;
 if(kind==='run-cwd')f.workspaces.find(w=>w.workspace_id===b.workspaceId).worktree.checkout_path=f.input.cwd;
 if(kind==='run-common')f.workspaces.find(w=>w.workspace_id===b.workspaceId).worktree.repo_key=f.input.commonDir;
 await save(f,state);const original=f.ports.command;
 f.ports.command=async args=>{const reply=await original(args);if(kind==='run-root'&&args[0]==='pane'&&args[3]===b.workspaceId)reply.result.panes[0].terminal_id='forged';if(kind==='inventory'&&args[0]==='workspace'&&args[1]==='list')reply.result.workspaces.push(reply.result.workspaces[0]);return reply;};
 const world=structuredClone(f.workspaces),bytes=await readFile(join(f.ports.directory,'registry.json'),'utf8');f.calls.length=0;
 await assert.rejects(f.open(bInput),{code:kind==='duplicate'?'invalid_layout_registry':kind==='occupied'?'repository_label_unavailable':kind==='inventory'?'invalid_workspace_inventory':'herdr_layout_identity_changed'});
 assert.deepEqual(mutations(f),[]);assert.deepEqual(f.workspaces,world);assert.equal(await readFile(join(f.ports.directory,'registry.json'),'utf8'),bytes);
});

for(const kind of ['tab','pane','identity','lost-close'])test(`2531B AC5: parent ${kind} prevents unsafe cleanup or repeated close`,async t=>{
 const {f,b,bInput}=await pair(t);await close(f,bInput,b);const original=f.ports.command;
 f.ports.command=async args=>{const reply=await original(args);if(args[3]===b.repoWorkspaceId){if(kind==='tab'&&args[0]==='tab')reply.result.tabs.push({tab_id:'personal'});if(kind==='pane'&&args[0]==='pane')reply.result.panes.push({pane_id:'personal'});}
 if(kind==='lost-close'&&args[0]==='workspace'&&args[1]==='close')throw Error('close lost');return reply;};
 if(kind==='identity')f.workspaces.find(w=>w.workspace_id===b.repoWorkspaceId).worktree.repo_key='/forged';
 f.calls.length=0;
 if(kind==='lost-close'){
  await assert.rejects(idle(f,bInput),/close lost/);assert.equal(await idle(f,bInput),false);assert.equal(f.calls.filter(a=>a[1]==='close').length,1);
 }else if(kind==='identity')await assert.rejects(idle(f,bInput),{code:'herdr_layout_identity_changed'});
 else assert.equal(await idle(f,bInput),false);
 assert.equal((await registry(f)).repositories.length,2);assert(f.workspaces.some(w=>w.worktree?.checkout_path===f.input.sourceRoot));
 if(kind!=='lost-close')assert.deepEqual(mutations(f),[]);
});

test('2531B AC6: mixed legacy A short, B hash, and C other origin only qualify the owned short label',async t=>{
 const {f,a,b,bInput}=await pair(t),before=await registry(f),bWorld=structuredClone(f.workspaces.filter(w=>[b.repoWorkspaceId,b.workspaceId].includes(w.workspace_id)));
 const cRoot=join(f.root,'third');await mkdir(cRoot);await f.init(cRoot,'bob/coffee');f.calls.length=0;
 await f.open({repository:'bob/coffee',sourceRoot:cRoot,commonDir:join(cRoot,'.git'),cwd:cRoot,runId:randomUUID()});
 assert.deepEqual(f.calls.filter(a=>a[1]==='rename'),[['workspace','rename',a.repoWorkspaceId,'alice/coffee']]);
 assert.equal(f.workspaces.find(w=>w.workspace_id===b.repoWorkspaceId).label,`alice/coffee@${token(bInput.commonDir)}`);
 assert.deepEqual(f.workspaces.filter(w=>[b.repoWorkspaceId,b.workspaceId].includes(w.workspace_id)),bWorld);
 const after=await registry(f);assert.deepEqual(after.repositories.slice(0,2),before.repositories);assert.deepEqual(after.runs.slice(0,2),before.runs);
});

test('2531B AC4,5: duplicate or inconsistent selected ownership cannot authorize cleanup or allocation',async t=>{
 for(const kind of ['duplicate','inconsistent']){
  const {f,b,bInput}=await pair(t),state=await registry(f);
  if(kind==='duplicate')state.repositories.push(structuredClone(state.repositories[1]));
  else state.repositories[1].repository='someone/else';
  await save(f,state);const world=structuredClone(f.workspaces);f.calls.length=0;
  await assert.rejects(f.open(bInput),{code:'invalid_layout_registry'});
  await assert.rejects(idle(f,bInput),{code:'invalid_layout_registry'});
  assert.deepEqual(mutations(f),[]);assert.deepEqual(f.workspaces,world);
 }
});
