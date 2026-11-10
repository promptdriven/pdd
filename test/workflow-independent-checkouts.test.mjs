import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdir, readFile, writeFile} from 'node:fs/promises';
import {join} from 'node:path';
import {randomUUID, createHash} from 'node:crypto';
import {fixture} from './helpers/herdr-layout-fixture.mjs';

const mutations = f => f.calls.filter(a => ['create','open','rename','close','remove'].includes(a[1]));
const token = path => createHash('sha256').update(path).digest('hex').slice(0,12);
async function second(f, repository = 'alice/coffee') {
 const sourceRoot=join(f.root,'second');await mkdir(sourceRoot);await f.init(sourceRoot,repository);
 const cwd=join(f.root,'second-run');await mkdir(cwd);
 return {...f.input,sourceRoot,commonDir:join(sourceRoot,'.git'),cwd,repository,runId:randomUUID()};
}
async function pair(t) {
 const f=await fixture(t),a=await f.open(),bInput=await second(f),peer=structuredClone(f.workspaces);
 const b=await f.open(bInput);assert.deepEqual(f.workspaces.slice(0,2),peer);
 return {f,a,b,bInput};
}
const idle = (f,input) => f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRepoLayoutIfIdle(input,f.ports),f.ports);
const close = (f,input,layout) => f.module.withHerdrLayoutLock(()=>f.close({...input,layout},f.ports),f.ports);

test('independent clones allocate and reuse exact live pairs without changing peer labels',async t=>{
 const {f,a,b,bInput}=await pair(t);
 assert.notEqual(a.repoWorkspaceId,b.repoWorkspaceId);assert.notEqual(a.workspaceId,b.workspaceId);
 assert.equal(f.workspaces.find(w=>w.workspace_id===b.repoWorkspaceId).label,'alice/coffee');
 assert.deepEqual(f.calls.filter(a=>a[0]==='workspace'&&a[1]==='create').map(a=>a.slice(2)),[
  ['--cwd',f.input.sourceRoot,'--label','coffee','--no-focus'],['--cwd',bInput.sourceRoot,'--label','alice/coffee','--no-focus']]);
 const world=structuredClone(f.workspaces);f.calls.length=0;
 assert.equal((await f.open({stageId:'next'})).repoWorkspaceId,a.repoWorkspaceId);
 assert.equal((await f.open({...bInput,repository:'ALICE/coffee',stageId:'next'})).repoWorkspaceId,b.repoWorkspaceId);
 assert.deepEqual(f.workspaces,world);
 assert.deepEqual(mutations(f).map(a=>a.slice(0,2)),[['tab','create'],['tab','create']]);
});
for(const kind of ['linked','bare'])test(`${kind} caller uses the verified clone parent`,async t=>{
 const f=await fixture(t);let primary=f.input.sourceRoot;
 if(kind==='bare'){
  primary=join(f.root,'primary.git');await f.git(f.root,'clone','--bare',f.input.sourceRoot,primary);
  await f.git(primary,'remote','set-url','origin','https://github.com/alice/coffee.git');
 }
 const linked=join(f.root,'linked');await f.git(primary,'worktree','add','-b','linked',linked);
 const commonDir=kind==='bare'?primary:f.input.commonDir,cwd=kind==='bare'?linked:f.input.cwd;
 const a=await f.open({sourceRoot:linked,commonDir,cwd});
 assert.equal(f.calls.find(a=>a[0]==='workspace'&&a[1]==='create')[3],primary);
 const b=await f.open({sourceRoot:kind==='bare'?linked:primary,commonDir,cwd,stageId:'again'});
 assert.equal(b.repoWorkspaceId,a.repoWorkspaceId);
 assert.equal(f.calls.filter(a=>a[0]==='workspace'&&a[1]==='create').length,1);
});
for(const target of ['A','B'])test(`cleanup ${target} closes the exact run and preserves peer and parent`,async t=>{
 const {f,a,b,bInput}=await pair(t),input=target==='A'?f.input:bInput,layout=target==='A'?a:b,peer=target==='A'?b:a;
 const world=structuredClone(f.workspaces.filter(w=>[peer.repoWorkspaceId,peer.workspaceId].includes(w.workspace_id)));
 f.calls.length=0;await close(f,input,layout);assert.equal(await idle(f,input),false);
 assert.deepEqual(f.calls.filter(a=>a[0]==='workspace'&&a[1]==='close'),[['workspace','close',layout.workspaceId]]);
 assert.deepEqual(f.workspaces.filter(w=>[peer.repoWorkspaceId,peer.workspaceId].includes(w.workspace_id)),world);
 assert(f.workspaces.some(w=>w.workspace_id===layout.repoWorkspaceId));
});
for(const field of ['checkout_path','repo_key','is_linked_worktree'])test(`changed live ${field} refuses before allocation or rebinding`,async t=>{
 const {f,b,bInput}=await pair(t);f.workspaces.find(w=>w.workspace_id===b.workspaceId).worktree[field]=field==='is_linked_worktree'?false:f.input.sourceRoot;
 const world=structuredClone(f.workspaces);f.calls.length=0;
 await assert.rejects(f.open(bInput),{code:'herdr_layout_identity_changed'});
 assert.deepEqual(mutations(f),[]);assert.deepEqual(f.workspaces,world);
});
test('legacy run labels do not override live checkout identity',async t=>{
 const f=await fixture(t),a=await f.open();f.workspaces.find(w=>w.workspace_id===a.workspaceId).label='#2 small-change';f.calls.length=0;
 assert.equal((await f.open()).workspaceId,a.workspaceId);assert.deepEqual(mutations(f),[]);
});
for(const kind of ['parent-lost','run-lost'])test(`${kind} reply is reconciled from live identity on explicit retry without duplicates`,async t=>{
 const f=await fixture(t);await f.open();const bInput=await second(f),command=f.ports.command;
 f.ports.command=async args=>{const reply=await command(args);if(args[0]===(kind==='parent-lost'?'workspace':'worktree')&&args[1]===(kind==='parent-lost'?'create':'open'))throw Error('reply lost');return reply;};
 await assert.rejects(f.open(bInput),/reply lost/);f.ports.command=command;
 await assert.doesNotReject(f.open(bInput));
 assert.equal(f.workspaces.filter(w=>w.worktree?.checkout_path===bInput.cwd).length,1);
 assert.equal(f.workspaces.filter(w=>w.worktree?.checkout_path===bInput.sourceRoot).length,1);
});
test('confirmed linked-source refusal permits retry; a lost retry adopts its verified live result',async t=>{
 const f=await fixture(t),command=f.ports.command;let refuse=true;
 f.ports.command=async args=>{if(args[0]==='worktree'&&refuse){f.calls.push(args);refuse=false;throw Object.assign(Error('refused'),{code:'linked_worktree_source'});}return command(args);};
 await assert.rejects(f.open(),{code:'linked_worktree_source'});
 f.ports.command=async args=>{const reply=await command(args);if(args[0]==='worktree')throw Error('retry lost');return reply;};
 await assert.rejects(f.open(),/retry lost/);f.ports.command=command;
 await assert.doesNotReject(f.open({preAgentRefusal:'linked_worktree_source'}));
 assert.equal(f.calls.filter(a=>a[0]==='worktree').length,2);
});
for(const kind of ['occupied','run-cwd','run-common','run-root','inventory'])test(`${kind} cannot authorize mutation of another clone`,async t=>{
 const {f,b,bInput}=await pair(t);
 if(kind==='occupied'){
  f.workspaces.splice(2);f.workspaces.push({workspace_id:'stranger',label:'alice/coffee'},{workspace_id:'stranger-2',label:`alice/coffee@${token(bInput.commonDir)}`});
  // A fresh run has no prior IDs; all parent labels are already occupied.
  bInput.runId=randomUUID();
 }
 if(kind==='run-cwd')f.workspaces.find(w=>w.workspace_id===b.workspaceId).worktree.checkout_path=f.input.cwd;
 if(kind==='run-common')f.workspaces.find(w=>w.workspace_id===b.workspaceId).worktree.repo_key=f.input.commonDir;
 if(kind==='run-root')f.herdr.paneOf(b).agent={agent:'claude',agent_status:'working'};
 const command=f.ports.command;
 f.ports.command=async args=>{const reply=await command(args);if(kind==='run-root'&&args[0]==='pane'&&args[3]===b.workspaceId)reply.result.panes[0].pane_id='forged';if(kind==='inventory'&&args[0]==='workspace'&&args[1]==='list')reply.result.workspaces.push(reply.result.workspaces[0]);return reply;};
 const world=structuredClone(f.workspaces);f.calls.length=0;
 await assert.rejects(f.open(bInput),{code:kind==='occupied'?'repository_label_unavailable':kind==='inventory'?'invalid_workspace_inventory':'herdr_layout_identity_changed'});
 assert.deepEqual(mutations(f),[]);assert.deepEqual(f.workspaces,world);
});
for(const kind of ['tab','pane','identity','lost-close'])test(`parent ${kind} never grants cleanup custody`,async t=>{
 const {f,b,bInput}=await pair(t);await close(f,bInput,b);
 const command=f.ports.command;
 f.ports.command=async args=>{const reply=await command(args);if(args[3]===b.repoWorkspaceId){if(kind==='tab'&&args[0]==='tab')reply.result.tabs.push({tab_id:'personal'});if(kind==='pane'&&args[0]==='pane')reply.result.panes.push({pane_id:'personal'});}if(kind==='lost-close'&&args[0]==='workspace'&&args[1]==='close')throw Error('close lost');return reply;};
 if(kind==='identity')f.workspaces.find(w=>w.workspace_id===b.repoWorkspaceId).worktree.repo_key='/forged';
 f.calls.length=0;assert.equal(await idle(f,bInput),false);assert.equal(await idle(f,bInput),false);
 assert.deepEqual(mutations(f),[]);assert(f.workspaces.some(w=>w.workspace_id===b.repoWorkspaceId));
});
test('mixed clones and origins retain every peer label',async t=>{
 const {f,b}=await pair(t),world=structuredClone(f.workspaces);
 const sourceRoot=join(f.root,'third');await mkdir(sourceRoot);await f.init(sourceRoot,'bob/coffee');f.calls.length=0;
 await f.open({repository:'bob/coffee',sourceRoot,commonDir:join(sourceRoot,'.git'),cwd:sourceRoot,runId:randomUUID()});
 assert.deepEqual(f.workspaces.slice(0,world.length),world);assert.deepEqual(f.calls.filter(a=>a[1]==='rename'),[]);
 assert.equal(f.workspaces.find(w=>w.workspace_id===b.repoWorkspaceId).label,'alice/coffee');
});
for(const kind of ['duplicate','inconsistent','intent','refused'])test(`${kind} legacy registry entries are ignored without repair`,async t=>{
 const {f,b,bInput}=await pair(t),file=join(f.ports.directory,'registry.json');
 const bytes=JSON.stringify({version:1,repositories:[{key:'alice/coffee',repository:kind==='inconsistent'?'someone/else':'alice/coffee',phase:kind}],runs:[{runId:bInput.runId,phase:kind}]});
 await writeFile(file,bytes);const world=structuredClone(f.workspaces);f.calls.length=0;
 const result=await f.open(bInput);assert.equal(result.workspaceId,b.workspaceId);
 assert.equal(await readFile(file,'utf8'),bytes);assert.deepEqual(mutations(f),[]);assert.deepEqual(f.workspaces,world);
});
test('a new run with no saved workspace uses an existing live clone parent',async t=>{
 const f=await fixture(t),a=await f.open(),cwd=join(f.root,'run-two');await mkdir(cwd);
 const result=await f.open({runId:randomUUID(),cwd,stageId:'scope'});
 assert.equal(result.repoWorkspaceId,a.repoWorkspaceId);assert.notEqual(result.workspaceId,a.workspaceId);
 assert.deepEqual(f.calls.filter(a=>['rename','remove'].includes(a[1])),[]);
});
test('multiple verified clone parents remain open and do not make the run ambiguous',async t=>{
 const {f,b,bInput}=await pair(t);
 await f.ports.command(['workspace','create','--cwd',bInput.sourceRoot,'--label','person-parent','--no-focus']);
 const world=structuredClone(f.workspaces);f.calls.length=0;
 assert.equal((await f.open(bInput)).workspaceId,b.workspaceId);assert.equal(await idle(f,bInput),false);
 assert.deepEqual(mutations(f),[]);assert.deepEqual(f.workspaces,world);
});
