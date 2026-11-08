import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdir, stat } from 'node:fs/promises';
import { join } from 'node:path';
import { randomUUID, createHash } from 'node:crypto';
import { allocateIssueWorktree } from '../src/workflow-worktree.mjs';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';

import {fixture} from './helpers/herdr-layout-fixture.mjs';

async function createWithoutWorktreeMetadata(f, {loseCreateReply = false, loseAttachReply = false, failCreateBeforeEffect = false} = {}) {
 const command=f.ports.command;
 f.ports.command=async args=>{
  if(args[0]==='worktree'&&args[1]==='open'&&args[args.indexOf('--path')+1]===f.input.sourceRoot){
   f.calls.push(args);
   const workspaceId=args[args.indexOf('--workspace')+1],row=f.workspaces.find(w=>w.workspace_id===workspaceId);
   if(row)row.worktree={checkout_path:f.input.sourceRoot,repo_key:f.input.commonDir,is_linked_worktree:false};
   const reply={id:'cli:worktree:open',result:{workspace:structuredClone(row),already_open:true}};
   if(loseAttachReply){loseAttachReply=false;throw Error('attach reply lost');}
   return reply;
  }
  if(args[0]==='workspace'&&args[1]==='create'&&failCreateBeforeEffect){
   failCreateBeforeEffect=false;f.calls.push(args);throw Error('create failed before mutation');
  }
  const reply=await command(args);
  if(args[0]==='workspace'&&args[1]==='create'){
   const workspaceId=reply.result.workspace.workspace_id;
   f.workspaces.find(w=>w.workspace_id===workspaceId).worktree=null;
   reply.result.workspace.worktree=null;
   if(loseCreateReply){loseCreateReply=false;throw Error('create reply lost');}
  }
  return reply;
 };
}
function openWithOwner(f, run) {
 return f.module.withHerdrLayoutLock(()=>f.module.openHerdrRunLayout({...f.input,...(run?{run}:{})},f.ports),f.ports);
}

test('2859: checkpoints a newly created parent before attaching it and retries the same workspace',async t=>{
 const f=await fixture(t);await createWithoutWorktreeMetadata(f);
 let saved,interrupt=true;f.ports.checkpoint=async custody=>{saved=structuredClone(custody);if(interrupt&&custody.repoWorkspaceId&&custody.repoRoot){interrupt=false;throw Error('stop after parent custody');}};
 await assert.rejects(openWithOwner(f),/stop after parent custody/);
 assert.equal(f.workspaces.length,1);assert.equal(f.workspaces[0].worktree,null);
 assert.equal(f.calls.filter(args=>args[0]==='worktree').length,0,'the attach must wait for durable parent custody');
 assert(saved.repoWorkspaceId);assert.deepEqual(Object.keys(saved.repoRoot).sort(),['cwd','paneId','tabId','terminalId']);
 const result=await openWithOwner(f,{runId:f.input.runId,layout:saved,chats:[]});
 assert.equal(f.workspaces.length,2,'retry must reuse the created parent');
 assert.equal(f.calls.filter(args=>args[0]==='workspace'&&args[1]==='create').length,1);
 assert.deepEqual(f.calls.find(args=>args[0]==='worktree'&&args[1]==='open'),['worktree','open','--workspace',saved.repoWorkspaceId,'--path',f.input.sourceRoot,'--no-focus']);
 const parent=f.workspaces.find(row=>row.workspace_id===saved.repoWorkspaceId);
 assert.deepEqual(parent.worktree,{checkout_path:f.input.sourceRoot,repo_key:f.input.commonDir,is_linked_worktree:false});
 assert.equal(result.repoWorkspaceId,saved.repoWorkspaceId);assert.deepEqual(result.repoRoot,saved.repoRoot);
 assert.equal(f.workspaces.find(row=>row.workspace_id===result.workspaceId).worktree.is_linked_worktree,true);
});

test('2859: a lost attach acknowledgement is resolved from the saved ID and live inventory',async t=>{
 const f=await fixture(t);await createWithoutWorktreeMetadata(f,{loseAttachReply:true});
 const result=await openWithOwner(f);
 assert.equal(f.calls.filter(args=>args[0]==='workspace'&&args[1]==='create').length,1);
 assert.equal(f.calls.filter(args=>args[0]==='worktree'&&args[1]==='open').length,2,'one parent attach and one assigned run-worktree open');
 assert.equal(result.repoWorkspaceId,f.workspaces[0].workspace_id);
 assert.equal(f.workspaces.filter(row=>row.worktree?.checkout_path===f.input.sourceRoot).length,1);
});

test('2859: a lost create reply keeps uncertainty and never creates a duplicate workspace',async t=>{
 const f=await fixture(t);await createWithoutWorktreeMetadata(f,{loseCreateReply:true});
 let saved;f.ports.checkpoint=async custody=>{saved=structuredClone(custody);};
 await assert.rejects(openWithOwner(f),/create reply lost/);
 assert(saved.repoCreateIntent);assert.equal(f.workspaces.length,1);
 const failure=await openWithOwner(f,{runId:f.input.runId,layout:saved,chats:[]}).then(()=>null,error=>error);
 assert.equal(failure.code,'herdr_layout_identity_changed');
 assert.equal(f.calls.filter(args=>args[0]==='workspace'&&args[1]==='create').length,1);
 assert.equal(f.workspaces.length,1);assert.equal(f.workspaces[0].worktree,null);
 assert.equal(f.calls.filter(args=>args[0]==='worktree').length,0);
});

test('2859: a create intent with no observed effect permits one safe retry',async t=>{
 const f=await fixture(t);await createWithoutWorktreeMetadata(f,{failCreateBeforeEffect:true});
 let saved;f.ports.checkpoint=async custody=>{saved=structuredClone(custody);};
 await assert.rejects(openWithOwner(f),/create failed before mutation/);
 assert(saved.repoCreateIntent);assert.equal(f.workspaces.length,0);
 const result=await openWithOwner(f,{runId:f.input.runId,layout:saved,chats:[]});
 assert.equal(f.calls.filter(args=>args[0]==='workspace'&&args[1]==='create').length,2);
 assert.equal(f.workspaces.filter(row=>row.worktree?.checkout_path===f.input.sourceRoot).length,1);
 assert(result.workspaceId);
});

test('2859: a fresh create checkpoint clears merged stale parent ID and root',async t=>{
 const f=await fixture(t),oldId='legacy-parent';
 f.workspaces.push({workspace_id:oldId,label:'legacy',worktree:{checkout_path:f.input.sourceRoot,repo_key:f.input.commonDir,is_linked_worktree:true}});
 const oldRoot={tabId:'old-tab',paneId:'old-pane',terminalId:'old-terminal',cwd:f.input.sourceRoot};
 const stale={repoWorkspaceId:oldId,repoRoot:oldRoot,repoCreateIntent:{label:'coffee',parentRoot:f.input.sourceRoot,
  commonDir:f.input.commonDir,workspaceIdsBefore:[oldId]}};
 let persisted=structuredClone(stale),interrupt=true;
 f.ports.checkpoint=async custody=>{
  persisted={...persisted,...structuredClone(custody)};
  if(interrupt&&custody.repoCreateIntent?.label==='coffee'&&custody.repoWorkspaceId===null&&custody.repoRoot===null){
   interrupt=false;throw Error('stop before replacement create');
  }
 };
 await assert.rejects(openWithOwner(f,{runId:f.input.runId,layout:stale,chats:[]}),/stop before replacement create/);
 assert.equal(persisted.repoWorkspaceId,null);assert.equal(persisted.repoRoot,null);
 assert.equal(f.calls.filter(args=>args[0]==='workspace'&&args[1]==='create').length,0);
 const result=await openWithOwner(f,{runId:f.input.runId,layout:persisted,chats:[]});
 assert.notEqual(result.repoWorkspaceId,oldId);
 assert.equal(f.calls.filter(args=>args[0]==='workspace'&&args[1]==='create').length,1);
 assert.equal(f.workspaces.filter(row=>row.worktree?.checkout_path===f.input.sourceRoot&&row.worktree?.is_linked_worktree===false).length,1);
});

test('2859: retries refuse a changed original root or foreign checkout identity',async t=>{
 for(const kind of ['root','identity','extra-pane']){
  const f=await fixture(t);await createWithoutWorktreeMetadata(f);
  let saved,interrupt=true;f.ports.checkpoint=async custody=>{saved=structuredClone(custody);if(interrupt&&custody.repoWorkspaceId&&custody.repoRoot){interrupt=false;throw Error('stop after parent custody');}};
  await assert.rejects(openWithOwner(f),/stop after parent custody/);
  const row=f.workspaces.find(w=>w.workspace_id===saved.repoWorkspaceId);
  if(kind==='root')f.herdr.panes.find(p=>p.workspace_id===row.workspace_id).pane_id='replacement';
  else if(kind==='identity')row.worktree={checkout_path:f.input.cwd,repo_key:f.input.commonDir,is_linked_worktree:false};
  else f.herdr.panes.push({...f.herdr.panes.find(p=>p.workspace_id===row.workspace_id),pane_id:'extra-pane'});
  await assert.rejects(openWithOwner(f,{runId:f.input.runId,layout:saved,chats:[]}),{code:'herdr_layout_identity_changed'});
  assert.equal(f.calls.filter(args=>args[0]==='workspace'&&args[1]==='create').length,1);
  assert.equal(f.calls.filter(args=>args[0]==='worktree').length,0);
 }
});

test('2903: a changed repository workspace refusal names its own first tab, not the run tab',async t=>{
 const f=await fixture(t);await createWithoutWorktreeMetadata(f);
 let saved,interrupt=true;f.ports.checkpoint=async custody=>{saved=structuredClone(custody);if(interrupt&&custody.repoWorkspaceId&&custody.repoRoot){interrupt=false;throw Error('stop after parent custody');}};
 await assert.rejects(openWithOwner(f),/stop after parent custody/);
 const row=f.workspaces.find(w=>w.workspace_id===saved.repoWorkspaceId);
 f.herdr.panes.push({...f.herdr.panes.find(p=>p.workspace_id===row.workspace_id),pane_id:'extra-pane'});
 const error=await openWithOwner(f,{runId:f.input.runId,layout:saved,chats:[]}).catch(e=>e);
 assert.equal(error.code,'herdr_layout_identity_changed');assert.equal(error.field,'parent_root');
 const lines=error.message.split('\n'),expected=lines.find(line=>line.startsWith('Expected parent_root: ')),found=lines.find(line=>line.startsWith('Found parent_root: '));
 assert.ok(found&&found.includes('paneCount 2')&&!/\bcwd\b/.test(found),error.message);
 // The saved tab is compared by its Herdr IDs only, so its folder is on neither line.
 assert.ok(expected&&expected.includes(JSON.stringify(saved.repoRoot.terminalId))&&!/\bcwd\b/.test(expected),error.message);
});

test('2903: a saved repository first tab that names another folder is refused as parent custody, with the folder on both lines',async t=>{
 const f=await fixture(t);await createWithoutWorktreeMetadata(f);
 let saved,interrupt=true;f.ports.checkpoint=async custody=>{saved=structuredClone(custody);if(interrupt&&custody.repoWorkspaceId&&custody.repoRoot){interrupt=false;throw Error('stop after parent custody');}};
 await assert.rejects(openWithOwner(f),/stop after parent custody/);
 // Herdr now shows the created parent with its worktree, but pdd's saved record of its first tab names another folder.
 const row=f.workspaces.find(w=>w.workspace_id===saved.repoWorkspaceId);
 row.worktree={checkout_path:f.input.sourceRoot,repo_key:f.input.commonDir,is_linked_worktree:false};
 const other=join(f.root,'other');await mkdir(other);
 const error=await openWithOwner(f,{runId:f.input.runId,layout:{...saved,repoRoot:{...saved.repoRoot,cwd:other}},chats:[]}).catch(e=>e);
 assert.equal(error.code,'herdr_layout_identity_changed',error.message);assert.equal(error.field,'parent_custody',error.message);
 const lines=error.message.split('\n'),expected=lines.find(line=>line.startsWith('Expected parent_custody: ')),found=lines.find(line=>line.startsWith('Found parent_custody: '));
 assert.ok(expected&&/\bcwd\b/.test(expected),error.message);
 assert.ok(found&&found.includes(`cwd ${JSON.stringify(other)}`),error.message);
 assert.equal(f.calls.filter(args=>args[0]==='worktree'&&args[1]==='open').length,0);
});

test('2859: a missing pending parent refuses, while verified live identity can recover a partial root',async t=>{
 {
  const f=await fixture(t);await createWithoutWorktreeMetadata(f);
  let saved,interrupt=true;f.ports.checkpoint=async custody=>{saved=structuredClone(custody);if(interrupt&&custody.repoWorkspaceId&&custody.repoRoot){interrupt=false;throw Error('stop after parent custody');}};
  await assert.rejects(openWithOwner(f),/stop after parent custody/);
  const parentId=saved.repoWorkspaceId;
  f.workspaces.splice(f.workspaces.findIndex(row=>row.workspace_id===parentId),1);
  f.herdr.tabs=f.herdr.tabs.filter(tab=>tab.workspace_id!==parentId);
  f.herdr.panes=f.herdr.panes.filter(pane=>pane.workspace_id!==parentId);
  await assert.rejects(openWithOwner(f,{runId:f.input.runId,layout:saved,chats:[]}),{code:'herdr_layout_identity_changed'});
  assert.equal(f.calls.filter(args=>args[0]==='workspace'&&args[1]==='create').length,1);
  assert.equal(f.calls.filter(args=>args[0]==='worktree'&&args[1]==='open').length,0);
 }
 {
  const f=await fixture(t);await createWithoutWorktreeMetadata(f);
  let saved,interrupt=true;f.ports.checkpoint=async custody=>{saved=structuredClone(custody);if(interrupt&&custody.repoWorkspaceId&&custody.repoRoot){interrupt=false;throw Error('stop after parent custody');}};
  await assert.rejects(openWithOwner(f),/stop after parent custody/);
  const parentId=saved.repoWorkspaceId,parent=f.workspaces.find(row=>row.workspace_id===parentId);
  parent.worktree={checkout_path:f.input.sourceRoot,repo_key:f.input.commonDir,is_linked_worktree:false};
  const partial={...saved,repoRoot:{tabId:null,paneId:null,terminalId:null,cwd:null}};
  const result=await openWithOwner(f,{runId:f.input.runId,layout:partial,chats:[]});
  assert.equal(result.repoWorkspaceId,parentId);
  assert.equal(result.repoCreateIntent,null);
  assert.equal(result.repoRoot,undefined);
  assert.equal(f.calls.filter(args=>args[0]==='worktree'&&args[1]==='open'&&args[args.indexOf('--workspace')+1]===parentId
   &&args[args.indexOf('--path')+1]===f.input.sourceRoot).length,0,
   'independently verified live parent identity permits reuse without attachment');
  assert.equal(f.calls.filter(args=>args[0]==='workspace'&&args[1]==='create').length,1);
 }
});

test('2859: an unrelated blank same-label workspace is never attached by label',async t=>{
 const f=await fixture(t),other=join(f.root,'other');await mkdir(other);await f.init(other,'bob/coffee');
 const unrelated=await f.ports.command(['workspace','create','--cwd',other,'--label','coffee','--no-focus']);
 const original=f.workspaces.find(w=>w.workspace_id===unrelated.result.workspace.workspace_id);original.worktree=null;
 const before=structuredClone(original),result=await f.open();
 assert.equal(f.workspaces.find(w=>w.workspace_id===original.workspace_id).worktree,null);
 assert.equal(f.workspaces.find(w=>w.workspace_id===result.repoWorkspaceId).label,'alice/coffee');
 assert.deepEqual(f.workspaces.find(w=>w.workspace_id===original.workspace_id),before);
 assert.equal(f.calls.some(args=>args[0]==='worktree'&&args[1]==='open'&&args[args.indexOf('--workspace')+1]===original.workspace_id),false);
});

test('2859: a unique verified run remains reusable when its old parent hint is unavailable',async t=>{
 const f=await fixture(t),first=await f.open(),parent=f.workspaces.find(w=>w.workspace_id===first.repoWorkspaceId),before=f.calls.length;
 parent.worktree=null;
 const reopened=await openWithOwner(f,{runId:f.input.runId,layout:{workspaceId:first.workspaceId,repoWorkspaceId:'stale-parent',repoCreateIntent:{label:'prior-attempt',parentRoot:f.input.sourceRoot,commonDir:f.input.commonDir,workspaceIdsBefore:[]},...first.root},chats:[]});
 assert.equal(reopened.workspaceId,first.workspaceId);
 assert.equal(f.workspaces.length,2);
 assert.equal(f.calls.slice(before).some(args=>args[0]==='workspace'&&args[1]==='create'||args[0]==='worktree'&&args[1]==='open'),false);
 assert.equal(parent.worktree,null);
});

test('repository reuse, one worktree per run, issue/workflow label and stage tabs',async t=>{
 const f=await fixture(t),a=await f.open(),b=await f.open({stageId:'change'});
 assert.equal(a.repoWorkspaceId,b.repoWorkspaceId);assert.equal(a.workspaceId,b.workspaceId);assert.notEqual(a.tabId,b.tabId);
 assert.deepEqual(f.workspaces.map(w=>w.label),['coffee','coffee#2 small-change']);
 assert.deepEqual(f.calls.find(a=>a[0]==='worktree'),['worktree','open','--workspace',a.repoWorkspaceId,'--path',f.input.cwd,'--label','coffee#2 small-change','--no-focus']);
 assert.equal(f.calls.filter(a=>a[0]==='worktree').length,1);
 assert(f.calls.filter(c=>c[0]==='tab'&&c[1]==='create').every(c=>c[c.indexOf('--workspace')+1]===a.workspaceId));
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
test('repo-name clash preserves the existing layout and qualifies the new parent',async t=>{
 const f=await fixture(t),a=await f.open(),other=join(f.root,'other');await mkdir(other);await f.init(other,'bob/coffee');
 await f.open({runId:randomUUID(),repository:'bob/coffee',sourceRoot:other,commonDir:join(other,'.git'),cwd:other});
 assert.deepEqual(f.workspaces.map(w=>w.label),['coffee','coffee#2 small-change','bob/coffee','coffee#2 small-change']);assert.equal(f.workspaces[1].workspace_id,a.workspaceId);
});
test('run cleanup closes only run workspace, retaining repository and git checkout',async t=>{
 const f=await fixture(t),layout=await f.open();
 await f.module.withHerdrLayoutLock(()=>f.close({...f.input,layout},f.ports),f.ports);
 assert.deepEqual(f.workspaces.map(w=>w.label),['coffee']);assert.deepEqual(f.calls.filter(a=>a[0]==='workspace'&&a[1]==='close'),[['workspace','close',layout.workspaceId]]);
 assert(!f.calls.some(a=>a[0]==='worktree'&&a[1]==='remove'));assert((await stat(f.input.cwd)).isDirectory());
});
test('unrelated workspace untouched, allocation reply loss never repeats creation',async t=>{
 const f=await fixture(t);f.workspaces.push({workspace_id:'personal',label:'notes'});const command=f.ports.command;
 f.ports.command=async args=>{const response=await command(args);if(args[0]==='worktree')throw Error('reply lost');return response;};
 await assert.rejects(f.open(),/reply lost/);f.ports.command=command;await assert.doesNotReject(f.open(),'Explicit retry adopts the unique live allocation');
 assert.deepEqual(f.workspaces[0],{workspace_id:'personal',label:'notes'});assert.equal(f.calls.filter(a=>a[0]==='worktree').length,1);
});

test('missing or changed worktree identity cannot authorize run reuse or close',async t=>{
 for(const patch of [null,{checkout_path:'/other',repo_key:'/other/.git',is_linked_worktree:true}]) {
  const f=await fixture(t),layout=await f.open();
  const row=f.workspaces.find(w=>w.workspace_id===layout.workspaceId);row.worktree=patch;
  await assert.rejects(f.open(),/herdr_layout_identity_changed/);
  await assert.rejects(f.module.withHerdrLayoutLock(()=>f.close({...f.input,layout},f.ports),f.ports),/herdr_layout_identity_changed/);
  assert(!f.calls.some(a=>a[0]==='workspace'&&a[1]==='close'));
 }
});
test('changed root terminal or an extra tab prevents run cleanup',async t=>{
 for(const kind of ['terminal','tab','pane']) {
  const f=await fixture(t),layout=await f.open();const original=f.ports.command;
  f.ports.command=async args=>{const response=await original(args);if(kind==='terminal'&&args[0]==='pane')response.result.panes[0].terminal_id='replacement';if(kind==='pane'&&args[0]==='pane')response.result.panes.push({pane_id:'person-pane'});if(kind==='tab'&&args[0]==='tab'&&args[1]==='list')response.result.tabs.push({tab_id:'user-tab'});return response;};
  await assert.rejects(f.module.withHerdrLayoutLock(()=>f.close({...f.input,layout},f.ports),f.ports),/herdr_layout_identity_changed|run_has_open_tabs/);
  assert(!f.calls.some(a=>a[0]==='workspace'&&a[1]==='close'));
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
  {workspace_id:'qualified',label:'alice/coffee',worktree:{checkout_path:other}},
  {workspace_id:'final',label:'alice/coffee@'+createHash('sha256').update(f.input.commonDir).digest('hex').slice(0,12)});
 const before=structuredClone(f.workspaces);
 await assert.rejects(f.open(),/repository_label_unavailable/);
 assert.deepEqual(f.workspaces,before);
 assert(f.calls.every(args=>args[0]==='workspace'&&args[1]==='list'));
});
test('repository workspace stays open without durable parent creation custody',async t=>{
 const f=await fixture(t),layout=await f.open(),idle=()=>f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir:f.input.commonDir},f.ports),f.ports);
 assert.equal(await idle(),false,'a run is still open');
 await f.module.withHerdrLayoutLock(()=>f.close({...f.input,layout},f.ports),f.ports);
 const command=f.ports.command;
 f.ports.command=async args=>{const reply=await command(args);if(args[0]==='tab'&&args[1]==='list'&&args[3]===layout.repoWorkspaceId)reply.result.tabs.push({tab_id:'person-tab'});return reply;};
 assert.equal(await idle(),false,'the person opened another tab there');assert.deepEqual(f.workspaces.map(w=>w.label),['coffee']);
 f.ports.command=command;
 assert.equal(await idle(),false);assert.deepEqual(f.workspaces.map(w=>w.label),['coffee']);
 assert.equal(await idle(),false,'Repeated cleanup still has no creation custody');
});

test('2531: a parent without Git metadata stays untouched while the verified run remains reusable',async t=>{
 const f=await fixture(t),layout=await f.open();
 f.workspaces.find(w=>w.workspace_id===layout.repoWorkspaceId).worktree=null;
 // Pane cwd remains the pinned parent even before Herdr has populated worktree metadata.
 const original=f.ports.command;f.ports.command=async args=>{
  const reply=await original(args);
  if(args[0]==='pane'&&args[1]==='list'&&args[3]===layout.repoWorkspaceId)reply.result.panes[0].cwd=f.input.sourceRoot;
  return reply;
 };
 await f.open({stageId:'change'});
 await f.module.withHerdrLayoutLock(()=>f.close({...f.input,layout},f.ports),f.ports);
 const closed=await f.module.withHerdrLayoutLock(()=>f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir:f.input.commonDir},f.ports),f.ports);
 assert.equal(closed,false);assert.deepEqual(f.workspaces.map(w=>w.label),['coffee']);
});

test('2531: a null-metadata parent is never renamed on a repository-name clash',async t=>{
 const f=await fixture(t),layout=await f.open(),other=join(f.root,'other-repo');await mkdir(other);await f.init(other,'bob/coffee');
 f.workspaces.find(w=>w.workspace_id===layout.repoWorkspaceId).worktree=null;
 const original=f.ports.command;f.ports.command=async args=>{
  const reply=await original(args);if(args[0]==='pane'&&args[1]==='list'&&args[3]===layout.repoWorkspaceId)reply.result.panes[0].cwd=f.input.sourceRoot;
  return reply;
 };
 await f.open({runId:randomUUID(),repository:'bob/coffee',sourceRoot:other,commonDir:join(other,'.git'),cwd:other});
 assert.equal(f.workspaces.find(w=>w.workspace_id===layout.repoWorkspaceId).label,'coffee');
});

test('2531: unverifiable parent metadata is never cleanup custody',async t=>{
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
  assert.equal(await f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir:f.input.commonDir},f.ports),false,kind);
  assert(f.workspaces.includes(row));
  assert(!f.calls.some(a=>a[0]==='workspace'&&a[1]==='close'));
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
 await f.module.withHerdrLayoutLock(()=>f.close({...f.input,...second,layout},f.ports),f.ports);
 assert.equal(await f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir:second.commonDir},f.ports),false);
 assert(f.workspaces.some(w=>w.workspace_id===layout.repoWorkspaceId));
 assert.deepEqual(f.workspaces.slice(0,original.length),original);
 assert(f.workspaces.some(w=>w.workspace_id===thirdLayout.repoWorkspaceId));
 const restart={...second,runId:randomUUID()},restarted=await f.open(restart);
 assert.notEqual(restarted.workspaceId,layout.workspaceId);
 assert.equal((await f.open({...restart,stageId:'change'})).workspaceId,restarted.workspaceId);
 const peer=f.workspaces.find(w=>w.workspace_id===first.workspaceId);peer.worktree.checkout_path='/changed';
 await assert.rejects(f.open(),/herdr_layout_identity_changed/,'multiple checkouts must not weaken identity checks');
 assert(!f.calls.some(args=>args[0]==='workspace'&&args[1]==='rename'));
});

test('2615: duplicate legacy parent rows are ignored and any verified live parent can be reused', async t => {
 const f=await fixture(t),first=await f.open();
 const {writeFile,readFile}=await import('node:fs/promises'),file=join(f.ports.directory,'registry.json');
 const bytes=JSON.stringify({repositories:[{workspaceId:'missing'},{workspaceId:'missing'}],runs:[{phase:'intent'}]});await writeFile(file,bytes);
 const other=await f.ports.command(['workspace','create','--cwd',f.input.sourceRoot,'--label','person-parent','--no-focus']);
 const result=await f.open({stageId:'change'});
 assert.equal(result.workspaceId,first.workspaceId);
 assert([first.repoWorkspaceId,other.result.workspace.workspace_id].includes(result.repoWorkspaceId));
 assert.equal(await readFile(file,'utf8'),bytes);
 assert(!f.calls.some(a=>['rename','remove'].includes(a[1])));
});


async function assertOpen(f,input={}) {
 let result;
 await assert.doesNotReject(async()=>{result=await f.open(input);},'the requested owned layout must remain available');
 return result;
}

test('2615: a new clone uses the free short label despite a closed peer workspace in the registry', async t => {
 const f=await fixture(t),first=await assertOpen(f);
 f.workspaces.splice(f.workspaces.findIndex(w=>w.workspace_id===first.repoWorkspaceId),1);
 const peers=structuredClone(f.workspaces),sourceRoot=join(f.root,'fresh-clone'),cwd=join(f.root,'fresh-run');
 await mkdir(sourceRoot);await mkdir(cwd);await f.init(sourceRoot,'alice/coffee');
 const next=await assertOpen(f,{runId:randomUUID(),sourceRoot,commonDir:join(sourceRoot,'.git'),cwd});
 assert.equal(f.workspaces.find(w=>w.workspace_id===next.repoWorkspaceId).label,'coffee');
 assert.deepEqual(f.workspaces.slice(0,peers.length),peers);
 assert(!f.calls.some(args=>args[0]==='workspace'&&args[1]==='rename'));
});

test('2615: canceling a run retains its short-label parent while another clone stays open', async t => {
 const f=await fixture(t),first=await assertOpen(f),sourceRoot=join(f.root,'peer'),cwd=join(f.root,'peer-run');
 await mkdir(sourceRoot);await mkdir(cwd);await f.init(sourceRoot,'alice/coffee');
 const peer=await assertOpen(f,{runId:randomUUID(),sourceRoot,commonDir:join(sourceRoot,'.git'),cwd});
 await f.module.withHerdrLayoutLock(async()=>{
  await f.close({...f.input,layout:first},f.ports);
  assert.equal(await f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir:f.input.commonDir},f.ports),false);
 },f.ports);
 const peerRows=structuredClone(f.workspaces),newCwd=join(f.root,'restart');await mkdir(newCwd);
 const restarted=await assertOpen(f,{runId:randomUUID(),cwd:newCwd});
 assert.equal(f.workspaces.find(w=>w.workspace_id===restarted.repoWorkspaceId).label,'coffee');
 assert.deepEqual(f.workspaces.slice(0,peerRows.length),peerRows);
 assert(f.workspaces.some(w=>w.workspace_id===peer.repoWorkspaceId));
});

for(const holder of ['free owner/repo label','unrelated workspace']) {
 test(`2615: different-repository qualification preserves stable peer labels with ${holder}`, async t => {
  const f=await fixture(t),first=await assertOpen(f);
  const clone=async name=>{
   const sourceRoot=join(f.root,name),cwd=join(f.root,name+'-run');
   await mkdir(sourceRoot);await mkdir(cwd);await f.init(sourceRoot,'alice/coffee');
   const input={runId:randomUUID(),sourceRoot,commonDir:join(sourceRoot,'.git'),cwd};
   return {input,layout:await assertOpen(f,input)};
  };
  const second=await clone('second'),third=await clone('third');
  const stable=f.workspaces.find(w=>w.workspace_id===third.layout.repoWorkspaceId).label;
  assert(stable.startsWith('alice/coffee@'));
  // Leave two active alice/coffee clones: the short name and a stable qualified name.
  await f.module.withHerdrLayoutLock(async()=>{
   await f.close({...f.input,...second.input,layout:second.layout},f.ports);
   assert.equal(await f.module.closeHerdrRepoLayoutIfIdle({repository:f.input.repository,commonDir:second.input.commonDir},f.ports),false);
  },f.ports);
  let unrelated;
  if(holder==='unrelated workspace') {
   unrelated={workspace_id:'personal',label:'alice/coffee',worktree:{checkout_path:'/personal'}};
   f.workspaces.push(structuredClone(unrelated));
  }
  const before=f.calls.length,sourceRoot=join(f.root,'bob'),cwd=join(f.root,'bob-run');
  await mkdir(sourceRoot);await mkdir(cwd);await f.init(sourceRoot,'bob/coffee');
  const bob=await assertOpen(f,{runId:randomUUID(),repository:'bob/coffee',sourceRoot,commonDir:join(sourceRoot,'.git'),cwd});
  const label=f.workspaces.find(w=>w.workspace_id===first.repoWorkspaceId).label;
  if(unrelated) {
   assert.equal(label,'coffee');assert.notEqual(label,stable);
   assert.deepEqual(f.workspaces.find(w=>w.workspace_id===unrelated.workspace_id),unrelated);
  } else assert.equal(label,'coffee');
  assert.equal(f.workspaces.find(w=>w.workspace_id===third.layout.repoWorkspaceId).label,stable,'qualification uses the common directory and does not replace a stable peer label');
  assert.equal(f.workspaces.find(w=>w.workspace_id===bob.repoWorkspaceId).label,'bob/coffee');
  assert.deepEqual(f.calls.slice(before).filter(args=>args[0]==='workspace'&&args[1]==='rename'),
   [],'Existing workspace labels stay intact');
 });
}

test('lost run-close acknowledgement reconciles absence and never repeats the close',async t=>{
 const f=await fixture(t),layout=await f.open(),command=f.ports.command,checkpoints=[];
 f.ports.checkpoint=async()=>checkpoints.push(layout.phase);
 f.ports.command=async args=>{const reply=await command(args);if(args[0]==='workspace'&&args[1]==='close')throw Error('close reply lost');return reply;};
 await assert.rejects(f.module.withHerdrLayoutLock(()=>f.close({...f.input,layout}),f.ports),/close reply lost/);
 assert.deepEqual(checkpoints,['close_intent']);assert.equal(layout.phase,'close_intent');
 f.ports.command=command;
 await assert.doesNotReject(f.module.closeHerdrRunLayout({...f.input,layout},f.ports));
 assert.equal(layout.phase,'closed');
 assert.equal(f.calls.filter(a=>a[0]==='workspace'&&a[1]==='close').length,1);
});
test('checkpoint failure prevents the next allocation or close effect',async t=>{
 const f=await fixture(t),fail=async()=>{throw Error('checkpoint failed');};
 f.ports.checkpoint=fail;await assert.rejects(f.open(),/checkpoint failed/);
 assert(!f.calls.some(a=>['create','open'].includes(a[1])));
 f.ports.checkpoint=async()=>{};const layout=await f.open();
 for(const tab of f.herdr.tabs.filter(t=>t.workspace_id===layout.workspaceId&&t.tab_id!==layout.root.tabId))await f.ports.command(['tab','close',tab.tab_id]);
 f.ports.checkpoint=fail;await assert.rejects(f.module.closeHerdrRunLayout({...f.input,layout},f.ports),/checkpoint failed/);
 assert(!f.calls.some(a=>a[0]==='workspace'&&a[1]==='close'));
});
