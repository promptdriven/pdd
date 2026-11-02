import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,symlinkSync} from 'node:fs';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-runner-fixture.mjs';
import {openHerdrRunLayout,withHerdrLayoutLock} from '../src/workflow-herdr-layout.mjs';
async function setup(t){
  const f=await fixture(t);await f.run();const run=f.record();
  const input={runId:run.runId,repository:run.repo,sourceRoot:run.sourceRoot,commonDir:run.commonDir,cwd:run.root,issueNumber:run.number,workflowName:run.workflow,stageId:run.areas[run.area].name,run,repair:true};
  const ports={command:f.herdr.herdr,directory:join(f.state,'herdr-layout'),checkpoint:async()=>{},execFile:f.ports.execFile};
  const open=()=>withHerdrLayoutLock(()=>openHerdrRunLayout(input,ports),ports);
  return {f,run,input,ports,open};
}
for(const side of ['live','saved'])test(`canonical ${side} checkout alias reuses the same owned workspace`,async t=>{
  const {f,run,input,open}=await setup(t),alias=join(f.base,'run-alias');symlinkSync(run.root,alias,'dir');
  const before=f.herdr.workspaces.length;
  if(side==='saved')input.cwd=alias;
  else {
    const workspace=f.herdr.workspaces.find(w=>w.workspace_id===run.chats[0].workspaceId);assert.ok(workspace);workspace.worktree.checkout_path=alias;
    for(const pane of f.herdr.panes.filter(p=>p.workspace_id===workspace.workspace_id))pane.cwd=alias;
  }
  let result,error;try{result=await open();}catch(e){error=e;}
  assert.equal(error,undefined,'Equivalent filesystem identities permit reuse');
  assert.equal(result.workspaceId,run.chats[0].workspaceId);
  assert.equal(f.herdr.workspaces.length,before);
});
for(const kind of ['missing','stale'])test(`${kind} registry rebuild adopts the run/live identity without destructive repair`,async t=>{
  const {f,run,ports,open}=await setup(t),file=join(ports.directory,'registry.json');
  const registry=JSON.parse(readFileSync(file,'utf8'));
  if(kind==='missing'){registry.runs=[];registry.repositories=[];}
  else {registry.runs.find(r=>r.runId===run.runId).workspaceId='stale-workspace';}
  writeFileSync(file,JSON.stringify(registry));
  const before=f.herdr.calls.length,count=f.herdr.workspaces.length;
  let result,error;try{result=await open();}catch(e){error=e;}
  assert.equal(error,undefined,'Run plus verified live identity can rebuild stale cache');
  assert.equal(result.workspaceId,run.chats[0].workspaceId);
  assert.equal(f.herdr.workspaces.length,count);
  assert.equal(f.herdr.calls.slice(before).filter(a=>['workspace','tab','worktree'].includes(a[0])&&['close','remove','rename'].includes(a[1])).length,0);
  assert.equal((await open()).workspaceId,result.workspaceId,'Repeated repair is idempotent');
});
test('unsafe identity diagnostic names field and both values while retaining custody',async t=>{
  const {f,run,open}=await setup(t),workspace=f.herdr.workspaces.find(w=>w.workspace_id===run.chats[0].workspaceId);assert.ok(workspace);
  workspace.worktree.repo_key='/other/clone/.git';
  let error;try{await open();}catch(e){error=e;}
  assert.ok(error,'Unsafe common-directory mismatch refuses');
  assert.equal(error.code,'herdr_layout_identity_changed');
  assert.ok(error.message.includes('repo_key'));
  assert.ok(error.message.includes(run.commonDir));
  assert.ok(error.message.includes('/other/clone/.git'));
  assert.equal(f.herdr.calls.filter(a=>a[1]==='close'||a[1]==='remove').length,0);
});

test('missing selected tab repair opens one tab in the same run and repeats without another allocation',async t=>{
  const {f,run,open}=await setup(t),chat=run.chats.at(-1);assert.ok(chat);
  f.herdr.tabs=f.herdr.tabs.filter(tab=>tab.tab_id!==chat.tabId);
  f.herdr.panes=f.herdr.panes.filter(pane=>pane.tab_id!==chat.tabId);
  const before=f.herdr.calls.length,workspaceCount=f.herdr.workspaces.length;
  const result=await open();assert.equal(result.workspaceId,chat.workspaceId);
  assert.equal(f.herdr.calls.slice(before).filter(a=>a[0]==='tab'&&a[1]==='create').length,1);
  const repeated=await open();assert.equal(repeated.tabId,result.tabId);
  assert.equal(f.herdr.calls.slice(before).filter(a=>a[0]==='tab'&&a[1]==='create').length,1);
  assert.equal(f.herdr.workspaces.length,workspaceCount);
  assert.equal(f.herdr.calls.slice(before).filter(a=>['close','remove'].includes(a[1])).length,0);
});
test('ambiguous run-matching live peers refuse cache repair without touching either peer',async t=>{
  const {f,run,ports,open}=await setup(t),workspace=f.herdr.workspaces.find(w=>w.workspace_id===run.chats[0].workspaceId);assert.ok(workspace);
  f.herdr.workspaces.push({...structuredClone(workspace),workspace_id:'ambiguous-peer'});
  const file=join(ports.directory,'registry.json'),registry=JSON.parse(readFileSync(file,'utf8'));registry.runs=[];writeFileSync(file,JSON.stringify(registry));
  const before=structuredClone(f.herdr.workspaces),at=f.herdr.calls.length;
  let error;try{await open();}catch(e){error=e;}
  assert.ok(error,'Multiple matching live workspaces cannot establish unique ownership');
  assert.deepEqual(f.herdr.workspaces,before);
  assert.equal(f.herdr.calls.slice(at).filter(a=>['create','open','close','remove','rename'].includes(a[1])).length,0);
});
for(const kind of ['duplicate','inconsistent'])test(`a ${kind} repository cache entry is rebuilt from the run record, not a dead end`,async t=>{
  const {f,run,ports,open}=await setup(t),file=join(ports.directory,'registry.json'),registry=JSON.parse(readFileSync(file,'utf8'));
  if(kind==='duplicate')registry.repositories.push(structuredClone(registry.repositories[0]));
  else registry.repositories[0].repository='someone/else';
  writeFileSync(file,JSON.stringify(registry));
  const count=f.herdr.workspaces.length,at=f.herdr.calls.length;
  let result,error;try{result=await open();}catch(e){error=e;}
  assert.equal(error,undefined,'The run record rebuilds the cache entry');
  assert.equal(result.workspaceId,run.chats[0].workspaceId);
  assert.equal(f.herdr.workspaces.length,count);
  assert.equal(f.herdr.calls.slice(at).filter(a=>['close','remove','rename'].includes(a[1])).length,0);
  const rebuilt=JSON.parse(readFileSync(file,'utf8')).repositories.filter(r=>r.commonDir===run.commonDir);
  assert.equal(rebuilt.length,1);assert.equal(rebuilt[0].repository,run.repo);assert.equal(rebuilt[0].workspaceId,run.chats[0].repoWorkspaceId);
});
