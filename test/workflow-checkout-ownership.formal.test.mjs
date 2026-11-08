import './helpers/test-home.mjs';
// Oracle: approved retry-with-live-herdr-layout.md, Rules to check and AC2–5.
// Issue 3084 permits terminal refresh in an unchanged layout.
// Registry contents have no authority; parent adoption does not confer close custody.
// Cleanup also applies the #2709 repair contract: reconcile a pending close only
// with verified original ownership and safe shell occupancy.
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtemp,mkdir,writeFile,readFile,rm,realpath,access} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {fakeHerdr} from './helpers/fake-herdr.mjs';
import {openHerdrRunLayout,closeHerdrRunLayout,closeHerdrRepoLayoutIfIdle,withHerdrLayoutLock} from '../src/workflow-herdr-layout.mjs';
const repository='example/project';
const copy=x=>structuredClone(x);
const registries=['ready','intent','refused','malformed'];
// area-shell-moved: the area tab's shell is in another folder (a shell startup cd); a live folder is not identity (2903).
const openStates=['unique','absent','already-open','duplicate-run','wrong-clone','wrong-linked','area-shell-moved','duplicate-area','restarted-terminal'];
// Exhaustive Cartesian products: open 4 registry states × 2 inventory orders ×
// 2 independent clones × 9 live states = 144; parent labels 2×2×4 = 16;
// cleanup 2×2×7 = 28. Total 188 seeded worlds, real public module boundaries.
test('bounded live checkout ownership: all 188 seeded worlds',async()=>{
 const root=await mkdtemp(join(tmpdir(),'pdd-formal-live-'));
 try {
  const clones=[];
  for(const name of ['A','B']){
   const source=join(root,name),cwd=join(root,`${name}-run`);await mkdir(source);
   const git=args=>execFileSync('git',args,{cwd:source,stdio:'pipe'});
   git(['init']);git(['remote','add','origin','https://github.com/example/project.git']);
   git(['-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','--allow-empty','-m','fixture']);
   git(['worktree','add','-b',`run-${name}`,cwd]);
   clones.push({source:await realpath(source),cwd:await realpath(cwd),common:await realpath(join(source,'.git'))});
  }
  let worlds=0;
  async function world(order,target,registry='intent'){
   const directory=join(root,`world-${worlds++}`);await mkdir(directory);
   const h=fakeHerdr(),events=[],c=clones[target];
   const seed=(w,label,path,common,linked)=>{
    h.workspaces.push({workspace_id:w,label,worktree:{checkout_path:path,repo_key:common,is_linked_worktree:linked}});
    h.tabs.push({workspace_id:w,tab_id:`${w}-t`,label:'1'});
    h.panes.push({workspace_id:w,tab_id:`${w}-t`,pane_id:`${w}-p`,terminal_id:`${w}-x`,cwd:path});
   };
   for(const [i,clone] of clones.entries()){
    seed(`parent-${i}`,i?'person-parent':'project',clone.source,clone.common,false);
    seed(`run-${i}`,'arbitrary run label',clone.cwd,clone.common,true);
   }
   h.workspaces.push({workspace_id:'legacy',label:'old linked source without metadata'});
   if(order)h.workspaces.reverse();
   const bytes=registry==='malformed'?'{not json':JSON.stringify({version:1,repositories:[{key:repository,sourceRoot:clones[1-target].cwd,commonDir:c.common,workspaceId:'legacy',phase:registry}],runs:[{runId:`run-${target}`,cwd:c.cwd,phase:registry}]});
   const file=join(directory,'registry.json');await writeFile(file,bytes);
   const saved={repo:repository,number:17,workflow:'bug',runId:`run-${target}`,root:c.cwd,commonDir:c.common,layout:{phase:registry==='refused'?'close_intent':'ready',workspaceId:`run-${target}`,tabId:`run-${target}-t`,paneId:`run-${target}-p`,terminalId:`run-${target}-x`},chats:[]};
   const input={repository,issueNumber:17,runId:saved.runId,workflowName:'bug',stageId:'formal',sourceRoot:c.source,commonDir:c.common,cwd:c.cwd,run:saved};
   let checkpoint=0, effectCheckpoint=0;
   const ports={directory,checkpoint:async()=>{checkpoint++;events.push('checkpoint');},command:async args=>{
    await access(join(directory,'lock')); // Every inventory/effect occurs inside the find/create lock.
    if(['create','open','close'].includes(args[1])){
     // Read-only inventory may follow custody persistence before the next effect.
     assert.ok(checkpoint>effectCheckpoint,'a fresh checkpoint precedes each effect');
     effectCheckpoint=checkpoint;
    }
    events.push(args.slice(0,2).join(':'));
    return h.herdr(args);
   }};
   const mutate=()=>h.calls.filter(a=>['create','open','close','remove','rename'].includes(a[1]));
   const peer=()=>copy({workspaces:h.workspaces.filter(w=>['legacy',`parent-${1-target}`,`run-${1-target}`].includes(w.workspace_id)),tabs:h.tabs.filter(t=>t.workspace_id.endsWith(`-${1-target}`)),panes:h.panes.filter(p=>p.workspace_id.endsWith(`-${1-target}`))});
   const before=peer();
   const unchanged=async()=>{assert.deepEqual(peer(),before,'unrelated clone and metadata-free legacy workspace preserved');assert.equal(await readFile(file,'utf8'),bytes,'registry bytes unchanged');};
   const open=()=>withHerdrLayoutLock(()=>openHerdrRunLayout(input,ports),ports);
   return {h,c,input,saved,ports,open,mutate,unchanged,seed,events,get checkpoints(){return checkpoint;}};
  }
  for(const registry of registries)for(const order of [0,1])for(const target of [0,1])for(const state of openStates){
   const w=await world(order,target,registry),id=`run-${target}`;
   const row=w.h.workspaces.find(x=>x.workspace_id===id);
   const addArea=(suffix,cwd)=>{w.h.tabs.push({workspace_id:id,tab_id:`area-${suffix}`,label:'formal'});w.h.panes.push({workspace_id:id,tab_id:`area-${suffix}`,pane_id:`area-p-${suffix}`,terminal_id:`area-x-${suffix}`,cwd});};
   if(state==='absent'||state==='already-open'){
    w.h.workspaces=w.h.workspaces.filter(x=>x!==row);w.h.tabs=w.h.tabs.filter(x=>x.workspace_id!==id);w.h.panes=w.h.panes.filter(x=>x.workspace_id!==id);delete w.input.run.layout;
    if(state==='already-open'){
     const command=w.ports.command;
     w.ports.command=async args=>{const reply=await command(args);if(args[0]==='worktree'&&args[1]==='open')reply.result.status='already_open';return reply;};
    }
   }
   if(state==='duplicate-run')w.seed('duplicate','duplicate',w.c.cwd,w.c.common,true);
   if(state==='wrong-clone')row.worktree.repo_key=clones[1-target].common;
   if(state==='wrong-linked')row.worktree.is_linked_worktree=false;
   if(state==='area-shell-moved')addArea('moved',clones[1-target].cwd);
   if(state==='duplicate-area'){addArea('one',w.c.cwd);addArea('two',w.c.cwd);}
   if(state==='restarted-terminal')w.h.panes.find(p=>p.workspace_id===id).terminal_id='changed';
   if(state==='unique')addArea('existing',w.c.cwd);
   const forbidden=['duplicate-run','wrong-clone','wrong-linked','duplicate-area'].includes(state);
   if(forbidden){await assert.rejects(w.open(),e=>e.code==='herdr_layout_identity_changed',state);assert.deepEqual(w.mutate(),[],`${state}: uncertainty forbids effects`);}
   else {
    let result;await assert.doesNotReject(async()=>{result=await w.open();},`${registry}/${order}/${target}/${state}: approved live identity succeeds`);
    assert.equal(result.repoWorkspaceId,`parent-${target}`);
    assert.equal(w.h.workspaces.find(x=>x.workspace_id===result.workspaceId).worktree.checkout_path,w.c.cwd);
    const pane=w.h.panes.find(p=>p.pane_id===result.paneId);assert.equal(pane.workspace_id,result.workspaceId);if(state!=='area-shell-moved')assert.equal(pane.cwd,w.c.cwd);
    assert.equal(w.h.tabs.find(t=>t.tab_id===result.tabId).label,'formal');
    assert.ok(w.checkpoints>0,'verified returned identities checkpointed');
    if(state==='unique'){assert.equal(result.tabId,'area-existing');assert.deepEqual(w.mutate(),[]);}
    else if(state==='area-shell-moved'){assert.equal(result.tabId,'area-moved','the area tab is adopted although its shell moved');assert.deepEqual(w.mutate(),[]);}
    else if(state==='restarted-terminal'){assert.equal(result.root.terminalId,'changed');assert.equal(result.workspaceId,id);assert.deepEqual(w.mutate().map(a=>a.slice(0,2).join(':')),['tab:create']);}
    else assert.deepEqual(w.mutate().map(a=>a.slice(0,2).join(':')),['worktree:open','tab:create']);
    // Replay adopts the same workspace/area and does not allocate duplicates.
    const n=w.mutate().length;w.input.run.layout={...result,phase:'ready'};
    const again=await w.open();assert.equal(again.workspaceId,result.workspaceId);assert.equal(again.tabId,result.tabId);assert.equal(w.mutate().length,n);
   }
   await w.unchanged();
  }
  for(const order of [0,1])for(const target of [0,1])for(const occupied of [0,1,2,3]){
   const w=await world(order,target),parent=`parent-${target}`,run=`run-${target}`;
   w.h.workspaces=w.h.workspaces.filter(x=>![parent,run].includes(x.workspace_id));w.h.tabs=w.h.tabs.filter(x=>![parent,run].includes(x.workspace_id));w.h.panes=w.h.panes.filter(x=>![parent,run].includes(x.workspace_id));delete w.input.run.layout;
   // Free all candidate labels before occupying the declared prefix of the label list.
   const labels=['project',repository,`${repository}@${createHash('sha256').update(w.c.common).digest('hex').slice(0,12)}`];
   for(const row of w.h.workspaces)if(labels.includes(row.label))row.label='peer-preserved-label';
   const peerLabels=copy(w.h.workspaces);
   for(let i=0;i<occupied;i++)w.h.workspaces.push({workspace_id:`occupied-${i}`,label:labels[i]});
   if(occupied===3){await assert.rejects(w.open(),{code:'repository_label_unavailable'});assert.deepEqual(w.mutate(),[]);}
   else {const result=await w.open();const allocated=w.h.workspaces.find(x=>x.workspace_id===result.repoWorkspaceId);assert.equal(allocated.label,labels[occupied]);assert.equal(allocated.worktree.checkout_path,w.c.source);assert.deepEqual(w.mutate().map(a=>a.slice(0,2).join(':')),['workspace:create','worktree:open','tab:create']);}
   for(const row of peerLabels)assert.deepEqual(w.h.workspaces.find(x=>x.workspace_id===row.workspace_id),row,'allocation preserves peer labels and identities');
  }
  for(const order of [0,1])for(const target of [0,1])for(const state of ['idle','extra-tab','extra-pane','changed-terminal','changed-cwd','changed-clone','close-intent']){
   const w=await world(order,target),id=`run-${target}`,layout={...w.saved.layout,createdWorkspaceId:id,phase:state==='close-intent'?'close_intent':'ready'};
   if(state==='extra-tab')w.h.tabs.push({workspace_id:id,tab_id:'person-tab',label:'personal'});
   if(state==='extra-pane')w.h.panes.push({...w.h.panes.find(p=>p.workspace_id===id),pane_id:'person-pane'});
   if(state==='changed-terminal')w.h.panes.find(p=>p.workspace_id===id).terminal_id='changed';
   if(state==='changed-cwd')w.h.workspaces.find(x=>x.workspace_id===id).worktree.checkout_path=clones[1-target].cwd;
   if(state==='changed-clone')w.h.workspaces.find(x=>x.workspace_id===id).worktree.repo_key=clones[1-target].common;
   const close=()=>withHerdrLayoutLock(()=>closeHerdrRunLayout({runId:w.saved.runId,cwd:w.c.cwd,commonDir:w.c.common,layout},w.ports),w.ports);
   if(['idle','close-intent','changed-terminal'].includes(state)){await assert.doesNotReject(close());assert.deepEqual(w.mutate(),[['workspace','close',id]]);assert.equal(layout.phase,'closed');}
   else {await assert.rejects(close());assert.deepEqual(w.mutate(),[],`${state}: destructive cleanup forbidden`);}
   const n=w.mutate().length;
   assert.equal(await closeHerdrRepoLayoutIfIdle({repository,commonDir:w.c.common},w.ports),false,'adopted parent has no creation custody');
   assert.equal(w.mutate().length,n);await w.unchanged();
  }
  assert.equal(worlds,188);
 }finally{await rm(root,{recursive:true,force:true});}
});
