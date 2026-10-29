// Independent bounded oracle: user_stories/workflow-independent-checkouts.md, Rules to check.
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtemp,mkdir,writeFile,readFile,rm,realpath} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {openHerdrRunLayout,closeHerdrRunLayout,closeHerdrRepoLayoutIfIdle} from '../src/workflow-herdr-layout.mjs';
const copy=x=>structuredClone(x);
const repository='promptdriven/pdd';
const states=['valid','legacy-label','parent-intent','run-intent','wrong-cwd','wrong-common','wrong-binding','wrong-label','duplicate-owner','parent-forged','run-forged','root-forged'];
// Exhaustive families: 2 registry orders × 2 selected clones × 12 open states = 48;
// 2 orders × 2 clones × 6 cleanup states = 24; 2 orders × 2 clones × 2 labels = 8.
// Total 80 independent seeded worlds. No arbitrary schedules/crashes/processes claim.
test('bounded public checkout ownership: all 80 seeded worlds',async()=>{
 const root=await mkdtemp(join(tmpdir(),'pdd-formal-ownership-'));
 try {
  const clones=[];
  for(const name of ['A','B']){
   const source=join(root,name),cwd=join(root,`${name}-run`);await mkdir(source);
   const git=args=>execFileSync('git',args,{cwd:source,stdio:'pipe'});
   git(['init']);git(['remote','add','origin','https://github.com/promptdriven/pdd.git']);
   git(['-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','--allow-empty','-m','fixture']);
   git(['worktree','add','-b',`run-${name}`,cwd]);
   clones.push({source:await realpath(source),cwd:await realpath(cwd),common:await realpath(join(source,'.git'))});
  }
  let worlds=0;
  async function world(order,target){
   const directory=join(root,`state-${worlds++}`);await mkdir(directory);
   const repos=clones.map((c,i)=>({key:repository,repository,sourceRoot:c.source,commonDir:c.common,phase:'ready',workspaceId:`parent-${i}`,rootTabId:`pt-${i}`,rootPaneId:`pp-${i}`,rootTerminalId:`px-${i}`}));
   const runs=clones.map((c,i)=>({runId:`run-${i}`,repoWorkspaceId:`parent-${i}`,commonDir:c.common,cwd:c.cwd,label:'pdd#2531 bug',phase:'ready',workspaceId:`run-w-${i}`,rootTabId:`rt-${i}`,rootPaneId:`rp-${i}`,rootTerminalId:`rx-${i}`}));
   const rows=[...repos.map((r,i)=>({workspace_id:r.workspaceId,label:i?'qualified-B':'pdd',worktree:{checkout_path:r.sourceRoot,repo_key:r.commonDir,is_linked_worktree:false}})),...runs.map(r=>({workspace_id:r.workspaceId,label:r.label,worktree:{checkout_path:r.cwd,repo_key:r.commonDir,is_linked_worktree:true}}))];
   const panes=new Map([...repos.map(r=>[r.workspaceId,[{workspace_id:r.workspaceId,tab_id:r.rootTabId,pane_id:r.rootPaneId,terminal_id:r.rootTerminalId,cwd:r.sourceRoot}]]),...runs.map(r=>[r.workspaceId,[{workspace_id:r.workspaceId,tab_id:r.rootTabId,pane_id:r.rootPaneId,terminal_id:r.rootTerminalId,cwd:r.cwd}]])]);
   const tabs=new Map([...panes].map(([w,p])=>[w,p.map(x=>({tab_id:x.tab_id}))]));
   const registry={version:1,repositories:order?[...repos].reverse():repos,runs};
   const calls=[],events=[];let serial=0,lose=false;
   const file=join(directory,'registry.json');
   const save=()=>writeFile(file,JSON.stringify(registry));
   const load=async()=>JSON.parse(await readFile(file,'utf8'));
   const command=async args=>{
    const [kind,action]=args;const op=`${kind}:${action}`;
    if(action==='list'){
     const value=kind==='workspace'?rows:kind==='pane'?panes.get(args[3]):tabs.get(args[3]);
     return {id:`cli:${op}`,result:{type:`${kind}_list`,[`${kind}s`]:copy(value??[])}};
    }
    calls.push(copy(args));events.push(op);
    // Durable intent must be observable before the external mutation.
    const durable=await load();
    if(op==='workspace:create')assert.ok(durable.repositories.some(r=>r.phase==='intent'));
    if(op==='worktree:open')assert.ok(durable.runs.some(r=>r.phase==='intent'));
    if(op==='workspace:close')assert.ok([...durable.repositories,...durable.runs].some(r=>r.workspaceId===args[2]&&r.phase==='close_intent'));
    assert.equal(events.at(-2),'checkpoint','checkpoint precedes every mutation');
    if(op==='workspace:close'){
     if(lose)throw Object.assign(new Error('lost close reply'),{code:'lost_reply'});
     rows.splice(rows.findIndex(w=>w.workspace_id===args[2]),1);return {id:`cli:${op}`,result:{type:'ok'}};
    }
    const w=`opaque-${++serial}`,t=`${w}-t`,p=`${w}-p`,x=`${w}-x`;
    const cwd=args[args.indexOf(op==='workspace:create'?'--cwd':'--path')+1];
    const label=args[args.indexOf('--label')+1];
    if(op==='tab:create')return {id:`cli:${op}`,result:{tab:{tab_id:t},root_pane:{pane_id:p,terminal_id:x}}};
    const c=clones[target];rows.push({workspace_id:w,label,worktree:{checkout_path:cwd,repo_key:c.common,is_linked_worktree:kind==='worktree'}});
    panes.set(w,[{workspace_id:w,tab_id:t,pane_id:p,terminal_id:x,cwd}]);tabs.set(w,[{tab_id:t}]);
    return {id:`cli:${op}`,result:{workspace:{workspace_id:w},tab:{tab_id:t},root_pane:{pane_id:p,terminal_id:x}}};
   };
   return {directory,repos,runs,rows,panes,tabs,registry,calls,events,save,load,setLose:()=>{lose=true;},ports:{directory,command,checkpoint:async()=>{events.push('checkpoint');}},input:{repository,issueNumber:2531,runId:`run-${target}`,workflowName:'bug',stageId:'formal',sourceRoot:clones[target].source,commonDir:clones[target].common,cwd:clones[target].cwd}};
  }
  const snapshot=(w,peer)=>({repo:copy(w.repos[peer]),run:copy(w.runs[peer]),row:copy(w.rows.filter(r=>[w.repos[peer].workspaceId,w.runs[peer].workspaceId].includes(r.workspace_id))),panes:copy([...w.panes].filter(([id])=>[w.repos[peer].workspaceId,w.runs[peer].workspaceId].includes(id)))});
  async function peerUnchanged(w,peer,before){
   assert.deepEqual(snapshot(w,peer),before,'peer external identity preserved');
   const saved=await w.load();assert.deepEqual(saved.repositories.find(r=>r.workspaceId===before.repo.workspaceId),before.repo);assert.deepEqual(saved.runs.find(r=>r.runId===before.run.runId),before.run);
  }
  for(const order of [0,1])for(const target of [0,1])for(const state of states){
   const w=await world(order,target),r=w.runs[target],p=w.repos[target],peer=1-target;
   if(state==='legacy-label')r.label='#2531 bug';
   if(state==='parent-intent')p.phase='intent';
   if(state==='run-intent')r.phase='intent';
   if(state==='wrong-cwd')r.cwd=clones[peer].cwd;
   if(state==='wrong-common')r.commonDir=clones[peer].common;
   if(state==='wrong-binding')r.repoWorkspaceId=w.repos[peer].workspaceId;
   if(state==='wrong-label')r.label='pdd#999 feature';
   if(state==='duplicate-owner')w.registry.repositories.push(copy(p));
   if(state==='parent-forged')w.rows.find(x=>x.workspace_id===p.workspaceId).worktree.repo_key=clones[peer].common;
   if(state==='run-forged')w.rows.find(x=>x.workspace_id===r.workspaceId).worktree.checkout_path=clones[peer].cwd;
   if(state==='root-forged')w.panes.get(r.workspaceId)[0].terminal_id='forged';
   await w.save();const before=await w.load(),peerBefore=snapshot(w,peer);
   if(['valid','legacy-label'].includes(state)){
    let result;await assert.doesNotReject(async()=>{result=await openHerdrRunLayout(w.input,w.ports);},`${order}/${target}/${state}: exact pair succeeds`);
    assert.equal(result.repoWorkspaceId,p.workspaceId);assert.equal(result.workspaceId,r.workspaceId);assert.deepEqual(w.calls.map(a=>a.slice(0,2)),[['tab','create']]);
   }else{
    await assert.rejects(openHerdrRunLayout(w.input,w.ports),e=>typeof e.code==='string',state);assert.deepEqual(w.calls,[]);assert.deepEqual(await w.load(),before);
   }
   await peerUnchanged(w,peer,peerBefore);
  }
  for(const order of [0,1])for(const target of [0,1])for(const state of ['idle','active','extra-tab','extra-pane','forged','lost-close']){
   const w=await world(order,target),r=w.runs[target],p=w.repos[target],peer=1-target;const before=snapshot(w,peer);
   if(state!=='active'){
    await w.save();await closeHerdrRunLayout({runId:r.runId,cwd:r.cwd,layout:{workspaceId:r.workspaceId,repoWorkspaceId:p.workspaceId}},w.ports);
   }
   if(state==='extra-tab')w.tabs.get(p.workspaceId).push({tab_id:'person-tab'});
   if(state==='extra-pane')w.panes.get(p.workspaceId).push({...w.panes.get(p.workspaceId)[0],pane_id:'person-pane'});
   if(state==='forged')w.rows.find(x=>x.workspace_id===p.workspaceId).worktree.repo_key='forged';
   if(state==='lost-close')w.setLose();
   if(state==='active')await w.save();w.calls.length=0;
   const input={repository,commonDir:clones[target].common};
   if(['forged','lost-close'].includes(state)){
    await assert.rejects(closeHerdrRepoLayoutIfIdle(input,w.ports));
    if(state==='lost-close'){const n=w.calls.length;assert.equal(await closeHerdrRepoLayoutIfIdle(input,w.ports),false);assert.equal(w.calls.length,n,'uncertain close never repeated');}
   }else assert.equal(await closeHerdrRepoLayoutIfIdle(input,w.ports),state==='idle');
   assert.deepEqual(w.calls,state==='idle'||state==='lost-close'?[['workspace','close',p.workspaceId]]:[]);
   await peerUnchanged(w,peer,before);
  }
  for(const order of [0,1])for(const target of [0,1])for(const occupied of [false,true]){
   const w=await world(order,target),peer=1-target,p=w.repos[target],r=w.runs[target],before=snapshot(w,peer);
   w.registry.repositories=w.registry.repositories.filter(x=>x!==p);w.registry.runs=w.registry.runs.filter(x=>x!==r);w.rows.splice(w.rows.findIndex(x=>x.workspace_id===p.workspaceId),1);w.rows.splice(w.rows.findIndex(x=>x.workspace_id===r.workspaceId),1);
   const label=`${repository}@${createHash('sha256').update(clones[target].common).digest('hex').slice(0,12)}`;
   if(occupied)w.rows.push({workspace_id:'stranger',label});await w.save();
   const saved=await w.load();
   if(occupied){await assert.rejects(openHerdrRunLayout(w.input,w.ports),{code:'repository_label_unavailable'});assert.deepEqual(w.calls,[]);assert.deepEqual(await w.load(),saved);}
   else {
    await assert.doesNotReject(()=>openHerdrRunLayout(w.input,w.ports),'independent namespace allocates despite earlier same-repository peer');
    assert.deepEqual(w.calls.map(a=>a.slice(0,2)),[['workspace','create'],['worktree','open'],['tab','create']]);assert.equal(w.calls[0][w.calls[0].indexOf('--label')+1],label);
   }
   await peerUnchanged(w,peer,before);
  }
  assert.equal(worlds,80);
 }finally{await rm(root,{recursive:true,force:true});}
});
