import test from 'node:test';
import assert from 'node:assert/strict';
import {formatStatus} from '../src/workflow-shortcuts.mjs';

test('merge waiting suggests observing the merge, while plan waiting suggests approval',()=>{
  const run={repo:'example/project',issue:{number:17,title:'Use two'},workflow:'small-change',state:'waiting'};
  assert.match(formatStatus([{...run,stage:{id:'wait-merge'},waitingFor:{decisions:[]}}]),/next: pdd workflow resume example\/project#17/);
  assert.match(formatStatus([{...run,stage:{id:'change'},waitingFor:{decisions:['approve','changes']}}]),/next: pdd workflow approve example\/project#17/);
});


test('W4 selectors bind subfolders and linked worktrees to their own common repo',async t=>{
  const fs=await import('node:fs/promises'),{tmpdir}=await import('node:os'),{join}=await import('node:path');
  const records=await import('../src/workflow-run-records.mjs'),{resolveRun}=await import('../src/workflow-shortcuts.mjs');
  const root=await fs.mkdtemp(join(tmpdir(),'pdd-shortcuts-'));t.after(()=>fs.rm(root,{recursive:true,force:true}));
  const ids=['11111111-1111-4111-8111-111111111111','22222222-2222-4222-8222-222222222222'];
  for(const [i,repo] of ['one/app','two/app'].entries()){
    const dir=join(root,String(i),'.git','pdd','workflows',ids[i]);await fs.mkdir(dir,{recursive:true});
    const state={runId:ids[i],name:'small-change',seq:1,repo,issue:{number:2,title:repo},root:join(root,String(i)),index:0,definitions:[{id:'plan',kind:'human'}],completed:[],pending:null};
    await fs.writeFile(join(dir,'journal.jsonl'),JSON.stringify({seq:1,state})+'\n');
    await records.appendRunIndex({runId:ids[i],repo,issue:state.issue,root:state.root,runDir:dir},{home:root});
  }
  const nested=join(root,'1','src','nested'),linked=join(root,'linked','nested');
  await fs.mkdir(nested,{recursive:true});await fs.mkdir(linked,{recursive:true});
  const metadata=join(root,'0','.git','worktrees','issue5');await fs.mkdir(metadata,{recursive:true});
  await fs.writeFile(join(root,'linked','.git'),`gitdir: ${metadata}\n`);await fs.writeFile(join(metadata,'commondir'),'../..\n');
  const localB=await resolveRun('2',{cwd:nested,waiting:true});assert.equal(localB.run.runId,ids[1]);
  const localA=await resolveRun('#2',{cwd:linked,waiting:true});assert.equal(localA.run.runId,ids[0]);
  const outside=await resolveRun('2',{cwd:root,waiting:true,records:{...records,readRunIndex:ports=>records.readRunIndex({...ports,home:root})}});
  assert.equal(outside.reason,'ambiguous');assert.equal(outside.runs.length,2);
});
