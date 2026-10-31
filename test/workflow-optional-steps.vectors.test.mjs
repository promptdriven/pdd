import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {vectors,fixture,clone,sha,packageRoot,jsonPointer,assertCheck,DEFECT} from './workflow-optional-steps.fixture.mjs';
// Approved JSON is read unchanged. All 373 result/world/calls checks have mappings below.
// Three preservation-only actions run inside the changed-behavior parent, without claiming they fail alpha alone.
test('2756: replay every approved optional-step scenario against production stepDone',async t=>{
 const bytes=readFileSync(join(packageRoot,'test/runtime/workflow-optional-steps.json'));
 assert.equal(sha(bytes),'16a112610ccebeea73219843c6137c500da9cfab61736e1eabc5d49161b7d07d','Approved vectors changed');
 const world=clone(vectors.initial_world),fixtures=new Map(),report=[];let checks=0;
 for(const row of world.runs){const run=JSON.parse(row.record);fixtures.set(row.cwd,fixture(t,run));}
 for(const step of vectors.steps)await t.test(step.step_id,async()=>{
  assert.equal(step.operation,'stepDone','Not replayed: unknown production boundary');
  const f=fixtures.get(step.input.cwd);assert.ok(f,'Replay setup requires a real saved v:1 run');
  const next=world.snapshots.find(row=>row.notePath===`${step.input.cwd}/notes/${step.input.step==='understand'?'understand':'prompt-story'}.md`);
  f.snapshot=next?.snapshot??{note:'',error:'missing',complete:false,files:[]};
  f.snapshotByPath=notePath=>world.snapshots.find(row=>row.notePath===notePath)?.snapshot??{note:'',error:'missing',complete:false,files:[]};
  f.reply=world.replies.find(row=>row.root===step.input.cwd)?.reply;
  const saves=f.record().journalSeq??0,people=f.personReads,choosers=f.chooserCalls;
  const result=await f.done(step.input.step,step.input.summary);
  assert.doesNotMatch(result.message,/works only in a run worktree/,`${DEFECT} Invalid replay setup`);
  world.runs.find(row=>row.cwd===step.input.cwd).record=f.compact();
  const calls={resources:{'workflow-runner-runStore-save':(f.record().journalSeq??0)-saves,'workflow-runner-person-readApprovalEvidence':f.personReads-people},internal:{'simulate-command':f.chooserCalls-choosers}};
  const failures=[];
  for(const check of step.checks){
   assert.ok(['result','world','calls'].includes(check.target),`Not replayed: target ${check.target}`);
   const actual=jsonPointer({result,world,calls}[check.target],check.path);let error;
   try{assertCheck(actual,check,step.step_id);}catch(cause){error=cause.message;failures.push(error);}
   report.push({case:step.step_id,criterion:check.criterion_id,target:check.target,path:check.path,operation:check.op,expected:check.value,got:actual===undefined?'<undefined>':actual,result:error?'fail':'pass',...(error?{error}:{})});checks++;
  }
  assert.equal(failures.length,0,`${DEFECT} ${step.step_id}: ${failures.length}/${step.checks.length} assertions failed. ${failures[0]??''}`);
 });
 if(process.env.PDD_OPTIONAL_REPLAY_REPORT)writeFileSync(process.env.PDD_OPTIONAL_REPLAY_REPORT,JSON.stringify({scenarioSha256:sha(bytes),executed:checks,notReplayed:[],checks:report},null,2)+'\n');
 assert.equal(checks,373,`${DEFECT} Every approved check must execute`);
});
