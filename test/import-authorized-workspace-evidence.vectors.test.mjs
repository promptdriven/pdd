import assert from 'node:assert/strict';
import test from 'node:test';
import {readFileSync,writeFileSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {recordEvidence,storyCount} from '../src/workflow-runner.mjs';
import {evidenceFixture,assertProtected,selection} from './helpers/workspace-evidence-fixture.mjs';

// Execute the unchanged approved operations/checks in order. Isolated native
// worlds are those in the approved native plan; repeat shares the clone world.
const vectorPath=new URL('./cases/import-authorized-workspace-evidence.scenario',import.meta.url);
const original=readFileSync(vectorPath),scenario=JSON.parse(original);
test('2899 replay: original selected workspace evidence through recordEvidence',async t=>{
  let repeat;const owner=t;
  for(const step of scenario.steps)await t.test(step.step_id,async t=>{
    const id=step.step_id, f=id==='repeat-original'?repeat.f:await evidenceFixture(owner);
    let producer=id.includes('nested')||id==='changed-dependency'?f.nested:id==='same-worktree'||id==='same-root-pr1-after-code'?f.root:f.clone;
    let saved;
    if(id==='repeat-original')saved=repeat.saved;
    else saved=f.receipt(producer);
    if(id==='extra-selection')saved=f.receipt(producer,[...selection,'tests/unknown-item.json']);
    const pr1=['pr1-after-code','same-root-pr1-after-code','missing-anchor','wrong-anchor','changed-anchor'].includes(id);
    if(pr1) {
      f.pr1();
      if(id==='same-root-pr1-after-code'){f.enterCode();await f.register(producer,'pr1');}
      else {await f.register(producer,'pr1');f.enterCode();}
    } else if(!['same-worktree','unassociated-clone','unassociated-nested','repeat-original'].includes(id))await f.register(id==='wrong-root'?f.other:producer);
    if(id==='authorized-clone')repeat={f,saved};
    if(id==='wrong-run'||id==='wrong-owner'){const r=f.read();r.evidenceAssociations[0][id==='wrong-run'?'runId':'repo']='foreign';f.save(r);}
    if(id==='changed-story')writeFileSync(join(producer,'user_stories/place-order.md'),'changed Story');
    if(id==='changed-dependency')writeFileSync(join(producer,'docs/menu.md'),'changed dependency');
    if(id==='changed-authored-source')writeFileSync(join(f.root,'user_stories/place-order.md'),'changed authored Story');
    if(id==='missing-source')rmSync(join(producer,'docs/menu.md'));
    if(id==='missing-anchor')rmSync(f.read().evidenceAssociations[0].sourceAnchor.root,{recursive:true});
    if(id==='changed-anchor')writeFileSync(join(f.read().evidenceAssociations[0].sourceAnchor.root,'user_stories/place-order.md'),'changed frozen Story');
    if(id==='wrong-anchor'){const r=f.read();r.evidenceAssociations[0].sourceAnchor.head='f'.repeat(40);f.save(r);}
    const before=readFileSync(f.status,'utf8'),head=f.git(f.root,'rev-parse','HEAD'),gitStatus=f.git(f.root,'status','--porcelain');
    assert.equal(step.operation,'recordEvidence');
    const result=await recordEvidence({...step.input,summaryFile:saved.file,cwd:f.root},f.ports);
    for(const check of step.checks){assert.equal(check.target,'result');assert.equal(check.op,'equals');
      const got=check.path.split('/').slice(1).reduce((value,key)=>value[key],result);
      assert.deepEqual(got,check.value,`2899 ${id} ${check.criterion_id}: ${result.message}`);}
    assert.equal(readFileSync(saved.file,'utf8'),saved.bytes,'Original receipt bytes');
    assert.equal(f.git(f.root,'rev-parse','HEAD'),head);assert.equal(f.git(f.root,'status','--porcelain'),gitStatus);
    if(result.exitCode===0) {
      const after=f.read();assertProtected(JSON.parse(before),after);assert.deepEqual(after.evidence.at(-1).receipt,saved.doc,'Every original provenance/expected/source field');
      if(pr1){assert.equal(after.evidence.at(-1).association.stage,'pr1');assert.equal(storyCount(after).pass,0);assert.equal(storyCount(after,{stage:'pr1'}).pass,1);}
    } else assert.equal(readFileSync(f.status,'utf8'),before,'Refusal preserves exact status/evidence bytes');
  });
  assert.deepEqual(readFileSync(vectorPath),original,'Approved scenario bytes remain unchanged');
});
