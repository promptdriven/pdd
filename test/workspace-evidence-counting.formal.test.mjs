import assert from 'node:assert/strict';
import test from 'node:test';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {ownStoryCount,recordEvidence} from '../src/workflow-runner.mjs';
import {renderJson} from '../src/runtime-output.mjs';
import {evidenceFixture} from './helpers/workspace-evidence-fixture.mjs';

// Independent oracle: import-authorized-workspace-evidence, Rules to check,
// and workflow-runner's "pdd's own results and agent notes" contract.
// Owned permission AND complete selected stage source make a fact eligible.
// Only the imported structured fact decides pass/fail; typed claims cannot.
const stages=['current','pr1'];
const custody=['owned','absent'];
const sources=['equal','changed-dependency'];
const facts=['passed','failed'];
const notes=['absent','opposite-known','invented'];

test('2899/2956 formal: counting requires owned stage source and ignores typed claims over 48 combinations',async t=>{
  let checked=0,passes=0,failures=0,unknown=0;
  for(const stage of stages)for(const fact of facts) {
    const f=await evidenceFixture(t),saved=f.receipt(f.clone);
    // Synthetic native result inputs, distinct from the immutable original fixture.
    const rows=saved.doc.rows.map(row=>({...row,state:fact,
      criteria:{passed:fact==='passed'?row.criteria.total:0,total:row.criteria.total},
      checks:{passed:fact==='passed'?10:0,total:10}}));
    const receipt=renderJson({repo:f.clone,sourceSha256:saved.doc.source_sha256,rows,exitCode:fact==='passed'?0:1});
    const file=join(f.base,'counting-fact.json'),bytes=JSON.stringify(receipt,null,2)+'\n';
    writeFileSync(file,bytes);
    if(stage==='pr1')f.pr1();
    const registration=await f.register(f.clone,stage);
    if(stage==='pr1')f.enterCode();
    assert.equal((await recordEvidence({ref:'17',cwd:f.root,summaryFile:file},f.ports)).exitCode,0,'structured receipt import');
    const baseline=f.read(),dependency=join(registration.sourceAnchor.root,'docs/menu.md');
    const original=readFileSync(dependency);
    for(const authority of custody)for(const source of sources)for(const note of notes) {
      writeFileSync(dependency,source==='equal'?original:Buffer.concat([original,Buffer.from('\nchanged\n')]));
      const run=structuredClone(baseline);
      if(authority==='absent')run.evidenceAssociations=[];
      if(note!=='absent') {
        const summary=note==='invented'?'Prompt tests (invented): ✓ 99 of 99 criteria':
          `Prompt tests (place-order): ${fact==='passed'?'✗ 0':'✓ 3'} of 3 criteria`;
        // Both typed channels carry the exact owned fact's binding, deliberately hostile.
        const claim={at:9000,source:structuredClone(run.evidence[0].source),summary};
        run.runtimeHistory=[claim];run.done.verify={...claim,at:9001};
      }
      const before=JSON.stringify(run),label=`${stage}/${authority}/${source}/${fact}/${note}`;
      const eligible=authority==='owned'&&source==='equal';
      const count=ownStoryCount(run,{stage});
      assert.equal(count.pass,Number(eligible&&fact==='passed'),`counting conjunction pass: ${label}`);
      assert.deepEqual(count.failing,eligible&&fact==='failed'?['place-order']:[],`counting conjunction failure: ${label}`);
      assert.equal(count.total,note==='invented'?2:1,`typed-only Story inventory: ${label}`);
      const expectedUnknown=[...(!eligible?['place-order']:[]),...(note==='invented'?['invented']:[])].sort();
      assert.deepEqual([...(count.unknown??[])].sort(),expectedUnknown,`counting conjunction unknown: ${label}`);
      if(stage==='pr1')assert.equal(ownStoryCount(run).pass,0,`PR 1 cannot become current: ${label}`);
      assert.equal(JSON.stringify(run),before,`counting leaves run unchanged: ${label}`);
      assert.equal(readFileSync(file,'utf8'),bytes,`original result bytes: ${label}`);
      assert.equal(readFileSync(saved.file,'utf8'),saved.bytes,`original fixture bytes: ${label}`);
      checked++;passes+=count.pass;failures+=count.failing.length;unknown+=(count.unknown??[]).length;
    }
    writeFileSync(dependency,original);
  }
  assert.deepEqual({checked,passes,failures,unknown},{checked:48,passes:6,failures:6,unknown:52});
  t.diagnostic('2899/2956 counting bounded: 48 combinations; 6 passing facts; 6 failing facts; 52 unknown Story observations (including typed-only names).');
});
