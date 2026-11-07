// This file uses only existing APIs. Run it FIRST in old-code proof commands:
// old code must fail the real CLI selection assertion before new API imports.
import test from 'node:test';
import assert from 'node:assert/strict';
import {nativeFixture,put} from './helpers/native-cli-fixture.mjs';
test('native Story selection reaches native evidence assessment before authentication',async t=>{
  const f=await nativeFixture(t);
  for(const args of [['lint','native','--json'],['lint','--local','native','--json'],['lint',f.storyPath,'--json'],['lint','user_stories','--json']]) {
    const result=f.command(...args);
    assert.equal(result.status,1,`NATIVE STORY SELECTION MUST REACH NATIVE EVIDENCE: ${result.stderr}`);
    const saved=JSON.parse(result.stdout);
    assert.equal(saved.native_assessments.length,1);
    assert.equal(saved.native_assessments[0].assessment.storyNativeProof,'none');
    assert.equal(saved.native_assessments[0].assessment.criteria[0].id,'AC1');
  }
  const control=f.command('test','--files','native');assert.equal(control.status,2,'native declaration grants no Runtime execution capability');
  put(f.parent,'report.tap','TAP version 13\nok 1 - required A\n1..1\n');
  put(f.parent,'import.json',{schema:'pdd.native-evidence-import.v1',profileId:'native',storyPath:f.storyPath,originals:[{path:'report.tap',role:'report'}]});
  const before=f.readRun(), imported=f.command('workflow','evidence','17','--summary',`${f.parent}/import.json`);
  assert.equal(imported.status,0,`NATIVE ORIGINAL INTAKE MUST RETAIN ORIGINAL BYTES: ${imported.stdout}${imported.stderr}`);
  const after=f.readRun();assert.equal(after.evidence.length,(before.evidence?.length??0)+1);
  for(const key of ['state','gate','done','decisions','area','pr'])assert.deepEqual(after[key],before[key]);
  assert.equal(after.evidence.at(-1).native.intake.admission,'unverified');
});
