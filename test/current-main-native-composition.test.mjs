import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {evidenceFixture} from './helpers/workspace-evidence-fixture.mjs';
import {readRunResults} from '../src/workflow-results.mjs';
import {readEvidenceEligibility,ownStoryCount,storyEvidence} from '../src/workflow-runner.mjs';

const tests=['tests/place-order.json','tests/unknown-item.json'];
function savedBatch(f,receipt,association=null) {
  const env={HOME:join(f.base,'home'),PDD_STATE_DIR:join(f.base,'runtime')};
  const batch='20261105-070000-abcd',folder=join(env.PDD_STATE_DIR,'batches',batch);
  mkdirSync(folder,{recursive:true});
  const rows=receipt.doc.rows.map((row,index)=>index===1
    ? {...row,unsent:true,state:'not_run',summary_line:`Prompt tests (${row.story}): no verdict`}
    : {...row,unsent:false});
  writeFileSync(join(folder,'batch.json'),JSON.stringify({batch,root:receipt.doc.repo,intent:'check',created_at:'2026-11-05T07:00:00Z',source_sha256:receipt.doc.source_sha256,rows,...(association?{association}: {})}));
  writeFileSync(join(folder,'summary.json'),JSON.stringify({...receipt.doc,rows}));
  const workspace=input=>readEvidenceEligibility(input,{allRuns:()=>[f.read()]});
  return {env,read:()=>readRunResults({root:f.root},{env,workspace})};
}

test('combined PDD batch reader admits the full registered selection including an unsent row',async t=>{
  const f=await evidenceFixture(t),receipt=f.receipt(f.clone,tests);
  await f.register(f.clone,'current',tests);
  const saved=savedBatch(f,receipt),before=readFileSync(f.status);
  const result=saved.read().find(row=>row.kind==='pdd test');
  assert.ok(result,'FULL ORIGINAL SELECTION MUST REACH THE CANONICAL OWNER');
  assert.deepEqual(result.tests,tests);
  assert.equal(result.sourceSha256,receipt.doc.source_sha256);
  assert.equal(result.stage,'current');
  const run=f.read();run.pddHistory=[result];
  assert.equal(ownStoryCount(run).pass,1);
  writeFileSync(join(f.clone,tests[1]),readFileSync(join(f.clone,tests[1]),'utf8')+'\n');
  assert.equal(saved.read().length,0,'An unsent selected test cannot disappear from source revalidation');
  assert.equal(ownStoryCount(run).pass,0,'Stored PDD history must revalidate the original producer');
  assert.deepEqual(readFileSync(f.status),before);
});

test('combined PDD-owned PR1 batch keeps historical scope even when current source bytes match',async t=>{
  const f=await evidenceFixture(t),receipt=f.receipt(f.root,tests);f.pr1();
  await f.register(f.root,'pr1',tests);
  const run=f.read();run.area=1;run.state='running';f.save(run);
  const saved=savedBatch(f,receipt,{runId:run.runId,stage:'pr1'}),before=readFileSync(f.status);
  const result=saved.read().find(row=>row.kind==='pdd test');assert.ok(result);
  assert.equal(result.stage,'pr1');assert.equal(result.source,'current');
  run.pddHistory=[result];
  assert.equal(ownStoryCount(run).pass,0,'HISTORICAL PDD BATCH MUST NOT BECOME CURRENT CODE PROOF');
  assert.equal(ownStoryCount(run,{stage:'pr1'}).pass,1);
  assert.ok(storyEvidence(run).every(row=>row.current===false));
  const lost={...run,evidenceAssociations:[]};
  assert.equal(ownStoryCount(lost,{stage:'pr1'}).pass,0,'A saved stage label cannot replace owned registration');
  assert.deepEqual(readFileSync(f.status),before);
});
