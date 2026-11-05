// Synthetic native integration controls for the existing 2899 and 2956 contracts.
import assert from 'node:assert/strict';
import test from 'node:test';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {recordEvidence,ownStoryCount,storyEvidence,runStatus} from '../src/workflow-runner.mjs';
import {evidenceFixture,assertProtected} from './helpers/workspace-evidence-fixture.mjs';

const claim = (source, summary, at) => ({source,summary,at});

test('2899/2956: owned associated receipt counts while source-bound agent claims stay unverified',async t=>{
  const f=await evidenceFixture(t),saved=f.receipt(f.clone);await f.register(f.clone);
  assert.equal((await recordEvidence({ref:'17',cwd:f.root,summaryFile:saved.file},f.ports)).exitCode,0);
  const run=f.read(),source=run.evidence[0].source;
  run.runtimeHistory=[claim(source,'Prompt tests (place-order): ✗ 0 of 3 criteria\nPrompt tests (invented): ✓ 99 of 99 criteria',9000)];
  run.done.verify=claim(source,'Prompt tests (place-order): ✗ 0 of 3 criteria',9001);f.save(run);
  const before=readFileSync(f.status,'utf8');
  const status=JSON.parse((await runStatus({ref:'17',cwd:f.root,json:true},f.ports)).message).runs[0];
  assert.equal(status.stories.pass,1);assert.equal(status.stories.total,2);
  assert.deepEqual(status.stories.failing,[]);assert.deepEqual(status.stories.unknown,['invented']);
  assert.deepEqual(storyEvidence(f.read()).map(row=>[row.story,row.pass,row.current]),[['place-order',true,true]]);
  assert.equal(readFileSync(f.status,'utf8'),before);assert.equal(readFileSync(saved.file,'utf8'),saved.bytes);
  // Source equality cannot repair lost independently owned registration.
  const unregistered=f.read();unregistered.evidenceAssociations=[];f.save(unregistered);
  assert.equal(ownStoryCount(f.read()).pass,0);assert.equal(storyEvidence(f.read())[0].current,false);
  f.save(run);writeFileSync(join(f.clone,'docs/menu.md'),'Changed selected dependency.\n');
  assert.equal(ownStoryCount(f.read()).pass,0);assert.equal(storyEvidence(f.read())[0].current,false);
});

test('2899/2956: frozen PR 1 stays historical in both status forms and agent claims cannot promote it',async t=>{
  const f=await evidenceFixture(t),saved=f.receipt(f.clone);f.pr1();await f.register(f.clone,'pr1');f.enterCode();
  assert.equal((await recordEvidence({ref:'17',cwd:f.root,summaryFile:saved.file},f.ports)).exitCode,0);
  const run=f.read();run.done.verify=claim(run.evidence[0].source,'Prompt tests (place-order): ✓ 3 of 3 criteria',9000);f.save(run);
  const before=readFileSync(f.status,'utf8');
  const json=JSON.parse((await runStatus({ref:'17',cwd:f.root,json:true},f.ports)).message).runs[0];
  assert.equal(json.stories.pass,0);assert.equal(json.pr1Stories.pass,1);
  const text=(await runStatus({ref:'17',cwd:f.root},f.ports)).message;
  assert.match(text,/^Stories: 0 of 1 Stories pass/m);assert.match(text,/^PR 1 Stories: 1 of 1 Stories pass$/m);
  assert.equal(storyEvidence(f.read())[0].current,false);assert.equal(readFileSync(f.status,'utf8'),before);
  assertProtected(run,f.read());assert.deepEqual(f.read().evidence[0].receipt,saved.doc);
});

test('2899/2956: PDD-owned partial batches retain source checks and typed passes never replace a failed fact',async t=>{
  const f=await evidenceFixture(t),saved=f.receipt(f.root),run=f.read();
  run.pddHistory=[{kind:'pdd test',batch:'synthetic-owned-batch',at:100,sourceSha256:saved.doc.source_sha256,tests:saved.doc.rows.map(row=>row.test),
    stories:['Prompt tests (place-order): ✗ 0 of 3 criteria'],summary:'Prompt tests: ✗ 0 of 3 criteria'}];
  run.done.verify=claim({kind:'runtime-capture-v1',sha256:saved.doc.source_sha256,tests:run.pddHistory[0].tests},'Prompt tests (place-order): ✓ 3 of 3 criteria',200);
  assert.deepEqual(ownStoryCount(run),{pass:0,total:1,failing:['place-order']});
  assert.equal(storyEvidence(run)[0].pass,false);assert.equal(storyEvidence(run)[0].current,true);
  run.pddHistory.push({...run.pddHistory[0],batch:'synthetic-owned-recheck',at:300,stories:['Prompt tests (place-order): ✓ 3 of 3 criteria']});
  assert.equal(ownStoryCount(run).pass,1);
  writeFileSync(join(f.root,'docs/menu.md'),'Later authored source.\n');
  assert.equal(ownStoryCount(run).pass,0);assert.deepEqual(ownStoryCount(run).unknown,['place-order']);
});
