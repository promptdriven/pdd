import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {pathToFileURL} from 'node:url';
import {nativeFixture,put} from './helpers/native-cli-fixture.mjs';
import {captureSource} from '../src/runtime-seam.mjs';
const {assessNativeEvidence,prepareNativeEvidence}=await import(process.env.PDD_FORMAL_MODULE_ROOT
  ? pathToFileURL(join(process.env.PDD_FORMAL_MODULE_ROOT,'src/workflow-results.mjs'))
  : new URL('../src/workflow-results.mjs',import.meta.url));

// Oracle: both approved native Stories' Rules to check. The unchanged supplied
// positive context supplies identities, never the expected proof decision.
test('bounded native proof requires execution, prerequisites, review, source and current Story facts',async t=>{
  const scenario=JSON.parse(readFileSync(new URL('./runtime/native-validation-profile.json',import.meta.url)));
  const supplied=scenario.simulation['native.read_context'].cases.find(row=>row.args.runId==='complete-optional-skip');
  const seed=JSON.parse(supplied.result.content);
  let checked=0;
  for(const execution of ['pass','failed','skipped','todo','not-completed','unknown-start','missing','pass-and-skip'])
  for(const gate of ['passed','missing'])
  for(const fixture of ['verified','missing'])
  for(const review of ['approved','missing'])
  for(const source of ['current','stale','unknown'])
  for(const story of ['valid','missing','unknown','empty','unmapped'])
  for(const optionalSkip of [false,true])
  for(const origin of ['external-machine','agent-note','modeled']) {
    const context=structuredClone(seed),required=context.report.observations.slice(0,2);
    context.report.observations=required;
    if(execution==='missing')required.pop();
    else if(execution==='unknown-start')required[1].started=null;
    else if(execution==='pass-and-skip')required.push({...required[1],occurrenceId:'bounded-duplicate',outcome:'skipped',started:false,skipReason:'required fixture unavailable'});
    else if(execution!=='pass')required[1].outcome=execution;
    if(optionalSkip)context.report.observations.push(structuredClone(seed.report.observations[2]));
    if(gate==='missing')context.report.gates=[];
    if(fixture==='missing')context.report.prerequisites=[];
    context.protected.review=review;
    if(source==='stale')context.candidate.sourceId='bounded-other-source';
    if(source==='unknown')context.candidate.sourceId=null;
    if(story==='missing')delete context.story;
    if(story==='unknown')context.story=null;
    if(story==='empty')context.story.criteria=[];
    if(story==='unmapped')context.protected.mappings=[];
    context.intake.origin=origin;
    const complete=execution==='pass'&&gate==='passed'&&fixture==='verified'&&review==='approved'&&source==='current'&&origin==='external-machine';
    const expectedProfile=complete?'qualified-external':'none';
    const expectedStory=complete&&story==='valid'?'qualified-external':'none';
    const label=JSON.stringify({execution,gate,fixture,review,source,story,optionalSkip,origin});
    const actual=await assessNativeEvidence(supplied.args,{readNativeContext:async()=>({content:JSON.stringify(context)})});
    assert.equal(actual.profileNativeProof,expectedProfile,`PROFILE PROOF REQUIRES ALL REQUIRED FACTS ${label}`);
    assert.equal(actual.storyNativeProof,expectedStory,`STORY PROOF REQUIRES CURRENT MAPPING ${label}`);
    assert.deepEqual(actual.optionalSkippedIds,optionalSkip?[seed.report.observations[2].testId]:[],`OPTIONAL SKIP MUST STAY VISIBLE ${label}`);
    if(optionalSkip)assert.equal(actual.observations.at(-1).skipReason,seed.report.observations[2].skipReason);
    checked++;
  }
  assert.equal(checked,5760);
  t.diagnostic(`Checked all ${checked} combinations; optional skips retained; complete profile assessed separately from whole Story.`);
});

test('actual default native reader requires the saved workflow gate decision as well as its journal event',async t=>{
  const f=await nativeFixture(t),dir=join(f.parent,'originals');
  const save=(name,value)=>put(dir,name,value),summaryFile=join(dir,'import.json');
  save('import.json',{schema:'pdd.native-evidence-import.v1',profileId:'native',storyPath:f.storyPath,originals:[{role:'report',path:'report.json'},{role:'source',path:'source.json'},{role:'selection',path:'selection.json'},{role:'execution',path:'execution.json'}]});
  save('report.json',{producer:'synthetic-test-runner',producerVersion:'1',runner:'synthetic-suite',runnerVersion:'1',runtimeVersion:'node-22',capture:{selectionComplete:true,terminalSeen:true,processEnded:true,eventRef:'original-report'},complete:true,exitCode:0,rows:[{occurrenceId:'a',testId:f.a,selected:true,started:true,outcome:'ok'},{occurrenceId:'b',testId:f.b,selected:true,started:true,outcome:'ok'}]});
  for(const name of ['source','selection','execution'])save(name+'.json',{});
  const selectors={root:f.root,runDir:f.runDir,runId:f.readRun().runId,summaryFile};
  const first=prepareNativeEvidence(selectors),source=Object.fromEntries(['sourceId','implementationId','testsId'].map(key=>[key,first.assessment.identity[key]]));
  const tests=['source.mjs',f.testPath,f.promptPath],source_sha256=captureSource(f.root,{tests}).sha256;
  const registered=f.command('workflow','evidence-associate','17','--workspace',f.root,'--stage','current','--test',...tests);
  assert.equal(registered.status,0,registered.stderr);
  save('source.json',{producerRoot:f.root,tests,source_sha256,source,runId:f.readRun().runId,stage:'current'});
  save('selection.json',{sourceId:source.sourceId,stage:'current',complete:true,testIds:[f.a,f.b]});
  save('execution.json',{sourceId:source.sourceId,stage:'current',processEnded:true,exitCode:0,producer:'synthetic-test-runner',producerVersion:'1',runner:'synthetic-suite',runnerVersion:'1',runtimeVersion:'node-22'});
  const imported=f.command('workflow','evidence','17','--summary',summaryFile);assert.equal(imported.status,0,imported.stderr);
  const positive=f.command('lint','native','--json');assert.equal(positive.status,0,positive.stderr);
  const positiveAssessment=JSON.parse(positive.stdout).native_assessments[0].assessment;
  assert.equal(positiveAssessment.storyNativeProof,'qualified-external','Matching actual gate/journal/originals must retain the positive control');
  const statusPath=join(f.runDir,'status.json'),run=f.readRun(),decision=run.decisions[0];
  assert.equal(decision.evidence.id,positiveAssessment.identity.profileApproval);
  const native=run.evidence.at(-1).native;
  const originals=native.originals.map(row=>({path:join(f.runDir,row.savedPath),bytes:readFileSync(join(f.runDir,row.savedPath))}));
  const journalPath=join(f.source,'.git/pdd/approvals.json'),journal=readFileSync(journalPath);
  const prompt=readFileSync(join(f.root,f.promptPath));
  // Change custody only. Keep approved prompt, journal and every original byte.
  run.decisions=[];writeFileSync(statusPath,JSON.stringify(run,null,2)+'\n');
  const before=readFileSync(statusPath),negative=f.command('lint','native','--json');
  const actual=JSON.parse(negative.stdout).native_assessments[0].assessment;
  assert.deepEqual(readFileSync(statusPath),before,'Reading must not repair a missing decision');
  for(const original of originals)assert.deepEqual(readFileSync(original.path),original.bytes,'Original bytes must remain unchanged');
  assert.deepEqual(readFileSync(journalPath),journal,'The actual approval journal must remain unchanged');
  assert.deepEqual(readFileSync(join(f.root,f.promptPath)),prompt,'Approved prompt bytes must remain unchanged');
  t.diagnostic(JSON.stringify({positiveExit:positive.status,positiveProof:positiveAssessment.storyNativeProof,negativeExit:negative.status,negativeProof:actual.storyNativeProof,requiresReview:actual.requiresReview,originalsUnchanged:true,statusUnchanged:true}));
  assert.equal(actual.storyNativeProof,'none','WORKFLOW JOURNAL WITHOUT SAVED GATE DECISION MUST NOT PROVE A NATIVE STORY');
  assert.equal(actual.profileNativeProof,'none','Incomplete review custody must deny profile proof too');
  assert.equal(actual.requiresReview,true);
});
