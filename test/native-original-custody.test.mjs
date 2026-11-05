import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {nativeFixture,put} from './helpers/native-cli-fixture.mjs';
import {prepareNativeEvidence} from '../src/workflow-results.mjs';
import {captureSource} from '../src/runtime-preflight.mjs';

async function originals(t) {
  const f=await nativeFixture(t),dir=join(f.parent,'originals'),summaryFile=join(dir,'import.json');
  const save=(name,value)=>put(dir,name,value);
  const descriptor={schema:'pdd.native-evidence-import.v1',profileId:'native',storyPath:f.storyPath,originals:[{role:'report',path:'report.json'},{role:'source',path:'source.json'},{role:'selection',path:'selection.json'},{role:'execution',path:'execution.json'}]};
  const report={producer:'synthetic-test-runner',producerVersion:'1',runner:'synthetic-suite',runnerVersion:'1',runtimeVersion:'node-22',capture:{selectionComplete:true,terminalSeen:true,processEnded:true,eventRef:'original-report'},complete:true,exitCode:0,rows:[{occurrenceId:'a',testId:f.a,selected:true,started:true,outcome:'ok'},{occurrenceId:'b',testId:f.b,selected:true,started:true,outcome:'ok'}]};
  save('import.json',descriptor);save('report.json',report);
  for(const name of ['source','selection','execution'])save(name+'.json',{});
  const first=prepareNativeEvidence({root:f.root,runDir:f.runDir,runId:f.readRun().runId,summaryFile});
  const source=Object.fromEntries(['sourceId','implementationId','testsId'].map(key=>[key,first.assessment.identity[key]]));
  const tests=['source.mjs',f.testPath,f.promptPath],source_sha256=captureSource(f.root,{tests}).sha256;
  const registered=f.command('workflow','evidence-associate','17','--workspace',f.root,'--stage','current','--test',...tests);
  assert.equal(registered.status,0,registered.stdout+registered.stderr);
  save('source.json',{producerRoot:f.root,tests,source_sha256,source,runId:f.readRun().runId,stage:'current'});
  save('selection.json',{sourceId:source.sourceId,stage:'current',complete:true,testIds:[f.a,f.b]});
  const execution={sourceId:source.sourceId,stage:'current',processEnded:true,exitCode:0,producer:report.producer,producerVersion:'1',runner:report.runner,runnerVersion:'1',runtimeVersion:'node-22'};
  save('execution.json',execution);
  const importOriginals=()=>{const result=f.command('workflow','evidence','17','--summary',summaryFile);assert.equal(result.status,0,result.stdout+result.stderr);};
  const judge=()=>{const result=f.command('lint','native','--json');return {exit:result.status,assessment:JSON.parse(result.stdout).native_assessments[0].assessment};};
  importOriginals();const positive=judge();assert.equal(positive.exit,0);assert.equal(positive.assessment.storyNativeProof,'qualified-external');
  return {...f,dir,save,descriptor,report,execution,importOriginals,judge};
}

test('actual original intake and default CLI reader deny contradictory, invalid or absent process completion',async t=>{
  const f=await originals(t),originalReport=readFileSync(join(f.dir,'report.json'));
  for(const [name,execution] of [
    ['contradictory completion',{...f.execution,processEnded:false}],
    ['unknown completion',{...f.execution,processEnded:null}],
    ['invalid exit',{...f.execution,exitCode:'0'}],
    ['contradictory exit',{...f.execution,exitCode:1}],
    ['foreign source',{...f.execution,sourceId:'other-source'}],
    ['malformed companion','not JSON']
  ]) {
    f.save('execution.json',execution);f.importOriginals();
    const before=readFileSync(join(f.runDir,'status.json')),actual=f.judge();
    assert.equal(actual.assessment.storyNativeProof,'none',`ORIGINAL EXECUTION CUSTODY MUST DENY PROOF: ${name}`);
    assert.equal(actual.assessment.profileNativeProof,'none',name);
    assert.equal(actual.assessment.profileState,'unverified',name);
    assert.equal(actual.assessment.occurrenceCount,2,name);
    assert.equal(actual.assessment.observations[0].outcome,'passed',name);
    assert.ok(actual.assessment.limits.some(limit=>limit.includes('process completion')),name);
    assert.deepEqual(readFileSync(join(f.runDir,'status.json')),before,'Reading must not repair custody');
    assert.deepEqual(readFileSync(join(f.dir,'report.json')),originalReport,'The report stays byte-identical');
  }
  f.save('import.json',{...f.descriptor,originals:f.descriptor.originals.filter(row=>row.role!=='execution')});f.importOriginals();
  assert.equal(f.judge().assessment.storyNativeProof,'none','Missing execution must not borrow the report flag');
  f.save('import.json',f.descriptor);f.save('execution.json',f.execution);f.importOriginals();
  assert.equal(f.judge().assessment.storyNativeProof,'qualified-external','Restoring valid originals preserves the positive control');
});

test('actual workflow approval custody rejects mismatched decision, snapshot and gate bindings',async t=>{
  const f=await originals(t),statusPath=join(f.runDir,'status.json'),saved=readFileSync(statusPath);
  for(const change of [
    decision=>{decision.decision='reject';},
    decision=>{decision.evidence.prompts[0].proseSha256='0'.repeat(64);},
    decision=>{decision.evidence.prompts=[];},
    decision=>{decision.gateId='another-gate';}
  ]) {
    const run=JSON.parse(saved);change(run.decisions[0]);writeFileSync(statusPath,JSON.stringify(run));
    const before=readFileSync(statusPath),actual=f.judge().assessment;
    assert.equal(actual.storyNativeProof,'none','Mismatched workflow custody cannot prove a Story');
    assert.equal(actual.requiresReview,true);
    assert.deepEqual(readFileSync(statusPath),before);
  }
  const missing=JSON.parse(saved);missing.decisions=[];missing.approvalRecord=null;
  writeFileSync(statusPath,JSON.stringify(missing));
  assert.equal(f.judge().assessment.storyNativeProof,'none','Absent custody cannot establish that a workflow event was standalone');
  writeFileSync(statusPath,saved);assert.equal(f.judge().assessment.storyNativeProof,'qualified-external');
});
