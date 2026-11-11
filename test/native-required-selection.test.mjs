import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {nativeFixture,put} from './helpers/native-cli-fixture.mjs';
import {prepareNativeEvidence} from '../src/workflow-results.mjs';
import {captureSource} from '../src/runtime/runtime-preflight.mjs';

// Synthetic external runner originals and the supported synthetic workflow actor
// exercise real CLI intake, default readers, source/approval and saved custody.
// They do not establish physical execution or authenticate an external speaker.
test('default CLI requires positive selection for each required passing ID and accepts checked companion fills',async t=>{
  const f=await nativeFixture(t),directory=join(f.parent,'originals');
  const descriptor={schema:'pdd.native-evidence-import.v1',profileId:'native',storyPath:f.storyPath,originals:['report','source','selection','execution'].map(role=>({role,path:role+'.json'}))};
  const report={producer:'synthetic-test-runner',producerVersion:'1',runner:'synthetic-suite',runnerVersion:'1',runtimeVersion:'node-22',capture:{selectionComplete:true,terminalSeen:true,processEnded:true,eventRef:'original-report'},complete:true,exitCode:0,
    rows:[{occurrenceId:'a',testId:f.a,selected:true,started:true,outcome:'ok'},{occurrenceId:'b',testId:f.b,selected:true,started:true,outcome:'ok'},{occurrenceId:'optional',testId:'optional-probe',selected:false,started:false,outcome:'skip',skipReason:'optional disabled'}]};
  const seed=join(directory,'seed'),summaryFile=join(seed,'import.json');
  put(seed,'import.json',descriptor);put(seed,'report.json',report);
  for(const role of ['source','selection','execution'])put(seed,role+'.json',{});
  const first=prepareNativeEvidence({root:f.root,runDir:f.runDir,runId:f.readRun().runId,summaryFile});
  const source=Object.fromEntries(['sourceId','implementationId','testsId'].map(key=>[key,first.assessment.identity[key]]));
  const tests=['source.mjs',f.testPath,f.promptPath],source_sha256=captureSource(f.root,{tests}).sha256;
  const registered=f.command('workflow','evidence-associate','17','--workspace',f.root,'--stage','current','--test',...tests);
  assert.equal(registered.status,0,registered.stdout+registered.stderr);

  // Expected decisions follow the accepted required-execution contract, before
  // reading any result: passing/started alone cannot supply required selection.
  for(const condition of ['known-positive','omitted-negative','null-negative','omitted-fill','null-fill','false-conflict','true-conflict']) {
    const dir=join(directory,condition),original=structuredClone(report);
    if(condition.startsWith('omitted'))delete original.rows[1].selected;
    if(condition.startsWith('null'))original.rows[1].selected=null;
    if(condition==='false-conflict')original.rows[1].selected=false;
    const selected=condition.endsWith('negative')||condition==='true-conflict'?[f.a]:[f.a,f.b];
    put(dir,'import.json',descriptor);put(dir,'report.json',original);
    put(dir,'source.json',{producerRoot:f.root,tests,source_sha256,source,runId:f.readRun().runId,stage:'current'});
    put(dir,'selection.json',{sourceId:source.sourceId,stage:'current',complete:true,testIds:selected});
    put(dir,'execution.json',{sourceId:source.sourceId,stage:'current',processEnded:true,exitCode:0,producer:report.producer,producerVersion:'1',runner:report.runner,runnerVersion:'1',runtimeVersion:'node-22'});
    const raw=descriptor.originals.map(row=>({role:row.role,bytes:readFileSync(join(dir,row.path))}));
    const before=f.readRun(),imported=f.command('workflow','evidence','17','--summary',join(dir,'import.json'));
    assert.equal(imported.status,0,imported.stdout+imported.stderr);
    const run=f.readRun(),saved=run.evidence.at(-1).native;
    for(const key of ['state','gate','done','decisions','area','pr'])assert.deepEqual(run[key],before[key],condition);
    for(const row of raw)assert.deepEqual(readFileSync(join(f.runDir,saved.originals.find(o=>o.role===row.role).savedPath)),row.bytes,`Original ${row.role} byte custody: ${condition}`);
    const pinned=[join(f.runDir,'status.json'),join(f.source,'.git/pdd/approvals.json'),join(f.root,f.promptPath),...saved.originals.map(row=>join(f.runDir,row.savedPath))].map(path=>({path,bytes:readFileSync(path)}));
    const result=f.command('lint','native','--json');
    const a=JSON.parse(result.stdout).native_assessments[0].assessment;
    const positive=condition==='known-positive'||condition.endsWith('fill');
    assert.equal(result.status,positive?0:1,`REQUIRED POSITIVE SELECTION EVIDENCE: ${condition}`);
    assert.equal(a.profileState,positive?'complete':condition.endsWith('conflict')?'unverified':'incomplete',condition);
    assert.equal(a.profileNativeProof,positive?'qualified-external':'none',condition);
    assert.equal(a.storyNativeProof,positive?'qualified-external':'none',condition);
    assert.deepEqual(a.optionalSkippedIds,['optional-probe'],condition);
    assert.equal(a.observations[1].started,true,condition);
    assert.equal(a.observations[1].outcome,'passed',condition);
    assert.equal(a.observations[1].selected,positive?true:condition==='false-conflict'?false:condition==='true-conflict'?true:null,condition);
    if(condition.endsWith('negative'))assert.deepEqual(a.unknownIds,[f.b],condition);
    assert.equal(a.identity.profileApproval,run.decisions[0].evidence.id,condition);
    for(const pin of pinned)assert.deepEqual(readFileSync(pin.path),pin.bytes,`Read cannot mutate custody: ${condition}`);
    for(const row of raw)assert.deepEqual(readFileSync(join(dir,descriptor.originals.find(o=>o.role===row.role).path)),row.bytes,condition);
    t.diagnostic(JSON.stringify({condition,exit:result.status,profileState:a.profileState,proof:a.storyNativeProof,unknownIds:a.unknownIds}));
  }
});
