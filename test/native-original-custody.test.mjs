import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {nativeFixture,put,git} from './helpers/native-cli-fixture.mjs';
import {prepareNativeEvidence} from '../src/workflow-results.mjs';
import {captureSource} from '../src/runtime-preflight.mjs';
import {stepDone,approveRun,readEvidenceEligibility} from '../src/workflow-runner.mjs';

async function originals(t,options) {
  const f=await nativeFixture(t,options),dir=join(f.parent,'originals'),summaryFile=join(dir,'import.json');
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
  return {...f,dir,save,descriptor,report,execution,source,tests,source_sha256,summaryFile,importOriginals,judge};
}

test('actual CLI preserves conflicting original source and capture identities without current proof',async t=>{
  const f=await originals(t);
  for(const [name,change] of [
    ...['sourceId','implementationId','testsId','requirementsId'].map(key=>[`report source ${key}`,report=>{report.source={...f.source,[key]:'foreign-original'};}]),
    ...['sourceId','implementationId','testsId','requirementsId','source_sha256','stage','runId','repo'].map(key=>[`report capture ${key}`,report=>{report.capture[key]='foreign-original';}])
  ]) {
    const report=structuredClone(f.report);change(report);f.save('report.json',report);
    const bytes=readFileSync(join(f.dir,'report.json'));f.importOriginals();
    const before=readFileSync(join(f.runDir,'status.json')),actual=f.judge();
    assert.equal(actual.assessment.storyNativeProof,'none',`CONTRADICTORY ORIGINAL SOURCE MUST DENY STORY PROOF: ${name}`);
    assert.equal(actual.assessment.profileNativeProof,'none',name);
    assert.equal(actual.assessment.profileState,'unverified',name);
    assert.notEqual(actual.exit,0,name);
    assert.ok(actual.assessment.limits.some(limit=>/source.*contradict|contradict.*source/i.test(limit)),name);
    assert.equal(actual.assessment.observations[1].outcome,'passed',name);
    assert.deepEqual(readFileSync(join(f.dir,'report.json')),bytes);
    const saved=f.readRun().evidence.at(-1).native.originals.find(row=>row.role==='report');
    assert.deepEqual(readFileSync(join(f.runDir,saved.savedPath)),bytes);
    assert.deepEqual(readFileSync(join(f.runDir,'status.json')),before);
  }
  f.save('report.json',{...f.report,source:{sourceId:'unknown'}});f.importOriginals();
  assert.equal(f.judge().assessment.storyNativeProof,'qualified-external','Unobserved fields may be filled from checked originals');
  for(const role of ['selection','execution']) {
    const saved=JSON.parse(readFileSync(join(f.dir,role+'.json')));
    f.save(role+'.json',{...saved,implementationId:'foreign-companion'});f.importOriginals();
    assert.equal(f.judge().assessment.storyNativeProof,'none',`${role} cannot contradict canonical implementation identity`);
    f.save(role+'.json',saved);
  }
});

async function publishFixturePr1(f) {
  const original=f.ports.execFile;let pr=null;
  const ports={...f.ports,execFile:async(file,args,options)=>{
    if(file==='git'&&args[0]==='ls-remote')return {stdout:`${git(f.root,'rev-parse','HEAD')}\t${args.at(-1)}\n`};
    if(file==='git'&&args[0]==='push')return {stdout:''};
    if(file==='gh'&&args[0]==='pr') {
      if(args[1]==='list')return {stdout:JSON.stringify(pr?[pr]:[])};
      if(args[1]==='create') {
        const value=key=>args[args.indexOf(key)+1];
        pr={number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:value('--head'),baseRefName:value('--base'),headRefOid:git(f.root,'rev-parse','HEAD'),body:options.input,isCrossRepository:false,headRepository:{name:'project'},headRepositoryOwner:{login:'example'},mergeCommit:null};
        return {stdout:pr.url};
      }
      if(args[1]==='view')return {stdout:JSON.stringify(pr)};
    }
    return original(file,args,options);
  }};
  for(const step of ['check','try']) {
    const result=await stepDone({step,summary:'Local synthetic historical-source fixture; no hosted check.',cwd:f.root},ports);
    assert.equal(result.exitCode,0,result.message);
  }
  const approved=await approveRun({ref:'17',said:'Approve local synthetic PR 1 fixture publication.',cwd:f.root},ports);
  assert.equal(approved.exitCode,0,approved.message);
  assert.ok(f.readRun().pr.find(row=>row.stage==='prompt-pr'),'The supported workflow must record its own PR 1');
}

test('actual CLI compares earlier candidate baseline at its canonical frozen PR 1 source',async t=>{
  const f=await originals(t,{workflow:'feature'});
  await publishFixturePr1(f);
  const registered=f.command('workflow','evidence-associate','17','--workspace',f.root,'--stage','pr1','--test',...f.tests);
  assert.equal(registered.status,0,registered.stdout+registered.stderr);
  const association=f.readRun().evidenceAssociations.find(row=>row.stage==='pr1');
  assert.ok(association.sourceAnchor.head);
  const owner=()=>readEvidenceEligibility({root:f.root,producerRoot:f.root,tests:f.tests,source_sha256:f.source_sha256,runId:f.readRun().runId,stage:'pr1'},{env:f.env});
  assert.equal(owner().state,'eligible','Canonical owner must admit historical bytes before testing intake');
  for(const name of ['import','source','selection','execution','report']) {
    const value=JSON.parse(readFileSync(join(f.dir,name+'.json'),'utf8'));
    if(['source','selection','execution'].includes(name))value.stage='pr1';
    put(f.dir,'baseline/'+name+'.json',value);
  }
  put(f.root,'source.mjs','export const value=2;\n');
  const next=prepareNativeEvidence({root:f.root,runDir:f.runDir,runId:f.readRun().runId,summaryFile:f.summaryFile}).assessment.identity;
  assert.notEqual(next.implementationId,f.source.implementationId);
  const source=Object.fromEntries(['sourceId','implementationId','testsId'].map(key=>[key,next[key]]));
  f.save('source.json',{producerRoot:f.root,tests:f.tests,source_sha256:captureSource(f.root,{tests:f.tests}).sha256,source,runId:f.readRun().runId,stage:'current'});
  assert.equal(f.command('workflow','evidence-associate','17','--workspace',f.root,'--stage','current','--test',...f.tests).status,0);
  f.save('selection.json',{sourceId:source.sourceId,stage:'current',complete:true,testIds:[f.a]});
  f.save('execution.json',{...f.execution,sourceId:source.sourceId});
  f.save('report.json',{...f.report,rows:[f.report.rows[0],{...f.report.rows[0],occurrenceId:'duplicate-A'}]});
  f.save('import.json',{...f.descriptor,baseline:'baseline/import.json'});
  assert.equal(owner().state,'eligible','Later code must not invalidate canonical frozen PR 1 source');
  assert.equal(readFileSync(join(association.sourceAnchor.root,'source.mjs'),'utf8'),'export const value=1;\n');
  assert.equal(readFileSync(join(f.root,'source.mjs'),'utf8'),'export const value=2;\n');
  assert.equal(captureSource(association.sourceAnchor.root,{tests:f.tests}).sha256,f.source_sha256,'Canonical capture proves the historical bytes independently of current source');
  const hashes=()=>Object.fromEntries(['import','source','selection','execution','report'].flatMap(name=>['','baseline/'].map(prefix=>{
    const path=prefix+name+'.json';return [path,createHash('sha256').update(readFileSync(join(f.dir,path))).digest('hex')];
  })));
  const controlHashes=process.env.PDD_NATIVE_OLD_CLI?hashes():null;
  if(controlHashes) {
    const imported=f.commandAt(process.env.PDD_NATIVE_OLD_CLI,'workflow','evidence','17','--summary',f.summaryFile);
    assert.equal(imported.status,0,imported.stdout+imported.stderr);
    const old=f.commandAt(process.env.PDD_NATIVE_OLD_CLI,'lint','native','--json'),assessment=JSON.parse(old.stdout).native_assessments[0].assessment;
    assert.equal(owner().state,'eligible');
    assert.equal(assessment.identity.sourceId,source.sourceId);
    assert.throws(()=>assert.equal(assessment.comparison.state,'comparable','EARLIER CANONICAL CANDIDATE BASELINE MUST REMAIN COMPARABLE'),{code:'ERR_ASSERTION'},'Old control must fail semantically after canonical admission');
    assert.deepEqual(hashes(),controlHashes);
    t.diagnostic(JSON.stringify({control:'old CLI on identical canonical fixture before repaired CLI replay',at:new Date().toISOString(),cli:process.env.PDD_NATIVE_OLD_CLI,owner:owner(),currentSource:source,historicalSource:f.source,hashes:controlHashes,oldExit:old.status,oldComparison:assessment.comparison}));
  }
  f.importOriginals();const actual=f.judge();
  assert.equal(actual.assessment.profileState,'incomplete');assert.equal(actual.assessment.storyNativeProof,'none');
  assert.equal(actual.assessment.identity.sourceId,source.sourceId,'Current proof stays bound to current source');
  assert.equal(actual.assessment.comparison.state,'comparable','EARLIER CANONICAL CANDIDATE BASELINE MUST REMAIN COMPARABLE');
  assert.deepEqual(actual.assessment.comparison.lostIds,[f.b]);
  assert.deepEqual(actual.assessment.comparison.changes,[{id:f.b,before:'passed',after:'missing'}]);
  if(controlHashes) {
    assert.deepEqual(hashes(),controlHashes);
    t.diagnostic(JSON.stringify({control:'repaired CLI on identical canonical fixture',at:new Date().toISOString(),hashes:hashes(),candidateIdentity:actual.assessment.identity,comparison:actual.assessment.comparison}));
  }
  const checks=f.readRun().evidence.at(-1).native.checks.find(row=>row.check==='historical-baseline');
  assert.equal(checks.stage,'pr1');
  assert.equal(checks.checks.find(row=>row.check==='selected-native-source').sourceId,f.source.sourceId);
  assert.match(actual.assessment.limits.join('\n'),/Historical baseline \(pr1\)/);
  const baselineReport=JSON.parse(readFileSync(join(f.dir,'baseline/report.json'))),baselineExecution=JSON.parse(readFileSync(join(f.dir,'baseline/execution.json')));
  f.save('baseline/report.json',{...baselineReport,runnerVersion:'2'});
  f.save('baseline/execution.json',{...baselineExecution,runnerVersion:'2'});
  f.importOriginals();assert.deepEqual(f.judge().assessment.comparison,{state:'incomparable',reason:'scope-or-version',lostIds:[],changes:[]},'Historical admission cannot weaken runner-version compatibility');
  f.save('baseline/report.json',baselineReport);f.save('baseline/execution.json',baselineExecution);
  f.importOriginals();assert.deepEqual(f.judge().assessment.comparison.lostIds,[f.b]);
  const baselineSource=JSON.parse(readFileSync(join(f.dir,'baseline/source.json')));
  f.save('baseline/source.json',{...baselineSource,runId:'foreign-run'});f.importOriginals();
  assert.equal(f.judge().assessment.comparison.state,'incomparable','A historical original cannot supply its own foreign ownership');
  f.save('baseline/source.json',baselineSource);f.importOriginals();
  assert.deepEqual(f.judge().assessment.comparison.lostIds,[f.b]);
  rmSync(join(association.sourceAnchor.root,'source.mjs'));
  const before=readFileSync(join(f.runDir,'status.json')),unavailable=f.judge().assessment;
  assert.equal(unavailable.comparison.state,'incomparable');
  assert.equal(unavailable.comparison.reason,'unverified');
  assert.deepEqual(readFileSync(join(f.runDir,'status.json')),before,'Read never reconstructs missing historical source');
});

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


test('actual CLI keeps contradictory original selection and execution facts unverified',async t=>{
  const f=await originals(t);
  for(const [name,change] of [
    ['row selection',report=>{report.rows[1].selected=false;}],
    ['complete selection',report=>{report.capture.selectionComplete=false;}],
    ['process completion',report=>{report.capture.processEnded=false;}],
    ['runner identity',report=>{report.runnerVersion='contradictory-version';}]
  ]) {
    const report=structuredClone(f.report);change(report);f.save('report.json',report);
    const bytes=readFileSync(join(f.dir,'report.json'));f.importOriginals();
    const before=readFileSync(join(f.runDir,'status.json')),actual=f.judge();
    assert.equal(actual.assessment.storyNativeProof,'none',`CONTRADICTORY ORIGINAL MUST DENY STORY PROOF: ${name}`);
    assert.equal(actual.assessment.profileNativeProof,'none',name);
    assert.equal(actual.assessment.profileState,'unverified',name);
    assert.notEqual(actual.exit,0,name);
    assert.equal(actual.assessment.occurrenceCount,2,name);
    assert.equal(actual.assessment.observations[1].selected,report.rows[1].selected,name);
    assert.equal(actual.assessment.observations[1].started,true,name);
    assert.equal(actual.assessment.observations[1].outcome,'passed',name);
    assert.deepEqual(readFileSync(join(f.dir,'report.json')),bytes);
    assert.deepEqual(readFileSync(join(f.runDir,'status.json')),before);
  }
  const report=structuredClone(f.report);delete report.capture.selectionComplete;
  for(const row of report.rows)delete row.selected;
  f.save('report.json',report);f.importOriginals();
  assert.equal(f.judge().assessment.storyNativeProof,'qualified-external','Companions may fill unobserved selection facts');
});
