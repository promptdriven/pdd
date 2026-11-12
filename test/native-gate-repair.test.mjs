import test from 'node:test';
import assert from 'node:assert/strict';
import {join} from 'node:path';
import {renameSync,symlinkSync,readFileSync} from 'node:fs';
import {nativeFixture,put,git} from './helpers/native-gate-fixture.mjs';
import {captureSource} from '../src/runtime-preflight.mjs';
import {prepareNativeEvidence,readRunResults,usableResult} from '../src/workflow-results.mjs';
import {stepDone,approveRun,readEvidenceEligibility} from '../src/workflow-runner.mjs';
async function originals(f,stage='current') {
  const directory=join(f.parent,'originals'),summaryFile=join(directory,'import.json');
  const descriptor={schema:'pdd.native-evidence-import.v1',profileId:'native',storyPath:f.storyPath,originals:[{role:'report',path:'report.json'},{role:'source',path:'source.json'},{role:'selection',path:'selection.json'},{role:'execution',path:'execution.json'}]};
  const save=(name,value)=>put(directory,name,value);
  const report={producer:'synthetic-test-runner',producerVersion:'1',runner:'synthetic-suite',runnerVersion:'1',runtimeVersion:'node-22',capture:{selectionComplete:true,terminalSeen:true,processEnded:true,eventRef:'original-report'},complete:true,exitCode:0,
    rows:[{occurrenceId:'a',testId:f.a,selected:true,started:true,outcome:'ok'},{occurrenceId:'b',testId:f.b,selected:true,started:true,outcome:'ok'},{occurrenceId:'optional',testId:'optional-probe',selected:true,started:false,outcome:'skip',skipReason:'optional probe disabled'}]};
  save('import.json',descriptor);save('report.json',report);for(const name of ['source','selection','execution'])save(name+'.json',{});
  const first=prepareNativeEvidence({root:f.root,runDir:f.runDir,runId:f.readRun().runId,summaryFile});
  const source=Object.fromEntries(['sourceId','implementationId','testsId'].map(key=>[key,first.assessment.identity[key]]));
  const tests=['source.mjs',f.testPath,f.promptPath],source_sha256=captureSource(f.root,{tests}).sha256;
  if(stage==='before'){git(f.root,'add','.');git(f.root,'commit','-qm','fixture before');}
  const registration=f.command('workflow','evidence-associate','17','--workspace',f.root,'--stage',stage,...(stage==='before'?['--commit',git(f.root,'rev-parse','HEAD')]:[]),'--test',...tests);
  assert.equal(registration.status,0,registration.stdout+registration.stderr);
  save('source.json',{producerRoot:f.root,tests,source_sha256,source,runId:f.readRun().runId,stage});
  save('selection.json',{sourceId:source.sourceId,stage,complete:true,testIds:[f.a,f.b,'optional-probe']});
  save('execution.json',{sourceId:source.sourceId,stage,processEnded:true,exitCode:0,producer:report.producer,producerVersion:'1',runner:report.runner,runnerVersion:'1',runtimeVersion:'node-22'});
  return {directory,summaryFile,descriptor,report,save,source,tests,source_sha256};
}

test('native proof opens a separate approval gate and stale evidence refuses approval',async t=>{
  const f=await nativeFixture(t,{workflow:'feature'}),o=await originals(f);
  assert.equal(f.command('workflow','evidence','17','--summary',o.summaryFile).status,0);
  const shown=await stepDone({step:'check',summary:'Native proof ready.',cwd:f.root},f.ports);
  assert.match(shown.message,/separate approval is required/);
  assert.equal(f.readRun().gate.nativeApproval,true);
  assert.ok(!f.readRun().decisions.some(row=>row.route==='automatic-check-pass'));
  put(f.root,'source.mjs','export const value=2;\n');
  const refused=await approveRun({ref:'17',said:'Approve native publication.',cwd:f.root},f.ports);
  assert.equal(refused.exitCode,1);assert.match(refused.message,/no longer current/);
});

test('later explicit approval publishes a current native Story',async t=>{
  const f=await nativeFixture(t,{workflow:'feature'}),o=await originals(f);
  assert.equal(f.command('workflow','evidence','17','--summary',o.summaryFile).status,0);
  let pr=null; const original=f.ports.execFile;
  const ports={...f.ports,execFile:async(file,args,options)=>{
    if(file==='git'&&args[0]==='ls-remote')return {stdout:`${git(f.root,'rev-parse','HEAD')}\t${args.at(-1)}\n`};
    if(file==='git'&&args[0]==='push')return {stdout:''};
    if(file==='gh'&&args[0]==='pr'){
      if(args[1]==='list')return {stdout:JSON.stringify(pr?[pr]:[])};
      if(args[1]==='create'){const value=key=>args[args.indexOf(key)+1];pr={number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:value('--head'),baseRefName:value('--base'),headRefOid:git(f.root,'rev-parse','HEAD'),body:options.input,isCrossRepository:false,headRepository:{name:'project'},headRepositoryOwner:{login:'example'},mergeCommit:null};return {stdout:pr.url};}
      if(args[1]==='view')return {stdout:JSON.stringify(pr)};
    }
    return original(file,args,options);
  }};
  const shown=await stepDone({step:'check',summary:'Native proof ready.',cwd:f.root},ports);
  assert.match(shown.message,/separate approval is required/);
  const approved=await approveRun({ref:'17',said:'Approve native publication.',cwd:f.root},ports);
  assert.equal(approved.exitCode,0,approved.message);assert.ok(pr);
  assert.ok(!f.readRun().decisions.some(row=>row.route==='automatic-check-pass'));
});

test('missing required native test cannot open the native approval route',async t=>{
  const f=await nativeFixture(t,{workflow:'feature'}),o=await originals(f);
  o.save('report.json',{...o.report,rows:[o.report.rows[0]]});
  assert.equal(f.command('workflow','evidence','17','--summary',o.summaryFile).status,0);
  const shown=await stepDone({step:'check',summary:'Incomplete native evidence.',cwd:f.root},f.ports);
  assert.doesNotMatch(shown.message,/separate approval is required/);
  assert.match(shown.message,/prompt check did not pass/);
});
test('a changed Story reopens its card before native approval',async t=>{
  const f=await nativeFixture(t,{workflow:'feature'}),o=await originals(f);
  assert.equal(f.command('workflow','evidence','17','--summary',o.summaryFile).status,0);
  put(f.root,f.storyPath,'# Native\n\n## Acceptance criteria\n\n1. Changed requirement.\n');
  const shown=await stepDone({step:'check',summary:'Story changed.',cwd:f.root},f.ports);
  assert.match(shown.message,/Story gate is open again/);
  assert.doesNotMatch(shown.message,/separate approval is required/);
});

test('missing Runtime scenario result blocks a mixed native Story gate',async t=>{
  const f=await nativeFixture(t,{workflow:'feature',mixed:true}),o=await originals(f);
  assert.equal(f.command('workflow','evidence','17','--summary',o.summaryFile).status,0);
  const shown=await stepDone({step:'check',summary:'Mixed evidence.',cwd:f.root},f.ports);
  assert.doesNotMatch(shown.message,/separate approval is required/);
  assert.match(shown.message,/test\/modeled.json: no saved check/);
});


test('native before originals retain their commit and cannot open current gate',async t=>{
  const f=await nativeFixture(t,{workflow:'feature'}),o=await originals(f,'before');
  const imported=f.command('workflow','evidence','17','--summary',o.summaryFile);
  assert.equal(imported.status,0,imported.stdout+imported.stderr);
  const saved=f.readRun();assert.equal(saved.evidenceAssociations.at(-1).stage,'before');
  assert.equal(saved.evidenceAssociations.at(-1).sourceAnchor.head,git(f.root,'rev-parse','HEAD'));
  const unrelated=f.command('workflow','evidence-associate','17','--workspace',f.root,'--stage','before','--commit',git(f.root,'rev-parse','HEAD'),'--test','source.mjs');
  assert.equal(unrelated.status,1);assert.match(unrelated.stdout+unrelated.stderr,/same Story/);
  assert.equal(saved.evidence.at(-1).native.intake.stage,'before');
  const result=readRunResults({root:f.root,runDir:f.runDir,runId:saved.runId},{env:f.env,workspace:input=>readEvidenceEligibility(input,{env:f.env})}).at(-1);
  assert.equal(result.assessment.identity.stage,'before');
  assert.equal(result.assessment.storyNativeProof,'qualified-external');
  assert.equal(usableResult(result),false);
  const shown=await stepDone({step:'check',summary:'Historical native evidence.',cwd:f.root},f.ports);
  assert.doesNotMatch(shown.message,/separate approval is required/);
  assert.match(shown.message,/prompt check did not pass/);
});

test('native before association refuses an escaping Story ancestor without writing',async t=>{
  const f=await nativeFixture(t,{workflow:'feature'});
  git(f.root,'add','.');git(f.root,'commit','-qm','fixture before');
  const head=git(f.root,'rev-parse','HEAD');
  const original=join(f.root,'user_stories'),outside=join(f.parent,'outside-stories');
  renameSync(original,outside);symlinkSync(outside,original,'dir');
  const before=readFileSync(join(f.runDir,'status.json'));
  const result=f.command('workflow','evidence-associate','17','--workspace',f.root,'--stage','before','--commit',head,'--test','source.mjs',f.testPath,f.promptPath);
  assert.equal(result.status,1,result.stdout+result.stderr);
  assert.deepEqual(readFileSync(join(f.runDir,'status.json')),before);
});
