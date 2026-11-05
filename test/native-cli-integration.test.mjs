import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,readdirSync,writeFileSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {nativeFixture,put} from './helpers/native-cli-fixture.mjs';
import {captureSource} from '../src/runtime-preflight.mjs';
import {prepareNativeEvidence,readRunResults,resultLines} from '../src/workflow-results.mjs';
import {readEvidenceEligibility,stepDone,runStatus} from '../src/workflow-runner.mjs';

async function originals(f) {
  const directory=join(f.parent,'originals'),summaryFile=join(directory,'import.json');
  const descriptor={schema:'pdd.native-evidence-import.v1',profileId:'native',storyPath:f.storyPath,originals:[{role:'report',path:'report.json'},{role:'source',path:'source.json'},{role:'selection',path:'selection.json'},{role:'execution',path:'execution.json'}]};
  const save=(name,value)=>put(directory,name,value);
  const report={producer:'synthetic-test-runner',producerVersion:'1',runner:'synthetic-suite',runnerVersion:'1',runtimeVersion:'node-22',capture:{selectionComplete:true,terminalSeen:true,processEnded:true,eventRef:'original-report'},complete:true,exitCode:0,
    rows:[{occurrenceId:'a',testId:f.a,selected:true,started:true,outcome:'ok'},{occurrenceId:'b',testId:f.b,selected:true,started:true,outcome:'ok'},{occurrenceId:'optional',testId:'optional-probe',selected:true,started:false,outcome:'skip',skipReason:'optional probe disabled'}]};
  save('import.json',descriptor);save('report.json',report);for(const name of ['source','selection','execution'])save(name+'.json',{});
  const first=prepareNativeEvidence({root:f.root,runDir:f.runDir,runId:f.readRun().runId,summaryFile});
  const source=Object.fromEntries(['sourceId','implementationId','testsId'].map(key=>[key,first.assessment.identity[key]]));
  const tests=['source.mjs',f.testPath,f.promptPath],source_sha256=captureSource(f.root,{tests}).sha256;
  const registration=f.command('workflow','evidence-associate','17','--workspace',f.root,'--stage','current','--test',...tests);
  assert.equal(registration.status,0,registration.stdout+registration.stderr);
  save('source.json',{producerRoot:f.root,tests,source_sha256,source,runId:f.readRun().runId,stage:'current'});
  save('selection.json',{sourceId:source.sourceId,stage:'current',complete:true,testIds:[f.a,f.b,'optional-probe']});
  save('execution.json',{sourceId:source.sourceId,stage:'current',processEnded:true,exitCode:0,producer:report.producer,producerVersion:'1',runner:report.runner,runnerVersion:'1',runtimeVersion:'node-22'});
  return {directory,summaryFile,descriptor,report,save,source,tests,source_sha256};
}
test('real gate, native association, original CLI intake and all local consumers share the current judgment',async t=>{
  const f=await nativeFixture(t),o=await originals(f);
  const before=f.readRun(),original=readFileSync(join(o.directory,'report.json'));
  const imported=f.command('workflow','evidence','17','--summary',o.summaryFile);assert.equal(imported.status,0,imported.stdout+imported.stderr);
  assert.match(imported.stdout,/Story native proof qualified-external/);
  const run=f.readRun(),saved=run.evidence.at(-1).native;
  assert.deepEqual(readFileSync(join(f.runDir,saved.originals.find(row=>row.role==='report').savedPath)),original);
  for(const key of ['state','gate','done','decisions','area','pr'])assert.deepEqual(run[key],before[key]);
  const lint=f.command('lint','native','--json');assert.equal(lint.status,0,lint.stdout+lint.stderr);
  const assessment=JSON.parse(lint.stdout).native_assessments[0].assessment;
  assert.equal(assessment.profileState,'complete');assert.equal(assessment.storyNativeProof,'qualified-external');assert.equal(assessment.optionalSkippedIds.length,1);
  assert.equal(assessment.identity.profileApproval,run.decisions[0].evidence.id);
  const workspace=input=>readEvidenceEligibility(input,{env:f.env});
  const results=readRunResults({root:f.root,runDir:f.runDir,runId:run.runId},{env:f.env,workspace});
  assert.equal(results.at(-1).assessment.storyNativeProof,assessment.storyNativeProof);
  assert.match(resultLines(results).at(-1),/AC1: supported/);
  const status=await runStatus({ref:'17',cwd:f.root,json:true},f.ports);assert.equal(JSON.parse(status.message).runs[0].nativeResults[0].assessment.storyNativeProof,'qualified-external');
  const step=await stepDone({step:'verify',summary:'Synthetic consumer observation.',cwd:f.root},f.ports);assert.match(step.message,/AC1: supported/);
  const text=f.command('lint','native');assert.equal(text.status,0,text.stdout+text.stderr);assert.match(text.stdout,/AC1: Both native effects work/);assert.match(text.stdout,/qualified-external/);
  put(f.root,'source.mjs','export const value=2;\n');
  const stale=f.command('lint','native','--json');assert.equal(stale.status,1);assert.equal(JSON.parse(stale.stdout).native_assessments[0].assessment.storyNativeProof,'none');
});
test('required skips and absent IDs with duplicated passes cannot borrow aggregate success',async t=>{
  const f=await nativeFixture(t),o=await originals(f);
  for(const condition of ['skip','missing','failed']) {
    const rows=structuredClone(o.report.rows);
    if(condition==='skip'){rows[1].started=false;rows[1].outcome='skip';rows[1].skipReason='required fixture B is missing';}
    if(condition==='failed')rows[1].outcome='fail';
    if(condition==='missing')rows[1]={...rows[0],occurrenceId:'duplicate-A'};
    o.save('report.json',{...o.report,rows});
    const imported=f.command('workflow','evidence','17','--summary',o.summaryFile);assert.equal(imported.status,0,imported.stdout+imported.stderr);
    const result=f.command('lint','native','--json');assert.equal(result.status,1,result.stdout+result.stderr);
    const a=JSON.parse(result.stdout).native_assessments[0].assessment;
    assert.equal(a.storyNativeProof,'none');
    assert.ok(a[condition==='skip'?'skippedIds':condition==='missing'?'missingIds':'failedIds'].includes(f.b));
    if(condition==='missing')assert.ok(a.duplicateIds.includes(f.a));
  }
});
test('original read refusals do not change history; tampered retained evidence cannot pass',async t=>{
  const f=await nativeFixture(t),o=await originals(f);
  const before=readFileSync(join(f.runDir,'status.json'));
  rmSync(join(o.directory,'report.json'));
  const refused=f.command('workflow','evidence','17','--summary',o.summaryFile);assert.equal(refused.status,1);
  assert.deepEqual(readFileSync(join(f.runDir,'status.json')),before);
  o.save('report.json',o.report);assert.equal(f.command('workflow','evidence','17','--summary',o.summaryFile).status,0);
  const saved=f.readRun().evidence.at(-1).native.originals.find(row=>row.role==='report');writeFileSync(join(f.runDir,saved.savedPath),'{}');
  const result=f.command('lint','native','--json');assert.equal(result.status,1);assert.equal(JSON.parse(result.stdout).native_assessments[0].assessment.profileNativeProof,'none');
  assert.ok(readdirSync(join(f.runDir,'evidence')).length);
});
test('mixed selection keeps native missing proof separate from local Runtime refusal and unknown operands',async t=>{
  const f=await nativeFixture(t);
  put(f.root,'user_stories/modeled.md','# Modeled\n\n## Acceptance criteria\n\n1. Modeled value.\n');
  put(f.root,'test/modeled.json',{schema_version:'prompt-runtime.program-scenario.v1',story_path:'user_stories/modeled.md',criteria:[{id:'AC1',text:'Modeled value.'}],initial_world:{},steps:[{step_id:'one',entry_path:'prompts/modeled.prompt.md',operation:'run',input:{},checks:[]}]});
  put(f.root,'prompts/modeled.prompt.md','# Modeled\n\n<details><summary>Runtime interface</summary>\n```json\n'+JSON.stringify({status:'draft',prose_sha256:'',entries:[],calls:[],resources:[],limits:{max_steps:0,max_model_calls:0},conventions:[]})+'\n```\n</details>\n');
  const mixed=f.command('lint','native','modeled','--json');assert.equal(mixed.status,4,mixed.stdout+mixed.stderr);
  const report=JSON.parse(mixed.stdout);assert.equal(report.native_assessments.length,1);assert.equal(report.rows.length,1);assert.equal(report.rows[0].story,'modeled');assert.equal(report.lint_state,'refused');
  const unknown=f.command('lint','native','not-a-story','--json');assert.equal(unknown.status,2);assert.match(unknown.stderr,/Unknown story/);
});
