import {test} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import {prepareNativeEvidence,readNativeContext,assessNativeEvidence} from '../src/workflow-results.mjs';
import {captureSource,proseSha256} from '../src/runtime-preflight.mjs';
import {recordPromptApproval} from '../src/approval-policy.mjs';
const git=(root,...args)=>execFileSync('git',['-C',root,...args],{encoding:'utf8',stdio:['ignore','pipe','pipe']}).trim();
async function fixture(t,format='json') {
  const root=mkdtempSync(join(tmpdir(),'pdd-native-'));t.after(()=>rmSync(root,{recursive:true,force:true}));git(root,'init','-q');
  for(const p of ['prompts','test','user_stories','originals','.git/pdd/runs/1'])mkdirSync(join(root,p),{recursive:true});
  const a='test/native.mjs::required A@1:1',b='test/native.mjs::required B@2:1';
  writeFileSync(join(root,'test/native.mjs'),'test("required A",()=>{});\ntest("required B",()=>{});\n');
  writeFileSync(join(root,'source.mjs'),'export const value = 1;\n');
  const reader={rows:'/rows',fields:Object.fromEntries(['producer','producerVersion','runner','runnerVersion','runtimeVersion','capture','complete','exitCode','source'].map(k=>[k,'/'+k]).concat(['occurrenceId','testId','selected','started','outcome','skipReason'].map(k=>[k,'/'+k]))),outcomes:{ok:'passed',skip:'skipped',fail:'failed'}};
  const profile={schema:'pdd.native-profile.v1',profileId:'native',reportFormat:format,requiredIds:[a,b],requiredGates:[],fixtures:[],mappings:[{storyPath:'user_stories/native.md',criterionId:'AC1',criterionText:'Both native effects work.',nativeIds:[a,b]}],sourcePaths:['source.mjs'],testPaths:['test/native.mjs'],...(format==='json'?{reader}:{})};
  const prompt='# Native module\n\n<a id="native-validation-profile-native"></a>\n<details><summary>Native validation profile: native</summary>\n\n```json\n'+JSON.stringify(profile)+'\n```\n</details>\n';
  writeFileSync(join(root,'prompts/native.prompt.md'),prompt);
  writeFileSync(join(root,'user_stories/native.md'),'# Native Story\n\n## Acceptance criteria\n\n1. Both native effects work.\n\n## Native validation\n\n[Owner](../prompts/native.prompt.md#native-validation-profile-native)\n');
  git(root,'add','.');
  await recordPromptApproval({commonDir:join(root,'.git'),evidence:{id:'native-review',route:'terminal',actor:{kind:'terminal',id:'test'},at:1,words:'Synthetic test review.',prompts:[{path:'prompts/native.prompt.md',proseSha256:proseSha256(prompt)}]}});
  const selectors={root,runDir:join(root,'.git/pdd/runs/1'),runId:'run-1',profileId:'native',storyPath:'user_stories/native.md'};
  const originals=join(root,'originals'),summaryFile=join(originals,'import.json');
  const save=(name,value)=>writeFileSync(join(originals,name),typeof value==='string'?value:JSON.stringify(value));
  const descriptor={schema:'pdd.native-evidence-import.v1',profileId:'native',storyPath:selectors.storyPath,originals:[{path:'report',role:'report'},{path:'source.json',role:'source'},{path:'selection.json',role:'selection'},{path:'execution.json',role:'execution'}]};
  save('import.json',descriptor);
  for(const name of ['source.json','selection.json','execution.json'])save(name,{});
  // Exact native selection includes implementation, tests, requirements and Story, through the real capture reader.
  const paths=['source.mjs','test/native.mjs','prompts/native.prompt.md'];
  const capture=captureSource(root,{tests:paths});
  // First preparation gets source identities from the default actual-source adapter; no source/approval port is faked.
  save('report',{producer:'runner',producerVersion:'1',runner:'native-suite',runnerVersion:'1',runtimeVersion:'node-22',capture:{selectionComplete:true,terminalSeen:true,processEnded:true,eventRef:'original'},complete:true,exitCode:0,rows:[{occurrenceId:'a',testId:a,selected:true,started:true,outcome:'ok'},{occurrenceId:'b',testId:b,selected:true,started:true,outcome:'ok'}]});
  const first=prepareNativeEvidence({...selectors,summaryFile});
  const source={sourceId:first.assessment.identity.sourceId,implementationId:first.assessment.identity.implementationId,testsId:first.assessment.identity.testsId};
  save('source.json',{producerRoot:root,tests:paths,source_sha256:capture.sha256,source,runId:'run-1',stage:'current'});
  save('selection.json',{sourceId:source.sourceId,stage:'current',complete:true,testIds:[a,b]});
  save('execution.json',{sourceId:source.sourceId,stage:'current',processEnded:true,exitCode:0,producer:'runner',producerVersion:'1',runner:'native-suite',runnerVersion:'1',runtimeVersion:'node-22'});
  const workspace=input=>({state:'eligible',reason:'synthetic supplied canonical association',runId:'run-1',repo:'fixture/repo',producerRoot:root,tests:input.tests,source_sha256:input.source_sha256,stage:'current',sourceAnchor:{root,head:null}});
  return {...selectors,summaryFile,save,a,b,workspace,descriptor};
}
test('default original intake binds actual native bytes and real approval journal; reread rejects changed originals',async t=>{
  const f=await fixture(t);
  const prepared=prepareNativeEvidence(f,{workspace:f.workspace});
  assert.equal(prepared.assessment.profileState,'complete');assert.equal(prepared.assessment.storyNativeProof,'qualified-external');
  assert.equal(prepared.assessment.origin,'external-machine');
  const history=join(f.runDir,'evidence','first');mkdirSync(history,{recursive:true});
  const native={...prepared.record,originals:prepared.record.originals.map((row,index)=>{const savedPath=`evidence/first/${index}`;writeFileSync(join(f.runDir,savedPath),prepared.originals[index].bytes);return {...row,savedPath};})};
  writeFileSync(join(f.runDir,'status.json'),JSON.stringify({v:1,number:1,runId:f.runId,root:f.root,evidence:[{at:1,native}]}));
  const reread=await assessNativeEvidence(f,{workspace:f.workspace});assert.equal(reread.storyNativeProof,'qualified-external');
  writeFileSync(join(history,'1'),'changed');
  const changed=await assessNativeEvidence(f,{workspace:f.workspace});assert.equal(changed.profileNativeProof,'none');assert.equal(changed.receiptState,'unknown');
});
test('source edits and lowered local profile retain approved inventory and give no current proof',async t=>{
  const f=await fixture(t),before=prepareNativeEvidence(f,{workspace:f.workspace});
  git(f.root,'-c','user.name=Native test','-c','user.email=native@example.invalid','commit','-qm','synthetic approved fixture');
  writeFileSync(join(f.root,'source.mjs'),'export const value = 2;\n');
  assert.equal(prepareNativeEvidence(f,{workspace:f.workspace}).assessment.profileNativeProof,'none');
  const promptPath=join(f.root,'prompts/native.prompt.md'),old=readFileSync(promptPath,'utf8');
  writeFileSync(promptPath,old.replace(JSON.stringify([f.a,f.b]),JSON.stringify([f.a])));
  const prepared=prepareNativeEvidence(f,{workspace:f.workspace});
  assert.equal(prepared.assessment.requiresReview,true);
  assert.deepEqual(prepared.assessment.requiredIds,[f.a,f.b]);
  assert.equal(before.record.reviewedPrompt.content,old);
});
test('unverified report flags never replace canonical association or original source',async t=>{
  const f=await fixture(t);
  const prepared=prepareNativeEvidence(f);
  assert.equal(prepared.assessment.profileNativeProof,'none');
  assert.equal(prepared.assessment.origin,'external-machine');
  assert.equal(prepared.record.intake.stage,'unknown');
});
test('hostile and missing originals refuse before file writes',async t=>{
  const f=await fixture(t);f.save('report','<!DOCTYPE x SYSTEM "https://invalid.example"><testsuite/>');
  const result=prepareNativeEvidence(f,{workspace:f.workspace});assert.equal(result.assessment.profileNativeProof,'none');
  rmSync(join(f.root,'originals/report'));
  assert.throws(()=>prepareNativeEvidence(f),/ENOENT/);
});
for(const [format,bytes]of [
  ['tap13','TAP version 13\nok 1 - required A\nok 2 - required B # SKIP missing fixture\n1..2\n'],
  ['junit-xml','<?xml version="1.0"?><testsuite tests="2"><testcase file="test/native.mjs" name="required A" line="1" column="1"/><testcase file="test/native.mjs" name="required B" line="2" column="1"><skipped message="missing fixture"/></testcase></testsuite>']
])test(`original ${format} keeps occurrences, skips and unknown provenance`,async t=>{
  const f=await fixture(t,format);f.save('report',bytes);
  const prepared=prepareNativeEvidence(f,{workspace:f.workspace});
  assert.equal(prepared.assessment.occurrenceCount,2);assert.equal(prepared.assessment.observations[1].outcome,'skipped');
  assert.equal(prepared.assessment.observations[1].skipReason,'missing fixture');
  assert.equal(prepared.assessment.profileNativeProof,'none');
  assert.deepEqual(prepared.originals[1].bytes,Buffer.from(bytes));
});
test('gate flags alone cannot establish execution; original linked occurrence is required',async t=>{
  const f=await fixture(t),path=join(f.root,'prompts/native.prompt.md');
  const prompt=readFileSync(path,'utf8').replace('"requiredGates":[]','"requiredGates":["suite"]').replace('"source":"/source"','"source":"/source","gates":"/gates"');
  writeFileSync(path,prompt);
  await recordPromptApproval({commonDir:join(f.root,'.git'),evidence:{id:'gate-review',route:'terminal',actor:{kind:'terminal',id:'test'},at:2,words:'Synthetic gate review.',prompts:[{path:'prompts/native.prompt.md',proseSha256:proseSha256(prompt)}]}});
  const current=prepareNativeEvidence(f).assessment.identity;
  const source=JSON.parse(readFileSync(join(f.root,'originals/source.json')));source.source={sourceId:current.sourceId,implementationId:current.implementationId,testsId:current.testsId};source.source_sha256=current.sourceId;f.save('source.json',source);
  for(const name of ['selection','execution']){const row=JSON.parse(readFileSync(join(f.root,`originals/${name}.json`)));row.sourceId=current.sourceId;f.save(name+'.json',row);}
  f.descriptor.originals.push({path:'gate.json',role:'gate'});f.save('import.json',f.descriptor);
  f.save('gate.json',{id:'suite',sourceId:current.sourceId,stage:'current',executed:true,outcome:'passed'});
  const claimed=prepareNativeEvidence(f,{workspace:f.workspace});
  assert.equal(claimed.assessment.profileState,'incomplete');assert.deepEqual(claimed.assessment.unexecutedGates,['suite']);
  const report=JSON.parse(readFileSync(join(f.root,'originals/report')));report.gates=[{id:'suite',outcome:'passed',occurrenceRef:'a'}];f.save('report',report);
  const reportRef='sha256:'+ (await import('node:crypto')).createHash('sha256').update(readFileSync(join(f.root,'originals/report'))).digest('hex');
  f.save('gate.json',{id:'suite',sourceId:current.sourceId,stage:'current',outcome:'passed',occurrenceRef:'a',reportRef});
  const linked=prepareNativeEvidence(f,{workspace:f.workspace});assert.equal(linked.assessment.profileState,'complete');
});
test('nested TAP identities and per-suite plans remain separate, bailout and truncation stay partial',async t=>{
  const f=await fixture(t,'tap13');
  f.save('report','TAP version 13\n# Subtest: suite one\n    # Subtest: child\n    ok 1 - child\n    1..1\nok 1 - suite one\n# Subtest: suite two\n    # Subtest: child\n    ok 1 - child # TODO pending\n    1..1\nok 2 - suite two\n1..2\n');
  const nested=prepareNativeEvidence(f,{workspace:f.workspace}).assessment;
  assert.equal(nested.occurrenceCount,4);assert.equal(nested.observations[0].testId,'suite one::child');assert.equal(nested.observations[2].testId,'suite two::child');assert.equal(nested.observations[2].outcome,'todo');
  f.save('report','TAP version 13\nok 1 - first\n1..2\n');
  assert.equal(prepareNativeEvidence(f,{workspace:f.workspace}).assessment.receiptState,'partial');
  f.save('report','TAP version 13\nok 1 - first\nBail out! incomplete\n1..1\n');
  assert.equal(prepareNativeEvidence(f,{workspace:f.workspace}).assessment.receiptState,'partial');
});
test('JUnit forbids entity documents and retains duplicate failed/skipped occurrences',async t=>{
  const f=await fixture(t,'junit-xml');
  f.save('report','<!DOCTYPE testsuite [<!ENTITY secret SYSTEM "file:///etc/passwd">]><testsuite><testcase name="&secret;"/></testsuite>');
  assert.equal(prepareNativeEvidence(f,{workspace:f.workspace}).assessment.profileNativeProof,'none');
  f.save('report','<testsuite><testcase file="test/native.mjs" name="required A" line="1" column="1"><failure/></testcase><testcase file="test/native.mjs" name="required A" line="1" column="1"><skipped message="second discovery"/></testcase></testsuite>');
  const a=prepareNativeEvidence(f,{workspace:f.workspace}).assessment;
  assert.equal(a.occurrenceCount,2);assert.deepEqual(a.duplicateIds,[f.a]);assert.deepEqual(a.failedIds,[f.a]);assert.deepEqual(a.skippedIds,[f.a]);assert.deepEqual(a.missingIds,[f.b]);
});
test('profile completion is kept distinct from incomplete Story mappings in saved result consumers',async t=>{
  const f=await fixture(t),prepared=prepareNativeEvidence(f,{workspace:f.workspace});
  const history=join(f.runDir,'evidence','first');mkdirSync(history,{recursive:true});
  const native={...prepared.record,originals:prepared.record.originals.map((row,index)=>{const savedPath=`evidence/first/${index}`;writeFileSync(join(f.runDir,savedPath),prepared.originals[index].bytes);return {...row,savedPath};})};
  writeFileSync(join(f.runDir,'status.json'),JSON.stringify({v:1,number:1,runId:f.runId,root:f.root,evidence:[{at:1,native}]}));
  const {readRunResults,resultLines,usableResult}=await import('../src/workflow-results.mjs');
  const results=readRunResults(f,{workspace:f.workspace,env:{PDD_STATE_DIR:join(f.root,'no-runtime')}});
  assert.equal(results.length,1);assert.equal(results[0].kind,'native evidence');assert.equal(usableResult(results[0]),true);
  const line=resultLines(results)[0];assert.match(line,/AC1: supported/);assert.match(line,/qualified-external/);assert.match(line,/command was not observed by PDD/);
  const storyPath=join(f.root,'user_stories/native.md');
  writeFileSync(storyPath,readFileSync(storyPath,'utf8').replace('Both native effects work.','The current criterion changed.'));
  const unmapped=readRunResults(f,{workspace:f.workspace,env:{PDD_STATE_DIR:join(f.root,'no-runtime')}});
  assert.equal(unmapped[0].assessment.profileState,'complete');
  assert.equal(unmapped[0].assessment.profileNativeProof,'qualified-external');
  assert.equal(unmapped[0].assessment.criteria[0].reason,'criterion-changed');
  assert.equal(usableResult(unmapped[0]),false);
  writeFileSync(join(f.root,'source.mjs'),'changed source\n');
  const changed=readRunResults(f,{workspace:f.workspace,env:{PDD_STATE_DIR:join(f.root,'no-runtime')}});
  assert.equal(usableResult(changed[0]),false);assert.match(resultLines(changed)[0],/Story native proof: none/);
});
test('fixture proof checks original occurrence, actual artifact bytes and source rather than verified flags',async t=>{
  const f=await fixture(t),crypto=await import('node:crypto'),artifact='controlled artifact\n',artifactId=crypto.createHash('sha256').update(artifact).digest('hex');
  f.save('artifact.bin',artifact);
  const path=join(f.root,'prompts/native.prompt.md'),prompt=readFileSync(path,'utf8').replace('"fixtures":[]',`"fixtures":[{"id":"fixture","artifactId":"${artifactId}"}]`).replace('"source":"/source"','"source":"/source","prerequisites":"/prerequisites"');writeFileSync(path,prompt);
  await recordPromptApproval({commonDir:join(f.root,'.git'),evidence:{id:'fixture-review',route:'terminal',actor:{kind:'terminal',id:'test'},at:2,words:'Synthetic fixture review.',prompts:[{path:'prompts/native.prompt.md',proseSha256:proseSha256(prompt)}]}});
  const current=prepareNativeEvidence(f).assessment.identity,source=JSON.parse(readFileSync(join(f.root,'originals/source.json')));source.source={sourceId:current.sourceId,implementationId:current.implementationId,testsId:current.testsId};source.source_sha256=current.sourceId;f.save('source.json',source);
  for(const name of ['selection','execution']){const row=JSON.parse(readFileSync(join(f.root,`originals/${name}.json`)));row.sourceId=current.sourceId;f.save(name+'.json',row);}
  const report=JSON.parse(readFileSync(join(f.root,'originals/report')));report.prerequisites=[{id:'fixture',artifactId,occurrenceRef:'b'}];f.save('report',report);
  const reportRef='sha256:'+crypto.createHash('sha256').update(readFileSync(join(f.root,'originals/report'))).digest('hex');
  f.descriptor.originals.push({path:'fixture.json',role:'fixture'});f.save('import.json',f.descriptor);
  const original={id:'fixture',artifactId,sourceId:current.sourceId,stage:'current',reportRef,occurrenceRef:'b',path:'artifact.bin',state:'verified'};f.save('fixture.json',original);
  const checked=prepareNativeEvidence(f,{workspace:f.workspace});assert.equal(checked.assessment.profileState,'complete');assert.equal(checked.assessment.prerequisites[0].state,'verified');
  f.save('artifact.bin','different bytes');
  const changed=prepareNativeEvidence(f,{workspace:f.workspace});assert.equal(changed.assessment.profileState,'incomplete');assert.equal(changed.assessment.prerequisites[0].state,'incompatible');
  rmSync(join(f.root,'originals/artifact.bin'));
  const missing=prepareNativeEvidence(f,{workspace:f.workspace});assert.equal(missing.assessment.prerequisites[0].state,'missing');assert.equal(missing.assessment.profileNativeProof,'none');
  f.save('fixture.json',{...original,path:undefined,verified:true});
  assert.equal(prepareNativeEvidence(f,{workspace:f.workspace}).assessment.prerequisites[0].state,'unknown');
});
