import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {appendFileSync,mkdirSync,readFileSync,readdirSync,renameSync,symlinkSync,unlinkSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {createHash,randomUUID} from 'node:crypto';
import {captureSource,interfaceBlocks,proseSha256} from '../src/runtime-seam.mjs';
import {readRunResults} from '../src/workflow-results.mjs';
import {fullCheckPass} from '../src/workflow-story-card.mjs';
import {affectedFixture,affectedRuntime,batch,check,checks,commit,disclaimer,historicalAssociation,put,vectors} from './helpers/affected-check-fixture.mjs';
const cases=vectors('affected-baseline-report').cases;
const vector=id=>{const data=cases.find(item=>item.id===id);assert.ok(data);return data;};
const c='test/runtime/C.json';
const file=(setup,id,name='batch.json')=>join(setup.state,'batches',id,name);
const read=(setup,id,name)=>JSON.parse(readFileSync(file(setup,id,name),'utf8'));
const write=(setup,id,value,name)=>writeFileSync(file(setup,id,name),JSON.stringify(value));
// A synthetic historical POST must retain its independent per-test dispatch identity.
const claim=(setup,saved,row,index,id)=>write(setup,saved.batch,{id,restart:index>0},`${createHash('sha256').update(row.test).digest('hex')}.${index}.dispatch.json`);
const saveBytes=(setup,id)=>Object.fromEntries(readdirSync(join(setup.state,'batches',id)).map(name=>[name,readFileSync(file(setup,id,name),'utf8')]));
async function original(t,{full=false,fail=true}={}) {
  const setup=affectedFixture(t),fake=await affectedRuntime(t,setup,{fail:fail?[c]:[]});
  const result=await check(setup,fake,{words:full?[]:['C'],options:{'--json':true}});assert.equal(result.code,fail?1:0,result.ports.stderr.text);
  return {setup,fake,result,saved:batch(setup,result.output.batch)};
}

test('3146 original-failure-separate: selected batch keeps original failed receipt with no C execution or history writes',async t=>{
  const data=vector('original-failure-separate'),{setup,fake,result,saved}=await original(t);
  const originalRow=saved.rows.find(row=>row.test===c),oldId=originalRow.request_ids[0];
  // Map the approved symbolic batch name to the real native batch ID; preserve its exact receipt identity and time.
  const receipt=read(setup,saved.batch,`${oldId}.json`);receipt.id=receipt.requestId=data.given.saved_C.request_id;
  write(setup,saved.batch,receipt,`${receipt.id}.json`);originalRow.request_ids=[receipt.id];claim(setup,saved,originalRow,0,receipt.id);saved.created_at=data.given.saved_C.created_at;write(setup,saved.batch,saved);
  const bytes=saveBytes(setup,saved.batch),offset=checks(fake).length;setup.change('docs/shared.md');
  const selected=await check(setup,fake,{advance:2000});assert.equal(selected.code,0,selected.ports.stderr.text);
  assert.deepEqual(selected.output.rows.map(row=>row.test),data.expected.batch_rows_tests);
  assert.equal(checks(fake).slice(offset).filter(row=>row.request.scenario===c).length,data.expected.C_paid_posts);
  const observed=selected.output.baseline_report.observations.find(row=>row.request_id===receipt.id);
  assert.deepEqual(observed,{story_path:'user_stories/C.md',test:c,batch:saved.batch,request_id:receipt.id,evidence_kind:'receipt',state:'failed',reason:{code:'check-failed',message:'Checks failed.'},created_at:data.given.saved_C.created_at,report_url:receipt.report_url,source_sha256:saved.source_sha256,currentness:'current',currentness_scope:'original-batch',stage:'current'});
  assert.deepEqual(saveBytes(setup,saved.batch),bytes);
  const current=batch(setup,selected.output.batch);assert.deepEqual(current.baseline_report,selected.output.baseline_report);assert.deepEqual(current.check_selection,selected.output.check_selection);
  assert.equal(result.output.exit_code,1);
});

test('3146 older-failure-not-lost and all-original-attempts preserve every original sent attempt',async t=>{
  vector('older-failure-not-lost');vector('all-original-attempts');
  const {setup,fake,saved}=await original(t);const old=saved.rows[0].request_ids[0],passed=randomUUID();
  const originalReceipt=read(setup,saved.batch,`${old}.json`),newReceipt=structuredClone(originalReceipt);newReceipt.id=newReceipt.requestId=passed;newReceipt.state='passed';newReceipt.result.outcome='Pass';newReceipt.result.exitCode=0;newReceipt.result.why='All checked criteria passed.';
  for(const sample of newReceipt.result.report.samples)for(const step of sample.steps)for(const check of step.checks){check.actual=check.expected;check.passed=true;}
  for(const criterion of newReceipt.result.report.criterion_results)criterion.status='passed';
  write(setup,saved.batch,newReceipt,`${passed}.json`);saved.rows[0].request_ids.push(passed);claim(setup,saved,saved.rows[0],1,passed);saved.rows[0].state='passed';write(setup,saved.batch,saved);
  // A later local placeholder is a distinct observation; it cannot replace the two sent receipts.
  const local={...structuredClone(saved),batch:'20261028-162747-abcd',created_at:'2026-10-28T16:27:47Z'};local.rows[0]={...local.rows[0],request_ids:[],unsent:true,state:'not run',reason:{code:'no-server-verdict',message:'Local placeholder.'}};
  put(setup.state,`batches/${local.batch}/batch.json`,local);setup.change('docs/shared.md');const offset=checks(fake).length;
  const result=await check(setup,fake,{advance:3000});assert.equal(result.code,0,result.ports.stderr.text);
  const observations=result.output.baseline_report.observations;
  assert.equal(observations.find(row=>row.request_id===old).state,'failed');assert.equal(observations.find(row=>row.request_id===passed).state,'passed');assert.equal(observations.at(-1).state,'not run');assert.deepEqual(observations.map(row=>row.request_id),[old,passed,null].sort((a,b)=>a===null?1:b===null?-1:a.localeCompare(b)));
  assert.equal(observations.filter(row=>row.evidence_kind==='receipt').length,2);assert.equal(checks(fake).slice(offset).length,3);
});

test('3146 canonical-nonpass-outcomes uses original receipt outcomes and reason codes',async t=>{
  const data=vector('canonical-nonpass-outcomes'),{setup,fake,saved}=await original(t);const row=saved.rows[0],template=read(setup,saved.batch,`${row.request_ids[0]}.json`);
  row.request_ids=[];
  for(const state of data.given.C_history_states) {
    const id=randomUUID(),receipt=structuredClone(template);receipt.id=receipt.requestId=id;receipt.state=state==='not_run'?'refused':state;
    if(['queued','running'].includes(state))receipt.result=null;
    else if(state==='not_run'){receipt.result.outcome='NotRun';receipt.result.refusals=[{code:'not-run-fixture',message:'Not run.',retryable:true}];receipt.dispatch='not_started';}
    else if(state==='refused'){receipt.result.refusals=[{code:'fixture-refused',message:'Fixture refused.'}];receipt.result.outcome='Inconclusive';}
    else if(state==='unknown')receipt.result.outcome='Inconclusive';
    write(setup,saved.batch,receipt,`${id}.json`);row.request_ids.push(id);claim(setup,saved,row,row.request_ids.length-1,id);
  }
  write(setup,saved.batch,saved);setup.change('docs/shared.md');const result=await check(setup,fake,{advance:1000});assert.equal(result.code,0);
  const byId=new Map(result.output.baseline_report.observations.map(row=>[row.request_id,row]));
  for(const [index,id] of row.request_ids.entries())assert.equal(byId.get(id).state,data.expected.display_states[index]);
  assert.equal([...byId.values()].some(row=>row.state==='passed'),false);
});

test('3146 current-stale-unavailable compares each original complete batch source selection',async t=>{
  const data=vector('current-stale-unavailable');
  for(const [index,variant] of data.given.capture_variants.entries())await t.test(variant,async t=>{
    const {setup,fake,saved}=await original(t,{full:true});
    if(index===3){delete saved.source_sha256;write(setup,saved.batch,saved);}
    const historyTests=[];setup.change('docs/shared.md');
    const result=await check(setup,fake,{advance:1000,extra:{captureSource(root,selection){
      if(selection.tests?.length===4){historyTests.push(selection.tests);if(index===2)throw Error('Controlled original-batch capture unavailable');const captured=captureSource(root,selection);return index===0?{...captured,sha256:saved.source_sha256}:captured;}
      return captureSource(root,selection);
    }}});
    assert.equal(result.code,0,result.ports.stderr.text);
    const observed=result.output.baseline_report.observations.find(row=>row.test===c);assert.equal(observed.currentness,data.expected.currentness[index]);assert.equal(observed.currentness_scope,data.expected.currentness_scope);
    if(index<3)assert.ok(historyTests.length>0);
    assert.equal(observed.owner,undefined);assert.equal(observed.defect_age,undefined);
  });
});

test('3146 no-evidence-and-corruption retains readable failure and never accepts saved passed labels',async t=>{
  const data=vector('no-evidence-and-corruption');
  for(const variant of data.given.history_variants)await t.test(variant,async t=>{
    const setup=affectedFixture(t),fake=await affectedRuntime(t,setup,{fail:[c]});let saved;
    if(!['missing state folder','unreadable directory'].includes(variant)) {
      const seeded=await check(setup,fake,{words:['C'],options:{'--json':true}});assert.equal(seeded.code,1);saved=batch(setup,seeded.output.batch);
      const other={...structuredClone(saved),batch:'20261028-000000-abcd'};
      if(variant==='corrupt batch beside readable C failure')put(setup.state,`batches/${other.batch}/batch.json`,'{broken');
      if(variant==='missing or mismatched receipt beside readable C failure')put(setup.state,`batches/${other.batch}/batch.json`,other);
      if(variant==='saved passed label without receipt'){saved.rows[0].state='passed';saved.rows[0].request_ids=[randomUUID()];write(setup,saved.batch,saved);}
    }
    setup.change('docs/shared.md');const gets=fake.gets.length;
    const result=await check(setup,fake,{advance:1000,extra:variant==='unreadable directory'?{baselineFiles:{list(){throw Object.assign(Error('Denied'),{code:'EACCES'});},read(){throw Error('Unexpected read');}}}:{}});
    assert.equal(result.code,0,result.ports.stderr.text);assert.equal(fake.gets.length,gets);
    const report=result.output.baseline_report;assert.equal(report.observations.some(row=>row.state==='passed'),false);
    if(variant.includes('beside readable'))assert.ok(report.observations.some(row=>row.state==='failed'));
    else assert.deepEqual(report.missing_tests,[c]);
    assert.ok(['unavailable','partial'].includes(report.availability));
  });
});

test('3146 foreign-and-historical-admission rejects foreign, runtime/account and unowned association history',async t=>{
  const data=vector('foreign-and-historical-admission');
  for(const variant of data.given.record_variants.slice(0,4))await t.test(variant,async t=>{
    const {setup,fake,saved}=await original(t);
    if(variant==='foreign root')saved.root=join(setup.sandbox,'foreign');
    if(variant==='different runtime/account')saved.user_id='4243';
    if(variant==='ineligible association')saved.association={runId:'unowned',stage:'pr1'};
    if(variant==='missing ownership')delete saved.login;
    write(setup,saved.batch,saved);setup.change('docs/shared.md');const result=await check(setup,fake,{advance:1000});assert.equal(result.code,0);
    assert.deepEqual(result.output.baseline_report.observations,[]);assert.deepEqual(result.output.baseline_report.missing_tests,[c]);
  });
});

test('3146 safe-links-and-original-time validates links and never substitutes read time',async t=>{
  const data=vector('safe-links-and-original-time'),{setup,fake,saved}=await original(t);saved.created_at=data.given.saved_time;
  const id=saved.rows[0].request_ids[0],receipt=read(setup,saved.batch,`${id}.json`);receipt.report_url='https://unsafe.example.test/r/ghp_secret_fixture';write(setup,saved.batch,receipt,`${id}.json`);write(setup,saved.batch,saved);setup.change('docs/shared.md');
  const result=await check(setup,fake,{advance:1000});const observed=result.output.baseline_report.observations[0];assert.equal(observed.created_at,data.expected.original_time);assert.equal(observed.report_url,data.expected.unsafe_report_url);assert.equal(JSON.stringify(result.output).includes('ghp_secret_fixture'),false);
});

test('3146 proposed-selected-exit-blocking-gate: real unchanged fullCheckPass still blocks beside selected zero exit',async t=>{
  const data=vector('proposed-selected-exit-blocking-gate');
  for(const strict of data.given.strict_modes)await t.test(String(strict),async t=>{
    const {setup,fake}=await original(t);put(setup.repo,'pdd.json',{strict_approvals:strict});commit(setup.repo);setup.change('docs/shared.md');
    const result=await check(setup,fake,{advance:2000});assert.equal(result.code,data.expected.affected_exit_code);assert.ok(result.output.warnings.includes(data.expected.required_text));
    assert.equal(fullCheckPass({root:setup.repo},{env:result.ports.env}).pass,data.expected.fullCheckPass);
    assert.equal(result.output.approval,undefined);
  });
});

test('3146 saved-read-retry-snapshot and workflow-result-consumer retain exact snapshots and scope',async t=>{
  vector('saved-read-retry-snapshot');vector('workflow-result-consumer');
  const {setup,fake}=await original(t);setup.change('docs/shared.md');const selected=await check(setup,fake,{advance:1000});assert.equal(selected.code,0);
  const snapshot=selected.output.baseline_report,selection=selected.output.check_selection,plan=selected.output.check_plan;setup.change('prompts/C.prompt.md');
  fake.failTests.splice(0);const later=await check(setup,fake,{words:['C'],options:{'--json':true},advance:2000});assert.equal(later.code,0);
  const before=checks(fake).length;
  for(const options of [{'--read':true,'--json':true},{'--retry':selected.output.batch,'--json':true}]) {
    const result=await check(setup,fake,{words:options['--read']?[selected.output.batch]:[],options,advance:3000});assert.equal(result.code,0,result.ports.stderr.text);
    assert.deepEqual(result.output.baseline_report,snapshot);assert.deepEqual(result.output.check_selection,selection);assert.deepEqual(result.output.check_plan,plan);
  }
  assert.equal(checks(fake).length,before);
  // Read this selected batch as newest in an isolated raw-history view, retaining real reader behavior.
  unlinkSync(file(setup,later.output.batch));
  const results=readRunResults({root:setup.repo},{env:selected.ports.env});
  assert.deepEqual(results[0].baselineReport,snapshot);assert.deepEqual(results[0].checkSelection,selection);assert.deepEqual(results[0].states.map(row=>row.test),selection.tests);
  assert.ok(results[0].summary.includes(disclaimer));assert.equal(results[0].states.some(row=>row.test===c),false);
});

test('3146 missing-and-stale-gates preserves native cross-batch full-pass accumulation',async t=>{
  const data=vector('missing-and-stale-gates');
  for(const [index,variant] of data.given.C_evidence_variants.entries())await t.test(variant,async t=>{
    const setup=affectedFixture(t),fake=await affectedRuntime(t,setup);let saved;
    if(variant!=='missing'){
      const seeded=await check(setup,fake,{words:['C'],options:{'--json':true}});assert.equal(seeded.code,0);saved=batch(setup,seeded.output.batch);
      if(variant==='stale'){setup.change('prompts/C.prompt.md');commit(setup.repo);}
      if(['refused','partial'].includes(variant)){
        const summary=read(setup,saved.batch,'summary.json');saved.rows[0].state=variant;summary.rows[0].state=variant;write(setup,saved.batch,saved);write(setup,saved.batch,summary,'summary.json');
        const id=saved.rows[0].request_ids[0],receipt=read(setup,saved.batch,`${id}.json`);receipt.state=variant==='partial'?'unknown':'refused';write(setup,saved.batch,receipt,`${id}.json`);
      }
    }
    setup.change('docs/shared.md');const result=await check(setup,fake,{advance:1000});assert.equal(result.code,0,result.ports.stderr.text);
    assert.equal(fullCheckPass({root:setup.repo},{env:result.ports.env}).pass,data.expected.fullCheckPass_by_variant[index]);
    assert.deepEqual(result.output.rows.map(row=>row.test),setup.selected);assert.equal(result.output.rows.some(row=>row.test===c),false);
  });
});


test('3146 foreign-and-historical-admission: production registration retains PR1/before stage and original source',async t=>{
  const data=vector('foreign-and-historical-admission');
  for(const variant of data.given.record_variants.slice(4))await t.test(variant,async t=>{
    const stage=variant.includes('pr1')?'pr1':'before', {setup,fake,saved}=await original(t,{fail:false});
    const registered=await historicalAssociation(setup,stage);saved.association={runId:registered.run.runId,stage};write(setup,saved.batch,saved);
    setup.change('docs/shared.md');const result=await check(setup,fake,{advance:1000});assert.equal(result.code,0,result.ports.stderr.text);
    const observation=result.output.baseline_report.observations[0];assert.ok(observation,JSON.stringify(result.output.baseline_report));
    assert.equal(observation.stage,stage);assert.equal(observation.currentness,'current');assert.equal(observation.currentness_scope,'original-batch');
    assert.equal(observation.batch,saved.batch);assert.equal(observation.request_id,saved.rows[0].request_ids[0]);
    assert.equal(observation.evidence_kind,'receipt');assert.equal(result.output.rows.some(row=>row.test===c),false);
  });
});

test('3146 saved-read-retry-snapshot: uncertain target receipt keeps identity and never reposts or widens to C',async t=>{
  const setup=affectedFixture(t);let uncertain=false;const unknownIds=new Set();
  const fake=await affectedRuntime(t,setup,{fail:[c],answer(entry,f){
    if(uncertain && entry.command==='check' && entry.request.scenario==='test/runtime/A.json'){
      unknownIds.add(entry.request.requestId);return {status:200,json:f.check(entry.request.requestId,'unknown')};
    }
    const id=entry.url?.split('/').at(-1);if(entry.method==='GET' && unknownIds.has(id))return {status:200,json:f.check(id,'unknown')};
  }});
  const original=await check(setup,fake,{words:['C'],options:{'--json':true}});assert.equal(original.code,1);
  setup.change('docs/shared.md');uncertain=true;const initial=await check(setup,fake,{advance:1000});assert.equal(initial.code,3);
  const snapshot=initial.output.baseline_report,selection=initial.output.check_selection,ids=batch(setup,initial.output.batch).rows.find(row=>row.test==='test/runtime/A.json').request_ids;
  setup.change('prompts/C.prompt.md');fake.failTests.splice(0);const later=await check(setup,fake,{words:['C'],options:{'--json':true},advance:2000});assert.equal(later.code,0);
  const posts=checks(fake).length;
  for(const options of [{'--read':true,'--json':true},{'--retry':initial.output.batch,'--json':true}]){
    const result=await check(setup,fake,{words:options['--read']?[initial.output.batch]:[],options,advance:3000});assert.equal(result.code,3,result.ports.stderr.text);
    assert.deepEqual(result.output.baseline_report,snapshot);assert.deepEqual(result.output.check_selection,selection);
    assert.deepEqual(batch(setup,initial.output.batch).rows.find(row=>row.test==='test/runtime/A.json').request_ids,ids);
    assert.match(result.output.check_scope.guidance,/unresolved selected checks: test\/runtime\/A.json/);assert.match(result.output.check_scope.guidance,/Omitted baseline work: test\/runtime\/C.json/);
  }
  assert.equal(checks(fake).length,posts);
});

test('3146 retained original receipt observations preserve an earlier failure when one request later reports a pass',async t=>{
  const {setup,fake,saved}=await original(t),id=saved.rows[0].request_ids[0],failed=read(setup,saved.batch,`${id}.json`),passed=structuredClone(failed);
  passed.state='passed';passed.result.outcome='Pass';passed.result.exitCode=0;passed.result.why='All checked criteria passed.';
  for(const sample of passed.result.report.samples)for(const step of sample.steps)for(const item of step.checks){item.actual=item.expected;item.passed=true;}
  for(const criterion of passed.result.report.criterion_results)criterion.status='passed';
  write(setup,saved.batch,[failed],`${id}.observations.json`);write(setup,saved.batch,passed,`${id}.json`);
  setup.change('docs/shared.md');const result=await check(setup,fake,{advance:1000});assert.equal(result.code,0);
  const history=result.output.baseline_report.observations.filter(row=>row.request_id===id);assert.deepEqual(history.map(row=>row.state),['failed','passed']);
});


test('3146 accepted symlinked state ancestors retain baseline history while linked batches and receipts are refused',async t=>{
  for(const escape of ['none','batch','receipt'])await t.test(escape,async t=>{
    const {setup,fake,saved}=await original(t),id=saved.rows[0].request_ids[0];
    const parent=join(setup.sandbox,'canonical-state-parent');mkdirSync(parent);renameSync(setup.state,join(parent,'runtime'));
    const alias=join(setup.sandbox,'state-parent-alias');symlinkSync(parent,alias);setup.state=join(alias,'runtime');
    if(escape==='batch'){
      const originalFolder=join(parent,'runtime','batches',saved.batch),outside=join(setup.sandbox,'outside-batch');renameSync(originalFolder,outside);symlinkSync(outside,originalFolder);
    }
    if(escape==='receipt'){
      const originalReceipt=join(parent,'runtime','batches',saved.batch,`${id}.json`),outside=join(setup.sandbox,'outside-receipt.json');renameSync(originalReceipt,outside);symlinkSync(outside,originalReceipt);
    }
    setup.change('docs/shared.md');const result=await check(setup,fake,{advance:1000});assert.equal(result.code,0,result.ports.stderr.text);
    if(escape==='none'){
      const observation=result.output.baseline_report.observations.find(row=>row.request_id===id);assert.equal(observation?.state,'failed');assert.equal(observation?.batch,saved.batch);
    }else{
      assert.deepEqual(result.output.baseline_report.observations,[]);assert.deepEqual(result.output.baseline_report.missing_tests,[c]);assert.equal(result.output.baseline_report.availability,'partial');
    }
  });
});

test('3146 a receipt outside its original producer selection cannot invent a C pass',async t=>{
  const setup=affectedFixture(t),fake=await affectedRuntime(t,setup,{fail:[c]});
  const failure=await check(setup,fake,{words:['C'],options:{'--json':true}});assert.equal(failure.code,1);
  const failed=batch(setup,failure.output.batch),oldId=failed.rows[0].request_ids[0];
  const seed=await check(setup,fake,{words:['A'],options:{'--json':true},advance:1000});assert.equal(seed.code,0);
  const saved=batch(setup,seed.output.batch);saved.rows[0].test=c;saved.rows[0].story_path='user_stories/C.md';write(setup,saved.batch,saved);
  const offset=checks(fake).length;setup.change('prompts/B.prompt.md');
  const result=await check(setup,fake,{advance:2000});assert.equal(result.code,0,result.ports.stderr.text);
  const report=result.output.baseline_report;
  assert.equal(report.observations.some(row=>row.test===c&&row.state==='passed'),false,'3146_FOREIGN_SELECTION_PASS: an A-only receipt was attributed as a C pass');
  assert.ok(report.observations.some(row=>row.test===c&&row.request_id===oldId&&row.state==='failed'),'readable original C failure must survive corrupt neighboring history');
  assert.equal(report.availability,'partial');assert.ok(report.warnings.length>0);
  assert.deepEqual(checks(fake).slice(offset).map(row=>row.request.scenario),['test/runtime/B.json']);
});

test('3146 contradictory producer rows, snapshots, requests and receipt source identity supply no pass',async t=>{
  for(const variant of ['row Story','row basename','outside manifest','snapshot Story','snapshot source hash','duplicate snapshot','duplicate row','shared request','request from A','crossed requests','receipt source hash','receipt projected source','receipt execution entry'])await t.test(variant,async t=>{
    const {setup,fake,saved}=await original(t,{full:true,fail:false}),row=saved.rows.find(row=>row.test===c),id=row.request_ids[0];
    const a=saved.rows.find(row=>row.test==='test/runtime/A.json'),snapshot=saved.contract_snapshots.find(story=>story.story_path==='user_stories/C.md');
    if(variant==='row Story')row.story_path='user_stories/A.md';
    if(variant==='row basename')row.story='A';
    if(variant==='outside manifest')saved.files=saved.files.filter(path=>path!==c);
    if(variant==='snapshot Story')snapshot.story_path='user_stories/A.md';
    if(variant==='snapshot source hash')snapshot.files.find(file=>file.path===c).sha256='a'.repeat(64);
    if(variant==='duplicate snapshot')saved.contract_snapshots.push(structuredClone(snapshot));
    if(variant==='duplicate row')saved.rows.push(structuredClone(row));
    if(variant==='shared request')a.request_ids.push(id);
    if(variant==='request from A'){row.request_ids=[a.request_ids[0]];a.request_ids=[];}
    if(variant==='crossed requests'){
      const own=row.request_ids;row.request_ids=a.request_ids;a.request_ids=own;
      // This protocol variant gives only a whole-batch hash, so claims must bind the Check IDs.
      for(const requestId of [...row.request_ids,...a.request_ids]){const raw=read(setup,saved.batch,`${requestId}.json`);delete raw.result.report.call_depth;write(setup,saved.batch,raw,`${requestId}.json`);}
    }
    const receipt=read(setup,saved.batch,`${id}.json`);
    if(variant==='receipt source hash')receipt.source_sha256='a'.repeat(64);
    if(variant==='receipt projected source')receipt.result.report.projected_context_bindings=[{prompt_path:'prompts/C.prompt.md',prompt_sha256:'a'.repeat(64),context_blobs:[]}];
    if(variant==='receipt execution entry')receipt.result.report.call_depth[0].entry_path='prompts/A.prompt.md';
    write(setup,saved.batch,receipt,`${id}.json`);write(setup,saved.batch,saved);
    setup.change('docs/shared.md');const result=await check(setup,fake,{advance:2000});assert.equal(result.code,0,result.ports.stderr.text);
    const report=result.output.baseline_report;
    assert.equal(report.observations.some(observation=>observation.test===c&&observation.state==='passed'),false,`3146_INCONSISTENT_HISTORY_PASS: ${variant}`);
    assert.equal(report.availability,'partial');assert.ok(report.warnings.length>0);
  });
});

test('3146 generic scenario report names retain correctly bound original source evidence',async t=>{
  const {setup,fake,saved}=await original(t,{fail:false}),row=saved.rows[0],id=row.request_ids[0],receipt=read(setup,saved.batch,`${id}.json`);
  assert.equal(receipt.result.report.scenario,'scenario.json');assert.equal(receipt.source_sha256,saved.source_sha256);
  const snapshot=saved.contract_snapshots[0];
  receipt.result.report.projected_context_bindings=[{prompt_path:'prompts/C.prompt.md',prompt_sha256:snapshot.files.find(file=>file.path==='prompts/C.prompt.md').sha256,context_blobs:[]}];
  write(setup,saved.batch,receipt,`${id}.json`);setup.change('docs/shared.md');
  const result=await check(setup,fake,{advance:1000});assert.equal(result.code,0,result.ports.stderr.text);
  const observation=result.output.baseline_report.observations.find(row=>row.request_id===id);
  assert.equal(observation?.state,'passed');assert.equal(observation?.story_path,'user_stories/C.md');assert.equal(result.output.baseline_report.availability,'available');
});

test('3146 malformed retained identity is partial history and cannot block selected execution',async t=>{
  for(const variant of ['null snapshot file','invalid capability file','invalid execution metadata','corrupt dispatch claim','missing original selection tests'])await t.test(variant,async t=>{
    const {setup,fake,saved}=await original(t,{fail:false}),row=saved.rows[0],id=row.request_ids[0];
    if(variant==='null snapshot file')saved.contract_snapshots[0].files.push(null);
    if(variant==='missing original selection tests')saved.source_selection={exclude_fixture_projects:false};
    if(variant==='corrupt dispatch claim')claim(setup,saved,row,0,'invalid');
    if(variant==='invalid execution metadata'){const receipt=read(setup,saved.batch,`${id}.json`);receipt.result.report.call_depth={unexpected:true};write(setup,saved.batch,receipt,`${id}.json`);}
    if(variant==='invalid capability file'){const lintId=saved.lint.request_ids.at(-1),receipt=read(setup,saved.batch,`${lintId}.json`);receipt.result.capabilities[0].report.source.files.push(null);write(setup,saved.batch,receipt,`${lintId}.json`);}
    write(setup,saved.batch,saved);setup.change('docs/shared.md');
    const result=await check(setup,fake,{advance:1000});assert.equal(result.code,0,result.ports.stderr.text);
    assert.deepEqual(result.output.baseline_report.observations,[]);assert.equal(result.output.baseline_report.availability,'partial');assert.ok(result.output.baseline_report.warnings.length>0);
    assert.deepEqual(result.output.rows.map(row=>row.test),setup.selected);
  });
});

test('3146 legacy raw failures remain visible with explicit missing binding diagnostics',async t=>{
  const {setup,fake,saved}=await original(t),row=saved.rows[0],id=row.request_ids[0],receipt=read(setup,saved.batch,`${id}.json`);
  delete saved.source_selection;delete saved.contract_snapshots;delete saved.source_sha256;delete saved.lint;
  delete receipt.source_sha256;delete receipt.result.report.call_depth;
  write(setup,saved.batch,receipt,`${id}.json`);write(setup,saved.batch,saved);
  for(const name of readdirSync(join(setup.state,'batches',saved.batch)))if(name.endsWith('.dispatch.json'))unlinkSync(file(setup,saved.batch,name));
  setup.change('docs/shared.md');const result=await check(setup,fake,{advance:1000});assert.equal(result.code,0,result.ports.stderr.text);
  const report=result.output.baseline_report;assert.equal(report.availability,'partial');assert.ok(report.warnings.length>0);
  const observation=report.observations.find(row=>row.request_id===id);assert.equal(observation?.state,'failed');assert.equal(observation?.currentness,'unavailable');
});

test('3146 separately identified unsent local evidence stays local outside the uploaded selection',async t=>{
  const setup=affectedFixture(t),fake=await affectedRuntime(t,setup),seed=await check(setup,fake,{words:['A'],options:{'--json':true}});assert.equal(seed.code,0);
  const saved=batch(setup,seed.output.batch);
  saved.rows.push({test:c,story:'C',story_path:'user_stories/C.md',request_ids:[],unsent:true,state:'not run',reason:{code:'no-server-verdict',message:'Local test was not sent.'}});
  write(setup,saved.batch,saved);setup.change('prompts/B.prompt.md');
  const offset=checks(fake).length,result=await check(setup,fake,{advance:1000});assert.equal(result.code,0,result.ports.stderr.text);
  const observation=result.output.baseline_report.observations.find(row=>row.test===c);
  assert.equal(observation?.evidence_kind,'local');assert.equal(observation?.request_id,null);assert.equal(observation?.state,'not run');
  assert.equal(checks(fake).slice(offset).some(row=>row.request.scenario===c),false);
});

test('3146 repair complete original currentness: mixed native and Runtime identities',async t=>{
  for(const variant of ['matching','native unavailable','stale and native unavailable','native changed','missing native identity','missing native hash','malformed native hash','array native hash','missing native tests','malformed native tests','empty native tests','unsafe native tests','duplicate native tests'])await t.test(variant,async t=>{
    const setup=affectedFixture(t),b='test/runtime/B.json',file=join(setup.repo,'prompts/B.prompt.md');
    const text=readFileSync(file,'utf8'),block=interfaceBlocks(text)[0];
    writeFileSync(file,text.replace(block[1],JSON.stringify({kind:'native-only',reason:'Real process identity.',status:'draft',prose_sha256:proseSha256(text)})));commit(setup.repo);
    const fake=await affectedRuntime(t,setup,{fail:[c]}),seed=await check(setup,fake,{words:['B','C'],options:{'--json':true}});
    assert.equal(seed.code,5,seed.ports.stderr.text); // The native-only row is a final not-run outcome.
    const saved=batch(setup,seed.output.batch),row=saved.rows.find(row=>row.test===c),id=row.request_ids[0],receipt=read(setup,saved.batch,`${id}.json`);
    assert.equal(row.state,'failed');assert.equal(receipt.state,'failed');
    assert.deepEqual(saved.source_selection.tests,[c]);assert.deepEqual(saved.native_source.tests,[b]);assert.match(saved.native_source.sha256,/^[a-f0-9]{64}$/);
    if(variant==='missing native hash')delete saved.native_source.sha256;
    if(variant==='malformed native hash')saved.native_source.sha256='not-a-sha256';
    if(variant==='array native hash')saved.native_source.sha256=[saved.native_source.sha256];
    if(variant==='missing native tests')delete saved.native_source.tests;
    if(variant==='malformed native tests')saved.native_source.tests={path:b};
    if(variant==='empty native tests')saved.native_source.tests=[];
    if(variant==='unsafe native tests')saved.native_source.tests=['../outside.json'];
    if(variant==='duplicate native tests')saved.native_source.tests=[b,b];
    if(variant==='missing native identity')delete saved.native_source;
    write(setup,saved.batch,saved);const bytes=saveBytes(setup,saved.batch),offset=checks(fake).length;setup.change('prompts/A.prompt.md');
    let nativeCaptures=0;
    const result=await check(setup,fake,{advance:2000,extra:{captureSource(root,selection){
      if(Array.isArray(selection.tests) && selection.tests.length===1 && selection.tests[0]===b){
        nativeCaptures++;
        if(variant.includes('unavailable'))throw Error('Controlled original native capture unavailable');
        const captured=captureSource(root,selection);return variant==='native changed'?{...captured,sha256:'a'.repeat(64)}:captured;
      }
      const captured=captureSource(root,selection);
      return variant==='stale and native unavailable' && selection.tests?.length===1 && selection.tests[0]===c ? {...captured,sha256:'a'.repeat(64)} : captured;
    }}});
    assert.equal(result.code,0,result.ports.stderr.text);
    const report=result.output.baseline_report,observed=report.observations.find(item=>item.request_id===id);
    const expected=variant==='matching'?'current':['stale and native unavailable','native changed'].includes(variant)?'stale':'unavailable';
    assert.equal(observed?.currentness,expected,'3146_INCOMPLETE_NATIVE_ORIGINAL_SOURCE_MUST_NOT_BE_CURRENT');
    assert.equal(observed.currentness_scope,'original-batch');assert.equal(observed.state,'failed');assert.equal(observed.batch,saved.batch);
    assert.equal(observed.created_at,saved.created_at);assert.equal(observed.report_url,receipt.report_url);assert.equal(observed.owner,undefined);assert.equal(observed.defect_age,undefined);
    const local=report.observations.find(item=>item.test===b);assert.equal(local?.evidence_kind,'local');assert.equal(local?.currentness,expected);
    assert.deepEqual(checks(fake).slice(offset).map(item=>item.request.scenario).sort(),['test/runtime/A.json','test/runtime/A.recorded.json'].sort());
    assert.deepEqual(saveBytes(setup,saved.batch),bytes);
    if(variant.includes('unavailable'))assert.ok(nativeCaptures>0,'the controlled failure must reach native capture');
    if(expected==='unavailable' || variant==='stale and native unavailable'){
      assert.equal(report.availability,'partial');assert.ok(report.warnings.some(message=>/original-batch source selections.*unavailable/.test(message)));
    }
  });
});

test('3146 repair lint fixture recovery: a lost accepted lint response keeps the original lint receipt',async t=>{
  const setup=affectedFixture(t),fake=await affectedRuntime(t,setup);setup.change('docs/shared.md');
  let lost=0;
  const result=await check(setup,fake,{extra:{async fetch(url,options){
    const response=await globalThis.fetch(url,options);
    if(options?.method==='POST' && String(url).endsWith('/v1/lint') && !lost){
      await response.text();lost++;throw new TypeError('Controlled lost accepted lint response');
    }
    return response;
  }}});
  assert.equal(lost,1);assert.equal(result.code,0,result.ports.stderr.text);
  const lints=fake.posts.filter(entry=>entry.command==='lint');assert.equal(lints.length,1);
  const id=lints[0].request.requestId;assert.equal(fake.jobs.get(id)?.command,'lint');assert.ok(fake.gets.some(entry=>entry.url===`/v1/runs/${id}`));
  assert.deepEqual(result.output.rows.map(row=>row.test),setup.selected);assert.ok(result.output.rows.every(row=>row.state==='passed'));
  assert.deepEqual(checks(fake).map(entry=>entry.request.scenario).sort(),setup.selected.slice().sort());
});

test('3146 repair legacy execution binding: empty execution cannot assign a positive receipt',async t=>{
  for(const variant of ['crossed empty','own empty pass','own empty failure','own substantive pass'])await t.test(variant,async t=>{
    const {setup,fake,saved}=await original(t,{full:true,fail:variant==='crossed empty' || variant==='own empty failure'});
    const row=saved.rows.find(row=>row.test===c),a=saved.rows.find(row=>row.test==='test/runtime/A.json'),originalId=row.request_ids[0];
    const folder=join(setup.state,'batches',saved.batch);
    for(const name of readdirSync(folder))if(name.endsWith('.dispatch.json'))unlinkSync(join(folder,name));
    if(variant!=='own substantive pass')for(const id of [...row.request_ids,...a.request_ids]){
      const receipt=read(setup,saved.batch,`${id}.json`);receipt.result.report.call_depth=[];write(setup,saved.batch,receipt,`${id}.json`);
    }
    if(variant==='crossed empty')[row.request_ids,a.request_ids]=[a.request_ids,row.request_ids];
    write(setup,saved.batch,saved);const bytes=saveBytes(setup,saved.batch),offset=checks(fake).length;setup.change('docs/shared.md');
    const result=await check(setup,fake,{advance:2000});assert.equal(result.code,0,result.ports.stderr.text);
    const report=result.output.baseline_report,observations=report.observations.filter(item=>item.test===c);
    assert.equal(observations.some(item=>item.state==='passed'),variant==='own substantive pass','3146_EMPTY_EXECUTION_MUST_NOT_INVENT_HISTORICAL_PASS');
    if(variant==='own empty failure')assert.ok(observations.some(item=>item.request_id===originalId && item.state==='failed'));
    if(variant==='own substantive pass')assert.ok(observations.some(item=>item.request_id===originalId && item.state==='passed'));
    assert.equal(report.availability,'partial');assert.ok(report.warnings.some(message=>/dispatch ownership/.test(message)));
    assert.deepEqual(checks(fake).slice(offset).map(item=>item.request.scenario).sort(),setup.selected.slice().sort());assert.deepEqual(saveBytes(setup,saved.batch),bytes);
  });
});
