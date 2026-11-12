import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {appendFileSync,mkdirSync,readFileSync,readdirSync,renameSync,symlinkSync,unlinkSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {randomUUID} from 'node:crypto';
import {captureSource} from '../src/runtime-preflight.mjs';
import {readRunResults} from '../src/workflow-results.mjs';
import {fullCheckPass} from '../src/workflow-story-card.mjs';
import {affectedFixture,affectedRuntime,batch,check,checks,commit,disclaimer,historicalAssociation,put,vectors} from './helpers/affected-check-fixture.mjs';
const cases=vectors('affected-baseline-report').cases;
const vector=id=>{const data=cases.find(item=>item.id===id);assert.ok(data);return data;};
const c='test/runtime/C.json';
const file=(setup,id,name='batch.json')=>join(setup.state,'batches',id,name);
const read=(setup,id,name)=>JSON.parse(readFileSync(file(setup,id,name),'utf8'));
const write=(setup,id,value,name)=>writeFileSync(file(setup,id,name),JSON.stringify(value));
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
  write(setup,saved.batch,receipt,`${receipt.id}.json`);originalRow.request_ids=[receipt.id];saved.created_at=data.given.saved_C.created_at;write(setup,saved.batch,saved);
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
  write(setup,saved.batch,newReceipt,`${passed}.json`);saved.rows[0].request_ids.push(passed);saved.rows[0].state='passed';write(setup,saved.batch,saved);
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
    write(setup,saved.batch,receipt,`${id}.json`);row.request_ids.push(id);
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
