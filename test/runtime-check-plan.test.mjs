import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {appendFileSync,readFileSync,writeFileSync,mkdirSync,unlinkSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {runCheck} from '../src/runtime-client.mjs';
import {readRunResults} from '../src/workflow-results.mjs';
import {findTests,interfaceBlocks,proseSha256} from '../src/runtime-preflight.mjs';
import {buildCheckPlan,checkPlanResults} from '../src/runtime-check-plan.mjs';
import {harbor,fakeRuntime,portsFor,PLACE} from './runtime-fake.mjs';

const git=(root,...args)=>{const r=spawnSync('git',args,{cwd:root,encoding:'utf8'});assert.equal(r.status,0,r.stderr);return r.stdout.trim();};
const commit=root=>{git(root,'add','.');git(root,'-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','fixture');};
const editInterface=(root,path,edit)=>{
  const text=readFileSync(join(root,path),'utf8'),block=interfaceBlocks(text)[0],doc=JSON.parse(block[1]);
  edit(doc);doc.status='draft';doc.prose_sha256=proseSha256(text);
  writeFileSync(join(root,path),text.replace(block[1],JSON.stringify(doc)));
};
const environment=(setup,fake)=>({HOME:setup.home,XDG_CONFIG_HOME:join(setup.home,'config'),PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});

test('3114: full dispatch saves target and baseline scope before checks; baseline failures survive read and run guidance',async t=>{
  const setup=harbor(t);
  appendFileSync(join(setup.repo,'user_stories/place-order.md'),'\n');
  let plannedBeforeDispatch=false;
  const fake=await fakeRuntime(t,(entry,f)=>{
    if(entry.command==='check') {
      plannedBeforeDispatch=ports.stderr.text.includes('user_stories/place-order.md') && ports.stderr.text.includes('baseline:');
      const failed=entry.request.scenario==='tests/unknown-item.json';
      return {status:200,json:f.check(entry.request.requestId,failed?'failed':'passed',[
        {criterion_id:'AC1',target:'result',path:'/value',op:'equals',expected:2,actual:failed?1:2,passed:!failed}])};
    }
    return f.normal(entry);
  });
  const {ports}=portsFor(environment(setup,fake));
  const code=await runCheck({cwd:setup.repo,options:{'--json':true,'--max-calls':8}},ports);
  const output=JSON.parse(ports.stdout.text);
  assert.equal(code,1);assert.equal(plannedBeforeDispatch,true);
  assert.ok(output.check_plan,'3114_CHECK_PLAN_MISSING');
  assert.equal(output.check_plan.stories.find(row=>row.story_path.endsWith('/place-order.md')).role,'target');
  assert.equal(output.check_plan.stories.find(row=>row.story_path.endsWith('/unknown-item.md')).role,'baseline');
  assert.deepEqual(output.check_scope.target.passed,['tests/place-order.json']);
  assert.deepEqual(output.check_scope.baseline.failures,['tests/unknown-item.json']);
  assert.equal(output.check_scope.target.state,'passed');assert.equal(output.check_scope.baseline.state,'failed');
  assert.deepEqual(output.check_plan.calls,{estimated:2,maximum:32,check_requests:4,lint_model_calls:0});
  const batch=JSON.parse(readFileSync(join(setup.state,'batches',output.batch,'batch.json'),'utf8'));
  assert.deepEqual(batch.check_plan,output.check_plan);
  const results=readRunResults({root:setup.repo},{env:ports.env});
  assert.deepEqual(results[0].checkScope,output.check_scope);
  assert.ok(results[0].summary.includes('tests/unknown-item.json'));
  const read=portsFor(ports.env).ports;
  assert.equal(await runCheck({cwd:setup.repo,words:[output.batch],options:{'--read':true,'--json':true}},read),1);
  const saved=JSON.parse(read.stdout.text);
  assert.deepEqual(saved.check_plan,output.check_plan);assert.deepEqual(saved.check_scope,output.check_scope);
  assert.equal(fake.posts.filter(row=>row.command==='check').length,2);
});

test('3114: shared transitive dependency selects every consuming Story',async t=>{
  const setup=harbor(t),path=join(setup.repo,PLACE);
  mkdirSync(join(setup.repo,'docs'));
  writeFileSync(join(setup.repo,'docs/shared.md'),'# Shared\n\n## Dependencies\n\n[Rates](rates.md)\n');
  writeFileSync(join(setup.repo,'docs/rates.md'),'# Rates\n');
  writeFileSync(path,readFileSync(path,'utf8').replace('None.','[Shared](../docs/shared.md)'));
  editInterface(setup.repo,PLACE,()=>{});commit(setup.repo);
  appendFileSync(join(setup.repo,'docs/rates.md'),'Changed rate\n');
  const fake=await fakeRuntime(t,(e,f)=>f.normal(e)),{ports}=portsFor(environment(setup,fake));
  assert.equal(await runCheck({cwd:setup.repo,options:{'--json':true}},ports),0);
  const result=JSON.parse(ports.stdout.text);
  assert.ok(result.check_plan,'3114_TRANSITIVE_PLAN_MISSING');
  assert.equal(result.check_plan.stories.length,2);
  for(const story of result.check_plan.stories) {
    assert.equal(story.role,'target');assert.deepEqual(story.affected_paths,['docs/rates.md']);
    assert.ok(story.dependency_closure.includes('docs/shared.md'));
  }
});

// Adapted from the integration review's public runCheck reproducer.
for(const owner of ['generated-header','unprovable'])test(`3114: deleted implementation with ${owner} keeps a failed Story in target work`,async t=>{
  const setup=harbor(t),independent='prompts/independent.prompt.md',deleted='src/order.mjs';
  writeFileSync(join(setup.repo,independent),readFileSync(join(setup.repo,PLACE),'utf8'));
  const path=join(setup.repo,'tests/unknown-item.json'),doc=JSON.parse(readFileSync(path,'utf8'));
  doc.steps[0].entry_path=independent;writeFileSync(path,JSON.stringify(doc));
  mkdirSync(join(setup.repo,'src'));
  writeFileSync(join(setup.repo,deleted),`${owner==='generated-header'?`// Generated from ${PLACE}.\n`:''}export const value=1;\n`);
  commit(setup.repo);
  unlinkSync(join(setup.repo,deleted));
  appendFileSync(join(setup.repo,'user_stories/unknown-item.md'),'\n');
  const fake=await fakeRuntime(t,(entry,f)=>{
    if(entry.command==='lint')return {status:200,json:f.lint(entry.request.requestId,[PLACE,independent].map(path=>({path,state:'approved',admission_state:'approved',interface:{calls:[]}})))};
    if(entry.command==='check'){
      const failed=entry.request.scenario==='tests/place-order.json';
      return {status:200,json:f.check(entry.request.requestId,failed?'failed':'passed',[
        {criterion_id:'AC1',target:'result',path:'/value',op:'equals',expected:2,actual:failed?1:2,passed:!failed}])};
    }
    return f.normal(entry);
  });
  const {ports}=portsFor(environment(setup,fake));
  assert.equal(await runCheck({cwd:setup.repo,options:{'--json':true}},ports),1,'the full batch must still fail');
  const result=JSON.parse(ports.stdout.text);
  assert.equal(result.check_scope.target.state,'failed','deleted implementation failure belongs to target repair');
  assert.deepEqual(result.check_scope.target.failures,['tests/place-order.json']);
  assert.deepEqual(result.check_scope.baseline.failures,[]);
  const story=result.check_plan.stories.find(row=>row.story_path==='user_stories/place-order.md');
  assert.equal(story.role,'target');
  if(owner==='generated-header')assert.deepEqual(story.affected_paths,[deleted]);
  else assert.match(story.reason,/conservative/);
  assert.equal(result.check_plan.stories.find(row=>row.story_path==='user_stories/unknown-item.md').role,'target');
  const saved=JSON.parse(readFileSync(join(setup.state,'batches',result.batch,'batch.json'),'utf8'));
  assert.deepEqual(saved.check_plan,result.check_plan);
  const read=portsFor(ports.env).ports;
  assert.equal(await runCheck({cwd:setup.repo,words:[result.batch],options:{'--read':true,'--json':true}},read),1);
  assert.deepEqual(JSON.parse(read.stdout.text).check_scope,result.check_scope);
  assert.equal(fake.posts.filter(row=>row.command==='check').length,2);

  // An excluded deletion must neither read historical bytes nor widen scope.
  writeFileSync(join(setup.repo,'pdd-workspace.json'),JSON.stringify({allowed_paths:['prompts/','tests/','user_stories/']}));
  const found=findTests({root:setup.repo}),reads=[];
  const plan=buildCheckPlan({root:setup.repo,found,selected:found.tests,rows:[],full:true},{
    git:(root,args)=>{reads.push(args);return git(root,...args);},
    capture:()=>({stories:found.stories.map(story=>({story_path:story.path,files:[{path:story.path},{path:story.path.endsWith('/place-order.md')?PLACE:independent}]}))})
  });
  assert.equal(reads.some(args=>args[0]==='show'),false);
  assert.equal(plan.stories.find(row=>row.story_path==='user_stories/place-order.md').role,'baseline');
});

for(const mode of ['missing-interface','missing-bound','missing-call-bound','recursive-call'])test(`3114: ${mode} names one prerequisite and blocks the whole paid batch`,async t=>{
  const setup=harbor(t);
  // Only one Story reaches this broken prompt. The other Story remains checkable.
  writeFileSync(join(setup.repo,'prompts/broken.prompt.md'),readFileSync(join(setup.repo,PLACE),'utf8'));
  const path=join(setup.repo,'tests/place-order.json'),doc=JSON.parse(readFileSync(path,'utf8'));
  doc.steps[0].entry_path='prompts/broken.prompt.md';writeFileSync(path,JSON.stringify(doc));
  if(mode==='missing-interface')writeFileSync(join(setup.repo,'prompts/broken.prompt.md'),'# Broken\n');
  else editInterface(setup.repo,'prompts/broken.prompt.md',iface=>{
    if(mode==='missing-bound')delete iface.limits.max_model_calls;
    else if(mode==='missing-call-bound')iface.calls=[{operation:'nested',target:PLACE,target_operation:'place_order'}];
    else iface.calls=[{operation:'self',target:'prompts/broken.prompt.md',target_operation:'place_order',max_calls:1}];
  });
  const fake=await fakeRuntime(t,(entry,f)=>f.normal(entry));
  const {ports,clock}=portsFor(environment(setup,fake));
  assert.equal(await runCheck({cwd:setup.repo,options:{'--json':true}},ports),4);
  assert.equal(fake.posts.filter(row=>row.command==='check').length,0,'3114_PAID_BATCH_NOT_BLOCKED');
  const result=JSON.parse(ports.stdout.text);
  assert.ok(result.check_plan,'3114_PREREQUISITE_PLAN_MISSING');
  assert.equal(result.check_plan.prerequisites.length,1);
  assert.equal(result.check_plan.prerequisites[0].path,'prompts/broken.prompt.md');
  assert.equal(result.check_plan.calls.maximum,null);assert.equal(clock.gh.length,0);
  assert.equal(result.rows.length,2);assert.ok(result.rows.every(row=>row.calls===0));
  assert.equal(result.exit_code,4);
});

test('3114: target admission and baseline outcomes stay separate for every bounded state pair',()=>{
  const plan={schema_version:'pdd.check-plan.v1',stories:[
    {role:'target',tests:['tests/target.json']},{role:'baseline',tests:['tests/baseline.json']} ]};
  const cases={passed:'passed',failed:'failed',refused:'not_run',not_run:'not_run',unknown:'not_run',running:'not_run'};
  for(const [target,expectedTarget] of Object.entries(cases))for(const [baseline,expectedBaseline] of Object.entries(cases)) {
    const result=checkPlanResults(plan,[{test:'tests/target.json',state:target},{test:'tests/baseline.json',state:baseline}]);
    assert.equal(result.target.state,expectedTarget,`${target}/${baseline}`);
    assert.equal(result.baseline.state,expectedBaseline,`${target}/${baseline}`);
    assert.deepEqual(result.target.failures,target==='failed'?['tests/target.json']:[]);
    assert.deepEqual(result.baseline.failures,baseline==='failed'?['tests/baseline.json']:[]);
  }
  assert.equal(checkPlanResults({schema_version:'pdd.check-plan.v1',stories:[{role:'target'}]},[]),null);
});

test('3114: committed run changes and generated source ownership select targets; unavailable Git stays conservative',t=>{
  const setup=harbor(t),base=git(setup.repo,'rev-parse','HEAD');
  mkdirSync(join(setup.repo,'src'));writeFileSync(join(setup.repo,'src/order.mjs'),`// Generated from ${PLACE}.\n`);commit(setup.repo);
  const found=findTests({root:setup.repo}),input={root:setup.repo,found,selected:found.tests,rows:[],full:true,base};
  const plan=buildCheckPlan(input);
  for(const story of plan.stories)assert.ok(story.affected_paths.includes('src/order.mjs'));
  const unknown=buildCheckPlan(input,{git:()=>{throw Error('unavailable');}});
  assert.equal(unknown.changed_paths,null);assert.ok(unknown.stories.every(row=>row.role==='target'));
  const incomplete=checkPlanResults(plan,[]);
  assert.equal(incomplete.target.state,'not_run');assert.equal(incomplete.target.unresolved.length,2);
});

test('3114: mixed fresh and reused full-batch rows retain scope on a saved read',async t=>{
  const setup=harbor(t),fake=await fakeRuntime(t,(entry,f)=>f.normal(entry));
  const execute=async(words=[],options={'--json':true})=>{
    const {ports}=portsFor(environment(setup,fake));
    const code=await runCheck({cwd:setup.repo,words,options,cache:true},ports);
    assert.equal(code,0,ports.stderr.text);
    return JSON.parse(ports.stdout.text);
  };
  await execute();
  appendFileSync(join(setup.repo,'user_stories/place-order.md'),'\n');
  const result=await execute();
  assert.equal(result.rows.filter(row=>row.cached).length,1);
  const saved=await execute([result.batch],{'--read':true,'--json':true});
  assert.deepEqual(saved.check_scope,result.check_scope);
  assert.equal(saved.rows.filter(row=>row.cached).length,1);
  assert.equal(fake.posts.filter(row=>row.command==='check').length,3);
});
