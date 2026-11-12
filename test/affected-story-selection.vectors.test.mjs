import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {appendFileSync,existsSync,readFileSync,symlinkSync,unlinkSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {runCheck} from '../src/runtime-client.mjs';
import {captureSource,findTests} from '../src/runtime-preflight.mjs';
import {portsFor} from './runtime-fake.mjs';
import {affectedFixture,affectedRuntime,batch,check,checks,cli,commit,disclaimer,git,hasState,historicalAssociation,installGh,put,vectors} from './helpers/affected-check-fixture.mjs';
const cases=vectors('affected-story-selection').cases;
const vector=id=>{const found=cases.find(item=>item.id===id);assert.ok(found);return found;};
const sorted=values=>[...values].sort();

test('3146 shared-change-all-variants: real CLI selects every affected variant before POST and retains criteria',async t=>{
  const data=vector('shared-change-all-variants'),setup=affectedFixture(t);setup.change(data.given.changed[0]);
  const fake=await affectedRuntime(t,setup);
  const result=await cli(setup,data.given.command.concat('--json'),{env:{PATH:installGh(setup),PDD_RUNTIME_URL:fake.origin}});
  assert.equal(result.code,0,`3146_AFFECTED_CLI_NOT_ACCEPTED: ${result.stderr}`);
  const output=JSON.parse(result.stdout),saved=batch(setup,output.batch);
  assert.deepEqual(sorted(checks(fake).map(entry=>entry.request.scenario)),sorted(data.expected.check_tests));
  assert.deepEqual(sorted(saved.source_selection.tests),sorted(data.expected.source_selection_tests));
  assert.deepEqual(saved.check_selection,{mode:'affected',tests:data.expected.check_tests,baseline_tests:data.expected.omitted_tests});
  assert.equal(saved.rows.some(row=>data.expected.omitted_tests.includes(row.test)),false);
  for(const row of saved.rows) {
    const authored=JSON.parse(readFileSync(join(setup.repo,row.test),'utf8'));
    assert.deepEqual(row.criterion_texts,Object.fromEntries(authored.criteria.map(item=>[item.id,item.text])));
    assert.equal(row.criteria_total,authored.criteria.length);
    assert.deepEqual(row.steps.flatMap(step=>step.checks.map(item=>item.criterion_id)),authored.steps.flatMap(step=>step.checks.map(item=>item.criterion_id)));
  }
  assert.match(output.check_scope.guidance,/Omitted baseline work/);
  assert.ok(output.warnings.includes(disclaimer));
});

test('3146 direct-story-test-and-transitive: native runCheck dispatch membership',async t=>{
  const data=vector('direct-story-test-and-transitive');
  for(const [index,paths] of data.given.change_sets.entries())await t.test(paths.join(','),async t=>{
    const setup=affectedFixture(t,{transitive:true});for(const path of paths)setup.change(path);
    const fake=await affectedRuntime(t,setup),result=await check(setup,fake);
    assert.equal(result.code,0,result.ports.stderr.text);
    assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(data.expected.selected_by_set[index]));
    for(const row of result.output.rows)assert.equal(row.criteria.total,3);
  });
});

test('3146 global-config-conservative and git-scope-and-no-target retain complete dispatch',async t=>{
  const global=vector('global-config-conservative'),scope=vector('git-scope-and-no-target');
  for(const path of [...global.given.changed_each,null,'README.md'])await t.test(path??'no changes',async t=>{
    const setup=affectedFixture(t);if(path)put(setup.repo,path,path==='pdd-source.json'?{include:[]}:path==='pdd-workspace.json'?{allowed_paths:['prompts/','test/','user_stories/','docs/']}:path==='pdd-bindings.json'?{schema_version:'pdd.bindings.v1',modules:[]}:'Unowned note.');
    const fake=await affectedRuntime(t,setup),result=await check(setup,fake);
    assert.equal(result.code,0,result.ports.stderr.text);
    assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(global.expected.check_tests));
    assert.equal(scope.expected.never_underselect,true);assert.equal(result.output.baseline_report.availability,'available');assert.deepEqual(result.output.baseline_report.warnings,[]);
  });
});

test('3146 safe-link-target-consumers dispatch A/B and preserve source authority',async t=>{
  const data=vector('safe-link-target-consumers'),setup=affectedFixture(t);
  put(setup.repo,'docs/shared-target.md','Original target.');
  for(const name of ['A','B']) {
    symlinkSync('shared-target.md',join(setup.repo,`docs/${name}-link.md`));
    const path=join(setup.repo,`prompts/${name}.prompt.md`);
    writeFileSync(path,readFileSync(path,'utf8').replace('../docs/shared.md',`../docs/${name}-link.md`));
  }
  // Fill draft hashes through the public local command after the fixture dependency edit.
  assert.equal((await cli(setup,['test','--fill-hash'])).code,0);commit(setup.repo);setup.change(data.given.changed[0]);
  const fake=await affectedRuntime(t,setup),result=await check(setup,fake);
  assert.equal(result.code,0,result.ports.stderr.text);assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(data.expected.check_tests));
});

test('3146 old-new-and-unknown-owners and deleted-unknown-even-with-target conserve membership',async t=>{
  const data=vector('old-new-and-unknown-owners');vector('deleted-unknown-even-with-target');
  for(const variant of data.given.ownership_variants)await t.test(variant,async t=>{
    const setup=affectedFixture(t);put(setup.repo,'src/owned.mjs',variant==='missing old metadata'?'export const value=1;\n':'// Generated from prompts/A.prompt.md.\nexport const value=1;\n');commit(setup.repo);
    if(variant==='old A/new B')put(setup.repo,'src/owned.mjs','// Generated from prompts/B.prompt.md.\nexport const value=2;\n');
    if(variant==='removed owner header')put(setup.repo,'src/owned.mjs','export const value=2;\n');
    if(variant==='missing old metadata')unlinkSync(join(setup.repo,'src/owned.mjs'));
    if(variant==='multiple A/B headers')put(setup.repo,'src/owned.mjs','// Generated from prompts/A.prompt.md.\n// Generated from prompts/B.prompt.md.\nexport const value=2;\n');
    if(variant==='unknown added implementation')put(setup.repo,'src/unowned.mjs','export const value=1;\n');
    setup.change('prompts/A.prompt.md');
    const fake=await affectedRuntime(t,setup),result=await check(setup,fake);
    assert.equal(result.code,0,result.ports.stderr.text);
    const expected=variant==='old A/new B'?data.expected.old_A_new_B_checks:variant==='multiple A/B headers'?data.expected.multiple_owner_checks:data.expected.unknown_owner_checks;
    assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(expected));
  });
  const setup=affectedFixture(t);put(setup.repo,'src/deleted-unknown.mjs','export const value=1;');commit(setup.repo);unlinkSync(join(setup.repo,'src/deleted-unknown.mjs'));setup.change('prompts/A.prompt.md');
  const fake=await affectedRuntime(t,setup),result=await check(setup,fake);assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(setup.tests));
});

test('3146 staged-unstaged-untracked-saved-base: staged and unstaged changes reach public dispatcher',async t=>{
  const data=vector('staged-unstaged-untracked-saved-base');
  for(const staged of [false,true])await t.test(String(staged),async t=>{
    const setup=affectedFixture(t);setup.change('prompts/A.prompt.md');if(staged)git(setup.repo,'add','prompts/A.prompt.md');
    const fake=await affectedRuntime(t,setup),result=await check(setup,fake);
    assert.equal(result.code,0);assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(data.expected.check_tests));
  });
});

test('3146 full-and-named-unchanged retains ordinary selection',async t=>{
  const data=vector('full-and-named-unchanged');
  for(const command of data.given.commands)await t.test(command.join(' '),async t=>{
    const setup=affectedFixture(t);setup.change('docs/shared.md');const fake=await affectedRuntime(t,setup);
    const words=command.slice(1).filter(word=>!word.startsWith('--')),options=Object.fromEntries(command.filter(word=>word.startsWith('--')).map(word=>[word,true]));
    const result=await check(setup,fake,{words,options:{...options,'--json':true},cache:true});assert.equal(result.code,0,result.ports.stderr.text);
    assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(words.length?data.expected.named_check_tests:data.expected.full_check_tests));
    assert.equal(result.output.check_selection,undefined);
  });
});

test('3146 clear-and-target-prerequisites separates omitted problems and preserves full prerequisite stop',async t=>{
  const data=vector('clear-and-target-prerequisites');
  for(const missing of ['A','C','fallback'])await t.test(missing,async t=>{
    const setup=affectedFixture(t),path=join(setup.repo,`prompts/${missing==='fallback'?'C':missing}.prompt.md`);
    writeFileSync(path,readFileSync(path,'utf8').split('<details>')[0]);commit(setup.repo);if(missing!=='fallback')setup.change('prompts/A.prompt.md');
    const fake=await affectedRuntime(t,setup),result=await check(setup,fake,{options:{'--affected':true,'--cache-clear':true,'--json':true}});
    if(missing==='C'){assert.equal(result.code,0,result.ports.stderr.text);assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(data.expected.cache_clear_scope));}
    else {assert.notEqual(result.code,0);assert.equal(checks(fake).length,0);if(missing==='fallback'){assert.equal(result.output.baseline_report.availability,'available');assert.deepEqual(result.output.baseline_report.warnings,[]);}}
  });
});

test('3146 invalid-option-combinations rejects before state/auth/network',async t=>{
  const data=vector('invalid-option-combinations');
  for(const command of data.given.commands)await t.test(command.join(' '),async t=>{
    const setup=affectedFixture(t),actual=await cli(setup,command);assert.equal(actual.code,data.expected.exit_code);assert.equal(hasState(setup),false);
    const options={'--affected':true},words=[];
    for(let index=2;index<command.length;index++){const word=command[index];if(word.startsWith('--'))options[word]=['--retry','--screen'].includes(word)?command[++index]:true;else words.push(word);}
    const {ports,clock}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state},{fetch:()=>{throw Error('NETWORK_EFFECT');}});
    assert.equal(await runCheck({cwd:setup.repo,words,options},ports),2);assert.equal(clock.gh.length,0);assert.equal(hasState(setup),false);
  });
});

test('3146 public-help-completion-and-docs publishes exact form and accepts flag',async t=>{
  const data=vector('public-help-completion-and-docs'),setup=affectedFixture(t);
  const help=await cli(setup,['test','--help']);assert.equal(help.code,0);assert.ok(help.stdout.includes(data.given.new_form));
  const completion=await cli(setup,['completion','bash']);assert.equal(completion.code,0);assert.match(completion.stdout,/--affected/);
  assert.ok(readFileSync(new URL('../docs/cli.md',import.meta.url),'utf8').includes(data.given.new_form));
});

test('3146 cache-and-call-plan-stay-selected bounds second-phase replacements and excludes C',async t=>{
  const data=vector('cache-and-call-plan-stay-selected'),setup=affectedFixture(t);setup.change('docs/shared.md');let changed=false;
  const fake=await affectedRuntime(t,setup,{answer(entry,f){
    if(changed && entry.command==='check') {
      const doc=JSON.parse(readFileSync(join(setup.repo,entry.request.scenario),'utf8'));
      const answer=f.check(entry.request.requestId,'passed',doc.steps.flatMap(step=>step.checks).map(item=>({...item,expected:item.value,actual:item.value,passed:true})));
      answer.engine_sha='1234567890abcdef1234567890abcdef12345678';return {status:200,json:answer};
    }
  }});
  const primed=await check(setup,fake,{words:['A'],options:{'--json':true,'--max-calls':30},cache:true});assert.equal(primed.code,0,primed.ports.stderr.text);
  const offset=checks(fake).length;changed=true;
  const result=await check(setup,fake,{options:{'--affected':true,'--json':true,'--max-calls':30},cache:true,advance:1000});assert.equal(result.code,0,result.ports.stderr.text);
  const dispatched=checks(fake).slice(offset);assert.deepEqual(sorted(dispatched.map(row=>row.request.scenario)),sorted(data.expected.all_dispatch_tests_with_replacements));
  assert.equal(dispatched.some(row=>row.request.scenario==='test/runtime/C.json'),false);
  assert.equal(result.output.check_plan.calls.maximum,data.expected.plan_calls.maximum);assert.equal(result.output.check_plan.calls.check_requests,data.expected.plan_calls.check_requests);
  assert.ok(dispatched.every(row=>row.request.max_calls===data.expected.per_request_max_calls));assert.ok(dispatched.length<=data.expected.total_check_posts_maximum);
  assert.equal(dispatched[0].request.scenario,'test/runtime/B.json');assert.deepEqual(sorted(dispatched.slice(1).map(row=>row.request.scenario)),['test/runtime/A.json','test/runtime/A.recorded.json']);
  assert.equal(result.output.rows.length,data.expected.selected_test_count);
});

test('3146 source drift restarts conservative planning before dispatch and includes the new owner',async t=>{
  const setup=affectedFixture(t);setup.change('docs/shared.md');let changed=false;
  const fake=await affectedRuntime(t,setup),result=await check(setup,fake,{extra:{captureSource(root,selection){
    if(selection.tests?.length===3 && !changed){changed=true;setup.change('prompts/C.prompt.md');}
    return captureSource(root,selection);
  }}});
  assert.equal(result.code,0,result.ports.stderr.text);assert.equal(changed,true);
  assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(setup.tests));
  assert.deepEqual(result.output.check_selection.baseline_tests,[]);assert.match(result.ports.stderr.text,/checking every Story conservatively before any paid Check/);
});

test('3146 newly discovered variants during capture are selected before any paid dispatch',async t=>{
  for(const phase of ['first planning capture','selected capture','last planning capture','post-cache planning capture'])await t.test(phase,async t=>{
    const setup=affectedFixture(t);setup.change('docs/shared.md');
    const added='test/runtime/A.new.json';let changed=false,sawSelectedCapture=false,captures=0,plansAfterSelected=0;
    const fake=await affectedRuntime(t,setup),result=await check(setup,fake,{cache:true,extra:{captureSource(root,selection){
      captures++;
      const captured=captureSource(root,selection),selectedCapture=selection.tests?.length===3;
      if(sawSelectedCapture && !selectedCapture)plansAfterSelected++;
      const changeNow=phase==='first planning capture'?captures===1:phase==='selected capture'?selectedCapture:
        phase==='post-cache planning capture'?plansAfterSelected===2:sawSelectedCapture;
      if(changeNow && !changed){
        assert.equal(checks(fake).length,0,'discovery must stabilize before any Check');
        changed=true;put(setup.repo,added,JSON.parse(readFileSync(join(setup.repo,'test/runtime/A.json'),'utf8')));
      }
      if(selectedCapture)sawSelectedCapture=true;
      return captured;
    }}});
    assert.equal(changed,true,phase);assert.equal(result.code,0,result.ports.stderr.text);
    const expected=sorted([...setup.tests,added]);
    assert.ok(checks(fake).some(row=>row.request.scenario===added),'Check dispatch must include the newly discovered A variant');
    assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),expected);
    assert.deepEqual(sorted(result.output.check_selection.tests),expected);
    assert.deepEqual(result.output.check_selection.baseline_tests,[]);
    assert.deepEqual(sorted(result.output.rows.map(row=>row.test)),expected);
    const saved=batch(setup,result.output.batch);
    assert.deepEqual(sorted(saved.source_selection.tests),expected);
    assert.equal(saved.source_selection.exclude_fixture_projects,true);
    assert.deepEqual(sorted(saved.check_plan.stories.find(row=>row.story_path==='user_stories/A.md').tests),sorted(['test/runtime/A.json','test/runtime/A.recorded.json',added]));
    const cache=JSON.parse(readFileSync(join(setup.repo,'.pdd/cache/test/stories.json'),'utf8'));
    assert.deepEqual(cache.latest_identity.in_progress,[]);
  });
});

test('3146 repeatedly changing discovery stops locally instead of looping or dispatching stale membership',async t=>{
  const setup=affectedFixture(t);setup.change('docs/shared.md');let captures=0;
  const fake=await affectedRuntime(t,setup),result=await check(setup,fake,{cache:true,extra:{captureSource(root,selection){
    const captured=captureSource(root,selection);
    captures++;
    assert.ok(captures<10,'planning must terminate under repeated discovery drift');
    put(setup.repo,`test/runtime/A.new${captures}.json`,JSON.parse(readFileSync(join(setup.repo,'test/runtime/A.json'),'utf8')));
    return captured;
  }}});
  assert.equal(result.code,4,result.ports.stderr.text);
  assert.match(result.ports.stderr.text,/Source selection kept changing during planning/);
  assert.equal(fake.posts.length,0);assert.equal(result.clock.gh.length,0);
  assert.equal(existsSync(join(setup.repo,'.pdd/cache/test/stories.json')),false);
});


test('3146 staged-unstaged-untracked-saved-base: real untracked closure and committed saved-base changes remain selected',async t=>{
  const data=vector('staged-unstaged-untracked-saved-base');
  for(const variant of ['untracked dependency A','committed A against saved run base'])await t.test(variant,async t=>{
    const setup=affectedFixture(t);
    if(variant.startsWith('untracked')){
      const path=join(setup.repo,'prompts/A.prompt.md');writeFileSync(path,readFileSync(path,'utf8').replace('../docs/shared.md','../docs/untracked-A.md'));
      setup.change('prompts/A.prompt.md');commit(setup.repo);put(setup.repo,'docs/untracked-A.md','Untracked A-only required dependency.');
    }else{
      await historicalAssociation(setup,'pr1');setup.change('prompts/A.prompt.md');commit(setup.repo);
    }
    const fake=await affectedRuntime(t,setup),result=await check(setup,fake);assert.equal(result.code,0,result.ports.stderr.text);
    assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(data.expected.check_tests));
  });
});

test('3146 git-scope-and-no-target: unavailable Git and rename coverage remain conservative at dispatch',async t=>{
  const data=vector('git-scope-and-no-target');
  for(const variant of ['Git unavailable','rename deletion/addition','committed no-run changes with HEAD comparison'])await t.test(variant,async t=>{
    const setup=affectedFixture(t);let extra={};
    if(variant==='Git unavailable'){setup.change('prompts/A.prompt.md');extra={checkPlanPorts:{git(){throw Error('Controlled Git scope unavailable');}}};}
    if(variant==='rename deletion/addition'){put(setup.repo,'src/unknown.mjs','export const x=1;');commit(setup.repo);git(setup.repo,'mv','src/unknown.mjs','src/renamed.mjs');}
    if(variant.startsWith('committed')){setup.change('prompts/A.prompt.md');commit(setup.repo);}
    const fake=await affectedRuntime(t,setup),result=await check(setup,fake,{extra});assert.equal(result.code,0,result.ports.stderr.text);
    assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(data.expected.no_established_target_checks));
  });
});

test('3146 late classification bytes cannot omit a newly affected implementation owner',async t=>{
  for(const variant of ['new changed path','untracked owner','same changed paths, new owner','same changed paths, unknown owner','dependency edge','safe-link spelling','global inventory'])await t.test(variant,async t=>{
    const setup=affectedFixture(t);
    put(setup.repo,'src/owned.mjs','// Generated from prompts/A.prompt.md.\nexport const value=1;\n');
    put(setup.repo,'src/C.mjs','// Generated from prompts/C.prompt.md.\nexport const value=1;\n');
    commit(setup.repo);setup.change('docs/shared.md');
    if(variant==='untracked owner')put(setup.repo,'src/untracked.mjs','// Generated from prompts/A.prompt.md.\nexport const value=2;\n');
    if(variant.startsWith('same changed'))put(setup.repo,'src/owned.mjs','// Generated from prompts/A.prompt.md.\nexport const value=2;\n');
    let sawSelected=false,plansAfterSelected=0,changed=false;
    const fake=await affectedRuntime(t,setup),result=await check(setup,fake,{cache:true,extra:{captureSource(root,selection){
      const captured=captureSource(root,selection),selectedCapture=selection.tests?.length===3;
      if(sawSelected&&!selectedCapture)plansAfterSelected++;
      if(plansAfterSelected===2&&!changed){
        assert.equal(checks(fake).length,0,'late planning change must precede every paid Check');changed=true;
        if(variant==='untracked owner')put(root,'src/untracked.mjs','// Generated from prompts/C.prompt.md.\nexport const value=2;\n');
        if(variant==='new changed path')appendFileSync(join(root,'src/C.mjs'),'export const changed=2;\n');
        if(variant==='same changed paths, new owner')put(root,'src/owned.mjs','// Generated from prompts/C.prompt.md.\nexport const value=2;\n');
        if(variant==='same changed paths, unknown owner')put(root,'src/owned.mjs','export const value=2;\n');
        if(variant==='dependency edge')put(root,'docs/shared.md','Shared changed dependency.\n\n## Dependencies\n\n[C](../prompts/C.prompt.md)\n');
        if(variant==='safe-link spelling'){const bytes=readFileSync(join(root,'docs/shared.md'));put(root,'docs/new-target.md',bytes.toString());unlinkSync(join(root,'docs/shared.md'));symlinkSync('new-target.md',join(root,'docs/shared.md'));}
        if(variant==='global inventory')put(root,'pdd-bindings.json',{schema_version:'pdd.bindings.v1',modules:[]});
      }
      if(selectedCapture)sawSelected=true;return captured;
    }}});
    assert.equal(changed,true);assert.equal(result.code,0,result.ports.stderr.text);
    assert.ok(checks(fake).some(row=>row.request.scenario==='test/runtime/C.json'),'3146_LATE_OWNER_OMITTED: late implementation or dependency change omitted genuinely affected C');
    assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(setup.tests));
    assert.deepEqual(result.output.check_selection.baseline_tests,[]);
    const cache=JSON.parse(readFileSync(join(setup.repo,'.pdd/cache/test/stories.json'),'utf8'));
    assert.deepEqual(cache.latest_identity.in_progress,[]);
  });
});

test('3146 continuously changing ownership bytes stop before authentication or paid work',async t=>{
  const setup=affectedFixture(t);put(setup.repo,'src/owned.mjs','// Generated from prompts/A.prompt.md.\nexport const value=1;\n');commit(setup.repo);
  setup.change('docs/shared.md');setup.change('src/owned.mjs');let captures=0;
  const fake=await affectedRuntime(t,setup),result=await check(setup,fake,{cache:true,extra:{captureSource(root,selection){
    const captured=captureSource(root,selection);captures++;assert.ok(captures<10,'ownership drift must terminate');
    appendFileSync(join(root,'src/owned.mjs'),`export const drift${captures}=${captures};\n`);return captured;
  }}});
  assert.equal(result.code,4,result.ports.stderr.text);assert.equal(fake.posts.length,0);assert.equal(result.clock.gh.length,0);
  assert.match(result.ports.stderr.text,/Source selection kept changing during planning/);
});

test('3146 unavailable planning identity keeps complete conservative dispatch',async t=>{
  const setup=affectedFixture(t);setup.change('docs/shared.md');
  const fake=await affectedRuntime(t,setup),result=await check(setup,fake,{extra:{checkPlanPorts:{git(root,args){
    if(args[0]==='rev-parse')throw Error('Controlled unavailable comparison identity');return git(root,...args);
  }}}});
  assert.equal(result.code,0,result.ports.stderr.text);
  assert.deepEqual(sorted(checks(fake).map(row=>row.request.scenario)),sorted(setup.tests));
  assert.deepEqual(result.output.check_selection.baseline_tests,[]);
});
