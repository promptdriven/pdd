import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync,appendFileSync,unlinkSync,renameSync,symlinkSync} from 'node:fs';
import {join,dirname} from 'node:path';
import {spawnSync} from 'node:child_process';
import {findTests,interfaceBlocks,proseSha256,captureSource} from '../src/runtime-preflight.mjs';
import {buildCheckPlan,selectCheckTests} from '../src/runtime-check-plan.mjs';
import {temp,root as projectRoot} from './runtime-fake.mjs';
import {affectedFixture,affectedRuntime,checks,cli,commit as commitAffected,installGh,put as putAffected} from './helpers/affected-check-fixture.mjs';

const cases = JSON.parse(readFileSync(new URL('./affected-checks/affected-story-selection-cases.json',import.meta.url),'utf8'));
const approved = id => cases.cases.find(item=>item.id === id);
const git = (root,...args) => {
  const reply=spawnSync('git',args,{cwd:root,encoding:'utf8'});
  assert.equal(reply.status,0,reply.stderr);return reply.stdout;
};
const commit = root => {git(root,'add','-A');git(root,'-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','fixture');};
const put = (root,path,text) => {mkdirSync(dirname(join(root,path)),{recursive:true});writeFileSync(join(root,path),text);};
const editPrompt = (root,path,edit) => {
  const text=readFileSync(join(root,path),'utf8'),block=interfaceBlocks(text)[0],iface=JSON.parse(block[1]);
  edit(iface);iface.status='draft';iface.prose_sha256=proseSha256(text);
  put(root,path,text.replace(block[1],JSON.stringify(iface)));
};
function fixture(t,{links=false}={}) {
  const root=temp(t),read=path=>readFileSync(join(projectRoot,'test/fixtures/harbor',path),'utf8');
  for (const letter of ['A','B','C']) {
    const dependency=letter === 'C' ? 'None.' : `[Shared](../docs/${links ? `${letter}-link` : 'shared'}.md)`;
    put(root,`prompts/${letter}.prompt.md`,read('prompts/place_order.prompt.md').replace('None.',dependency));
    put(root,`user_stories/${letter}.md`,read('user_stories/place-order.md'));
    const doc=JSON.parse(read('tests/place-order.json'));doc.story_path=`user_stories/${letter}.md`;
    doc.steps[0].entry_path=`prompts/${letter}.prompt.md`;
    for (const path of approved('shared-change-all-variants').given.fixture.story_tests[letter]) put(root,path,JSON.stringify(doc));
  }
  put(root,'docs/shared.md','# Shared\n\n## Dependencies\n\n[Transitive](transitive-to-A-and-B.md)\n');
  put(root,'docs/transitive-to-A-and-B.md','# Transitive\n');
  if (links) {
    put(root,'docs/shared-target.md','# Safe target\n');
    for (const letter of ['A','B']) symlinkSync('shared-target.md',join(root,`docs/${letter}-link.md`));
  }
  git(root,'init','-q');commit(root);return root;
}
const plan = (root,options={},ports={}) => {
  const found=findTests({root,excludeFixtureProjects:true});
  return buildCheckPlan({root,found,selected:found.tests,full:true,affected:true,...options},ports);
};
const selected = value => selectCheckTests(value,{affected:true}).tests;
const all = approved('shared-change-all-variants').expected.check_tests.concat(approved('shared-change-all-variants').expected.omitted_tests);

test('3146 native AC1: real transitive capture retains A variants and B; baseline C is omitted',t=>{
  const root=fixture(t);appendFileSync(join(root,'docs/transitive-to-A-and-B.md'),'changed\n');
  const result=plan(root);
  assert.deepEqual(selected(result),approved('shared-change-all-variants').expected.check_tests);
  assert.deepEqual(selectCheckTests(result,{affected:true}).baseline_tests,approved('shared-change-all-variants').expected.omitted_tests);
  assert.deepEqual(result.stories[0].affected_paths,['docs/transitive-to-A-and-B.md']);
  assert.deepEqual(result.calls,{estimated:0,maximum:0,check_requests:0,lint_model_calls:0});
  assert.deepEqual(result.prerequisites,[],'rows-empty classification has no dispatch prerequisites');
});

for (const [index,changes] of approved('direct-story-test-and-transitive').given.change_sets.entries()) test(`3146 native AC1 direct and transitive set ${index+1}`,t=>{
  const root=fixture(t);for (const path of changes)appendFileSync(join(root,path),'\n');
  assert.deepEqual(selected(plan(root)),approved('direct-story-test-and-transitive').expected.selected_by_set[index]);
});

for (const path of approved('global-config-conservative').given.changed_each) test(`3146 native AC2 global source: ${path}`,t=>{
  const root=fixture(t),content=path === 'pdd-source.json' ? {include:[]} : path === 'pdd-workspace.json' ? {allowed_paths:['prompts/','user_stories/','test/','docs/']} : {schema_version:'pdd.bindings.v1',modules:[]};
  put(root,path,JSON.stringify(content));
  const result=plan(root);assert.deepEqual(selected(result),approved('global-config-conservative').expected.check_tests);
  assert.ok(result.stories.every(story=>/conservative/.test(story.reason)));
});

test('3146 native AC2: safe-link final target change selects every captured consumer',t=>{
  const root=fixture(t,{links:true});appendFileSync(join(root,'docs/shared-target.md'),'changed\n');
  const result=plan(root);assert.deepEqual(selected(result),approved('safe-link-target-consumers').expected.check_tests);
  for (const story of result.stories.filter(story=>story.role === 'target')) assert.deepEqual(story.affected_paths,['docs/shared-target.md']);
});

test('3146 native AC2: missing old safe-link relationship keeps all Stories',t=>{
  const root=fixture(t,{links:true});appendFileSync(join(root,'docs/shared-target.md'),'changed\n');
  const result=plan(root,{}, {git:(cwd,args)=>{
    if (args[0] === 'show' && args[1] === 'HEAD:docs/A-link.md') throw Error('old alias unavailable');
    return git(cwd,...args);
  }});
  assert.deepEqual(selected(result),approved('safe-link-target-consumers').expected.fallback_if_relationship_unavailable);
  assert.ok(result.stories.every(story=>/safe-link.*unavailable/.test(story.reason)));
});

for (const variant of ['old A/new B','multiple A/B headers','removed owner header','missing old metadata','unknown added implementation']) test(`3146 native AC2 ownership: ${variant}`,t=>{
  const root=fixture(t),path='src/owned.mjs';
  if (variant !== 'unknown added implementation') {put(root,path,'// Generated from prompts/A.prompt.md.\n');commit(root);}
  put(root,path,['old A/new B','missing old metadata'].includes(variant) ? '// Generated from prompts/B.prompt.md.\n' : variant === 'multiple A/B headers' ? '// Generated from prompts/A.prompt.md.\n// Generated from prompts/B.prompt.md.\n' : 'export const value=1;\n');
  appendFileSync(join(root,'prompts/A.prompt.md'),'\n');
  const result=plan(root,{},variant === 'missing old metadata' ? {git:(cwd,args)=>{
    if(args[0] === 'show' && args[1] === 'HEAD:src/owned.mjs')throw Error('old metadata unavailable');return git(cwd,...args);
  }} : {});
  const expected=approved('old-new-and-unknown-owners').expected;
  assert.deepEqual(selected(result),variant === 'old A/new B' ? expected.old_A_new_B_checks : variant === 'multiple A/B headers' ? expected.multiple_owner_checks : expected.unknown_owner_checks);
});

test('3146 native AC2: unknown deleted owner keeps all obligations even with a known target',t=>{
  const root=fixture(t);put(root,'src/deleted-unknown.mjs','export const value=1;\n');commit(root);
  unlinkSync(join(root,'src/deleted-unknown.mjs'));appendFileSync(join(root,'prompts/A.prompt.md'),'\n');
  const result=plan(root);assert.deepEqual(selected(result),approved('deleted-unknown-even-with-target').expected.check_tests);
  assert.ok(result.stories.every(story=>/deleted ownership/.test(story.reason)));
});

for (const variant of ['staged','unstaged','untracked dependency','saved base']) test(`3146 native AC2 change intake: ${variant}`,t=>{
  const root=fixture(t),base=git(root,'rev-parse','HEAD').trim();
  if (variant === 'untracked dependency') {
    put(root,'docs/A-only.md','# A\n');
    const path='prompts/A.prompt.md';put(root,path,readFileSync(join(root,path),'utf8').replace('[Shared](../docs/shared.md)','[Own](../docs/A-only.md)'));
  } else appendFileSync(join(root,'prompts/A.prompt.md'),'\n');
  if (variant === 'staged')git(root,'add','prompts/A.prompt.md');
  if (variant === 'saved base')commit(root);
  assert.deepEqual(selected(plan(root,{...(variant === 'saved base'?{base}:{})})),approved('staged-unstaged-untracked-saved-base').expected.check_tests);
  if (variant === 'saved base')assert.deepEqual(selected(plan(root)),approved('git-scope-and-no-target').expected.no_working_changes_checks);
});

test('3146 native AC2: unavailable base metadata and an unavailable unrelated closure cannot establish independence',t=>{
  const root=fixture(t);appendFileSync(join(root,'prompts/A.prompt.md'),'\n');
  const oldUnavailable=plan(root,{}, {git:(cwd,args)=>{if(args[0] === 'ls-tree')throw Error('base unavailable');return git(cwd,...args);}});
  assert.deepEqual(selected(oldUnavailable),all);assert.ok(oldUnavailable.stories.every(story=>/old ownership.*unavailable/.test(story.reason)));
  const closureUnavailable=plan(root,{}, {capture:(cwd,options)=>{
    const captured=captureSource(cwd,options);
    captured.stories=captured.stories.map(story=>story.story_path === 'user_stories/C.md' ? {...story,unavailable:[{cause:'injected unavailable closure'}]} : story);
    return captured;
  }});
  assert.deepEqual(selected(closureUnavailable),all);assert.ok(closureUnavailable.stories.every(story=>/closure unavailable/.test(story.reason)));
});

test('3146 native AC2: unknown Git, empty/no target, unreadable closure and rename retain conservative obligations',t=>{
  const root=fixture(t);
  assert.deepEqual(selected(plan(root)),all);
  assert.deepEqual(selected(plan(root,{}, {git:()=>{throw Error('Git unavailable');}})),all);
  put(root,'notes.md','# Unrelated\n');assert.deepEqual(selected(plan(root)),all);unlinkSync(join(root,'notes.md'));
  renameSync(join(root,'prompts/A.prompt.md'),join(root,'prompts/A-renamed.prompt.md'));
  assert.deepEqual(selected(plan(root)),all);
});

test('3146 native exclusions: excluded deleted implementation and fixture paths neither widen scope nor read base metadata',t=>{
  const root=fixture(t);put(root,'src/unknown.mjs','export const value=1;\n');
  put(root,'test/fixtures/nested/package.json','{}');put(root,'test/fixtures/nested/src/unknown.mjs','export const value=1;\n');
  put(root,'test/fixtures/nested/user_stories/README.md','# Fixture\n');put(root,'test/fixtures/nested/tests/fixture-data.json','{}');
  put(root,'pdd-workspace.json',JSON.stringify({allowed_paths:['prompts/','user_stories/','test/','docs/']}));commit(root);
  unlinkSync(join(root,'src/unknown.mjs'));appendFileSync(join(root,'test/fixtures/nested/src/unknown.mjs'),'// changed\n');
  appendFileSync(join(root,'prompts/A.prompt.md'),'\n');const reads=[];
  const result=plan(root,{}, {git:(cwd,args)=>{reads.push(args);return git(cwd,...args);}});
  assert.deepEqual(selected(result),approved('staged-unstaged-untracked-saved-base').expected.check_tests);
  assert.ok(reads.filter(args=>args[0] === 'show' || args[0] === 'ls-tree').every(args=>args.every(arg=>!arg.includes('src/unknown.mjs'))));
});

test('3146 native fixture exclusion keeps an explicitly captured dependency in affected scope',t=>{
  const root=fixture(t);
  put(root,'test/fixtures/nested/user_stories/README.md','# Fixture\n');put(root,'test/fixtures/nested/tests/fixture-data.json','{}');
  put(root,'test/fixtures/nested/rule.md','# Consumed rule\n');
  const path='prompts/A.prompt.md';put(root,path,readFileSync(join(root,path),'utf8').replace('[Shared](../docs/shared.md)','[Rule](../test/fixtures/nested/rule.md)'));
  commit(root);appendFileSync(join(root,'test/fixtures/nested/rule.md'),'changed\n');appendFileSync(join(root,'prompts/B.prompt.md'),'\n');
  assert.deepEqual(selected(plan(root)),approved('shared-change-all-variants').expected.check_tests);
});

test('3146 native dispatch bounds inspect selected rows only, and full fallback still stops on baseline prerequisites',t=>{
  const root=fixture(t);editPrompt(root,'prompts/C.prompt.md',iface=>{delete iface.limits.max_model_calls;});commit(root);
  appendFileSync(join(root,'prompts/A.prompt.md'),'\n');const found=findTests({root});
  const rows=found.tests.map(item=>({test:item.path,steps:item.doc.steps,state:'ready',max_calls:30}));
  const result=plan(root,{rows});
  assert.deepEqual(selected(result),approved('staged-unstaged-untracked-saved-base').expected.check_tests);
  assert.deepEqual(result.prerequisites,[]);assert.deepEqual(result.calls,{estimated:2,maximum:120,check_requests:4,lint_model_calls:0});
  const full=plan(root,{rows,affected:false});assert.ok(full.prerequisites.some(item=>item.path === 'prompts/C.prompt.md'));
  assert.equal(full.calls.maximum,null);assert.equal(full.calls.estimated,null);
  const fallback=plan(root,{rows},{git:()=>{throw Error('scope unavailable');}});
  assert.ok(fallback.prerequisites.some(item=>item.path === 'prompts/C.prompt.md'));assert.equal(fallback.calls.maximum,null);
});

// A canonical owner header is authoritative for every extension and location.
for (const extension of ['svg','md','json','txt','csv']) for (const variant of ['removed header','changed owner','old metadata unavailable']) test(`3146 repair asset ownership: ${extension}, ${variant}`,t=>{
  const root=fixture(t),path=`assets/generated.${extension}`;
  put(root,path,'<!-- Generated from prompts/C.prompt.md. -->\noriginal asset\n');commit(root);
  put(root,path,variant === 'changed owner' ? '<!-- Generated from prompts/A.prompt.md. -->\nchanged asset\n' : 'changed asset\n');
  appendFileSync(join(root,'prompts/A.prompt.md'),'\n');
  const reads=[],result=plan(root,{}, {git:(cwd,args)=>{
    reads.push(args);
    if(variant === 'old metadata unavailable' && args[0] === 'show' && args[1] === `HEAD:${path}`)throw Error('old asset metadata unavailable');
    return git(cwd,...args);
  }});
  const expected=variant === 'changed owner' ? ['test/runtime/A.json','test/runtime/A.recorded.json','test/runtime/C.json'] : all;
  assert.deepEqual(selected(result),expected,'3146_OLD_ASSET_OWNER_MUST_NOT_BE_OMITTED');
  assert.ok(reads.some(args=>args[0] === 'show' && args[1] === `HEAD:${path}`));
});

test('3146 repair asset ownership: excluded old headers are never read or admitted',t=>{
  const root=fixture(t),paths=['private/generated.svg','test/fixtures/nested/generated.md'];
  for(const path of paths)put(root,path,'<!-- Generated from prompts/C.prompt.md. -->\noriginal\n');
  put(root,'test/fixtures/nested/user_stories/README.md','# Fixture\n');
  put(root,'test/fixtures/nested/tests/fixture-data.json','{}');
  put(root,'pdd-workspace.json',JSON.stringify({allowed_paths:['prompts/','user_stories/','test/','docs/']}));commit(root);
  for(const path of paths)put(root,path,'<!-- Generated from prompts/B.prompt.md. -->\nchanged\n');
  appendFileSync(join(root,'prompts/A.prompt.md'),'\n');
  const result=plan(root,{}, {git:(cwd,args)=>{
    if(['show','ls-tree'].includes(args[0]))assert.ok(!args.some(arg=>paths.some(path=>arg.includes(path))),'excluded historical asset metadata must not be requested');
    return git(cwd,...args);
  }});
  assert.deepEqual(selected(result),['test/runtime/A.json','test/runtime/A.recorded.json']);
});

test('3146 repair asset ownership: real CLI dispatch retains an SVG owner after its header disappears',async t=>{
  const setup=affectedFixture(t),path='assets/generated.svg';
  putAffected(setup.repo,path,'<!-- Generated from prompts/C.prompt.md. -->\n<svg xmlns="http://www.w3.org/2000/svg"><rect width="1"/></svg>\n');
  commitAffected(setup.repo);
  putAffected(setup.repo,path,'<svg xmlns="http://www.w3.org/2000/svg"><rect width="2"/></svg>\n');setup.change('prompts/A.prompt.md');
  const fake=await affectedRuntime(t,setup),result=await cli(setup,['test','--affected','--json'],{env:{PATH:installGh(setup),PDD_RUNTIME_URL:fake.origin}});
  assert.equal(result.code,0,result.stderr);
  const output=JSON.parse(result.stdout);
  assert.deepEqual(checks(fake).map(row=>row.request.scenario).sort(),setup.tests.slice().sort(),'3146_CLI_OLD_SVG_OWNER_MUST_NOT_BE_OMITTED');
  assert.deepEqual(output.check_selection.tests,setup.tests);assert.deepEqual(output.check_selection.baseline_tests,[]);
});
