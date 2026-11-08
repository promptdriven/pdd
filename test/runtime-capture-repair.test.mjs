import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {harbor,storyTest,fakeRuntime,portsFor} from './runtime-fake.mjs';
import {runCheck} from '../src/runtime-client.mjs';
import {captureSource,findTests,preflight,proseSha256,interfaceBlocks} from '../src/runtime-preflight.mjs';
import {readRunResults} from '../src/workflow-results.mjs';

const read=(root,path)=>JSON.parse(readFileSync(join(root,path),'utf8'));
const variants={
  scope:doc=>{doc.criteria_scope=['AC1'];},
  exemptions:doc=>{doc.check_exemptions=[{criterion_id:'AC2',reason:'out-of-scope',detail:'authored'}];},
  'empty-checks':doc=>{for(const step of doc.steps)step.checks=[];},
  'inexact-only':doc=>{for(const step of doc.steps)for(const c of step.checks){c.op='exists';delete c.value;}},
  'changed-text':doc=>{doc.criteria[1].text='A criterion absent from the Story.';},
  'changed-story':(_doc,repo)=>{const path=join(repo,'user_stories/place-order.md');writeFileSync(path,readFileSync(path,'utf8').replace('900','901'));}
};
const expected=variant=>['scope','exemptions'].includes(variant)?'pdd-partial-test':variant.includes('check')||variant==='inexact-only'?'unchecked-criteria':'story-criterion-mismatch';
const coverage=variant=>['empty-checks','inexact-only'].includes(variant);

for(const [variant,edit] of Object.entries(variants))for(const mode of ['test','lint','files']){
  test(`capture repair: ${mode} isolates ${variant}, retains saved refusal and excludes full-pass cache`,async t=>{
    const {repo,home,state}=harbor(t,repo=>storyTest(repo,'z-good'));
    const fake=await fakeRuntime(t,(entry,fake)=>fake.normal(entry));
    const {ports}=portsFor({HOME:home,PDD_STATE_DIR:state,PDD_RUNTIME_URL:fake.origin});
    // Seed a real complete pass to prove capture validation precedes reuse.
    assert.equal(await runCheck({cwd:repo,cache:true,words:['place-order'],options:{'--json':true}},ports),0);
    assert.ok(read(repo,'.pdd/cache/test/stories.json').stories['user_stories/place-order.md'].pass);
    const original=readFileSync(join(repo,'tests/place-order.json'),'utf8');
    let changed=false;
    ports.captureSource=(root,selection)=>{
      if(!changed){changed=true;const doc=JSON.parse(original);edit(doc,repo);writeFileSync(join(repo,'tests/place-order.json'),JSON.stringify(doc));}
      return captureSource(root,selection);
    };
    const offset=fake.posts.length;ports.stdout.text='';
    const options={'--json':true,...(mode==='lint'?{'--lint':true}:mode==='files'?{'--files':true}:{})};
    const code=await runCheck({cwd:repo,cache:mode==='test',words:['place-order','z-good'],options},ports);
    assert.equal(code,4,'A captured local refusal must prevent a successful selection.');
    const result=JSON.parse(ports.stdout.text), row=result.rows.find(r=>r.test==='tests/place-order.json');
    assert.equal(row.state,'not run');assert.equal(row.unsent,true);
    assert.equal(row.refusals[0].code,expected(variant));assert.ok(row.refusals[0].hint);
    assert.equal(result.rows.find(r=>r.test==='tests/z-good.json').state,mode==='files'?'ready':'passed');
    if(coverage(variant)){
      assert.equal(row.not_checked.length,3);
      assert.ok(row.not_checked.every(c=>c.reason&&c.text));
    }
    for(const post of fake.posts.slice(offset)){
      const listing=spawnSync('tar',['-tf','-'],{input:post.tar,encoding:'utf8'});
      assert.equal(listing.status,0);assert.ok(!listing.stdout.includes('tests/place-order.json'));
      assert.ok(listing.stdout.includes('tests/z-good.json'));
    }
    assert.deepEqual(fake.posts.slice(offset).filter(p=>p.command==='check').map(p=>p.request.scenario),mode==='test'?['tests/z-good.json']:[]);
    if(mode==='files'){
      assert.equal(fake.posts.length,offset);
      assert.ok(!result.files.some(f=>f.path==='tests/place-order.json'));
    }else{
      const saved=read(state,`batches/${result.batch}/batch.json`).rows.find(r=>r.test===row.test);
      assert.equal(saved.state,'not run');assert.equal(saved.refusals[0].code,expected(variant));
      assert.deepEqual(saved.not_checked,row.not_checked);
      ports.stdout.text='';const sent=fake.posts.length;
      assert.equal(await runCheck({cwd:repo,words:[result.batch],options:{'--read':true,'--json':true}},ports),4);
      const reread=JSON.parse(ports.stdout.text).rows.find(r=>r.test===row.test);
      assert.equal(reread.state,'not run');assert.deepEqual(reread.not_checked,row.not_checked);
      assert.equal(fake.posts.length,sent);
    }
    if(mode==='test'){
      assert.equal(read(repo,'.pdd/cache/test/stories.json').stories['user_stories/place-order.md'].pass,undefined);
      const evidence=readRunResults({root:repo},{env:{HOME:home,PDD_STATE_DIR:state}});
      const latest=evidence.find(r=>r.kind==='pdd test');
      assert.ok(latest);
      const storyLine=latest.stories.find(line=>line.includes('(place-order)'));
      assert.ok(storyLine);assert.match(storyLine,/not run \(broken-test\)/);assert.ok(!storyLine.includes('✓'));
    }
  });
}

for(const [variant,edit] of Object.entries(variants))test(`capture repair: sole ${variant} refusal removes an older cached pass without upload`,async t=>{
  const {repo,home,state}=harbor(t);
  const fake=await fakeRuntime(t,(entry,fake)=>fake.normal(entry));
  const {ports}=portsFor({HOME:home,PDD_STATE_DIR:state,PDD_RUNTIME_URL:fake.origin});
  assert.equal(await runCheck({cwd:repo,cache:true,words:['place-order'],options:{'--json':true}},ports),0);
  const before=fake.posts.length;
  let changed=false;
  ports.captureSource=(root,selection)=>{
    if(!changed){changed=true;const doc=read(repo,'tests/place-order.json');edit(doc,repo);writeFileSync(join(repo,'tests/place-order.json'),JSON.stringify(doc));}
    return captureSource(root,selection);
  };
  ports.stdout.text='';
  assert.equal(await runCheck({cwd:repo,cache:true,words:['place-order'],options:{'--json':true}},ports),4);
  const row=JSON.parse(ports.stdout.text).rows[0];
  assert.equal(row.state,'not run');assert.equal(row.refusals[0].code,expected(variant));
  if(coverage(variant))assert.equal(row.not_checked.length,3);
  assert.equal(fake.posts.length,before);
  assert.equal(read(repo,'.pdd/cache/test/stories.json').stories['user_stories/place-order.md'].pass,undefined);
});

const root=fileURLToPath(new URL('..',import.meta.url));
test('capture repair: changed output prompt keeps a current draft prose hash',()=>{
  const text=readFileSync(join(root,'prompts/cli/runtime-output.prompt.md'),'utf8');
  const iface=JSON.parse(interfaceBlocks(text)[0][1]);
  assert.equal(iface.status,'draft');assert.equal(iface.prose_sha256,proseSha256(text));
});
for(const name of ['check-no-verdict','pr-current-head-evidence','prompt-tests-line'])test(`capture repair: ${name} has no stale output interface refusal`,()=>{
  const found=findTests({root});
  const selected=found.tests.filter(t=>t.path===`test/runtime/${name}.json`);
  assert.equal(selected.length,1);
  const result=preflight({root,found,selected});
  assert.ok(!result.rows.flatMap(r=>r.refusals).some(r=>r.code==='interface-stale'));
});
