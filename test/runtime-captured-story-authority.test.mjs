import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {harbor,storyTest,fakeRuntime,portsFor} from './runtime-fake.mjs';
import {runCheck} from '../src/runtime-client.mjs';
import {captureSource} from '../src/runtime-preflight.mjs';
import {readRunResults,resultLines} from '../src/workflow-results.mjs';
const load=(root,path)=>JSON.parse(readFileSync(join(root,path),'utf8'));
for(const mode of ['test','lint','files']) for(const variant of ['missing','missing-incomplete','wrong'])
test(`captured Story authority: ${variant} in ${mode}`, async t=>{
  const {repo,home,state}=harbor(t,repo=>{
    storyTest(repo,'z-good');
    if(variant==='missing-incomplete') {
      const doc=load(repo,'tests/place-order.json');
      doc.steps[0].checks=doc.steps[0].checks.filter(c=>c.criterion_id!=='AC2');
      writeFileSync(join(repo,'tests/place-order.json'),JSON.stringify(doc));
    }
  });
  const fake=await fakeRuntime(t,(entry,f)=>f.normal(entry));
  const {ports}=portsFor({HOME:home,PDD_STATE_DIR:state,PDD_RUNTIME_URL:fake.origin});
  let changed=false;
  ports.captureSource=(root,selection)=>{
    if(!changed) {
      changed=true; const doc=load(root,'tests/place-order.json');
      if(variant==='wrong')doc.story_path='user_stories/z-good.md';else delete doc.story_path;
      writeFileSync(join(root,'tests/place-order.json'),JSON.stringify(doc));
    }
    return captureSource(root,selection);
  };
  const code=await runCheck({cwd:repo,words:['place-order','z-good'],options:{'--json':true,...(mode==='lint'?{'--lint':true}:mode==='files'?{'--files':true}:{})}},ports);
  const result=JSON.parse(ports.stdout.text),row=result.rows.find(r=>r.test==='tests/place-order.json');
  assert.equal(row.state,'not run'); assert.equal(code,4); assert.equal(row.unsent,true);
  assert.equal(row.refusals[0].code,variant==='wrong'?'pdd-story-mismatch':'pdd-no-story');
  assert.ok(row.refusals[0].hint);
  if(variant==='missing-incomplete' && mode!=='files')assert.equal(row.not_checked.length,1);
  assert.equal(result.rows.find(r=>r.test==='tests/z-good.json').state,mode==='files'?'ready':'passed');
  assert.deepEqual(fake.posts.filter(p=>p.command==='check').map(p=>p.request.scenario),mode==='test'?['tests/z-good.json']:[]);
  if(mode==='files')assert.ok(!result.files.some(f=>f.path===row.test));
  else {
    const saved=load(state,`batches/${result.batch}/batch.json`).rows.find(r=>r.test===row.test);
    assert.equal(saved.state,'not run');
    if(variant==='missing-incomplete')assert.equal(saved.not_checked.length,1);
    assert.doesNotMatch(load(state,`batches/${result.batch}/summary.json`).summary_line,/✓/);
    if(mode==='test') {
      const downstream=readRunResults({root:repo},{env:{HOME:home,PDD_STATE_DIR:state}});
      assert.ok(downstream.length);
      assert.ok(downstream[0].stories.some(line=>line.includes('place-order') && !line.includes('✓')));
    }
  }
});
