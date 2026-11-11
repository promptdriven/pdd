import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {harbor,storyTest,fakeRuntime,portsFor} from './runtime-fake.mjs';
import {runCheck} from '../src/runtime/runtime-client.mjs';
for(const mode of ['test','lint','files']) test(`local broken test has a named not-run result in ${mode}`, async t=>{
  const {repo,home,state}=harbor(t,repo=>{
    storyTest(repo,'z-broken');const doc=JSON.parse(readFileSync(join(repo,'tests/z-broken.json')));
    doc.steps[0].entry_path='prompts/missing.prompt.md';writeFileSync(join(repo,'tests/z-broken.json'),JSON.stringify(doc));
  });
  const fake=await fakeRuntime(t,(entry,f)=>f.normal(entry));
  const {ports}=portsFor({HOME:home,PDD_STATE_DIR:state,PDD_RUNTIME_URL:fake.origin});
  assert.equal(await runCheck({cwd:repo,words:['place-order','z-broken'],options:{'--json':true,...(mode==='lint'?{'--lint':true}:mode==='files'?{'--files':true}:{})}},ports),4);
  const result=JSON.parse(ports.stdout.text),row=result.rows.find(r=>r.test==='tests/z-broken.json');
  assert.equal(row.state,'not run');assert.equal(row.reason.code,'broken-test');assert.equal(row.unsent,true);
  assert.ok(row.refusals[0].code);assert.ok(row.refusals[0].hint);
  assert.equal(result.rows.find(r=>r.test==='tests/place-order.json').state,mode==='files'?'ready':'passed');
  assert.ok(!fake.posts.some(p=>p.command==='check'&&p.request.scenario===row.test));
  if(mode!=='files') {
    const saved=JSON.parse(readFileSync(join(state,'batches',result.batch,'batch.json'))).rows.find(r=>r.test===row.test);
    assert.equal(saved.state,'not run');assert.equal(saved.reason.code,'broken-test');assert.equal(saved.recovery_state,'refused');
    assert.deepEqual(saved.refusals.map(({code,message,hint})=>({code,message,hint})),row.refusals.map(({code,message,hint})=>({code,message,hint})));
  }
});
