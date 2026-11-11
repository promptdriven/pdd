import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {harbor,fakeRuntime,portsFor} from './runtime-fake.mjs';
import {runCheck} from '../src/runtime/runtime-client.mjs';
for(const json of [false,true]) test(`request recovery retains incomplete coverage (json=${json})`, async t=>{
  const {repo,home,state}=harbor(t,repo=>{
    const doc=JSON.parse(readFileSync(join(repo,'tests/place-order.json')));
    doc.steps[0].checks=doc.steps[0].checks.filter(c=>c.criterion_id!=='AC2');
    writeFileSync(join(repo,'tests/place-order.json'),JSON.stringify(doc));
  });
  const fake=await fakeRuntime(t,(entry,f)=>f.normal(entry));
  const {ports}=portsFor({HOME:home,PDD_STATE_DIR:state,PDD_RUNTIME_URL:fake.origin});
  assert.notEqual(await runCheck({cwd:repo,words:['place-order'],options:{'--json':true}},ports),0);
  const first=JSON.parse(ports.stdout.text),id=first.rows[0].request_id;
  const batch=join(state,'batches',first.batch),before=readFileSync(join(batch,'batch.json'),'utf8');
  const summary=readFileSync(join(batch,'summary.json'),'utf8'),receipt=readFileSync(join(batch,`${id}.json`),'utf8');
  ports.stdout.text='';const sent=fake.posts.length;
  const code=await runCheck({cwd:repo,options:{'--request':id,...(json?{'--json':true}:{})}},ports);
  assert.equal(fake.posts.length,sent);
  assert.notEqual(code,0);
  if(json) {
    const row=JSON.parse(ports.stdout.text).rows[0];
    assert.notEqual(row.state,'passed');assert.equal(row.not_checked.length,1);
    assert.equal(row.criteria.total,first.rows[0].criteria.total);
    assert.deepEqual(row.usage,first.rows[0].usage);assert.equal(row.report_url,first.rows[0].report_url);
  } else {assert.match(ports.stdout.text,/not checked:/);assert.doesNotMatch(ports.stdout.text,/✓/);}
  assert.equal(readFileSync(join(batch,'batch.json'),'utf8'),before);
  assert.equal(readFileSync(join(batch,'summary.json'),'utf8'),summary);
  assert.equal(readFileSync(join(batch,`${id}.json`),'utf8'),receipt);
});
