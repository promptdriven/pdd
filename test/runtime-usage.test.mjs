import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

const run = async (setup, fake, options) => {
  const { ports, clock } = portsFor({ HOME:setup.home, PDD_STATE_DIR:setup.state, PDD_RUNTIME_URL:fake.origin });
  const code=await runCheck({words:options['--read'] ? [] : ['place-order'],options:{'--json':true,...options},cwd:setup.repo},ports);
  return {code,json:JSON.parse(ports.stdout.text),clock};
};

test('issue 13: checks held behind unknown lint have zero calls, including an older saved batch read',async t=>{
  const setup=harbor(t);let ready=false;
  const fake=await fakeRuntime(t,(entry,f)=>{
    if(entry.method==='POST')return {status:202,json:f.job(entry.request.requestId,'lint','queued')};
    const id=entry.url.split('/').at(-1);return {status:200,json:ready?f.lint(id):f.job(id,'lint','running')};
  });
  const first=await run(setup,fake,{'--timeout':'1'});
  assert.equal(first.code,3);assert.equal(first.json.rows[0].state,'not_run');
  assert.equal(first.json.rows[0].request_id,null);assert.equal(first.json.rows[0].calls,0);
  assert.doesNotMatch(first.json.summary_line,/\+ \d+ unknown/);
  assert.deepEqual(fake.posts.map(p=>p.command),['lint']);
  const file=join(setup.state,'batches',first.json.batch,'batch.json');
  const saved=JSON.parse(readFileSync(file,'utf8'));
  saved.rows[0].calls='unknown';saved.rows[0].phase='server';writeFileSync(file,JSON.stringify(saved));
  ready=true;const reads=fake.gets.length;
  const again=await run(setup,fake,{'--read':first.json.batch});
  assert.equal(again.code,5);assert.equal(again.json.rows[0].calls,0);
  assert.equal(again.json.rows[0].request_id,null);assert.equal(again.clock.uuids,0);
  assert.equal(fake.posts.length,1);assert.equal(fake.gets.length,reads+1,'only the outstanding lint is read');
  assert.doesNotMatch(again.json.summary_line,/\+ \d+ unknown/);
});

test('issues 11 and 20: incomplete server usage stays unknown despite a raw zero provider count',async t=>{
  const setup=harbor(t);
  const fake=await fakeRuntime(t,(entry,f)=>{
    if(entry.command==='lint')return {status:200,json:f.lint(entry.request.requestId)};
    const answer=f.check(entry.request.requestId,'refused',[],[{code:'graph-data-boundary-failure'}]);
    answer.usage={...answer.usage,calls:'unknown',reported_calls:0,accounting_complete:false};
    answer.result.report.provider_calls=0;
    answer.result.report.samples=[{refusal_call_accounting:'incomplete',steps:[]}];
    return {status:200,json:answer};
  });
  const result=await run(setup,fake,{});
  assert.equal(result.code,4);assert.equal(result.json.rows[0].calls,'unknown');
  assert.match(result.json.summary_line,/\+ 1 unknown/);
  assert.deepEqual(fake.posts.map(p=>p.command),['lint','check']);
});
