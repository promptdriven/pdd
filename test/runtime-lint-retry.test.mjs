import test from 'node:test';
import assert from 'node:assert/strict';
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

// Wire shape independently transcribed from the saved staging queue refusal and server/work_queue.py.
function queuedOut(f, id, retryable = true) {
  const refusal = { code:'lint-queue-timeout', message:'Lint is waiting for a free slot.', details:{retryable,retry_after:5,max_wait_seconds:20} };
  return f.job(id,'lint','refused',{exitCode:1,refusals:[refusal],report:{verdict:'refused',provider_calls:0,dispatch:'not_started',refusal,lint:{complete:false,tests:[]}}},0);
}
async function invoke(t, mode, answer, extra={}) {
  const setup=harbor(t), fake=await fakeRuntime(t,answer);
  const {ports,clock}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin},extra);
  const options=mode==='lint'?{'--lint':true,'--json':true}:mode==='try'?{'--no-open':true,'--no-wait':true}:{'--json':true};
  const code=await(mode==='try'?runTry:runCheck)({cwd:setup.repo,words:['place-order'],options},ports);
  return {setup,fake,ports,clock,code};
}
const normal=(entry,f)=>entry.command==='try'?{status:200,json:f.tryJob(entry.request.requestId)}
  :entry.url.endsWith('/tests')||entry.url.endsWith('/approvals')?{status:404,json:{}}:f.normal(entry);

for(const mode of ['check','lint','try']) test(`LINT-RETRY: ${mode} retries a confirmed queue timeout, retains IDs and succeeds`,async t=>{
  let attempt=0;
  const r=await invoke(t,mode,(entry,f)=>entry.command==='lint'&&++attempt===1?{status:200,json:queuedOut(f,entry.request.requestId)}:normal(entry,f));
  assert.equal(r.code,0,r.ports.stderr.text+r.ports.stdout.text);
  const lints=r.fake.posts.filter(p=>p.command==='lint');assert.equal(lints.length,2);
  assert.notEqual(lints[0].request.requestId,lints[1].request.requestId);assert.ok(lints[0].tar.equals(lints[1].tar));
  assert.deepEqual(lints[1].request,{...lints[0].request,requestId:lints[1].request.requestId},'retry keeps every original lint option');
  if(mode!=='lint') for(const p of lints) assert.equal(Object.hasOwn(p.request,'complete'),false);
  assert.match(r.ports.stderr.text,/The server is busy\. Waiting for a lint slot/);
  assert.doesNotMatch(r.ports.stderr.text+r.ports.stdout.text,/lint result is unknown/);
  const saved=r.setup.state;
  const dir=mode==='try'?join(saved,'tries'):join(saved,'batches',readdirSync(join(saved,'batches'))[0]);
  assert.equal(JSON.parse(readFileSync(join(dir,lints[0].request.requestId+'.json'))).state,'refused');
  assert.equal(r.fake.posts.filter(p=>p.command==='check').length,mode==='check'?1:0);
  assert.equal(r.fake.posts.filter(p=>p.command==='try').length,mode==='try'?1:0);
});

for(const mode of ['check','lint','try']) test(`LINT-RETRY: ${mode} waits through busy attempts until its deadline as not-run, never unknown`,async t=>{
  const r=await invoke(t,mode,(e,f)=>({status:200,json:queuedOut(f,e.request.requestId)}));
  assert.equal(r.code,5,r.ports.stderr.text+r.ports.stdout.text);
  if(mode==='check') assert.equal(JSON.parse(r.ports.stdout.text).rows[0].calls,0,'confirmed busy lint leaves a positively unsent zero-call check');
  assert.ok(r.fake.posts.length>3);assert.ok(r.fake.posts.every(p=>p.command==='lint'));
  assert.equal(new Set(r.fake.posts.map(p=>p.request.requestId)).size,r.fake.posts.length);
  assert.match(r.ports.stderr.text+r.ports.stdout.text,/server.*busy/i);
  assert.match(r.ports.stderr.text+r.ports.stdout.text,/same.*command.*later/i);
  assert.doesNotMatch(r.ports.stderr.text+r.ports.stdout.text,/lint result is unknown|"state":"unknown"|Fix the prompt/i);
  assert.ok(r.clock.now-Date.parse('2026-10-27T16:27:47Z')<=90_000);
});

test('LINT-RETRY: queued GET and a lost POST retry only after that same ID confirms safe capacity',async t=>{
  let first,reads=0;
  const r=await invoke(t,'check',(e,f)=>{
    if(e.command==='lint') {if(!first){first=e.request.requestId;return{destroy:true};}return{status:200,json:f.lint(e.request.requestId)};}
    if(e.method==='GET'&&e.url.endsWith(first)){reads++;return reads===1?{status:200,json:f.job(first,'lint','queued')}:{status:200,json:queuedOut(f,first)};}
    return normal(e,f);
  });
  assert.equal(r.code,0,r.ports.stderr.text);assert.equal(reads,2);assert.equal(r.fake.posts.filter(p=>p.command==='lint').length,2);
});

test('LINT-RETRY: literal opt-in required; unrelated or uncertain replies never repost lint',async t=>{
  for(const value of [false,undefined,'true']) {
    const r=await invoke(t,'check',(e,f)=>{const answer=queuedOut(f,e.request.requestId,value);if(value===undefined){delete answer.result.report.refusal.details.retryable;}return{status:200,json:answer};});
    assert.equal(r.fake.posts.length,1);assert.notEqual(r.code,0);
  }
  const r=await invoke(t,'check',(e,f)=>e.method==='POST'?{destroy:true}:{status:404,json:{state:'refused',job_created:false,error:{code:'lint-queue-timeout',details:{retryable:true}}}});
  assert.equal(r.code,3);assert.equal(r.fake.posts.length,1);
  assert.ok(r.clock.now-Date.parse('2026-10-27T16:27:47Z')<=90_000);
});

test('LINT-RETRY: direct lint queue full is busy, and interrupting backoff sends nothing else',async t=>{
  let attempt=0;
  const r=await invoke(t,'lint',(e,f)=>++attempt===1?{status:503,json:{error:{code:'lint-queue-full',details:{retryable:true,retry_after:1}}}}:{status:200,json:f.lint(e.request.requestId)});
  assert.equal(r.code,0,r.ports.stderr.text);assert.equal(r.fake.posts.length,2);
  let interrupt;
  const stopped=await invoke(t,'check',(e,f)=>({status:200,json:queuedOut(f,e.request.requestId)}),{
    onInterrupt:fn=>{interrupt=fn;return()=>{};},sleep:async()=>{interrupt();}
  });
  assert.equal(stopped.fake.posts.length,1);assert.doesNotMatch(stopped.ports.stderr.text+stopped.ports.stdout.text,/lint result is unknown|"state":"unknown"/i);
});

for (const json of [false, true]) test(`h2048-1: explicit lint still running exits 3, never success (json=${json})`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => ({ status: 200, json: f.job(e.request?.requestId ?? e.url.split('/').at(-1), 'lint', e.method === 'POST' ? 'queued' : 'running') }));
  const { ports, clock } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true, ...(json ? { '--json': true } : {}) } }, ports), 3);
  assert.match(ports.stderr.text, /Lint is still running.*pdd check --read/);
  assert.equal(fake.posts.length, 1); assert.equal(fake.posts[0].command, 'lint');
  assert.ok(clock.now - Date.parse('2026-10-27T16:27:47Z') <= 90_000);
});
