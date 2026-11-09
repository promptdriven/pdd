import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import * as runner from '../src/workflow-runner.mjs';
import { captureSource } from '../src/runtime-preflight.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { fakeRuntime, portsFor, sink, storyTest } from './runtime-fake.mjs';

const OLD = '20261027-170000-abcd';
const PATH = 'tests/place-order.json';
async function setup(t, { outcome = 'passed', mixed = false, native = false, uncertain = false, restart = null } = {}) {
  const f = await fixture(t); await f.run();
  const run = f.record(); run.state = 'paused'; run.runtimeWait = {at:f.clock,batch:OLD,cause:'unknown',reason:'runner-stopped'};
  writeRun(run);
  cpSync(join(packageRoot,'test/fixtures/harbor'),run.root,{recursive:true});
  if (mixed) storyTest(run.root,'already-passed');
  f.git(run.root,'add','.'); f.git(run.root,'commit','-qm','test source');
  const paths = [PATH,...(mixed?['tests/already-passed.json']:[])];
  const source = captureSource(run.root,{tests:paths,appMap:null});
  const folder = join(f.ports.env.HOME,'.pdd','runtime','batches',OLD); mkdirSync(folder,{recursive:true});
  const rows = [{test:PATH,story:'place-order',state:'partial',recovery_state:'unknown',max_calls:23,request_ids:['old-check'],reason:{code:'runner-stopped'},calls:3},
    ...(mixed?[{test:paths[1],story:'already-passed',state:'passed',max_calls:40,calls:2}]:[])];
  const batch = {version:1,batch:OLD,intent:'check',root:run.root,created_at:new Date(f.clock).toISOString(),source_sha256:source.sha256,rows};
  writeFileSync(join(folder,'batch.json'),JSON.stringify(batch));
  writeFileSync(join(folder,'summary.json'),JSON.stringify({batch:OLD,rows}));
  f.clock += 1000;
  let restartId;
  const fake = await fakeRuntime(t, entry => {
    if (entry.command==='lint') return {status:200,json:fake.lint(entry.request.requestId)};
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    if (restart && !restartId) restartId = id;
    if (restart && id === restartId) {
      const refusal = {code:'service-restarted'};
      const result = restart === 'refusals' ? {refusals:[refusal]} : {report:{refusal}};
      return {status:200,json:fake.job(id,'check','unknown',result,2)};
    }
    return {status:200,json:fake.check(id,outcome)};
  });
  f.ports.env={...f.ports.env,PDD_RUNTIME_URL:fake.origin};
  const {ports,clock} = portsFor(f.ports.env); clock.now=f.clock;
  const sends = [];
  if (native) {
    const bin=join(f.base,'bin');mkdirSync(bin);
    writeFileSync(join(bin,'gh'),'#!/bin/sh\nif [ "$1" = auth ]; then echo fixture-token; else echo "octo 4242"; fi\n',{mode:0o700});
    f.ports.env={...f.ports.env,PATH:bin+':'+process.env.PATH,PDD_RUNTIME_URL:fake.origin};
  }
  const workflowRunner = { ...runner, resendChecks: (input, forwarded) => runner.resendChecks(input,{
    ...f.ports,...forwarded,isTTY:false,execFile:async (file,args,options)=> {
      if (file !== process.execPath) return f.ports.execFile(file,args,options);
      const current=f.record();
      const sending = (options.cwd===current.root?current:JSON.parse(readFileSync(join(current.commonDir,'pdd','runs','18','status.json')))).checkResends.at(-1);
      assert.equal(sending.state,'sending','durable consumption precedes the paid boundary');
      sends.push({file,args,options});
      if (uncertain) throw Error('synthetic lost child reply');
      if (native) return promisify(execFile)(file,args,{...options,encoding:'utf8'});
      ports.stdout=sink(); ports.stderr=sink();
      const result = await runCheck({cwd:options.cwd,words:inputWords(args),options:{'--json':true,'--max-calls':Number(args[args.indexOf('--max-calls')+1]),'--cache-clear':true}},{...ports,env:options.env});
      return {stdout:ports.stdout.text,code:result};
    }
  })};
  const command = async (args = [], words = 'resend once\n') => {
    const stdout=sink(),stderr=sink();
    const code=await runPdd(['workflow','resend','17',...args],{cwd:f.source,packageRoot,env:f.ports.env,workflowRunner,stdin:(async function*(){yield words;})(),stdout,stderr});
    return {code,out:stdout.text+stderr.text};
  };
  return {f,run,folder,batch,command,sends,fake};
}
function inputWords(args) {return args.slice(2,args.indexOf('--json'));}

test('3097: missing or blank person words send nothing and change no record',async t=>{
  const s=await setup(t),before=s.f.record();
  const missing=await s.command(),blank=await s.command(['--said','-'],' \n');
  assert.notEqual(missing.code,0);assert.match(missing.out,/person.*decide/i);
  assert.notEqual(blank.code,0);assert.match(blank.out,/--said.*nonblank/);
  assert.equal(s.sends.length,0);assert.deepEqual(s.f.record(),before);
});

test('3097: one said decision resends only lost rows with a bounded cap and retains both batches',async t=>{
  const s=await setup(t,{mixed:true}),before=s.f.record();
  const result=await s.command(['--said','-'],'Yes, resend this check once.\n');
  assert.equal(result.code,0,result.out);
  const after=s.f.record(),record=after.checkResends.at(-1);
  assert.equal(s.sends.length,1);assert.deepEqual(inputWords(s.sends[0].args),[PATH]);
  assert.equal(record.words,'Yes, resend this check once.\n');assert.equal(record.route,'said');
  assert.equal(record.oldBatch,OLD);assert.deepEqual(record.oldCost,{calls:5,knownCalls:5});
  assert.equal(record.maxCalls,23);assert.equal(record.state,'verdict');assert.notEqual(record.newBatch,OLD);
  assert.deepEqual(JSON.parse(readFileSync(join(s.folder,'batch.json'))),s.batch,'old paid receipt remains intact');
  for(const key of ['gate','question','done','runtimeWait','state','parking'])assert.deepEqual(after[key],before[key],key);
  assert.notEqual((await s.command(['--said','-'])).code,0);assert.equal(s.sends.length,1);
});

test('3097: another lost verdict records its new batch and stops without another send',async t=>{
  const s=await setup(t,{outcome:'unknown'});
  const result=await s.command(['--said','-']);assert.notEqual(result.code,0);
  assert.ok(s.f.record().checkResends?.length,'supported resend records the authorized replacement');
  const receipt=s.f.record().checkResends.at(-1);assert.equal(receipt.state,'no-verdict');
  assert.ok(receipt.newBatch);assert.notEqual(receipt.newBatch,OLD);assert.equal(s.sends.length,1);
  assert.match(result.out,new RegExp(receipt.newBatch));
});

for(const change of ['changed-source','active','passed','missing-cap','already-consumed','strict']) test(`3097 refuses ${change} before sending`,async t=>{
  const s=await setup(t);
  if(change==='changed-source')writeFileSync(join(s.run.root,'prompts/place_order.prompt.md'),'changed source');
  if(['active','passed','missing-cap'].includes(change)){
    const batch=structuredClone(s.batch);
    if(change==='missing-cap')delete batch.rows[0].max_calls;
    else batch.rows[0].state=batch.rows[0].recovery_state=change==='active'?'running':'passed';
    writeFileSync(join(s.folder,'batch.json'),JSON.stringify(batch));
  }
  if(change==='already-consumed'){const run=s.f.record();run.checkResends=[{oldBatch:OLD,state:'sending'}];writeRun(run);}
  if(change==='strict')writeFileSync(join(s.f.source,'pdd.json'),JSON.stringify({strict_approvals:true}));
  const result=await s.command(['--said','-']);assert.notEqual(result.code,0,result.out);assert.equal(s.sends.length,0);
  const guard={'changed-source':/source changed/,active:/no stopped lost-verdict/,passed:/no stopped lost-verdict/,
    'missing-cap':/valid call caps/,'already-consumed':/consumed.*decision/,strict:/person terminal/};
  assert.match(result.out,guard[change]);
});


test('3097: the installed test process sends to the local fake with a private HOME and config',async t=>{
  const s=await setup(t,{native:true});
  const result=await s.command(['--said','-']);assert.equal(result.code,0,result.out);
  assert.equal(s.sends.length,1);assert.equal(s.fake.posts.filter(row=>row.command==='check').length,1);
  assert.equal(s.f.record().checkResends.at(-1).state,'verdict');
});

test('3097: an unknown child reply consumes the decision and cannot be resent',async t=>{
  const s=await setup(t,{uncertain:true});
  assert.notEqual((await s.command(['--said','-'])).code,0);
  assert.ok(s.f.record().checkResends?.length,'resend custody must be recorded');
  assert.equal(s.f.record().checkResends.at(-1).state,'uncertain');
  assert.notEqual((await s.command(['--said','-'])).code,0);assert.equal(s.sends.length,1);
});

for(const outcome of ['passed','unknown'])test(`3097: one decision for a group; first outcome ${outcome}`,async t=>{
  const s=await setup(t,{outcome});
  const original=s.f.record(), secondRoot=join(s.f.base,'second-worktree');
  s.f.git(s.f.source,'worktree','add','-qb','second-fixture',secondRoot,s.f.git(original.root,'rev-parse','HEAD'));
  const second={...structuredClone(original),number:18,runId:'second-run',root:secondRoot,runDir:join(original.commonDir,'pdd','runs','18')};
  mkdirSync(second.runDir,{recursive:true});writeRun(second);
  const old='20261027-170001-efgh',folder=join(s.f.ports.env.HOME,'.pdd','runtime','batches',old);mkdirSync(folder,{recursive:true});
  writeFileSync(join(folder,'batch.json'),JSON.stringify({...s.batch,batch:old,root:secondRoot}));
  writeFileSync(join(folder,'summary.json'),JSON.stringify({batch:old,rows:s.batch.rows}));
  const result=await s.command(['18','--said','-'],'Resend both once.\n');
  assert.equal(result.code,outcome==='passed'?0:1,result.out);
  const a=s.f.record().checkResends.at(-1),b=JSON.parse(readFileSync(join(second.runDir,'status.json'))).checkResends.at(-1);
  assert.equal(a.id,b.id);assert.equal(a.words,b.words);assert.equal(a.oldBatch,OLD);assert.equal(b.oldBatch,old);
  assert.equal(s.sends.length,outcome==='passed'?2:1);
  assert.equal(b.state,outcome==='passed'?'verdict':'authorized');
});


test('3097: source changes while reading the decision send nothing',async t=>{
  const s=await setup(t);
  const stdout=sink(),stderr=sink();
  const code=await runPdd(['workflow','resend','17','--said','-'],{cwd:s.f.source,packageRoot,env:s.f.ports.env,stdout,stderr,
    workflowRunner:{...runner,resendChecks:(input,ports)=>runner.resendChecks(input,{...s.f.ports,...ports,isTTY:false})},
    stdin:(async function*(){writeFileSync(join(s.run.root,'prompts/place_order.prompt.md'),'changed while deciding');yield 'Resend once.';})()});
  assert.notEqual(code,0);assert.match(stdout.text+stderr.text,/source changed during.*decision/);
  assert.equal(s.sends.length,0);assert.equal(s.f.record().checkResends,undefined);
});


for (const restart of ['refusals','report']) test(`3097 repair 1: native ${restart} restart stops the group after one paid attempt and later reads stay read-only`,async t=>{
  const s=await setup(t,{native:true,restart});
  const original=s.f.record(), secondRoot=join(s.f.base,'second-worktree');
  s.f.git(s.f.source,'worktree','add','-qb','second-fixture',secondRoot,s.f.git(original.root,'rev-parse','HEAD'));
  const second={...structuredClone(original),number:18,runId:'second-run',root:secondRoot,runDir:join(original.commonDir,'pdd','runs','18')};
  mkdirSync(second.runDir,{recursive:true});writeRun(second);
  const old='20261027-170001-efgh',folder=join(s.f.ports.env.HOME,'.pdd','runtime','batches',old);mkdirSync(folder,{recursive:true});
  writeFileSync(join(folder,'batch.json'),JSON.stringify({...s.batch,batch:old,root:secondRoot}));
  writeFileSync(join(folder,'summary.json'),JSON.stringify({batch:old,rows:s.batch.rows}));
  const result=await s.command(['18','--said','-'],'Resend both once.\n');
  const posts=s.fake.posts.filter(row=>row.command==='check');
  assert.equal(posts.length,1,'a structured restart must not spend a second paid attempt');
  assert.equal(result.code,1,result.out);
  assert.equal(s.sends.length,1,'the next run must not start after a lost verdict');
  assert.deepEqual(posts.map(row=>row.request.max_calls),[23]);
  const record=s.f.record().checkResends.at(-1);
  assert.equal(record.state,'no-verdict');assert.ok(record.newBatch);assert.notEqual(record.newBatch,OLD);
  assert.equal(JSON.parse(readFileSync(join(second.runDir,'status.json'))).checkResends.at(-1).state,'authorized');
  const receiptFolder=join(s.f.ports.env.HOME,'.pdd','runtime','batches',record.newBatch);
  const receipt=JSON.parse(readFileSync(join(receiptFolder,'batch.json')));
  const ids=receipt.rows[0].request_ids;
  assert.deepEqual(ids,[posts[0].request.requestId]);
  const raw=JSON.parse(readFileSync(join(receiptFolder,`${ids[0]}.json`)));
  assert.equal(raw.state,'unknown');assert.equal(raw.usage.calls,2);
  assert.equal((raw.result.refusals?.[0] ?? raw.result.report.refusal).code,'service-restarted');
  assert.deepEqual(JSON.parse(readFileSync(join(s.folder,'batch.json'))),s.batch);
  assert.match(result.out,new RegExp(record.newBatch));
  const env={...s.sends[0].options.env};delete env.PDD_CHECK_SINGLE_ATTEMPT;
  for(const mode of ['--read','--retry']){
    let output;
    try { output=await promisify(execFile)(process.execPath,[join(packageRoot,'bin','pdd.mjs'),'test',mode,record.newBatch,'--json'],{cwd:s.run.root,env,encoding:'utf8'}); }
    catch(error){output=error;}
    const report=JSON.parse(output.stdout);
    assert.notEqual(report.exit_code,0);
    assert.equal(s.fake.posts.filter(row=>row.command==='check').length,1,`${mode} cannot replace a person-authorized lost attempt`);
    assert.deepEqual(JSON.parse(readFileSync(join(receiptFolder,'batch.json'))).rows[0].request_ids,ids);
  }
});
