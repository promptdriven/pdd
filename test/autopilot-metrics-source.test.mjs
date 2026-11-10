import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {readAutopilotMetrics,recordAutopilotMetric} from '../src/autopilot-metrics-source.mjs';
import {runMetrics} from '../src/metrics-command.mjs';

const head='a'.repeat(40), stale='b'.repeat(40), merge='c'.repeat(40);
const at='2026-11-10T12:00:00Z', observedAt='2026-11-11T10:00:00Z';
const evidence='Evidence: runtime=pass (2/2); vectors=pass (3/3); formal=not-run; tests=pass';
const comment=(sha=head)=>({created_at:at,body:`Autopilot merge check passed for head ${sha}.\n- CI: green (2 check(s))\n- Full test suite: pass\n- Review: PASS from a fresh reviewer\n${evidence}\n<!-- pdd:autopilot-core:merge:${sha} -->`});
const rows=report=>Object.fromEntries(report.rows.map(row=>[row.key,row.day]));
function world(t) {
  const root=fs.mkdtempSync(join(tmpdir(),'autopilot-metrics-')); t.after(()=>fs.rmSync(root,{recursive:true,force:true}));
  const save=(path,value)=>{fs.mkdirSync(join(path,'..'),{recursive:true});fs.writeFileSync(path,typeof value === 'string' ? value : JSON.stringify(value));};
  const add=(id,repo)=>{const core=join(root,`${id}-core`);save(join(root,`${id}.json`),{repo,enabled:false}); fs.mkdirSync(join(core,'jobs'),{recursive:true});return core;};
  const core=add('a'.repeat(20),'owner/alpha');
  const calls=[];
  const github=async(repo,path)=>{
    calls.push([repo,path]);
    if(path === 'pulls/10') return {head:{sha:head},body:evidence,updated_at:at,merged_at:'2026-11-10T13:00:00Z',merge_commit_sha:merge};
    if(path === 'issues/10/comments') return [comment()];
    if(path === `commits/${merge}/check-runs`) return {check_runs:[{head_sha:merge,status:'completed',conclusion:'failure',completed_at:'2026-11-10T14:00:00Z'}]};
    throw Error('unavailable');
  };
  return {root,core,save,add,calls,ports:{stateRoot:root,github},read:ports=>readAutopilotMetrics({timezone:'UTC',observedAt},{stateRoot:root,github,...ports})};
}

test('reads core jobs/history, ignores corrupt lines, deduplicates and collects core PR evidence',async t=>{
  const w=world(t);
  w.save(join(w.core,'history.jsonl'),`{broken\n${JSON.stringify({at:Date.parse('2026-11-09T11:00:00Z'),issue:1,outcome:'merged',pr:10})}\n`);
  w.save(join(w.core,'jobs','1.json'),{schema:'pdd.core-job.v1',issue:1,started:Date.parse('2026-11-10T09:00:00Z'),prAt:Date.parse(at),pr:10,head,agent:{started:Date.parse(at)}});
  const other=w.add('b'.repeat(20),'owner/beta'); w.save(join(other,'jobs','1.json'),{schema:'pdd.core-job.v1',issue:1,started:Date.parse(at)});
  const report=await w.read();
  assert.deepEqual(rows(report),{started:2,worked:2,runtime:1,vectors:1,formal:0,validated:1,merged:1,regressions:1,startedToMerged:50});
  assert.equal(w.calls.filter(([,path])=>path === 'pulls/10').length,1);
});

test('missing evidence never implies Runtime/vector/formal success or validation',async t=>{
  const w=world(t); w.save(join(w.core,'history.jsonl'),JSON.stringify({at:Date.parse(at),issue:1,outcome:'merged',pr:10}));
  const report=await w.read({github:async(repo,path)=>path === 'pulls/10' ? {head:{sha:head},body:'Runtime: PASS',updated_at:at} : path.includes('comments') ? [{...comment(),body:comment().body.replace(evidence,'')}] : {check_runs:[]}});
  assert.equal(rows(report).runtime,0); assert.equal(rows(report).vectors,0); assert.equal(rows(report).formal,0); assert.equal(rows(report).validated,0); assert.equal(rows(report).merged,1);
});

test('stale review heads, absent/red CI and manual PR merges cannot establish validation or automatic merge',async t=>{
  for(const body of [comment(stale).body,comment().body.replace('green (2 check(s))','none'),comment().body.replace('green (2 check(s))','red'),comment().body.replace('- Review: PASS from a fresh reviewer','- Review: PASS'),evidence]) {
    const w=world(t); w.save(join(w.core,'jobs','1.json'),{schema:'pdd.core-job.v1',issue:1,started:Date.parse(at),pr:10,head});
    const report=await w.read({github:async(repo,path)=>path.includes('comments') ? [{created_at:at,body}] : path === 'pulls/10' ? {head:{sha:head},merged_at:'2026-11-10T13:00:00Z'} : {check_runs:[]}});
    assert.equal(rows(report).validated,0);
    if(body === evidence || body === comment(stale).body) assert.equal(rows(report).merged,0);
  }
});

test('foreign merge-commit CI and unrecorded prior merges never count regressions',async t=>{
  const w=world(t); w.save(join(w.core,'history.jsonl'),JSON.stringify({at:Date.parse(at),issue:1,outcome:'merged',pr:10}));
  const report=await w.read({github:async(repo,path)=>path.includes('check-runs') ? {check_runs:[{head_sha:stale,status:'completed',conclusion:'failure',completed_at:at}]} : w.ports.github(repo,path)});
  assert.equal(rows(report).regressions,0);
});

test('PR merge time refines cleanup history across the 09:00 boundary without double counting',async t=>{
  const w=world(t); w.save(join(w.core,'history.jsonl'),JSON.stringify({at:Date.parse('2026-11-10T09:01:00Z'),issue:1,outcome:'merged',pr:10}));
  const report=await w.read({github:async(repo,path)=>path === 'pulls/10' ? {head:{sha:head},merged_at:'2026-11-10T08:59:00Z'} : []});
  assert.equal(rows(report).merged,0);
  assert.equal(rows(report).worked,1);
  assert.equal(report.rows.find(row=>row.key === 'merged').weekAverage,0.5);
});

test('merge-check comment followed by manual merge cannot credit Autopilot or its regressions',async t=>{
  const w=world(t);
  w.save(join(w.core,'jobs','1.json'),{schema:'pdd.core-job.v1',issue:1,started:Date.parse(at),pr:10,head});
  const report=await w.read();
  assert.equal(rows(report).validated,1);
  assert.equal(rows(report).merged,0);
  assert.equal(rows(report).regressions,0);
});

test('hook preserves starts and BAD/revert discoveries after cleanup without leaking arbitrary fields',async t=>{
  const w=world(t); w.save(join(w.core,'history.jsonl'),'{cut');
  for(const event of [{kind:'started',at},{kind:'merged',at,pr:10},{kind:'regression',at:'2026-11-10T14:00:00Z',pr:10,reason:'reverted'}]) recordAutopilotMetric({root:w.core,repo:'OWNER/alpha',issue:1,...event,privateText:'never store this'});
  const saved=fs.readFileSync(join(w.core,'history.jsonl'),'utf8'); assert.ok(saved.startsWith('{cut\n')); assert.ok(!saved.includes('never store'));
  const report=await w.read({github:async()=>{throw Error('offline')}}); assert.equal(rows(report).started,1); assert.equal(rows(report).merged,1); assert.equal(rows(report).regressions,1);
  assert.equal(fs.statSync(join(w.core,'history.jsonl')).mode & 0o077,0);
  for(const change of [{kind:'unknown'},{repo:'../invalid'},{issue:-1},{at:'bad'},{head:'bad'},{pr:0}]) assert.throws(()=>recordAutopilotMetric({root:w.core,repo:'owner/alpha',issue:1,kind:'worked',at,...change}),/Invalid Autopilot metric/);
});

test('reader skips symlinks and never follows saved job log/worktree paths',async t=>{
  const w=world(t), other=w.add('b'.repeat(20),'owner/beta');
  w.save(join(other,'history.jsonl'),JSON.stringify({at:Date.parse(at),issue:5,outcome:'merged'}));
  fs.symlinkSync(join(other,'history.jsonl'),join(w.core,'history.jsonl'));
  w.save(join(w.core,'jobs','1.json'),{schema:'pdd.core-job.v1',issue:1,started:Date.parse(at),agent:{log:'/outside/private',result:'/outside/private'},worktree:'/outside/private'});
  const report=await w.read(); assert.equal(rows(report).merged,1); assert.equal(rows(report).started,1);
});

test('missing local state is zero and storage permission errors are exposed',async t=>{
  const w=world(t); const report=await w.read({stateRoot:join(w.root,'absent')}); assert.equal(rows(report).started,0);
  await assert.rejects(()=>w.read({fs:{lstatSync(){throw Object.assign(Error('denied'),{code:'EACCES'})}}}),/denied/);
});

test('native adapter collects paginated comments and checks through a fake process',async t=>{
  const w=world(t), calls=[];
  w.save(join(w.core,'history.jsonl'),JSON.stringify({at:Date.parse(at),issue:1,outcome:'merged',pr:10}));
  const report=await w.read({github:undefined,execFile:async(file,args)=>{
    calls.push([file,args]);
    const endpoint=args.at(-1);
    if(endpoint.includes('/comments')) return {stdout:JSON.stringify([[],[comment()]])};
    if(endpoint.includes('/check-runs')) return {stdout:JSON.stringify([{check_runs:[]},{check_runs:[{head_sha:merge,status:'completed',conclusion:'failure',completed_at:'2026-11-10T14:00:00Z'}]}])};
    return {stdout:JSON.stringify([{head:{sha:head},merged_at:'2026-11-10T13:00:00Z',merge_commit_sha:merge}])};
  }});
  assert.equal(rows(report).validated,1); assert.equal(rows(report).regressions,1);
  assert.equal(calls.length,3);
  for(const [file,args] of calls) {assert.equal(file,'gh');assert.deepEqual(args.slice(0,3),['api','--paginate','--slurp']);assert.ok(!args.includes('--method'));}
});

test('command appends shared Autopilot table/JSON using configured zone and leaves actions alone',async()=>{
  const calls=[]; const ports={repository:async()=>({repo:'owner/repo',root:'/repo'}),now:()=>observedAt,historical:async()=>[],github:async()=>[],selector:async()=>({snapshotId:'s',events:[]}),store:{readEvents:async()=>({events:[]}),appendEvents:async()=>{},exportMetrics:async()=>({})},writeFile:async()=>{},autopilot:async options=>{calls.push(options);return readAutopilotMetrics(options,{stateRoot:'/missing-fixture-state'});}};
  let out='',err=''; assert.equal(await runMetrics({ports,argv:['--json','--timezone','Asia/Kathmandu'],stdout:s=>out+=s,stderr:s=>err+=s}),0,err);
  assert.equal(JSON.parse(out).autopilot.timezone,'Asia/Kathmandu'); assert.equal(calls.length,1);
  out=''; assert.equal(await runMetrics({ports,argv:['--timezone','UTC'],stdout:s=>out+=s}),0); assert.match(out,/Autopilot.*2026-11-10/); assert.match(out,/Tue\s+Week avg/);
  assert.equal(await runMetrics({ports,argv:['export','out.json'],stdout:()=>{}}),0); assert.equal(calls.length,2);
});
