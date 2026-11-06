import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtemp, mkdir, writeFile, readFile, rm} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join, resolve} from 'node:path';
import {execFileSync} from 'node:child_process';

// Synthetic fixture: one ready issue, one trusted PASS, one passing CI run,
// and one merged code PR. These expectations are fixed before invocation.
test('native CLI exports current GitHub facts for an offline machine without inflating comments', async t => {
  const dir=await mkdtemp(join(tmpdir(),'metrics-snapshot-')); t.after(()=>rm(dir,{recursive:true,force:true}));
  const a=join(dir,'a'),b=join(dir,'b'),c=join(dir,'c'),bin=join(dir,'bin'); await Promise.all([mkdir(a),mkdir(b),mkdir(c),mkdir(bin)]);
  for(const root of [a,b,c]) {execFileSync('git',['init','-q',root]); execFileSync('git',['-C',root,'remote','add','origin','https://github.com/example/demo.git']);}
  const head='a'.repeat(40), next='b'.repeat(40), at='2026-10-30T00:00:00Z';
  const base={schema:'pdd.metrics.event.v1',repo:'example/demo',issue:1,at,observedAt:at,source:'fixture'};
  await writeFile(join(dir,'facts.json'),JSON.stringify([{...base,id:'selection-1',type:'selection',data:{snapshotId:'group1',inScope:true,state:'ready',reasons:[]}},{...base,id:'ready-1',type:'milestone',data:{stage:'implementation-ready',pr:42,head}},{...base,id:'prompt-1',type:'milestone',data:{stage:'prompt-pr',pr:41}}]));
  const fixture=`#!/usr/bin/env node\nconst a=process.argv.join(' '),head=process.env.GH_HEAD||'${head}'; if(process.env.GH_OFF)process.exit(1); if(a.includes('/collaborators/')) console.log(JSON.stringify({permission:process.env.GH_PERMISSION||'read'})); else if(a.includes('/pulls/41')) console.log(JSON.stringify({head:{sha:'c'.repeat(40)}})); else if(a.includes('/issues/41/comments?')) console.log(''); else if(a.includes('/pulls/42/files?')) console.log('src/example.mjs'); else if(a.includes('/pulls/42')) console.log(JSON.stringify({merged_at:'2026-11-01T00:00:00Z',html_url:'https://github.com/example/demo/pull/42',head:{sha:head}})); else if(a.includes('/issues/42/comments?')) console.log(JSON.stringify({id:99,author_association:process.env.GH_ASSOC||'OWNER',user:{login:'checker'},body:String.fromCharCode(96,96,96)+'json\\n'+JSON.stringify({verdict:'PASS',head:'${head}',risk:1,family:'codex',session:'verify1',checker_mode:'different-family',evidence:'Ran full suite successfully'})+'\\n'+String.fromCharCode(96,96,96),html_url:'https://github.com/example/demo/pull/42#issuecomment-99',created_at:'2026-10-31T00:00:00Z'})); else if(a.includes('/check-runs?')) console.log(JSON.stringify({check_runs:[{name:'full suite',head_sha:head,status:'completed',conclusion:'success',html_url:'https://github.com/example/demo/actions/runs/7'}]})); else process.exit(1);\n`;
  await writeFile(join(bin,'gh'),fixture,{mode:0o755});
  const cli=resolve('bin/pdd.mjs'), env={...process.env,PATH:`${bin}:${process.env.PATH}`};
  const run=(root,args,extra={})=>execFileSync(process.execPath,[cli,'metrics',...args],{cwd:root,env:{...env,...extra},encoding:'utf8'});
  run(a,['record',join(dir,'facts.json')]);
  const live=JSON.parse(run(a,['--snapshot','group1','--json']));
  assert.equal(live.issues[0].candidate.data.pr,42); assert.equal(live.issues[0].candidate.data.head,head); assert.equal(live.stages.validated.numerator,1); assert.equal(live.stages.delivered.numerator,1);
  assert.equal(live.issues[0].checks.length,1); assert.equal(live.issues[0].ci.filter(e=>e.data.status==='passed').length,1);
  run(a,['--snapshot','group1','--json']); run(a,['export',join(dir,'bundle.json')]); run(b,['import',join(dir,'bundle.json')]); run(b,['import',join(dir,'bundle.json')]);
  const offline=JSON.parse(run(b,['--snapshot','group1','--json'],{GH_OFF:'1'}));
  assert.equal(offline.issues[0].candidate.data.pr,42); assert.equal(offline.stages.validated.numerator,1); assert.equal(offline.stages.delivered.numerator,1); assert.equal(offline.issues[0].checks.length,1);
  assert.equal(offline.issues[0].ci.filter(e=>e.data.status==='passed').length,1); assert.equal(offline.issues[0].checks[0].data.evidence,live.issues[0].checks[0].data.evidence);
  const changed=JSON.parse(run(a,['--snapshot','group1','--json'],{GH_HEAD:next})); assert.equal(changed.issues[0].validated,'unknown');
  run(a,['export',join(dir,'new.json')],{GH_HEAD:next}); run(b,['import',join(dir,'new.json')]);
  const later=JSON.parse(run(b,['--snapshot','group1','--json'],{GH_OFF:'1'})); assert.equal(later.issues[0].validated,'unknown'); assert.equal(later.issues[0].candidate.data.head,next);
  assert.ok(!(await readFile(join(dir,'bundle.json'),'utf8')).includes('Ran full suite successfully'));
  run(c,['record',join(dir,'facts.json')]);
  const untrusted=JSON.parse(run(c,['--snapshot','group1','--json'],{GH_ASSOC:'MEMBER',GH_PERMISSION:'read'})); assert.equal(untrusted.issues[0].validated,'unknown');
  const trusted=JSON.parse(run(c,['--snapshot','group1','--json'],{GH_ASSOC:'MEMBER',GH_PERMISSION:'write'})); assert.equal(trusted.issues[0].validated,'yes'); assert.equal(trusted.conflicts.length,0);
});

test('snapshot headers and members import atomically and retain empty observations', async t => {
  const dir=await mkdtemp(join(tmpdir(),'metrics-headers-')); t.after(()=>rm(dir,{recursive:true,force:true}));
  const a=join(dir,'a'),b=join(dir,'b'),bin=join(dir,'bin'); await Promise.all([mkdir(a),mkdir(b),mkdir(bin)]);
  for(const root of [a,b]) {execFileSync('git',['init','-q',root]); execFileSync('git',['-C',root,'remote','add','origin','https://github.com/example/demo.git']);}
  const at='2026-11-01T00:00:00Z', id='snapshot:11111111-1111-4111-8111-111111111111', empty='snapshot:22222222-2222-4222-8222-222222222222';
  const selection={schema:'pdd.metrics.event.v1',id:'selection',repo:'example/demo',issue:1,type:'selection',at,observedAt:at,source:'fixture',data:{snapshotId:id,inScope:false,state:'excluded',reasons:['outside-activation-scope']}};
  const snapshot={snapshotId:id,repo:'example/demo',observedAt:at,source:'fixture',events:[selection]};
  const emptySnapshot={snapshotId:empty,repo:'example/demo',observedAt:'2026-11-02T00:00:00Z',source:'fixture',events:[]};
  const store=await import('../src/metrics-store.mjs');
  const metadata={repo:'example/demo',timezone:'UTC',exportedAt:'2026-11-03T00:00:00Z',cliVersion:'1'};
  const bundle=await store.exportMetrics({root:a,metadata}); bundle.snapshots=[snapshot,emptySnapshot];
  const bad=structuredClone(bundle); bad.snapshots[1].events=[{...selection,data:{...selection.data,snapshotId:empty}}];
  await assert.rejects(store.importMetrics({root:b,bundle:bad})); assert.deepEqual((await store.readEvents({root:b})).snapshots,[]);
  await store.importMetrics({root:b,bundle:{...bundle,snapshots:[snapshot]}});
  await writeFile(join(bin,'gh'),"#!/bin/sh\nprintf '%s\\n' '{\"number\":1}'\n",{mode:0o755});
  const run=(args)=>execFileSync(process.execPath,[resolve('bin/pdd.mjs'),'metrics',...args],{cwd:b,env:{...process.env,PATH:`${bin}:${process.env.PATH}`},encoding:'utf8'});
  const observed=JSON.parse(run(['--json'])); assert.equal(observed.queue.unknown.count,1); assert.equal(observed.selectorObservation.snapshotId,id); assert.equal(observed.selectorObservation.queue.excluded.count,1); assert.deepEqual(observed.selectorObservation.queue.excluded.issues[0].reasons,['outside-activation-scope']);
  await store.importMetrics({root:b,bundle}); await store.importMetrics({root:b,bundle});
  const saved=await store.readEvents({root:b}); assert.equal(saved.snapshots.length,2); assert.equal(saved.events.filter(e=>e.id==='selection').length,1);
  const exported=await store.exportMetrics({root:b,metadata}); assert.equal(exported.snapshots.length,2); assert.ok(exported.snapshots.some(s=>s.snapshotId===empty && s.events.length===0));
  const current=JSON.parse(run(['--json'])); assert.equal(current.queue.unknown.count,1); assert.equal(current.selectorObservation.snapshotId,empty); assert.equal(current.selectorObservation.queue.excluded.count,0);
  const cohort=JSON.parse(run(['--snapshot',id,'--json'])); assert.equal(cohort.queue.excluded.count,1);
});

test('checker acceptance refinement preserves the comment and contradictory claims remain visible', async () => {
  const {calculateMetrics}=await import('../src/metrics-model.mjs');
  const at='2026-11-01T00:00:00Z', later='2026-11-02T00:00:00Z', head='a'.repeat(40);
  const base={schema:'pdd.metrics.event.v1',repo:'example/demo',issue:1,at,observedAt:at,source:'github:example/demo'};
  const selection={...base,id:'selection',type:'selection',data:{snapshotId:'s',inScope:true,state:'ready',reasons:[]}};
  const ready={...base,id:'ready',type:'milestone',data:{stage:'implementation-ready',pr:42,head}};
  const check={...base,id:'check:99:1',type:'check',data:{pr:42,head,verdict:'PASS',reviewer:'codex:verify',evidence:'https://github.com/example/demo/pull/42#issuecomment-99',acceptance:'unknown'}};
  const args={repo:'example/demo',scope:{kind:'cohort',snapshotId:'s'},timezone:'UTC',observedAt:later,sources:[]};
  const report=calculateMetrics({...args,events:[selection,ready,check,{...check,observedAt:later,data:{...check.data,acceptance:'accepted'}}]});
  assert.equal(report.issues[0].validated,'yes'); assert.equal(report.issues[0].checks.length,1); assert.equal(report.conflicts.length,0);
  const contradictory=calculateMetrics({...args,events:[selection,ready,check,{...check,observedAt:later,data:{...check.data,verdict:'FAIL'}}]});
  assert.equal(contradictory.issues[0].validated,'unknown'); assert.equal(contradictory.conflicts.length,1);
  const historical=calculateMetrics({...args,observedAt:at,events:[selection,ready,check,{...check,observedAt:later,data:{...check.data,acceptance:'accepted'}}]});
  assert.equal(historical.issues[0].validated,'unknown');
});
