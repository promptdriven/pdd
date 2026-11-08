import './helpers/test-home.mjs';
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, rm, readFile, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { appendEvents, readEvents, exportMetrics, importMetrics } from '../src/metrics-store.mjs';

const at = '2026-11-05T12:00:00.000Z';
const event = (id, source='machine-a') => ({schema:'pdd.metrics.event.v1', id, repo:'owner/repo', issue:1, type:'milestone', at, observedAt:at, source, data:{stage:'implementation-ready',pr:2,head:'abc'}});
async function repo(t) { const root=await mkdtemp(join(tmpdir(),'metrics-test-')); execFileSync('git',['init','-q',root]); t.after(()=>rm(root,{recursive:true,force:true})); return root; }

test('concurrent transactions retain over 200 events and conflicts, independent of status', async t => {
  const root=await repo(t); const events=Array.from({length:230},(_,i)=>event(`e${i}`));
  await Promise.all(events.map(e=>appendEvents({root,events:[e]})));
  const status=join(root,'.git','pdd','status.json'); await writeFile(status,'{"done":"first"}'); await writeFile(status,'{"done":"second"}');
  await appendEvents({root,events:[events[0],{...events[0],data:{stage:'wait',reason:'review'}}]});
  const read=await readEvents({root}); assert.equal(read.events.length,231); assert.equal(read.events.filter(e=>e.id==='e0').length,2);
});

test('export import deduplicates, keeps issue observations from multiple sources and rejects malformed bundles atomically',async t=>{
  const a=await repo(t), b=await repo(t); await appendEvents({root:a,events:[event('one'),event('two','machine-b')]});
  const metadata={repo:'owner/repo',timezone:'UTC',exportedAt:at,cliVersion:'0.1.18'};
  const bundle=await exportMetrics({root:a,metadata}); const second=await exportMetrics({root:a,metadata}); assert.equal(bundle.source,second.source); assert.equal(bundle.captureStartedAt,second.captureStartedAt);
  await importMetrics({root:b,bundle}); await importMetrics({root:b,bundle}); assert.equal((await readEvents({root:b})).events.length,2);
  const before=JSON.stringify(await readEvents({root:b}));
  for (const altered of [{...bundle,definitionVersion:'2'}, {...bundle,timezone:'bad/time'}, {...bundle,events:[event('three'),{...event('bad'),data:{password:'secret'}}]}, {...bundle,events:[event('three'),{...event('bad'),data:{evidence:'https://user:secret@example.com/'}}]}]) {
    await assert.rejects(importMetrics({root:b,bundle:altered})); assert.equal(JSON.stringify(await readEvents({root:b})),before);
  }
});

test('linked worktree shares ledger and retains public evidence links',async t=>{
  const root=await repo(t); execFileSync('git',['-C',root,'-c','user.name=test','-c','user.email=test@example.com','commit','--allow-empty','-qm','initial']);
  const worktree=join(root,'linked'); execFileSync('git',['-C',root,'worktree','add','-q','-b','other',worktree]);
  await appendEvents({root:worktree,events:[{...event('link'),type:'delivery',data:{pr:2,head:'abc',explicit:true,evidence:'https://github.com/owner/repo/pull/2'}}]});
  assert.equal((await readEvents({root})).events[0].data.evidence,'https://github.com/owner/repo/pull/2');
});

test('repeat observations retain earliest observation time without hiding changed facts',async t=>{
  const root=await repo(t), first=event('repeat');
  await appendEvents({root,events:[{...first,observedAt:'2026-11-06T12:00:00.000Z'},first,{...first,data:{stage:'wait'}}]});
  const {events}=await readEvents({root}); assert.equal(events.length,2); assert.equal(events.find(e=>e.data.stage==='implementation-ready').observedAt,at);
});

test('re-export retains source metadata through multiple machines and public comment anchors', async t => {
  const a=await repo(t), b=await repo(t), c=await repo(t);
  const metadata={repo:'owner/repo',timezone:'UTC',exportedAt:at,cliVersion:'0.1.18'};
  await appendEvents({root:a,events:[{...event('comment'),type:'check',data:{verdict:'PASS',evidence:'https://github.com/owner/repo/pull/2#issuecomment-123'}}]});
  const first=await exportMetrics({root:a,metadata});
  await importMetrics({root:b,bundle:first});
  const second=await exportMetrics({root:b,metadata});
  await importMetrics({root:c,bundle:second});
  assert.ok((await readEvents({root:c})).sources.some(s=>s.source===first.source && s.captureStartedAt===first.captureStartedAt));
  await assert.rejects(appendEvents({root:c,events:[{...event('/home/user/private'),data:{stage:'wait'}}]}));
});

test('refuses private prose, paths and private evidence addresses', async t => {
  const root=await repo(t);
  for (const altered of [
    {...event('private'),data:{stage:'wait',reason:'My password is in the shared chat'}},
    {...event('private'),data:{stage:'wait',reasons:['please read this confidential chat']}},
    {...event('private'),type:'check',data:{verdict:'PASS',evidence:'https://127.0.0.1/private'}},
    {...event('/home/worker/secret'),data:{stage:'wait'}}
  ]) await assert.rejects(appendEvents({root,events:[altered]}));
});

 test('rejects malformed top-level source before import and permits re-export', async t => {
  const a=await repo(t), b=await repo(t);
  const metadata={repo:'owner/repo',timezone:'UTC',exportedAt:at,cliVersion:'0.1.18'};
  const bundle=await exportMetrics({root:a,metadata});
  await assert.rejects(importMetrics({root:b,bundle:{...bundle,source:'private prose can pass'}}));
  await importMetrics({root:b,bundle});
  const exported=await exportMetrics({root:b,metadata});
  assert.ok(exported.sources.some(s=>s.source===bundle.source));
 });

test('export scope survives multiple hops, legacy scope stays unknown, and invalid scope is atomic', async t => {
  const a=await repo(t), b=await repo(t), c=await repo(t), legacyRoot=await repo(t);
  const metadata={repo:'owner/repo',timezone:'UTC',exportedAt:at,cliVersion:'0.1.18'};
  await appendEvents({root:a,events:[event('scoped')]});
  const first=await exportMetrics({root:a,metadata});
  assert.equal(first.scope,'all-retained-repo-events');
  const legacy=await exportMetrics({root:legacyRoot,metadata});
  delete legacy.scope;
  await importMetrics({root:b,bundle:first});
  await importMetrics({root:b,bundle:legacy});
  const second=await exportMetrics({root:b,metadata});
  await importMetrics({root:c,bundle:second});
  const third=await exportMetrics({root:c,metadata});
  assert.equal(third.sources.find(s=>s.source===first.source).scope,'all-retained-repo-events');
  assert.equal(third.sources.find(s=>s.source===second.source).scope,'all-retained-repo-events');
  assert.equal(Object.hasOwn(third.sources.find(s=>s.source===legacy.source),'scope'),false);
  const before=await readEvents({root:c});
  for (const bad of [{...first,scope:'cohort'}, {...first,scope:null}, {...first,sources:[{...second.sources[0],scope:'/private/path'}]}]) {
    await assert.rejects(importMetrics({root:c,bundle:bad}));
    assert.deepEqual(await readEvents({root:c}),before);
  }
});
