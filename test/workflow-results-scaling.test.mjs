import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { readRunResults } from '../src/workflow-results.mjs';

const sha='a'.repeat(64), since=Date.parse('2026-11-03T10:00:00Z');
function fixture(t) {
 const base=mkdtempSync(join(tmpdir(),'pdd-scaling-')); t.after(()=>rmSync(base,{recursive:true,force:true}));
 const root=join(base,'root'), other=join(base,'other'), state=join(base,'state');
 for(const dir of [root,other,state]) mkdirSync(dir);
 function batch(name, fields={}) { const dir=join(state,'batches',name); mkdirSync(dir,{recursive:true});
  writeFileSync(join(dir,'batch.json'),JSON.stringify({batch:name,root,rows:[{test:'tests/a.json'}],source_sha256:sha,created_at:'2026-11-03T11:00:00Z',intent:'check',...fields}));
  writeFileSync(join(dir,'summary.json'),JSON.stringify({summary_line:name})); }
 return {root,other,state,batch, env:{PDD_STATE_DIR:state,HOME:base}};
}
const rejected=()=>({state:'ineligible'});
test('eligible alternate producer retains original stage and anchor; foreign and wrong-stage rejected',t=>{
 const f=fixture(t),anchor=join(f.root,'anchor'); mkdirSync(anchor);
 f.batch('20261103-110000-aaaa',{root:f.other,association:{runId:'run-1',stage:'pr1'}});
 f.batch('20261103-120000-bbbb',{root:f.other,association:{runId:'wrong',stage:'current'}});
 const calls=[]; const workspace=x=>{calls.push(x); return x.runId==='run-1'?{state:'eligible',runId:'run-1',repo:'example/repo',producerRoot:f.other,tests:x.tests,source_sha256:sha,stage:'pr1',sourceAnchor:{root:anchor,head:'f'.repeat(40)}}:rejected();};
 const captures=[];const [result]=readRunResults({root:f.root,since},{env:f.env,workspace,capture:(root,args)=>{captures.push([root,args]);return {sha256:sha};}});
 assert.equal(calls.length,2);assert.equal(result.batch,'20261103-110000-aaaa');assert.equal(result.source,'current');assert.equal(result.stage,'pr1');assert.equal(result.association.runId,'run-1');assert.equal(result.sourceAnchor.root,anchor);assert.equal(captures[0][0],anchor);
});
test('same worktree ineligible unassociated source stays changed or unknown; bound ineligible never falls back',t=>{
 const f=fixture(t);
 f.batch('20261103-110000-aaaa');
 f.batch('20261103-120000-bbbb',{association:{runId:'wrong',stage:'pr1'}});
 const read=capture=>readRunResults({root:f.root,since},{env:f.env,workspace:rejected,capture})[0];
 assert.equal(read(()=>({sha256:'b'.repeat(64)})).source,'changed');
 assert.equal(read(()=>{throw Error('unavailable');}).source,'unknown');
 assert.equal(read(()=>({sha256:sha})).batch,'20261103-110000-aaaa');
});
test('discard invalid or old timestamps and unsupported intent before workspace admission',t=>{
 const f=fixture(t),calls=[];
 f.batch('20261103-090000-aaaa',{created_at:'2026-11-03T09:00:00Z'});
 f.batch('20261103-090001-bbbb',{created_at:'not-a-date'});
 f.batch('20261103-090002-cccc',{intent:'other'});
 f.batch('20261103-090003-dddd',{root:f.other,created_at:'2026-11-03T09:00:00Z'});
 const results=readRunResults({root:f.root,since},{env:f.env,workspace:x=>{calls.push(x);return rejected();}});
 assert.deepEqual(results,[]);assert.equal(calls.length,0,'irrelevant batch records must not reach costly workspace read');
});
test('skip an uncoercible saved date before admission and retain a later valid result',t=>{
 const f=fixture(t),calls=[];
 f.batch('20261103-110000-aaaa',{root:f.other,created_at:{toString:null}});
 f.batch('20261103-120000-bbbb',{created_at:'2026-11-03T12:00:00Z'});
 const results=readRunResults({root:f.root,since},{env:f.env,workspace:x=>{calls.push(x);return rejected();},capture:()=>({sha256:sha})});
 assert.equal(results.length,1);
 assert.equal(results[0].batch,'20261103-120000-bbbb');
 assert.equal(results[0].source,'current');
 assert.equal(results[0].summary,'20261103-120000-bbbb');
 assert.equal(calls.length,1,'malformed dates must not reach workspace admission');
 assert.equal(calls[0].producerRoot,f.root);
});
