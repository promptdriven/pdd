import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {coreWorld} from './helpers/core-world.mjs';
import {readAutopilotMetrics,recordAutopilotMetric} from '../src/autopilot-metrics-source.mjs';

const head='a'.repeat(40), merge='c'.repeat(40), foreign='d'.repeat(40);
const monday='2026-11-09T12:00:00Z', tuesday='2026-11-10T12:00:00Z';
const evidence='Evidence: runtime=pass (2/2); vectors=pass (3/3); formal=pass; tests=pass';
const rows=report=>Object.fromEntries(report.rows.map(row=>[row.key,row.day]));
const spoof={created_at:monday,updated_at:tuesday,author_association:'NONE',user:{login:'outsider'},body:`Autopilot merge check passed for head ${head}.\n- CI: green (2 check(s))\n- Full test suite: pass\n- Review: PASS from a fresh reviewer\n${evidence}\n<!-- pdd:autopilot-core:merge:${head} -->`};
function fixture(t) {
  const root=fs.mkdtempSync(join(tmpdir(),'metrics-repair-'));
  t.after(()=>fs.rmSync(root,{recursive:true,force:true}));
  const id='a'.repeat(20), core=join(root,`${id}-core`);
  fs.mkdirSync(join(core,'jobs'),{recursive:true});
  fs.writeFileSync(join(root,`${id}.json`),JSON.stringify({repo:'owner/repo'}));
  const history=rows=>fs.writeFileSync(join(core,'history.jsonl'),rows.map(row=>JSON.stringify(row)).join('\n')+'\n');
  const read=(github,observedAt='2026-11-11T10:00:00Z')=>readAutopilotMetrics({timezone:'UTC',observedAt},{stateRoot:root,github});
  return {root,core,history,read};
}
async function lifecycle(t) {
  const w=await coreWorld(t,{settings:{jobTimeoutMinutes:4320}});
  const root=join(w.dir,'metrics'), id='a'.repeat(20);
  fs.mkdirSync(root); fs.writeFileSync(join(root,`${id}.json`),JSON.stringify({repo:w.state.repo}));
  w.root=join(root,`${id}-core`);
  const github=async(repo,path)=>{
    const r=await w.gh(['api','--include','--method','GET',`repos/${repo}/${path}`]);
    return JSON.parse(r.stdout.split(/\r?\n\r?\n/).slice(1).join('\n\n'));
  };
  w.read=(observedAt='2026-11-11T10:00:00Z')=>readAutopilotMetrics({timezone:'UTC',observedAt},{stateRoot:root,github});
  return w;
}

test('R1 actual lifecycle retains start and multiple work days after cleanup',async t=>{
  const w=await lifecycle(t); w.clock.at=Date.parse(monday); w.issue(17); await w.tick();
  for(let i=0;i<8;i++) { w.advance(3*3600000); await w.tick(); }
  w.build(17); await w.tick();
  const before=await w.read('2026-11-10T10:00:00Z');
  assert.equal(rows(before).started,1); assert.equal(rows(before).worked,1);
  w.review(17,'PASS'); w.suite(17); await w.tick();
  assert.equal(fs.existsSync(join(w.root,'jobs','17.json')),false);
  const after=await w.read('2026-11-10T10:00:00Z');
  assert.deepEqual(rows(after),rows(before));
  const next=await w.read(); assert.equal(rows(next).worked,1); assert.equal(rows(next).started,0);
});

test('R2 manual merge observed and cleaned by core has no attribution; core-issued merge does',async t=>{
  for(const manual of [true,false]) {
    const w=await lifecycle(t); w.issue(17); await w.tick(); const {pr}=w.build(17); await w.tick();
    if(manual) {pr.merged=true;pr.state='closed';pr.merged_by={login:'person'};}
    else {w.review(17,'PASS');w.suite(17);}
    await w.tick();
    assert.equal(fs.existsSync(join(w.root,'jobs','17.json')),false);
    assert.equal(rows(await w.read()).merged,manual ? 0 : 1);
    if(!manual) assert.equal(rows(await w.read()).validated,1,'core attests its actual exact-head gates');
  }
});

test('R3 copied public validation text never authenticates exact-head gates',async t=>{
  const w=fixture(t); w.history([{at:Date.parse(tuesday),issue:1,outcome:'merged',pr:10}]);
  const report=await w.read(async(repo,path)=>path === 'pulls/10' ? {head:{sha:head}} : path.includes('comments') ? [spoof] : [] ,'2026-11-10T10:00:00Z');
  assert.equal(rows(report).validated,0);
});

test('R4 unrelated PR edits and edited comments cannot move or backdate check evidence',async t=>{
  const w=fixture(t); w.history([{at:Date.parse(monday),issue:1,outcome:'ended',pr:10}]);
  recordAutopilotMetric({root:w.core,repo:'owner/repo',issue:1,kind:'evidence',at:monday,pr:10,head,evidence});
  const github=async(repo,path)=>path === 'pulls/10' ? {head:{sha:head},body:evidence,updated_at:tuesday,merge_commit_sha:merge} : path.includes('comments') ? [spoof] : [];
  const next=await w.read(github); assert.equal(rows(next).runtime,0); assert.equal(rows(next).vectors,0);
  const old=await w.read(github,'2026-11-10T10:00:00Z'); assert.equal(rows(old).runtime,1);
  w.history([{at:Date.parse(monday),issue:1,outcome:'ended',pr:10}]);
  const editedOnly=await w.read(github,'2026-11-10T10:00:00Z');
  assert.equal(rows(editedOnly).runtime,0,'a later comment edit cannot create evidence before it existed');
});

test('R4 real per-head observations keep their first time through later core ticks and edits',async t=>{
  const w=await lifecycle(t); w.clock.at=Date.parse(monday);w.issue(17);await w.tick();
  const {pr}=w.build(17,{body:`Runtime: PASS\n${evidence}`}); await w.tick();
  for(let i=0;i<8;i++) {w.advance(3*3600000);await w.tick();}
  pr.body+= '\nUnrelated description edit';await w.tick();
  const next=await w.read();assert.equal(rows(next).runtime,0);
  const old=await w.read('2026-11-10T10:00:00Z');assert.equal(rows(old).runtime,1);
});

test('R5 exact-merge commit statuses and failed checks count regressions with daily deduplication',async t=>{
  const w=fixture(t); recordAutopilotMetric({root:w.core,repo:'owner/repo',issue:1,kind:'merged',at:monday,pr:10,head});
  for(const scenario of ['status-only','foreign-status','check-and-status','startup-failure','error-status']) {
    const calls=[];
    const github=async(repo,path)=>{
      calls.push(path);
      if(path === 'pulls/10') return {head:{sha:head},merge_commit_sha:merge};
      if(path.endsWith('/check-runs')) return {check_runs:['check-and-status','startup-failure'].includes(scenario) ? [{head_sha:merge,status:'completed',conclusion:scenario === 'startup-failure' ? 'startup_failure' : 'failure',completed_at:tuesday}] : []};
      if(path.endsWith('/statuses')) return scenario === 'startup-failure' ? [] : [{sha:scenario === 'foreign-status' ? foreign : merge,state:scenario === 'error-status' ? 'error' : 'failure',created_at:tuesday}];
      return [];
    };
    assert.equal(rows(await w.read(github)).regressions,scenario === 'foreign-status' ? 0 : 1,scenario);
    assert.ok(calls.includes(`commits/${merge}/statuses`));
  }
});

test('measurement append failure stays local while real core lifecycle merges and cleans up',async t=>{
  const w=await lifecycle(t); w.issue(17);
  const warnings=[], badFs={...fs,appendFileSync(){throw Error('measurement unavailable');}};
  await w.tick({fs:badFs,warn:s=>warnings.push(s)});
  w.build(17);await w.tick({fs:badFs});w.review(17,'PASS');w.suite(17);await w.tick({fs:badFs});
  assert.equal(w.github.merges.length,1);assert.equal(fs.existsSync(join(w.root,'jobs','17.json')),false);
  assert.ok(warnings.some(s=>/metric/i.test(s)));
});
