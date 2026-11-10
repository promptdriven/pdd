import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {createHash,randomUUID} from 'node:crypto';
import {auditMerge} from '../src/autopilot-audit.mjs';
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
  w.metricsRoot=root;
  w.read=(observedAt='2026-11-11T10:00:00Z',ports={})=>readAutopilotMetrics({timezone:'UTC',observedAt},{stateRoot:root,github,now:w.now,...ports});
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

test('R4 malformed duplicate Evidence lines cannot be filtered into a pass',async t=>{
  const w=await lifecycle(t);w.issue(17);await w.tick();
  w.build(17,{body:`Runtime: PASS\n${evidence}\nEvidence: runtime=maybe; vectors=pass; formal=pass; tests=pass`});
  await w.tick();assert.equal(rows(await w.read()).runtime,0);
});

test('measurement bookkeeping save errors do not interrupt evidence, validation or merge cleanup',async t=>{
  const w=await lifecycle(t);w.issue(17);await w.tick();w.build(17,{body:`Runtime: PASS\n${evidence}`});
  const failed=new Set(), badFs={...fs,renameSync(from,to){
    if(to === join(w.root,'jobs','17.json')) {
      const job=JSON.parse(fs.readFileSync(from,'utf8'));
      for(const key of ['metricEvidence','metricValidatedHead','autopilotMerge']) if(job[key] && !failed.has(key)) { failed.add(key);throw Error('measurement bookkeeping unavailable'); }
    }
    return fs.renameSync(from,to);
  }};
  await w.tick({fs:badFs});assert.ok(w.job(17,'review'),'measurement save cannot defer checks');
  w.review(17,'PASS');w.suite(17);await w.tick({fs:badFs});
  assert.equal(w.github.merges.length,1);assert.equal(fs.existsSync(join(w.root,'jobs','17.json')),false);
  assert.deepEqual([...failed],['metricEvidence','metricValidatedHead','autopilotMerge']);
});


test('R5 native GitHub status objects bind to the requested merge SHA without a sha property',async t=>{
  const w=fixture(t);recordAutopilotMetric({root:w.core,repo:'owner/repo',issue:1,kind:'merged',at:monday,pr:10,head});
  const report=await w.read(async(repo,path)=>path === 'pulls/10' ? {head:{sha:head},merge_commit_sha:merge} : path.endsWith('/check-runs') ? {check_runs:[]} : [{id:123,state:'failure',context:'ci',created_at:tuesday}]);
  assert.equal(rows(report).regressions,1);
});


for(const mismatch of ['head','branch','base']) test(`round 2: rejected result ${mismatch} never records check passes after cleanup`,async t=>{
  const w=await lifecycle(t);w.issue(17);await w.tick();
  const {pr}=w.build(17,{result:{evidence,...(mismatch === 'head' ? {head:foreign} : {})}});
  if(mismatch === 'branch')pr.branch='unrelated-branch';
  if(mismatch === 'base')pr.base='unrelated-base';
  await w.tick();
  assert.equal(fs.existsSync(join(w.root,'jobs','17.json')),false);
  const report=rows(await w.read());
  for(const key of ['runtime','vectors','formal','merged'])assert.equal(report[key],0,key);
  const history=fs.readFileSync(join(w.root,'history.jsonl'),'utf8');
  assert.equal(history.split('\n').some(line=>{try{return JSON.parse(line).metric?.kind==='evidence';}catch{return false;}}),false);
});

for(const edit of ['duplicate','spacing'])test(`round 2: ${edit} evidence presentation keeps first observation across reporting days`,async t=>{
  const w=await lifecycle(t);w.clock.at=Date.parse(monday);w.issue(17);await w.tick();
  const {pr}=w.build(17,{body:`Runtime: PASS\n${evidence}`});await w.tick();
  for(let i=0;i<8;i++){w.advance(3*3600000);await w.tick();}
  pr.body=edit === 'duplicate' ? `Runtime: PASS\n${evidence}\n${evidence}` : `Runtime: PASS\r\n  ${evidence.replaceAll('; ',';')}  `;
  await w.tick();
  for(const key of ['runtime','vectors','formal']) {
    assert.equal(rows(await w.read())[key],0,key);
    assert.equal(rows(await w.read('2026-11-10T10:00:00Z'))[key],1,key);
  }
});

for(const invalid of ['conflicting','impossible-count'])test(`round 2: ${invalid} complete observations never enter evidence history`,async t=>{
  const w=await lifecycle(t);w.issue(17);await w.tick();
  const bad=invalid === 'conflicting' ? `${evidence}\n${evidence.replace('formal=pass','formal=fail')}` : evidence.replace('2/2','3/2');
  w.build(17,{body:`Runtime: PASS\n${bad}`,result:{evidence:bad}});await w.tick();
  assert.equal(fs.readFileSync(join(w.root,'history.jsonl'),'utf8').includes('"kind":"evidence"'),false);
});

for(const stale of [false,true])test(`round 2: ${stale ? 'stale' : 'exact-head'} merge-comment-only evidence flows through core cleanup and reader`,async t=>{
  const w=await lifecycle(t);w.issue(17);await w.tick();const {pr,head:actual}=w.build(17);await w.tick();
  const sha=stale ? foreign : actual;
  pr.comments.push({id:987,created_at:monday,updated_at:monday,user:{login:'producer'},body:`Autopilot merge check passed for head ${sha}.\n\n${evidence}\n<!-- pdd:autopilot-core:merge:${sha} -->`});
  w.review(17,'PASS');w.suite(17);await w.tick();
  const report=rows(await w.read());
  for(const key of ['runtime','vectors','formal'])assert.equal(report[key],stale ? 0 : 1,key);
  assert.equal(report.merged,1);assert.equal(report.validated,1);
  assert.equal(fs.existsSync(join(w.root,'jobs','17.json')),false);
  if(!stale)assert.ok(pr.comments.some(c=>c.id!==987 && c.body.includes(evidence)),'core merge-note producer retains fixed Evidence');
});

async function mergedWorld(t) {
  const w=await lifecycle(t);w.clock.at=Date.parse(monday);w.issue(17);await w.tick();
  const {pr}=w.build(17);await w.tick();w.review(17,'PASS');w.suite(17);await w.tick();
  w.advance(24*3600000);return {w,pr};
}

for(const match of ['owned','foreign-merge','manual','damaged-record'])test(`round 2: real BAD audit discovery ${match} feeds metrics with green merge CI`,async t=>{
  const {w,pr}=await mergedWorld(t);
  if(match === 'manual') {
    const file=join(w.root,'history.jsonl');fs.writeFileSync(file,fs.readFileSync(file,'utf8').split('\n').filter(line=>!line.includes('"kind":"merged"')).join('\n'));
  }
  const auditRoot=join(w.dir,'audits'),auditStateRoot=join(auditRoot,createHash('sha256').update(w.state.repo.toLowerCase()).digest('hex').slice(0,20));
  const run={repo:w.state.repo,number:17,runId:randomUUID(),runDir:join(w.dir,'run'),commonDir:join(w.dir,'common'),root:w.cwd,baseBranch:'main',agent:'codex',automaticOrigin:{machine:'test'},pr:[{number:pr.number,state:'merged'}]};
  fs.mkdirSync(run.runDir);
  const mergeSha=match === 'foreign-merge' ? foreign : pr.mergeSha;
  const result={verdict:'BAD',kind:'',summary:'Synthetic regression',evidence:'Synthetic recorded audit evidence',revert:false};
  const audit=await auditMerge({run,pr:pr.number},{now:w.now,env:{HOME:join(w.dir,'home')},auditStateRoot,readConfig:async()=>({autopilot:{mode:'auto'}}),agentDefinitions:()=>[{kind:'codex',command:'fake-codex'}],codexLimits:async()=>({state:'healthy'}),
    execFile:async(file,args)=>({code:0,stdout:JSON.stringify(args.some(a=>String(a).includes('/pulls/')) ? {number:pr.number,merged:true,merge_commit_sha:mergeSha,base:{ref:'main',repo:{full_name:w.state.repo}}} : args.some(a=>String(a).includes('/commits/')) ? {sha:mergeSha,parents:[{sha:head}]} : {})}),
    runAuditor:async()=>({code:0,stdout:JSON.stringify({type:'thread.started',thread_id:randomUUID()})+'\n'+JSON.stringify({type:'item.completed',item:{type:'agent_message',text:JSON.stringify(result)}})+'\n'}),
    sendAlert:async()=>({exitCode:0,message:'Alert sent for #17 decision; the webhook confirmed it.'})});
  assert.equal(audit.exitCode,0,audit.message);
  if(match === 'damaged-record') {
    const dir=join(auditStateRoot,'records'),file=join(dir,fs.readdirSync(dir)[0]),record=JSON.parse(fs.readFileSync(file,'utf8'));
    delete record.chat.session;fs.writeFileSync(file,JSON.stringify(record));
  }
  if(match === 'owned')assert.equal(rows(await w.read(undefined,{auditRoot,github:async()=>{throw Error('offline');}})).regressions,1,'local exact-merge BAD discovery survives GitHub outage');
  for(let i=0;i<2;i++)assert.equal(rows(await w.read(undefined,{auditRoot})).regressions,match === 'owned' ? 1 : 0);
  if(match === 'owned')assert.match(fs.readFileSync(join(w.root,'history.jsonl'),'utf8'),/"reason":"bad-audit"/);
});

for(const match of ['owned','foreign-merge','manual'])test(`round 2: base-history revert discovery ${match} persists first day after cleanup`,async t=>{
  const {w,pr}=await mergedWorld(t);
  if(match === 'manual') {
    const file=join(w.root,'history.jsonl');fs.writeFileSync(file,fs.readFileSync(file,'utf8').split('\n').filter(line=>!line.includes('"kind":"merged"')).join('\n'));
  }
  const github=async(repo,path)=>path === `pulls/${pr.number}` ? {head:{sha:pr.head},base:{ref:'main'},merge_commit_sha:pr.mergeSha} : path.startsWith('commits?') ? [{sha:foreign,commit:{message:`Revert synthetic\n\nThis reverts commit ${match === 'foreign-merge' ? merge : pr.mergeSha}.`,committer:{date:monday}}}] : [];
  const ports={github};
  for(let i=0;i<2;i++)assert.equal(rows(await w.read(undefined,ports)).regressions,match === 'owned' ? 1 : 0);
  w.advance(24*3600000);
  assert.equal(rows(await w.read('2026-11-12T10:00:00Z',ports)).regressions,0,'repeat discovery is not a new day');
  if(match === 'owned')assert.match(fs.readFileSync(join(w.root,'history.jsonl'),'utf8'),/"reason":"reverted"/);
});


test('round 2: multiple recorded BAD audits retain earliest discovery regardless of directory order',async t=>{
  const w=fixture(t);recordAutopilotMetric({root:w.core,repo:'owner/repo',issue:1,pr:10,kind:'merged',head,mergeCommit:merge,at:monday});
  const auditRoot=join(w.root,'audits'),hash=createHash('sha256').update('owner/repo').digest('hex').slice(0,20),dir=join(auditRoot,hash,'records');fs.mkdirSync(dir,{recursive:true});
  const files=[];
  for(const at of ['2026-11-11T12:00:00Z',tuesday]) {
    const record={schema:'pdd.audit.v1',repository:'owner/repo',runId:randomUUID(),pr:10,merge,parent:head,at:Date.parse(at),completedAt:Date.parse(at),state:'recorded',chat:{agent:'codex',configDir:null,startedAt:Date.parse(at),session:{id:randomUUID()}},result:{verdict:'BAD',kind:'',summary:'Synthetic',evidence:'Recorded',revert:false}};
    const name=createHash('sha256').update(JSON.stringify([record.runId,10,merge])).digest('hex')+'.json';fs.writeFileSync(join(dir,name),JSON.stringify(record));files.push(name);
  }
  const github=async(repo,path)=>path === 'pulls/10' ? {head:{sha:head},merge_commit_sha:merge} : [];
  const ports={stateRoot:w.root,auditRoot,github,now:()=>Date.parse('2026-11-11T13:00:00Z'),fs:{...fs,readdirSync:path=>path === dir ? files : fs.readdirSync(path)}};
  const report=await readAutopilotMetrics({timezone:'UTC',observedAt:'2026-11-11T10:00:00Z'},ports);
  assert.equal(rows(report).regressions,1,'Tuesday discovery is retained, not later Wednesday result');
});


test('round 2: pending result evidence never transfers to a refreshed head',async t=>{
  const w=await lifecycle(t);w.issue(17);await w.tick();const {head:old}=w.build(17,{result:{evidence}});await w.tick();
  w.baseCommit('base.txt','Updated base');w.review(17,'PASS');w.suite(17);await w.tick();
  const job=JSON.parse(fs.readFileSync(join(w.root,'jobs','17.json'),'utf8'));assert.notEqual(job.head,old);
  await w.tick();
  const observations=fs.readFileSync(join(w.root,'history.jsonl'),'utf8').split('\n').filter(Boolean).map(line=>JSON.parse(line)).filter(row=>row.metric?.kind === 'evidence');
  assert.deepEqual([...new Set(observations.map(row=>row.metric.head))],[old]);
});
