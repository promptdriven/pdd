import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {execFileSync} from 'node:child_process';
import {chmodSync,linkSync,mkdirSync,mkdtempSync,readFileSync,realpathSync,rmSync,symlinkSync,writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
const hash=value=>createHash('sha256').update(value).digest('hex');
async function fixture(t) {
  const api=await import('../src/workflow-replay.mjs');
  const base=realpathSync(mkdtempSync(join(tmpdir(),'pdd-replay-')));t.after(()=>rmSync(base,{recursive:true,force:true}));
  const root=join(base,'repo'),runDir=join(base,'run');mkdirSync(root);mkdirSync(runDir);mkdirSync(join(root,'tests'));
  const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8'}).trim();git('init','-q');
  const checks=[{criterion_id:'AC1',target:'result',path:'/total',op:'equals',value:3},{criterion_id:'AC2',target:'calls',path:'/save',op:'equals',value:0}];
  const vector={schema_version:'prompt-runtime.program-scenario.v1',steps:[{step_id:'sum',entry_path:'prompts/add.prompt.md',operation:'add',checks}]};
  const vectorPath=join(root,'tests/add.json');writeFileSync(vectorPath,JSON.stringify(vector)+'\n');writeFileSync(join(root,'code.mjs'),'export const add=(a,b)=>a+b;\n');
  git('add','.');git('-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','fixture');
  const run={root,runDir,runId:'synthetic-run',replayBaseline:api.pinReplayVectors(root,['tests/add.json'])};
  const rows=checks.map((check,check_index)=>({vector:'tests/add.json',step_id:'sum',check_index,entry_path:'prompts/add.prompt.md',operation:'add',criterion_id:check.criterion_id,target:check.target,path:check.path,op:check.op,outcome:'pass'}));
  const manifest={schema_version:'pdd.replay-evidence.v1',run_id:run.runId,source:{kind:'git-content-v1',sha256:api.sourceFingerprint(root)},vectors:[{path:'tests/add.json',sha256:hash(readFileSync(vectorPath))}],checks:rows,
    operations:[{vector:'tests/add.json',step_id:'sum',entry_path:'prompts/add.prompt.md',operation:'add',executed:true,outcome:'returned',boundary:{kind:'function',name:'add'},command:'node test/add.vectors.test.mjs',exit_code:0}],
    counts:{total:2,pass:2,fail:0,blocked:0,not_replayed:0},mutation:{kind:'semantic',description:'Change addition to subtraction',command:'node test/add.vectors.test.mjs --mutant',exit_code:1,outcome:'assertion_failure',failed_checks:[{vector:'tests/add.json',step_id:'sum',check_index:0}]},
    formal:{result:'not_applicable',scope:'Public addition wiring',reason:'No additional formal rule approved',control_outcome:'not_run'}};
  const save=()=>writeFileSync(join(runDir,'replay-evidence.json'),JSON.stringify(manifest));
  return {api,base,root,runDir,run,manifest,save,vectorPath,git};
}

test('2530: valid agent record passes with exact counts and honest trust boundary',async t=>{
  const f=await fixture(t);f.save();const r=f.api.readReplayEvidence(f.run);
  assert.equal(r.outcome,'pass',r.reason);assert.deepEqual(r.counts,f.manifest.counts);
  assert.equal(r.operations.executed,1);assert.equal(r.formal.result,'not_applicable');
  const report=f.api.formatReplayEvidence(r);assert.match(report,/^Code replay: PASS/);assert.match(report,/does not independently prove/);assert.match(report,/2 passed/);
});

test('2530: genuine assertion and formal failures are explicit outcomes',async t=>{
  for(const kind of ['assertion','formal']){
    const f=await fixture(t);
    if(kind==='assertion'){f.manifest.checks[0].outcome='fail';f.manifest.counts.pass=1;f.manifest.counts.fail=1;}
    else f.manifest.formal={result:'failed',scope:'Addition',reason:'Counterexample',control_outcome:'assertion_failure',counterexample:{a:1,b:2}};
    f.save();const r=f.api.readReplayEvidence(f.run);assert.equal(r.outcome,'fail',r.reason);
    assert.match(f.api.formatReplayEvidence(r),/✗|FAIL/);
  }
});

test('2530: missing, malformed, oversized, foreign and unsupported manifests cannot pass',async t=>{
  for(const kind of ['missing','malformed','oversized','foreign','version','symlink']){
    const f=await fixture(t),path=join(f.runDir,'replay-evidence.json');
    if(kind==='malformed')writeFileSync(path,'{');
    else if(kind==='oversized')writeFileSync(path,' '.repeat(2*1024*1024+1));
    else if(kind==='symlink'){writeFileSync(join(f.base,'foreign.json'),JSON.stringify(f.manifest));symlinkSync(join(f.base,'foreign.json'),path);}
    else if(kind!=='missing'){if(kind==='foreign')f.manifest.run_id='another-run';else f.manifest.schema_version='pdd.replay-evidence.v9';f.save();}
    const r=f.api.readReplayEvidence(f.run);assert.equal(r.outcome,'blocked',kind);assert.ok(r.reason);
  }
});

test('2530: absent, empty, duplicate, unmapped and unknown check rows cannot pass',async t=>{
  for(const kind of ['empty','missing','duplicate','unmapped','unknown','identity','counts']){
    const f=await fixture(t);
    if(kind==='empty'){f.manifest.checks=[];f.manifest.counts={total:2,pass:0,fail:0,blocked:0,not_replayed:2};}
    if(kind==='missing'){f.manifest.checks.pop();f.manifest.counts.pass=1;f.manifest.counts.not_replayed=1;}
    if(kind==='duplicate')f.manifest.checks[1]={...f.manifest.checks[0]};
    if(kind==='unknown')f.manifest.checks[0].check_index=900;
    if(kind==='identity')f.manifest.checks[0].operation='another';
    if(kind==='unmapped'){f.manifest.checks[1].outcome='not_replayed';f.manifest.checks[1].reason='No calls mapping';f.manifest.counts.pass=1;f.manifest.counts.not_replayed=1;}
    if(kind==='counts')f.manifest.counts.pass=99;
    f.save();const r=f.api.readReplayEvidence(f.run);assert.notEqual(r.outcome,'pass',kind);
  }
});

test('2530: unexecuted or missing public operations invalidate supplied pass rows',async t=>{
  for(const kind of ['unexecuted','missing','crash']){
    const f=await fixture(t);
    if(kind==='missing')f.manifest.operations=[];
    else if(kind==='unexecuted')Object.assign(f.manifest.operations[0],{executed:false,outcome:'not_run',exit_code:null});
    else Object.assign(f.manifest.operations[0],{outcome:'crash',exit_code:1});
    f.manifest.counts={total:2,pass:0,fail:0,blocked:0,not_replayed:2};
    f.save();const r=f.api.readReplayEvidence(f.run);assert.equal(r.outcome,'not_replayed',r.reason);
  }
});

test('2530: unreadable or unsafe vectors remain unproved with advisory warnings',async t=>{
  for(const kind of ['unreadable','hardlink']){
    const f=await fixture(t);
    if(kind==='unreadable')chmodSync(f.vectorPath,0);
    if(kind==='hardlink')linkSync(f.vectorPath,join(f.base,'linked.json'));
    f.manifest.source.sha256=f.api.sourceFingerprint(f.root);f.save();
    const r=f.api.readReplayEvidence(f.run);assert.equal(r.outcome,'not_replayed',kind);assert.ok(r.warnings.length);
    if(kind==='unreadable')chmodSync(f.vectorPath,0o600);
  }
});

test('2870: corrected saved values and check paths replay with warnings and an unchanged anchor',async t=>{
  const f=await fixture(t),anchor=structuredClone(f.run.replayBaseline);
  const doc=JSON.parse(readFileSync(f.vectorPath));
  doc.steps[0].checks[0].value=999;doc.steps[0].checks[1].path='/resources/store-save';
  writeFileSync(f.vectorPath,JSON.stringify(doc));
  f.manifest.vectors[0].sha256=hash(readFileSync(f.vectorPath));
  f.manifest.checks[1].path='/resources/store-save';
  f.manifest.source.sha256=f.api.sourceFingerprint(f.root);f.save();
  const result=f.api.readReplayEvidence(f.run);
  assert.equal(result.outcome,'pass',result.reason);
  assert.deepEqual(f.run.replayBaseline,anchor);
  const report=f.api.formatReplayEvidence(result);
  assert.match(report,/warning:.*saved test/i);
  assert.match(report,/\/steps\/0\/checks\/0\/value.*3.*999/);
  assert.match(report,/\/steps\/0\/checks\/1\/path.*save.*resources/);
  assert.match(report,/Current vector: tests\/add\.json/);assert.doesNotMatch(report,/Original vector:/);
});

test('2870: every changed value is shown even without a manifest, including false, zero, null and missing',async t=>{
  const f=await fixture(t),doc=JSON.parse(readFileSync(f.vectorPath));
  // Synthetic requirements: all 20 edits must be visible, without a display cap.
  doc.initial_world=Object.fromEntries(Array.from({length:20},(_,i)=>[`item${i}`,i]));
  writeFileSync(f.vectorPath,JSON.stringify(doc));f.run.replayBaseline=f.api.pinReplayVectors(f.root,['tests/add.json']);
  Object.assign(doc.initial_world,{item0:false,item1:null,item2:'',item3:0});delete doc.initial_world.item4;
  for(let i=5;i<20;i++)doc.initial_world[`item${i}`]+=100;
  writeFileSync(f.vectorPath,JSON.stringify(doc));
  const report=f.api.formatReplayEvidence(f.api.readReplayEvidence(f.run));
  for(let i=0;i<20;i++)assert.ok(report.includes(`/initial\\_world/item${i} `),report);
  assert.match(report,/0.*false/);assert.match(report,/1.*null/);assert.match(report,/4.*missing/);
  assert.doesNotMatch(report,/Return to prompt space/);
});

test('2870: a moved scenario can replay at its current path and lists removed and added values',async t=>{
  const f=await fixture(t),old='tests/add.json',next='tests/moved.json';
  writeFileSync(join(f.root,next),readFileSync(f.vectorPath));rmSync(f.vectorPath);
  f.manifest.vectors[0].path=next;
  for(const row of [...f.manifest.checks,...f.manifest.operations,...f.manifest.mutation.failed_checks])row.vector=next;
  f.manifest.source.sha256=f.api.sourceFingerprint(f.root);f.save();
  const result=f.api.readReplayEvidence(f.run,[old,next]);
  assert.equal(result.outcome,'pass',result.reason);
  const report=f.api.formatReplayEvidence(result);
  assert.match(report,/tests\/add\.json/);assert.match(report,/tests\/moved\.json/);assert.match(report,/missing/);
});

test('2870: older saved anchors report hash changes without inventing original values',async t=>{
  const f=await fixture(t);delete f.run.replayBaseline.vectors[0].snapshot;
  const doc=JSON.parse(readFileSync(f.vectorPath));doc.steps[0].checks[0].value=9;writeFileSync(f.vectorPath,JSON.stringify(doc));
  f.manifest.vectors[0].sha256=hash(readFileSync(f.vectorPath));f.manifest.source.sha256=f.api.sourceFingerprint(f.root);f.save();
  const result=f.api.readReplayEvidence(f.run);assert.equal(result.outcome,'pass',result.reason);
  assert.match(f.api.formatReplayEvidence(result),/original values unavailable/);
});

for(const kind of ['missing','empty','malformed'])test(`2870: ${kind} saved scenario is warned and not replayed`,async t=>{
  const f=await fixture(t);
  if(kind==='missing')rmSync(f.vectorPath);else writeFileSync(f.vectorPath,kind==='empty'?'':'{');
  f.manifest.source.sha256=f.api.sourceFingerprint(f.root);f.save();
  const result=f.api.readReplayEvidence(f.run);
  assert.equal(result.outcome,'not_replayed',result.reason);assert.match(f.api.formatReplayEvidence(result),/warning:.*tests\/add\.json/i);
});

test('2530: uncommitted, untracked and executable source edits make evidence stale; commits alone do not',async t=>{
  const f=await fixture(t);f.save();const original=f.manifest.source.sha256;
  f.git('-c','user.name=Test','-c','user.email=test@example.invalid','commit','--allow-empty','-qm','no content change');
  assert.equal(f.api.sourceFingerprint(f.root),original);assert.equal(f.api.readReplayEvidence(f.run).outcome,'pass');
  writeFileSync(join(f.root,'new.mjs'),'new source');assert.equal(f.api.readReplayEvidence(f.run).outcome,'blocked');rmSync(join(f.root,'new.mjs'));
  chmodSync(join(f.root,'code.mjs'),0o755);assert.equal(f.api.readReplayEvidence(f.run).outcome,'blocked');chmodSync(join(f.root,'code.mjs'),0o644);
  writeFileSync(join(f.root,'code.mjs'),'changed');assert.equal(f.api.readReplayEvidence(f.run).outcome,'blocked');
});

test('2530: a crash, survived mutation or empty assertion list is never semantic detection',async t=>{
  for(const kind of ['crash','survived','empty','unknown','zero-exit']){
    const f=await fixture(t);
    if(['crash','survived'].includes(kind))f.manifest.mutation.outcome=kind;
    if(kind==='empty')f.manifest.mutation.failed_checks=[];
    if(kind==='unknown')f.manifest.mutation.failed_checks[0].check_index=99;
    if(kind==='zero-exit')f.manifest.mutation.exit_code=0;
    f.save();assert.equal(f.api.readReplayEvidence(f.run).outcome,'blocked',kind);
  }
});

test('2530: formal result and scope are typed; proved checks need assertion control',async t=>{
  for(const kind of ['unknown','scope','control','counterexample']){
    const f=await fixture(t);
    if(kind==='unknown')f.manifest.formal.result='proved';
    if(kind==='scope')f.manifest.formal.scope='';
    if(kind==='control')f.manifest.formal.result='proved_bounded';
    if(kind==='counterexample')f.manifest.formal.result='failed';
    f.save();assert.equal(f.api.readReplayEvidence(f.run).outcome,'blocked',kind);
  }
});

test('2530: explicit blocked checks and a not-run mutation remain honest without invented exits',async t=>{
  const f=await fixture(t);f.manifest.checks[0].outcome='blocked';f.manifest.checks[0].reason='Unavailable fixture';
  f.manifest.counts.pass=1;f.manifest.counts.blocked=1;
  f.manifest.mutation={kind:'semantic',description:'Replace addition',command:null,exit_code:null,outcome:'not_run',failed_checks:[],reason:'Fixture unavailable'};
  f.save();const r=f.api.readReplayEvidence(f.run);assert.equal(r.outcome,'blocked');assert.equal(r.counts.blocked,1);assert.equal(r.mutation.outcome,'not_run');
});

test('2530: malformed UTF-8, hardlinked or unreadable manifests are blocked',async t=>{
  for(const kind of ['utf8','hardlink','unreadable']){
    const f=await fixture(t);f.save();const path=join(f.runDir,'replay-evidence.json');
    if(kind==='utf8')writeFileSync(path,Buffer.concat([Buffer.from('{"bad":"'),Buffer.from([0xff]),Buffer.from('"}') ]));
    if(kind==='hardlink')linkSync(path,join(f.base,'linked-manifest.json'));
    if(kind==='unreadable')chmodSync(path,0);
    assert.equal(f.api.readReplayEvidence(f.run).outcome,'blocked',kind);
    if(kind==='unreadable')chmodSync(path,0o600);
  }
});

test('2530: missing and empty anchors and substituted vector lists cannot pass',async t=>{
  for(const kind of ['anchor','empty','omitted','substituted']){
    const f=await fixture(t);
    if(kind==='anchor')delete f.run.replayBaseline;
    if(kind==='empty')f.run.replayBaseline=f.api.pinReplayVectors(f.root,[]);
    if(kind==='omitted')f.manifest.vectors=[];
    if(kind==='substituted')f.manifest.vectors[0].sha256='f'.repeat(64);
    f.save();assert.notEqual(f.api.readReplayEvidence(f.run).outcome,'pass',kind);
  }
});

test('2530: a FIFO masquerading as evidence is refused without waiting for a writer',async t=>{
  const f=await fixture(t),path=join(f.runDir,'replay-evidence.json');execFileSync('mkfifo',[path]);
  const moduleUrl=new URL('../src/workflow-replay.mjs',import.meta.url).href;
  const script=`import {readReplayEvidence} from ${JSON.stringify(moduleUrl)};console.log(JSON.stringify(readReplayEvidence(${JSON.stringify(f.run)})))`;
  const out=execFileSync(process.execPath,['--input-type=module','-e',script],{encoding:'utf8',timeout:1500});
  assert.equal(JSON.parse(out).outcome,'blocked');
});

test('2530: report metadata cannot hide counts or the trust boundary with HTML comments',async t=>{
  for(const kind of ['formal','parse-error']){
    const f=await fixture(t);
    if(kind==='formal'){f.manifest.formal.scope='<!-- <details> & hidden';f.save();}
    else {writeFileSync(f.vectorPath,'<!--');f.run.replayBaseline=f.api.pinReplayVectors(f.root,['tests/add.json']);}
    const report=f.api.formatReplayEvidence(f.api.readReplayEvidence(f.run));
    assert.doesNotMatch(report,/<!--|<details>/,kind);
    assert.match(report,/&lt;!--/);assert.match(report,/checks:/);assert.match(report,/does not independently prove/);
  }
});
