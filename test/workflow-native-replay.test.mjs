import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {mkdirSync,mkdtempSync,rmSync,writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {pinReplayVectors,readReplayEvidence,sourceFingerprint} from '../src/workflow-replay.mjs';
import {storyFingerprint,storyCard} from '../src/workflow-story-card.mjs';

test('native cases appear in the Story card and pin their original public boundary and checks', t => {
  const root=mkdtempSync(join(tmpdir(),'native-case-'));t.after(()=>rmSync(root,{recursive:true,force:true}));
  mkdirSync(join(root,'tests'));mkdirSync(join(root,'user_stories'));
  execFileSync('git',['init','-q'],{cwd:root});
  const story='user_stories/native.md', path='tests/native.json';
  writeFileSync(join(root,story),'# Native\n\n## Acceptance criteria\n\n1. Return the requested value.\n');
  writeFileSync(join(root,path),JSON.stringify({schema_version:'pdd.native-scenario.v1',story_path:story,criteria:[{id:'AC1'}],steps:[{step_id:'request',entry_path:'prompts/example.prompt.md',operation:'example CLI',runtime_reason:'Native command effects require this boundary.',input:{value:4},checks:[{criterion_id:'AC1',target:'result',path:'/value',op:'equals',value:4}]}]}));
  const changed=[story,path];
  const card=storyCard({run:{repo:'example/repo',number:1,issue:{title:'Native',url:'https://example.invalid'}},root,changed,prompts:[]});
  assert.match(card,/request/);assert.match(card,/AC1/);
  assert.equal(storyFingerprint({root,changed}).tests.length,1);
  const anchor=pinReplayVectors(root,[path]);assert.equal(anchor.vectors.length,1);assert.equal(anchor.vectors[0].checks.length,1);
  const empty=pinReplayVectors(root,[]);
  assert.equal(readReplayEvidence({root,runDir:root,runId:'one',replayBaseline:empty},[path]).outcome,'not_replayed');
  const runDir=mkdtempSync(join(tmpdir(),'native-record-'));t.after(()=>rmSync(runDir,{recursive:true,force:true}));
  const vector=anchor.vectors[0], check={...vector.checks[0],outcome:'pass'};
  const record={schema_version:'pdd.replay-evidence.v1',run_id:'one',source:{kind:'git-content-v1',sha256:sourceFingerprint(root)},vectors:[{path,sha256:vector.sha256}],checks:[check],operations:[{...vector.steps[0],executed:true,outcome:'returned',boundary:{kind:'command',name:'example CLI'},command:'synthetic test',exit_code:0}],counts:{total:1,pass:1,fail:0,blocked:0,not_replayed:0},mutation:{kind:'semantic',description:'change value',command:'synthetic control',exit_code:1,outcome:'assertion_failure',failed_checks:[{vector:path,step_id:'request',check_index:0}]},formal:{result:'not_applicable',scope:'display',reason:'plain wording',control_outcome:'not_run'}};
  const save=()=>writeFileSync(join(runDir,'replay-evidence.json'),JSON.stringify(record));save();
  const run={root,runDir,runId:'one',replayBaseline:anchor};
  assert.equal(readReplayEvidence(run).outcome,'pass');
  record.operations[0].boundary.name='other command';save();assert.equal(readReplayEvidence(run).outcome,'blocked');
  record.operations[0].boundary.name='example CLI';record.mutation.outcome='crash';save();assert.equal(readReplayEvidence(run).outcome,'blocked');
  writeFileSync(join(root,path),JSON.stringify({...JSON.parse(readFileSync(join(root,path))),'extra':true}));
  assert.equal(readReplayEvidence(run).outcome,'blocked');
});

import {cpSync,readFileSync} from 'node:fs';
import {startRun,stepDone,approveRun} from '../src/workflow-runner.mjs';
import {fixture,packageRoot} from './helpers/workflow-runner-fixture.mjs';

test('native case publication requires a shown, explicit approval and freezes the published cases', async t => {
  const f=await fixture(t,{name:'feature',agent:'codex'});
  const started=await startRun({name:'feature',issue:'17',agent:'codex',cwd:f.source,packageRoot},f.ports);
  assert.equal(started.exitCode,0,started.message);
  const root=f.record().root;
  const done=async step=>{f.tick();const r=await stepDone({step,summary:step,cwd:root,...(step==='visual'?{skipped:'no screen'}:{})},f.agentPorts());assert.equal(r.exitCode,0,r.message);return r;};
  await done('understand');await done('visual');
  for(const dir of ['prompts','user_stories','tests'])mkdirSync(join(root,dir),{recursive:true});
  const harbor=join(packageRoot,'test','fixtures','harbor');
  cpSync(join(harbor,'prompts/place_order.prompt.md'),join(root,'prompts/place_order.prompt.md'));
  cpSync(join(harbor,'user_stories/place-order.md'),join(root,'user_stories/place-order.md'));
  const scenario=JSON.parse(readFileSync(join(harbor,'tests/place-order.json')));scenario.schema_version='pdd.native-scenario.v1'; scenario.steps.forEach(step=>{step.operation='nativePlaceOrder';step.runtime_reason='Native filesystem effects require this boundary.';});
  writeFileSync(join(root,'tests/place-order.json'),JSON.stringify(scenario));
  f.git(root,'add','.');f.git(root,'commit','-qm','Story and native cases');
  await done('prompt-story');
  const approve=async words=>{f.tick();return approveRun({ref:'17',cwd:root,said:'-'},{...f.agentPorts(),stdin:(async function*(){yield words;})()});};
  let out=await approve('I approve these cases.');assert.equal(out.exitCode,0,out.message);
  out=await done('check');assert.equal(f.prs.length,0);assert.match(out.message,/Explicit approval/);
  writeFileSync(join(root,'tests/other.json'),JSON.stringify({...scenario,schema_version:'prompt-runtime.program-scenario.v1'}));
  out=await approve('I approve publication with no Runtime verdict.');assert.notEqual(out.exitCode,0);assert.equal(f.prs.length,0);
  rmSync(join(root,'tests/other.json'));
  out=await approve('I approve publication with no Runtime verdict.');assert.equal(out.exitCode,0,out.message);
  assert.equal(f.prs.length,1);assert.equal(f.record().gate.kind,'ask-code');
  assert.equal(f.record().replayBaseline.vectors.length,1);
});

import {openRun} from '../src/workflow-runner.mjs';
import {preparedCard,TEST,PROMPT} from './helpers/workflow-prompt-reentry-card-fixture.mjs';
import {interfaceBlocks} from '../src/runtime-preflight.mjs';

test('returning to prompt space publishes a native case whose owner has no Runtime interface',async t=>{
  const f=await preparedCard(t), initial=f.record(), root=initial.root;
  const status=join(f.git(f.source,'rev-parse','--path-format=absolute','--git-common-dir'),'pdd','runs','17','status.json');
  initial.replayBaseline={...pinReplayVectors(root,[]),base:{commit:initial.baseSha,note:'No approved cases on base.',select:'linked'}};
  writeFileSync(status,JSON.stringify(initial));
  const before=f.record();
  assert.equal(readReplayEvidence(before,[TEST]).outcome,'not_replayed');
  let out=await openRun({ref:'17',area:'prompt-pr',cwd:f.source},f.ports);assert.equal(out.exitCode,0,out.message);
  const promptPath=join(root,PROMPT), prompt=readFileSync(promptPath,'utf8'), blocks=interfaceBlocks(prompt);
  assert.equal(blocks.length,1);
  writeFileSync(promptPath,prompt.replace(blocks[0][0],''));
  const doc=JSON.parse(readFileSync(join(root,TEST),'utf8'));doc.schema_version='pdd.native-scenario.v1';
  doc.steps.forEach(step=>{step.operation='nativePlaceOrder';step.runtime_reason='Native filesystem effects require this boundary.';});
  doc.steps[0].checks[0].value=901;
  writeFileSync(join(root,TEST),JSON.stringify(doc));
  out=await f.done('check');
  assert.match(out.message,/Story or expected contract changed/);
  assert.equal(f.record().areas[f.record().area].name,'story');
  assert.deepEqual(f.record().replayBaseline,before.replayBaseline);
  out=await f.done('prompt-story');assert.equal(f.record().gate.kind,'approve');
  assert.match(out.message,/901/);
  assert.deepEqual(f.record().replayBaseline,before.replayBaseline);
  f.tick();out=await approveRun({ref:'17',cwd:f.source,said:'I approve the changed native case.'},f.agentPorts());assert.equal(out.exitCode,0,out.message);
  out=await f.done('check');assert.match(out.message,/Native approval covers only/);
  f.tick();out=await approveRun({ref:'17',cwd:f.source,said:'I approve publishing these native cases.'},f.agentPorts());assert.equal(out.exitCode,0,out.message);
  assert.equal(f.record().replayBaseline.vectors[0].snapshot.schema_version,'pdd.native-scenario.v1');
  assert.equal(f.record().replayBaseline.vectors[0].snapshot.steps[0].checks[0].value,901);
  f.tick();out=await approveRun({ref:'17',cwd:f.source,said:'Proceed with code.'},f.agentPorts());assert.equal(out.exitCode,0,out.message);
  assert.equal(f.record().areas[f.record().area].name,'code');
});

test('native publication cannot replace a base Runtime case or a declared Runtime operation', async t => {
  for (const mode of ['replace-base','declared-operation','changed-program','failed-runtime']) await t.test(mode,async t=>{
    const f=await fixture(t,{name:'feature',agent:'codex'}), harbor=join(packageRoot,'test','fixtures','harbor');
    if(['replace-base','failed-runtime'].includes(mode)) {
      for(const dir of ['prompts','user_stories','tests'])mkdirSync(join(f.source,dir),{recursive:true});
      for(const path of ['prompts/place_order.prompt.md','user_stories/place-order.md','tests/place-order.json'])cpSync(join(harbor,path),join(f.source,path));
      f.git(f.source,'add','.');f.git(f.source,'commit','-qm','Existing Runtime case');f.git(f.source,'update-ref','refs/remotes/origin/main',f.git(f.source,'rev-parse','HEAD'));
    }
    const started=await startRun({name:'feature',issue:'17',agent:'codex',cwd:f.source,packageRoot},f.ports);assert.equal(started.exitCode,0,started.message);
    const root=f.record().root,done=async step=>{f.tick();return stepDone({step,summary:step,cwd:root,...(step==='visual'?{skipped:'no screen'}:{})},f.agentPorts());};
    assert.equal((await done('understand')).exitCode,0);assert.equal((await done('visual')).exitCode,0);
    for(const dir of ['prompts','user_stories','tests'])mkdirSync(join(root,dir),{recursive:true});
    for(const path of ['prompts/place_order.prompt.md','user_stories/place-order.md'])cpSync(join(harbor,path),join(root,path));
    const doc=JSON.parse(readFileSync(join(harbor,'tests/place-order.json')));doc.schema_version='pdd.native-scenario.v1';
    doc.steps.forEach(step=>{if(mode!=='declared-operation')step.operation='nativePlaceOrder';step.runtime_reason='Native filesystem effects require this boundary.';});
    writeFileSync(join(root,mode==='failed-runtime'?'tests/native.json':'tests/place-order.json'),JSON.stringify(doc));
    if(mode==='changed-program')cpSync(join(harbor,'tests/place-order.json'),join(root,'tests/program.json'));
    f.git(root,'add','.');f.git(root,'commit','-qm','Native cases');
    assert.equal((await done('prompt-story')).exitCode,0);f.tick();
    assert.equal((await approveRun({ref:'17',cwd:root,said:'I approve these cases.'},f.agentPorts())).exitCode,0);
    if(mode==='failed-runtime') {
      const state=join(f.base,'runtime-state');f.ports.env.PDD_STATE_DIR=state;
      const batch='20261027-180000-abcd',folder=join(state,'batches',batch),row={test:'tests/place-order.json',state:'failed'};
      mkdirSync(folder,{recursive:true});
      writeFileSync(join(folder,'batch.json'),JSON.stringify({batch,root,created_at:'2026-10-27T18:00:00.000Z',intent:'check',source_sha256:'f'.repeat(64),rows:[row]}));
      writeFileSync(join(folder,'summary.json'),JSON.stringify({batch,repo:root,source_sha256:'f'.repeat(64),rows:[row]}));
    }
    const out=await done('check');assert.doesNotMatch(out.message,/Native approval covers only/);assert.equal(f.prs.length,0);
    if(mode==='failed-runtime')assert.match(out.message,/Not passed \(failed\): tests\/place-order.json/);
  });
});
