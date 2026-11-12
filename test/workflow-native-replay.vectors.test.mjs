import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {readFileSync,writeFileSync,mkdirSync,mkdtempSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {pinReplayVectors,readReplayEvidence,sourceFingerprint} from '../src/workflow-replay.mjs';
import {fullCheckPass} from '../src/workflow-story-card.mjs';
import {openRun,stepDone,approveRun} from '../src/workflow-runner.mjs';
import {preparedCard,TEST} from './helpers/workflow-prompt-reentry-card-fixture.mjs';

const cases=JSON.parse(readFileSync(new URL('../tests/native-case-replay-3124.json',import.meta.url),'utf8'));
const completed=[];
test('approved native cases replay at their public boundaries',t=>{
  const root=mkdtempSync(join(tmpdir(),'native-vector-')), previous=process.cwd();
  t.after(()=>{process.chdir(previous);rmSync(root,{recursive:true,force:true});});
  mkdirSync(join(root,'tests'));execFileSync('git',['init','-q'],{cwd:root});mkdirSync(join(root,'.git/run'));
  for(const [path,document] of Object.entries(cases.initial_world.files)) writeFileSync(join(root,path),JSON.stringify(document));
  process.chdir(root);
  const record=structuredClone(cases.initial_world.replay_record.document);
  record.source.sha256=sourceFingerprint('.');
  writeFileSync('.git/run/replay-evidence.json',JSON.stringify(record));
  const actions={pinReplayVectors:({root,paths})=>pinReplayVectors(root,paths),readReplayEvidence:({run,paths})=>readReplayEvidence(run,paths),fullCheckPass:({options})=>fullCheckPass(options,{env:{HOME:root}})};
  for(const step of cases.steps.filter(step=>Object.hasOwn(actions,step.operation))){
    assert.equal(typeof actions[step.operation],'function',step.operation);
    const result=actions[step.operation](step.input);
    for(const check of step.checks){
      assert.equal(check.target,'result');assert.equal(check.op,'equals');
      const actual=check.path.slice(1).split('/').reduce((value,part)=>value?.[part.replaceAll('~1','/').replaceAll('~0','~')],result);
      assert.deepEqual(actual,check.value,`${step.step_id}: ${check.path}`);
    }
    completed.push(step.step_id);
  }
});


test('approved recovery calls return to prompt space and resume code',async t=>{
  const f=await preparedCard(t), initial=f.record(), root=initial.root;
  const status=join(f.git(f.source,'rev-parse','--path-format=absolute','--git-common-dir'),'pdd','runs','17','status.json');
  initial.replayBaseline={...pinReplayVectors(root,[]),base:{commit:initial.baseSha,note:'No approved cases on base.',select:'linked'}};
  writeFileSync(status,JSON.stringify(initial));
  const previous=process.cwd();process.chdir(root);t.after(()=>process.chdir(previous));
  const actions={
    openRun:input=>{process.chdir(f.source);return openRun(input,f.ports);},
    stepDone:input=>{process.chdir(root);f.tick();return stepDone(input,f.agentPorts());},
    approveRun:input=>{process.chdir(root);f.tick();return approveRun(input,f.agentPorts());},
  };
  for(const step of cases.steps.filter(step=>Object.hasOwn(actions,step.operation))){
    const result=await actions[step.operation](step.input);
    // Fixture setup is declared separately from the public operation.
    for(const setup of cases.initial_world.recovery.setup_actions.filter(item=>item.after_step===step.step_id)){
      writeFileSync(join(root,setup.path),JSON.stringify(setup.document));
      assert.deepEqual(JSON.parse(readFileSync(join(root,setup.path),'utf8')),setup.expected_document);
    }
    for(const check of step.checks){
      const state=f.record(), world={...state,activeAreaName:state.areas[state.area].name};
      assert.ok(['result','world'].includes(check.target));
      const actual=check.path.slice(1).split('/').reduce((value,part)=>value?.[part.replaceAll('~1','/').replaceAll('~0','~')],check.target==='result'?result:world);
      if(check.op==='contains')assert.ok(actual.includes(check.value),`${step.step_id}: ${actual}`);
      else {assert.equal(check.op,'equals');assert.deepEqual(actual,check.value,step.step_id+': '+result.message);}
    }
    completed.push(step.step_id);
  }
});

test('every approved step was replayed in order',()=>{
  assert.deepEqual(completed,cases.steps.map(step=>step.step_id));
  assert.equal(new Set(completed).size,completed.length);
});
