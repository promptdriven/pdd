import test from 'node:test';
import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
import {resolve} from 'node:path';
import {mergeWorld} from './helpers/autopilot-merge-world.mjs';
const source=process.env.PDD_MERGE_TEST_SOURCE;
const {evaluateMergeRules}=await import(source?pathToFileURL(resolve(source,'src/autopilot-merge.mjs')).href:'../src/autopilot-merge.mjs');

test('merge admission obeys all six guards across 576 bounded combinations',()=>{
  let examined=0;
  // Oracle from Story AC2: all five binary proofs and repairs within the base limit.
  for(let mask=0;mask<32;mask++)for(const limit of [0,1,2])for(const repairs of [-1,0,1,2,3,null]){
    const w=mergeWorld();w.config.autopilot.merge={max_repairs:limit};w.evidence.repairs=repairs;
    w.evidence.reviews[0].mustFix=mask&1?0:1;
    w.evidence.fullSuite.passed=!!(mask&2);
    w.ci.checks[0].passed=!!(mask&4);
    w.config.autopilot.merge.autonomy=mask&8?'merge':'manual';
    w.evidence.audit.planned=!!(mask&16);
    const expected=mask===31 && Number.isInteger(repairs) && repairs>=0 && repairs<=limit;
    const result=evaluateMergeRules({config:w.config,evidence:w.evidence,pull:w.pull,ci:w.ci,trusted:true});
    assert.equal(result.allowed,expected,`mask=${mask} limit=${limit} repairs=${repairs}`);
    assert.equal(result.rule===null,expected);examined++;
  }
  assert.equal(examined,576);
});

test('optional skip eligibility obeys required and at-least-one-ran rules across 96 combinations',()=>{
  let examined=0;
  // Oracle from Repair 2: only completed optional skips may accompany passing CI.
  for(const primary of ['pass','skipping','fail','unknown'])
    for(const extra of ['pass','skipping','fail','pending','cancel','unknown'])
      for(const required of [[],['tests'],['extra'],['tests','extra']]){
        const w=mergeWorld();const states={tests:primary,extra};
        w.ci.checks=Object.entries(states).map(([name,state])=>({name,passed:state==='pass',skipped:state==='skipping'}));
        w.ci.required=required;
        const expected=[primary,extra].includes('pass')
          && [primary,extra].every(state=>['pass','skipping'].includes(state))
          && required.every(name=>states[name]==='pass');
        const result=evaluateMergeRules({config:w.config,evidence:w.evidence,pull:w.pull,ci:w.ci,trusted:true});
        assert.equal(result.allowed,expected,JSON.stringify({primary,extra,required}));
        assert.equal(result.rule,expected?null:'required_ci');examined++;
      }
  assert.equal(examined,96);
});
