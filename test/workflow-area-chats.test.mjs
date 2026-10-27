import test from 'node:test';
import assert from 'node:assert/strict';
import {areaChatForStage,areaChatStatus,AREA_CHATS} from '../src/workflow-area-chats.mjs';
import {runStatusFromState} from '../src/workflow-run-records.mjs';

test('small-change has exactly two area boundaries, with publication and merge in build',()=>{
  assert.deepEqual(AREA_CHATS['small-change'].map(a=>a.label),['Chat 1: plan','Chat 2: build']);
  assert.equal(areaChatForStage('small-change','scope').id,'plan');
  for(const id of ['change','verify','open-pr','wait-merge'])assert.equal(areaChatForStage('small-change',id).id,'build');
  assert.equal(areaChatForStage('feature','scope'),null);
});

test('plan approval stays in Chat 1; shared C3 fields survive area projection without invented sessions',()=>{
  const state={chat:true,name:'small-change',runId:'run-1',agent:'codex',index:1,seq:2,
    definitions:[{id:'scope',kind:'agent'},{id:'change',kind:'agent'},{id:'verify',kind:'agent'}],
    completed:[{id:'scope',startedAt:10,endedAt:20,backend:{agent:'codex',session:'pdd',nativeSession:null}}],
    proposal:{approval:'next-advance'},accepted:null,links:[],changes:[],approvalRecord:null};
  const base=runStatusFromState(state,{phase:'exit',outcome:{state:'waiting'},now:30});
  const status=areaChatStatus({state,base,now:30});
  assert.equal(status.area.id,'plan');assert.equal(status.gate,'approve-plan');
  assert.deepEqual(status.waitingFor.decisions,['approve']);
  assert.deepEqual(status.steps,base.steps);assert.equal(status.steps[0].session,null);
  assert.equal(status.steps[0].startedAt,10);assert.equal(status.steps[0].endedAt,20);
  assert.equal(status.links,base.links);assert.equal(status.changes,base.changes);
  assert.equal(areaChatStatus({state:{...state,chat:false},base}),null);
});
