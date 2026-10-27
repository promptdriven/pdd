import test from 'node:test';
import assert from 'node:assert/strict';
import {runPdd} from '../src/pdd-cli.mjs';
import {parseArgv} from '../src/argument-parser.mjs';
const runId='12345678-1234-4123-8123-123456789abc',attemptId='87654321-4321-4321-8321-cba987654321';
const capture=()=>({text:'',write(v){this.text+=v;}});
const stages=Object.fromEntries(['runHerdrStage','inspectHerdrStage','attachHerdrStage','closeHerdrStage','inspectHerdrChat'].map(name=>[name,()=>assert.fail('CLI must delegate rather than launch directly')]));

test('chat opt-in reaches the runner and finite running is a successful CLI reply',async()=>{
  const stdout=capture(),stderr=capture();let called=0;
  const code=await runPdd(['workflow','run','small-change','3','--chat'],{stdout,stderr,workflowStages:stages,
    workflowRunner:{async runWorkflow(input,ports){called++;assert.equal(input.chat,true);assert.equal(input.issue,'3');assert.equal(ports.inspectHerdrChat,stages.inspectHerdrChat);return {state:'running',exitCode:0,message:'Chat 1 is working.'};}}});
  assert.equal(code,0);assert.equal(called,1);assert.equal(stderr.text,'');assert.match(stdout.text,/returns after delivery/);
});

test('step done and workflow report bind the same exact attempt and keep stdout as one JSON result',async()=>{
  for(const argv of [['step','done','scope',runId,attemptId],['workflow','report',runId,'scope',attemptId]]){
    const stdout=capture(),stderr=capture();let calls=0;
    const code=await runPdd(argv,{stdout,stderr,workflowStages:stages,workflowRunner:{async reportWorkflowStage(input,ports){
      calls++;assert.equal(input.runId,runId);assert.equal(input.stageId,'scope');assert.equal(input.attemptId,attemptId);
      ports.stdout.write('native check output\n');return {state:'waiting',exitCode:2,message:'Plan awaits approval'};
    }}});
    assert.equal(code,2);assert.equal(calls,1);assert.equal(JSON.parse(stdout.text).state,'waiting');assert.equal(stderr.text,'native check output\n');
  }
  assert.throws(()=>parseArgv(['step','done','scope']));
  assert.throws(()=>parseArgv(['workflow','report',runId,'../scope',attemptId]));
});
