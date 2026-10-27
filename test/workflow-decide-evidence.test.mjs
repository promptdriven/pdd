import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtemp, mkdir, writeFile, rm} from 'node:fs/promises';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {decideWorkflow} from '../src/workflow-decide.mjs';

// The seam can ship without W11. Composed branches use their local reader;
// standalone verification may select the production module via this test-only URL.
const readerUrl=process.env.PDD_TEST_APPROVAL_EVIDENCE_MODULE??new URL('../src/approval-evidence.mjs',import.meta.url).href;
let readApprovalEvidence;
try { ({readApprovalEvidence}=await import(readerUrl)); }
catch(error) {
 if(process.env.PDD_TEST_APPROVAL_EVIDENCE_MODULE||error.code!=='ERR_MODULE_NOT_FOUND') throw error;
}
const runId='11111111-1111-4111-8111-111111111111';
const decisionId='22222222-2222-4222-8222-222222222222';
const input={runId,decisionId,decision:'approve',expectStage:'change',expectSeq:7};
const state={root:'/repo',agent:'codex',waitingDecision:{at:200,evidenceStage:{agent:'codex',root:'/repo',startedAt:100,endedAt:190}}};
const messages=[['Do not approve this plan.',false],['What does this change do?',false],['What does this change do',false],['I approve this plan.',true]];
for(const mode of ['non-TTY','non-TTY yes','agent TTY yes']) {
 for(const [message,accepted] of messages) test(`real Codex JSONL ${mode}: ${message}`,{skip:!readApprovalEvidence&&'optional W11 evidence module is not installed'},async t=>{
  const home=await mkdtemp(join(tmpdir(),'pdd-decide-evidence-'));
  t.after(()=>rm(home,{recursive:true,force:true}));
  const directory=join(home,'sessions');await mkdir(directory);
  const rows=[
   {type:'session_meta',payload:{id:runId,cwd:'/repo',timestamp:new Date(100).toISOString()}},
   {type:'response_item',timestamp:new Date(250).toISOString(),payload:{type:'message',role:'user',content:[{type:'input_text',text:message}]}},
  ];
  await writeFile(join(directory,'rollout-decision.jsonl'),rows.map(row=>JSON.stringify(row)).join('\n')+'\n');
  let admitted=0;
  const ports={codexHome:home,env:mode==='agent TTY yes'?{PDD_AGENT_SESSION:'run/scope'}:{},
   stdin:{isTTY:mode==='agent TTY yes'},stderr:{isTTY:mode==='agent TTY yes'},now:()=>300,readApprovalEvidence,
   confirm:()=>assert.fail('chat cannot use terminal confirmation'),
   workflowRunner:{async applyWorkflowDecision(i,p){
    const auth=await p.authorizeDecision({input:i,state});
    if(!auth.ok)return {state:'refused',code:auth.code,exitCode:1};
    admitted++;return {state:'recorded',code:null,exitCode:0,approvalRecord:auth.approvalRecord};
   }},
  };
  const result=await decideWorkflow({...input,yes:mode!=='non-TTY'},ports);
  assert.equal(admitted,accepted?1:0);
  assert.equal(result.state,accepted?'recorded':'refused');
  if(accepted)assert.deepEqual(result.approvalRecord,{kind:'chat',agent:'codex',sessionId:runId,userMessage:message,userMessageAt:250,at:300});
  else {assert.equal(result.code,'person_required');assert.equal(result.approvalRecord,undefined);}
 });
}
