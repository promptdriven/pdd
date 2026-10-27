// Generated from prompts/cli/workflow-decide.prompt.md (sha256: f239262f051dfae8e78545cb377c54369ac5d5030459abe83dcea25345cc4e8b).
import {verifyPhoneApproval} from './phone-approval.mjs';
import {createInterface} from 'node:readline/promises';
const UUID=/^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/;
const STAGE=/^(?=.{1,64}$)[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/;
const validText=value=>typeof value==='string'&&[...value].length>=1&&[...value].length<=4000&&!/[\x00-\x08\x0b-\x1f\x7f-\x9f]/u.test(value);
export function validDecisionInput(i) {
  return i&&UUID.test(i.runId??'')&&UUID.test(i.decisionId??'')&&['approve','skip','changes'].includes(i.decision)
    &&STAGE.test(i.expectStage??'')&&Number.isSafeInteger(i.expectSeq)&&i.expectSeq>0
    &&(i.decision==='changes'?validText(i.text):i.text===undefined)
    &&(i.yes===undefined||typeof i.yes==='boolean')
    &&(i.via===undefined?i.phoneId===undefined&&i.approval===undefined:i.via==='phone'&&typeof i.phoneId==='string'&&i.phoneId.length>0&&typeof i.approval==='string'&&i.approval.length>0);
}
async function terminalQuestion(question,stdin,stderr) {
  const rl=createInterface({input:stdin,output:stderr});
  try{return /^(?:y|yes)$/i.test((await rl.question(question)).trim());}finally{rl.close();}
}
const clean=value=>String(value??'').replace(/[\x00-\x1f\x7f-\x9f]/g,' ');
function matchesChatIntent(input, userMessage) {
  if(typeof userMessage!=='string')return false;
  const reply=userMessage.trim();
  if(input.decision==='approve')return /^(?:I )?approve(?: (?:this|the) (?:plan|proposal|step))?[.!]?$/i.test(reply);
  if(input.decision==='changes') {
    const changes=/^(?:request )?changes:\s*([\s\S]+)$/i.exec(reply);
    return !!changes && changes[1].trim()===input.text.trim();
  }
  return false;
}
async function authorize(input,state,ports) {
  const refused=(code,message)=>({ok:false,code,message});
  const now=(ports.now??Date.now)();
  if(input.via==='phone') {
    return verifyPhoneApproval({token:input.approval,phoneId:input.phoneId,runId:input.runId,stage:input.expectStage,
      decision:input.decision,expectSeq:input.expectSeq,...(input.text!==undefined?{text:input.text}:{}),
      usedNonces:(state.decisions??[]).filter(d=>d.approvalRecord?.kind==='phone').map(d=>d.approvalRecord.nonce)},
      {lookupPhone:ports.lookupPhone===undefined&&typeof ports.clientAdapter?.lookupPhone==='function'?ports.clientAdapter.lookupPhone.bind(ports.clientAdapter):ports.lookupPhone,now:ports.now});
  }
  if(ports.authorizeDecision) {
    const evidence=await ports.authorizeDecision({input,state});
    return evidence?.kind==='phone'&&evidence.authenticated===true
      ?{ok:true,approvalRecord:{...evidence,at:now}}
      :refused('person_required','An authenticated phone tap is required.');
  }
  const env=ports.env??process.env,stdin=ports.stdin??process.stdin,stderr=ports.stderr??process.stderr;
  if(!env.PDD_AGENT_SESSION&&stdin.isTTY===true&&stderr.isTTY===true) {
    const verb={approve:'Approve the plan for',changes:'Request changes for',skip:'Skip the optional step for'}[input.decision];
    const question=`${verb} ${clean(state.repo)}#${state.issue?.number??'?'} "${clean(state.issue?.title)}"? (y/N) `;
    const accepted=input.yes===true||await (ports.confirm??(q=>terminalQuestion(q,stdin,stderr)))(question);
    return accepted===true?{ok:true,approvalRecord:{kind:'terminal',at:now}}:refused('person_required','Decision declined; the run is unchanged.');
  }
  let read=ports.readApprovalEvidence;
  if(!read)try{read=(await import('./approval-evidence.mjs')).readApprovalEvidence;}catch{}
  if(typeof read!=='function')return refused('approval_evidence_unavailable','A terminal confirmation, authenticated phone tap or verified user chat message is required; chat evidence verification is unavailable.');
  const evidence=await read({stage:state.waitingDecision?.evidenceStage??{agent:state.agent,root:state.root,startedAt:undefined,endedAt:undefined},gateAskedAt:state.waitingDecision?.at,decision:input.decision},ports);
  if(evidence?.ok!==true)return refused('person_required',clean(evidence?.message||'No user message after the gate could be verified.'));
  if(!matchesChatIntent(input,evidence.userMessage))return refused('person_required',
    'The latest user message does not explicitly authorize this decision. Reply "approve" to approve, or "changes: <exact requested text>" to request changes.');
  return {ok:true,approvalRecord:{kind:'chat',agent:evidence.agent,sessionId:evidence.sessionId,userMessage:evidence.userMessage,userMessageAt:evidence.userMessageAt,at:now}};
}
export async function decideWorkflow(input,ports={}) {
  const i=structuredClone(input??{});
  const base={runId:UUID.test(i.runId??'')?i.runId:null,decisionId:UUID.test(i.decisionId??'')?i.decisionId:null,
    decision:['approve','skip','changes'].includes(i.decision)?i.decision:null,stage:null,journalSeq:null,controller:null};
  const fail=(code,state='refused')=>({...base,state,code,exitCode:code==='bad_args'?2:1,message:`${state}: ${code??'decision could not be confirmed'}.`});
  if(!validDecisionInput(i))return fail('bad_args');
  try {
    const runner=ports.workflowRunner??await import('./workflow-runner.mjs');
    if(typeof runner.applyWorkflowDecision!=='function')return fail('unsupported');
    const answer=await runner.applyWorkflowDecision(i,{...ports,authorizeDecision:({state})=>authorize(i,state,ports)});
    return {...base,...answer};
  }catch{return fail(null,'failed');}
}
