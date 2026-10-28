// Generated from prompts/cli/agent-case-collector.prompt.md (sha256: f58b85afdfdd77a8651a0360db80848ec97a123e3fb6ff0560c9b451f6a42da8).
import {createHash} from 'node:crypto';
import {join} from 'node:path';
import {importAgentSavedCase,agentSavedCaseFingerprint} from './agent-saved-case.mjs';
import {planAgentStoryRule,applyAgentStoryRule,resumeAgentStoryRule} from './agent-story-rule.mjs';
import {cleanText} from './runtime-output.mjs';
const object=x=>x!==null&&typeof x==='object'&&!Array.isArray(x);
const ID=/^[A-Za-z0-9_-]{1,128}$/;
const digest=x=>createHash('sha256').update(x).digest('hex');
const final=state=>['added','declined','failed'].includes(state);
const interrupted=context=>context.interrupted||context.signal?.aborted;
function message(context,value){return Array.from(cleanText(String(value??''),context.secrets??[]).replace(/[\x00-\x1f\x7f-\x9f]/g,' ').trim()).slice(0,500).join('')||'The saved-case import has no result yet.';}
function wire(context,outcome,saved){const state=['added','already_added'].includes(outcome.status)?'added':outcome.status==='declined'?'declined':outcome.status==='pending'?'pending':'failed',body={state,message:message(context,outcome.result)};if(state==='added'){body.path=outcome.path;body.step_ids=saved.test.steps.map(s=>s.step_id);if(outcome.receipt?.criterion_id)body.criterion_id=outcome.receipt.criterion_id;}return body;}
export async function collectAgentSavedCases(context,tryId,{answers=null,timeoutMs=30000}={}){
 if(typeof tryId!=='string'||!ID.test(tryId))throw Error('The saved-case Try identity is invalid.');
 if(interrupted(context))return'ended';
 const {runtime,store,root,ports}=context,path=join(store.folder('tries'),`${tryId}.tests.json`);
 const read=await runtime.send(`/v1/try/${tryId}/tests`,{method:'GET'},timeoutMs);
 if([401,403,410].includes(read.status))return'ended';
 if(read.status!==200||!Array.isArray(read.json?.tests))return read.lost?'ok':'missing';
 const previous=store.read(path),records=Object.assign(Object.create(null),object(previous)?previous:{});
 const persist=()=>store.write(path,records),print=text=>ports.stdout.write(`${text}\n`);
 for(const saved of read.json.tests.slice(0,50)){
  if(interrupted(context))return'ended';
  const key=saved?.id;if(typeof key!=='string'||!ID.test(key))continue;
  const localId=`try-case-${digest(tryId+'\0'+key)}`,local={...saved,id:localId};
  let payloadHash,record=records[key];
  try{payloadHash=agentSavedCaseFingerprint(local);}catch{
   if(record&&!record.invalid){if(!record.changedNotice){print('not added: the saved case changed under an existing identity. Save it again with a new case ID.');record.changedNotice=true;persist();}continue;}
   if(!record){const body={state:'failed',message:'not added: the saved case has invalid or unsafe data.'};record={invalid:true,state:'failed',result:body.message,wire:body,posted:false};records[key]=record;persist();print(body.message);}
  }
  if(payloadHash&&record?.invalid){if(!record.changedNotice){print('not added: the saved case changed under an existing identity. Save it again with a new case ID.');record.changedNotice=true;persist();}continue;}
  // Old successful or refused imports are already handled, without a verifiable new receipt.
  if(record&&!record.state)continue;
  if(record?.payloadHash&&record.payloadHash!==payloadHash){if(!record.changedNotice){print('not added: the saved case changed under an existing identity. Save it again with a new case ID.');record.changedNotice=true;persist();}continue;}
  if(payloadHash&&(!record||!final(record.state))){
   const stateDir=store.folder('agent-story-rules');
   let outcome=resumeAgentStoryRule({root,stateDir,caseId:localId,saved:local}),approved=outcome.status!=='absent'&&outcome.status!=='refused';
   if(record?.approved&&outcome.status==='refused'){approved=true;outcome={status:'pending',result:outcome.result};}
   else if(outcome.status==='absent'){
    outcome=importAgentSavedCase({root,saved:local,receipt:record?.receipt??null});
    if(outcome.status==='needs_rule'){
     if(outcome.rules.length!==1)outcome={status:'refused',result:'not added: this case needs more than one new Story rule. Review it with your agent first.'};
     else {
      const planned=planAgentStoryRule({root,saved:local,rule:outcome.rules[0]});
      if(planned.status!=='ready')outcome=planned;
      else if(!answers)outcome={status:'pending',result:'Not saved. Add this Story rule from a terminal: run pdd try with this Story and answer the question.'};
      else {print(planned.plan.question);const answer=await answers.ask();if(interrupted(context))return'ended';if(/^(?:y|yes)$/i.test(String(answer).trim())){outcome=applyAgentStoryRule({root,stateDir,plan:planned.plan,approved:true});approved=['added','already_added','pending'].includes(outcome.status);}else outcome={status:'declined',result:'Not saved. You declined the new Story rule; the Story and tests were not changed.'};}
     }
    }
   }
   const body=wire(context,outcome,saved),changed=!record||record.result!==body.message||record.state!==body.state;
   const wasAdded=record?.state==='added';
   record={...(record??{}),at:new Date(ports.now()).toISOString(),payloadHash,localId,state:body.state,result:body.message,approved,...(outcome.receipt?{receipt:outcome.receipt}:{}),wire:body,posted:record?.posted===true&&JSON.stringify(record.wire)===JSON.stringify(body)};
   records[key]=record;persist();
   if(changed)print(body.message);
   if(body.state==='added'&&!wasAdded){try{context.onAgentCaseSaved?.({id:key,name:saved.name,story_path:saved.story_path??saved.test?.story_path,result:body.message});}catch{}}
  }
  if(record.posted||context.agentCaseReceiptUnsupported||interrupted(context))continue;
  const reply=await runtime.send(`/v1/try/${tryId}/tests/${key}/result`,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(record.wire)},timeoutMs);
  if([401,403,410].includes(reply.status))return'ended';
  if(reply.status===404){context.agentCaseReceiptUnsupported=true;continue;}
  if(reply.status>=200&&reply.status<300&&reply.json?.ok===true){record.posted=true;persist();}
 }
 return'ok';
}
