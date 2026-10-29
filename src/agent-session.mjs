// Generated from prompts/cli/agent-session.prompt.md (sha256: 9fb4a8813cef410378455d25fce8bbc0602057e10f1abe45e380b852990ff5ec).
import { randomUUID } from 'node:crypto';
import { runAgentProcess } from './agent-adapters.mjs';
import { createCodexSession } from './agent-codex-session.mjs';
import { createClaudeSession } from './agent-claude-session.mjs';
import { createSessionFiles } from './agent-session-files.mjs';
import { validSessionId } from './workflow-chat.mjs';
const failure = message => ({code:1,stdout:'',stderr:message});
const configArgs = args => args.flatMap((arg,index) => arg === '-c' && index+1 < args.length ? ['-c',args[index+1]] : []);
const firstLine = text => String(text || '').split(/\r?\n/).map(line=>line.trim()).find(Boolean) || '';
function unavailable(answer,sessionId) {
 if(answer.code===0 || String(answer.stdout||'').trim())return false;
 const line=firstLine(answer.stderr);
 if(/rate.?limit|usage.?limit|quota|credits|capacity|authenticat|sign.?in|not logged|provider/i.test(line))return false;
 return /^(?:error:\s*)?(?:unexpected argument|unknown option|unrecognized (?:option|argument))/i.test(line)&&/--(?:resume|json)\b/.test(line)
  || !!sessionId&&line.includes(sessionId)&&/^(?:error:\s*)?(?:no (?:saved session|conversation) found|(?:conversation|session).*(?:not found|does not exist))/i.test(line);
}
function codexAnswer(answer,expectedId) {
 let id=null,text=null,complete=false;
 try {
  for(const line of String(answer.stdout||'').split(/\r?\n/).filter(line=>line.trim())) {
   const event=JSON.parse(line);
   if(complete)return {answer:failure('The resumed agent sent data after completion.'),id};
   if(event.item&&!['agent_message','reasoning','plan','todo_list','context_compaction'].includes(event.item.type))return {answer:failure('The resumed agent attempted an unavailable tool.'),id};
   if(!['thread.started','turn.started','turn.completed','turn.failed','item.started','item.updated','item.completed','error'].includes(event.type))return {answer:failure('The resumed agent returned an unsupported event.'),id};
   if(event.type==='thread.started') {
    if(!validSessionId(event.thread_id)||(id&&id!==event.thread_id)||(expectedId&&expectedId!==event.thread_id))return {answer:failure('The resumed agent returned a different session identity.'),id:null};
    id=event.thread_id;
   }
   if(event.type==='item.completed'&&event.item?.type==='agent_message')text=event.item.text;
   if(event.type==='turn.completed')complete=true;
   if(event.type==='turn.failed'||event.type==='error')return {answer:failure(event.error?.message||event.message||'The resumed agent turn failed.'),id};
  }
 }catch{return {answer:failure('The resumed agent returned malformed structured output.'),id};}
 if(answer.code!==0)return {answer,id};
 if(!complete||typeof text!=='string'||!text.trim()||!(id||expectedId))return {answer:failure('The resumed agent did not confirm a complete answer.'),id};
 return {answer:{...answer,stdout:text},id};
}
const fingerprint = (command,options) => JSON.stringify([command,options.cwd,Object.entries(options.env||{}).sort(([a],[b])=>a.localeCompare(b))]);
export function createAgentSession({kind,run:processRun=runAgentProcess,spawn,now=Date.now,createCodex=createCodexSession,createClaude=createClaudeSession,createFiles=createSessionFiles}={}) {
 let unclaimed=false,cleanupUnsafe=false;
 let closed=false,mode='warm',provider=null,binding=null,sessionId=null,files=null,prepared=false,active=null,controller=null,closing=null;
 async function disposeWarm(){const previous=provider;provider=null;if(previous)try{await previous.close();}catch{closed=true;throw Error('The agent process could not be closed. Reconnect pdd try.');}}
 async function persistent(command,args,options) {
  if(!prepared) {
   files=createFiles({agent:kind,cwd:options.cwd,env:options.env,now});
   try{await files.prepare();prepared=true;}catch{files=null;mode='fresh';return processRun(command,args,options);}
  }
  const startedAt=now(),previous=sessionId;
  let persistentArgs;
  if(kind==='codex') {
   const safe=[...configArgs(args),'-c','project_doc_max_bytes=0'];
   persistentArgs=previous?['exec','resume',previous,'--json','--color','never','--ignore-rules','-c','sandbox_mode="read-only"',...safe,'-']
    :['exec','--sandbox','read-only','--json','--color','never','--ignore-rules',...safe,'-'];
  }else {
   persistentArgs=args.filter(arg=>arg!=='--no-session-persistence');
   if(!previous){sessionId=randomUUID();if(!files.own(sessionId,startedAt)){sessionId=null;mode='fresh';return processRun(command,args,options);}}
   persistentArgs.push(previous?'--resume':'--session-id',sessionId);
  }
  if(kind==='codex'&&!previous)unclaimed=true;
  let response;
  try{response=await processRun(command,persistentArgs,options);}catch(error){
   if(error.teardownUncertain===true){cleanupUnsafe=true;closed=true;}
   if(kind==='codex'&&!previous&&typeof error.stdout==='string'){const owned=codexAnswer({code:1,stdout:error.stdout,stderr:error.stderr},null).id;if(owned&&files.own(owned,startedAt)){sessionId=owned;unclaimed=false;}}
   throw error;
  }
  if(unavailable(response,previous)){unclaimed=false;mode='fresh';return processRun(command,args,options);}
  if(kind==='codex') {
   const parsed=codexAnswer(response,previous);
   if(parsed.id&&!previous){if(files.own(parsed.id,startedAt)){sessionId=parsed.id;unclaimed=false;}else return failure('The agent session could not be safely owned. Reconnect pdd try.');}
   return parsed.answer;
  }
  if(response.code!==0)return response;
  try{const result=JSON.parse(response.stdout);if(result.session_id!==undefined&&result.session_id!==sessionId)return failure('The resumed agent returned a different session identity.');if(result.type!=='result'||typeof result.result!=='string')return failure('The resumed agent did not return a structured result.');}
  catch{return failure('The resumed agent returned malformed structured output.');}
  return response;
 }
 async function execute(command,args,options) {
  if(!['codex','claude'].includes(kind))return processRun(command,args,options);
  if(mode==='fresh')return processRun(command,args,options);
  if(mode==='resume')return persistent(command,args,options);
  if(!provider)provider=kind==='codex'?createCodex({command,cwd:options.cwd,env:options.env,configArgs:configArgs(args),spawn,timeoutMs:options.timeoutMs,maxBytes:options.maxBytes})
   :createClaude({command,cwd:options.cwd,env:options.env,args,spawn,timeoutMs:options.timeoutMs,maxBytes:options.maxBytes});
  try{return await provider.run(options.input,{signal:options.signal,timeoutMs:options.timeoutMs,maxBytes:options.maxBytes});}
  catch(error) {
   mode='resume';await disposeWarm();
   if(!options.signal.aborted&&error.safeToFallback===true)return persistent(command,args,options);
   if(!closed&&!options.signal.aborted)error.recoverable=true;
   throw error;
  }
 }
 async function run(command,args,options={}) {
  if(closed)throw Error('The agent session is closed.');
  if(active)throw Error('An agent turn is already running.');
  if(options.signal?.aborted)throw Error('cancelled');
  if(typeof options.input!=='string'||!options.input.trim()||Buffer.byteLength(options.input)>24576||[options.timeoutMs??120000,options.maxBytes??131072].some(value=>!Number.isSafeInteger(value)||value<=0))throw Error('Invalid agent session input or limits.');
  const identity=fingerprint(command,options);if(binding&&binding!==identity)throw Error('The agent launcher settings changed. Reconnect pdd try.');binding=identity;
  controller=new AbortController();const turnController=controller;const abort=()=>turnController.abort();options.signal?.addEventListener('abort',abort,{once:true});
  let timedOut=false;const timer=setTimeout(()=>{timedOut=true;turnController.abort();},Math.min(options.timeoutMs??120000,120000));
  const bound={...options,signal:controller.signal,timeoutMs:Math.min(options.timeoutMs??120000,120000),maxBytes:Math.min(options.maxBytes??131072,131072)};
  active=execute(command,args,bound);
  try{return await active;}catch(error){if(error.teardownUncertain===true){cleanupUnsafe=true;closed=true;}if(timedOut){error=Error('Agent turn timed out.');}if(!closed&&!options.signal?.aborted&&!/rate.?limit|usage.?limit|quota|credits|capacity|not logged|not signed|sign.?in|login required|unauthorized|authentication/i.test(error.stderr||error.message))error.recoverable=true;throw error;}finally{clearTimeout(timer);options.signal?.removeEventListener('abort',abort);active=null;controller=null;}
 }
 function close() {
  if(closing)return closing;closed=true;
  closing=(async()=>{const pending=active;controller?.abort();let teardownError=false;try{await disposeWarm();}catch{teardownError=true;}await pending?.catch(()=>{});
   try{const result=files&&!cleanupUnsafe?await files.cleanup():{deleted:0,retained:0,errors:[]};if(teardownError||unclaimed||cleanupUnsafe){result.retained++;result.errors.push('An agent transcript may remain after an interrupted launch.');}return result;}catch{return {deleted:0,retained:1,errors:['An owned agent transcript could not be verified for cleanup.']};}
  })();return closing;
 }
 return {run,close};
}
