// Generated from prompts/cli/agent-codex-session.prompt.md (sha256: f7d370ecbc200eaf6a4489bb898a93e8c8042b85ff7c49766a6a2fdea282dcaf).
import {spawn as nodeSpawn} from 'node:child_process';
import {StringDecoder} from 'node:string_decoder';
const object=x=>x!==null&&typeof x==='object'&&!Array.isArray(x);
const id=x=>typeof x==='string'&&x.length>0;
const limit=x=>Number.isSafeInteger(x)&&x>0&&x<=16777216;
function byteClip(text,max){let out='',bytes=0;for(const c of text){const size=Buffer.byteLength(c);if(bytes+size>max)break;out+=c;bytes+=size;}return out;}
function failure(message,safe=false){return Object.assign(new Error(message),{safeToFallback:safe});}
export function createCodexSession({command,cwd,env,configArgs=[],spawn=nodeSpawn,timeoutMs=120000,maxBytes=131072}={}) {
 let child=null,thread=null,nextId=0,active=null,dead=null,submitted=false,closing=null,buffer='',decoder=new StringDecoder('utf8'),idleBytes=0;
 const waiting=new Map();let childClosed=Promise.resolve();
 function send(value){if(!child||dead)throw dead??failure('Codex session is unavailable.');child.stdin.write(JSON.stringify(value)+'\n');}
 function terminate(){
  if(closing)return closing;
  closing=(async()=>{if(!child)return;const target=child;try{target.stdin.end();}catch{}
   const kill=signal=>{if(process.platform!=='win32'&&Number.isInteger(target.pid)){try{process.kill(-target.pid,signal);return;}catch{}}try{target.kill(signal);}catch{}};
   kill('SIGTERM');await new Promise(resolve=>setTimeout(resolve,100));kill('SIGKILL');
   let timer;await Promise.race([childClosed,new Promise(resolve=>{timer=setTimeout(resolve,250);})]);clearTimeout(timer);
  })();return closing;
 }
 function stop(error){if(dead)return;if(!error.stderr)error.stderr=byteClip(active?.stderr??'',active?.maxBytes??maxBytes);dead=error;for(const pending of waiting.values())pending.reject(error);waiting.clear();if(active)active.reject(error);void terminate();}
 function protocol(message='Codex returned an unsupported protocol.'){stop(failure(message,!submitted));}
 function rpc(method,params){return new Promise((resolve,reject)=>{if(dead){reject(dead);return;}const requestId=++nextId;waiting.set(requestId,{resolve,reject});try{send({id:requestId,method,params});}catch{stop(failure('Codex transport failed.'));}});}
 function providerError(detail,fallback){const text=typeof detail?.message==='string'?detail.message:'';const cap=active?.maxBytes??maxBytes;const error=failure(byteClip(text||fallback,cap));error.stderr=byteClip([text,active?.stderr].filter(Boolean).join('\n'),cap);return error;}
 function settleTurn(){const a=active;if(!a?.turnId||!a.completed)return;if(a.completed.status!=='completed'||a.completed.error){stop(providerError(a.completed.error,'Codex turn did not complete successfully.'));return;}if(a.final===null){stop(failure('Codex completed without a final answer.'));return;}a.resolve({code:0,stdout:a.final,stderr:a.stderr+a.stderrDecoder.end()});}
 function notification(message){const a=active;if(!a||!submitted)return;const p=message.params;
  if(!object(p)||p.threadId!==thread)return;
  if(!a.turnId){if(a.early.length>=256){stop(failure('Codex sent too many early events.'));return;}a.early.push(message);return;}
  const turnId=message.method==='turn/completed'?p.turn?.id:p.turnId;
  if(turnId!==a.turnId)return;
  if(message.method==='item/started'||message.method==='item/completed'){
   const item=p.item;if(!object(item)){protocol();return;}
   if(!['userMessage','agentMessage','reasoning','plan','contextCompaction'].includes(item.type)){stop(failure('Codex attempted an unavailable tool.'));return;}
   if(message.method==='item/completed'&&item.type==='agentMessage'&&item.phase!=='commentary'){
    if(typeof item.text!=='string'){protocol();return;}a.final=item.text;
   }
  }
  if(message.method==='turn/completed'){if(!object(p.turn)||!id(p.turn.status)){protocol();return;}a.completed=p.turn;settleTurn();}
  if(message.method==='error'){stop(providerError(p.error,'Codex reported a turn error.'));}
 }
 function receive(message){
  if(dead)return;
  if(!object(message)){protocol();return;}
  if(typeof message.method==='string'){
   if(Object.hasOwn(message,'id')){
    const method=message.method;let response;
    if(['item/commandExecution/requestApproval','item/fileChange/requestApproval'].includes(method))response={result:{decision:'decline'}};
    else if(['execCommandApproval','applyPatchApproval'].includes(method))response={result:{decision:'abort'}};
    else if(method==='item/permissions/requestApproval')response={result:{permissions:{},scope:'turn'}};
    else response={error:{code:-32601,message:'Method not available.'}};
    try{send({id:message.id,...response});}catch{}stop(failure('Codex requested an unavailable capability.'));return;
   }
   notification(message);return;
  }
  if(!Object.hasOwn(message,'id')){protocol();return;}
  const pending=waiting.get(message.id);if(!pending)return;
  waiting.delete(message.id);
  if(object(message.error)){const safe=!submitted&&[-32601,-32602].includes(message.error.code);const error=failure('Codex rejected a protocol request.',safe);pending.reject(error);stop(error);return;}
  if(!Object.hasOwn(message,'result')){const error=failure('Codex returned an unsupported protocol.',!submitted);pending.reject(error);stop(error);return;}
  pending.resolve(message.result);
 }
 function start(){
  if(child)return;
  try{child=spawn(command,['app-server',...configArgs],{cwd,env,stdio:['pipe','pipe','pipe'],detached:process.platform!=='win32',windowsHide:true});}
  catch(error){stop(failure('Codex could not start.',['ENOENT','EACCES'].includes(error.code)&&!submitted));throw dead;}
  childClosed=new Promise(resolve=>child.once('close',resolve));
  child.stdin.on('error',()=>stop(failure('Codex input closed unexpectedly.')));
  child.on('error',error=>stop(failure('Codex could not start.',['ENOENT','EACCES'].includes(error.code)&&!submitted)));
  child.on('close',()=>{if(!dead){const first=(active?.stderr??'').split(/\r?\n/).map(x=>x.trim()).find(Boolean)??'';const unsupported=!submitted&&/^(?:error:\s*)?(?:unrecognized subcommand|unknown (?:subcommand|command)|unsupported (?:subcommand|command))\s+['"`]?app-server(?:['"`]|\s|$)/i.test(first);stop(failure('Codex exited before completing the session.',unsupported));}});
  child.stdout.on('data',chunk=>{
   if(dead)return;if(!account(chunk.length))return;
   buffer+=decoder.write(chunk);let newline;
   while(!dead&&(newline=buffer.indexOf('\n'))>=0){const line=buffer.slice(0,newline);buffer=buffer.slice(newline+1);if(!line.trim())continue;let message;try{message=JSON.parse(line);}catch{protocol();return;}receive(message);}
  });
  child.stderr.on('data',chunk=>{if(dead||!account(chunk.length))return;if(active)active.stderr+=active.stderrDecoder.write(chunk);});
 }
 function account(bytes){if(active){active.bytes+=bytes;if(active.bytes>active.maxBytes){stop(failure('Codex output exceeded its limit.'));return false;}}else {idleBytes+=bytes;if(idleBytes>maxBytes){stop(failure('Codex idle output exceeded its limit.'));return false;}}return true;}
 async function initialize(){
  start();await rpc('initialize',{clientInfo:{name:'pdd',title:'pdd Try guide',version:'0.1.9'}});send({method:'initialized'});
  const result=await rpc('thread/start',{cwd,sandbox:'read-only',approvalPolicy:'never',ephemeral:true,config:{project_doc_max_bytes:0}});
  if(!object(result)||!id(result.thread?.id)||result.thread.ephemeral!==true||!(result.sandbox==='read-only'||object(result.sandbox)&&result.sandbox.type==='readOnly'&&result.sandbox.networkAccess!==true)||result.approvalPolicy!=='never'){protocol('Codex did not start a read-only ephemeral thread.');throw dead;}
  thread=result.thread.id;
 }
 async function run(input,{signal,timeoutMs:turnTimeout=timeoutMs,maxBytes:turnMax=maxBytes}={}){
  if(dead)throw dead;if(active)throw failure('A Codex turn is already active.');
  if(typeof command!=='string'||!command||!Array.isArray(configArgs)||configArgs.some(x=>typeof x!=='string')||typeof input!=='string'||!limit(turnTimeout)||!limit(turnMax)||Buffer.byteLength(input)>turnMax)throw failure('Invalid Codex session input.');
  if(signal?.aborted){stop(failure('Codex turn was cancelled.'));throw dead;}
  let resolve,reject;const finished=new Promise((ok,no)=>{resolve=ok;reject=no;});
  // The rejection handler is attached before startup, which may fail synchronously.
  finished.catch(()=>{});
  const state={resolve,reject,stderr:'',stderrDecoder:new StringDecoder('utf8'),bytes:0,maxBytes:turnMax,turnId:null,early:[],final:null,completed:null};active=state;idleBytes=0;
  const abort=()=>stop(failure('Codex turn was cancelled.'));
  signal?.addEventListener('abort',abort,{once:true});
  const timer=setTimeout(()=>stop(failure('Codex turn timed out.')),turnTimeout);
  void (async()=>{try{
   if(!thread)await initialize();if(dead)throw dead;
   submitted=true;
   const result=await rpc('turn/start',{threadId:thread,input:[{type:'text',text:input}]});
   if(!id(result?.turn?.id)){protocol();return;}state.turnId=result.turn.id;
   for(const event of state.early.splice(0))notification(event);
   settleTurn();
  }catch(error){stop(error?.safeToFallback!==undefined?error:failure('Codex session failed.'));}})();
  try{return await finished;}finally{clearTimeout(timer);signal?.removeEventListener('abort',abort);if(active===state)active=null;if(dead)await terminate();}
 }
 async function close(){if(!dead)stop(failure('Codex session was closed.'));await terminate();}
 return {run,close};
}
