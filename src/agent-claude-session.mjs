// Generated from prompts/cli/agent-claude-session.prompt.md (sha256: 06ac33eede4692897f55516997829d77b49c67008875aee6ba4d1392cfe1db67).
import {spawn as nativeSpawn} from 'node:child_process';
import {randomUUID} from 'node:crypto';
import {StringDecoder} from 'node:string_decoder';
const object=x=>x!==null&&typeof x==='object'&&!Array.isArray(x);
const defaults=['-p','--safe-mode','--tools','Read,Grep,Glob','--permission-mode','plan','--permission-prompts','none','--strict-mcp-config','--no-chrome','--no-session-persistence'];
function warmArgs(given){
 const args=given.length?[...given]:[...defaults];
 const seen=new Set(),valued=new Set(['--tools','--permission-mode','--permission-prompts','--input-format','--output-format']),flags=new Set(['-p','--print','--safe-mode','--strict-mcp-config','--no-chrome','--no-session-persistence','--verbose']);
 for(let i=0;i<args.length;i++){
  const key=args[i];if(!valued.has(key)&&!flags.has(key))throw issue('Unsupported Claude startup argument.');
  const identity=key==='--print'?'-p':key;if(seen.has(identity))throw issue('Duplicate Claude startup argument.');seen.add(identity);
  if(valued.has(key)){if(typeof args[i+1]!=='string'||args[i+1].startsWith('-'))throw issue('Missing Claude startup argument value.');i++;}
 }
 const option=flag=>args[args.indexOf(flag)+1];
 if(!(args.includes('-p')||args.includes('--print'))||!['--safe-mode','--strict-mcp-config','--no-chrome','--no-session-persistence'].every(f=>args.includes(f))||option('--permission-mode')!=='plan'||option('--permission-prompts')!=='none'||option('--tools')!=='Read,Grep,Glob'||args.some(f=>/dangerously-skip|permission-prompt-tool|--resume|--continue/.test(f)))throw issue('Claude warm session requires the existing restricted print arguments.');
 const result=[];
 for(let i=0;i<args.length;i++){if(['--input-format','--output-format'].includes(args[i])){i++;continue;}if(/^--(?:input|output)-format=/.test(args[i]))continue;result.push(args[i]);}
 result.push('--input-format','stream-json','--output-format','stream-json');if(!result.includes('--verbose'))result.push('--verbose');return result;
}
function issue(message,safeToFallback=false,stderr=''){return Object.assign(new Error(message),{safeToFallback,stderr});}
const bound=(n,label)=>{if(!Number.isInteger(n)||n<1||n>2147483647)throw issue(`Invalid Claude ${label} limit.`);return n;};
export function createClaudeSession({command='claude',cwd,env=process.env,args=[],spawn=nativeSpawn,timeoutMs=120000,maxBytes=131072}={}){
 if(typeof command!=='string'||!command||!Array.isArray(args)||args.some(a=>typeof a!=='string'))throw issue('Invalid Claude session configuration.');
 const terminalIds=new Set();
 const argv=warmArgs(args);bound(timeoutMs,'timeout');bound(maxBytes,'output');
 let child=null,active=null,dead=false,ready=false,submittedEver=false,sessionId=null,initId=null,buffer='',idleBytes=0,decoder=new StringDecoder('utf8'),stderrDecoder=new StringDecoder('utf8'),closing=null,resolveExit=null,exitPromise=null,killTimer=null,exited=false;
 const unsupported=()=>!submittedEver&&/^(?:error:\s*)?(?:unknown|unrecognized|unsupported|invalid) (?:option|argument|input format|output format|request|control request)[^\n]*(?:stream-json|--input-format|--output-format|initialize)/im.test(active?.stderr??'');
 function signalChild(signal){if(!child)return;try{if(process.platform!=='win32'&&Number.isInteger(child.pid)&&child.pid>1)process.kill(-child.pid,signal);else if(!exited)child.kill(signal);}catch{try{child.kill(signal);}catch{}}}
 function stop(){if(!child)return;try{child.stdin.end();}catch{}signalChild('SIGTERM');if(!killTimer){killTimer=setTimeout(()=>signalChild('SIGKILL'),500);killTimer.unref();}}
 function finish(error,value){const turn=active;if(!turn)return;active=null;clearTimeout(turn.timer);turn.signal?.removeEventListener('abort',turn.abort);if(error)turn.reject(error);else turn.resolve(value);}
 function fail(message,safe=false){if(dead)return;dead=true;const stderr=active?.stderr??'';finish(issue(message,safe,stderr));stop();}
 function write(row){try{child.stdin.write(JSON.stringify(row)+'\n',error=>{if(error)fail('Claude input stream failed.');});}catch{fail('Claude input stream failed.');}}
 function submit(){if(!active||dead||!ready)return;active.submitted=true;submittedEver=true;write({type:'user',message:{role:'user',content:active.input},parent_tool_use_id:null,session_id:sessionId??'',uuid:randomUUID(),client_composed:true});}
 function deny(row){
  const id=row.request_id,request=row.request;
  if(typeof id!=='string'||!id||!object(request)){fail('Malformed Claude control request.');return;}
  if(request.subtype==='can_use_tool'){
   write({type:'control_response',response:{subtype:'success',request_id:id,response:{behavior:'deny',message:'This Try chat never grants tool permission.'}}});
   if(!['Read','Grep','Glob'].includes(request.tool_name))fail('Claude requested an unavailable tool.');
  }else{
   write({type:'control_response',response:{subtype:'error',request_id:id,error:'Unsupported control request in read-only Try chat.'}});fail('Claude requested an unsupported control operation.');
  }
 }
 function frame(row){
  if(!object(row)||typeof row.type!=='string'){fail('Malformed Claude stream frame.');return;}
  if(row.type==='control_request'){deny(row);return;}
  if(row.type==='control_response'){
   const r=row.response;if(ready||!active||!object(r)||r.request_id!==initId){fail('Unexpected Claude initialization response.');return;}
   if(r.subtype!=='success'){const unsupportedInit=typeof r.error==='string'&&/unsupported|unknown|unrecognized/i.test(r.error)&&/initializ|control|protocol/i.test(r.error);fail('Claude streaming initialization failed.',!submittedEver&&unsupportedInit);return;}
   ready=true;submit();return;
  }
  if(typeof row.session_id==='string'&&row.session_id){if(sessionId&&row.session_id!==sessionId){fail('Claude changed the private session identity.');return;}sessionId=row.session_id;}
  if(row.type==='result'){
   if(!active?.submitted||active.terminal){fail('Unexpected Claude terminal result.');return;}
   if(typeof row.session_id!=='string'||!row.session_id||typeof row.is_error!=='boolean'||(!row.is_error&&typeof row.result!=='string')){fail('Malformed Claude terminal result.');return;}
   if(typeof row.uuid==='string'){if(terminalIds.has(row.uuid)||terminalIds.size>=256){fail('Claude terminal result identity was replayed or exhausted.');return;}terminalIds.add(row.uuid);}
   const turn=active;turn.terminal=true;
   queueMicrotask(()=>{if(dead||active!==turn)return;if(buffer.trim()){fail('Trailing partial Claude frame after terminal result.');return;}const value={code:0,stdout:JSON.stringify(row),stderr:turn.stderr};finish(null,value);if(row.is_error){dead=true;stop();}});return;
  }
  if(!['system','assistant','user','stream_event','tool_progress','tool_use_summary','rate_limit_event','auth_status'].includes(row.type)){fail('Unknown Claude stream frame.');return;}
  if(row.type==='assistant'){
   const content=row.message?.content;
   if(content!==undefined&&!Array.isArray(content)){fail('Malformed Claude assistant frame.');return;}
   for(const block of content??[])if(block?.type==='tool_use'&&!['Read','Grep','Glob'].includes(block.name)){fail('Claude emitted an unavailable tool.');return;}
  }
  if(row.type==='stream_event'&&row.event?.content_block?.type==='tool_use'&&!['Read','Grep','Glob'].includes(row.event.content_block.name)){fail('Claude streamed an unavailable tool.');}
 }
 function data(kind,chunk){
  if(dead)return;const bytes=Buffer.byteLength(chunk);const limit=active?.limit??maxBytes;
  if(active){active.bytes+=bytes;if(active.bytes>limit){fail('Claude turn output limit exceeded.');return;}}
  else{idleBytes+=bytes;if(idleBytes>limit){fail('Claude idle output limit exceeded.');return;}}
  if(kind==='stderr'){const text=stderrDecoder.write(chunk);if(active)active.stderr+=text;return;}
  buffer+=decoder.write(chunk);
  let newline;while(!dead&&(newline=buffer.indexOf('\n'))>=0){const line=buffer.slice(0,newline).replace(/\r$/,'');buffer=buffer.slice(newline+1);if(!line.trim())continue;let row;try{row=JSON.parse(line);}catch{fail('Malformed Claude streaming JSON.');return;}frame(row);}
 }
 function start(){
  try{child=spawn(command,argv,{cwd,env,stdio:['pipe','pipe','pipe'],shell:false,detached:process.platform!=='win32'});}catch{fail('Claude session could not start.');return;}
  exitPromise=new Promise(resolve=>{resolveExit=resolve;});
  child.stdout.on('data',c=>data('stdout',c));child.stderr.on('data',c=>data('stderr',c));
  child.stdin.on('error',()=>fail('Claude input stream failed.'));
  child.on('error',()=>fail('Claude session could not start.'));
  child.on('close',()=>{exited=true;resolveExit?.();if(!dead)fail('Claude session exited before completing the turn.',unsupported());});
  initId=randomUUID();write({type:'control_request',request_id:initId,request:{subtype:'initialize',hooks:null}});
 }
 async function run(input,{signal,timeoutMs:turnTimeout=timeoutMs,maxBytes:limit=maxBytes}={}){
  if(dead)throw issue('Claude session is closed.');if(active)throw issue('A Claude turn is already active.');
  if(typeof input!=='string')throw issue('Claude input must be text.');bound(turnTimeout,'timeout');bound(limit,'output');if(signal?.aborted)throw issue('Claude turn cancelled.');
  return new Promise((resolve,reject)=>{
   const turn={resolve,reject,input,limit,signal,bytes:0,stderr:'',submitted:false,terminal:false};active=turn;idleBytes=0;
   turn.abort=()=>fail('Claude turn cancelled.');signal?.addEventListener('abort',turn.abort,{once:true});turn.timer=setTimeout(()=>fail('Claude turn timed out.'),turnTimeout);
   if(!child)start();else if(ready)submit();
  });
 }
 async function close(){
  if(closing)return closing;dead=true;finish(issue('Claude session closed.'));stop();
  closing=(async()=>{if(exitPromise&&!exited){let timer;await Promise.race([exitPromise,new Promise(r=>{timer=setTimeout(r,650);})]);clearTimeout(timer);}clearTimeout(killTimer);signalChild('SIGKILL');})();return closing;
 }
 return Object.freeze({run,close});
}
