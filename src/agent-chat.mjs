// Generated from prompts/cli/agent-chat.prompt.md (sha256: 5509e41bb6322a27811ea88b5c5d58a78275999aee5f922610b922d5d478896c).
import {discoverAgents,askAgent} from './agent-adapters.mjs';
import {cleanText} from './runtime-output.mjs';
const object=x=>x!==null&&typeof x==='object'&&!Array.isArray(x);
const known=id=>['codex','claude','gemini'].includes(id);
const ready=a=>['ready','available'].includes(a?.state);
const write=(context,text)=>context.ports.stderr.write(`${cleanText(text,context.secrets)}\n`);
const json=body=>({method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});
const good=reply=>reply?.status>=200&&reply.status<300&&object(reply.json);
function scrub(value,secrets){
 if(typeof value==='string'){for(const secret of secrets??[])if(secret)value=value.split(secret).join('[redacted]');return value.replace(/\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,})\b/g,'[redacted]').replace(/Bearer\s+\S+/gi,'Bearer [redacted]');}
 if(Array.isArray(value))return value.map(v=>scrub(v,secrets));
 if(object(value))return Object.fromEntries(Object.entries(value).map(([k,v])=>[k,/token|password|secret|api[_-]?key|authorization|cookie|credential/i.test(k)?'[redacted]':scrub(v,secrets)]));
 return value;
}
export async function createAgentBridge(context,test,tryId,options={},link){
 const {ports,root,store,runtime}=context,prefix=`/v1/try/${tryId}`,bridge_id=ports.randomUUID();
 const modelReply=await runtime.send(`${prefix}/model`,{method:'GET'},30000);
 if(modelReply.status===404){write(context,'This runtime does not support Ask your agent yet. The ordinary Try link remains available.');return null;}
 if(!good(modelReply)||!Array.isArray(modelReply.json.entries))throw Error('Could not read the owner’s Try model for agent chat.');
 const model=modelReply.json,entries=model.entries.filter(e=>typeof e.entry_path==='string'&&typeof e.operation==='string'&&object(e.input_schema))
  .map(e=>({entry:`${e.entry_path}#${e.operation}`,prompt_path:e.entry_path,operation:e.operation,input_schema:e.input_schema}));
 let agents=await (ports.discoverAgents??discoverAgents)({cwd:root,env:ports.env}),choice=options['--agent']??store.repo(root).agent_choice;
 if(!known(choice)||(!options['--agent']&&agents.find(a=>a.id===choice)?.state==='not_installed'))choice=agents.find(ready)?.id??agents.find(a=>a.state!=='not_installed')?.id??'codex';
 const remember=id=>{if(!known(id))return;choice=id;const saved=store.repo(root);if(saved.agent_choice!==id)store.saveRepo(root,{...saved,agent_choice:id});};
 const connected=await runtime.send(`${prefix}/agent/connect`,json({bridge_id,agents,selected:choice}),30000);
 if(connected.status===404){write(context,'This runtime does not support Ask your agent yet. The ordinary Try link remains available.');return null;}
 if(!good(connected)||connected.json.bridge_id!==bridge_id||connected.json.connected!==true||!/^[A-Za-z0-9_-]{43,128}$/.test(connected.json.browser_key??''))throw Error('Could not connect your agent to this Try. Run pdd try again.');
 remember(choice);
 const ownerUrl=new URL(link);ownerUrl.hash=`agent=${connected.json.browser_key}`;
 let closed=false,task=null,tickTask=null,failed=false;const seen=new Set(),controller=new AbortController();
 const stop=()=>controller.abort();context.signal?.addEventListener('abort',stop,{once:true});
 if(context.signal?.aborted)stop();
 async function close(){if(closed)return;closed=true;stop();context.onAgentChatClose?.();context.signal?.removeEventListener('abort',stop);
  try{await (context.agentFinalSend??runtime.send.bind(runtime))(`${prefix}/agent/disconnect`,json({bridge_id}),5000);}catch{}
 }
 async function answer(message){
  const agent=agents.find(a=>a.id===message.agent);let result;
  if(!ready(agent))result={say:agent?.state==='signed_out'?`${agent.name} is signed out. Sign in at your terminal, or switch to another agent.`:agent?.state==='quota'?`${agent.name} has reached its usage limit. Switch to another agent.`:`${agent?.name??'This agent'} is not available. Choose an installed agent.`,fill:null};
  else result=await (ports.askAgent??askAgent)({agent:agent.id,cwd:root,env:ports.env,entries,signal:controller.signal,
   context:scrub({message:message.text,story:test.story,stories:model.stories??[],entries,current:message.context??{}},context.secrets)});
  if(controller.signal.aborted)return;
  if(result.error)agents=agents.map(a=>a.id===message.agent?{...a,state:result.error.state,detail:result.error.message}:a);
  else if(agent)agents=agents.map(a=>a.id===message.agent?{...a,state:'ready',detail:undefined}:a);
  const safe=scrub(result,context.secrets);
  const reply=await runtime.send(`${prefix}/agent/reply`,json({bridge_id,message_id:message.id,say:safe.say,fill:safe.fill??null,agents}),30000);
  if(!good(reply)||reply.json.ok!==true){failed=true;write(context,'Your agent reply could not be delivered. It will not be run again. Reconnect with pdd try.');stop();}
 }
 async function run(onTick){
  write(context,`Ask your agent is connected (${agents.find(a=>a.id===choice)?.name??choice}). Keep pdd running; Ctrl-C disconnects chat and keeps the Try open.`);
  try{while(!closed&&!controller.signal.aborted&&!context.interrupted){
   const before=ports.now();const poll=await runtime.send(`${prefix}/agent/poll?bridge_id=${bridge_id}`,{method:'GET'},25000);
   if(controller.signal.aborted||context.interrupted)break;
   if(!good(poll)||poll.json.connected!==true){failed=true;write(context,'Your agent connection ended. Run pdd try again to reconnect.');break;}
   remember(poll.json.selected);
   const message=poll.json.message;
   if(message!==null&&message!==undefined){
    if(!object(message)||typeof message.id!=='string'||message.id.length>128||typeof message.text!=='string'||message.text.length>8000||!known(message.agent)){failed=true;write(context,'The server sent an invalid agent message. Reconnect with pdd try.');break;}
    if(!seen.has(message.id)){
     if(task){failed=true;write(context,'Another agent message arrived while one was running. Reconnect with pdd try.');break;}
     seen.add(message.id);task=answer(message).catch(()=>{failed=true;write(context,'Your agent could not finish this message. It will not be run again.');stop();}).finally(()=>{task=null;});
    }
   }
   if(onTick&&!tickTask)tickTask=Promise.resolve().then(onTick).then(keep=>{if(keep===false)stop();}).catch(()=>{failed=true;write(context,'Saved Try updates could not be read. Reconnect with pdd try.');stop();}).finally(()=>{tickTask=null;});
   if(ports.now()-before<1000)await ports.sleep(1000,controller.signal);
  }}finally{await close();await task;await tickTask;}
  return failed?5:0;
 }
 return{url:ownerUrl.href,run,close};
}
