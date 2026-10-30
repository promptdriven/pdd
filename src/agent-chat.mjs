// Generated from prompts/cli/agent-chat.prompt.md (sha256: efcefafc9ee05a7cb82c766d9c2fdf8161a11682000ec00298eb66d47afd0646).
import {discoverAgents,askAgent} from './agent-adapters.mjs';
import {loadAgentDefinitions} from './agent-config.mjs';
import {createTryGuide} from './agent-guide.mjs';
import {cleanText} from './runtime-output.mjs';
const object=x=>x!==null&&typeof x==='object'&&!Array.isArray(x);
const FEATURES=['apply','progress','run_events','expect','save','run'];
const ready=a=>['ready','available'].includes(a?.state);
const write=(context,text)=>context.ports.stderr.write(`${cleanText(text,context.secrets)}\n`);
const json=body=>({method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});
const good=reply=>reply?.status>=200&&reply.status<300&&object(reply.json);
// Why a relay request failed, for the terminal: the network cause, else the server's message, else the HTTP status.
const why=reply=>reply?.unreachable??cleanText(reply?.json?.error?.message??reply?.why??(reply?.status?`HTTP ${reply.status}`:'no answer'));
function scrub(value,secrets){
 if(typeof value==='string'){for(const secret of secrets??[])if(secret)value=value.split(secret).join('[redacted]');return value.replace(/\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,})\b/g,'[redacted]').replace(/Bearer\s+\S+/gi,'Bearer [redacted]');}
 if(Array.isArray(value))return value.map(v=>scrub(v,secrets));
 if(object(value))return Object.fromEntries(Object.entries(value).map(([k,v])=>[k,/token|password|secret|api[_-]?key|authorization|cookie|credential/i.test(k)?'[redacted]':scrub(v,secrets)]));
 return value;
}
export async function createAgentBridge(context,test,tryId,options={},link){
 const definitions=context.agentDefinitions??loadAgentDefinitions({cwd:context.root,env:context.ports.env});
 if(!definitions.length)throw Error('No agents are configured. Add an agent or enable defaults in agents.json.');
 const known=id=>definitions.some(d=>d.id===id),byChoice=value=>definitions.find(d=>d.name===value)??definitions.find(d=>['codex','claude','gemini'].includes(d.id)&&d.id===value);
 const explicit=options['--agent']!==undefined?byChoice(options['--agent']):null;
 if(options['--agent']!==undefined&&!explicit)throw Error('Unknown agent name. Choose a name from agents.json or an enabled default.');
 const {ports,root,store,runtime}=context,prefix=`/v1/try/${tryId}`,bridge_id=ports.randomUUID();
 write(context,'Connecting your agent to the Try page…');
 const modelReply=await runtime.send(`${prefix}/model`,{method:'GET'},30000);
 if(modelReply.status===404){write(context,'This interpreter does not support Ask your agent yet. The ordinary Try link remains available.');return null;}
 if(!good(modelReply)||!Array.isArray(modelReply.json.entries))throw Error(`Could not read the owner’s Try model for agent chat (${why(modelReply)}). Run pdd try again.`);
 const model=modelReply.json,entries=model.entries.filter(e=>typeof e.entry_path==='string'&&typeof e.operation==='string'&&object(e.input_schema))
  .map(e=>({entry:`${e.entry_path}#${e.operation}`,prompt_path:e.entry_path,operation:e.operation,input_schema:e.input_schema,...Object.fromEntries(['label','name','cli','http'].filter(k=>Object.hasOwn(e,k)).map(k=>[k,e[k]]))}));
 const discovered=await (ports.discoverAgents??discoverAgents)({cwd:root,env:ports.env,definitions});
 let agents=definitions.map(d=>{const found=discovered.find(a=>a.id===d.id);return{id:d.id,name:d.name,state:found?.state??'error',...(typeof found?.detail==='string'?{detail:found.detail}:{})};});
 let choice=(explicit??byChoice(store.repo(root).agent_choice))?.id;
 if(!known(choice)||(!explicit&&agents.find(a=>a.id===choice)?.state==='not_installed'))choice=agents.find(ready)?.id??agents.find(a=>a.state!=='not_installed')?.id??definitions[0].id;
 const remember=id=>{if(!known(id))return;choice=id;const name=definitions.find(d=>d.id===id).name,saved=store.repo(root);if(saved.agent_choice!==name)store.saveRepo(root,{...saved,agent_choice:name});};
 const connected=await runtime.send(`${prefix}/agent/connect`,json({bridge_id,agents,selected:choice,features:FEATURES}),30000);
 if(connected.status===404){write(context,'This interpreter does not support Ask your agent yet. The ordinary Try link remains available.');return null;}
 if(!good(connected)||connected.json.bridge_id!==bridge_id||connected.json.connected!==true||!/^[A-Za-z0-9_-]{43,128}$/.test(connected.json.browser_key??''))throw Error(`Could not connect your agent to this Try (${why(connected)}). Run pdd try again.`);
 remember(choice);
 const features=Array.isArray(connected.json.features)?connected.json.features.slice(0,32).filter(x=>FEATURES.includes(x)):[];
 const secretName=/token|password|secret|api[_-]?key|authorization|cookie|credential/i;
 const secrets=[...(context.secrets??[]),...Object.entries(ports.env??{}).filter(([k,v])=>secretName.test(k)&&typeof v==='string'&&v).map(([,v])=>v),...definitions.flatMap(d=>Object.entries(d.env??{}).filter(([k,v])=>secretName.test(k)&&typeof v==='string'&&v).map(([,v])=>v))];
 const guide=createTryGuide({root,env:ports.env,model,test,features,secrets,ports:ports.guidePorts});
 const onSaved=record=>guide.saved(record);context.onAgentCaseSaved=onSaved;
 const ownerUrl=new URL(link);ownerUrl.hash=`agent=${connected.json.browser_key}`;
 let closed=false,task=null,tickTask=null,failed=false;const seen=new Set(),controller=new AbortController();
 const stop=()=>controller.abort();context.signal?.addEventListener('abort',stop,{once:true});
 if(context.signal?.aborted)stop();
 async function close(){if(closed)return;closed=true;stop();guide.close();if(context.onAgentCaseSaved===onSaved)delete context.onAgentCaseSaved;context.onAgentChatClose?.();context.signal?.removeEventListener('abort',stop);
  try{await (context.agentFinalSend??runtime.send.bind(runtime))(`${prefix}/agent/disconnect`,json({bridge_id}),5000);}catch{}
 }
 async function answer(message){
  const agent=agents.find(a=>a.id===message.agent),name=agent?.name??'Your agent',turn=guide.prepare(message);let result,asked=false;
  if(turn.fast)result=turn.fast;
  else if(!ready(agent))result={say:agent?.state==='signed_out'?`${agent.name} is signed out. Sign in at your terminal, or switch to another agent.`:agent?.state==='quota'?`${agent.name} has reached its usage limit. Switch to another agent.`:`${agent?.name??'This agent'} is not available. Choose an installed agent.`,fill:null};
  else {asked=true;write(context,`${name} is answering a question from the Try page…`);result=await (ports.askAgent??askAgent)({agent:agent.id,definition:definitions.find(d=>d.id===agent.id),cwd:root,env:ports.env,entries,signal:controller.signal,supportsApply:features.includes('apply'),supportsRun:features.includes('run'),context:turn.context});}
  if(controller.signal.aborted)return;
  if(turn.fast)write(context,'PDD checked the run against the local test cases.');
  else write(context,result.error||!ready(agent)?`${name} could not answer: ${result.error?.message??result.say}`:`${name} answered.${result.fill?' It proposed input for the form.':''}`);
  if(result.error)agents=agents.map(a=>a.id===message.agent?{...a,state:result.error.state,detail:result.error.message}:a);
  else if(asked&&agent)agents=agents.map(a=>a.id===message.agent?{...a,state:'ready',detail:undefined}:a);
  const decorated=guide.decorate(result),safe=guide.wire(decorated);
  const reply=await runtime.send(`${prefix}/agent/reply`,json({bridge_id,message_id:message.id,...safe,agents:scrub(agents,secrets)}),30000);
  if(!good(reply)||reply.json.ok!==true){failed=true;write(context,'Your agent reply could not be delivered. It will not be run again. Reconnect with pdd try.');stop();}
  else guide.delivered(message,decorated);
 }
 async function run(onTick){
  write(context,`Ask your agent is connected (${agents.find(a=>a.id===choice)?.name??choice}). Keep this window open for Ask your agent; Ctrl-C disconnects the chat and keeps the Try open.`);
  try{while(!closed&&!controller.signal.aborted&&!context.interrupted){
   const before=ports.now();const poll=await runtime.send(`${prefix}/agent/poll?bridge_id=${bridge_id}`,{method:'GET'},25000);
   if(controller.signal.aborted||context.interrupted)break;
   if(!good(poll)||poll.json.connected!==true){failed=true;write(context,'Your agent connection ended. Run pdd try again to reconnect.');break;}
   remember(poll.json.selected);
   const message=poll.json.message;
   if(message!==null&&message!==undefined){
    if(!object(message)||typeof message.id!=='string'||message.id.length>128||typeof message.text!=='string'||message.text.length>8000||!known(message.agent)||(message.kind!==undefined&&!['chat','run','walk','own'].includes(message.kind))){failed=true;write(context,'The server sent an invalid agent message. Reconnect with pdd try.');break;}
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
