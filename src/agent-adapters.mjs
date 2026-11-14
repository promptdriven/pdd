// Generated from prompts/cli/agent-adapters.prompt.md (sha256: b4ca499ce3b8af0f5d894cb75554c87bfce1445f6b8e6a1ba1640c7bb26d2a1e).
import { spawn } from 'node:child_process';
import { lstatSync, statSync } from 'node:fs';
import { delimiter, resolve, isAbsolute } from 'node:path';
import { loadAgentDefinitions } from './agent-config.mjs';
import { runtimeWorkspaceSlice, workspace } from './runtime-seam.mjs';
runtimeWorkspaceSlice();
const AGENTS = [['codex','Codex'],['claude','Claude'],['gemini','Gemini']];
const TIER_PROFILES = {
 codex:{worker:{model:'gpt-5.4-mini',reasoningEffort:'medium'},reviewer:{model:'gpt-5.4',reasoningEffort:'high'}},
 claude:{worker:{model:'claude-sonnet-4-6',reasoningEffort:'medium'},reviewer:{model:'claude-opus-4-6',reasoningEffort:'high'}},
 gemini:{worker:{model:'gemini-2.5-flash',reasoningEffort:'medium'},reviewer:{model:'gemini-2.5-pro',reasoningEffort:'high'}},
 agy:{worker:{model:'gemini-2.5-flash',reasoningEffort:'medium'},reviewer:{model:'gemini-2.5-pro',reasoningEffort:'high'}},
};
const WORKER_STEPS = new Set(['intake','triage','sort','dependencies','improve','groom','clarify','small-change','worker','story','story/pr1','pr1','prompt','prompts','code','code/pr2','pr2','implement','build','repair','fix','rebase','base-refresh','conflict']);
const REVIEWER_STEPS = new Set(['review','check','independent-review','audit','merge','publish']);
const VALID_EFFORTS = new Set(['low','medium','high','xhigh']);
// A configured credential is not a successful provider request; never expose the status payload.
export function parseAgentAuthStatus({agent,result} = {}) {
 if(!result||!Number.isInteger(result.code)||typeof result.stdout!=='string'||typeof result.stderr!=='string')return 'unavailable';
 if(agent==='claude'){
  try{const value=JSON.parse(result.stdout);if(value?.loggedIn===true&&result.code===0)return 'ready';if(value?.loggedIn===false&&[0,1].includes(result.code))return 'signed_out';}catch{}
  return 'unavailable';
 }
 if(agent!=='codex')return 'unavailable';
 const text=`${result.stdout}\n${result.stderr}`.replace(/\x1b\[[0-?]*[ -/]*[@-~]/g,'');
 const negative=/\bnot\s+(?:logged|signed)\s+in\b|\b(?:login|sign[ -]?in)\s+required\b/i.test(text);
 const affirmative=text.replace(/\bnot\s+(?:logged|signed)\s+in\b/gi,'');
 const positive=/\blogged in\b|\bapi key configured\b/i.test(affirmative);
 if(positive&&negative)return 'unavailable';
 if([0,1].includes(result.code)&&negative)return 'signed_out';
 return result.code===0&&positive?'ready':'unavailable';
}
function executableMissing(command,{cwd,env}={}) {
 try{
  const directory=cwd??process.cwd(),childEnv=env??process.env;
  if(!statSync(directory).isDirectory())return false;
  const pathKey=process.platform==='win32'?Object.keys(childEnv).find(key=>key.toLowerCase()==='path'):(Object.hasOwn(childEnv,'PATH')?'PATH':undefined);
  const search=pathKey===undefined?(process.platform==='win32'?process.env.PATH??'':'/usr/bin:/bin'):childEnv[pathKey];
  const qualified=isAbsolute(command)||/[\\/]/.test(command);
  const endings=process.platform==='win32'?['',...(childEnv.PATHEXT??'.COM;.EXE;.BAT;.CMD').split(';')]:[''];
  const candidates=qualified?[resolve(directory,command)]:(search??'').split(delimiter).flatMap(folder=>endings.map(ending=>resolve(directory,folder||'.',command+ending)));
  for(const file of candidates){try{lstatSync(file);return false;}catch(error){if(error.code!=='ENOENT')return false;}}
  return true;
 }catch{return false;}
}
export function runAgentProcess(command,args,{cwd,env,input='',signal,timeoutMs=120000,maxBytes=131072}={}) {
 return new Promise((resolve,reject)=>{
  if(signal?.aborted){reject(new Error('cancelled'));return;}
  let child,stdout='',stderr='',size=0,settled=false,killTimer,stopping=false;
  const stop=()=>{if(!child)return;stopping=true;try{process.kill(-child.pid,'SIGTERM');}catch{child.kill('SIGTERM');}killTimer=setTimeout(()=>{try{process.kill(-child.pid,'SIGKILL');}catch{child.kill('SIGKILL');}},500);killTimer.unref();};
  const finish=(error,code)=>{if(settled)return;settled=true;clearTimeout(timer);signal?.removeEventListener('abort',abort);if(error){if(error.code==='ENOENT')error.executableMissing=executableMissing(command,{cwd,env});if(error.stdout===undefined)error.stdout=stdout;error.stderr=stderr;reject(error);}else resolve({code,stdout,stderr});};
  const abort=()=>{stop();finish(new Error('cancelled'));};
  const timer=setTimeout(()=>{stop();finish(new Error('timeout'));},timeoutMs);
  try{child=spawn(command,args,{cwd,env,stdio:['pipe','pipe','pipe'],shell:false,detached:process.platform!=='win32'});}catch(e){finish(e);return;}
  signal?.addEventListener('abort',abort,{once:true});
  const data=(kind,chunk)=>{size+=chunk.length;if(size>maxBytes){stop();finish(new Error('output limit'));return;}if(kind==='stdout')stdout+=chunk;else stderr+=chunk;};
  child.stdout.on('data',c=>data('stdout',c));child.stderr.on('data',c=>data('stderr',c));child.on('error',e=>finish(e));child.on('close',code=>{if(!stopping)clearTimeout(killTimer);finish(null,code);});child.stdin.on('error',()=>{});child.stdin.end(input);
 });
}
function geminiCapabilityError(help) {
 if(help.code!==0)return 'Gemini Try read-only capability discovery failed (--help).';
 const missing=['--approval-mode','--admin-policy','--extensions','--allowed-mcp-server-names','--output-format'].find(flag=>!help.stdout.includes(flag));
 return missing?`Gemini Try read-only mode requires ${missing}; update Gemini CLI.`:null;
}
export async function discoverAgents({cwd=process.cwd(),env=process.env,run=runAgentProcess,definitions}={}) {
 if((arguments[0]?.workspace??workspace.policy({root:cwd})).configured)return (arguments[0].definitions??AGENTS.map(([id,name])=>({id,name}))).map(d=>({id:d.id,name:d.name,state:'error',detail:'Bounded agent connection is unavailable: packet-only context cannot be established.'}));
 const result=[];
 for(const {id,name,kind,command,env:overrides} of definitions??loadAgentDefinitions({cwd,env})){
  const childEnv={...env,...overrides},opts={cwd,env:childEnv,timeoutMs:10000,maxBytes:131072};
  try{
   const help=await run(command,['--help'],opts);
   if(kind==='gemini'){const detail=geminiCapabilityError(help);result.push({id,name,state:detail?'error':'available',detail:detail||'Installed; sign-in is checked when you send a message.'});continue;}
   if(help.code!==0){result.push({id,name,state:'error',detail:'The agent help command failed.'});continue;}
   const flags=kind==='codex'?['--sandbox']:['--safe-mode','--tools','--permission-prompts'];
   if(flags.some(f=>!help.stdout.includes(f))){result.push({id,name,state:'error',detail:'Update this agent to a version with the required read-only controls.'});continue;}
   const auth=await run(command,kind==='codex'?['login','status']:['auth','status','--json'],{...opts,maxBytes:16384});
   const state=parseAgentAuthStatus({agent:kind,result:auth});
   result.push({id,name,state:state==='unavailable'?'error':state});
  }catch(e){result.push({id,name,state:e.code==='ENOENT'&&e.executableMissing===true?'not_installed':'error'});}
 }
 return result;
}
function checkModel(model) {
 if(model===undefined||model===null||model==='')return null;
 if(typeof model!=='string'||!model.length||model!==model.trim()||/^-|[\x00-\x1f\x7f]/.test(model))throw new Error('Invalid model name: must be nonblank without control characters or a leading dash.');
 return model;
}
function checkEffort(effort) {
 if(effort===undefined||effort===null||effort==='')return null;
 const clean=String(effort).trim().toLowerCase();
 if(!VALID_EFFORTS.has(clean))throw new Error('Invalid reasoning effort: choose low, medium, high, or xhigh.');
 return clean;
}
export function resolveAgentStepLaunch({agent='codex',definition=null,step=null,model=null,reasoningEffort=null,tiering=null,env=process.env}={}) {
 const rawKind=definition?.kind??agent,normalizedAgent=typeof rawKind==='string'&&Object.hasOwn(TIER_PROFILES,rawKind.trim().toLowerCase())?rawKind.trim().toLowerCase():'codex';
 const command=definition?.command??rawKind,explicitModel=checkModel(model),explicitEffort=checkEffort(reasoningEffort);
 const cleanStep=typeof step==='string'?step.trim().toLowerCase():'';
 const tier=WORKER_STEPS.has(cleanStep)?'worker':REVIEWER_STEPS.has(cleanStep)?'reviewer':null;
 const cfg=tiering&&typeof tiering==='object'&&!Array.isArray(tiering)?tiering:null;
 const flag=String(env?.PDD_MODEL_TIERING??'').trim().toLowerCase();
 const tieringOn=tiering===true||cfg?.enabled===true?true:(tiering===false||cfg?.enabled===false?false:(flag==='1'||flag==='true'));
 if(!tieringOn||!tier)return {agent:normalizedAgent,command,tier,model:explicitModel,reasoningEffort:explicitEffort,args:explicitModel?['--model',explicitModel]:[],tieringEnabled:false};
 const defaults=TIER_PROFILES[normalizedAgent]?.[tier]??TIER_PROFILES.codex[tier];
 const envModel=tier==='worker'?env?.PDD_WORKER_MODEL:env?.PDD_REVIEWER_MODEL;
 const envEffort=tier==='worker'?env?.PDD_WORKER_EFFORT:env?.PDD_REVIEWER_EFFORT;
 const resolvedModel=explicitModel&&cfg?.overrideExplicitModel!==true?explicitModel:checkModel(cfg?.models?.[normalizedAgent]?.[tier]??cfg?.[tier]?.model??envModel??defaults.model);
 const resolvedEffort=explicitEffort??checkEffort(cfg?.efforts?.[normalizedAgent]?.[tier]??cfg?.[tier]?.reasoningEffort??envEffort??defaults.reasoningEffort);
 const args=[];
 if(resolvedModel)args.push('--model',resolvedModel);
 if(resolvedEffort){if(normalizedAgent==='codex')args.push('-c',`model_reasoning_effort="${resolvedEffort}"`);else if(normalizedAgent==='claude')args.push('--effort',resolvedEffort);}
 return {agent:normalizedAgent,command,tier,model:resolvedModel,reasoningEffort:resolvedEffort,args,tieringEnabled:true};
}
function inspectCallerArgs(rawArgs,overrideExplicitModel) {
 const list=Array.isArray(rawArgs)?rawArgs:[];
 const cleaned=[];
 let callerModel=null,hasModelFlag=false,hasEffortFlag=false;
 for(let i=0;i<list.length;i++){
  const arg=String(list[i]??'');
  if(arg==='--'){cleaned.push(...list.slice(i));break;}
  if(arg==='--model'||arg==='-m'){
   hasModelFlag=true;
   if(i+1<list.length)callerModel=list[i+1];
   if(!overrideExplicitModel)cleaned.push(list[i],...(i+1<list.length?[list[i+1]]:[]));
   i+=1;continue;
  }
  if(arg.startsWith('--model=')||arg.startsWith('-m=')){
   hasModelFlag=true;
   callerModel=arg.slice(arg.indexOf('=')+1);
   if(!overrideExplicitModel)cleaned.push(list[i]);
   continue;
  }
  if(arg==='--effort'||arg.startsWith('--effort='))hasEffortFlag=true;
  if((arg==='-c'||arg==='--config')&&typeof list[i+1]==='string'&&/^\s*model_reasoning_effort\s*=/.test(list[i+1]))hasEffortFlag=true;
  cleaned.push(list[i]);
 }
 return {callerModel,hasModelFlag,hasEffortFlag,cleaned};
}
function composeStepChildArgs(launch,caller,hasExplicitEffortOption) {
 const injected=[];
 for(let i=0;i<launch.args.length;i++){
  const item=launch.args[i];
  if(item==='--model'){
   if(!caller.hasModelFlag)injected.push(item,launch.args[i+1]);
   i+=1;continue;
  }
  if(item==='-c'&&typeof launch.args[i+1]==='string'&&launch.args[i+1].startsWith('model_reasoning_effort=')){
   if(!caller.hasEffortFlag||hasExplicitEffortOption)injected.push(item,launch.args[i+1]);
   i+=1;continue;
  }
  if(item==='--effort'){
   if(!caller.hasEffortFlag||hasExplicitEffortOption)injected.push(item,launch.args[i+1]);
   i+=1;continue;
  }
  injected.push(item);
 }
 const rest=caller.cleaned;
 if(launch.agent==='codex'&&rest.length){
  const prefixLen=(rest[0]==='exec'||rest[0]==='e')?(['resume','fork','review'].includes(rest[1])?2:1):(['resume','review','fork'].includes(rest[0])?1:0);
  if(prefixLen>0)return [...rest.slice(0,prefixLen),...injected,...rest.slice(prefixLen)];
 }
 return [...injected,...rest];
}
export async function runStepAgentProcess({agent='codex',definition=null,step=null,args=[],model=null,reasoningEffort=null,tiering=null,cwd,env=process.env,input='',signal,timeoutMs=120000,maxBytes=131072,run=runAgentProcess,now=Date.now}={}) {
 const childEnv={...env,...definition?.env};
 const overrideExplicitModel=Boolean(tiering&&typeof tiering==='object'&&tiering.overrideExplicitModel===true);
 const hasModelOpt=model!==null&&model!==undefined;
 const caller=inspectCallerArgs(args,overrideExplicitModel||hasModelOpt);
 const effectiveCallerModel=hasModelOpt?model:(!overrideExplicitModel&&caller.hasModelFlag?caller.callerModel:null);
 const launch=resolveAgentStepLaunch({agent,definition,step,model:effectiveCallerModel,reasoningEffort,tiering,env:childEnv});
 const childArgs=composeStepChildArgs(launch,{...caller,hasModelFlag:caller.hasModelFlag&&!overrideExplicitModel&&!hasModelOpt},reasoningEffort!==null&&reasoningEffort!==undefined);
 const {extractHarnessTokens,normalizeAutopilotPhase}=await import('./autopilot-telemetry.mjs');
 const phase=normalizeAutopilotPhase(step),startedAt=now();
 let result;
 try{
  result=await run(launch.command,childArgs,{cwd,env:childEnv,input,signal,timeoutMs,maxBytes});
 }catch(error){
  const endedAt=now(),durationMs=Math.max(0,endedAt-startedAt);
  const tokens=extractHarnessTokens(typeof error?.stdout==='string'?error.stdout:'',{agent:launch.agent});
  if(error&&typeof error==='object'){error.launch=launch;error.telemetry={phase,step:step??null,startedAt,endedAt,durationMs,tokens};}
  throw error;
 }
 const endedAt=now(),durationMs=Math.max(0,endedAt-startedAt);
 const stdout=typeof result?.stdout==='string'?result.stdout:'';
 const tokens=extractHarnessTokens(stdout,{agent:launch.agent});
 return {...(result&&typeof result==='object'?result:{}),stdout,launch,telemetry:{phase,step:step??null,startedAt,endedAt,durationMs,tokens}};
}
