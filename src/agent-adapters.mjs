// Generated from prompts/cli/agent-adapters.prompt.md (sha256: f778e52a2317b125f122cd9765b1d20c7657231e5b1d6e1c3cbaf7d6f5f58f98).
import { spawn } from 'node:child_process';
import { lstatSync, statSync } from 'node:fs';
import { delimiter, resolve, isAbsolute } from 'node:path';
import { loadAgentDefinitions } from './agent-config.mjs';
import { runtimeWorkspaceSlice, workspace } from './runtime-seam.mjs';
runtimeWorkspaceSlice();
const AGENTS = [['codex','Codex'],['claude','Claude'],['gemini','Gemini']];
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
  const finish=(error,code)=>{if(settled)return;settled=true;clearTimeout(timer);signal?.removeEventListener('abort',abort);if(error){if(error.code==='ENOENT')error.executableMissing=executableMissing(command,{cwd,env});error.stderr=stderr;reject(error);}else resolve({code,stdout,stderr});};
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
