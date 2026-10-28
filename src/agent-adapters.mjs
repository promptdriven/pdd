// Generated from prompts/cli/agent-adapters.prompt.md (sha256: 8c25ed3c1eb724b1ff31142cc8e3f1f19eaab04f179c62a34d7a7c5fcc188598).
import { spawn } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { mkdtempSync, writeFileSync, readFileSync, readdirSync, rmSync, chmodSync, mkdirSync, lstatSync, openSync, fstatSync, closeSync, fchmodSync, constants } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { buildAgentInput } from './agent-packet.mjs';
import { loadAgentDefinitions } from './agent-config.mjs';
import { checkInput } from './runtime-preflight.mjs';
const AGENTS = [['codex','Codex'],['claude','Claude'],['gemini','Gemini']];
const SECRET = /token|password|secret|api[_-]?key|authorization|cookie|credential/i;
const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const fail = (state, message) => ({say:message,fill:null,error:{state,message}});
const MESSAGES = {signed_out:'This agent is signed out. Sign in at your terminal, or choose another agent.',quota:'This agent has reached its usage limit. Choose another agent or try later.',not_installed:'This agent is not installed. Choose another agent.'};
function stateOf(text) { return /rate.?limit|usage.?limit|quota|credits|capacity/i.test(text)?'quota':/not logged|not signed|sign.?in|login required|unauthorized|authentication/i.test(text)?'signed_out':'error'; }
function scrub(value,env) {
 const values=Object.entries(env).filter(([k,v])=>SECRET.test(k)&&typeof v==='string'&&v.length>0).map(([,v])=>v);
 const clean=x=>{
  if(typeof x==='string'){for(const v of values)x=x.split(v).join('[redacted]');return x.replace(/-----BEGIN [^-]*PRIVATE KEY-----[\s\S]*?-----END [^-]*PRIVATE KEY-----/g,'[redacted]').replace(/\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,})\b/g,'[redacted]').replace(/Bearer\s+\S+/gi,'Bearer [redacted]').replace(/\b(token|password|secret|api[_-]?key|authorization|cookie|credential)["']?\s*[:=]\s*(?:"[^"]*"|'[^']*'|[^\s,;]+)/gi,'$1=[redacted]').replace(/(https?:\/\/)[^\s/@]+:[^\s/@]+@/gi,'$1[redacted]@');}
  if(Array.isArray(x))return x.map(clean);
  if(object(x))return Object.fromEntries(Object.entries(x).map(([k,v])=>[k,SECRET.test(k)?'[redacted]':clean(v)]));
  return x;
 };return clean(value);
}
function diagnostic(text,env) {
 return scrub(String(text??''),env).replace(/\x1b\[[0-?]*[ -/]*[@-~]/g,'').replace(/[\x00-\x08\x0b-\x1f\x7f]/g,'');
}
function logDiagnostic(agent,text,env) {
 if(!env.HOME)return null;
 const folder=join(env.HOME,'.pdd','runtime'),file=join(folder,'agent-chat.log');let fd;
 try{
  for(const dir of [join(env.HOME,'.pdd'),folder]){try{mkdirSync(dir,{mode:0o700});}catch(e){if(e.code!=='EEXIST')throw e;}const st=lstatSync(dir);if(!st.isDirectory()||st.isSymbolicLink())throw Error('Unsafe log directory');}
  fd=openSync(file,constants.O_WRONLY|constants.O_APPEND|constants.O_CREAT|constants.O_NOFOLLOW|constants.O_NONBLOCK,0o600);if(!fstatSync(fd).isFile())throw Error('Unsafe log');fchmodSync(fd,0o600);
  writeFileSync(fd,`[${new Date().toISOString()}] ${agent}\n${diagnostic(text,env)}\n`);return file;
 }catch{return null;}finally{if(fd!==undefined)closeSync(fd);}
}
function failedInvocation(agent,text,env,state=stateOf(text),name=AGENTS.find(([id])=>id===agent)?.[1]??'Agent') {
 const line=diagnostic(text,env).split(/\r?\n/).map(x=>x.trim()).find(Boolean)?.slice(0,500)||'The CLI exited without an error message.';
 const log=logDiagnostic(name,text,env),prefix=state==='error'?`${name} could not start`:MESSAGES[state];
 return fail(state,`${prefix}${state==='error'?': ': ' '}${line}. ${log?`Details: ${log}`:'Local diagnostic log unavailable.'}`);
}
function unknownFeature(answer,args) {
 if(stateOf(answer.stderr+' '+answer.stdout)!=='error')return null;
 const text=answer.stderr||answer.stdout;
 const first=text.split(/\r?\n/).map(x=>x.trim()).find(Boolean)??'';
 if(answer.stdout?.trim()||! /^(?:error loading config|configuration error|error:\s*(?:unknown|unrecognized|unsupported)\s+feature)/i.test(first))return null;
 const match=text.match(/(?:unknown|unrecognized|unsupported)\s+feature(?:\s+(?:flag|key))?\s*[:=]?\s*[`"']?(?:features\.)?([a-z][a-z0-9_]*)/i);
 const flag=match&&`features.${match[1]}=false`;
 return flag&&args.includes(flag)?flag:null;
}
export function runAgentProcess(command,args,{cwd,env,input='',signal,timeoutMs=120000,maxBytes=131072}={}) {
 return new Promise((resolve,reject)=>{
  if(signal?.aborted){reject(new Error('cancelled'));return;}
  let child,stdout='',stderr='',size=0,settled=false,killTimer,stopping=false;
  const stop=()=>{if(!child)return;stopping=true;try{process.kill(-child.pid,'SIGTERM');}catch{child.kill('SIGTERM');}killTimer=setTimeout(()=>{try{process.kill(-child.pid,'SIGKILL');}catch{child.kill('SIGKILL');}},500);killTimer.unref();};
  const finish=(error,code)=>{if(settled)return;settled=true;clearTimeout(timer);signal?.removeEventListener('abort',abort);if(error){error.stderr=stderr;reject(error);}else resolve({code,stdout,stderr});};
  const abort=()=>{stop();finish(new Error('cancelled'));};
  const timer=setTimeout(()=>{stop();finish(new Error('timeout'));},timeoutMs);
  try{child=spawn(command,args,{cwd,env,stdio:['pipe','pipe','pipe'],shell:false,detached:process.platform!=='win32'});}catch(e){finish(e);return;}
  signal?.addEventListener('abort',abort,{once:true});
  const data=(kind,chunk)=>{size+=chunk.length;if(size>maxBytes){stop();finish(new Error('output limit'));return;}if(kind==='stdout')stdout+=chunk;else stderr+=chunk;};
  child.stdout.on('data',c=>data('stdout',c));child.stderr.on('data',c=>data('stderr',c));child.on('error',e=>finish(e));child.on('close',code=>{if(!stopping)clearTimeout(killTimer);finish(null,code);});child.stdin.on('error',()=>{});child.stdin.end(input);
 });
}
export async function discoverAgents({cwd=process.cwd(),env=process.env,run=runAgentProcess,definitions}={}) {
 const result=[];
 for(const {id,name,kind,command,env:overrides} of definitions??loadAgentDefinitions({cwd,env})){
  const childEnv={...env,...overrides},opts={cwd,env:childEnv,timeoutMs:10000,maxBytes:131072};
  try{
   const help=await run(command,['--help'],opts);
   if(help.code!==0){result.push({id,name,state:'error',detail:'The agent help command failed.'});continue;}
   if(kind==='gemini'){const version=await run(command,['--version'],{...opts,maxBytes:1024});const verified=version.code===0&&version.stdout.trim()==='0.66.0';result.push({id,name,state:verified?'available':'error',detail:verified?'Installed; sign-in is checked when you send a message.':'This Gemini version has no verified read-only adapter yet.'});continue;}
   const flags=kind==='codex'?['--sandbox']:['--safe-mode','--tools','--permission-prompts'];
   if(flags.some(f=>!help.stdout.includes(f))){result.push({id,name,state:'error',detail:'Update this agent to a version with the required read-only controls.'});continue;}
   const auth=await run(command,kind==='codex'?['login','status']:['auth','status','--json'],{...opts,maxBytes:16384});
   let ready=false;if(kind==='claude'){try{ready=JSON.parse(auth.stdout).loggedIn===true;}catch{}}
   else ready=auth.code===0&&/logged in/i.test(auth.stdout+' '+auth.stderr)&&!/not logged/i.test(auth.stdout+' '+auth.stderr);
   result.push({id,name,state:ready?'ready':'signed_out'});
  }catch(e){result.push({id,name,state:e.code==='ENOENT'?'not_installed':'error'});}
 }
 return result;
}
function geminiOverlay(env) {
 const systemDir=process.platform==='darwin'?'/Library/Application Support/GeminiCli':process.platform==='win32'?'C:\\ProgramData\\gemini-cli':'/etc/gemini-cli';
 try{if(readdirSync(join(systemDir,'policies')).some(name=>name.endsWith('.toml')))throw new Error('Gemini system policy prevents the private deny-all policy.');}catch(e){if(e.code!=='ENOENT')throw e;}
 const original=env.GEMINI_CLI_SYSTEM_SETTINGS_PATH||join(systemDir,'settings.json');let existing={};
 try{const bytes=readFileSync(original);if(bytes.length>1048576)throw new Error('Settings too large');existing=JSON.parse(bytes.toString('utf8'));if(!object(existing))throw new Error('Invalid settings');}catch(e){if(e.code!=='ENOENT')throw e;}
 const config={...existing,tools:{...existing.tools,core:[],allowed:[],discoveryCommand:'',callCommand:''},hooksConfig:{...existing.hooksConfig,enabled:false},admin:{...existing.admin,mcp:{...existing.admin?.mcp,enabled:false},extensions:{...existing.admin?.extensions,enabled:false},skills:{...existing.admin?.skills,enabled:false}},general:{...existing.general,enableAutoUpdate:false,enableAutoUpdateNotification:false,plan:{...existing.general?.plan,enabled:false,modelRouting:false}}};
 const folder=mkdtempSync(join(tmpdir(),'pdd-agent-gemini-'));chmodSync(folder,0o700);
 try{const settings=join(folder,'settings.json'),policy=join(folder,'deny.toml');writeFileSync(settings,JSON.stringify(config),{mode:0o600});writeFileSync(policy,'[[rule]]\ntoolName = "*"\ndecision = "deny"\npriority = 999\n',{mode:0o600});return {env:{...env,GEMINI_CLI_SYSTEM_SETTINGS_PATH:settings,GEMINI_CLI_SYSTEM_DEFAULTS_PATH:env.GEMINI_CLI_SYSTEM_DEFAULTS_PATH||join(dirname(original),'system-defaults.json')},policy,cleanup:()=>rmSync(folder,{recursive:true,force:true})};}catch(e){rmSync(folder,{recursive:true,force:true});throw e;}
}
function references(x){return Array.isArray(x)?x.some(references):object(x)&&(Object.hasOwn(x,'$step_result')||Object.values(x).some(references));}
function validFill(fill,entries){
 if(fill===null)return true;
 if(!object(fill)||Object.keys(fill).sort().join(',')!=='entry,input'||!object(fill.input)||references(fill.input))return false;
 const entry=entries.find(e=>e.entry===fill.entry);if(!entry)return false;
 const result=checkInput(fill.input,entry.input_schema,0);return !result.refusals.length&&!result.warnings.length;
}
export async function askAgent({agent,definition,cwd,env=process.env,context={},entries=[],supportsApply=false,supportsRun=false,signal,run=runAgentProcess,timeoutMs=120000}={}) {
 const command=definition?.command??agent,name=definition?.name??AGENTS.find(([id])=>id===agent)?.[1];
 agent=definition?.kind??agent;env={...env,...definition?.env};
 if(!AGENTS.some(([id])=>id===agent))return fail('error','Choose Codex, Claude or Gemini.');
 if(signal?.aborted)return fail('error','The agent request was cancelled.');
 try{
  const safe=scrub({context,entries},env);
  const input=buildAgentInput({context:safe.context,entries:safe.entries,supportsApply,supportsRun});
  const opts={cwd,env,input,signal,timeoutMs,maxBytes:131072};
  let args,overlay;
  if(agent==='gemini'){const version=await run(command,['--version'],{cwd,env,signal,timeoutMs:10000,maxBytes:1024});if(version.code!==0||version.stdout.trim()!=='0.66.0')return fail('error','This Gemini version has no verified read-only adapter. Choose another agent.');overlay=geminiOverlay(env);opts.env=overlay.env;}
  if(agent==='codex'){
   args=['exec','--sandbox','read-only','--ephemeral','--color','never','--ignore-rules','-c','approval_policy="never"','-c','web_search="disabled"','-c','mcp_servers={}'];
   for(const feature of ['hooks','plugins','apps','browser_use','browser_use_external','browser_use_full_cdp_access','computer_use','multi_agent','multi_agent_v2','shell_tool','unified_exec','code_mode','code_mode_host'])args.push('-c',`features.${feature}=false`);
   args.push('-');
  }else if(agent==='gemini')args=['--extensions','none','--allowed-mcp-server-names',`pdd-disabled-${randomUUID()}`,'-p','Answer the supplied Try question as strict JSON.','--approval-mode','default','--admin-policy',overlay.policy,'--output-format','json'];
  else args=['-p','--safe-mode','--tools','Read,Grep,Glob','--permission-mode','plan','--permission-prompts','none','--strict-mcp-config','--no-chrome','--no-session-persistence','--output-format','json'];
  let answer;try{answer=await run(command,args,opts);if(agent==='codex'&&answer.code!==0){const flag=unknownFeature(answer,args);if(flag){logDiagnostic(name,answer.stderr||answer.stdout,env);const index=args.indexOf(flag);args.splice(index-1,2);answer=await run(command,args,opts);}}}finally{overlay?.cleanup();}
  if(answer.code!==0)return failedInvocation(agent,answer.stderr||answer.stdout,env,stateOf(answer.stdout+' '+answer.stderr),name);
  let parsed=JSON.parse(answer.stdout);
  // Claude's JSON transport wraps the textual final answer; it is not the chat schema.
  if(agent==='claude'&&object(parsed)&&typeof parsed.result==='string'){
   if(parsed.is_error)return failedInvocation(agent,parsed.result,env,stateOf(parsed.result),name);parsed=JSON.parse(parsed.result);
  }
  if(agent==='gemini'&&object(parsed)&&typeof parsed.response==='string')parsed=JSON.parse(parsed.response);
  if(!object(parsed)||Object.keys(parsed).some(key=>!['say','fill','apply','criterion','expect','save','next','run'].includes(key))||typeof parsed.say!=='string'||!parsed.say.trim())return fail('error','The agent returned an invalid answer. No fields were applied.');
  const clean=scrub(parsed,env),result={say:clean.say,fill:null};
  const fillValid=validFill(clean.fill??null,entries);
  if(fillValid)result.fill=clean.fill??null;
  if(typeof clean.apply==='boolean'&&fillValid&&(result.fill!==null||!clean.apply))result.apply=clean.apply;
  if(typeof clean.run==='boolean'&&supportsRun&&supportsApply&&['chat','own','walk'].includes(context.requestKind??'chat')&&(!clean.run||(result.apply===true&&result.fill!==null)))result.run=clean.run;
  const known=new Set((Array.isArray(context.criteria)?context.criteria:[]).map(c=>c.id));
  if(clean.criterion===null||known.has(clean.criterion))result.criterion=clean.criterion;
  if(clean.next===null)result.next=null;
  else if(object(clean.next)&&Object.keys(clean.next).sort().join(',')==='criterion,text'&&typeof clean.next.text==='string'&&clean.next.text.trim()&&clean.next.text.length<=200&&(clean.next.criterion===null||known.has(clean.next.criterion)))result.next=clean.next;
  const pointer=path=>typeof path==='string'&&path.length<=256&&(path===''||(path.startsWith('/')&&!/~(?:[^01]|$)/.test(path)));
  const checks=(list,expected)=>Array.isArray(list)&&list.length>0&&list.length<=32&&list.every(c=>object(c)&&Object.keys(c).sort().join(',')===(expected?'path,target,value':'path,target')&&['result','world'].includes(c.target)&&pointer(c.path)&&(!expected||!references(c.value)));
  if(clean.expect===null)result.expect=null;
  else if(result.fill&&object(clean.expect)&&Object.keys(clean.expect).sort().join(',')==='checks,text'&&typeof clean.expect.text==='string'&&clean.expect.text.trim()&&clean.expect.text.length<=500&&checks(clean.expect.checks,true)&&Buffer.byteLength(JSON.stringify(clean.expect))<=16384)result.expect=clean.expect;
  if(clean.save===null)result.save=null;
  else if(object(clean.save)&&['checks,criterion,name','checks,criterion,name,proposed_criterion'].includes(Object.keys(clean.save).sort().join(','))&&typeof clean.save.name==='string'&&clean.save.name.trim()&&clean.save.name.length<=100&&(clean.save.criterion===null||known.has(clean.save.criterion))&&checks(clean.save.checks,false)&&(!Object.hasOwn(clean.save,'proposed_criterion')||(clean.save.criterion===null&&typeof clean.save.proposed_criterion==='string'&&clean.save.proposed_criterion.trim()&&clean.save.proposed_criterion===clean.save.proposed_criterion.trim()&&clean.save.proposed_criterion.length<=500&&!/[\x00-\x1f\x7f-\x9f]/.test(clean.save.proposed_criterion))))result.save=clean.save;
  return result;
 }catch(e){if(e instanceof SyntaxError)return fail('error','The agent returned invalid JSON. No fields were applied.');const state=e.code==='ENOENT'?'not_installed':'error';return failedInvocation(agent,e.stderr||e.message,env,state,name);}
}
