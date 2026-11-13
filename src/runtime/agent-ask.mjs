// Generated from prompts/cli/agent-ask.prompt.md (sha256: 69f7563df2b19a37af55ce4af2778710044fc1477906a8a93e054ec24094bd14).
import { createHash } from 'node:crypto';
import { mkdtempSync, writeFileSync, readFileSync, readSync, readdirSync, rmSync, chmodSync, mkdirSync, lstatSync, openSync, fstatSync, closeSync, fchmodSync, statSync, constants } from 'node:fs';
import { homedir, tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { loadRuntimeWorkspace } from './runtime-workspace.mjs';
import { buildAgentInput } from './agent-packet.mjs';
import { checkInput } from './runtime-preflight.mjs';
const AGENTS = [['codex','Codex'],['claude','Claude'],['gemini','Gemini']];
const SECRET = /token|password|secret|api[_-]?key|authorization|cookie|credential/i;
const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const fail = (state, message) => ({say:message,fill:null,error:{state,message}});
const unboundPortError = message => Object.assign(new Error(message), { unboundPort: true });
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
function geminiCapabilityError(help) {
 if(help.code!==0)return 'Gemini Try read-only capability discovery failed (--help).';
 const missing=['--approval-mode','--admin-policy','--extensions','--allowed-mcp-server-names','--output-format'].find(flag=>!help.stdout.includes(flag));
 return missing?`Gemini Try read-only mode requires ${missing}; update Gemini CLI.`:null;
}
function claudeCapabilities(help) {
 if(!help||help.code!==0||typeof help.stdout!=='string')return {mode:null,excludeDynamic:false};
 const text=help.stdout;
 const mode=/(?:^|\s)--system-prompt(?:-file|\[-file\])(?:\s|<|=|,|\.|$)/m.test(text)?'file':/(?:^|\s)--system-prompt(?:\s|<|=|$)/m.test(text)?'arg':null;
 return {mode,excludeDynamic:/(?:^|\s)--exclude-dynamic-system-prompt-sections(?:\s|$)/m.test(text)};
}
function splitClaudeInput(input) {
 const marker='\n\nDATA\n',index=input.indexOf(marker),header=input.slice(0,index),data=JSON.parse(input.slice(index+marker.length));
 const staticData={productRules:data.productRules,ways:data.ways,project:data.project,criteria:data.criteria};
 const turnData={conversation:data.conversation,coverage:data.coverage,progress:data.progress,try:data.try,message:data.message,changed:data.changed};
 return {systemPrompt:`${header}\nDATA\n${JSON.stringify(staticData)}`,turnInput:JSON.stringify(turnData)};
}
function claudeSystemPromptFile(text) {
 const folder=mkdtempSync(join(tmpdir(),'pdd-agent-claude-'));chmodSync(folder,0o700);
 try{const file=join(folder,'system-prompt.txt');writeFileSync(file,text,{mode:0o600});return {file,cleanup:()=>rmSync(folder,{recursive:true,force:true})};}catch(e){rmSync(folder,{recursive:true,force:true});throw e;}
}
function parseJsonc(text) {
 const src=text.charCodeAt(0)===0xfeff?text.slice(1):text;let out='',inStr=false;
 for(let i=0;i<src.length;i++){
  const ch=src[i];
  if(inStr){out+=ch;if(ch==='\\'&&i+1<src.length)out+=src[++i];else if(ch==='"')inStr=false;}
  else if(ch==='"'){inStr=true;out+=ch;}
  else if(ch==='/'&&src[i+1]==='/'){i+=2;while(i<src.length&&src[i]!=='\n'&&src[i]!=='\r')i++;i--;}
  else if(ch==='/'&&src[i+1]==='*'){const end=src.indexOf('*/',i+2);if(end===-1)throw new SyntaxError('Unterminated comment');i=end+1;}
  else out+=ch;
 }
 let clean='';inStr=false;
 for(let i=0;i<out.length;i++){
  const ch=out[i];
  if(inStr){clean+=ch;if(ch==='\\'&&i+1<out.length)clean+=out[++i];else if(ch==='"')inStr=false;}
  else if(ch==='"'){inStr=true;clean+=ch;}
  else if(ch===','){let j=i+1;while(j<out.length&&(out[j]===' '||out[j]==='\t'||out[j]==='\n'||out[j]==='\r'))j++;if(out[j]!=='}'&&out[j]!==']')clean+=ch;}
  else clean+=ch;
 }
 return JSON.parse(clean);
}
function geminiMcpSentinel(cwd,env,existing,defaultsPath) {
 const configured=new Set(object(existing?.mcpServers)?Object.keys(existing.mcpServers):[]),failed=existing?.mcpServers!==undefined&&!object(existing.mcpServers)?[Buffer.from('system:mcpServers')]:[];
 const effectiveCwd=cwd??process.cwd(),home=env.HOME||homedir(),files=[...new Set([defaultsPath,...(env.GEMINI_CLI_HOME?[join(env.GEMINI_CLI_HOME,'settings.json'),join(env.GEMINI_CLI_HOME,'.gemini','settings.json')]:[]),home?join(home,'.gemini','settings.json'):null,effectiveCwd?join(effectiveCwd,'.gemini','settings.json'):null].filter(Boolean))];
 for(const file of files){
  try{lstatSync(file);}catch(e){if(e.code==='ENOENT'||e.code==='ENOTDIR')continue;failed.push(Buffer.from(`${file}:${e.code||e.message}`));continue;}
  let fd,raw=null;
  try{
   const st=statSync(file);if(!st.isFile()||st.size>1048576)throw new Error('invalid_target');
   fd=openSync(file,'r');const fst=fstatSync(fd);if(!fst.isFile()||fst.size>1048576)throw new Error('invalid_target');
   const buf=Buffer.alloc(fst.size+1);let n=0;while(n<buf.length){const got=readSync(fd,buf,n,buf.length-n,n);if(!got)break;n+=got;}
   if(n>1048576)throw new Error('too_large');raw=buf.subarray(0,n);
   const doc=parseJsonc(raw.toString('utf8'));if(!object(doc)||(doc.mcpServers!==undefined&&!object(doc.mcpServers)))throw new Error('invalid_json');
   if(doc.mcpServers)for(const key of Object.keys(doc.mcpServers))configured.add(key);
  }catch(e){
   failed.push(raw??Buffer.from(`${file}:${e.code||e.message}`));
   if(raw)for(const [tok] of raw.toString('utf8').matchAll(/pdd-disabled-[0-9A-Za-z_-]*/g))configured.add(tok);
  }finally{if(fd!==undefined)try{closeSync(fd);}catch{}}
 }
 if(!failed.length&&!configured.has('pdd-disabled-none'))return 'pdd-disabled-none';
 let salt=0,sentinel;
 do{const h=createHash('sha256');h.update([...configured].sort().join('\0')+'\0');for(const chunk of failed){h.update(chunk);h.update('\0');}h.update(String(salt++));sentinel=`pdd-disabled-${h.digest('hex').slice(0,16)}`;}while(configured.has(sentinel)||failed.some(b=>b.includes(sentinel)));
 return sentinel;
}
function geminiOverlay(env,cwd) {
 const systemDir=process.platform==='darwin'?'/Library/Application Support/GeminiCli':process.platform==='win32'?'C:\\ProgramData\\gemini-cli':'/etc/gemini-cli';
 try{if(readdirSync(join(systemDir,'policies')).some(name=>name.endsWith('.toml')))throw new Error('Gemini system policy prevents the private deny-all policy.');}catch(e){if(e.code!=='ENOENT')throw e;}
 const original=env.GEMINI_CLI_SYSTEM_SETTINGS_PATH||join(systemDir,'settings.json'),defaultsPath=env.GEMINI_CLI_SYSTEM_DEFAULTS_PATH||join(dirname(original),'system-defaults.json');let existing={};
 try{const bytes=readFileSync(original);if(bytes.length>1048576)throw new Error('Settings too large');existing=parseJsonc(bytes.toString('utf8'));if(!object(existing))throw new Error('Invalid settings');}catch(e){if(e.code!=='ENOENT')throw e;}
 const mcpSentinel=geminiMcpSentinel(cwd,env,existing,defaultsPath);
 const config={...existing,tools:{...existing.tools,core:[],allowed:[],discoveryCommand:'',callCommand:''},hooksConfig:{...existing.hooksConfig,enabled:false},admin:{...existing.admin,mcp:{...existing.admin?.mcp,enabled:false},extensions:{...existing.admin?.extensions,enabled:false},skills:{...existing.admin?.skills,enabled:false}},general:{...existing.general,enableAutoUpdate:false,enableAutoUpdateNotification:false,plan:{...existing.general?.plan,enabled:false,modelRouting:false}}};
 const folder=mkdtempSync(join(tmpdir(),'pdd-agent-gemini-'));chmodSync(folder,0o700);
 try{const settings=join(folder,'settings.json'),policy=join(folder,'deny.toml');writeFileSync(settings,JSON.stringify(config),{mode:0o600});writeFileSync(policy,'[[rule]]\ntoolName = "*"\ndecision = "deny"\npriority = 999\n',{mode:0o600});return {env:{...env,GEMINI_CLI_SYSTEM_SETTINGS_PATH:settings,GEMINI_CLI_SYSTEM_DEFAULTS_PATH:defaultsPath},policy,mcpSentinel,cleanup:()=>rmSync(folder,{recursive:true,force:true})};}catch(e){rmSync(folder,{recursive:true,force:true});throw e;}
}
function references(x){return Array.isArray(x)?x.some(references):object(x)&&(Object.hasOwn(x,'$step_result')||Object.values(x).some(references));}
function validFill(fill,entries){
 if(fill===null)return true;
 if(!object(fill)||Object.keys(fill).sort().join(',')!=='entry,input'||!object(fill.input)||references(fill.input))return false;
 const entry=entries.find(e=>e.entry===fill.entry);if(!entry)return false;
 const result=checkInput(fill.input,entry.input_schema,0);return !result.refusals.length&&!result.warnings.length;
}
export async function askAgent({agent,definition,cwd,env=process.env,context={},entries=[],supportsApply=false,supportsRun=false,workspace,signal,run,timeoutMs=120000}={}, ports={}) {
 if((workspace??(cwd?loadRuntimeWorkspace({root:cwd}):null))?.configured)return fail('error','Bounded agent connection is unavailable: native tool and automatic context controls cannot establish packet-only context.');
 const command=definition?.command??agent,name=definition?.name??AGENTS.find(([id])=>id===agent)?.[1];
 agent=definition?.kind??agent;env={...env,...definition?.env};
 if(!AGENTS.some(([id])=>id===agent))return fail('error','Choose Codex, Claude or Gemini.');
 if(signal?.aborted)return fail('error','The agent request was cancelled.');
 const runPort=run??ports.run??ports.runAgentProcess??ports.agents?.run;
 if(typeof runPort!=='function')throw unboundPortError('Agent process port (run / agents.run) is not bound.');
 try{
  const safe=scrub({context,entries},env);
  const input=buildAgentInput({context:safe.context,entries:safe.entries,supportsApply,supportsRun});
  const opts={cwd,env,input,signal,timeoutMs,maxBytes:131072};
  let args,overlay,claudePrompt,answer;
  try{
   if(agent==='gemini'){const detail=geminiCapabilityError(await runPort(command,['--help'],{cwd,env,signal,timeoutMs:10000,maxBytes:131072}));if(detail)return fail('error',detail);overlay=geminiOverlay(env,cwd);opts.env=overlay.env;}
   if(agent==='codex'){
    args=['exec','--sandbox','read-only','--ephemeral','--color','never','--ignore-rules','-c','approval_policy="never"','-c','web_search="disabled"','-c','mcp_servers={}'];
    for(const feature of ['hooks','plugins','apps','browser_use','browser_use_external','browser_use_full_cdp_access','computer_use','multi_agent','multi_agent_v2','shell_tool','unified_exec','code_mode','code_mode_host'])args.push('-c',`features.${feature}=false`);
    args.push('-');
   }else if(agent==='gemini')args=['--extensions','none','--allowed-mcp-server-names',overlay.mcpSentinel,'-p','Answer the supplied Try question as strict JSON.','--approval-mode','default','--admin-policy',overlay.policy,'--output-format','json'];
   else{
    const caps=claudeCapabilities(await runPort(command,['--help'],{cwd,env,signal,timeoutMs:10000,maxBytes:131072}));
    args=['-p','--safe-mode','--tools','Read,Grep,Glob','--permission-mode','plan','--permission-prompts','none','--strict-mcp-config','--no-chrome','--no-session-persistence'];
    if(caps.excludeDynamic)args.push('--exclude-dynamic-system-prompt-sections');
    if(caps.mode){const split=splitClaudeInput(input);opts.input=split.turnInput;if(caps.mode==='file'){claudePrompt=claudeSystemPromptFile(split.systemPrompt);args.push('--system-prompt-file',claudePrompt.file);}else args.push('--system-prompt',split.systemPrompt);}
    args.push('--output-format','json');
   }
   answer=await runPort(command,args,opts);
   if(agent==='codex'&&answer.code!==0){const flag=unknownFeature(answer,args);if(flag){logDiagnostic(name,answer.stderr||answer.stdout,env);const index=args.indexOf(flag);args.splice(index-1,2);answer=await runPort(command,args,opts);}}
  }finally{overlay?.cleanup();claudePrompt?.cleanup();}
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
  else if(object(clean.save)&&Object.keys(clean.save).sort().join(',')==='checks,criterion,name'&&typeof clean.save.name==='string'&&clean.save.name.trim()&&clean.save.name.length<=100&&(clean.save.criterion===null||known.has(clean.save.criterion))&&checks(clean.save.checks,false))result.save=clean.save;
  return result;
 }catch(e){if(e?.unboundPort)throw e;if(e instanceof SyntaxError)return fail('error','The agent returned invalid JSON. No fields were applied.');const state=e.code==='ENOENT'?'not_installed':'error';return failedInvocation(agent,e.stderr||e.message,env,state,name);}
}
