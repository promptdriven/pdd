// Generated from prompts/cli/program-run.prompt.md (sha256: ab46e28caca9a02a015bd16afc9e04824b94be429228e90571c28c7a495876e1).
import { spawn, spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync, chmodSync, lstatSync, openSync, closeSync, constants } from 'node:fs';
import { basename, join, relative, resolve } from 'node:path';
import { gitFiles, readPrompt, checkInput, interfaceSchemaProblems } from './runtime-preflight.mjs';
import { programData, readPrivate, writePrivate, safeDirectory, localError, object, acquireProgramLock } from './program-data.mjs';
import { openProgramSession } from './program-session.mjs';
import { programTransport } from './runtime-client.mjs';
const quote=word=>"'"+word.replaceAll("'","'\\''")+"'";
const fallback='Screen apps and HTTP entries open this way in the next release; for now run pdd simulate STORY.';
const fail=message=>{throw Object.assign(new Error(message),{exitCode:125});};
async function stdinText(input) {
  if(input?.isTTY)return '';
  const chunks=[];let size=0;
  for await(const chunk of input??[]) {const bytes=Buffer.from(chunk);size+=bytes.length;if(size>1024*1024)throw localError('Input exceeds 1 MiB.');chunks.push(bytes);}
  try{return new TextDecoder('utf-8',{fatal:true}).decode(Buffer.concat(chunks));}catch{throw localError('Input must be UTF-8 text.');}
}
function validate(input,schema) {
  const checked=checkInput(input,schema,0,{literal:true});
  if(checked.warnings.length)throw localError(checked.warnings.join('\n'));
  if(checked.refusals.length)throw localError(checked.refusals.map(r=>r.message).join('\n'));
}
function scalar(value,schema) {
  if(schema.type==='integer') {if(!/^-?(?:0|[1-9][0-9]*)$/.test(value)||!Number.isSafeInteger(Number(value)))throw localError('Expected an integer.');return Number(value);}
  if(schema.type==='number') {if(!/^-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?$/.test(value)||!Number.isFinite(Number(value)))throw localError('Expected a finite number.');return Number(value);}
  if(schema.type==='boolean'){if(!['true','false'].includes(value))throw localError('Expected true or false.');return value==='true';}
  if(schema.type!=='string')throw localError('Use --input JSON for this field.');return value;
}
async function typedInput(args,entry,root,stdin) {
  if(!args.length){const text=await stdinText(stdin);return text?JSON.parse(text):{};}
  let whole,fields={};
  for(let i=0;i<args.length;i++){
    const key=args[i];if(!key.startsWith('--')||i+1>=args.length)throw localError('Expected --name value.');
    const value=args[++i];
    if(key==='--input'){if(whole!==undefined)throw localError('Repeated --input.');whole=JSON.parse(value.startsWith('@')?readFileSync(resolve(root,value.slice(1)),'utf8'):value);continue;}
    const name=key.slice(2),schema=entry.input_schema.properties?.[name];
    if(!schema)throw localError(`Unknown field ${name}.`);
    if(schema.type==='array'){if(!Object.hasOwn(fields,name))Object.defineProperty(fields,name,{value:[],enumerable:true});fields[name].push(scalar(value,schema.items));}
    else {if(Object.hasOwn(fields,name))throw localError(`Repeated field ${name}.`);Object.defineProperty(fields,name,{value:scalar(value,schema),enumerable:true});}
  }
  if(whole!==undefined&&Object.keys(fields).length)throw localError('Whole input and field flags cannot mix.');
  return whole===undefined?fields:whole;
}
function estimate(root,visible,file,stack=new Set()) {
  if(stack.has(file))fail('The prompt call graph has a cycle; set a finite graph before running.');
  const prompt=readPrompt(root,visible,file);if(prompt.error)fail(`Cannot read ${file}: ${prompt.error}.`);
  const issues=interfaceSchemaProblems(prompt.interface);if(issues.length)throw localError(`${file}: ${issues.map(i=>i.pointer+' '+i.rule).join('; ')}`);
  const next=new Set(stack).add(file);let cap=1;
  for(const call of prompt.interface.calls??[]) {
    if(!Number.isInteger(call.max_calls)||call.max_calls<0)fail('The prompt call budget cannot be determined.');
    cap+=call.max_calls*(estimate(root,visible,call.target,next)+1);
    if(!Number.isSafeInteger(cap))fail('The prompt call budget is too large.');
  }
  return cap;
}
function trace(report,write,sanitize) {
  if(Array.isArray(report.call_chain)&&report.call_chain.length){write('Traceback (prompt calls, most recent last):\n');for(const frame of report.call_chain)write(`  ${sanitize(frame.prompt)}, operation ${sanitize(frame.operation)}${frame.call_index!=null&&frame.max_calls!=null?` (call ${frame.call_index} of at most ${frame.max_calls})`:''}\n`);}
  const error=report.error??report.refusal;if(error)write(`Error ${sanitize(error.code)}: ${sanitize(error.message)}\n`);
}
function sessionRecord(session) {
  const {transport,capture,newSession,save,serve,...record}=session;return record;
}
async function shellProgram({root,file,name,env,flags,data},ports) {
  const bin=safeDirectory(root,[...relative(root,data.dir).split('/'),'bin']);
  const launcher=join(bin,name);
  const moduleUrl=new URL('./program-run.mjs',import.meta.url).href;
  const scriptBody=`import(process.argv[1]).then(async ({runProgram})=>{process.exitCode=await runProgram({root:process.argv[2],file:process.argv[3],args:process.argv.slice(4),env:process.env,once:true,flags:JSON.parse(process.env.PDD_PROGRAM_FLAGS||'{}')});}).catch(()=>{process.stderr.write('The program launcher could not load. Open the prompt shell again.\\n');process.exitCode=125;});`;
  const script=`#!/bin/sh\n# PDD program launcher v1\nexec ${quote(process.execPath)} --input-type=commonjs -e ${quote(scriptBody)} -- ${quote(moduleUrl)} ${quote(root)} ${quote(file)} "$@"\n`;
  try {const info=lstatSync(launcher);if(!info.isFile()||info.nlink!==1)fail('Refusing an unsafe program launcher.');const st=readFileSync(launcher,'utf8');if(!st.startsWith('#!/bin/sh\n# PDD program launcher v1\n'))fail('Refusing to overwrite an existing launcher.');}catch(e){if(e.code!=='ENOENT')throw e;}
  const fd=openSync(launcher,constants.O_WRONLY|constants.O_CREAT|constants.O_TRUNC|constants.O_NOFOLLOW,0o700);try{writeFileSync(fd,script);}finally{closeSync(fd);}chmodSync(launcher,0o700);
  ports.stdout.write('Answers come from prompts on the PDD interpreter, not installed code.\n');
  ports.stdout.write(`${name} works only in this shell; exit removes its PATH context. Another terminal: export PATH=${quote(bin)}:"$PATH"\n`);
  const requested=env.SHELL||'/bin/sh',shell=['sh','bash','zsh'].includes(basename(requested))?requested:'/bin/sh';
  const shellEnv={...env,PATH:bin+':'+(env.PATH??''),PDD_PROGRAM_FLAGS:JSON.stringify(Object.fromEntries(Object.entries(flags).filter(([k])=>!['fresh','data','read','show-data'].includes(k))))};
  if(ports.shell)return ports.shell(shell,shellEnv);
  return new Promise((done,reject)=>{const child=spawn(shell,['-i'],{cwd:root,env:shellEnv,stdio:'inherit'});child.once('error',reject);child.once('exit',(code,signal)=>done(code??(signal?130:0)));});
}
export async function runProgram({file,args=[],root=process.cwd(),env=process.env,flags={},once=false},givenPorts={}) {
  const ports={stdout:process.stdout,stderr:process.stderr,stdin:process.stdin,...givenPorts,env};
  const quiet=flags.q||flags.quiet;let usage,unlock,session,usagePrinted=false;
  const summary=(cached=false)=>{if(!quiet){ports.stderr.write(cached?'pdd: cached · 0 AI calls\n':`pdd: ${usage?.calls??'unknown'} AI calls · ${usage?.seconds??'unknown'} s${session?.draft?' · DRAFT':''}${session?.newSession?' · prompt behavior, not tested code':''}\n`);}usagePrinted=true;};
  try {
    const found=spawnSync('git',['rev-parse','--show-toplevel'],{cwd:root,encoding:'utf8',stdio:['ignore','pipe','pipe']});if(found.status!==0)throw localError('Run the prompt inside a Git repository.');
    const cwd=root;root=found.stdout.trim();file=relative(root,resolve(cwd,file)).split('\\').join('/');
    const visible=new Set(gitFiles(root)),prompt=readPrompt(root,visible,file);if(prompt.error)throw localError(`Cannot read ${file}: ${prompt.error}.`);
    let app=ports.programApp;try{if(!app)app=await import('./program-app.mjs');}catch(e){if(e.code!=='ERR_MODULE_NOT_FOUND'||!e.message.includes('/program-app.mjs'))throw e;}
    const appKind=app?await app.appKind({file,root},ports):null;
    const entries=prompt.interface.entries??[];
    if(appKind)return await app.runApp({file,root,env,flags},ports);
    const cliIndex=entries.findIndex((e,i)=>['input_schema','result_schema'].every(key=>(prompt.interface.conventions??[]).some(c=>c.path===`/entries/${i}/${key}`&&c.convention==='cli')));
    const cli=cliIndex>=0;let entry=cli?entries[cliIndex]:entries.length===1?entries[0]:undefined;
    if(!entries.length){ports.stderr.write(fallback+'\n');return 2;}
    const usageText=`Usage: pdd ${file}${entries.length>1?' '+entries.map(e=>e.operation).join('|'):''} ${Object.keys((entry??entries[0]).input_schema?.properties??{}).map(k=>'--'+k+' VALUE').join(' ')}\n`;
    if(!cli&&args.includes('--help')){ports.stdout.write(usageText);return 0;}
    let input,name;
    const schemaIssues=interfaceSchemaProblems(prompt.interface);if(schemaIssues.length){ports.stderr.write(usageText+schemaIssues.map(i=>i.pointer+' '+i.rule).join('\n')+'\n');return 2;}
    try {
      if(cli){name=prompt.text.match(/^#\s+(.+?)\s*$/m)?.[1]?.replace(/^`([^`]+)`$/,'$1');if(!args.length&&!once&&!flags.read&&(!/^[A-Za-z][A-Za-z0-9._-]{0,63}$/.test(name??'')||['pdd','node','gh','git'].includes(name.toLowerCase())))throw localError('Name the program with a safe first heading; pdd, node, gh and git are reserved.');
        input={argv:args};if((args.length||once)&&!flags.read){if(entry.input_schema.properties?.stdin&&!ports.stdin?.isTTY)input.stdin=await stdinText(ports.stdin);else if(entry.input_schema.required?.includes('stdin'))input.stdin='';validate(input,entry.input_schema);}
      }else if(!flags.read){if(entries.length>1){entry=entries.find(e=>e.operation===args[0]);if(!entry)throw localError('Choose an operation: '+entries.map(e=>e.operation).join(', '));args=args.slice(1);}input=await typedInput(args,entry,cwd,ports.stdin);validate(input,entry.input_schema);}
    }catch(e){ports.stderr.write(usageText+(e.message??'Invalid input.')+'\n');return 2;}
    const program=file.slice(0,-'.prompt.md'.length);
    const data=programData({root,program,flags:{...flags,...(flags.data?{data:resolve(cwd,flags.data)}:{})}},ports);
    if(flags['show-data']){ports.stdout.write(JSON.stringify(data.startingData.initial_world)+'\n');return 0;}
    unlock=acquireProgramLock(data.dir);
    if(cli&&!args.length&&!flags.read&&!once){
      estimate(root,visible,file);
      session=await openProgramSession({root,file,program,data},ports);
      unlock();unlock=undefined;
      return await shellProgram({root,file,name,env,flags,data},ports);
    }
    let answer,record,before=data.startingData.initial_world;
    if(flags.read){
      const saved=readPrivate(join(data.dir,'session.json'),null);if(!saved?.pending||saved.pending.id!==flags.read)fail('No matching pending request belongs to this program.');
      
      const transport=programTransport({root,expectedLogin:saved.login},ports);if(saved.origin!==transport.origin)fail('The saved request belongs to another interpreter origin.');
      session={...saved,transport,newSession:false,save:r=>writePrivate(join(data.dir,'session.json'),r)};
      if(saved.pending.command!=='call'){
        const command=saved.pending.command;
        answer=await transport.finish(await transport.get(flags.read),flags.read,command);
        if(answer.state!=='passed')fail('Program setup was refused. Fix the prompt before trying again.');
        const updated={...saved};delete updated.pending;
        if(command==='stop'){delete updated.id;}
        if(command==='try'){if(answer.result?.session?.state!=='running')fail('Program setup did not confirm a running session. Read the saved setup again.');Object.assign(updated,{id:answer.result.session.id,url:answer.result.url,remaining:answer.result.session.remaining_calls});writePrivate(join(data.dir,'data.json'),saved.pending.initial_world);}
        session.save(updated);ports.stdout.write('Program setup confirmed. Run the prompt again.\n');return 0;
      }
      input=saved.pending.input;entry=entries.find(e=>e.operation===saved.pending.operation);if(!entry)fail('The pending operation is no longer in this prompt. Restore its source before reading.');before=saved.pending.before;
      answer=await transport.finish(await transport.get(flags.read),flags.read,'call',{sessionId:saved.id});
    }else{
      usage={calls:0,seconds:0};
      const worst=estimate(root,visible,file),cap=flags['max-calls']===undefined?worst:Number(flags['max-calls']);
      if(flags['max-calls']!==undefined&&(!Number.isInteger(cap)||cap<1||cap>1000))throw localError('--max-calls must be from 1 to 1000.');
      if(cap<worst)fail(`This prompt may need ${worst} AI calls. Raise --max-calls; no call was dispatched.`);
      if(cap>20)ports.stderr.write(`pdd: may use up to ${cap} AI calls.\n`);
      usage=undefined;
      session=await openProgramSession({root,file,program,data},ports);session.draft=session.capture.sources.filter(s=>s.path.endsWith('.prompt.md')).some(s=>/"status"\s*:\s*"draft"/.test(s.bytes.toString()));
      record=sessionRecord(session);
      const last=readPrivate(join(data.dir,'last.json'),null);
      if(!data.fresh&&!data.explicit&&last?.source===session.source&&last.login===session.login&&last.origin===session.origin&&last.operation===entry.operation&&JSON.stringify(last.input)===JSON.stringify(input)&&JSON.stringify(last.data_before)===JSON.stringify(before)&&last.cacheable){
        summary(true);if(cli){ports.stdout.write(last.output.stdout);ports.stderr.write(last.output.stderr);return last.output.exit_code;}ports.stdout.write(JSON.stringify(last.output)+'\n');return 0;
      }
      if(session.remaining<cap){usage={calls:0,seconds:0};fail('No AI calls remain for this call. Start fresh with a sufficient session budget.');}
      const id=session.transport.ports.randomUUID();record.pending={id,command:'call',input,operation:entry.operation,before};session.save(record);
      let interrupted=false;const off=session.transport.ports.onInterrupt(()=>{interrupted=true;});
      try{const reply=await session.transport.call(session.id,{requestId:id,prompt:file,operation:entry.operation,input,max_calls:cap});if(interrupted)throw Object.assign(new Error('Interrupted.'),{exitCode:130,requestId:id});answer=await session.transport.finish(reply,id,'call',{sessionId:session.id});}finally{off();}
    }
    usage=answer.usage;const report=answer.result?.report??{},result=report.result??answer.result?.program_result;
    let world=report.world??answer.result?.world;
    if(report.action_id){const state=await session.transport.state(session.id);const action=state.status===200&&Array.isArray(state.json?.actions)?state.json.actions.find(a=>a.action_id===report.action_id):null;if(action){if(object(action.world))world=session.transport.redact(action.world);if(object(action.input_world))before=session.transport.redact(action.input_world);}}
    if(report.error||report.refusal||answer.state!=='passed')trace(report,text=>ports.stderr.write(text),session.transport.sanitize);
    if(!object(world))fail(`The interpreter did not confirm the program data. Read the accepted request with pdd --read ${session.pending?.id??record?.pending?.id??answer.requestId} ${file}; do not repeat it.`);
    if(object(world))writePrivate(join(data.dir,'data.json'),world);
    record=sessionRecord(session);delete record.pending;record.world=world;if(Number.isFinite(report.remaining_calls))record.remaining=report.remaining_calls;session.save(record);
    if(report.error||report.refusal||answer.state!=='passed'){
      writePrivate(join(data.dir,'last.json'),session.transport.redact({input,operation:entry.operation,output:report.error??report.refusal??null,data_before:before,data_after:world,ai_calls:usage?.calls,source:session.source,login:session.login,origin:session.origin,cacheable:false}));
      summary();if(report.error)return 1;if(!report.refusal)ports.stderr.write('The interpreter refused this call. Fix the prompt and try again.\n');return 125;
    }
    if(result===undefined)fail('The interpreter result is missing. Fix its result schema before running again.');
    if(cli&&(typeof result.stdout!=='string'||typeof result.stderr!=='string'||!Number.isInteger(result.exit_code)||result.exit_code<0||result.exit_code>255||result.exit_code===125))fail('The CLI result must contain stdout, stderr and exit_code 0–255 except reserved 125.');
    try{validate(result,entry.result_schema);}catch(e){fail('Invalid interpreter result: '+e.message);}
    writePrivate(join(data.dir,'last.json'),session.transport.redact({input,operation:entry.operation,output:result,data_before:before,...(object(world)?{data_after:world}:{}),ai_calls:usage?.calls,source:session.source,login:session.login,origin:session.origin,cacheable:object(world)}));
    if(cli){ports.stdout.write(result.stdout);ports.stderr.write(result.stderr);if(result.stderr&&!result.stderr.endsWith('\n')&&!quiet)ports.stderr.write('\n');summary();return result.exit_code;}
    ports.stdout.write(JSON.stringify(result)+'\n');summary();return 0;
  }catch(e){ports.stderr.write((session?.transport?.sanitize(e.message)??e.message??'The program could not run.')+'\n');if(e.requestId)ports.stderr.write(`pdd --read ${e.requestId} ${file}\n`);if(!usagePrinted&&(e.exitCode??125)!==2)summary();return e.exitCode??125;}finally{unlock?.();}
}
