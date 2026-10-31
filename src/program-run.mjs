// Generated from prompts/cli/program-run.prompt.md (sha256: fa60143ec8762e0467c457a00885e524dfa92c87f74381efaa50f02beadc1b46).
import { spawn, spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync, chmodSync, lstatSync, openSync, closeSync, constants } from 'node:fs';
import { basename, join, relative, resolve, posix } from 'node:path';
import { gitFiles, readPrompt, checkInput, interfaceSchemaProblems } from './runtime-preflight.mjs';
import { programData, renderResetNotice, readPrivate, writePrivate, safeDirectory, localError, object, acquireProgramLock } from './program-data.mjs';
import { openProgramSession } from './program-session.mjs';
import { programTransport } from './runtime-client.mjs';
const quote=word=>"'"+word.replaceAll("'","'\\''")+"'";
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
  if(!args.length){const text=await stdinText(stdin);if(!text.trim())throw localError('Supply input flags or piped JSON.');return JSON.parse(text);}
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
function estimate(root,visible,file,operation,simulation={}) {
  let external=false;
  function visit(path,selected,stack=new Set()) {
    const key=JSON.stringify([path,selected]);
    if(stack.has(key))fail('The prompt call graph has a cycle; set a finite graph before running.');
    const prompt=readPrompt(root,visible,path);if(prompt.error)fail(`Cannot read ${path}: ${prompt.error}.`);
    const issues=interfaceSchemaProblems(prompt.interface);if(issues.length)throw localError(`${path}: ${issues.map(i=>i.pointer+' '+i.rule).join('; ')}`);
    const entry=prompt.interface.entries.find(e=>e.operation===selected);if(!entry)fail(`Cannot find operation ${selected} in ${path}.`);
    const next=new Set(stack).add(key);let cap=1;
    const add=(bound,cost)=>{if(!Number.isInteger(bound)||bound<0)fail('The prompt call budget cannot be determined.');cap+=bound*(cost+1);if(!Number.isSafeInteger(cap))fail('The prompt call budget is too large.');};
    for(const call of prompt.interface.calls??[])if(entry.call_operations===undefined||entry.call_operations.includes(call.operation))add(call.max_calls,visit(call.target,call.target_operation,next));
    for(const resource of prompt.interface.resources??[])for(const op of resource.operations??[]) {
      const name=resource.name+'.'+op.name;if(entry.resource_operations!==undefined&&!entry.resource_operations.includes(name))continue;
      const binding=simulation[name];
      if(['http.prompt','port.prompt'].includes(binding?.action))add(binding.max_calls,visit(binding.target,binding.operation,next));
      else if(binding?.action==='service.prompt'||(!binding&&['http','command','model','port'].includes(resource.kind)&&!(resource.kind==='port'&&resource.name.toLowerCase()==='clock'&&['now','read','time'].includes(op.name.toLowerCase())&&op.access!=='write')))add(Math.min(20,prompt.interface.limits.max_steps),1);
      else external=true;
    }
    return cap;
  }
  const worst=visit(file,operation);
  const declared=readPrompt(root,visible,file).interface.limits.max_model_calls;
  return external?Math.max(worst,20,declared):worst;
}
function trace(report,write,sanitize) {
  if(Array.isArray(report.call_chain)&&report.call_chain.length){write('Traceback (prompt calls, most recent call last):\n');for(const frame of report.call_chain)write(`  ${sanitize(frame.prompt)}, operation ${sanitize(frame.operation)}${frame.call_index!=null&&frame.max_calls!=null?` (call ${frame.call_index} of at most ${frame.max_calls})`:''}\n`);}
  if(report.call_chain_total>(report.call_chain?.length??0))write(`${report.call_chain_total} total prompt calls; ${report.call_chain_total-(report.call_chain?.length??0)} frames omitted.\n`);
  const error=report.error??report.refusal;if(error)write(`${sanitize(error.code)}${error.message===undefined?'':`: ${sanitize(error.message)}`}\n`);
}
function sessionRecord(session) {
  const {transport,capture,newSession,save,serve,...record}=session;return record;
}
async function shellProgram({root,file,name,env,flags,data},ports) {
  const bin=safeDirectory(root,[...relative(root,data.dir).split('/'),'bin']);
  const launcher=join(bin,name);
  const moduleUrl=new URL('./program-run.mjs',import.meta.url).href;
  const scriptBody=`import(process.argv[1]).then(async ({runProgram})=>{process.exitCode=await runProgram({root:process.argv[2],file:process.argv[3],args:process.argv.slice(4),env:process.env,once:true,flags:JSON.parse(process.env.PDD_PROGRAM_FLAGS||'{}')});}).catch(()=>{process.stderr.write('pdd: The program launcher could not load. Open the prompt shell again.\\n');process.exitCode=125;});`;
  const script=`#!/bin/sh\n# PDD program launcher v1\nexec ${quote(process.execPath)} --input-type=commonjs -e ${quote(scriptBody)} -- ${quote(moduleUrl)} ${quote(root)} ${quote(file)} "$@"\n`;
  try {const info=lstatSync(launcher);if(!info.isFile()||info.nlink!==1)fail('Refusing an unsafe program launcher.');const st=readFileSync(launcher,'utf8');if(!st.startsWith('#!/bin/sh\n# PDD program launcher v1\n'))fail('Refusing to overwrite an existing launcher.');}catch(e){if(e.code!=='ENOENT')throw e;}
  const fd=openSync(launcher,constants.O_WRONLY|constants.O_CREAT|constants.O_TRUNC|constants.O_NOFOLLOW,0o700);try{writeFileSync(fd,script);}finally{closeSync(fd);}chmodSync(launcher,0o700);
  if(!ports.stdin?.isTTY){ports.stdout.write(`export PATH=${quote(bin)}:$PATH   # then: ${name} --help\n`);return 0;}
  if(!flags.q&&!flags.quiet){ports.stderr.write(`pdd: "${name}" is a command in this shell. Type exit to leave.\npdd: data: ${relative(root,data.dir)}/ (kept between runs) · prompt behavior, not tested code\n`);}
  const requested=env.SHELL||'/bin/sh',shell=['sh','bash','zsh'].includes(basename(requested))?requested:'/bin/sh';
  const shellEnv={...env,PATH:bin+':'+(env.PATH??''),PDD_PROGRAM_FLAGS:JSON.stringify(Object.fromEntries(Object.entries(flags).filter(([k])=>!['reset','data','read','show-data'].includes(k))))};
  if(ports.shell)return ports.shell(shell,shellEnv);
  return new Promise((done,reject)=>{const child=spawn(shell,['-i'],{cwd:root,env:shellEnv,stdio:'inherit'});child.once('error',reject);child.once('exit',(code,signal)=>done(code??(signal?130:0)));});
}
export async function runProgram({file,args=[],root=process.cwd(),env=process.env,flags={},once=false},givenPorts={}) {
  const ports={stdout:process.stdout,stderr:process.stderr,stdin:process.stdin,...givenPorts,env};
  const quiet=flags.q||flags.quiet;const sessionPorts={...ports,programQuiet:!!quiet};const originalFile=file,originalArgs=[...args];let usage,unlock,session,callCap,admissionBound,usagePrinted=false;
  const capAdvice=()=>{const next=Math.max(admissionBound??0,(callCap??0)+1);return next<=1000?`pdd --max-calls ${next} ${[originalFile,...originalArgs].map(word=>/^[A-Za-z0-9_./-]+$/.test(word)?word:quote(word)).join(' ')}`:'Reduce the prompt call graph before trying again.';};
  const summary=(cached=false)=>{if(!quiet){ports.stderr.write(cached?'pdd: cached · 0 AI calls\n':`pdd: ${usage?.calls??'unknown'} AI call${usage?.calls===1?'':'s'} · ${Number.isFinite(usage?.seconds)?Math.round(usage.seconds):'unknown'} s${session?.draft?' · DRAFT':''}${session?.newSession?' · prompt behavior, not tested code':''}\n`);}usagePrinted=true;};
  try {
    const found=spawnSync('git',['rev-parse','--show-toplevel'],{cwd:root,encoding:'utf8',stdio:['ignore','pipe','pipe']});if(found.status!==0)throw localError('Run the prompt inside a Git repository.');
    const cwd=root;root=found.stdout.trim();file=relative(root,resolve(cwd,file)).split('\\').join('/');
    const visible=new Set(gitFiles(root)),prompt=readPrompt(root,visible,file);if(prompt.error)throw localError(`Cannot read ${file}: ${prompt.error}.`);
    let app=ports.programApp;try{if(!app)app=await import('./program-app.mjs');}catch(e){if(e.code!=='ERR_MODULE_NOT_FOUND'||!e.message.includes('/program-app.mjs'))throw e;}
    const classification=app?await app.appKind({file,root,all:true},ports):null;
    const entries=prompt.interface.entries??[];
    const cliEntries=entries.filter((e,i)=>['input_schema','result_schema'].every(key=>(prompt.interface.conventions??[]).some(c=>c.path===`/entries/${i}/${key}`&&c.convention==='cli')));
    if(cliEntries.length>1)throw localError('Multiple CLI entries cannot run together.');
    const kinds=typeof classification==='string'?[classification]:classification?.kinds??[];
    const httpOperations=typeof classification==='string'?entries.filter(e=>!cliEntries.includes(e)).map(e=>e.operation):classification?.httpOperations??[];
    const screenOperations=typeof classification==='string'?[]:classification?.screenOperations??[];
    const typed=entries.filter(e=>!cliEntries.includes(e)&&!httpOperations.includes(e.operation)&&!screenOperations.includes(e.operation));
    const available=[...(cliEntries.length?['cli']:[]),...(typed.length?['call']:[]),...kinds.map(k=>k==='screen'?'app':k)];
    const declaration=prompt.interface.start;
    const declarationUsage=()=>`pdd: Usage: pdd ${file} ${(declaration?.dispatch??[]).map(row=>row.word).join('|')} [ARGS]\n`;
    let selected,recoveredData;
    if(flags.read){
      recoveredData=programData({root,program:file.slice(0,-'.prompt.md'.length),flags:{}},ports);
      const saved=readPrivate(join(recoveredData.dir,'session.json'),null);
      if(!saved?.pending||saved.pending.id!==flags.read)fail('No matching pending request belongs to this program.');
      if(saved.pending.command==='call'){
        const entry=entries.find(e=>e.operation===saved.pending.operation);
        if(!entry)fail('The pending operation is no longer in this prompt. Restore its source before reading.');
        selected={kind:cliEntries.includes(entry)?'cli':'typed',entry};
      }else selected={kind:'setup',entry:entries[0]};
    }else if(once){selected={kind:'cli',entry:cliEntries[0]};if(!selected.entry)throw localError('No CLI entry belongs to this launcher.');}
    else if(declaration!==undefined){
      const invalid=()=>{throw localError('Invalid start declaration in Interface.');};
      if(!object(declaration)||!Object.keys(declaration).every(k=>['default','default_operation','dispatch'].includes(k))||(!Object.hasOwn(declaration,'default')&&!Object.hasOwn(declaration,'dispatch')))invalid();
      const check=row=>{
        if(!object(row)||!['cli','shell','http','app','call'].includes(row.kind))invalid();
        if(row.app_map!==undefined&&(row.kind!=='app'||typeof row.app_map!=='string'||!row.app_map||/[\0-\x1f]/.test(row.app_map)||row.app_map==='.git'||row.app_map.startsWith('.git/')||row.app_map.startsWith('/')||/^[A-Za-z]:/.test(row.app_map)||row.app_map.split('/').some(p=>!p||p==='.'||p==='..'||p.includes('\\')||p.includes('\0'))))invalid();
        if(!available.includes(row.kind==='shell'?'cli':row.kind)&&!(row.kind==='app'&&row.app_map!==undefined&&app))invalid();
        if(row.kind==='call'&&!typed.some(e=>e.operation===row.operation))invalid();
        if(row.kind!=='call'&&row.operation!==undefined)invalid();
      };
      const rows=Object.hasOwn(declaration,'dispatch')?declaration.dispatch:[];if(!Array.isArray(rows))invalid();
      const words=new Set();for(const row of rows){check(row);if(!Object.keys(row).every(k=>['word','kind','operation','app_map'].includes(k))||typeof row.word!=='string'||!row.word||/\s/.test(row.word)||row.word.startsWith('-')||words.has(row.word))invalid();words.add(row.word);}
      let fallback;if(Object.hasOwn(declaration,'default')){fallback={kind:declaration.default,operation:declaration.default_operation};check(fallback);}else if(declaration.default_operation!==undefined)invalid();
      let row=rows.find(row=>row.word===args[0]);if(row)args=args.slice(1);else row=fallback;
      if(!row){ports.stderr.write(declarationUsage());return 2;}
      selected={kind:row.kind==='call'?'typed':row.kind==='app'?'screen':row.kind,entry:row.kind==='call'?typed.find(e=>e.operation===row.operation):cliEntries[0],...(row.app_map===undefined?{}:{appMap:row.app_map})};
    }else if(available.length>1){
      ports.stderr.write(`pdd: ${file} has ${available.length} kinds (${available.join(', ')}) and no "start" in its Interface.\n  Declare what starts, for example:\n  "start": {"default": "shell", "dispatch": [{"word": "runserver", "kind": "http"}]}\n`);return 2;
    }else if(cliEntries.length)selected={kind:'shell',entry:cliEntries[0]};
    else if(kinds.length)selected={kind:kinds[0]};
    else if(typed.length){
      let entry=typed.length===1?typed[0]:typed.find(e=>e.operation===args[0]);
      if(entry&&args[0]===entry.operation)args=args.slice(1);
      if(entry)selected={kind:'typed',entry};
    }
    if(selected&&['http','screen'].includes(selected.kind)){
      if(args.length)throw localError((declaration?declarationUsage().trim()+'\n':'')+(selected.kind==='http'?'HTTP programs take no ARGS. Call the link.':'Screen programs take no ARGS. Open the link.'));
      return await app.runApp({file,root,env,flags:{...flags,...(flags.data?{data:resolve(cwd,flags.data)}:{})},kind:selected.kind,...(selected.appMap===undefined?{}:{appMap:selected.appMap})},ports);
    }
    const cli=['cli','shell'].includes(selected?.kind);let entry=selected?.entry;
    if(!entries.length&&!available.length&&!recoveredData){
      ports.stderr.write(`pdd: ${file} has no entry, so it cannot run.\npdd: It is context for other prompts.\n`);
      const links=new Map();
      for(const path of visible){if(!path.endsWith('.prompt.md'))continue;const caller=readPrompt(root,visible,path);if(caller.error)continue;
        const section=caller.text.split(/^##\s+Dependencies\s*$/mi)[1]?.split(/^#{1,2}\s+/m)[0]??'';
        const targets=[...(caller.interface.calls??[]).map(c=>c.target)];
        for(const match of section.matchAll(/\]\(([^)#]+)(?:#[^)]*)?\)|^\s*[-*+]\s+`([^`]+)`/gm)){const target=match[1]??match[2];if(!/^[a-z]+:/i.test(target))targets.push(posix.normalize(posix.join(posix.dirname(path),target)));}
        links.set(path,targets);
      }
      const uses=(path,seen=new Set())=>{if(seen.has(path))return false;seen.add(path);return (links.get(path)??[]).some(target=>target===file||uses(target,seen));};
      for(const path of links.keys())if(path!==file&&uses(path))ports.stderr.write(`pdd: used by ${path}\n`);return 2;
    }
    if(!selected){ports.stderr.write(`pdd: Usage: pdd ${file} ${typed.map(row=>row.operation).join('|')} [ARGS]\n`);return 2;}
    const usageText=`pdd: Usage: pdd ${file}${entries.length>1?' '+entries.map(e=>e.operation).join('|'):''} ${Object.entries((entry??entries[0])?.input_schema?.properties??{}).map(([k,v])=>{const flag='--'+k+' '+(v.enum?v.enum.join('|'):(v.type??'JSON').toUpperCase());return ((entry??entries[0])?.input_schema.required??[]).includes(k)?flag:'['+flag+']';}).join(' ')}\n`;
    if(!cli&&args.includes('--help')){ports.stdout.write(usageText);return 0;}
    let input,name;
    const schemaIssues=interfaceSchemaProblems(prompt.interface);if(schemaIssues.length){ports.stderr.write(usageText+schemaIssues.map(i=>i.pointer+' '+i.rule).join('\n')+'\n');return 2;}
    try {
      if(cli){name=prompt.text.match(/^#\s+(.+?)\s*$/m)?.[1]?.replace(/^`([^`]+)`$/,'$1');if(selected.kind==='shell'&&!args.length&&!once&&!flags.read&&(!/^[A-Za-z][A-Za-z0-9._-]{0,63}$/.test(name??'')||['pdd','node','gh','git'].includes(name.toLowerCase())))throw localError('Name the program with a safe first heading; pdd, node, gh and git are reserved.');
        input={argv:args};if((selected.kind!=='shell'||args.length||once)&&!flags.read){if(entry.input_schema.properties?.stdin&&!ports.stdin?.isTTY)input.stdin=await stdinText(ports.stdin);else if(entry.input_schema.required?.includes('stdin'))input.stdin='';validate(input,entry.input_schema);}
      }else if(!flags.read){input=await typedInput(args,entry,cwd,ports.stdin);validate(input,entry.input_schema);}
    }catch(e){ports.stderr.write(usageText+'pdd: '+(e.message??'Invalid input.').replaceAll('\n','\npdd: ')+'\n');return 2;}
    const program=file.slice(0,-'.prompt.md'.length);
    let data=recoveredData??programData({root,program,flags:{...flags,...(flags.data?{data:resolve(cwd,flags.data)}:{})}},ports);
    if(once){const selected=readPrivate(join(data.dir,'launcher.json'),null);if(selected){data={...data,startingData:{initial_world:selected.pending?selected.initial_world:data.startingData.initial_world,...(selected.simulation===undefined?{}:{simulation:selected.simulation})},reset:false,noCache:!!(selected.noCache||data.noCache),fresh:!!(selected.noCache||data.noCache)};}}
    if(data.reset)ports.stderr.write(renderResetNotice({root,backupPath:data.backupPath,quiet}));
    if(flags['show-data']){ports.stdout.write(JSON.stringify(data.startingData.initial_world)+'\n');return 0;}
    unlock=acquireProgramLock(data.dir);
    if(selected.kind==='shell'&&!args.length&&!flags.read&&!once){
      writePrivate(join(data.dir,'launcher.json'),{...data.startingData,noCache:data.noCache,pending:true});
      if(ports.stdin?.isTTY){session=await openProgramSession({root,file,program,data},sessionPorts);}
      unlock();unlock=undefined;
      const code=await shellProgram({root,file,name,env,flags,data},ports);if(ports.stdin?.isTTY&&!quiet)ports.stderr.write(`pdd: session ended. Data saved: ${relative(root,data.dir)}/world.json\n`);return code;
    }
    let answer,record,before=data.startingData.initial_world;
    if(flags.read){
      const saved=readPrivate(join(data.dir,'session.json'),null);if(!saved?.pending||saved.pending.id!==flags.read)fail('No matching pending request belongs to this program.');
      
      const transport=programTransport({root,expectedLogin:saved.login},sessionPorts);if(saved.origin!==transport.origin)fail('The saved request belongs to another interpreter origin.');
      session={...saved,transport,newSession:false,save:r=>writePrivate(join(data.dir,'session.json'),r)};
      if(saved.pending.command!=='call'){
        const command=saved.pending.command;
        answer=await transport.finish(await transport.get(flags.read),flags.read,command);
        if(answer.state!=='passed')fail('Program setup was refused. Fix the prompt before trying again.');
        const updated={...saved};delete updated.pending;
        if(command==='stop'){delete updated.id;}
        if(command==='try'){if(answer.result?.session?.state!=='running')fail('Program setup did not confirm a running session. Read the saved setup again.');Object.assign(updated,{id:answer.result.session.id,url:answer.result.url,remaining:answer.result.session.remaining_calls});writePrivate(join(data.dir,'world.json'),saved.pending.initial_world);}
        session.save(updated);if(!quiet)ports.stderr.write('pdd: Program setup confirmed. Run the prompt again.\n');return 0;
      }
      input=saved.pending.input;entry=entries.find(e=>e.operation===saved.pending.operation);if(!entry)fail('The pending operation is no longer in this prompt. Restore its source before reading.');before=saved.pending.before;
      admissionBound=estimate(root,visible,file,entry.operation,JSON.parse(session.simulation??'null')??{});
      callCap=saved.pending.cap??Number(flags['max-calls']??Math.min(admissionBound,100));
      answer=await transport.finish(await transport.get(flags.read),flags.read,'call',{sessionId:saved.id});
    }else{
      if(data.noCache&&!quiet)ports.stderr.write(`pdd: asked again${data.reset?'':', data kept'}. The interpreter may still reuse a saved answer.\n`);
      usage={calls:0,seconds:0};
      let cap=flags['max-calls']===undefined?undefined:Number(flags['max-calls']);
      if(flags['max-calls']!==undefined&&(!Number.isInteger(cap)||cap<1||cap>1000))throw localError('--max-calls must be from 1 to 1000.');
      usage=undefined;
      session=await openProgramSession({root,file,program,data},sessionPorts);session.draft=session.capture.sources.filter(s=>s.path.endsWith('.prompt.md')).some(s=>/"status"\s*:\s*"draft"/.test(s.bytes.toString()));
      admissionBound=estimate(root,visible,file,entry.operation,JSON.parse(session.simulation??'null')??{});if(cap===undefined)cap=Math.min(admissionBound,100);
      callCap=cap;if(cap>20&&!quiet)ports.stderr.write(`pdd: may use up to ${cap} AI calls.\n`);
      record=sessionRecord(session);
      const last=readPrivate(join(data.dir,'last-run.json'),null);
      if(!data.noCache&&last?.simulation===session.simulation&&last?.cap===cap&&!session.capture.sources.some(s=>s.path.endsWith('.prompt.md')&&(readPrompt(root,visible,s.path).interface?.resources??[]).some(r=>r.name==='clock'||r.kind==='clock'))&&last?.source===session.source&&last.login===session.login&&last.origin===session.origin&&last.operation===entry.operation&&JSON.stringify(last.input)===JSON.stringify(input)&&JSON.stringify(last.data_before)===JSON.stringify(before)&&JSON.stringify(last.data_after)===JSON.stringify(before)&&last.cacheable){
        summary(true);if(flags.json){ports.stdout.write(JSON.stringify(last)+'\n');return last.exit_code;}if(cli){ports.stdout.write(last.output.stdout);ports.stderr.write(last.output.stderr);return last.output.exit_code;}ports.stdout.write(JSON.stringify(last.output)+'\n');return 0;
      }
      if(session.remaining<cap){usage={calls:0,seconds:0};fail('No AI calls remain for this call. Start a new session with a sufficient session budget, preserving the saved world.');}
      if(once){const selected=readPrivate(join(data.dir,'launcher.json'),null);if(selected?.pending)writePrivate(join(data.dir,'launcher.json'),{...selected,pending:false});}
      const id=session.transport.ports.randomUUID();record.pending={id,command:'call',input,operation:entry.operation,before,cap};session.save(record);
      let interrupted=false;const off=session.transport.ports.onInterrupt(()=>{interrupted=true;});
      try{
        const execute=async()=>{const reply=await session.transport.call(session.id,{requestId:record.pending.id,prompt:file,operation:entry.operation,input,max_calls:cap,fresh:!!data.noCache});if(interrupted)throw Object.assign(new Error('Interrupted.'),{exitCode:130,requestId:record.pending.id});return session.transport.finish(reply,record.pending.id,'call',{sessionId:session.id});};
        try{answer=await execute();}catch(error){
          if(!error.definiteAdmission){if(error.definiteRejection){const rejected=sessionRecord(session);delete rejected.pending;session.save(rejected);}throw error;}
          const stopped=sessionRecord(session);delete stopped.pending;delete stopped.id;session.save(stopped);
          session=await openProgramSession({root,file,program,data:{...data,startingData:{...data.startingData,initial_world:before}}},sessionPorts);
          record=sessionRecord(session);record.pending={id:session.transport.ports.randomUUID(),command:'call',input,operation:entry.operation,before,cap};session.save(record);
          answer=await execute();
        }
      }finally{off();}
    }
    usage=answer.usage;const report=answer.result?.report??{},result=answer.result?.output,world=answer.result?.world;
    const refusals=answer.result?.refusals===undefined?[]:answer.result.refusals;
    const validRefusal=value=>object(value)&&typeof value.code==='string'&&value.code.length>0&&typeof value.message==='string'&&value.message.length>0;
    const validRefusals=Array.isArray(refusals)&&refusals.every(validRefusal);
    const verdict=report.verdict,refusal=Array.isArray(refusals)?refusals[0]??report.refusal:report.refusal;
    const recovery=`Read the accepted request with pdd --read ${session.pending?.id??record?.pending?.id??answer.requestId} ${file}; do not repeat it.`;
    const validError=object(report.error)&&typeof report.error.code==='string'&&report.error.code.length>0&&(report.error.message===undefined||typeof report.error.message==='string');
    const outerValid=answer.state==='passed'||(['failed','refused'].includes(answer.state)&&answer.state===verdict);
    if(!object(report)||!validRefusals||!['passed','failed','refused'].includes(verdict)||!outerValid||
      (verdict==='failed'&&!validError)||
      (report.error!=null&&!validError)||
      (verdict==='passed'&&(report.error!=null||refusal!==undefined||refusals.length!==0)))fail(`Invalid interpreter terminal receipt. ${recovery}`);
    if(verdict==='passed'){
      if(result===undefined)fail(`The interpreter result is missing. ${recovery}`);
      if(cli&&(typeof result?.stdout!=='string'||typeof result?.stderr!=='string'||!Number.isInteger(result?.exit_code)||result.exit_code<0||result.exit_code>255||result.exit_code===125))fail(`The CLI result must contain stdout, stderr and exit_code 0–255 except reserved 125. ${recovery}`);
      try{validate(result,entry.result_schema);}catch(e){fail(`Invalid interpreter result: ${e.message} ${recovery}`);}
    }
    if(verdict!=='passed')trace({...report,...(!report.error&&refusal?{refusal}: {})},text=>ports.stderr.write(text.startsWith('  ')?text:'pdd: '+text),session.transport.sanitize);
    if(!object(world))fail(`The interpreter did not confirm the program data. Read the accepted request with pdd --read ${session.pending?.id??record?.pending?.id??answer.requestId} ${file}; do not repeat it.`);
    writePrivate(join(data.dir,'world.json'),world);
    record=sessionRecord(session);delete record.pending;record.world=world;if(Number.isFinite(report.remaining_calls))record.remaining=report.remaining_calls;session.save(record);
    const reportUrl=answer.report_url??report.report_url??answer.result?.report_url;
    usage={...usage,calls:usage?.calls??report.provider_calls};if(report.replayed)usage={...usage,calls:0};
    const exit=verdict==='refused'?125:verdict==='failed'?1:cli?result?.exit_code:0;
    const receipt={...report,input,operation:entry.operation,output:result??null,data_before:before,data_after:world,ai_calls:usage?.calls,source:session.source,login:session.login,origin:session.origin,simulation:session.simulation,cap:callCap,cacheable:verdict==='passed',session_id:session.id,url:session.url,report_url:reportUrl,exit_code:exit,outside_calls:report.outside_calls??[],call_chain:report.call_chain??[],refusals:answer.result?.refusals??[]};
    if(verdict!=='passed'){
      receipt.cacheable=false;writePrivate(join(data.dir,'last-run.json'),receipt);
      if(verdict==='refused')ports.stderr.write(`pdd: refused, ${usage?.calls??0} AI call${usage?.calls===1?'':'s'}.\n`);
      const error=report.error??refusal;if(error?.fix??error?.hint)ports.stderr.write(`pdd: Fix: ${error.fix??error.hint}\n`);
      if(verdict==='refused'&&error?.code==='session-call-cap')ports.stderr.write(`pdd: Fix: ${capAdvice()}\n`);
      else if(verdict==='refused'&&!error?.fix&&!error?.hint)ports.stderr.write('pdd: Fix: Fix the reported prompt or call allowance before trying again.\n');
      if(reportUrl)ports.stderr.write(`pdd: details: ${reportUrl}\n`);if(flags.json)ports.stdout.write(JSON.stringify(receipt)+'\n');summary(!!report.replayed);return exit;
    }
    writePrivate(join(data.dir,'last-run.json'),receipt);
    if(!quiet&&receipt.outside_calls.length){ports.stderr.write('pdd: outside calls:\n');for(const call of receipt.outside_calls)ports.stderr.write(`pdd:   ${session.transport.sanitize(call.summary??JSON.stringify(call))} (${session.transport.sanitize(call.mode??'unknown')}, ${session.transport.sanitize(call.source??call.level??'unknown')})\n`);}
    if(flags.json)ports.stdout.write(JSON.stringify(receipt)+'\n');else if(cli){ports.stdout.write(result.stdout);ports.stderr.write(result.stderr);if(result.stderr&&!result.stderr.endsWith('\n')&&!quiet)ports.stderr.write('\n');}else ports.stdout.write(JSON.stringify(result)+'\n');
    summary(!!report.replayed);if(!quiet&&reportUrl)ports.stderr.write(`pdd: details: ${reportUrl}\n`);return exit;
  }catch(e){if(e.runtimeCode==='session-call-cap'&&Number.isFinite(admissionBound))ports.stderr.write(`pdd: Fix: ${capAdvice()}\n`);ports.stderr.write('pdd: '+(session?.transport?.sanitize(e.message)??e.message??'The program could not run.').replaceAll('\n','\npdd: ')+'\n');if(e.requestId)ports.stderr.write(`pdd: pdd --read ${e.requestId} ${file}\n`);if(!usagePrinted&&(e.exitCode??125)!==2)summary();return e.exitCode??125;}finally{unlock?.();}
}
