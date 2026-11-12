// Generated from prompts/cli/interface-draft.prompt.md (sha256: ffefb26b5154fe96e536a04c2a1897e6d4d75ff1c901ff30525922a4e8d5482b).
import { readFileSync, writeFileSync, mkdirSync, mkdtempSync, linkSync, renameSync, rmSync, openSync, closeSync, fstatSync, chmodSync } from 'node:fs';
import { randomUUID } from 'node:crypto';
import { basename, dirname, join, relative, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { isDeepStrictEqual } from 'node:util';
import { expandSource } from './contract-refs.mjs';
import { gitFiles, findTests, readPrompt, promptRefusal, interfaceBlocks, interfaceSchemaProblems, proseSha256, sourceFilePort, sha256 } from './runtime-preflight.mjs';
import { loadRuntimeWorkspace, allowsRuntimePath, nativeWorkspaceFiles } from './runtime-workspace.mjs';

function promptPaths(root) {
  const found = findTests({root, excludeFixtureProjects:true});
  return [...found.discoveryVisible].filter(path => path.endsWith('.prompt.md')).sort();
}
export function missingInterfaces(root) {
  return promptPaths(root).filter(path => !interfaceBlocks(sourceFilePort(root).read({path}).content).length);
}
export function interfaceFindings({root, paths = promptPaths(root)}) {
  const visible = new Set(gitFiles(root));
  return paths.flatMap(path => {
    try {
      const prompt = readPrompt(root, visible, path), problem = promptRefusal(prompt, 'interface');
      if (!prompt.interface) return [{...problem,path}];
      const schema=interfaceSchemaProblems(prompt.interface).map(item => ({code:item.code,path,section:item.pointer,message:`${path} ${item.pointer} ${item.rule}`}));
      return problem && !schema.some(item=>item.code===problem.code) ? [{...problem,path},...schema] : schema;
    } catch (error) { return [{code:error.code ?? 'interface-unreadable',path,message:error.message}]; }
  });
}
export function runtimeCoverage({root, paths = promptPaths(root)}) {
  const visible = new Set(gitFiles(root));
  let checkable = 0, native_only = 0;
  for (const path of paths) {
    try {
      const prompt = readPrompt(root,visible,path);
      if (promptRefusal(prompt,'interface') || interfaceSchemaProblems(prompt.interface).length) continue;
      if (prompt.interface.kind === 'native-only') native_only++;
      else if (Array.isArray(prompt.interface.entries) && prompt.interface.entries.length && prompt.interface.entries.every(entry=>typeof entry?.operation==='string' && entry.operation.trim() && entry.input_schema && entry.result_schema)) checkable++;
    } catch { /* Missing and invalid source remains in the denominator. */ }
  }
  return {checkable,total:paths.length,native_only};
}

const git = (root,args,bytes=false) => {
  const result=spawnSync('git',args,{cwd:root,encoding:bytes ? undefined : 'utf8',stdio:['ignore','pipe','pipe'],maxBuffer:32*1024*1024});
  if (result.status !== 0) throw Error('Cannot read repository source.');
  return result.stdout;
};
function rootFor(cwd) { return git(cwd,['rev-parse','--show-toplevel']).trim(); }
const shellWord = value => /^[A-Za-z0-9_./-]+$/.test(value) ? value : "'"+value.replaceAll("'","'\\''")+"'";
const metadataFile = root => join(root,'.pdd/interface-drafts.json');
function drafts(root) {
  try { return JSON.parse(readFileSync(metadataFile(root),'utf8')); }
  catch(error) { if(error.code==='ENOENT') return {}; throw Error('Cannot read interface draft provenance.'); }
}
function saveDrafts(root, records) {
  mkdirSync(join(root,'.pdd'),{recursive:true});
  // This local folder must also stay ignored in projects that have not run setup.
  try { writeFileSync(join(root,'.pdd/.gitignore'),'*\n',{flag:'wx'}); } catch(error) {if(error.code!=='EEXIST') throw error;}
  let mode;
  try {
    // Preserve the permission check of an in-place save without truncating it.
    const descriptor=openSync(metadataFile(root),'r+');
    try { mode=fstatSync(descriptor).mode & 0o777; }
    finally { closeSync(descriptor); }
  } catch(error) { if(error.code!=='ENOENT') throw error; }
  const temporary=join(root,'.pdd',`interface-drafts-${randomUUID()}.tmp`);
  try {
    writeFileSync(temporary,JSON.stringify(records,null,2)+'\n',{flag:'wx',mode:mode===undefined ? 0o600 : mode & 0o600});
    if(mode!==undefined) chmodSync(temporary,mode);
    renameSync(temporary,metadataFile(root));
  } catch(error) {
    if(error.code==='EEXIST') throw error;
    try { rmSync(temporary,{force:true}); }
    catch(cleanup) { throw new Error(`${error.message}\nCannot remove temporary interface draft provenance: ${cleanup.message}`,{cause:error}); }
    throw error;
  }
}
function replaceDraftPrompt(root, path, next) {
  const file=join(root,path),descriptor=openSync(file,'r+');
  let mode;
  try { mode=fstatSync(descriptor).mode & 0o777; }
  finally { closeSync(descriptor); }
  const directory=mkdtempSync(join(dirname(file),`.pdd-${basename(file).slice(0,32)}-`));
  const backup=join(directory,'original'),staged=join(directory,'next');
  try {
    // Retain the original inode: recovery must not need another content write.
    linkSync(file,backup);
    writeFileSync(staged,next,{flag:'wx',mode:mode & 0o600});
    chmodSync(staged,mode);
    renameSync(staged,file);
    return {path,directory,backup};
  } catch(error) {
    try { rmSync(directory,{recursive:true,force:true}); }
    catch(cleanup) { throw new Error(`${error.message}\nCannot remove temporary draft for ${path}: ${cleanup.message}`,{cause:error}); }
    throw error;
  }
}
function restoreDraftPrompts(root, changes, error) {
  const failures=[];
  for(const {path,directory,backup} of [...changes].reverse()) {
    try {
      renameSync(backup,join(root,path));
    } catch(rollback) {
      // Leave the retained original available if restoration itself is refused.
      failures.push(`Cannot restore ${path}: ${rollback.message}`);continue;
    }
    try { rmSync(directory,{recursive:true,force:true}); }
    catch(cleanup) { failures.push(`Cannot remove temporary draft for ${path}: ${cleanup.message}`); }
  }
  return failures.length ? new Error([error.message,...failures].join('\n'),{cause:error}) : error;
}
function jsonDeclarations(text) {
  const values=[];
  try {values.push(JSON.parse(text));} catch { /* Markdown is read below. */ }
  for(const match of text.matchAll(/```json\s*\n([\s\S]*?)\n```/g)) {
    try {values.push(JSON.parse(match[1]));} catch { /* Examples with placeholders are not schemas. */ }
  }
  return values.filter(value => value && typeof value==='object' && !Array.isArray(value));
}
const objectSchema = properties => ({type:'object',properties,required:Object.keys(properties),additionalProperties:false});
const objectTransport = schema => object(schema) && (schema.type==='object' || Array.isArray(schema.oneOf) && schema.oneOf.length>0 && schema.oneOf.every(objectTransport));
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
function questionsFor(iface, problems=interfaceSchemaProblems(iface)) {
  const questions=[];
  const ask=(pointer,question)=>{if(!questions.some(item=>item.pointer===pointer && item.question===question)) questions.push({pointer,question});};
  if (!Array.isArray(iface.entries) || !iface.entries.length) ask('/entries','Which public operations must this interface expose?');
  for (const [i,entry] of (Array.isArray(iface.entries) ? iface.entries : []).entries()) {
    if (typeof entry?.operation!=='string' || !entry.operation.trim()) ask(`/entries/${i}/operation`,'What is the public operation name?');
    for (const key of ['input_schema','result_schema']) if (!object(entry?.[key])) ask(`/entries/${i}/${key}`,`What are the complete ${key} fields, types, required fields and allowed alternatives for ${entry?.operation ?? i}?`);
    if (!Array.isArray(entry?.errors)) ask(`/entries/${i}/errors`,`Which error codes can ${entry?.operation ?? i} return (or explicitly none)?`);
  }
  for (const key of ['calls','resources']) if (!Array.isArray(iface[key])) ask('/'+key,`Which ${key} are used, with their operation bindings and schemas (or explicitly none)?`);
  if (!object(iface.limits)) ask('/limits','What max_steps and max_model_calls execution ceilings should this contract use?');
  if (iface.draft_gaps !== undefined) {
    if (!Array.isArray(iface.draft_gaps)) ask('/draft_gaps','Supply a list of unresolved contract questions.');
    else for (const [i,gap] of iface.draft_gaps.entries()) {
      const saved=typeof gap==='string' && /^(\/[^:]*): ([\s\S]*)$/.exec(gap);
      ask(saved ? saved[1] : `/draft_gaps/${i}`,saved ? saved[2] : typeof gap==='string' && gap.trim() ? gap : 'Resolve this malformed draft gap.');
    }
  }
  for (const problem of problems) {
    if (problem.code==='interface-draft-incomplete') continue;
    ask(problem.pointer ?? '/',problem.rule);
  }
  if (iface.kind==='partial' && !questions.length) ask('/kind','Which contract facts remain unresolved in this partial declaration?');
  return questions;
}

// Consume each quoted example once, so an unsupported tail cannot repartition a list.
function numericExamples(sentence) {
  if(!sentence.startsWith('For example, ') || !sentence.endsWith('.')) return false;
  const end=sentence.length-1;
  let cursor='For example, '.length;
  if(cursor===end) return false;
  while(cursor<end) {
    const open=sentence.indexOf('`',cursor);
    if(open<0 || !/^[\d, -]+(?:and [\d-]+ )?(?:produce|produces) $/.test(sentence.slice(cursor,open))) return false;
    const close=sentence.indexOf('`',open+1);
    if(close<=open+1 || close>=end) return false;
    cursor=close+1;
    for(const separator of [', and ',' and ', ', ']) {
      if(sentence.startsWith(separator,cursor)) {cursor+=separator.length;break;}
    }
  }
  return cursor===end;
}

// Full-sentence grammar: unrecognized clauses never inherit a nearby sentence's mapping.
function proseCoverage(text, transport, errors) {
  const sentences=[];
  // Keep every non-heading character, including an unclosed code span or a sentence without punctuation.
  const prose=text.replace(/^#{1,6}[^\n]*$/gm,'');
  for(const paragraph of prose.split(/\n\s*\n/)) {
    let start=0,quoted=false;
    for(let i=0;i<paragraph.length;i++) {
      if(paragraph[i]==='`') quoted=!quoted;
      if(!quoted && /[.!?]/.test(paragraph[i]) && (i+1===paragraph.length || /\s/.test(paragraph[i+1]))) {
        const sentence=paragraph.slice(start,i+1).trim();if(sentence) sentences.push(sentence);start=i+1;
      }
    }
    const rest=paragraph.slice(start).trim();if(rest) sentences.push(rest);
  }
  const result='/entries/0/result_schema', input='/entries/0/input_schema';
  const grammar=[
    [/^(?:In the Runtime interface, |The Runtime interface uses JSON transport: )?operation [\s\S]+\.$/i,s=>['','In the Runtime interface, ','The Runtime interface uses JSON transport: '].some(prefix=>s===prefix+transport),[input,result]],
    [/^(?:There are |This is pure behavior: )?no external resources, operating-system commands(?:,| or) (?:or )?(?:saved data|persistent state)\.$/i,null,['/calls','/resources']],
    [/^(?:Throw a |Negative values, fractions, non-number values, NaN, infinities and unsafe integers throw )`RangeError` with `code` equal to `[^`]+`\.$/,s=>errors.some(code=>s.includes('`'+code+'`')),['/entries/0/errors']],
    [/^Public binding: module function `[^`]+` in `[^`]+`, exported (?:from|at) `[^`]+`\.$/,null,['/entries/0/operation']],
    [/^(?:It takes a Number of basis points and returns a string|It returns a string|`text` is the returned string)\.$/,null,[input,result]],
    [/^Its input schema admits representative JSON shapes for rejection; the native function rejects every non-number, including arbitrary JavaScript objects\.$/,null,[input]],
    // Numeric formatting rules are retained verbatim as result/input descriptions, not executable schema constraints.
    [/^(?:This module displays a basis-point rate as a percentage beside a price|It owns the percentage format of the library|This module formats downloaded file sizes so they are easy to scan in a list|It owns byte-count formatting)\.$/,null,[result]],
    [/^This is new behavior authorized by issue #\d+; existing price, duration and word contracts remain unchanged\.$/,null,['/entries/0/operation']],
    [/^(?:100 basis points equal one percent|Accept a Number only if it is a safe integer|Accept only a nonnegative safe integer Number, including negative zero|Do not coerce inputs|No input is rounded)\.$/,null,[input]],
    [/^(?:Show the exact rate with two decimal digits and a trailing `%`, without spaces or grouping separators|Use the magnitude for the digits and a leading minus sign for negative rates|Zero, including negative zero, is `0\.00%`|Rates above 100 percent are allowed; do not clamp or round|Use powers of 1,024 for B, KiB, MiB, GiB, TiB and PiB, respectively|Select the largest unit whose size is no greater than the input, capped at PiB; zero uses B|Divide by that unit's size and round down to a whole number|Return its ungrouped decimal digits, one space, and the unit name)\.$/,null,[result]],
    [/^For example, (?:-?\d+ is `-?[0-9.]+%`(?:, |, and | and )?)+\.$/,null,[result]],
    [/^For example, /,numericExamples,[result]],
    [/^Fractions, non-number values, NaN, infinities and unsafe integers are refused\.$/,null,['/entries/0/errors']],
    [/^(?:Preserve existing helpers and add no dependencies|None)\.$/,null,['/calls','/resources']],
  ];
  if(!transport) return sentences.map(sentence=>({sentence,pointers:[]}));
  return sentences.map(sentence=>({sentence,pointers:grammar.find(([pattern,guard])=>pattern.test(sentence) && (!guard || guard(sentence)))?.[2] ?? []}));
}
const transportDeclaration = text => /\boperation\s+`([\w$]+)`\s+takes an object with required\s+(?:(numeric|number|string|boolean|integer)\s+)?`([\w$]+)`(?: and no other properties)?,? and returns an object with required\s+(numeric|number|string|boolean|integer)\s+`([\w$]+)`(?:, the returned string; neither object has additional properties| and no other properties)\./i.exec(text);
function proseInterface(text, transportOnly=false) {
  // This grammar requires explicit transport facts. Business-domain names and examples do not supply types.
  const transport=transportDeclaration(text);
  const operation=transport && [transport[0],transport[1],transport[2],transport[3]];
  const result=transport && [transport[0],transport[4],transport[5]];
  const pure=/(?:no|neither) external resources, operating-system commands(?:,| or) (?:or )?(?:saved data|persistent state)/i.test(text);
  const noDependencies=/^## Dependencies\s+None\.\s*$/m.test(text);
  if (!operation || !result || !transportOnly && (!pure || !noDependencies || [...text.matchAll(/\boperation\s+`([\w$]+)`/g)].length!==1)) return null;
  let type=operation[2]?.toLowerCase();
  const representative=/input schema admits representative JSON shapes for rejection/i.test(text) && /rejects every non-number/i.test(text);
  if (!type && !representative) return null;
  if(type==='numeric') type='number';
  const input=representative ? {oneOf:[{type:'number'},{type:'string'},{type:'boolean'},{type:'null'},{type:'array',items:{type:'number'}},objectSchema({})]} : {type};
  const errors=[...text.matchAll(/\bcode`?\s+equal to\s+`([^`]+)`/g)].map(match=>match[1]);
  const iface={kind:'full',status:'draft',prose_sha256:'',entries:[{operation:operation[1],input_schema:objectSchema({[operation[3]]:input}),result_schema:objectSchema({[result[2]]:{type:result[1]==='numeric'?'number':result[1]}})}],calls:[],resources:[],limits:{max_steps:4,max_model_calls:2},conventions:[]};
  if(!/\b(?:throw|throws|refuse|refused|reject|rejects|error|errors|exception)\b/i.test(text) || errors.length && [...text.matchAll(/\bcode\b/g)].length===errors.length) iface.entries[0].errors=[...new Set(errors)];
  const coverage=proseCoverage(text,transport[0],errors);
  for (const key of ['input_schema','result_schema']) iface.entries[0][key].description=coverage.filter(row=>row.pointers.includes('/entries/0/'+key) || key==='input_schema' && row.pointers.length>0).map(row=>row.sentence).join(' ');
  return {iface,coverage};
}
function declarationError(pointer,rule) {
  return Object.assign(Error(`${pointer}: ${rule}`),{code:'interface-contract-invalid',pointer,rule});
}
function completeContract(value) {
  if (!object(value)) throw declarationError('','Use one JSON interface object.');
  if (Object.hasOwn(value,'kind') && value.kind!=='full') throw declarationError('/kind','Supply a full executable contract.');
  const allowed=['kind','status','prose_sha256','entries','calls','resources','limits','conventions','schema_version','instance_types'];
  for(const key of Object.keys(value)) if(!allowed.includes(key)) throw declarationError('/'+key,'Unknown interface field; declare effect ports in resources.');
  const iface={...value,status:'draft',prose_sha256:''};
  delete iface.kind;
  const fields=(item,names,pointer)=>{for(const key of Object.keys(item)) if(!names.includes(key)) throw declarationError(pointer+'/'+key,'Unknown declaration field.');};
  const questions=questionsFor(iface);
  if (questions.length) throw declarationError(questions[0].pointer,questions[0].question);
  const unique=(items,key,pointer)=>{
    if(!Array.isArray(items)) throw declarationError(pointer,'Must be an array.');
    const seen=new Set();
    for(const [i,item] of items.entries()) {
      if(!object(item) || typeof item[key]!=='string' || !item[key].trim() || seen.has(item[key])) throw declarationError(`${pointer}/${i}/${key}`,'Use a unique nonblank name.');
      seen.add(item[key]);
    }
  };
  unique(iface.entries,'operation','/entries');unique(iface.calls,'operation','/calls');unique(iface.resources,'name','/resources');
  for(const [i,entry] of iface.entries.entries()) {
    fields(entry,['operation','input_schema','result_schema','errors','instance','resource_operations','copy_out'],`/entries/${i}`);
    if(Object.hasOwn(entry,'instance')) {
      const binding=entry.instance,pointer=`/entries/${i}/instance`;
      if(!object(binding)) throw declarationError(pointer,'Declare a factory or method binding object.');
      fields(binding,['kind','type','path'],pointer);
      if(!['factory','method'].includes(binding.kind)) throw declarationError(pointer+'/kind','Use factory or method.');
      if(typeof binding.type!=='string' || !binding.type.trim() || !Array.isArray(iface.instance_types) || !iface.instance_types.some(type=>type?.name===binding.type)) throw declarationError(pointer+'/type','Name the instance type.');
      if(typeof binding.path!=='string' || !binding.path.startsWith('/')) throw declarationError(pointer+'/path','Use the handle JSON pointer.');
    }
    if(Object.hasOwn(entry,'copy_out')) {
      if(!Array.isArray(entry.copy_out)) throw declarationError(`/entries/${i}/copy_out`,'Declare copy-out path/schema rows.');
      for(const [j,row] of entry.copy_out.entries()) {
        if(!object(row) || typeof row.path!=='string' || !row.path.startsWith('/') || !object(row.post_schema)) throw declarationError(`/entries/${i}/copy_out/${j}`,'Declare a JSON path and post_schema.');
        fields(row,['path','post_schema'],`/entries/${i}/copy_out/${j}`);
        const problems=interfaceSchemaProblems({limits:iface.limits,entries:[{input_schema:row.post_schema}]});
        if(problems.length) throw declarationError(`/entries/${i}/copy_out/${j}/post_schema`,problems[0].rule);
      }
    }
    if(Object.hasOwn(entry,'resource_operations') && (!Array.isArray(entry.resource_operations) || entry.resource_operations.some(name=>typeof name!=='string' || !name.trim()))) throw declarationError(`/entries/${i}/resource_operations`,'List the bound resource operations.');
    if(entry.errors.some(code=>typeof code!=='string' || !code.trim()) || new Set(entry.errors).size!==entry.errors.length) throw declarationError(`/entries/${i}/errors`,'Use unique nonblank error codes.');
  }
  for(const [i,call] of iface.calls.entries()) {
    fields(call,['operation','target','target_operation','max_calls'],`/calls/${i}`);
    if(typeof call.target!=='string' || !/^(?!\/)(?!.*(?:^|\/)\.\.(?:\/|$)).+\.prompt\.md$/.test(call.target)) throw declarationError(`/calls/${i}/target`,'Name a repository-relative target prompt.');
    if(typeof call.target_operation!=='string' || !call.target_operation.trim()) throw declarationError(`/calls/${i}/target_operation`,'Name the target operation.');
    if(!Number.isSafeInteger(call.max_calls) || call.max_calls<1) throw declarationError(`/calls/${i}/max_calls`,'Declare a positive safe integer call ceiling.');
  }
  for(const [i,resource] of iface.resources.entries()) {
    const pointer=`/resources/${i}`;
    fields(resource,['name','kind','access','operations'],pointer);
    if(!['port','sql','blob','compute','collection'].includes(resource.kind)) throw declarationError(pointer+'/kind','Use port, sql, blob, compute or collection.');
    if(!['read','write'].includes(resource.access)) throw declarationError(pointer+'/access','Declare read or write access.');
    unique(resource.operations,'name',pointer+'/operations');
    if(!resource.operations.length) throw declarationError(pointer+'/operations','Declare at least one bound operation.');
    for(const [j,operation] of resource.operations.entries()) {
      const opPointer=pointer+`/operations/${j}`;
      fields(operation,['name','access','arguments_schema','result_schema'],opPointer);
      if(!['read','write'].includes(operation.access)) throw declarationError(opPointer+'/access','Declare read or write access.');
      if(resource.access==='read' && operation.access==='write') throw declarationError(opPointer+'/access','A read resource cannot bind a write operation.');
      for(const key of ['arguments_schema','result_schema']) if(!objectTransport(operation[key])) throw declarationError(opPointer+'/'+key,'Declare a complete closed object schema.');
    }
  }
  if(Object.hasOwn(iface,'schema_version') && !['prompt-runtime.interface.v1','prompt-runtime.interface.v2'].includes(iface.schema_version)) throw declarationError('/schema_version','Use a supported Runtime interface version.');
  if(Object.hasOwn(iface,'instance_types')) {
    if(iface.schema_version!=='prompt-runtime.interface.v2') throw declarationError('/schema_version','Instance bindings require prompt-runtime.interface.v2.');
    unique(iface.instance_types,'name','/instance_types');
    for(const [i,type] of iface.instance_types.entries()) {
      fields(type,['name','resource'],`/instance_types/${i}`);
      if(!iface.resources.some(resource=>resource.name===type.resource && resource.kind==='collection' && resource.access==='write')) throw declarationError(`/instance_types/${i}/resource`,'Bind a declared write collection.');
    }
  }
  if(Object.hasOwn(iface,'conventions') && !Array.isArray(iface.conventions)) throw declarationError('/conventions','Must be an array.');
  for(const [i,convention] of (iface.conventions ?? []).entries()) {
    const pointer=`/conventions/${i}`;
    if(!object(convention)) throw declarationError(pointer,'Declare a path and convention object.');
    fields(convention,['path','convention'],pointer);
    if(typeof convention.path!=='string' || !convention.path.startsWith('/') || /~(?:[^01]|$)/.test(convention.path)) throw declarationError(pointer+'/path','Use an existing interface JSON pointer.');
    let selected=iface;
    for(const part of convention.path.slice(1).split('/').map(part=>part.replaceAll('~1','/').replaceAll('~0','~'))) selected=object(selected)||Array.isArray(selected) ? selected[part] : undefined;
    if(selected===undefined) throw declarationError(pointer+'/path','The interface pointer does not exist.');
    if(typeof convention.convention!=='string' || !convention.convention.trim()) throw declarationError(pointer+'/convention','Name the convention.');
  }
  const problems=interfaceSchemaProblems(iface);
  if (problems.length) throw declarationError(problems[0].pointer,problems[0].rule);
  return iface;
}
function extendContract(previous, addition) {
  if(!object(addition)) throw declarationError('','Use one additive JSON contract object.');
  for(const key of Object.keys(addition)) if(!['entries','calls','resources','limits','conventions','kind','status','prose_sha256','schema_version','instance_types'].includes(key)) throw declarationError('/'+key,'Unknown extension field.');
  const merged={...previous};
  for (const [field,key] of [['entries','operation'],['calls','operation'],['resources','name'],['instance_types','name']]) {
    if(field==='instance_types' && previous[field]===undefined && addition[field]===undefined) continue;
    if(field==='instance_types' && previous[field]===undefined) merged[field]=[];
    if (field!=='instance_types' && !Array.isArray(previous[field])) throw declarationError('/'+field,'Refresh the incomplete block with a complete contract first.');
    merged[field]=[...(previous[field] ?? [])];
    if(addition[field]!==undefined && !Array.isArray(addition[field])) throw declarationError('/'+field,'Must be an array.');
    for (const item of addition[field] ?? []) {
      const index=merged[field].findIndex(old=>old[key]===item?.[key]);
      if(index<0) merged[field].push(item);
      else if(!isDeepStrictEqual(merged[field][index],item)) throw declarationError(`/${field}/${index}`,'An extension cannot change an existing declaration.');
    }
  }
  if(addition.schema_version!==undefined) {
    if(previous.schema_version!==undefined && previous.schema_version!==addition.schema_version) throw declarationError('/schema_version','An extension must preserve the declared version.');
    merged.schema_version=addition.schema_version;
  }
  for(const key of ['limits','conventions']) if(Object.hasOwn(addition,key) && !isDeepStrictEqual(previous[key],addition[key])) throw declarationError('/'+key,'An extension must preserve the existing value.');
  return merged;
}
function preservedPointers(before,after) {
  return ['entries','calls','resources','instance_types'].flatMap(key=>(before[key] ?? []).flatMap((item,i)=>isDeepStrictEqual(item,after[key]?.[i]) ? [`/${key}/${i}`] : []));
}
// Locate JSON value boundaries without reserializing existing declarations.
function bodyFields(body) {
  const stringEnd=start=>{let i=start+1;while(i<body.length && body[i]!=='"') i+=body[i]==='\\'?2:1;return i+1;};
  const whitespace=start=>{while(/\s/.test(body[start] ?? '') && start<body.length) start++;return start;};
  const fields=new Map();let at=whitespace(0)+1;
  while((at=whitespace(at))<body.length && body[at]!=='}') {
    const keyStart=at,keyEnd=stringEnd(at),key=JSON.parse(body.slice(at,keyEnd));
    at=whitespace(keyEnd)+1;const start=at=whitespace(at);let depth=0;
    do {
      const char=body[at];
      if(char==='"') {at=stringEnd(at);continue;}
      if(char==='{' || char==='[') depth++;
      if(char==='}' || char===']') {if(depth===0) break;depth--;}
      if(char===',' && depth===0) break;
      at++;
    } while(at<body.length);
    let end=at;while(/\s/.test(body[end-1])) end--;
    if(fields.has(key)) throw declarationError('/'+key,'Duplicate top-level fields cannot be extended safely.');
    fields.set(key,{keyStart,start,end,separator:at});
    if(body[at]===',') at++;
  }
  return fields;
}
function extendBody(body,previous,iface) {
  const fields=bodyFields(body),edits=[],added=[];
  for(const [key,value] of Object.entries(iface)) {
    const span=fields.get(key);
    if(!span) {added.push(JSON.stringify(key)+':'+JSON.stringify(value));continue;}
    if(isDeepStrictEqual(previous[key],value)) continue;
    if(Array.isArray(value) && Array.isArray(previous[key])) {
      const tail=value.slice(previous[key].length);
      if(tail.length) edits.push([span.end-1,span.end-1,(previous[key].length?',':'')+tail.map(item=>JSON.stringify(item)).join(',')]);
    } else edits.push([span.start,span.end,JSON.stringify(value)]);
  }
  if(fields.has('kind') && !Object.hasOwn(iface,'kind')) {
    const span=fields.get('kind');
    if(body[span.separator]===',') edits.push([span.keyStart,span.separator+1,'']);
    else {let start=span.keyStart-1;while(/\s/.test(body[start])) start--;edits.push([body[start]===','?start:span.keyStart,span.end,'']);}
  }
  if(added.length) edits.push([body.lastIndexOf('}'),body.lastIndexOf('}'),','+added.join(',')]);
  const next=edits.sort((a,b)=>b[0]-a[0]).reduce((text,[from,to,value])=>text.slice(0,from)+value+text.slice(to),body);
  if(!isDeepStrictEqual(JSON.parse(next),iface)) throw declarationError('/','Cannot preserve the existing declaration bytes safely.');
  return next;
}
const markdownFragment = title => title.toLowerCase().replace(/[^\p{L}\p{N}\s_-]/gu,'').replace(/\s+/g,'-');
function explicitAnchorId(attributes) {
  let at=0;
  while(at<attributes.length) {
    const space=/^[\t\n\f\r ]+/.exec(attributes.slice(at));
    if(!space) return null;
    at+=space[0].length;
    const name=/^[^\t\n\f\r />=]+/.exec(attributes.slice(at));
    if(!name) return null;
    at+=name[0].length;
    const gap=/^[\t\n\f\r ]*/.exec(attributes.slice(at))[0];
    at+=gap.length;
    let value=null,quoted=false;
    if(attributes[at]==='=') {
      at++;
      const beforeValue=/^[\t\n\f\r ]*/.exec(attributes.slice(at))[0];
      at+=beforeValue.length;
      const quote=attributes[at];
      if(quote==='"'||quote==="'") {
        const end=attributes.indexOf(quote,at+1);
        if(end<0) return null;
        value=attributes.slice(at+1,end);quoted=true;at=end+1;
      } else {
        const bare=/^[^\t\n\f\r "'=<>`]+/.exec(attributes.slice(at));
        if(!bare) return null;
        value=bare[0];at+=bare[0].length;
      }
    }
    if(name[0].toLowerCase()==='id'&&quoted&&value) return value;
  }
  return null;
}
function markdownSection(text, requested) {
  let fragment;
  try { fragment=decodeURIComponent(requested); }
  catch { throw declarationError('/dependencies','Required context has an invalid Markdown fragment: '+requested); }
  if(!fragment) throw declarationError('/dependencies','Required context needs a stable Markdown fragment.');
  const headings=[], anchors=[], lines=text.split(/\n/); let offset=0,fence=null;
  for(const raw of lines) {
    const line=raw.endsWith('\r') ? raw.slice(0,-1) : raw;
    const marker=/^ {0,3}(\x60{3,}|~{3,})(.*)$/.exec(line);
    if(fence) {
      if(marker && marker[1][0]===fence.char && marker[1].length>=fence.length && !marker[2].trim()) fence=null;
      offset+=raw.length+1;continue;
    }
    if(marker) { fence={char:marker[1][0],length:marker[1].length};offset+=raw.length+1;continue; }
    for(const match of line.matchAll(/<a\b([^>]*)>\s*(?:<\/a>)?/gi)) {
      const anchor=explicitAnchorId(match[1]);
      if(anchor) anchors.push({anchor,end:offset+match.index+match[0].length});
    }
    const heading=/^ {0,3}(#{1,6})[ \t]+(.+?)[ \t]*$/.exec(line);
    if(heading) {
      const title=heading[2].replace(/[ \t]+#+[ \t]*$/,'');
      headings.push({level:heading[1].length,anchor:markdownFragment(title),start:offset});
    }
    offset+=raw.length+1;
  }
  const matches=headings.filter(heading=>heading.anchor===fragment);
  for(const alias of anchors.filter(alias=>alias.anchor===fragment)) {
    const heading=headings.find(heading=>heading.start>=alias.end);
    if(heading && !text.slice(alias.end,heading.start).trim()) matches.push(heading);
  }
  const selected=[...new Set(matches)];
  if(!selected.length) throw declarationError('/dependencies','Required context has no Markdown heading for fragment: '+fragment);
  if(selected.length!==1) throw declarationError('/dependencies','Required context has an ambiguous Markdown fragment: '+fragment);
  const heading=selected[0],after=headings.find(item=>item.start>heading.start && item.level<=heading.level);
  return {anchor:fragment,text:text.slice(heading.start,after?.start)};
}
const negatedMarker=(text,marker) => new RegExp('\\bnot(?:\\s+\\w+){0,2}\\s+'+marker+'\\b','i').test(text);
function declaredDependencyLinks(section) {
  const declarations=section.split(/\n(?= {0,3}[-*+] )|\n{2,}/);
  return declarations.flatMap(declaration => {
    if(/\bnavigation[- ]only\b/i.test(declaration) && !negatedMarker(declaration,'navigation[- ]only')) return [];
    const links=[...declaration.matchAll(/\[([^\]]*)\]\(([^)\s]+)\)/g)];
    if(/^\s*[-*+]\s+/.test(declaration)) return links;
    return links.filter(link => {
      const start=declaration.lastIndexOf('\n',link.index)+1,end=declaration.indexOf('\n',link.index);
      const line=declaration.slice(start,end < 0 ? declaration.length : end);
      const bareLink=/^\s*\[[^\]]*\]\([^\s)]+\)\.?\s*$/.test(line);
      return !negatedMarker(line,'required') && (/\brequired\b/i.test(line) || bareLink);
    });
  });
}
// Load only declared context. JSON declarations are data, never prose coverage.
function draftSources(root,path,text) {
  const files=sourceFilePort(root), sources=[], visiting=new Set(), loaded=new Set();
  function load(path,text,fragment) {
    const identity=fragment === undefined ? path : path+'#'+fragment;
    if(visiting.has(identity)) throw declarationError('/dependencies','Required context contains a cycle: '+identity);
    if(loaded.has(identity)) return;
    visiting.add(identity);
    const selected=fragment === undefined ? null : markdownSection(text,fragment);
    const context=interfaceBlocks(selected ? selected.text : text).reduce((prose,block)=>prose.replace(block[0],''),selected ? selected.text : text);
    sources.push({path:identity,text:context});
    const section=/^## Dependencies\s*\n([\s\S]*?)(?=^## |$(?![\s\S]))/m.exec(context)?.[1] ?? '';
    for(const link of declaredDependencyLinks(section)) {
      const reference=link[2],at=reference.indexOf('#'),file=at<0 ? reference : reference.slice(0,at),targetFragment=at<0 ? undefined : reference.slice(at+1);
      if(/^[a-z]+:|^\//i.test(file || reference)) throw declarationError('/dependencies','Required context must name a local workspace file.');
      const target=file ? relative(root,resolve(root,join(path,'..'),file)).split('\\').join('/') : path;
      load(target,files.read({path:target}).content,targetFragment);
    }
    visiting.delete(identity);loaded.add(identity);
  }
  load(path,text);
  return sources;
}
function proseText(text) {
  try {JSON.parse(text);return '';} catch { /* Read Markdown prose below. */ }
  return text.replace(/```json\s*\n([\s\S]*?)\n```/g,(block,body)=>{
    try {JSON.parse(body);return '';} catch {return block;}
  }).replace(/^(## Dependencies\s*\n)([\s\S]*?)(?=^## |$(?![\s\S]))/m,(_all,heading,body)=>heading+body.replace(/\[([^\]]*)\]\(([^)\s]+)\)\.?/g,''));
}
const schemaMeaning=value=>{
  if(!object(value)) return value;
  const {description,title,...schema}=value;
  if(object(schema.properties)) schema.properties=Object.fromEntries(Object.entries(schema.properties).map(([key,item])=>[key,schemaMeaning(item)]));
  if(schema.items) schema.items=schemaMeaning(schema.items);
  if(Array.isArray(schema.oneOf)) schema.oneOf=schema.oneOf.map(schemaMeaning);
  return schema;
};
// Type requirements qualify retained prose. Ambiguous bindings remain review work.
const hasType=(schema,type)=>schema?.type===type || type==='number' && schema?.type==='integer' || schema?.oneOf?.some(item=>hasType(item,type));
function sentenceTypes(sentence,entry) {
  let conflicting=false,unresolved=false;
  for(const token of sentence.matchAll(/\b(Number|String|Boolean|numeric|number|string|boolean|integer)\b/g)) {
    const before=sentence.slice(0,token.index),after=sentence.slice(token.index+token[0].length);
    if(/non-$/.test(before)) continue;
    // Quantities such as "a whole number" are not transport type declarations.
    if(token[0]==='number' && /\bwhole\s+$/i.test(before) || token[0]==='integer' && /\bsafe\s+$/i.test(before)) continue;
    const left=before.split(/;|\band\b/i).at(-1),right=after.split(/;|\band\b/i)[0];
    const clause=left+token[0]+right;
    const input=/\b(?:input|takes?|accepts?)\b/i.test(clause),result=/\b(?:result|output|returns?|returned)\b/i.test(clause);
    const schemas=input===result ? ['input_schema','result_schema'] : [input?'input_schema':'result_schema'];
    const names=[...clause.matchAll(/`([\w$]+)`/g)].map(match=>match[1]);
    const named=schemas.flatMap(key=>names.flatMap(name=>entry?.[key]?.properties?.[name] ? [entry[key].properties[name]] : []));
    let target=named.length===1 ? named[0] : null;
    if(!names.length && input!==result) {
      const fields=Object.values(entry?.[schemas[0]]?.properties ?? {});
      if(fields.length===1) target=fields[0];
    }
    if(!target) {unresolved=true;continue;}
    const type=token[0].toLowerCase()==='numeric'?'number':token[0].toLowerCase();
    if(!hasType(target,type)) conflicting=true;
  }
  return {conflicting,unresolved};
}
// This is review evidence, not a proof that arbitrary prose has been compiled.
function sentenceCoverage(sources,expanded) {
  const described=[];
  const visit=(value,pointer)=>{
    if(!object(value)) return;
    if(typeof value.description==='string') described.push({pointer,meaning:value});
    for(const [key,child] of Object.entries(value)) {
      const next=pointer+'/'+key.replaceAll('~','~0').replaceAll('/','~1');
      if(Array.isArray(child)) child.forEach((item,i)=>visit(item,next+'/'+i));
      else visit(child,next);
    }
  };
  visit(expanded,'');
  return sources.flatMap((source,index)=>{
    const prose=proseText(source.text),expected=proseInterface(prose,true)?.iface;
    const declaration=transportDeclaration(prose);
    const entryIndex=expected ? expanded.entries?.findIndex(entry=>entry.operation===expected.entries[0].operation) : -1;
    const actual=expanded.entries?.[entryIndex] ?? (expanded.entries?.length===1 ? expanded.entries[0] : undefined);
    // None is dependency syntax, not a claim about effects.
    const content=prose.replace(/^(## Dependencies\s*\n)\s*None\.\s*$/m,'');
    const rows=proseCoverage(content,declaration?.[0],actual?.errors ?? []);
    const multipleTransports=rows.filter(row=>transportDeclaration(row.sentence)).length>1;
    return rows.map(row=>{
      const sentence=row.sentence;
      let mappings=[];
      let {conflicting,unresolved}=sentenceTypes(sentence,multipleTransports?undefined:actual);
      const ownDeclaration=transportDeclaration(sentence);
      const ownExpected=ownDeclaration && (ownDeclaration[0]===declaration?.[0] ? expected : proseInterface(sentence,true)?.iface);
      const ownIndex=ownDeclaration ? expanded.entries?.findIndex(entry=>entry.operation===ownDeclaration[1]) : -1;
      const ownActual=expanded.entries?.[ownIndex];
      const binding=/^Public binding: module function `([\w$]+)(?:\([^`]*\))?`/.exec(sentence);
      if(binding && !expanded.entries?.some(entry=>entry.operation===binding[1])) conflicting=true;
      if(ownDeclaration && ownExpected) {
        unresolved=false;
        conflicting=!ownActual || ['input_schema','result_schema'].some(key=>!isDeepStrictEqual(schemaMeaning(ownActual[key]),schemaMeaning(ownExpected.entries[0][key])));
        if(!conflicting) mappings=['operation','input_schema','result_schema'].map(key=>({pointer:`/entries/${ownIndex}/${key}`,meaning:ownActual[key]}));
      }
      if(/^(?:There are |This is pure behavior: )?no external resources, operating-system commands(?:,| or) (?:or )?(?:saved data|persistent state)\.$/i.test(sentence)) {
        conflicting=!!(expanded.calls?.length || expanded.resources?.length);
        if(!conflicting && Array.isArray(expanded.calls) && Array.isArray(expanded.resources)) mappings=['calls','resources'].map(key=>({pointer:'/'+key,meaning:expanded[key]}));
      }
      if(!conflicting && !unresolved && !mappings.length) mappings=described.filter(({meaning})=>{
        // A whole sentence must occur in a retained description. Substrings of longer clauses do not qualify.
        return proseCoverage(meaning.description).some(row=>row.sentence===sentence);
      });
      if(conflicting) mappings=[];
      return {sentence,status:conflicting?'conflicting':mappings.length?'mapped':'unmapped',pointers:mappings.map(item=>item.pointer),mappings,...(index ? {source:source.path} : {})};
    });
  });
}
export function contractCoverage({root,path,text,iface}) {
  const files=sourceFilePort(root);
  text ??= files.read({path}).content;
  iface ??= readPrompt(root,new Set(gitFiles(root)),path).interface;
  return sentenceCoverage(draftSources(root,path,text),expandedInterface(path,iface,files));
}
function coverageQuestions(coverage,next_step) {
  return coverage.filter(row=>row.status!=='mapped').map(row=>({
    pointer:/\b(?:input|locale)\b/i.test(row.sentence) ? '/entries/0/input_schema' : /\b(?:result|output|flag)\b/i.test(row.sentence) ? '/entries/0/result_schema' : '/resources',
    sentence:row.sentence,status:row.status,
    question:`${row.status}: "${row.sentence}". Should the prose or the declaration change, or do you accept the authored contract as written?`,next_step
  }));
}
export function coverageView(coverage) {
  return ['Contract coverage (review evidence):',...coverage.map(row=>`${row.status}: ${JSON.stringify(row.sentence)}${row.source ? ' ('+row.source+')' : ''}`+(row.mappings.length ? '\n'+row.mappings.map(item=>`  ${item.pointer}: ${JSON.stringify(item.meaning)}`).join('\n') : ''))];
}
function coverageDecision(coverage) {
  return 'Decide the contract for these sentences:\n'+coverage.filter(row=>row.status!=='mapped').map(row=>`  ${row.status}: ${JSON.stringify(row.sentence)}`).join('\n')+'\nShould the prose change, should the declaration change, or do you accept the authored contract as written? Use pdd approve PROMPT after a person decides.';
}
function expandedInterface(path,iface,files) {
  const candidate='<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify(iface)+'\n```\n</details>';
  return JSON.parse(interfaceBlocks(expandSource({path,text:candidate,format:'prompt'},files).text)[0][1]);
}
function inferInterface(root,path,text,sources) {
  const files=sourceFilePort(root);
  const declarations=sources.filter(source=>!source.path.endsWith('.prompt.md') || source.path===path).flatMap(source=>jsonDeclarations(source.text));
  const candidates=declarations.filter(value=>Array.isArray(value.entries) && value.entries.length
    && value.entries.every(entry=>typeof entry?.operation==='string'));
  let iface;
  if(candidates.length===1) {
    const value=candidates[0];
    iface={...value,kind:Object.hasOwn(value,'kind') ? value.kind : 'full',status:'draft',prose_sha256:''};
    const missing=['calls','resources','limits'].filter(key=>!Object.hasOwn(value,key));
    if(missing.length) {
      iface.kind='partial';
      iface.draft_gaps=[...(Array.isArray(iface.draft_gaps) ? iface.draft_gaps : []),`Declare ${missing.join(', ')} from the owning contract.`];
    }
    if(iface.kind==='native-only') throw Error('Drafting cannot choose native-only. Declare and review its reason.');
  } else {
    if (!candidates.length) { const inferred=proseInterface(text); if(inferred) return {...inferred,defaultBudget:true}; }
    const named=[...text.matchAll(/\boperation\s+`([\w$]+)`/g)].map(match=>match[1]);
    const operations=[...named,...[...text.matchAll(/\b(?:Export|export|exports)\s+(?:(?:async|module|function)\s+)*`?([A-Za-z_$][\w$]*)\s*\(/g)].map(match=>match[1])];
    // An explicitly owned source file can add clear exported function names, never schemas.
    const own=/`(src\/[\w./-]+\.[cm]js)`/.exec(text)?.[1];
    if(own) {
      const code=files.read({path:own}).content;
      for(const match of code.matchAll(/^export\s+(?:async\s+)?function\s+([\w$]+)\s*\(/gm)) operations.push(match[1]);
    }
    iface={kind:'partial',status:'draft',prose_sha256:'',entries:[...new Set(operations)].map(operation=>({operation})),
      draft_gaps:[candidates.length>1 ? 'More than one interface declaration is present; select the owning contract.' : 'Declare complete input_schema and result_schema for each public operation. Review calls, resources and limits against the prompt.']};
  }
  return {iface,defaultBudget:false};
}
export async function runInterfaceDraft({words=[],all=false,json=false,cwd=process.cwd(),contract,extend=false,refresh=false}={},ports={}) {
  const stdout=ports.stdout ?? process.stdout,stderr=ports.stderr ?? process.stderr;
  try {
    if(all && words.length || !all && !words.length) throw Error('Use pdd interface draft PROMPT... or pdd interface draft --all.');
    if ((contract || extend || refresh) && (all || words.length!==1) || extend && (!contract || refresh)) throw Error('Use one prompt; --extend requires --contract and cannot combine with --refresh.');
    const root=rootFor(cwd),workspace=loadRuntimeWorkspace({root}),visible=new Set(gitFiles(root));
    const paths=all ? promptPaths(root) : [...new Set(words.map(word=>relative(root,resolve(cwd,word)).split('\\').join('/')))];
    const files=sourceFilePort(root,visible,workspace);
    const recovery=(path,hasBlock=true)=>`pdd interface draft ${shellWord(relative(cwd,resolve(root,path)).split('\\').join('/'))} ${hasBlock?'--refresh ':''}--contract FILE`;
    // Validate the entire selection before any mutation.
    for(const path of paths) {
      if(!path.endsWith('.prompt.md') || !visible.has(path) || !allowsRuntimePath(workspace,path)) throw Error(`Not a workspace prompt: ${path}`);
      nativeWorkspaceFiles(root).stat({path});
      files.read({path});
    }
    let supplied;
    if(contract) {
      const target=relative(root,resolve(cwd,contract)).split('\\').join('/');
      if (!visible.has(target) || !allowsRuntimePath(workspace,target)) throw Error('Contract must be a Git-visible workspace file.');
      nativeWorkspaceFiles(root).stat({path:target});
      supplied=JSON.parse(files.read({path:target}).content);
    }
    const records=drafts(root),rows=[],changes=[];
    for(const path of paths) {
      try {
        const text=files.read({path}).content,blocks=interfaceBlocks(text);
        if(blocks.length>1) throw Error('Expected one Runtime interface block.');
        const block=blocks[0];
        if(block && !extend && !refresh) {
          if(contract) throw Error('Use --extend to add declarations or --refresh to replace an existing block.');
          const iface=readPrompt(root,visible,path).interface;
          const coverage=contractCoverage({root,path,text,iface});
          const questions=questionsFor(iface);
          for(const question of coverageQuestions(coverage,recovery(path))) {const existing=questions.find(item=>item.question===question.question);if(existing) Object.assign(existing,question);else questions.push(question);}
          rows.push({path,state:'existing',prose_coverage:coverage,...(questions.length ? {questions,next_step:recovery(path)} : {})});continue;
        }
        if(!block && (extend || refresh)) throw Error('Draft the missing interface before extending or refreshing it.');
        if(!block && /<summary[^>]*>\s*(?:<strong[^>]*>\s*)?Runtime\s+interface/i.test(text)) throw Error('The Runtime interface block is malformed. Fix it before drafting.');
        const previous=block ? JSON.parse(block[1]) : null;
        const sources=draftSources(root,path,text);
        const inference=!extend && !supplied && !refresh ? inferInterface(root,path,text,sources) : null;
        const iface=extend ? extendContract(previous,supplied) : {...(supplied ?? (refresh ? previous : inference.iface))};
        iface.status='draft';iface.prose_sha256='';
        if(iface.kind==='full') delete iface.kind;
        const expanded=expandedInterface(path,iface,files);
        if(!inference) completeContract(expanded);
        const questions=questionsFor(iface,interfaceSchemaProblems(expanded));
        if(inference && !questions.length) completeContract(expanded);
        const coverage=sentenceCoverage(sources,expanded);
        const reviewQuestions=coverageQuestions(coverage,recovery(path));
        const inferredBudget=inference?.defaultBudget===true;
        if(inferredBudget) questions.push(...reviewQuestions);
        if(questions.length) {
          iface.kind='partial';
          iface.draft_gaps=questions.map(item=>item.pointer+': '+item.question);
        }
        if(!inferredBudget) questions.push(...reviewQuestions);
        // All whitespace outside the block is original prose, including its final newline.
        const render=()=>{if(extend) return text.replace(block[0],()=>block[0].replace(block[1],()=>extendBody(block[1],previous,iface)));const rendered='<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify(iface,null,2)+'\n```\n</details>';return block ? text.replace(block[0],()=>rendered) : text+rendered;};
        iface.prose_sha256=proseSha256(render());
        const next=render();
        const record={head:git(root,['rev-parse','HEAD']).trim(),original_sha256:sha256(text),prose_sha256:iface.prose_sha256,interface_sha256:sha256(JSON.stringify(iface)),...(block ? {mode:extend?'extend':'refresh',...(extend ? {extension_before:block[1]} : {})} : inferredBudget ? {mode:'prose'} : {})};
        const change=replaceDraftPrompt(root,path,next);
        records[path]=record;
        changes.push(change);
        rows.push({path,state:'drafted',prose_coverage:coverage,...(extend ? {approval_scope:'whole-interface',approval_note:'The Runtime interface has one global status; mixed approval status is unavailable. The whole interface needs re-approval.',interface_diff:{before:block[1],after:interfaceBlocks(next)[0][1],unchanged:preservedPointers(previous,iface)}} : {}),...(inferredBudget ? {draft_budget:{source:'command-default',limits:iface.limits}} : {}),...(questions.length ? {questions,next_step:recovery(path)} : {})});
      } catch(error) {rows.push({path,state:'refused',problems:[{code:error.code ?? 'interface-draft-failed',message:error.message,...(error.pointer!==undefined ? {section:error.pointer,rule:error.rule} : {})}]});}
    }
    if(changes.length) {
      try { saveDrafts(root,records); }
      catch(error) { throw restoreDraftPrompts(root,changes,error); }
      for(const {path,directory} of changes) {
        try { rmSync(directory,{recursive:true,force:true}); }
        catch(cleanup) { stderr.write(`Draft saved; cannot remove temporary draft for ${path}: ${cleanup.message}\n`); }
      }
    }
    for(const row of rows) {
      row.problems ??= interfaceFindings({root,paths:[row.path]});
      row.lint_clean=row.problems.length===0;
      if(row.state==='existing' && row.problems.length) {
        const iface=readPrompt(root,visible,row.path).interface;row.questions ??= questionsFor(iface);row.next_step=recovery(row.path);
      }
      if(row.problems.length && !row.questions?.length) {
        row.questions=row.problems.map(item=>({pointer:item.section ?? '/',question:item.rule ?? item.message}));
        row.next_step=recovery(row.path,interfaceBlocks(files.read({path:row.path}).content).length>0);
      }
    }
    const summary={drafted:rows.filter(row=>row.state==='drafted').length,existing:rows.filter(row=>row.state==='existing').length,lint_clean:rows.filter(row=>row.lint_clean).length,refused:rows.filter(row=>row.problems.length).length,total:rows.length};
    const exit_code=summary.refused ? 4 : 0;
    stdout.write(json ? JSON.stringify({exit_code,summary,rows})+'\n' : [...rows.map(row=>`${row.path}: ${row.state}; ${row.lint_clean ? 'lint clean' : row.problems.map(item=>`${item.code}: ${item.message}`).join('; ')}`+(row.prose_coverage ? '\n'+coverageView(row.prose_coverage).join('\n') : '')+(row.questions?.length ? '\n'+row.questions.map(item=>`Question ${item.pointer}: ${item.question}`).join('\n') : '')+(row.next_step ? `\nNext: ${row.next_step}` : '')+(row.approval_note ? `\n${row.approval_note}\nInterface diff:\n- ${row.interface_diff.before}\n+ ${row.interface_diff.after}\nUnchanged: ${row.interface_diff.unchanged.join(', ')}` : '')+(row.draft_budget ? `\nDraft budget (command default, needs review): ${JSON.stringify(row.draft_budget.limits)}` : '')),`Interfaces: ${summary.drafted} drafted, ${summary.existing} existing, ${summary.lint_clean} lint clean, ${summary.refused} refused. 0 AI calls.`].join('\n')+'\n');
    return exit_code;
  } catch(error) {stderr.write(`${error.message}\n`);return 2;}
}

// Automatic approval runs its own native tests and prompt check; callers cannot supply a pass receipt.
function sourceSnapshot(root) {
  const files=sourceFilePort(root);
  return Object.fromEntries(gitFiles(root).filter(path=>!path.startsWith('.pdd/')).map(path=>{files.stat({path});return [path,sha256(readFileSync(join(root,path)))];}));
}
function nativeTestArgs(root,command,head) {
  if(typeof command!=='string' || !command.trim()) throw Error('Name the existing native tests with --tests COMMAND.');
  const words=command.trim().split(/\s+/);
  if(words[0]==='node' && words[1]==='--test' && words.length>2 && words.slice(2).every(path=>/^[\w./-]+\.(?:[cm]js|ts)$/.test(path) && !path.startsWith('-') && /(?:^|\/)tests?\/|\.(?:test|spec)\.[cm]?[jt]s$/.test(path))) {
    for(const path of words.slice(2)) git(root,['show',`${head}:${path}`]);
    return [process.execPath,['--test-reporter=tap',...words.slice(1)]];
  }
  if(words[0]==='npm' && (words.length===2 && words[1]==='test' || words.length===3 && words[1]==='run')) {
    const name=words[1]==='test' ? 'test' : words[2], pkg=JSON.parse(git(root,['show',`${head}:package.json`]));
    if(/^(?:test|test:.+)$/.test(name) && typeof pkg.scripts?.[name]==='string' && pkg.scripts[name].trim()) return ['npm',words.slice(1)];
  }
  throw Error('Use existing committed tests: node --test TEST... or npm test or npm run SCRIPT.');
}
export async function runAutomaticApproval({path,root,tests},ports={}) {
  const stdout=ports.stdout ?? process.stdout,stderr=ports.stderr ?? process.stderr;
  try {
    const {readApprovalPolicy,approvalActor,recordPromptApproval,readPromptApprovals}=await import('./approval-policy.mjs');
    const {approvePromptText,promptPath}=await import('./prompt-approve.mjs');
    const {runCheck}=await import('./runtime-client.mjs');
    const {randomUUID}=await import('node:crypto');
    if(readApprovalPolicy({root},ports).strictApprovals) throw Error('Strict approvals require a person at a terminal.');
    if(!promptPath(root,root,path)) throw Error('Name one Git-visible regular prompt.');
    const file=join(root,path),text=readFileSync(file,'utf8'),blocks=interfaceBlocks(text);
    if(blocks.length!==1) throw Error('Draft a Runtime interface before automatic approval.');
    const records=drafts(root),iface=JSON.parse(blocks[0][1]),record=records[path];
    if(!record || record.mode || iface.status!=='draft' || iface.kind==='native-only' || interfaceFindings({root,paths:[path]}).length || !iface.entries?.length)
      throw Error('Automatic approval needs a valid draft made by pdd interface draft.');
    if(sha256(JSON.stringify(iface))!==record.interface_sha256 || proseSha256(text)!==record.prose_sha256 || record.original_sha256!==sha256(text.replace(blocks[0][0],'')))
      throw Error('The draft changed. Ask a person to approve the new contract.');
    const head=git(root,['rev-parse','HEAD']).trim();
    if(sha256(git(root,['show',`${record.head}:${path}`]))!==record.original_sha256)
      throw Error('The committed prompt changed or this draft includes new behavior. Ask a person.');
    const coverage=contractCoverage({root,path,text,iface});
    stdout.write(coverageView(coverage).join('\n')+'\n');
    if(coverage.some(row=>row.status!=='mapped')) throw Error(coverageDecision(coverage));
    const before=sourceSnapshot(root),committed=git(root,['ls-tree','-r','--name-only','-z',record.head]).split('\0').filter(Boolean);
    for(const name of new Set([...Object.keys(before),...committed])) {
      if(name.startsWith('.pdd/')) continue;
      let expected=name===path ? record.original_sha256 : before[name];
      const other=records[name];
      if(name!==path && other?.head===record.head && name.endsWith('.prompt.md') && before[name]) {
        const otherText=readFileSync(join(root,name),'utf8'),otherBlocks=interfaceBlocks(otherText);
        if(otherBlocks.length===1) {
          const value=JSON.parse(otherBlocks[0][1]);
          if(['draft','approved'].includes(value.status) && sha256(otherText.replace(otherBlocks[0][0],''))===other.original_sha256
            && sha256(JSON.stringify({...value,status:'draft'}))===other.interface_sha256) expected=other.original_sha256;
        }
      }
      if(!committed.includes(name) || expected===undefined || sha256(git(root,['show',`${record.head}:${name}`],true))!==expected)
        throw Error('Automatic approval needs unchanged committed source and existing tests.');
    }
    const [program,args]=nativeTestArgs(root,tests,head);
    const native=ports.runNativeTests ? await ports.runNativeTests(program,args,{cwd:root})
      : await new Promise((done,reject)=>{
        import('node:child_process').then(({execFile})=>execFile(program,args,{cwd:root,env:ports.env ?? process.env,maxBuffer:16*1024*1024},(error,out,err)=>{
          if(error && typeof error.code!=='number') reject(error);else done({code:error?.code ?? 0,stdout:out,stderr:err});
        }));
      });
    if(native.code!==0) throw Error('Existing native tests did not pass. No prompt was approved.');
    const count = key => {const matches=[...(native.stdout ?? '').matchAll(new RegExp(`^# ${key} (\\d+)\\s*$`,'gm'))];return matches.length===1 ? Number(matches[0][1]) : null;};
    const nativeCounts={total:count('tests'),passed:count('pass'),failed:count('fail')};
    if(!(nativeCounts.total>0) || nativeCounts.passed!==nativeCounts.total || nativeCounts.failed!==0) throw Error('The native command did not report a complete passing TAP test run.');
    if(JSON.stringify(sourceSnapshot(root))!==JSON.stringify(before)) throw Error('Source changed during native tests. No prompt was approved.');
    const found=findTests({root,excludeFixtureProjects:true});
    // Follow calls too: every scenario that can reach the drafted contract must pass in full.
    const reaches=(entry,seen=new Set())=>{
      if(entry===path) return true;
      if(typeof entry!=='string' || seen.has(entry)) return false;
      seen.add(entry);
      const prompt=readPrompt(root,found.visible,entry);
      return (prompt.interface?.calls ?? []).some(call=>reaches(call.target,seen));
    };
    const affected=found.tests.filter(test=>(test.doc?.steps ?? []).some(step=>reaches(step.entry_path)));
    const stories=new Set(affected.map(test=>test.storyPath ?? test.story));
    const selected=found.tests.filter(test=>stories.has(test.storyPath ?? test.story));
    if(!selected.length || selected.some(test=>test.error)) throw Error('No complete existing prompt tests cover this draft.');
    let output='';
    const checkPorts={...ports,stdout:{write:chunk=>{output+=chunk;}},stderr};
    const code=await runCheck({cwd:root,words:selected.map(test=>test.path),options:{'--json':true},cache:false},checkPorts);
    let result;try {result=JSON.parse(output);}catch {throw Error('Prompt check evidence is unavailable.');}
    const complete=code===0 && result.exit_code===0 && result.rows?.length===selected.length && selected.every(test=>{
      const row=result.rows.find(row=>row.test===test.path),checks=test.doc.steps.reduce((sum,step)=>sum+(step.checks?.length ?? 0),0);
      return row?.state==='passed' && !row.cached && !row.native_only?.length && !row.time_limit && !row.refusals?.length
        && row.criteria?.passed===test.doc.criteria.length && row.criteria?.total===test.doc.criteria.length
        && row.checks?.passed===checks && row.checks?.total===checks;
    });
    if(!complete) throw Error('The prompt check did not pass every current test, criterion and check.');
    if(JSON.stringify(sourceSnapshot(root))!==JSON.stringify(before) || git(root,['rev-parse','HEAD']).trim()!==head || readFileSync(file,'utf8')!==text)
      throw Error('Source changed during checking. No prompt was approved.');
    const commonDir=git(root,['rev-parse','--path-format=absolute','--git-common-dir']).trim();
    readPromptApprovals({commonDir},ports);
    const next=approvePromptText(text);
    if(!next) throw Error('The prompt could not be approved safely.');
    const evidence={id:(ports.randomUUID ?? randomUUID)(),route:'automatic-check-pass',actor:approvalActor(ports.env ?? process.env),at:(ports.now ?? Date.now)(),words:null,
      prompts:[{path,proseSha256:record.prose_sha256,kind:iface.kind ?? 'full'}],coverage,checks:{native:{command:tests,exit_code:native.code,counts:nativeCounts},prompt:result,head,source:before,draft:record}};
    try {
      writeFileSync(file,next);
      await recordPromptApproval({commonDir,evidence},ports);
    } catch(error) {writeFileSync(file,text);throw error;}
    stdout.write(`Approved ${path}. Approval route: automatic-check-pass.\n`);
    return 0;
  } catch(error) {stderr.write(`${error.message}\n`);return 4;}
}
