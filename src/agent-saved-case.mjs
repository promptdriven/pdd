// Generated from prompts/cli/agent-saved-case.prompt.md (sha256: 92c6f0879b073cde163a8f17dea44a928b1bc2c9a97b04faba5d87f3e88470c2).
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
import {basename,join,resolve,relative,sep} from 'node:path';
import {constants,lstatSync,statSync,realpathSync,openSync,fstatSync,readSync,writeSync,fsyncSync,closeSync,mkdirSync,unlinkSync,rmdirSync} from 'node:fs';
import {isSecretPath,storyCriteria,TEST_SCHEMA} from './runtime-preflight.mjs';
const LIMIT=1048576;
const object=value=>value!==null&&typeof value==='object'&&!Array.isArray(value);
const controls=/[\u0000-\u001f\u007f-\u009f]/;
const TOP=new Set(['schema_version','story_path','criteria','initial_world','steps','entry_paths','simulation','check_exemptions','context','context_byte_budget','criteria_scope','prompt_mappings']);
const CHECK=new Set(['criterion_id','target','path','op','value','json_path','html','measure']);
const OPS=new Set(['equals','not_equals','one_of','exists','count','contains','at_most','at_least','not_contains','all_in','equals_ignore_case']);
const NEEDS_VALUE=new Set([...OPS].filter(op=>op!=='exists'));
const STEP=new Set(['step_id','entry_path','operation','input','checks','expected_error','simulation_overrides','model']);
const digest=bytes=>createHash('sha256').update(bytes).digest('hex');
class Invalid extends Error {}
const fail=message=>{throw new Invalid(message);};
const stat=path=>{try{return lstatSync(path);}catch(error){if(error.code==='ENOENT')return null;throw error;}};
const same=(a,b)=>a&&b&&a.dev===b.dev&&a.ino===b.ino;
const close=fd=>{if(fd!==undefined)try{closeSync(fd);}catch{}};
const clone=value=>structuredClone(value);
function canonicalPath(path){return typeof path==='string'&&path.length>0&&!path.includes('\\')&&!path.startsWith('/')&&!controls.test(path)&&!path.split('/').some(part=>!part||part==='.'||part==='..'||part==='.git')&&!isSecretPath(path);}
function checkedPath(root,path){
 if(!canonicalPath(path))fail('the case contains an unsafe repository path');
 const full=resolve(root,path),rel=relative(root,full);if(rel==='..'||rel.startsWith('..'+sep)||rel.startsWith(sep))fail('the case path is outside the repository');
 let current=root;
 for(const part of path.split('/')){current=join(current,part);const info=stat(current);if(!info)fail('a required repository file is missing');if(info.isSymbolicLink())fail('symbolic links are not allowed for saved cases');}
 return{path:full,info:stat(full)};
}
function readBounded(path,limit,expected){
 let fd;
 try{
  fd=openSync(path,constants.O_RDONLY|constants.O_NOFOLLOW|constants.O_NONBLOCK);
  const info=fstatSync(fd);if(!info.isFile()||info.size>limit||(expected&&!same(info,expected)))fail('a saved-case source is not a safe bounded regular file');
  const bytes=Buffer.alloc(limit+1);let size=0;
  while(size<bytes.length){const count=readSync(fd,bytes,size,bytes.length-size,null);if(!count)break;size+=count;}
  if(size>limit)fail('a saved-case source is too large');
  const after=fstatSync(fd);if(!same(info,after)||info.size!==after.size||info.mtimeMs!==after.mtimeMs)fail('a saved-case source changed while reading');
  return bytes.subarray(0,size);
 }finally{close(fd);}
}
function readStory(root,path){const checked=checkedPath(root,path);if(!checked.info?.isFile())fail('the Story is not a regular file');const bytes=readBounded(checked.path,65536,checked.info);let text;try{text=new TextDecoder('utf-8',{fatal:true}).decode(bytes);}catch{fail('the Story is not valid UTF-8');}return{text,hash:digest(bytes)};}
function visibleStory(root,story){const list=spawnSync('git',['-c','core.fsmonitor=false','ls-files','-z','-co','--exclude-standard'],{cwd:root,maxBuffer:1048576,timeout:2000});if(list.status!==0||!list.stdout.toString('utf8').split('\0').includes(story))fail('the Story is not Git-visible in this repository');}
function identity({story,name,id}){
 if(!canonicalPath(story)||!story.endsWith('.md'))fail('the Story path must be a safe repository Markdown file');
 if(typeof id!=='string'||!id||id.trim()!==id||id.length>128||Buffer.byteLength(id)>256||controls.test(id))fail('the saved case needs a valid stable identity');
 if(name!==undefined&&(typeof name!=='string'||Array.from(name).length>200||controls.test(name)))fail('the saved case name is invalid');
}
const slug=(value,fallback)=>value.normalize('NFKD').replace(/[\u0300-\u036f]/g,'').toLowerCase().replace(/[^a-z0-9]+/g,'-').replace(/^-+|-+$/g,'').slice(0,64).replace(/-+$/,'')||fallback;
export function agentSavedCasePath({story,name,id}){identity({story,name,id});return`tests/${slug(basename(story,'.md'),'story')}-${slug(name||'saved-case','saved-case')}-${digest(Buffer.from(id,'utf8')).slice(0,10)}.json`;}
function finiteJson(value){
 const active=new Set();let nodes=0,bytes=0;
 const visit=(item,depth)=>{
  if(++nodes>100000||depth>64)fail('the saved case is too complex');
  if(item===null||typeof item==='boolean')return;
  if(typeof item==='number'){if(!Number.isFinite(item))fail('the saved case must contain finite JSON values');return;}
  if(typeof item==='string'){bytes+=Buffer.byteLength(item);if(bytes>LIMIT)fail('the saved case is too large');return;}
  if(typeof item!=='object'||active.has(item))fail('the saved case must contain only JSON data');
  if(!Array.isArray(item)&&Object.getPrototypeOf(item)!==Object.prototype&&Object.getPrototypeOf(item)!==null)fail('the saved case must contain only JSON data');
  if(Reflect.ownKeys(item).some(key=>typeof key!=='string'))fail('the saved case must contain only JSON data');if(Array.isArray(item)&&(Object.keys(item).length!==item.length||Array.from({length:item.length},(_,index)=>index).some(index=>!Object.hasOwn(item,index))))fail('the saved case must contain dense JSON arrays');active.add(item);for(const [key,descriptor]of Object.entries(Object.getOwnPropertyDescriptors(item))){if(Array.isArray(item)&&key==='length')continue;if(!Object.hasOwn(descriptor,'value')||!descriptor.enumerable)fail('the saved case must contain only JSON data');bytes+=Buffer.byteLength(key);visit(descriptor.value,depth+1);}active.delete(item);
 };
 visit(value,0);
}
function stringify(value,depth=0){
 if(value===null||typeof value!=='object')return Object.is(value,-0)?'-0':JSON.stringify(value);
 const indent='  '.repeat(depth),next='  '.repeat(depth+1);
 if(Array.isArray(value))return value.length?'[\n'+value.map(item=>next+stringify(item,depth+1)).join(',\n')+'\n'+indent+']':'[]';
 const rows=Object.entries(value);return rows.length?'{\n'+rows.map(([key,item])=>next+JSON.stringify(key)+': '+stringify(item,depth+1)).join(',\n')+'\n'+indent+'}':'{}';
}
export function serializeAgentScenario(value){finiteJson(value);const text=stringify(value)+'\n';if(Buffer.byteLength(text)>LIMIT)fail('the saved case is too large');return text;}
function validateTest(test){
 if(!object(test)||test.schema_version!==TEST_SCHEMA||Object.keys(test).some(key=>!TOP.has(key))||!object(test.initial_world)||!Array.isArray(test.criteria)||!test.criteria.length||!Array.isArray(test.steps)||!test.steps.length)fail('the saved payload is not a runnable scenario');
 if(test.check_exemptions!==undefined&&(!Array.isArray(test.check_exemptions)||test.check_exemptions.length))fail('saved cases cannot import check exemptions');
 if(test.simulation!==undefined&&!object(test.simulation))fail('the saved simulation must be an object');
 if(test.context!==undefined&&!Array.isArray(test.context))fail('the saved context must be an array');
 const criteria=new Map();
 for(const criterion of test.criteria){if(!object(criterion)||Object.keys(criterion).length!==2||typeof criterion.id!=='string'||!criterion.id||typeof criterion.text!=='string'||!criterion.text||criteria.has(criterion.id))fail('the saved criteria are invalid or ambiguous');criteria.set(criterion.id,criterion.text);}
 const steps=new Set();
 for(const step of test.steps){
  if(!object(step)||Object.keys(step).some(key=>!STEP.has(key))||typeof step.step_id!=='string'||!step.step_id||steps.has(step.step_id)||!canonicalPath(step.entry_path)||!step.entry_path.endsWith('.prompt.md')||typeof step.operation!=='string'||!step.operation||!object(step.input)||!Array.isArray(step.checks)||!step.checks.length)fail('the saved steps are invalid');
  steps.add(step.step_id);
  for(const check of step.checks)if(!object(check)||typeof check.criterion_id!=='string'||!criteria.has(check.criterion_id)||!['result','world','calls','error'].includes(check.target)||typeof check.path!=='string'||(check.path!==''&&!check.path.startsWith('/'))||/~(?:[^01]|$)/.test(check.path)||!OPS.has(check.op)||Object.keys(check).some(key=>!CHECK.has(key))||(NEEDS_VALUE.has(check.op)&&!Object.hasOwn(check,'value')))fail('the saved checks have invalid fields or criterion references');
 }
 return criteria;
}
function sentence(text){const collapsed=text.trim().replace(/[\u0000-\u001f\u007f-\u009f]/g,' ').replace(/\s+/g,' ');const first=collapsed.split(/(?<=[.!?])\s+(?=[A-Z])/)[0];return Array.from(first).slice(0,500).join('');}
export function agentSavedCaseFingerprint(saved){const story=saved?.story_path??saved?.test?.story_path;identity({story,name:saved?.name,id:saved?.id});return digest(Buffer.from(serializeAgentScenario({id:saved.id,name:saved.name??null,story_path:story,test:saved.test}),'utf8'));}
function refused(error){return{status:'refused',result:`not added: ${error instanceof Invalid?error.message:'pdd could not safely import this case'}.`};}
function planUnsafe({root,saved,receipt=null,storyTextOverride}){
 const repo=realpathSync(root);if(!stat(repo)?.isDirectory())fail('the repository is unavailable');
 const raw=saved?.test;
 const story=saved?.story_path??raw?.story_path;
 identity({story,name:saved?.name,id:saved?.id});
 if((saved?.story_path!==undefined&&typeof saved.story_path!=='string')||(raw?.story_path!==undefined&&raw.story_path!==story))fail('the saved case names a different Story');
 finiteJson(raw);const original=clone(raw);const source=validateTest(original);
 if(Buffer.byteLength(stringify(original))>LIMIT)fail('the saved case is too large');
 visibleStory(repo,story);const authored=readStory(repo,story);
 if(storyTextOverride!==undefined&&(typeof storyTextOverride!=='string'||Buffer.byteLength(storyTextOverride)>65536))fail('the planned Story is invalid or too large');
 const storyText=storyTextOverride??authored.text,authoredCriteria=storyCriteria(storyText);
 if(!authoredCriteria.length)fail('the Story has no acceptance criteria');
 if(new Set(authoredCriteria).size!==authoredCriteria.length)fail('duplicate Story criterion text is ambiguous');
 const byText=new Map(authoredCriteria.map((text,index)=>[text,`ac-${index+1}`]));
 const selected=new Set(),mapping=new Map(),rules=[];
 for(const step of original.steps)for(const check of step.checks){const text=source.get(check.criterion_id),id=byText.get(text);if(id){mapping.set(check.criterion_id,id);selected.add(id);}else if(!rules.some(rule=>rule.source_id===check.criterion_id))rules.push({text:sentence(text),source_text:text,source_id:check.criterion_id});}
 if(rules.length)return{status:'needs_rule',result:'not added: this case needs a Story rule confirmed by the person.',rules};
 const criteria=authoredCriteria.map((text,index)=>({id:`ac-${index+1}`,text})).filter(criterion=>selected.has(criterion.id));
 const doc={...original,story_path:story,criteria,criteria_scope:criteria.map(criterion=>criterion.id),steps:original.steps.map(step=>({...step,checks:step.checks.map(check=>({...check,criterion_id:mapping.get(check.criterion_id)}))}))};
 const text=stringify(doc)+'\n';if(Buffer.byteLength(text)>LIMIT)fail('the saved case is too large');
 const path=agentSavedCasePath({story,name:saved.name,id:saved.id}),sha256=digest(Buffer.from(text,'utf8'));
 const expected={case_id:saved.id,repo,path,sha256};
 if(receipt!==null&&(!object(receipt)||Object.keys(expected).some(key=>receipt[key]!==expected[key])))fail('the saved-case receipt does not match this case');
 const directory=stat(join(repo,'tests'));
 if(directory){if(!directory.isDirectory()||directory.isSymbolicLink())fail('tests must be a real directory inside the repository');const target=stat(join(repo,path));if(target){const checked=checkedPath(repo,path);if(!target.isFile()||target.isSymbolicLink())fail('the destination is not a safe regular file');const bytes=readBounded(checked.path,LIMIT,checked.info);if(!bytes.equals(Buffer.from(text)))fail('the destination already contains a different or edited case');return{status:'already_added',result:`added to ${path} (already present)`,path,receipt:expected};}}
 if(receipt!==null)fail('the receipted saved-case file is missing');
 return{status:'planned',result:`ready to add ${path}`,repo,path,text,receipt:expected,story_path:story,sourceHash:authored.hash,storyHash:digest(Buffer.from(storyText,'utf8'))};
}
export function planAgentSavedCase(options){try{return planUnsafe(options);}catch(error){return refused(error);}}
function directoryMatches(path,fd){try{const info=lstatSync(path);return info.isDirectory()&&!info.isSymbolicLink()&&same(info,fstatSync(fd));}catch{return false;}}
function anchor(fd){for(const path of [`/proc/self/fd/${fd}`,`/dev/fd/${fd}`])try{const info=statSync(path+'/.');if(info.isDirectory()&&same(info,fstatSync(fd)))return path;}catch{}return null;}
function writePlan(plan){
 let rootFd,dirFd,fileFd,createdFile=false,createdDirectory=false,filePath,dirPath,createdIdentity;
 try{
  rootFd=openSync(plan.repo,constants.O_RDONLY|constants.O_DIRECTORY|constants.O_NOFOLLOW|constants.O_NONBLOCK);
  if(!directoryMatches(plan.repo,rootFd)||readStory(plan.repo,plan.story_path).hash!==plan.sourceHash)fail('the repository or Story changed before saving');
  const rootAnchor=anchor(rootFd),testsName=join(plan.repo,'tests');
  dirPath=join(rootAnchor??plan.repo,'tests');
  if(!stat(testsName)){try{mkdirSync(dirPath,{mode:0o755});createdDirectory=true;}catch(error){if(error.code!=='EEXIST')throw error;}}
  dirFd=openSync(dirPath,constants.O_RDONLY|constants.O_DIRECTORY|constants.O_NOFOLLOW|constants.O_NONBLOCK);
  if(!directoryMatches(plan.repo,rootFd)||!directoryMatches(testsName,dirFd))fail('the tests directory changed before saving');
  const dirAnchor=anchor(dirFd);filePath=join(dirAnchor??testsName,basename(plan.path));
  if(readStory(plan.repo,plan.story_path).hash!==plan.sourceHash)fail('the Story changed before saving');
  try{fileFd=openSync(filePath,constants.O_WRONLY|constants.O_CREAT|constants.O_EXCL|constants.O_NOFOLLOW|constants.O_NONBLOCK,0o600);createdFile=true;createdIdentity=fstatSync(fileFd);}catch(error){if(error.code==='EEXIST'){const bytes=readBounded(filePath,LIMIT);if(directoryMatches(plan.repo,rootFd)&&directoryMatches(testsName,dirFd)&&bytes.equals(Buffer.from(plan.text)))return{status:'already_added',result:`added to ${plan.path} (already present)`,path:plan.path,receipt:plan.receipt};fail('the destination already contains a different or edited case');}throw error;}
  if(!createdIdentity.isFile()||!directoryMatches(plan.repo,rootFd)||!directoryMatches(testsName,dirFd))fail('the tests directory changed while opening the case');
  const bytes=Buffer.from(plan.text,'utf8');let offset=0;while(offset<bytes.length){const n=writeSync(fileFd,bytes,offset,bytes.length-offset);if(n<=0)fail('the case could not be completely written');offset+=n;}fsyncSync(fileFd);
  if(!directoryMatches(plan.repo,rootFd)||!directoryMatches(testsName,dirFd)||readStory(plan.repo,plan.story_path).hash!==plan.sourceHash||!same(stat(filePath),createdIdentity))fail('the repository or Story changed while saving');
  return{status:'added',result:`added to ${plan.path}`,path:plan.path,receipt:plan.receipt};
 }catch(error){
  try{if(createdFile&&filePath&&same(stat(filePath),createdIdentity))unlinkSync(filePath);}catch{}
  try{if(createdDirectory&&dirPath&&dirFd!==undefined&&directoryMatches(join(plan.repo,'tests'),dirFd))rmdirSync(dirPath);}catch{}
  return refused(error);
 }finally{close(fileFd);close(dirFd);close(rootFd);}
}
export function importAgentSavedCase({root,saved,receipt=null}){const plan=planAgentSavedCase({root,saved,receipt});return plan.status==='planned'?writePlan(plan):plan;}
