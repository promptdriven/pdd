// Generated from prompts/cli/agent-story-rule.prompt.md (sha256: 145d74914ca32e18c1c2d717bb38c1898af64f7be834e3b578929803879b0751).
import {constants,lstatSync,statSync,realpathSync,openSync,fstatSync,readSync,writeSync,fsyncSync,fchmodSync,closeSync,mkdirSync,unlinkSync,linkSync,renameSync} from 'node:fs';
import {join,dirname,basename,resolve,relative,isAbsolute,sep} from 'node:path';
import {createHash,randomUUID} from 'node:crypto';
import {isDeepStrictEqual} from 'node:util';
import {gitFiles,isSecretPath,storyCriteria,TEST_SCHEMA} from './runtime-preflight.mjs';
import {planAgentSavedCase,agentSavedCasePath,agentSavedCaseFingerprint} from './agent-saved-case.mjs';
const LIMIT=1048576,JOURNAL_LIMIT=67108864,PLAN_LIMIT=JOURNAL_LIMIT-65536,SCHEMA='pdd.agent-story-rule.plan.v1',JOURNAL='pdd.agent-story-rule.journal.v1',issued=new WeakMap();
const object=x=>x!==null&&typeof x==='object'&&!Array.isArray(x);
const hash=x=>createHash('sha256').update(x).digest('hex');
const control=/[\u0000-\u001f\u007f-\u009f]/;
const TOP_KEYS=new Set(['schema_version','story_path','criteria','initial_world','steps','entry_paths','simulation','check_exemptions','context','context_byte_budget','criteria_scope','prompt_mappings']);
const STEP_KEYS=new Set(['step_id','entry_path','operation','input','checks','expected_error','simulation_overrides','model']);
const exact=new Set(['equals','not_equals','one_of','count','at_most','at_least','not_contains','all_in','equals_ignore_case']);
class Invalid extends Error{}
const fail=message=>{throw new Invalid(message);};
const refused=e=>({status:'refused',result:`not added: ${e instanceof Invalid?e.message:'the Story rule could not be safely saved'}.`});
const stat=path=>{try{return lstatSync(path);}catch(e){if(e.code==='ENOENT')return null;throw e;}};
const same=(a,b)=>a&&b&&a.ino===b.ino&&a.dev===b.dev;
const close=fd=>{if(fd!==undefined)try{closeSync(fd);}catch{}};
function syncDirectory(fd){try{fsyncSync(fd);}catch(e){if(!['EINVAL','ENOTSUP','EBADF'].includes(e.code))throw e;}}
function safePath(path){return typeof path==='string'&&path&&!path.includes('\\')&&!path.startsWith('/')&&!control.test(path)&&!path.split('/').some(p=>!p||p==='.'||p==='..'||p==='.git')&&!isSecretPath(path);}
function checked(root,path,{missing=false}={}){
 if(!safePath(path))fail('an affected repository path is unsafe');let current=root;
 const parts=path.split('/');for(let i=0;i<parts.length;i++){current=join(current,parts[i]);const info=stat(current);if(!info){if(missing)return null;fail('an affected file is missing');}if(info.isSymbolicLink())fail('symbolic links are not allowed for Story changes');if(i<parts.length-1&&!info.isDirectory())fail('an affected parent is not a directory');}
 return stat(current);
}
function read(path,limit=LIMIT,expected){let fd;try{fd=openSync(path,constants.O_RDONLY|constants.O_NOFOLLOW|constants.O_NONBLOCK);const info=fstatSync(fd);if(!info.isFile()||info.size>limit||(expected&&!same(info,expected)))fail('an affected file is not a bounded regular file');const buffer=Buffer.alloc(Math.min(info.size+1,limit+1));let size=0;while(size<buffer.length){const n=readSync(fd,buffer,size,buffer.length-size,null);if(!n)break;size+=n;}const after=fstatSync(fd);if(size>limit||size!==info.size||info.size!==after.size||info.mtimeMs!==after.mtimeMs||!same(info,after))fail('an affected file changed while reading');return new TextDecoder('utf-8',{fatal:true,ignoreBOM:true}).decode(buffer.subarray(0,size));}finally{close(fd);}}
function source(root,path,limit=LIMIT){const info=checked(root,path);if(!info.isFile())fail('an affected file is not regular');return{text:read(join(root,path),limit,info),mode:info.mode&0o777};}
function appendRule(source,text){
 const criteria=storyCriteria(source);if(!criteria.length||new Set(criteria).size!==criteria.length)fail('the Story has missing or ambiguous criteria');
 if(typeof text!=='string'||!text||text.trim()!==text||Array.from(text).length>500||control.test(text)||criteria.includes(text))fail('the proposed rule is invalid or already in the Story');
 const heading=/^##[ \t]+Acceptance(?:[ \t]+Criteria)?[ \t]*\r?$/im.exec(source);if(!heading)fail('the Story needs a numbered Acceptance criteria list');
 const body=source.slice(heading.index+heading[0].length),lines=[...body.matchAll(/[^\n]*(?:\n|$)/g)].filter(m=>m[0].length);let expected=1,end=null,current=false;
 for(const line of lines){const raw=line[0].replace(/\r?\n$/,''),number=/^([1-9][0-9]*)[.)][ \t]+/.exec(raw);if(number){if(Number(number[1])!==expected){if(expected>1)break;continue;}current=true;expected++;end=heading.index+heading[0].length+line.index+line[0].length;}else if(current){if(!raw.trim()||raw.startsWith('#'))current=false;else end=heading.index+heading[0].length+line.index+line[0].length;}else if(expected>1&&raw.startsWith('##'))break;}
 if(expected-1!==criteria.length||end===null)fail('the Story numbered list cannot be safely extended');
 const eol=source.includes('\r\n')?'\r\n':'\n',prefix=end>0&&source[end-1]==='\n'?'':eol,newText=source.slice(0,end)+prefix+`${criteria.length+1}. ${text}`+eol+source.slice(end);
 if(Buffer.byteLength(newText)>65536||!isDeepStrictEqual(storyCriteria(newText),[...criteria,text]))fail('the appended rule would change other Story criteria');return newText;
}
function spans(text){
 JSON.parse(text);let i=0;const white=()=>{while(/[\t\r\n ]/.test(text[i]??'!'))i++;};
 function node(){white();const start=i,char=text[i];if(char==='"'){i++;while(i<text.length){if(text[i]==='\\'){i+=2;continue;}if(text[i++]==='"')break;}return{start,end:i};}
  if(char==='{'||char==='['){const type=char==='{'?'object':'array',properties=new Map(),items=[];i++;white();while(text[i]!== (type==='object'?'}':']')){if(type==='object'){const keyNode=node(),key=JSON.parse(text.slice(keyNode.start,keyNode.end));if(properties.has(key))fail('duplicate JSON keys prevent safe test migration');white();i++;const value=node();properties.set(key,value);items.push(value);}else items.push(node());white();if(text[i]===','){i++;white();}else break;}i++;return{start,end:i,type,properties,items};}
  while(i<text.length&&!/[\s,}\]]/.test(text[i]))i++;return{start,end:i};
 }
 return node();
}
function validateLocalChecks(doc){
 const ids=new Set(doc.criteria.map(c=>c.id)),checkedIds=new Set(),steps=new Set();
 for(const step of doc.steps){
  if(!object(step)||Object.keys(step).some(k=>!STEP_KEYS.has(k))||typeof step.step_id!=='string'||!step.step_id||steps.has(step.step_id)||typeof step.entry_path!=='string'||!safePath(step.entry_path)||!step.entry_path.endsWith('.prompt.md')||typeof step.operation!=='string'||!step.operation||!Object.hasOwn(step,'input')||!Array.isArray(step.checks)||!step.checks.length||(Object.hasOwn(step,'model')&&(typeof step.model!=='string'||!step.model.trim()))||(Object.hasOwn(step,'expected_error')&&typeof step.expected_error!=='string'))fail('a local Story test has inconsistent steps');
  steps.add(step.step_id);
  for(const check of step.checks){if(!object(check)||typeof check.criterion_id!=='string'||!ids.has(check.criterion_id)||typeof check.target!=='string'||typeof check.path!=='string'||typeof check.op!=='string'||!check.op)fail('a local Story test has inconsistent check fields or criterion IDs');if(exact.has(check.op)){if(!Object.hasOwn(check,'value'))fail('a local Story test exact check has no expected value');checkedIds.add(check.criterion_id);}else if(check.op==='exists'&&Object.hasOwn(check,'html'))checkedIds.add(check.criterion_id);}
  if(Object.hasOwn(step,'expected_error')&&!step.checks.some(c=>c.target==='error'&&c.path==='/code'&&c.op==='equals'&&c.value===step.expected_error))fail('a local Story test has an incomplete expected error check');
 }
 if([...ids].some(id=>!checkedIds.has(id)))fail('a local Story test lacks an exact selected criterion check');
}
function migrate(text,story,criteria){
 const tree=spans(text),doc=JSON.parse(text);if(!object(doc)||Object.keys(doc).some(k=>!TOP_KEYS.has(k))||doc.schema_version!==TEST_SCHEMA||doc.story_path!==story||!object(doc.initial_world)||!Array.isArray(doc.criteria)||!doc.criteria.length||!Array.isArray(doc.steps)||!doc.steps.length)fail('a local Story test is inconsistent');
 if(doc.check_exemptions!==undefined&&(!Array.isArray(doc.check_exemptions)||doc.check_exemptions.length))fail('a local Story test uses unsupported exemptions');
 const criterionIds=new Set();for(const c of doc.criteria){if(!object(c)||Object.keys(c).sort().join(',')!=='id,text'||typeof c.id!=='string'||!c.id||typeof c.text!=='string'||!c.text||criterionIds.has(c.id))fail('a local Story test has inconsistent criteria');criterionIds.add(c.id);}
 validateLocalChecks(doc);
 const authored=criteria.map((text,index)=>({id:`ac-${index+1}`,text}));
 if(Object.hasOwn(doc,'criteria_scope')){const scope=doc.criteria_scope,selected=authored.filter(c=>Array.isArray(scope)&&scope.includes(c.id));if(!Array.isArray(scope)||!scope.length||new Set(scope).size!==scope.length||!isDeepStrictEqual(scope,selected.map(c=>c.id))||!isDeepStrictEqual(doc.criteria,selected))fail('a scoped local test does not match the Story');return null;}
 const oldIds=new Map(),byText=new Map(authored.map(c=>[c.text,c.id]));
 for(const c of doc.criteria){if(!byText.has(c.text))fail('a full Story test has inconsistent criteria');oldIds.set(c.id,byText.get(c.text));}
 if(doc.criteria.length!==criteria.length||new Set(doc.criteria.map(c=>c.text)).size!==criteria.length)fail('a full Story test does not cover the old Story');
 const criteriaNode=tree.properties.get('criteria'),stepsNode=tree.properties.get('steps');if(!criteriaNode||stepsNode?.items?.length!==doc.steps.length)fail('a local test cannot be safely migrated');
 const patches=[{start:criteriaNode.start,end:criteriaNode.end,text:JSON.stringify(authored)}];
 for(let index=0;index<doc.steps.length;index++){const checks=stepsNode.items[index].properties?.get('checks');if(checks?.items?.length!==doc.steps[index].checks.length)fail('a local test cannot be safely migrated');for(let n=0;n<checks.items.length;n++){const id=checks.items[n].properties?.get('criterion_id');if(!id)fail('a local test cannot be safely migrated');patches.push({start:id.start,end:id.end,text:JSON.stringify(oldIds.get(doc.steps[index].checks[n].criterion_id))});}}
 const insert=tree.items.at(-1).end;patches.push({start:insert,end:insert,text:`,"criteria_scope":${JSON.stringify(authored.map(c=>c.id))}`});
 let after=text;for(const patch of patches.sort((a,b)=>b.start-a.start))after=after.slice(0,patch.start)+patch.text+after.slice(patch.end);JSON.parse(after);return after;
}
function change(kind,path,before,after,mode){return{kind,path,before,after,before_sha256:before===null?null:hash(before),after_sha256:hash(after),mode};}
function planUnsafe({root,saved,rule}){
 const payloadHash=agentSavedCaseFingerprint(saved),repo=realpathSync(root),initial=planAgentSavedCase({root:repo,saved});if(initial.status!=='needs_rule'||initial.rules.length!==1||!object(rule)||!['text','source_text','source_id'].every(k=>rule[k]===initial.rules[0][k]))fail('this saved case needs exactly one matching proposed rule');
 const story=saved.story_path??saved.test.story_path;if(!safePath(story)||!story.endsWith('.md')||story.endsWith('.prompt.md'))fail('the proposed rule does not name a safe Story');
 const old=source(repo,story,65536),oldCriteria=storyCriteria(old.text),future=appendRule(old.text,rule.text),canonical=`ac-${oldCriteria.length+1}`;
 const normalized=structuredClone(saved);for(const criterion of normalized.test.criteria)if(criterion.id===rule.source_id)criterion.text=rule.text;
 const next=planAgentSavedCase({root:repo,saved:normalized,storyTextOverride:future});if(next.status!=='planned'||next.sourceHash!==hash(old.text))fail('the separate case could not be planned for the new Story');
 const receipt={...next.receipt,rule:rule.text,criterion_id:canonical},changes=[],plan={schema:SCHEMA,repo,case_id:saved.id,payload_sha256:payloadHash,case_name:saved.name??null,story_path:story,rule:structuredClone(rule),criterion_id:canonical,question:`This is not in the Story yet. Add it as a new rule: '${rule.text}'? y/N`,case_path:next.path,receipt,changes};
 let retainedBytes=Buffer.byteLength(JSON.stringify(plan));
 const addChange=item=>{const size=Buffer.byteLength(JSON.stringify(item))+(changes.length?1:0);if(retainedBytes+size>PLAN_LIMIT)fail('the Story transaction is too large');retainedBytes+=size;changes.push(item);};
 addChange(change('case',next.path,null,next.text,0o600));
 for(const path of gitFiles(repo)){if(!path.endsWith('.json')||isSecretPath(path))continue;const info=checked(repo,path,{missing:true});if(!info)continue;if(!info.isFile()||info.size>LIMIT)continue;const original=source(repo,path);if(!original.text.includes('prompt-runtime.program-scenario'))continue;let doc;try{doc=JSON.parse(original.text);}catch{fail('an invalid local scenario prevents safe Story migration');}if(doc?.story_path!==story)continue;const after=migrate(original.text,story,oldCriteria);if(after!==null)addChange(change('test',path,original.text,after,original.mode));}
 addChange(change('story',story,old.text,future,old.mode));

 if(Buffer.byteLength(JSON.stringify(plan))>JOURNAL_LIMIT)fail('the Story transaction is too large');issued.set(plan,hash(JSON.stringify(plan)));return{status:'ready',result:'ready for the person to approve one Story rule',plan};
}
export function planAgentStoryRule(options){try{return planUnsafe(options);}catch(e){return refused(e);}}
function validatePlan(plan,repo,caseId){
 if(!object(plan)||plan.schema!==SCHEMA||plan.repo!==repo||plan.case_id!==caseId||typeof plan.payload_sha256!=='string'||!/^[0-9a-f]{64}$/.test(plan.payload_sha256)||typeof caseId!=='string'||!caseId||caseId.length>128||control.test(caseId)||!Array.isArray(plan.changes)||plan.changes.length<2||!object(plan.rule))fail('the approved Story plan is invalid');
 const path=agentSavedCasePath({story:plan.story_path,name:plan.case_name??undefined,id:caseId});if(path!==plan.case_path||plan.story_path.endsWith('.prompt.md'))fail('the approved Story plan has an unsafe destination');
 const list=plan.changes,story=list.at(-1),first=list[0];if(first.kind!=='case'||first.path!==path||first.before!==null||story.kind!=='story'||story.path!==plan.story_path)fail('the approved Story plan has invalid changes');
 const oldCriteria=storyCriteria(story.before),future=appendRule(story.before,plan.rule.text),criterionId=`ac-${oldCriteria.length+1}`;
 if(story.after!==future||plan.criterion_id!==criterionId||plan.question!==`This is not in the Story yet. Add it as a new rule: '${plan.rule.text}'? y/N`)fail('the approved Story rule changed');
 const paths=new Set();for(let index=0;index<list.length;index++){const item=list[index];if(!object(item)||!safePath(item.path)||paths.has(item.path)||typeof item.after!=='string'||item.after_sha256!==hash(item.after)||item.before_sha256!==(item.before===null?null:hash(item.before))||!Number.isInteger(item.mode)||item.mode<0||item.mode>0o777)fail('the approved Story plan checksum is invalid');paths.add(item.path);if(index>0&&index<list.length-1){if(item.kind!=='test'||!item.path.endsWith('.json')||migrate(item.before,plan.story_path,oldCriteria)!==item.after)fail('a planned local test migration changed');}}
 const doc=JSON.parse(first.after),scope=doc.criteria_scope,authored=storyCriteria(future).map((text,i)=>({id:`ac-${i+1}`,text})),selected=authored.filter(c=>Array.isArray(scope)&&scope.includes(c.id));
 if(doc.schema_version!==TEST_SCHEMA||doc.story_path!==plan.story_path||!Array.isArray(scope)||!scope.includes(criterionId)||!isDeepStrictEqual(scope,selected.map(c=>c.id))||!isDeepStrictEqual(doc.criteria,selected)||!Array.isArray(doc.steps)||!doc.steps.length)fail('the planned case does not match the approved rule');
 if(!object(plan.receipt)||plan.receipt.repo!==repo||plan.receipt.case_id!==caseId||plan.receipt.path!==path||plan.receipt.sha256!==first.after_sha256||plan.receipt.rule!==plan.rule.text||plan.receipt.criterion_id!==criterionId)fail('the approved Story receipt is invalid');
}
function fileState(repo,item){const info=checked(repo,item.path,{missing:true});if(!info){if(item.before===null)return'before';fail('an approved source file disappeared');}if(!info.isFile())fail('an approved target is not regular');const current=read(join(repo,item.path),Math.max(LIMIT,Buffer.byteLength(item.after)),info),digest=hash(current);if(digest===item.after_sha256)return'after';if(item.before!==null&&digest===item.before_sha256)return'before';fail('an affected file has unrelated edits; the approved transaction was not changed');}
function stateLocation(repo,stateDir,caseId,{create=false}={}){
 if(typeof caseId!=='string'||!caseId||caseId.trim()!==caseId||caseId.length>128||Buffer.byteLength(caseId)>256||control.test(caseId))fail('the Story transaction needs a valid case identity');
 if(typeof stateDir!=='string'||!isAbsolute(stateDir)||resolve(stateDir)!==stateDir)fail('the Story journal needs a canonical private state directory');const rel=relative(repo,stateDir);if(rel===''||(!rel.startsWith('..'+sep)&&rel!=='..'&&!isAbsolute(rel)))fail('the Story journal must stay outside the repository');
 let current=resolve(stateDir).startsWith(sep)?sep:'';for(const part of stateDir.split(sep).filter(Boolean)){current=join(current,part);let info=stat(current);if(!info){if(!create)return null;mkdirSync(current,{mode:0o700});info=stat(current);}if(!info.isDirectory()||info.isSymbolicLink())fail('the Story journal directory is unsafe');}
 const info=stat(stateDir);if((info.mode&0o077)!==0||(process.getuid&&info.uid!==process.getuid()))fail('the Story journal directory is not private');return join(stateDir,`agent-story-rule-${hash(repo+'\0'+caseId)}.json`);
}
const journalHash=record=>hash(JSON.stringify({plan:record.plan,completed:record.completed,receipt:record.receipt}));
function privateJournal(path){const info=stat(path);if(!info)return null;if(!info.isFile()||info.isSymbolicLink()||(info.mode&0o077)!==0||(process.getuid&&info.uid!==process.getuid()))fail('the Story journal file is unsafe');let record;try{record=JSON.parse(read(path,JOURNAL_LIMIT,info));}catch{fail('the Story journal is invalid');}if(record?.schema!==JOURNAL||record.approved!==true||!object(record.plan)||typeof record.completed!=='boolean'||record.sha256!==journalHash(record)||(record.completed?!isDeepStrictEqual(record.receipt,record.plan.receipt):record.receipt!==null))fail('the Story journal has no valid approved plan');return record;}

function writeAll(path,text,mode,guard=()=>{}){let fd,identity;try{fd=openSync(path,constants.O_WRONLY|constants.O_CREAT|constants.O_EXCL|constants.O_NOFOLLOW|constants.O_NONBLOCK,mode);identity=fstatSync(fd);guard();fchmodSync(fd,mode);const bytes=Buffer.from(text);let offset=0;while(offset<bytes.length){const n=writeSync(fd,bytes,offset,bytes.length-offset);if(n<=0)fail('a transaction file could not be completely written');offset+=n;}fsyncSync(fd);guard();}catch(e){if(identity&&same(stat(path),identity))try{unlinkSync(path);}catch{}throw e;}finally{close(fd);}}

function anchor(fd){for(const path of [`/proc/self/fd/${fd}`,`/dev/fd/${fd}`])try{if(same(statSync(path+'/.'),fstatSync(fd)))return path;}catch{}return null;}
function publish(repo,item,guard=()=>{}){
 guard();
 let parent=dirname(join(repo,item.path));if(item.kind==='case'&&!stat(parent)){if(parent!==join(repo,'tests'))fail('the case directory is invalid');mkdirSync(parent,{mode:0o755});}
 checked(repo,item.path,{missing:true});let dirFd,temp;try{dirFd=openSync(parent,constants.O_RDONLY|constants.O_DIRECTORY|constants.O_NOFOLLOW|constants.O_NONBLOCK);const identity=fstatSync(dirFd),matches=()=>same(stat(parent),identity)&&stat(parent)?.isDirectory()&&!stat(parent)?.isSymbolicLink();if(!matches())fail('an affected directory changed');const base=anchor(dirFd)??parent,target=join(base,basename(item.path));temp=join(base,`.pdd-story-rule-${randomUUID()}.tmp`);writeAll(temp,item.after,item.mode,()=>{guard();if(!matches())fail('an affected directory changed');});guard();if(!matches())fail('an affected directory changed');if(fileState(repo,item)==='after')return;if(item.before===null){try{linkSync(temp,target);}catch(e){if(e.code!=='EEXIST'||fileState(repo,item)!=='after')throw e;}}else renameSync(temp,target);syncDirectory(dirFd);if(!matches()||fileState(repo,item)!=='after')fail('an affected file changed during publication');}finally{if(temp)try{unlinkSync(temp);}catch{}close(dirFd);}
}
function execute(plan,stateGuard=()=>{}){
 let rootFd;try{rootFd=openSync(plan.repo,constants.O_RDONLY|constants.O_DIRECTORY|constants.O_NOFOLLOW|constants.O_NONBLOCK);const identity=fstatSync(rootFd),guard=()=>{stateGuard();const info=stat(plan.repo);if(!same(info,identity)||!info.isDirectory()||info.isSymbolicLink())fail('the repository directory changed');};guard();
 const states=plan.changes.map(item=>{guard();return fileState(plan.repo,item);});let wrote=false;
 for(let i=0;i<plan.changes.length;i++)if(states[i]!=='after'){guard();publish(plan.repo,plan.changes[i],guard);wrote=true;}
 guard();if(plan.changes.some(item=>fileState(plan.repo,item)!=='after'))fail('the Story transaction did not complete');return{status:wrote?'added':'already_added',result:`added to ${plan.case_path}${wrote?'':' (already present)'}`,path:plan.case_path,receipt:structuredClone(plan.receipt)};
 }finally{close(rootFd);}
}
function completeJournal(folder,dirFd,path,record,guard){
 const target=join(anchor(dirFd)??folder,basename(path)),temp=join(anchor(dirFd)??folder,`.agent-story-rule-${randomUUID()}.tmp`),next={...record,completed:true,receipt:structuredClone(record.plan.receipt)};next.sha256=journalHash(next);const text=JSON.stringify(next)+'\n';if(Buffer.byteLength(text)>JOURNAL_LIMIT)fail('the completed Story journal exceeds its limit');
 try{guard();writeAll(temp,text,0o600,guard);guard();const current=privateJournal(target);if(!current||current.sha256!==record.sha256)fail('the approved Story journal changed before completion');renameSync(temp,target);syncDirectory(dirFd);guard();const completed=privateJournal(target);if(!completed?.completed||completed.sha256!==next.sha256)fail('the completed Story receipt changed');}finally{try{unlinkSync(temp);}catch{}}
}
function resumeAt(repo,path,caseId,expectedPlanHash,saved){let dirFd;try{const folder=dirname(path);dirFd=openSync(folder,constants.O_RDONLY|constants.O_DIRECTORY|constants.O_NOFOLLOW|constants.O_NONBLOCK);const identity=fstatSync(dirFd),guard=()=>{const info=stat(folder);if(!same(info,identity)||!info.isDirectory()||info.isSymbolicLink()||(info.mode&0o077)!==0)fail('the private Story journal directory changed');};guard();const journal=privateJournal(join(anchor(dirFd)??folder,basename(path)));guard();if(!journal)return{status:'absent',result:'no approved Story rule is pending'};validatePlan(journal.plan,repo,caseId);if(saved!==undefined&&agentSavedCaseFingerprint(saved)!==journal.plan.payload_sha256)fail('the queued case changed after this Story rule was approved');if(expectedPlanHash&&hash(JSON.stringify(journal.plan))!==expectedPlanHash)fail('another approved transaction already owns this case');
 try{
  if(journal.completed){if(journal.plan.changes.some(item=>fileState(repo,item)!=='after'))fail('a completed Story transaction file is missing or edited');return{status:'already_added',result:`added to ${journal.plan.case_path} (already present)`,path:journal.plan.case_path,receipt:structuredClone(journal.receipt)};}
  const result=execute(journal.plan,guard);completeJournal(folder,dirFd,path,journal,guard);return result;
 }catch(e){if(e instanceof Invalid)throw e;return{status:'pending',case_id:caseId,result:'not added yet: the approved Story transaction was interrupted; reconnect to resume it without another question.'};}
 }finally{close(dirFd);}}

function persistJournal(stateDir,path,text){let dirFd,temp;try{dirFd=openSync(stateDir,constants.O_RDONLY|constants.O_DIRECTORY|constants.O_NOFOLLOW|constants.O_NONBLOCK);const identity=fstatSync(dirFd),guard=()=>{const info=stat(stateDir);if(!same(info,identity)||!info.isDirectory()||info.isSymbolicLink()||(info.mode&0o077)!==0)fail('the private Story journal directory changed');};guard();const base=anchor(dirFd)??stateDir;temp=join(base,`.agent-story-rule-${randomUUID()}.tmp`);writeAll(temp,text,0o600,guard);guard();linkSync(temp,join(base,basename(path)));syncDirectory(dirFd);guard();}finally{if(temp)try{unlinkSync(temp);}catch{}close(dirFd);}}

export function resumeAgentStoryRule({root,stateDir,caseId,saved}){try{const repo=realpathSync(root),path=stateLocation(repo,stateDir,caseId);return path?resumeAt(repo,path,caseId,undefined,saved):{status:'absent',result:'no approved Story rule is pending'};}catch(e){return refused(e);}}
export function applyAgentStoryRule({root,stateDir,plan,approved=false}){
 if(approved!==true)return{status:'declined',result:'not added: the person did not approve the new Story rule'};
 try{const repo=realpathSync(root);if(!issued.has(plan)||issued.get(plan)!==hash(JSON.stringify(plan)))fail('the Story rule plan is missing or changed');validatePlan(plan,repo,plan.case_id);
  const existingPath=stateLocation(repo,stateDir,plan.case_id);if(existingPath&&stat(existingPath))return resumeAt(repo,existingPath,plan.case_id,issued.get(plan));
  if(plan.changes.some(item=>fileState(repo,item)!=='before'))fail('the Story rule plan is stale');
  const path=stateLocation(repo,stateDir,plan.case_id,{create:true}),record={schema:JOURNAL,approved:true,plan,completed:false,receipt:null};record.sha256=journalHash(record);const text=JSON.stringify(record)+'\n';if(Buffer.byteLength(text)>JOURNAL_LIMIT)fail('the approved Story journal exceeds its limit');
  persistJournal(stateDir,path,text);return resumeAt(repo,path,plan.case_id);

 }catch(e){return refused(e);}
}
