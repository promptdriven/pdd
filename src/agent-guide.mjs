// Generated from prompts/cli/agent-guide.prompt.md (sha256: 762868e85137d7c6a71bb0fc2fbf5f37861fb8e64477901c6db7c4bc9cdc2c8f).
import {createHash} from 'node:crypto';
import {buildProjectCard,readAgentScenarios,readAgentStoryCriteria} from './agent-project.mjs';
import {createRunJudge,compareExpectation} from './agent-judge.mjs';
import {createCoverage} from './agent-coverage.mjs';
import {checkInput} from './runtime-preflight.mjs';
const object=x=>x!==null&&typeof x==='object'&&!Array.isArray(x);
const own=(x,k)=>object(x)&&Object.hasOwn(x,k);
const clone=x=>structuredClone(x);
const hash=x=>createHash('sha256').update(JSON.stringify(x)).digest('hex');
const clip=(x,n)=>Array.from(String(x??'')).slice(0,n).join('');
const clipBytes=(value,max)=>{let text='',bytes=0;for(const c of String(value??'')){const n=Buffer.byteLength(c);if(bytes+n>max)break;text+=c;bytes+=n;}return text;};
const entryId=e=>typeof e==='string'?e:object(e)&&typeof e.entry_path==='string'&&typeof e.operation==='string'?`${e.entry_path}#${e.operation}`:null;
const rank=states=>['fail','differs','tried'].find(s=>states.includes(s))??(states.length&&states.every(s=>s==='pass')?'pass':'todo');
function progress(items){const marks={pass:'✓',fail:'✗',differs:'~',tried:'~',todo:'·'};return{line:clip(`Story progress: ${items.filter(x=>x.state==='pass').length} of ${items.length} pass · ${items.map(x=>`${x.id}${marks[x.state]??'·'}${x.check_passed?' (check ✓)':''}`).join(' ')}`,300),items:items.slice(0,64)};}
const SECRET=/token|password|secret|api[_-]?key|authorization|cookie|credential/i;
function clean(value,secrets){
 if(typeof value==='string'){
  for(const secret of secrets)if(typeof secret==='string'&&secret)value=value.split(secret).join('[redacted]');
  value=value.replace(/https?:\/\/[^\s"'<>]+/g,text=>{try{const url=new URL(text);let changed=false;if(url.username||url.password){url.username='';url.password='';changed=true;}for(const key of [...url.searchParams.keys()])if(SECRET.test(key)||/^(?:key|auth|signature)$/i.test(key)){url.searchParams.set(key,'[redacted]');changed=true;}return changed?url.href:text;}catch{return text.replace(/(https?:\/\/)[^\s/@]+(?::[^\s/@]*)?@/gi,'$1[redacted]@');}});
  return value.replace(/-----BEGIN [^-]*PRIVATE KEY-----[\s\S]*?(?:-----END [^-]*PRIVATE KEY-----|$)/g,'[redacted]').replace(/\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,})\b/g,'[redacted]').replace(/\b(?:Bearer|Basic)\s+\S+/gi,'[redacted]').replace(/\b(token|password|secret|api[_-]?key|authorization|cookie|credential)["']?\s*[:=]\s*(?:"[^"]*"|'[^']*'|[^\s,;]+)/gi,'$1=[redacted]').replace(/[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]/g,'');
 }
 if(Array.isArray(value))return value.map(x=>clean(x,secrets));
 if(object(value)){let path=value.path;try{path=decodeURIComponent(path);}catch{}const secretPath=typeof path==='string'&&SECRET.test(path);return Object.fromEntries(Object.entries(value).map(([k,v])=>[k,SECRET.test(k)||(secretPath&&['expected','got','actual'].includes(k))?'[redacted]':clean(v,secrets)]));}
 return value;
}
function normalizeScenarios(found){
 const rows=[];let incomplete=!Array.isArray(found)||found.incomplete===true;
 for(const candidate of (Array.isArray(found)?found:[]).slice(0,128)){
  let doc;try{doc=clone(candidate?.doc);}catch{incomplete=true;continue;}
  if(typeof candidate?.path!=='string'||!object(doc)||doc.schema_version!=='prompt-runtime.program-scenario.v1'||typeof doc.story_path!=='string'||!Array.isArray(doc.criteria)||!Array.isArray(doc.steps)){incomplete=true;continue;}
  const fingerprint=hash(doc);let invalid=!object(doc.initial_world);if(invalid)delete doc.initial_world;
  const criteria=doc.criteria.filter(c=>{const valid=object(c)&&typeof c.id==='string'&&c.id.length>0&&c.id.length<=64;if(!valid)invalid=true;return valid;}).slice(0,64);
  if(criteria.length!==doc.criteria.length||new Set(criteria.map(c=>c.id)).size!==criteria.length)invalid=true;
  const steps=[];
  for(const step of doc.steps.slice(0,256)){
   if(!object(step)||typeof step.entry_path!=='string'||typeof step.operation!=='string'||!object(step.input)){invalid=true;continue;}
   const checks=(Array.isArray(step.checks)?step.checks:[]).filter(c=>{const valid=object(c)&&typeof c.criterion_id==='string'&&typeof c.target==='string'&&typeof c.path==='string'&&typeof c.op==='string';if(!valid)invalid=true;return valid;}).slice(0,256);
   if(!Array.isArray(step.checks)||checks.length!==step.checks.length)invalid=true;
   steps.push({...step,checks});
  }
  if(steps.length!==doc.steps.length)invalid=true;
  incomplete ||= invalid;
  rows.push({path:candidate.path,doc:{...doc,criteria,steps},incomplete:invalid,fingerprint});
 }
 if(Array.isArray(found)&&found.length>128)incomplete=true;
 Object.defineProperty(rows,'incomplete',{value:incomplete});Object.defineProperty(rows,'readerIncomplete',{value:found?.incomplete===true});return rows;
}
function criterionIdentities(records,model,sourceFound){
 const pinned=Array.isArray(model.stories)?model.stories:Object.values(model.stories??{}),sources=new Map();
 let incomplete=records.incomplete||!Array.isArray(sourceFound)||sourceFound.incomplete===true;
 for(const row of (Array.isArray(sourceFound)?sourceFound:[]).slice(0,128)){
  if(!object(row)||typeof row.path!=='string'||!Array.isArray(row.criteria)){incomplete=true;continue;}
  const valid=row.criteria.every((c,index)=>object(c)&&c.id===`ac-${index+1}`&&typeof c.text==='string'&&c.text.length>0);
  if(!valid||sources.has(row.path)){incomplete=true;sources.set(row.path,{criteria:[],invalid:true});}else sources.set(row.path,row);
 }
 if(Array.isArray(sourceFound)&&sourceFound.length>128)incomplete=true;
 const paths=new Set([...pinned.map(s=>s?.path).filter(x=>typeof x==='string'),...records.map(s=>s.doc.story_path)]),maps=new Map(),stories=[];
 for(const path of paths){
  const source=sources.get(path),sourceCriteria=source?.criteria??[],local=records.filter(r=>r.doc.story_path===path),pinnedStory=pinned.find(s=>s?.path===path),pinnedCriteria=Array.isArray(pinnedStory?.criteria)?pinnedStory.criteria:[];
  const aliases=new Map();let ambiguous=source?.invalid===true;
  const add=c=>{if(!object(c)||typeof c.id!=='string'||!c.id||typeof c.text!=='string'||!c.text){ambiguous=true;return;}if(!aliases.has(c.id))aliases.set(c.id,new Set());aliases.get(c.id).add(c.text);};
  for(const c of pinnedCriteria)add(c);for(const row of local)for(const c of row.doc.criteria)add(c);
  if([...aliases.values()].some(texts=>texts.size!==1))ambiguous=true;
  if(new Set(sourceCriteria.map(c=>c.text)).size!==sourceCriteria.length||new Set(pinnedCriteria.map(c=>c?.text)).size!==pinnedCriteria.length)ambiguous=true;
  const texts=source?[...new Set(sourceCriteria.map(c=>c.text))]:[...new Set([...pinnedCriteria,...local.flatMap(r=>r.doc.criteria)].map(c=>c?.text).filter(x=>typeof x==='string'&&x))];
  if(source&&[...aliases.values()].some(values=>[...values].some(text=>!texts.includes(text))))ambiguous=true;
  const display=new Map(),used=new Map();
  for(const text of texts){
   const candidates=pinnedCriteria.filter(c=>c?.text===text&&aliases.get(c.id)?.size===1).map(c=>c.id),canonical=sourceCriteria.find(c=>c.text===text)?.id;
   let id=candidates.length===1?candidates[0]:canonical;
   if(!id&&!source){const old=[...aliases].filter(([,values])=>values.size===1&&values.has(text)).map(([key])=>key);if(old.length===1)id=old[0];else if(!old.length)ambiguous=true;}
   if(typeof id!=='string'||!/^[A-Za-z0-9._-]{1,64}$/.test(id)||used.has(id)&&used.get(id)!==text){ambiguous=true;id=`unknown-${hash(text).slice(0,12)}`;}
   display.set(text,id);used.set(id,text);
  }
  const alias=new Map([...aliases].map(([raw,texts])=>[raw,texts.size===1?display.get([...texts][0])??null:null])),official=new Map();
  for(const c of sourceCriteria){const raw=aliases.get(c.id);official.set(c.id,!ambiguous&&(!raw||raw.size===1&&raw.has(c.text))?display.get(c.text)??null:null);}
  if(ambiguous)incomplete=true;
  maps.set(path,{display,alias,official,ambiguous});
  stories.push({...pinnedStory,path,title:pinnedStory?.title??path.split('/').at(-1).replace(/\.md$/,''),criteria:texts.map(text=>({id:display.get(text),text}))});
 }
 const normalized=records.map(row=>{
  const map=maps.get(row.doc.story_path),byRaw=new Map(),criteria=[];let invalid=row.incomplete||map?.ambiguous===true;
  for(const c of row.doc.criteria){const id=map?.display.get(c.text);if(!id){invalid=true;continue;}byRaw.set(c.id,id);if(criteria.some(item=>item.id===id)){invalid=true;continue;}criteria.push({...c,id});}
  const steps=row.doc.steps.map(step=>({...step,checks:step.checks.flatMap(check=>{const id=byRaw.get(check.criterion_id);if(!id){invalid=true;return[];}return[{...check,criterion_id:id}];})}));
  if(invalid)incomplete=true;
  return{...row,doc:{...row.doc,criteria,steps},incomplete:invalid};
 });
 Object.defineProperty(normalized,'incomplete',{value:incomplete});Object.defineProperty(normalized,'readerIncomplete',{value:records.readerIncomplete});
 const bindings=(Array.isArray(model.criterion_bindings)?model.criterion_bindings:[]).flatMap(binding=>{const map=maps.get(binding?.story_path);if(!map||map.ambiguous)return[];const id=map.alias.get(binding.criterion_id)??map.official.get(binding.criterion_id);return id?[{...binding,criterion_id:id}]:[];});
 return{records:normalized,stories,maps,model:{...model,stories:Object.fromEntries(stories.map(s=>[s.path,s])),criterion_bindings:bindings},sourceIdentity:{rows:Array.isArray(sourceFound)?sourceFound:[],incomplete:sourceFound?.incomplete===true}};
}
const uncertain=verdict=>({...verdict,state:verdict.state==='pass'?'tried':verdict.state,items:(verdict.items??[]).map(item=>({...item,state:item.state==='pass'?'tried':item.state}))});
function compactSurface(run){
 const result=[];
 if(typeof run.entry==='string')result.push({entry:run.entry,input:Array.isArray(run.input?.argv)?{argv:run.input.argv.length?[run.input.argv[0]]:[]}:{}});
 for(const screen of [run.screen,...(Array.isArray(run.screens)?run.screens:[])])if(typeof screen==='string')result.push({screen});
 return result;
}
function observed(current){const last=current.last_answer;if(!object(last)||typeof last.id!=='string'||(!last.id.length||last.id.length>128)||last.notSent)return null;const entry=entryId(last.entry);if(!entry||!object(last.input))return null;const report=object(last.report)?last.report:{};const native=own(report,'program_result'),lossless=(last.lossless===true||current.lossless===true)&&native;
 const run={id:last.id,entry,input:clone(last.input),lossless};
 if(lossless)run.result=clone(report.program_result);else if(own(report,'result'))run.result=clone(report.result);else if(own(last,'result'))run.result=clone(last.result);
 const before=own(report,'input_world')?report.input_world:own(last,'world_before')?last.world_before:undefined;
 const after=own(report,'world')?report.world:own(last,'world_after')?last.world_after:undefined;
 if(before!==undefined)run.world_before=clone(before);if(after!==undefined)run.world_after=clone(after);
 if(typeof last.screen==='string')run.screen=last.screen;if(Array.isArray(last.screens))run.screens=last.screens.filter(x=>typeof x==='string').slice(0,64);
 return run;
}
export function createTryGuide({root,env={},model,test={},features=[],secrets=[],ports={}}){
 let closed=false,mode='chat',conversation=[],runs=[],ownCases=[],pending=null,lastContext=null,requestKind=null,card=null,sourceAtConnect=null,scenarios=[],scenarioHash=null,scenarioAtConnect=null,judges=[],coverage=null,count=0,savedCount=0;
 const seen=new Set(),savedIds=new Set(),surfaceEvidence=new Map();let coverageHash=null;const entries=(model.entries??[]).map(e=>({...e,entry:entryId(e)}));
 const storyPath=test.storyPath??model.seed?.story_path??null;
 let modelStories=Array.isArray(model.stories)?model.stories:Object.values(model.stories??{}),identityMaps=new Map(),viewModel=model;
 const currentStory=()=>storyPath??scenarios.find(s=>s.path===test.path)?.doc.story_path??modelStories[0]?.path??null;
 const validFill=fill=>{if(!object(fill)||!object(fill.input))return false;const e=entries.find(e=>e.entry===fill.entry);if(!e)return false;const checked=checkInput(fill.input,e.input_schema,0);return !checked.refusals.length&&!checked.warnings.length;};
 const safe=x=>clean(x,secrets);
 const finalFills=value=>{if(own(value,'run')&&(typeof value.run!=='boolean'||!features.includes('run')||!features.includes('apply')||!['chat','own','walk'].includes(requestKind)||(value.run===true&&(value.apply!==true||!validFill(value.fill)))))delete value.run;if(own(value,'fill')&&!validFill(value.fill)){value.fill=null;if(value.apply===true)delete value.apply;}if(object(value.next)&&own(value.next,'fill')&&!validFill(value.next.fill))delete value.next.fill;return value;};
 function refresh(){
  const parsed=normalizeScenarios((ports.readAgentScenarios??readAgentScenarios)({root}));
  const identity=criterionIdentities(parsed,model,(ports.readAgentStoryCriteria??readAgentStoryCriteria)({root}));
  const next=identity.records,digest=hash({rows:next,incomplete:next.incomplete,readerIncomplete:next.readerIncomplete,sourceIdentity:identity.sourceIdentity});scenarioAtConnect??=digest;
  if(digest!==scenarioHash){scenarios=next;scenarioHash=digest;modelStories=identity.stories;identityMaps=identity.maps;viewModel=identity.model;judges=scenarios.map(s=>{const base=createRunJudge({scenario:s.doc});return{path:s.path,story:s.doc.story_path,judge:s.incomplete?{record:r=>uncertain(base.record(r)),snapshot:()=>uncertain(base.snapshot()),bindings:()=>base.bindings()}:base};});for(const r of runs)if(!r.redacted)for(const j of judges)j.judge.record(r);}
 }
 function refreshCard(byStory){
  card=(ports.buildProjectCard??buildProjectCard)({root,env,story:test.story??currentStory(),progress:byStory[currentStory()]??[],previousFingerprint:card?.fingerprint,secrets,entries,startWorld:model.seed?.initial_world,model:viewModel,scenarios,seedTest:test.path,savedCount});
  sourceAtConnect??=card.sourceFingerprint??card.fingerprint;
  const digest=hash({scenarioHash,source:card.sourceFingerprint??card.fingerprint,rules:card.productRules??[]});
  if(!coverage||digest!==coverageHash){coverage=createCoverage({scenarios,model:viewModel,productRules:card.productRules??[]});coverageHash=digest;}for(const r of surfaceEvidence.values())coverage.record(r);
 }
 function statesByStory(){const result={};const paths=new Set([...modelStories.map(s=>s.path).filter(Boolean),...judges.map(j=>j.story)]);
  for(const path of paths){const rows=judges.filter(j=>j.story===path).map(j=>j.judge.snapshot().items);const declared=[...(modelStories.find(s=>s.path===path)?.criteria??[]),...scenarios.filter(s=>s.doc.story_path===path).flatMap(s=>s.doc.criteria)];const unique=[...new Map(declared.filter(object).map(c=>[c.id,c])).values()];
   result[path]=unique.filter(c=>typeof c.id==='string').slice(0,64).map(c=>{const all=rows.flatMap(r=>r.filter(i=>i.id===c.id));const checks=(card?.latestCheck?.rows??[]).filter(row=>row.story===path||row.story===path.split('/').at(-1).replace(/\.md$/,''));const identities=identityMaps.get(path);const official=identities?.ambiguous?[]:checks.flatMap(row=>(row.criterion_results??[]).filter(x=>{const id=/^ac-[1-9][0-9]*$/.test(x.criterion_id)?identities?.official.get(x.criterion_id):identities?.alias.get(x.criterion_id);return id===c.id;}));return{id:c.id,state:rank(all.map(x=>x.state)),...(official.length&&official.every(x=>x.status==='passed')?{check_passed:true}:{})};});
  }return result;
 }
 function bindings(){const bound=[];for(const j of judges.filter(j=>j.story===currentStory()))for(const b of j.judge.bindings())if(!bound.some(x=>x.id===b.id))bound.push(b);
  for(const b of viewModel.criterion_bindings??[])if(b.story_path===currentStory()&&!bound.some(x=>x.id===b.criterion_id)){const fill={entry:entryId(b),input:b.input};if(validFill(fill))bound.push({id:b.criterion_id,...fill});}return bound;
 }
 function ensureOwn(name){let current=ownCases.at(-1);if(!current||current.state==='saved'){current={id:`own-${++count}`,name:safe(clip(name||`Own case ${count}`,100)),state:'planned'};ownCases.push(current);ownCases=ownCases.slice(-32);}return current;}
 function prepare(message){
  if(closed)throw Error('The Try guide is closed.');
  requestKind=message.kind??'chat';
  const rawCurrent=object(message.context)?message.context:{},current=safe(rawCurrent);refresh();
  if(message.kind==='own'){mode='own case';pending=null;ownCases.push({id:`own-${++count}`,name:`Own case ${count}`,state:'planned'});ownCases=ownCases.slice(-32);}
  else if(message.kind==='walk'||/walk me through/i.test(message.text))mode='walk';else if(/^\s*(?:stop|stop walking|exit walk|stop the walkthrough)[.!]?\s*$/i.test(message.text))mode='chat';
  const rawRun=observed(rawCurrent),run=rawRun?safe(rawRun):null;let verdict=null;
  if(run&&!seen.has(run.id)){
   const compact=compactSurface(run);const additions=compact.filter(item=>!surfaceEvidence.has(hash(item)));
   if(seen.size>=256||surfaceEvidence.size+additions.length>256)throw Error('Reconnect your agent before more run events; this connection reached its deduplication limit.');
   seen.add(run.id);for(const item of compact)surfaceEvidence.set(hash(item),item);
   const redacted=JSON.stringify(rawRun)!==JSON.stringify(run);if(redacted)run.redacted=true;
   const outcomes=judges.map(j=>({story:j.story,path:j.path,...(redacted?{state:'tried',matched:false,items:[],unchecked:['Observation redacted; comparisons unavailable.']}:j.judge.record(run))}));
   const ownVerdict=pending&&!redacted?compareExpectation({expect:pending.expect,run,entry:pending.fill.entry,input:pending.fill.input,...(own(pending,'world_before')?{world_before:pending.world_before}:{})}):null;
   if(ownVerdict&&ownVerdict.state!=='not_compared'){const c=ownCases.find(x=>x.id===pending.caseId);if(c)c.state=ownVerdict.state==='match'?'matched':'differs';run.own_expectation=safe({text:pending.expect.text,...ownVerdict});}
   run.check=safe(outcomes.filter(o=>o.story===currentStory()));
   const matching=outcomes.filter(o=>o.story===currentStory()&&o.matched);
   if(matching.length&&matching.every(o=>o.state==='pass')&&!scenarios.incomplete)verdict={state:'pass',items:matching.flatMap(o=>o.items)};
   runs.push(run);runs=runs.slice(-8);
  }
  let byStory=statesByStory();refreshCard(byStory);byStory=statesByStory();
  const items=byStory[currentStory()]??modelStories[0]?.criteria?.map(c=>({id:c.id,state:'todo'}))??[];
  const p=progress(items),coverageView=coverage.snapshot({progressByStory:byStory,ownCases});
  if(!coverageView.fullyTried){card={...card,nextStep:'Finish the Try',text:/Next step:[^\n]*/.test(card.text)?card.text.replace(/Next step:[^\n]*/,'Next step: Finish the Try.'):`Next step: Finish the Try.\n${card.text}`};}
  const declared=[...(modelStories.find(s=>s.path===currentStory())?.criteria??[]),...scenarios.filter(s=>s.doc.story_path===currentStory()).flatMap(s=>s.doc.criteria)];
  const bound=bindings();const criteria=[...new Map(declared.filter(object).map(c=>[c.id,c])).values()].filter(c=>typeof c.id==='string').slice(0,64).map(c=>({...c,...items.find(i=>i.id===c.id),...bound.find(b=>b.id===c.id),story_path:currentStory()}));
  if(mode==='walk'&&items.length&&items.every(x=>x.state==='pass'))mode='chat';
  const fields={entry:current.entry??null,input:current.input??null,preloaded:runs.length===0&&conversation.every(c=>!c.fill),...(mode==='own case'?{source:'blank: the person pressed + Your own case'}:{})};
  const changed=scenarioHash!==scenarioAtConnect||(card.sourceFingerprint??card.fingerprint)!==sourceAtConnect;const project=clipBytes((changed?'Local copy changed: checks use your current local Story/test copy, which changed after this Try opened.\n':'')+card.text,1536);
  lastContext=safe({requestKind,project,coverage:coverageView,productRules:card.productRules??[],criteria,progress:p,world:current.world,runs,fields,mode,conversation,message:message.text,changed,ownCases,current});
  let fast=null;
  if(message.kind==='run'&&features.includes('run_events')&&verdict?.state==='pass'&&!ownCases.some(c=>c.state!=='saved')){
   const ids=[...new Set(verdict.items.filter(i=>i.state==='pass').map(i=>i.id).filter(x=>/^AC\d+$/.test(x)))];
   fast={say:`${ids.join(', ')||'Compared checks'} pass: the compared checks match. Other checks remain for pdd check.`,fill:null};
   const next=criteria.find(c=>c.state!=='pass'&&c.entry&&object(c.input));if(next){fast.next={text:`Next: ${next.id}. Fill it?`,criterion:next.id};if(mode==='walk'){fast.fill={entry:next.entry,input:clone(next.input)};fast.apply=features.includes('apply');fast.criterion=next.id;}}
  }
  return{context:clone(lastContext),fast};
 }
 function decorate(reply){const result=safe(clone(reply));result.progress={...(lastContext?.progress??progress([])),coverage:lastContext?.coverage};if(object(result.next))delete result.next.fill;if(result.next?.criterion){const b=bindings().find(x=>x.id===result.next.criterion);const candidate=b?safe({entry:b.entry,input:clone(b.input)}):null;if(candidate&&validFill(candidate))result.next={...result.next,fill:candidate};}return finalFills(safe(result));}
 function wire(reply){const out={say:clip(reply.say,14000),fill:validFill(reply.fill)?reply.fill:null};if(features.includes('apply')&&typeof reply.apply==='boolean')out.apply=reply.apply;if(features.includes('run')&&typeof reply.run==='boolean')out.run=reply.run;if(features.includes('progress')){for(const key of ['criterion','next','progress'])if(own(reply,key))out[key]=reply[key];}else if(reply.progress?.line)out.say=clip(out.say,13500)+'\n'+reply.progress.line;if(features.includes('expect')&&own(reply,'expect'))out.expect=reply.expect;if(features.includes('save')&&own(reply,'save'))out.save=reply.save;return finalFills(safe(out));}
 function delivered(message,reply){if(closed)return;const visible=wire(reply);const row=safe({person:clip(message.text,500),say:clip(visible.say,500),...Object.fromEntries(['fill','expect','save','next','run'].filter(k=>own(visible,k)).map(k=>[k,visible[k]])),...(typeof visible.apply==='boolean'?{apply:visible.apply}:{})});conversation.push(row);conversation=conversation.slice(-6);
  if(reply.expect&&validFill(reply.fill)){const c=ensureOwn(reply.save?.name);pending={caseId:c.id,fill:safe(clone(reply.fill)),expect:safe(clone(reply.expect)),...(own(lastContext?.current,'world')?{world_before:clone(lastContext.current.world)}:{})};}
  if(visible.save){const c=ensureOwn(visible.save.name);c.name=safe(clip(visible.save.name,100));c.offered=true;}
 }
 function saved(record){if(closed||typeof record?.id!=='string'||!record.id||record.id.length>128||typeof record.result!=='string'||!record.result.startsWith('added to ')||savedIds.has(record.id))return;if(savedIds.size>=256)throw Error('Reconnect your agent before importing more saved-case receipts.');savedIds.add(record.id);savedCount++;let c=ownCases.find(x=>x.name===record.name);if(!c)c=ensureOwn(record.name);c.state='saved';c.destination=safe(clip(record.result,300));pending=null;}
 function close(){closed=true;conversation=[];runs=[];ownCases=[];pending=null;lastContext=null;card=null;scenarios=[];judges=[];coverage=null;coverageHash=null;surfaceEvidence.clear();seen.clear();savedIds.clear();}
 refresh();refreshCard(statesByStory());
 return{prepare,decorate,wire,delivered,saved,close};
}
