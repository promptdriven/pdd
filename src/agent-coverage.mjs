// Generated from prompts/cli/agent-coverage.prompt.md (sha256: 0b965a159573795ed2298532748378aff66e76d0dc270441918792658790a0c1).
import {basename} from 'node:path';
const object=x=>x!==null&&typeof x==='object'&&!Array.isArray(x);
function clip(value,max=160){let text='',bytes=0;for(const c of String(value??'').replace(/[\u0000-\u001f\u007f-\u009f]/g,' ')){const n=Buffer.byteLength(c);if(bytes+n>max)break;text+=c;bytes+=n;}return text;}
const id=e=>typeof e?.entry==='string'?e.entry:typeof e?.entry_path==='string'&&typeof e?.operation==='string'?`${e.entry_path}#${e.operation}`:'';
const slug=path=>basename(path,'.md');
const states=new Set(['pass','fail','differs','tried','todo']);
const first=input=>Array.isArray(input?.argv)&&input.argv.every(x=>typeof x==='string')?(input.argv[0]??''):null;
const MARK={pass:'✓',fail:'✗',differs:'~',tried:'~',todo:'·'};
const escaped=text=>text.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
export function createCoverage({scenarios=[],model={},productRules=[]}={}){
 let incomplete=scenarios.incomplete===true;
 model=object(model)?model:{};scenarios=Array.isArray(scenarios)?scenarios:[];
 const entries=new Map(),stories=new Map(),commands=new Map(),endpoints=new Map(),screens=new Map();
 const admitted=Array.isArray(model.entries)?model.entries:[];
 if(admitted.length>64)incomplete=true;
 for(const e of admitted.slice(0,64)){const key=id(e);if(key)entries.set(key,e);}
 const keyFor=(entry,word)=>JSON.stringify([entry,word]);
 const addCommand=(entry,word)=>{
  if(typeof word!=='string'||Buffer.byteLength(word)>120||/[\u0000-\u001f\u007f-\u009f]/.test(word)){incomplete=true;return;}
  const key=keyFor(entry,word);if(commands.has(key))return;
  if(commands.size>=64){incomplete=true;return;}
  const e=entries.get(entry),name=clip(e?.name||basename(entry.split('#')[0]).split('.')[0],64);
  commands.set(key,{entry,command:word,label:clip(`${name} ${word||'(default)'}`),tried:false});
 };
 const cli=new Set();
 for(const [entry,e] of entries){
  if(e.cli===true||e.convention==='cli'||e.input_schema?.properties?.argv||(Array.isArray(e.conventions)&&e.conventions.some(c=>c?.convention==='cli')))cli.add(entry);
  const title=e.input_schema?.title;
  const match=typeof title==='string'?/^HTTP\s+([A-Z]+)\s+(\/\S*)$/i.exec(title):null;
  const method=match?.[1]??e.http?.method,path=match?.[2]??e.http?.path;
  if(typeof method==='string'&&typeof path==='string'&&path.startsWith('/'))endpoints.set(entry,{entry,label:clip(`${method.toUpperCase()} ${path}`),tried:false});
 }
 const storyFor=path=>{
  if(typeof path!=='string'||!path)return null;
  if(!stories.has(path)){if(stories.size>=64){incomplete=true;return null;}stories.set(path,{path:clip(path,256),title:slug(path),criteria:new Map(),references:new Set()});}
  return stories.get(path);
 };
 const addCriteria=(story,list)=>{
  if(!story||!Array.isArray(list))return;
  for(const criterion of list){if(typeof criterion?.id!=='string'||!criterion.id||criterion.id.length>64)continue;if(!story.criteria.has(criterion.id)&&story.criteria.size>=64){incomplete=true;continue;}story.criteria.set(criterion.id,{id:criterion.id});}
 };
 if(scenarios.length>128)incomplete=true;
 for(const scenario of scenarios.slice(0,128)){
  const doc=scenario?.doc;if(!object(doc))continue;
  const story=storyFor(doc.story_path);addCriteria(story,doc.criteria);
  const steps=Array.isArray(doc.steps)?doc.steps:[];
  for(const step of steps){const entry=id(step);if(story&&entry)story.references.add(entry);if(cli.has(entry)){const word=first(step.input);if(word!==null)addCommand(entry,word);}}
 }
 const modelStories=Array.isArray(model.stories)?model.stories:Object.values(object(model.stories)?model.stories:{});
 for(const source of modelStories){const story=storyFor(source?.path);if(!story)continue;if(typeof source.title==='string')story.title=clip(source.title);addCriteria(story,source.criteria);}
 for(const binding of Array.isArray(model.criterion_bindings)?model.criterion_bindings:[]){const story=storyFor(binding?.story_path);const entry=id(binding);if(story&&entry)story.references.add(entry);}
 for(const example of Array.isArray(model.examples)?model.examples:[]){const entry=id(example);if(cli.has(entry)){const word=first(example.input);if(word!==null)addCommand(entry,word);}}
 for(const [entry,e] of entries){
  if(!cli.has(entry))continue;
  const path=entry.split('#')[0];
  for(const rule of Array.isArray(productRules)?productRules:[]){
   if(rule?.path!==path||typeof rule.text!=='string')continue;
   const program=clip(e.name||rule.text.match(/\bUsage:\s*([A-Za-z][\w.-]*)/i)?.[1]||basename(path).split('.')[0],64);
   const pattern=new RegExp('(?:`|^\\s*(?:[-*]\\s*)?(?:Usage:\\s*)?)'+escaped(program)+'\\s+([A-Za-z][A-Za-z0-9_-]*|--[a-z][a-z-]*)','gmi');
   for(const match of rule.text.matchAll(pattern))addCommand(entry,match[1]);
  }
 }
 for(const entry of cli)if(![...commands.values()].some(x=>x.entry===entry)){incomplete=true;if(commands.size>=64)continue;commands.set(keyFor(entry,null),{entry,command:null,label:clip(`${entries.get(entry)?.name||'CLI'} (commands unknown)`),tried:false});}
 const screenSources=[...(Array.isArray(model.screen_sources)?model.screen_sources:[]),...(Array.isArray(model.app_map?.screens)?model.app_map.screens:[])];
 for(const source of screenSources){if(typeof source?.id!=='string'||!source.id)continue;if(screens.size>=64&&!screens.has(source.id)){incomplete=true;continue;}screens.set(source.id,{id:clip(source.id,128),label:clip(source.name||source.title||source.id),tried:false});}
 if(model.app_map===true&&!screens.size)incomplete=true;
 function record(run){
  if(!object(run))return;
  const entry=run.entry;
  if(endpoints.has(entry))endpoints.get(entry).tried=true;
  if(cli.has(entry)){const unknown=commands.get(keyFor(entry,null));if(unknown)unknown.tried=true;const word=first(run.input);if(word!==null&&commands.has(keyFor(entry,word)))commands.get(keyFor(entry,word)).tried=true;}
  const ids=[run.screen,...(Array.isArray(run.screens)?run.screens:[])];
  for(const screen of ids)if(typeof screen==='string'&&screens.has(screen))screens.get(screen).tried=true;
 }
 function snapshot({progressByStory={},ownCases=[]}={}){
  progressByStory=progressByStory instanceof Map||object(progressByStory)?progressByStory:{};ownCases=Array.isArray(ownCases)?ownCases:[];
  const projected=[];
  for(const story of stories.values()){
   const raw=progressByStory instanceof Map?(progressByStory.get(story.path)??progressByStory.get(slug(story.path))):(progressByStory[story.path]??progressByStory[slug(story.path)]);
   const list=Array.isArray(raw)?raw:Array.isArray(raw?.items)?raw.items:[];
   const progress=new Map(list.filter(x=>typeof x?.id==='string').map(x=>[x.id,states.has(x.state)?x.state:'todo']));
   const criteria=[...story.criteria.keys()].map(id=>({id,state:progress.get(id)??'todo'}));
   const runnable=story.references.size>0&&[...story.references].every(entry=>entries.has(entry));
   projected.push({path:story.path,title:story.title,runnable,needsOwnTry:runnable?null:`pdd simulate ${slug(story.path)}`,criteria,passed:criteria.filter(x=>x.state==='pass').length,total:criteria.length});
  }
  const own=(Array.isArray(ownCases)?ownCases:[]).slice(0,64).map(item=>({name:clip(item?.name||'Own case'),state:item?.saved===true||item?.state==='saved'?'saved':item?.matched===true||['match','matched'].includes(item?.state)?'matched':item?.state==='differs'?'differs':'pending'}));
  const allCli=[...commands.values()].map(x=>({...x})),http=[...endpoints.values()].map(x=>({...x})),allScreens=[...screens.values()].map(x=>({...x}));
  const known=projected.length+allCli.length+http.length+allScreens.length>0;
  const fullyTried=known&&!incomplete&&ownCases.length<=64&&projected.every(s=>s.runnable&&s.criteria.every(c=>c.state==='pass'))&&[...allCli,...http,...allScreens].every(x=>x.tried)&&own.every(x=>['matched','saved'].includes(x.state));
  const total=projected.reduce((n,s)=>n+s.total,0),passed=projected.reduce((n,s)=>n+s.passed,0);
  const line=`Coverage: ${passed}/${total} criteria pass · ${[...allCli,...http,...allScreens].filter(x=>x.tried).length}/${allCli.length+http.length+allScreens.length} surfaces tried${fullyTried?' · fully tried':''}${incomplete?' · inventory incomplete':''}`;
  const lines=[line,...projected.map(s=>`${s.title}: ${s.runnable?`${s.passed}/${s.total} pass ${s.criteria.map(c=>c.id+MARK[c.state]).join(' ')}`:'needs its own Try: '+s.needsOwnTry}`),`CLI: ${allCli.map(x=>x.label+(x.tried?' ✓':' ·')).join(', ')||'none'}`,`HTTP: ${http.map(x=>x.label+(x.tried?' ✓':' ·')).join(', ')||'none'}`,`Screens: ${allScreens.map(x=>x.label+(x.tried?' ✓':' ·')).join(', ')||(model.app_map===true?'unknown (inventory incomplete)':'none')}`,`Own cases: ${own.map(x=>x.name+' ('+x.state+')').join(', ')||'none yet'}`];
  return{stories:projected,cli:allCli,http,screens:allScreens,ownCases:own,fullyTried,line,text:clip(lines.join('\n'),1024)};
 }
 return{record,snapshot};
}
