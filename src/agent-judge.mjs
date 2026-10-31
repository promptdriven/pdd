// Generated from prompts/cli/agent-judge.prompt.md (sha256: 1f1b319ce2b65c859531b654773135e9ec5fbff098cde31f5c6d8b8e356f59ab).
import {isDeepStrictEqual} from 'node:util';
const clone=value=>JSON.parse(JSON.stringify(value));
const own=(x,k)=>x!==null&&typeof x==='object'&&Object.hasOwn(x,k);
const references=x=>Array.isArray(x)?x.some(references):x!==null&&typeof x==='object'&&(own(x,'$step_result')||Object.values(x).some(references));
const entry=s=>`${s.entry_path}#${s.operation}`;
const validPointer=p=>typeof p==='string'&&(p===''||(p.startsWith('/')&&!/~(?:[^01]|$)/.test(p)));
function at(value,path){if(!validPointer(path))return{invalid:true};if(value===undefined)return{missing:true};if(path==='')return{value};for(const key of path.slice(1).split('/').map(k=>k.replace(/~1/g,'/').replace(/~0/g,'~'))){if(!own(value,key))return{missing:true};value=value[key];}return{value};}
const ranked=states=>['fail','differs','tried','todo','pass'].find(s=>states.includes(s))??'todo';
function expectedStart(scenario,index){if(index===0)return own(scenario,'initial_world')&&!references(scenario.initial_world)?{known:true,value:scenario.initial_world}:{known:false};const values=(scenario.steps[index-1].checks??[]).filter(c=>c.target==='world'&&c.op==='equals'&&c.path==='').map(c=>c.value);return values.length&&values.every(v=>v!==null&&typeof v==='object'&&!Array.isArray(v)&&!references(v)&&isDeepStrictEqual(v,values[0]))?{known:true,value:values[0]}:{known:false};}
export function createRunJudge({scenario,checkPassed=[]}){
 scenario=clone(scenario);const criteria=scenario.criteria??[],steps=scenario.steps??[],official=new Set(checkPassed),history=new Map(),evidence=new Map(),tried=new Set();
 const groups=new Map(criteria.map(c=>[c.id,steps.map((s,i)=>(s.checks??[]).some(ch=>ch.criterion_id===c.id)?i:null).filter(i=>i!==null)]));
 function bindings(){return criteria.flatMap(c=>{const s=steps.find(s=>(s.checks??[]).some(ch=>ch.criterion_id===c.id)&&!references(s.input));return s?[{id:c.id,entry:entry(s),input:clone(s.input)}]:[];});}
 function snapshot(){const items=criteria.map(c=>{const required=groups.get(c.id),states=required.map(i=>evidence.get(`${c.id}:${i}`)?.state??'todo');let state=ranked(states);if(state==='todo'&&(tried.has(c.id)||states.some(s=>s!=='todo')))state='tried';return{id:c.id,state,...(official.has(c.id)?{check_passed:true}:{})};});const marks={pass:'✓',fail:'✗',differs:'~',tried:'~',todo:'·'};return{line:`Story progress: ${items.filter(i=>i.state==='pass').length} of ${items.length} pass · ${items.map(i=>`${i.id}${marks[i.state]}${i.check_passed?' (check ✓)':''}`).join(' ')}`,items};}
 function record(run){
  if(run.id!==undefined&&history.has(run.id))return clone(history.get(run.id));
  const exact=steps.flatMap((s,index)=>entry(s)===run.entry&&!references(s.input)&&isDeepStrictEqual(s.input,run.input)?[{s,index}]:[]),matched=exact.length>0;
  const items=[],allStarts=[];let firstDifference;
  if(!matched){for(const c of criteria){if(steps.some(s=>entry(s)===run.entry&&(s.checks??[]).some(ch=>ch.criterion_id===c.id))){tried.add(c.id);items.push({id:c.id,state:'tried',compared:0,unchecked:[]});}}}
  for(const {s,index} of exact){
   const expected=expectedStart(scenario,index),same=expected.known&&own(run,'world_before')&&isDeepStrictEqual(run.world_before,expected.value);allStarts.push(same);
   for(const c of criteria){const checks=(s.checks??[]).filter(ch=>ch.criterion_id===c.id);if(!checks.length)continue;const item={id:c.id,state:'tried',compared:0,unchecked:[]};
    const skip=reason=>{if(!item.unchecked.includes(reason))item.unchecked.push(reason);};
    for(const ch of checks){
     if(ch.target==='calls'){skip('calls not checked here: pdd test covers them');continue;}
     if(ch.op!=='equals'||!['result','world'].includes(ch.target)||!validPointer(ch.path)||!own(ch,'value')){skip('unsupported check not checked here');continue;}
     if(references(ch.value)){skip('step-result reference not checked here');continue;}
     if(ch.target==='world'&&!same){skip('world not checked: different or unknown starting data');continue;}
     if(ch.target==='result'&&run.lossless!==true&&(ch.path==='/stdout'||ch.path.startsWith('/stdout/')||(ch.path===''&&own(ch.value,'stdout')))){skip('ledger stdout not checked: lossless result required');continue;}
     if((ch.target==='result'?run.result:run.world_after)===undefined){skip(`${ch.target} not checked: observation unavailable`);continue;}
     const actual=at(ch.target==='result'?run.result:run.world_after,ch.path);item.compared++;
     if(actual.missing||!isDeepStrictEqual(actual.value,ch.value)){const difference={target:ch.target,path:ch.path,expected:clone(ch.value),got:actual.missing||actual.value===undefined?null:clone(actual.value),...(actual.missing?{missing:true}:{})};item.first_difference??=difference;firstDifference??=difference;}
    }
    item.state=item.first_difference?(same?'fail':'differs'):item.compared?'pass':'tried';evidence.set(`${c.id}:${index}`,clone(item));items.push(item);
   }
  }
  const merged=criteria.flatMap(c=>{const rows=items.filter(i=>i.id===c.id);if(!rows.length)return[];const difference=rows.find(i=>i.first_difference)?.first_difference;return[{id:c.id,state:ranked(rows.map(i=>i.state)),compared:rows.reduce((n,i)=>n+i.compared,0),unchecked:[...new Set(rows.flatMap(i=>i.unchecked))],...(difference?{first_difference:difference}:{})}];});
  const verdict={state:ranked(merged.map(i=>i.state)),matched,start_matches:matched&&allStarts.every(Boolean),items:merged,...(firstDifference?{first_difference:firstDifference}:{}),...(matched?{step_id:exact[0].s.step_id}:{})};
  if(run.id!==undefined)history.set(run.id,clone(verdict));return clone(verdict);
 }
 return{record,snapshot,bindings};
}

export function compareExpectation(args={}) {
 const {expect,run,entry:bindingEntry,input,world_before}=args;
 const out={state:'not_compared',compared:0,unchecked:[]};
 const skip=reason=>{if(!out.unchecked.includes(reason))out.unchecked.push(reason);};
 if(!expect||!Array.isArray(expect.checks)){skip('no own expectation to compare');return out;}
 if(!run||typeof bindingEntry!=='string'||input===undefined||references(input)||run.entry!==bindingEntry||!isDeepStrictEqual(run.input,input)){skip('run does not match the delivered fill');return out;}
 const same=own(args,'world_before')&&world_before!==undefined&&own(run,'world_before')&&run.world_before!==undefined&&isDeepStrictEqual(world_before,run.world_before);
 for(const check of expect.checks){
  if(!check||!['result','world'].includes(check.target)||(own(check,'op')&&check.op!=='equals')||!validPointer(check.path)||!own(check,'value')){skip('unsupported expectation check not compared');continue;}
  if(references(check.value)){skip('step-result reference not compared');continue;}
  if(check.target==='world'&&!same){skip('world not compared: different or unknown fill starting data');continue;}
  if(check.target==='result'&&run.lossless!==true&&(check.path==='/stdout'||check.path.startsWith('/stdout/')||(check.path===''&&own(check.value,'stdout')))){skip('ledger stdout not checked: lossless result required');continue;}
  if((check.target==='result'?run.result:run.world_after)===undefined){skip(`${check.target} not compared: observation unavailable`);continue;}
  const actual=at(check.target==='result'?run.result:run.world_after,check.path);out.compared++;
  if(actual.missing||!isDeepStrictEqual(actual.value,check.value))out.first_difference??={target:check.target,path:check.path,expected:clone(check.value),got:actual.missing||actual.value===undefined?null:clone(actual.value),...(actual.missing?{missing:true}:{})};
 }
 out.state=out.first_difference?'differs':out.compared?'match':'not_compared';return clone(out);
}
