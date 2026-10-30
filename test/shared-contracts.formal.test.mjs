import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { expandSource, catalogRecords, compareCopies, planSync } from '../src/contract-refs.mjs';
import { captureSource, interfaceBlocks } from '../src/runtime-preflight.mjs';
import { readContractHistory } from '../src/runtime-client.mjs';
import { runContracts } from '../src/contracts.mjs';
import { harbor, PLACE, sink } from './runtime-fake.mjs';

// Bounded Story oracles, not Runtime replays. The domains below are exhaustive;
// native capture/history use temporary Git/state files, never a live service.
const path = 'prompts/bounded.prompt.md';
const schema = (mask, type = 'string') => ({ type:'object', properties:Object.fromEntries(
  ['a','b','c','d','e'].flatMap((name, bit) => mask & (1 << bit) ? [[name,{type}]] : [])), required:[], additionalProperties:false });
const prompt = (input, extra = {}) => `# Unchanged prose\r\n\r\n<details><summary>Runtime interface</summary>\n\n\x60\x60\x60json\n${JSON.stringify({status:'approved',prose_sha256:'unchanged-hash',entries:[{operation:'act',input_schema:input,...extra}],calls:[],resources:[]})}\n\x60\x60\x60\n</details>\nUnchanged tail.\n`;
const body = text => JSON.parse(interfaceBlocks(text)[0][1]);
const port = sources => ({
  stat: ({path}) => ({exists:Object.hasOwn(sources,path),is_symlink:false,size:Buffer.byteLength(sources[path] ?? '')}),
  read: ({path}) => ({content:sources[path]}),
});
const expand = (text, format, sources) => expandSource({path,text,format},port(sources));
const write = (root, name, value) => { mkdirSync(join(root,name,'..'),{recursive:true}); writeFileSync(join(root,name),typeof value==='string'?value:JSON.stringify(value)); };
const popcount = n => [1,2,4,8,16].filter(bit => n & bit).length;

test('FORMAL shared-records: all 125 three-record successor graphs from all three roots', () => {
  // Each record terminates, references one of three records, or is missing.
  // Reachability and repeated-node detection define the Story's refusal oracle.
  for (let a=0;a<5;a++) for (let b=0;b<5;b++) for (let c=0;c<5;c++) {
    const next=[a,b,c], sources=Object.fromEntries(next.map((to,i)=>[
      `contracts/${i}.json`,JSON.stringify(to===3?{type:'string',default:0}:{$contract:`contracts/${to}.json#`}),
    ]));
    for(let start=0;start<3;start++) {
      const visited=new Set(); let at=start, error;
      while(at!==3) {
        if(at===4) {error='contract-missing';break;}
        if(visited.has(at)) {error='contract-cycle';break;}
        visited.add(at);at=next[at];
      }
      const invoke=()=>expand(JSON.stringify({$contract:`contracts/${start}.json#`}), 'json-schema',sources);
      const label=JSON.stringify({next,start});
      if(error) assert.throws(invoke,e=>e.code===error,label);
      else {
        const got=invoke();assert.deepEqual(JSON.parse(got.text),{type:'string',default:0},label);
        assert.deepEqual(got.references.map(ref=>ref.target),[...visited].sort().map(i=>`contracts/${i}.json#`),label);
        for(const ref of got.references) assert.equal(ref.value_json,'{"default":0,"type":"string"}',label);
      }
    }
  }
});

test('FORMAL shared-records: schema slots expand; six literal containers and local annotations stay literal', () => {
  const target='contracts/value.json#', sources={'contracts/value.json':'{"type":"string","title":"shared","default":9007199254740993}'};
  const reference={$contract:target,title:'local',description:'kept'};
  for(const child of ['root','properties','items','oneOf']) for(const literal of ['default','examples','enum','const','input','checks']) {
    const wrapped=child==='root'?reference:child==='properties'?{type:'object',properties:{x:reference}}:child==='items'?{type:'array',items:reference}:{oneOf:[reference]};
    const iface={entries:[{input_schema:wrapped,result_schema:wrapped}],resources:[{operations:[{arguments_schema:wrapped,result_schema:wrapped}]}]};
    // Literal annotations are inside schemas; business inputs/checks are outside.
    for(const entry of iface.entries) entry[literal]={$contract:'contracts/missing.json#'};
    if(['default','examples','enum','const'].includes(literal)) {
      const value=literal==='examples'||literal==='enum'?[{$contract:'contracts/missing.json#'}]:{$contract:'contracts/missing.json#'};
      iface.entries[0].input_schema={type:'object',properties:{x:reference},[literal]:value};
    }
    const text=`<details><summary>Runtime interface</summary>\n\x60\x60\x60json\n${JSON.stringify(iface)}\n\x60\x60\x60\n</details>`;
    const got=expand(text,'prompt',sources), parsed=body(got.text);
    assert.equal(got.references.length,4,`${child}/${literal}`);
    assert.deepEqual(parsed.entries[0][literal],{$contract:'contracts/missing.json#'});
    assert.equal((got.text.match(/9007199254740993/g)??[]).length,4);
    assert.equal((got.text.match(/"title":"local"/g)??[]).length,4);
    assert.deepEqual(parsed.entries[0].input_schema[literal],iface.entries[0].input_schema[literal]);
  }
  for(const key of ['minimum','required','properties','$ref']) assert.throws(
    ()=>expand(JSON.stringify({...reference,[key]:0}),'json-schema',sources),e=>e.code==='contract-invalid');
  const untouched=' { "type":"string", "default":{"$contract":"missing.json#"}, "$ref":"literal" }\n';
  assert.deepEqual(expand(untouched,'json-schema',sources),{text:untouched,references:[]});
});

test('FORMAL shared-records: heading aliases, ambiguity and escaped own JSON Pointer members', () => {
  for(const [title,fragment] of [['Sign in','sign-in'],['Sign_in input','sign_in-input'],['A / B','a-b'],['Ångström value','ångström-value']]) {
    const record=heading=>`### ${heading}\n\x60\x60\x60json\n{"type":"string"}\n\x60\x60\x60\n`;
    const sources={'contracts/headings.md':record(title)};
    for(const selected of new Set([title,fragment])) {
      const got=expand(JSON.stringify({$contract:`contracts/headings.md#${selected}`}),'json-schema',sources);
      assert.equal(got.references[0].target,`contracts/headings.md#${title}`);
      sources['contracts/headings.md']=record(title)+record(title);
      assert.throws(()=>expand(JSON.stringify({$contract:`contracts/headings.md#${selected}`}),'json-schema',sources),e=>e.code==='contract-ambiguous');
      sources['contracts/headings.md']=record(title);
    }
    sources['contracts/headings.md']=record(title)+record(fragment);
    assert.throws(()=>expand(JSON.stringify({$contract:`contracts/headings.md#${fragment}`}),'json-schema',sources),e=>e.code==='contract-ambiguous');
  }
  const sources={'contracts/keys.json':'{"__proto__":{"type":"string"},"constructor":{"type":"boolean"},"a/b":{"~":[{"type":"null"}]}}'};
  for(const [pointer,type] of [['/__proto__','string'],['/constructor','boolean'],['/a~1b/~0/0','null']]) {
    assert.deepEqual(JSON.parse(expand(JSON.stringify({$contract:`contracts/keys.json#${pointer}`}),'json-schema',sources).text),{type});
  }
  for(const pointer of ['/toString','/a~1b/~0/1','/a~1b/~0/01']) assert.throws(
    ()=>expand(JSON.stringify({$contract:`contracts/keys.json#${pointer}`}),'json-schema',sources),e=>e.code==='contract-missing');
});

test('FORMAL shared-seed: all 36 replacement pairs, both overlap orders and disjoint permutations', () => {
  const values=[0,false,null,[],{},''], seed='{"branch":{"x":1},"other":2,"array":[1,2]}';
  const sources={'contracts/world.json':seed};
  const run=set=>expand(JSON.stringify({initial_world:{$seed:'contracts/world.json',set},steps:[{input:{$seed:'literal'},checks:[{value:{$contract:'literal'}}]}]}),'scenario',sources);
  for(const x of values) for(const y of values) {
    for(const parentFirst of [true,false]) {
      const entries=parentFirst?[['/branch',{x}],['/branch/x',y]]:[['/branch/x',y],['/branch',{x}]];
      const got=JSON.parse(run(Object.fromEntries(entries)).text);
      assert.deepEqual(got.initial_world,{branch:{x:parentFirst?y:x},other:2,array:[1,2]});
      assert.deepEqual(got.steps,[{input:{$seed:'literal'},checks:[{value:{$contract:'literal'}}]}]);
      const root=parentFirst?[['',{branch:{x}}],['/branch/x',y]]:[['/branch/x',y],['',{branch:{x}}]];
      assert.deepEqual(JSON.parse(run(Object.fromEntries(root)).text).initial_world,{branch:{x:parentFirst?y:x}});
    }
    const first=run({'/branch/x':x,'/other':y}), second=run({'/other':y,'/branch/x':x});
    assert.equal(first.text,second.text);assert.deepEqual(first.references,second.references);
    assert.deepEqual(JSON.parse(run({'/array/0':x,'/added':y}).text).initial_world,{branch:{x:1},other:2,array:[x,2],added:y});
    assert.equal(sources['contracts/world.json'],seed);
    assert.deepEqual(JSON.parse(run({}).text).initial_world,JSON.parse(seed));
  }
});

test('FORMAL shared-seed: own escaped names, exact number tokens, invalid parents and indices', () => {
  const seed='{"__proto__":{"x":0},"constructor":{"x":0},"a/b":{"~":0},"array":[0,0],"n":9007199254740993}';
  const sources={'contracts/world.json':seed};
  const before=Object.getOwnPropertyDescriptors(Object.prototype);
  for(const pointer of ['/__proto__/x','/constructor/x','/a~1b/~0','/array/0','/array/1','/new']) {
    const text=`{"initial_world":{"$seed":"contracts/world.json","set":{${JSON.stringify(pointer)}:9007199254740993}},"expected":9007199254740993}`;
    const got=expand(text,'scenario',sources);
    assert.equal((got.text.match(/9007199254740993/g)??[]).length,3,pointer);
    assert.equal(got.references[0].target,'contracts/world.json#');
    assert.match(got.references[0].value_json,/"n":9007199254740993/);
  }
  for(const pointer of ['/missing/x','/toString/x','/array/2','/array/-','/array/01','/array/-1','/a~2b','not-pointer']) {
    assert.throws(()=>expand(JSON.stringify({initial_world:{$seed:'contracts/world.json',set:{[pointer]:0}}}),'scenario',sources),e=>e.code==='seed-invalid',pointer);
  }
  for(const value of [0,false,null,[], '']) assert.throws(
    ()=>expand(JSON.stringify({initial_world:{$seed:'contracts/world.json',set:{'':value}}}),'scenario',sources),e=>e.code==='seed-invalid');
  assert.deepEqual(Object.getOwnPropertyDescriptors(Object.prototype),before);
  assert.equal(sources['contracts/world.json'],seed);
});

test('FORMAL shared-contract-drift: all 4096 field-set/type pairs and 121 numeric token pairs', () => {
  for(let copyMask=0;copyMask<32;copyMask++) for(let recordMask=0;recordMask<32;recordMask++) for(const copyType of ['string','boolean']) for(const recordType of ['string','boolean']) {
    const inline={...schema(copyMask,copyType),title:'local',description:'local'}, canonical=schema(recordMask,recordType);
    const records=catalogRecords([{path:'contracts/value.json',text:JSON.stringify(canonical)}]);
    const got=compareCopies([{path,text:prompt(inline)}],records.records), distance=popcount(copyMask^recordMask);
    const exact=copyMask===recordMask && (copyMask===0 || copyType===recordType);
    const eligible=popcount(copyMask)>=3 && (exact || popcount(recordMask)>=4 && distance<=1);
    assert.equal(got.matches.length,eligible?1:0,JSON.stringify({copyMask,recordMask,copyType,recordType}));
    assert.equal(got.warnings.length,0);
    if(eligible) {
      assert.equal(got.matches[0].kind,exact?'exact':'near');
      assert.equal(got.matches[0].differences.length===0,exact);
      for(let bit=0;bit<5;bit++) if((copyMask^recordMask)&(1<<bit) || (copyMask&recordMask&(1<<bit)) && copyType!==recordType)
        assert.ok(got.matches[0].differences.some(d=>d.includes(`/properties/${['a','b','c','d','e'][bit]}`)));
    }
  }
  // Expected equivalence classes are declared independently of binary64 parsing.
  const tokens=[['0',0],['-0',0],['0.0',0],['0e0',0],['1',1],['1.0',1],['1e0',1],['10e-1',1],['2',2],['9007199254740992',3],['9007199254740993',4]];
  for(const [left,a] of tokens) for(const [right,b] of tokens) {
    const text=token=>`{"type":"object","properties":{"a":{"type":"number","minimum":${token}},"name":{"type":"string"},"kind":{"type":"string"},"active":{"type":"boolean"}},"required":[],"additionalProperties":false}`;
    const records=catalogRecords([{path:'contracts/value.json',text:text(right)}]);
    const source=prompt(schema(1)).replace(JSON.stringify(schema(1)),text(left));
    const got=compareCopies([{path,text:source}],records.records);
    assert.equal(got.matches[0].kind,a===b?'exact':'near',`${left} versus ${right}`);
  }
});

test('FORMAL shared-contract-sync: all 32768 two-candidate field sets, ambiguity and second-plan idempotence', () => {
  for(let copy=0;copy<32;copy++) for(let a=0;a<32;a++) for(let b=0;b<32;b++) {
    const source={path,text:prompt({...schema(copy),title:'local',description:'keep'})};
    const records=catalogRecords([{path:'contracts/a.json',text:JSON.stringify(schema(a))},{path:'contracts/b.json',text:JSON.stringify(schema(b))}]).records;
    const exact=[a,b].flatMap((mask,i)=>popcount(copy)>=3 && mask===copy?[i]:[]), near=[a,b].flatMap((mask,i)=>popcount(copy)>=3 && popcount(mask)>=4 && popcount(mask^copy)<=1?[i]:[]);
    const candidates=exact.length?exact:near, got=compareCopies([source],records), plan=planSync([source],got.matches);
    assert.equal(got.matches.length,candidates.length===1?1:0);
    assert.equal(got.warnings.length,candidates.length>1?1:0);
    assert.equal(plan.edits.length,candidates.length===1?1:0);
    if(candidates.length!==1) continue;
    const edit=plan.edits[0], parsed=body(edit.after), target=`contracts/${candidates[0]===0?'a':'b'}.json#`;
    assert.equal(edit.before,source.text);
    assert.deepEqual(parsed.entries[0].input_schema,{$contract:target,title:'local',description:'keep'});
    assert.equal(parsed.status,'draft');assert.equal(parsed.prose_sha256,'unchanged-hash');
    const block=interfaceBlocks(source.text)[0], afterBlock=interfaceBlocks(edit.after)[0];
    assert.equal(edit.after.slice(0,afterBlock.indices[1][0]),source.text.slice(0,block.indices[1][0]));
    assert.equal(edit.after.slice(afterBlock.indices[1][1]),source.text.slice(block.indices[1][1]));
    const migrated={path,text:edit.after};
    assert.deepEqual(planSync([migrated],compareCopies([migrated],records).matches).edits,[]);
    const supplied=Object.fromEntries(records.map(record=>[record.path,record.value_json]));
    assert.deepEqual(body(expand(edit.after,'prompt',supplied).text).entries[0].input_schema,{...schema(candidates[0]===0?a:b),title:'local',description:'keep'});
  }
});

const STORY='user_stories/place-order.md', OTHER_STORY='user_stories/unknown-item.md';
const ids=['00000000-0000-0000-0000-000000000001','00000000-0000-0000-0000-000000000002'];
function savedCheck(setup, index, {state='passed',time=0,evaluated=true,command='check',intent='check',snapshot}={}) {
  const folder=join(setup.state,'batches',`20261030-000000-000${index}`), id=ids[index];
  mkdirSync(folder,{recursive:true});
  write(folder,'batch.json',{root:setup.repo,intent,rows:[{test:'tests/place-order.json',story:'place-order',story_path:STORY,request_ids:[id]}],...(snapshot?{contract_snapshots:[{...snapshot,tests:['tests/place-order.json']}]}:{})});
  write(folder,`${id}.json`,{id,requestId:id,command,state,created_at:new Date(1_800_000_000_000+time*1000).toISOString(),result:{report:{samples:[{steps:[{checks:evaluated?[{passed:state==='passed'}]:[]}]}]}}});
}

test('FORMAL shared-contract-status: all 192 history pairs, latest evaluated Check and failed ties', t => {
  const setup=harbor(t), env={HOME:setup.home,PDD_STATE_DIR:setup.state};
  const kinds=[{state:'passed'},{state:'failed'},{state:'running'},{state:'refused'},{state:'unknown'},{state:'passed',evaluated:false},{state:'passed',intent:'lint-only'},{state:'passed',legacy:true}];
  for(let a=0;a<kinds.length;a++) for(let b=0;b<kinds.length;b++) for(const delta of [-1,0,1]) {
    const rows=[{...kinds[a],time:0},{...kinds[b],time:delta}];
    rows.forEach((row,i)=>savedCheck(setup,i,{...row,snapshot:row.legacy?undefined:{story_path:STORY,files:[{path:'witness',sha256:String(i)}],references:[]}}));
    const eligible=rows.map((row,i)=>({...row,i})).filter(row=>['passed','failed'].includes(row.state)&&row.evaluated!==false&&row.intent!=='lint-only');
    const got=readContractHistory({root:setup.repo,env});assert.deepEqual(got.warnings,[]);
    const value=got.stories.find(story=>story.story_path===STORY), label=JSON.stringify({a,b,delta});
    if(!eligible.length) assert.equal(value.baseline,'not-checked',label);
    else {
      const latest=Math.max(...eligible.map(row=>row.time)), atTime=eligible.filter(row=>row.time===latest);
      const result=atTime.some(row=>row.state==='failed')?'failed':'passed', winners=atTime.filter(row=>row.state===result);
      assert.equal(value.result_state,result,label);
      assert.equal(value.checked_at,new Date(1_800_000_000_000+latest*1000).toISOString(),label);
      assert.ok(winners.some(row=>row.legacy?value.baseline==='unavailable':value.baseline==='checked'&&value.files[0].sha256===String(row.i)),label);
    }
    assert.deepEqual(readContractHistory({root:setup.repo,env}),got,'equal choices must be deterministic');
  }
});

test('FORMAL shared-contract-status: all four independent same-file record changes and transitive footprints', t => {
  const setup=harbor(t), env={HOME:setup.home,PDD_STATE_DIR:setup.state};
  const original=readFileSync(join(setup.repo,PLACE),'utf8');
  const changePrompt=(text,target)=>{
    const block=interfaceBlocks(text)[0], value=JSON.parse(block[1]);value.entries[0].input_schema={$contract:target};
    return text.slice(0,block.indices[1][0])+JSON.stringify(value)+text.slice(block.indices[1][1]);
  };
  write(setup.repo,PLACE,changePrompt(original,'contracts/both.json#/a'));
  write(setup.repo,'prompts/other.prompt.md',changePrompt(original,'contracts/both.json#/b'));
  const other=JSON.parse(readFileSync(join(setup.repo,'tests/unknown-item.json'),'utf8'));
  for(const step of other.steps)step.entry_path='prompts/other.prompt.md';write(setup.repo,'tests/unknown-item.json',other);
  const contracts=(a,b)=>write(setup.repo,'contracts/both.json',{a:{$contract:'contracts/both.json#/leaf'},leaf:{...schema(1),description:`a${a}`},b:{...schema(2),description:`b${b}`}});
  contracts(0,0);const baseline=captureSource(setup.repo);
  const snapshot=baseline.stories.find(story=>story.story_path===STORY);
  savedCheck(setup,0,{snapshot});
  const folder=join(setup.state,'batches','20261030-000000-0000'), batch=JSON.parse(readFileSync(join(folder,'batch.json'),'utf8'));
  batch.rows.push({test:'tests/unknown-item.json',story:'unknown-item',story_path:OTHER_STORY,request_ids:[ids[0]]});
  batch.contract_snapshots.push({...baseline.stories.find(story=>story.story_path===OTHER_STORY),tests:['tests/unknown-item.json']});write(folder,'batch.json',batch);
  for(const a of [0,1]) for(const b of [0,1]) {
    contracts(a,b);const current=captureSource(setup.repo);
    for(const [story,changed] of [[STORY,a],[OTHER_STORY,b]]) {
      const before=baseline.stories.find(row=>row.story_path===story), after=current.stories.find(row=>row.story_path===story);
      assert.equal(JSON.stringify(before)===JSON.stringify(after),!changed,`${story}, a=${a}, b=${b}`);
    }
    assert.deepEqual(current.stories.find(row=>row.story_path===STORY).references.map(ref=>ref.target),['contracts/both.json#/a','contracts/both.json#/leaf']);
    assert.equal(current.files.some(file=>file.path==='contracts/both.json'),false);
    const stdout=sink(),stderr=sink();assert.equal(runContracts({cwd:setup.repo},{env,stdout,stderr}),0,stderr.text);
    for(const [story,changed] of [[STORY,a],[OTHER_STORY,b]]) assert.ok(stdout.text.includes(`${story}: ${changed?'stale: needs a new check':'current'}`),stdout.text);
  }
});

test('FORMAL shared-contract-drift: all 36 required/enum permutations retain multiplicities and nested literal order',()=>{
  const permutations=values=>values.length?values.flatMap((value,i)=>permutations(values.filter((_,j)=>j!==i)).map(rest=>[value,...rest])):[[]];
  const canonical=schema(31);canonical.required=['a','b','a'];
  canonical.properties.a={type:'array',items:{type:'number'},enum:[[1,2],[3,4],[1,2]]};
  const records=[{path:'contracts/value.json',target:'contracts/value.json#',value_json:JSON.stringify(canonical)}];
  for(const required of permutations(canonical.required)) for(const alternatives of permutations(canonical.properties.a.enum)) {
    const copy=structuredClone(canonical);copy.required=required;copy.properties.a.enum=alternatives;
    assert.equal(compareCopies([{path,text:prompt(copy)}],records).matches[0].kind,'exact');
    copy.required=['a','b','b'];
    assert.equal(compareCopies([{path,text:prompt(copy)}],records).matches[0].kind,'near');
    copy.required=required;copy.properties.a.enum=[[2,1],[3,4],[1,2]];
    assert.equal(compareCopies([{path,text:prompt(copy)}],records).matches[0].kind,'near');
  }
  for(const keyword of ['default','examples','const']) for(const values of permutations(['a','b','c'])) {
    const reference=schema(31),copy=schema(31);
    reference.properties.a[keyword]={required:['a','b','c'],enum:[1,2]};
    copy.properties.a[keyword]={required:values,enum:[1,2]};
    const literalRecords=[{path:'contracts/value.json',target:'contracts/value.json#',value_json:JSON.stringify(reference)}];
    assert.equal(compareCopies([{path,text:prompt(copy)}],literalRecords).matches[0].kind,values.join('')==='abc'?'exact':'near');
  }
});
