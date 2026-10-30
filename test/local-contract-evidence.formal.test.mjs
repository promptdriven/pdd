import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {spawnSync} from 'node:child_process';
import {tmpdir} from 'node:os';
import {dirname,join,resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
// Independent domain oracle frozen by Root BEFORE Code GO. Never executed during preparation.
// 155 command configurations *2 modes =310 invocations, plus24 schema equality invocations.
const root=resolve(process.env.PDD_FORMAL_TARGET??process.cwd());
const {runContracts}=await import(pathToFileURL(join(root,'src/contracts.mjs')));
const refs=await import(pathToFileURL(join(root,'src/contract-refs.mjs')));
const J=JSON.stringify, integer={type:'integer'};
let count=0,equalities=0;
const empty={type:'object',properties:{},required:[],additionalProperties:false};
const obj=(names,field={type:'string'})=>({type:'object',properties:Object.fromEntries(names.map(n=>[n,structuredClone(field)])),required:[...names],additionalProperties:false});
const md=entries=>entries.map(([name,schema])=>'### '+name+'\n```json\n'+J(schema)+'\n```\n').join('\n');
const iface=schemas=>'# Synthetic consumer\n<details><summary>Runtime interface</summary>\n```json\n'+J({status:'draft',prose_sha256:'',entries:schemas.map((input_schema,i)=>({operation:'act'+i,input_schema,result_schema:empty,errors:[]})),calls:[],resources:[],limits:{max_steps:1,max_model_calls:1},conventions:[]})+'\n```\n</details>\n';
const table=(column,rows)=>'# Synthetic world\n| '+column+' | Writer | What it holds | Schema |\n|---|---|---|---|\n'+rows.map(([key,writer,holds='',schema=''])=>'| '+key+' | '+writer+' | '+holds+' | '+schema+' |\n').join('');
const missing=keys=>({kind:'world-schema-missing',file:'contracts/world.md',world_keys:[...keys].sort()});
const disagreement=records=>({kind:'declared-record-disagreement',records:[...records].sort()});
const project=w=>Object.fromEntries(Object.entries(w).filter(([k])=>k!=='message'));
const sortWarnings=ws=>ws.map(project).sort((a,b)=>J(a).localeCompare(J(b)));
async function check(label,files,expected,{records,values=0,skips=[],warnings=[],problemFile,problemField}={}){
 count++;
 const cwd=fs.mkdtempSync(join(tmpdir(),'pdd-formal1438-'));
 try{
  for(const [path,text]of Object.entries(files)){fs.mkdirSync(dirname(join(cwd,path)),{recursive:true});fs.writeFileSync(join(cwd,path),text);}
  assert.equal(spawnSync('git',['init','-q'],{cwd}).status,0);
  assert.equal(spawnSync('git',['add','.'],{cwd}).status,0);
  let text='';
  for(const json of [false,true]){
   let stdout='',stderr='';
   const code=await runContracts({cwd,words:[],options:{'--check':true,...(json?{'--json':true}:{})}},{env:{...process.env,PDD_STATE_DIR:join(cwd,'.private-state')},stdout:{write:s=>{stdout+=s;}},stderr:{write:s=>{stderr+=s;}}});
   assert.equal(code,expected,label+' '+(json?'json':'text')+' '+stdout+stderr);
   if(!json){text=stdout+stderr;continue;}
   const got=JSON.parse(stdout);
   assert.deepEqual(Object.keys(got).sort(),['checked_records','checked_world_values','diagnostics','exit_code','skipped_files','warnings'],label);
   assert.equal(got.exit_code,expected,label);
   if(records!==undefined)assert.equal(got.checked_records,records,label+' records');
   assert.equal(got.checked_world_values,values,label+' values');
   assert.deepEqual(got.skipped_files,skips,label+' skipped');
   assert.deepEqual(sortWarnings(got.warnings),sortWarnings(warnings),label+' warning projections');
   for(const w of got.warnings){
    assert.equal(typeof w.message,'string',label);assert.ok(w.message.trim().length>0,label);
    if(w.kind==='world-schema-missing'){
     assert.deepEqual(w.world_keys,[...new Set(w.world_keys)].sort(),label);
     assert.ok(text.split('\n').some(line=>new RegExp('\\b'+w.world_keys.length+'\\b').test(line)&&/schema/i.test(line)),label+' semantic missing count');
    }else if(w.kind==='declared-record-disagreement'){
     assert.equal(w.records.length,2,label);assert.deepEqual(w.records,[...w.records].sort(),label);
     for(const record of w.records)assert.ok(text.includes(record),label+' warning record '+record);
    }
   }
   if(expected===0)assert.deepEqual(got.diagnostics,[],label);
   if(problemFile)assert.ok(got.diagnostics.some(d=>d.file===problemFile&&d.kind==='problem'&&(!problemField||d.field===problemField)),label+' expected problem '+J(got));
   const identities=new Set();
   for(const d of got.diagnostics){
    for(const k of ['file','record','field','kind','message'])assert.equal(typeof d[k],'string',label);
    const identity=J([d.file,d.record,d.field,d.kind,d.source_pointer,d.target,d.message]);
    assert.ok(!identities.has(identity),label+' duplicate diagnostic');identities.add(identity);
    assert.ok(text.includes(d.file),label+' text diagnostic file');
   }
  }
  for(const [path,bytes]of Object.entries(files))assert.equal(fs.readFileSync(join(cwd,path),'utf8'),bytes,label+' unchanged');
  assert.equal(fs.existsSync(join(cwd,'.private-state')),false,label+' no state writes');
 }finally{fs.rmSync(cwd,{recursive:true,force:true});}
}

test('1438 A:56 unique exact actors',async()=>{
 const cells=[['owner',0],['  owner  ',0],['owner,owner',0],['owner and owner',0],['owner/owner',0],['owner, second',4],['owner and second',4],['owner/second',4],['owner, second/owner',4],['owner and second, owner',4],['candy',0],['android',0],['',4],['   ',4]];
 for(const [cell,expected]of cells)for(const column of ['Key','Path'])for(const reverse of [false,true]){
  const rows=[['/items',cell],['/items',cell]];if(reverse)rows.reverse();
  await check(`A/${cell}/${column}/${reverse}`,{'contracts/world.md':table(column,rows),'contracts/seed-world.json':'{"items":0}'},expected,{records:0,warnings:[missing(['/items'])],...(expected?{problemFile:'contracts/world.md',problemField:'Writer'}:{})});
 }
});

test('1438 B:20 per-member and explicit-selection configurations',async()=>{
 const bad={type:'objekt'};
 const cases=[
 ['metadata-good',{description:'ordinary',leaf:integer},'/leaf',0,0,false],
 ['metadata-bad',{description:'ordinary',leaf:bad},'/leaf',4,4,false],
 ['empty-sibling',{empty:{},leaf:integer},'/leaf',0,0,false],
 ['nested',{note:'ordinary',box:{note:1,leaf:integer}},'/box/leaf',0,0,false],
 ['business',{business:{enum:[{properties:{literal:{$contract:'contracts/missing.json#'}}}],default:{properties:{literal:{$contract:'contracts/missing.json#'}}}},leaf:integer},'/leaf',0,0,false],
 ['resources',{resources:{leaf:integer}},'/resources/leaf',0,0,true],
 ['simulation',{simulation:{leaf:integer}},'/simulation/leaf',0,0,true],
 ['empty',{},'',0,4,true],
 ['typo',{tyep:'integer'},'',0,4,true],
 ['forbidden',{$ref:'x'},'',4,4,false],
 ];
 for(const [name,value,pointer,unselected,selected,skip]of cases)for(const choose of [false,true]){
  await check(`B/${name}/${choose}`,{'contracts/shapes.json':J(value),...(choose?{'prompts/select.prompt.md':iface([{$contract:'contracts/shapes.json#'+pointer}])}:{})},choose?selected:unselected,{skips:skip&&!choose?['contracts/shapes.json']:[],...((choose?selected:unselected)?{problemFile:'contracts/shapes.json'}:{})});
 }
});

test('1438 C:48 exact schema inference and explicit precedence',async()=>{
 const agent=obj(['id'],integer),other=obj(['other'],{type:'boolean'});
 const routes=[
 ['token','Path','/items','agent','',true],
 ['key-token','Key','agent','','',true],
 ['same-file-link','Path','/items','[agent](#agent)','',true],
 ['relative-link','Path','/items','[agent](shapes.md#agent)','',true],
 ['repeated','Path','/items','agent [agent](shapes.md#agent) agent','',true],
 ['explicit','Path','/items','other [other](shapes.md#other)','contracts/shapes.md#agent',true],
 ['unknown-link','Path','/items','[unknown](shapes.md#unknown)','',false],
 ['broken-link','Path','/items','[unknown](missing.md#unknown)','',false],
 ['ambiguous','Path','/items','`agent` and `other`','',false],
 ['plural','Path','/items','agents','',false],
 ['explicit-broken','Path','/items','','contracts/missing.md#agent','broken'],
 ['contract-broken','Path','/items','','contracts/broken.md#bad','broken'],
 ];
 for(const [name,column,key,holds,schema,chosen]of routes)for(const [state,value]of [['absent',undefined],['valid',{id:0}],['invalid',{id:false}],['array',[]]]){
  // Same-file link route declares agent in world.md itself, rather than assuming cross-file anchors.
  const same=name==='same-file-link';
  const world=table(column,[[key,'owner',holds,schema]])+(same?'\n'+md([['agent',agent]]):'');
  const files={'contracts/world.md':world,'contracts/seed-world.json':J(state==='absent'?{}:{[column==='Key'?'agent':'items']:value}),'contracts/shapes.md':md(same?[['other',other]]:[['agent',agent],['other',other]])};
  if(name==='contract-broken')files['contracts/broken.md']=md([['bad',{$contract:'contracts/missing.md#agent'}]]);
  const expected=chosen==='broken'?4:chosen&&['invalid','array'].includes(state)?4:0;
  await check(`C/${name}/${state}`,files,expected,{values:chosen===true&&state!=='absent'?1:0,warnings:chosen===false?[missing(['/items'])]:[],...(chosen===true&&expected?{problemFile:'contracts/seed-world.json'}:{})});
 }
});

test('1438 C supplemental:2 recognized-member row selections',async()=>{
 for(const holds of ['order','[order](shapes.json#/order)'])await check('C-member/'+holds,{'contracts/world.md':table('Path',[['/item','owner',holds]]),'contracts/seed-world.json':'{"item":0}','contracts/shapes.json':J({description:'metadata',order:integer})},0,{records:1,values:1});
});

test('1438 C conservative designation:2 prose/path negative witnesses',async()=>{
 const work=obj(['id'],integer);
 for(const [path,holds,seed]of [
  ['/wire/notices','Run events: work resumed',{wire:{notices:[]}}],
  ['/wire/work','Work items',{wire:{work:[]}}],
 ])await check('C-negative/'+path,{'contracts/world.md':table('Path',[[path,'owner',holds]]),'contracts/seed-world.json':J(seed),'contracts/shapes.md':md([['work',work]])},0,{records:1,values:0,warnings:[missing([path])]});
});

test('1438 D:8 exact namespace and top-level coverage configurations',async()=>{
 const cases=[
 ['bare','Key',[['items','owner']],{items:0},0,['/items']],
 ['descendant','Key',[['/kv/shop','owner']],{kv:{shop:0}},0,['/kv/shop']],
 ['siblings','Key',[['/kv/shop','owner'],['/kv/other','second']],{kv:{shop:0,other:1}},0,['/kv/shop','/kv/other']],
 ['parent','Key',[['/kv/shop','owner'],['/kv','second']],{kv:{shop:0}},0,['/kv/shop','/kv']],
 ['extra','Key',[['/kv/shop','owner']],{kv:{shop:0},outside:0},4,['/kv/shop']],
 ['path-extra','Path',[['/kv/shop','owner']],{kv:{shop:0},outside:0},0,['/kv/shop']],
 ['escaped','Key',[['/a~1b','owner']],{'a/b':0},0,['/a~1b']],
 ['symbolic','Key',[['/hosts/<machine_id>','owner']],{},0,['/hosts/<machine_id>']],
 ];
 for(const [name,column,rows,seed,exit,keys]of cases)await check('D/'+name,{'contracts/world.md':table(column,rows),'contracts/seed-world.json':J(seed)},exit,{records:0,warnings:[missing(keys)]});
});

test('1438 E:19 declared-pair disagreement and independent consumer drift configurations',async()=>{
 for(const n of [1,2,4])for(const variant of ['equal','type','literal'])for(const reverse of [false,true]){
  const names=['a','b','c','d'].slice(0,n),a=obj(names,{type:'array',items:{type:'string'},default:['x','y']}),b=structuredClone(a);
  if(variant==='equal')b.properties=Object.fromEntries(Object.entries(b.properties).reverse());
  if(variant==='type')b.properties.a={type:'string',default:'x'};
  if(variant==='literal')b.properties.a.default=['y','x'];
  const entries=[['A',a],['B',b]];if(reverse)entries.reverse();
  await check(`E/${n}/${variant}/${reverse}`,{'contracts/pair.md':md(entries)},0,{records:2,warnings:variant==='equal'?[]:[disagreement(['contracts/pair.md#A','contracts/pair.md#B'])]});
 }
 const a=obj(['a','b','c','d']),b=structuredClone(a);b.properties.a={type:'boolean'};
 await check('E/coexist',{'contracts/pair.md':md([['A',a],['B',b],['C',obj(['w','x','y','z'])]]),'prompts/copy.prompt.md':iface([obj(['w','x','y'])])},4,{records:3,warnings:[disagreement(['contracts/pair.md#A','contracts/pair.md#B'])],problemFile:'prompts/copy.prompt.md'});
});

test('1438 F:24 direct read-only lossless schema equalities',()=>{
 const pairs=[
 ['{"type":"object","properties":{"a":{"type":"string"},"b":{"type":"integer"}}}','{"properties":{"b":{"type":"integer"},"a":{"type":"string"}},"type":"object"}',true],
 ['{"type":"string","title":"a","description":"a"}','{"type":"string","title":"b","description":"b"}',true],
 ['{"required":["a","b"]}','{"required":["b","a"]}',true],
 ['{"enum":[1,2]}','{"enum":[2,1]}',true],
 ['{"const":1}','{"const":1.0}',true],
 ['{"const":0}','{"const":-0}',true],
 [J(obj(['one'])),J(obj(['one'])),true],
 ['{"properties":{"a":{"type":"integer"}}}','{"properties":{"a":{"type":"boolean"}}}',false],
 ['{"required":["a","a"]}','{"required":["a"]}',false],
 ['{"const":[1,2]}','{"const":[2,1]}',false],
 ['{"enum":[[1,2]]}','{"enum":[[2,1]]}',false],
 ['{"const":9007199254740992}','{"const":9007199254740993}',false],
 ];
 for(const [a,b,expected]of pairs)for(const reversed of [false,true]){
  const left=refs.parseJsonValue(reversed?b:a),right=refs.parseJsonValue(reversed?a:b);
  const before=[refs.stringifyJsonValue(left),refs.stringifyJsonValue(right)];
  assert.equal(refs.schemaValuesEqual(left,right),expected,`F/${a}/${b}/${reversed}`);equalities++;
  assert.deepEqual([refs.stringifyJsonValue(left),refs.stringifyJsonValue(right)],before,'read-only trees');
 }
});

test('1438 fixed inventory',()=>{assert.equal(count,155);assert.equal(equalities,24);});
