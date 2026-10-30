import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {spawnSync} from 'node:child_process';
import {tmpdir} from 'node:os';
import {dirname,join,resolve} from 'node:path';
import {pathToFileURL} from 'node:url';

// Independent requirements oracle frozen by Root before Code GO.
// Native execution targets this checkout; an explicit alternate checkout supports isolated controls.
// 138 finite configurations, each text+JSON =276 invocations; five syntax controls.
const root=resolve(process.env.PDD_FORMAL_TARGET ?? process.cwd());
const {runContracts}=await import(pathToFileURL(join(root,'src/contracts.mjs')));
const {runPdd}=await import(pathToFileURL(join(root,'src/pdd-cli.mjs')));
const J=JSON.stringify;
const integer={type:'integer'};
const record=schema=>'### Shape\n```json\n'+J(schema)+'\n```\n';
const iface=schemas=>'# Synthetic formal consumer\n<details><summary>Runtime interface</summary>\n```json\n'+J({status:'draft',prose_sha256:'',entries:schemas.map((input_schema,i)=>({operation:'act'+i,input_schema,result_schema:{type:'object',properties:{},required:[],additionalProperties:false},errors:[]})),calls:[],resources:[],limits:{max_steps:1,max_model_calls:1},conventions:[]})+'\n```\n</details>\n';
const table=(column,rows,layout='blank')=>'# Synthetic world\n| '+column+' | Writer |'+(layout==='absent'?'':' Schema |')+'\n|---|---|'+(layout==='absent'?'':'---|')+'\n'+rows.map(([path,writer,target=''])=>'| '+path+' | '+writer+' |'+(layout==='absent'?'':' '+target+' |')+'\n').join('');
let configurations=0;
async function check(label,files,expected,{worldValues,records,skips,problemFile,problemField}={}) {
  configurations++;
  const cwd=fs.mkdtempSync(join(tmpdir(),'pdd-followup-formal-'));
  try {
    for(const [path,text] of Object.entries(files)) {fs.mkdirSync(dirname(join(cwd,path)),{recursive:true});fs.writeFileSync(join(cwd,path),text);}
    assert.equal(spawnSync('git',['init','-q'],{cwd}).status,0);
    assert.equal(spawnSync('git',['add','.'],{cwd}).status,0);
    const invoke=async json=>{
      let stdout='',stderr='';
      const code=await runContracts({cwd,words:[],options:{'--check':true,...(json?{'--json':true}:{})}},{env:{...process.env,PDD_STATE_DIR:join(cwd,'.private-state')},stdout:{write:s=>{stdout+=s;}},stderr:{write:s=>{stderr+=s;}}});
      assert.equal(code,expected,label+' '+stdout+stderr);
      return {code,stdout,stderr};
    };
    const text=await invoke(false),json=await invoke(true);
    const got=JSON.parse(json.stdout);
    assert.deepEqual(Object.keys(got).sort(),['checked_records','checked_world_values','diagnostics','exit_code','skipped_files','warnings']);
    assert.equal(got.exit_code,expected,label);
    assert.ok(Number.isInteger(got.checked_records)&&got.checked_records>=0,label);
    assert.ok(Number.isInteger(got.checked_world_values)&&got.checked_world_values>=0,label);
    if(records!==undefined)assert.equal(got.checked_records,records,label);
    if(worldValues!==undefined)assert.equal(got.checked_world_values,worldValues,label);
    if(skips!==undefined)assert.deepEqual(got.skipped_files,skips,label);
    assert.deepEqual(got.skipped_files,[...got.skipped_files].sort(),label);
    if(expected===0)assert.deepEqual(got.diagnostics,[],label);
    if(problemFile)assert.ok(got.diagnostics.some(d=>d.file===problemFile&&d.kind==='problem'&&(!problemField||d.field===problemField)),label+' '+J(got));
    const identities=new Set();
    for(const d of got.diagnostics) {
      for(const key of ['file','record','field','kind','message'])assert.equal(typeof d[key],'string',label);
      assert.ok(d.message.length>0,label);
      const key=J([d.file,d.record,d.field,d.kind,d.source_pointer,d.target]);
      assert.ok(!identities.has(key),label+' duplicate diagnostic '+key);identities.add(key);
      assert.ok((text.stdout+text.stderr).includes(d.file),label+' text diagnostic file');
      assert.ok((text.stdout+text.stderr).includes(d.field),label+' text diagnostic field');
      for(const key of ['source_pointer','target'])if(d[key])assert.ok((text.stdout+text.stderr).includes(d[key]),label+' text provenance '+key);
    }
    for(const [path,bytes] of Object.entries(files))assert.equal(fs.readFileSync(join(cwd,path),'utf8'),bytes,label+' source unchanged');
    assert.equal(fs.existsSync(join(cwd,'.private-state')),false,label+' no history/state writes');
    return got;
  } finally {fs.rmSync(cwd,{recursive:true,force:true});}
}

test('followup formal A:24 exact ownership cases and2 fixed literal/template witnesses',async()=>{
 const sets=[[[['`/a`','owner']],0],[[['`/a`','owner'],['`/a`','owner']],0],[[['`/a`','owner'],['`/a`','second']],4],[[['`/a`','parent'],['`/a/b`','child']],0],[[['`/a`, `/b`','owner'],['`/b`','second']],4],[[['`/a`','owner, second']],4]];
 for(let i=0;i<sets.length;i++)for(const reversed of [false,true])for(const layout of ['absent','blank']) {
  const [rows,expected]=sets[i];
  await check(`A/${i}/${reversed}/${layout}`,{'contracts/world.md':table('Path',reversed?[...rows].reverse():rows,layout),'contracts/seed-world.json':'{"unrelated":0}'},expected,{records:0,worldValues:0,skips:[],...(expected?{problemFile:'contracts/world.md',problemField:'Writer'}:{})});
 }
 for(const path of ['`/hosts/<machine_id>`','`/a,b`'])await check('A/witness/'+path,{'contracts/world.md':table('Path',[[path,'owner, second']],'absent'),'contracts/seed-world.json':'{"unrelated":0}'},4,{records:0,worldValues:0,skips:[]});
});

test('followup formal B:48 optional schema and value-presence cases',async()=>{
 const values=[['absent',undefined],['null',null],['false',false],['zero',0],['array',[]],['object',{}]];
 for(const state of ['absent','blank','integer','invalid'])for(const [name,value]of values)for(const column of ['Key','Path']) {
  const present=name!=='absent',selected=state==='integer'||state==='invalid';
  const schema=state==='invalid'?{type:'array'}:integer;
  const seed=column==='Key'?(present?{item:value}:{}):{unrelated:1,branch:present?{item:value}:{}};
  const expected=state==='invalid'||state==='integer'&&present&&name!=='zero'?4:0;
  await check(`B/${state}/${name}/${column}`,{'contracts/world.md':table(column,[[column==='Key'?'item':'`/branch/item`','owner',selected?'contracts/shapes.md#Shape':'']],state==='absent'?'absent':'blank'),'contracts/seed-world.json':J(seed),...(selected?{'contracts/shapes.md':record(schema)}:{})},expected,{records:selected?1:0,worldValues:state==='integer'&&present?1:0,skips:[],...(state==='invalid'?{problemFile:'contracts/shapes.md'}:expected?{problemFile:'contracts/seed-world.json'}:{})});
 }
});

const roles=[
 ['root',integer,'',false,true],['invalid',{type:'array'},'',false,false],
 ['pure',{defs:{leaf:integer}},'/defs/leaf',false,true],
 ['metadata',{note:'business',leaf:integer},'/leaf',false,true],
 ['empty',{empty:{},leaf:integer},'/leaf',false,true],
 ['resources',{resources:{leaf:integer}},'/resources/leaf',true,true],
 ['simulation',{simulation:{leaf:integer}},'/simulation/leaf',true,true],
 ['business',{note:'data',leaf:integer,business:{enum:[{properties:{literal:{$contract:'contracts/missing.json#'}}}],default:{properties:{literal:{$contract:'contracts/missing.json#'}}}}},'/leaf',false,true],
];
test('followup formal C:16 JSON role and explicit selection cases',async()=>{
 for(const [name,value,pointer,skip,valid]of roles)for(const selected of [false,true]) {
  await check(`C/${name}/${selected}`,{'contracts/shapes.json':J(value),...(selected?{'prompts/select.prompt.md':iface([{$contract:'contracts/shapes.json#'+pointer}])}:{})},valid?0:4,{skips:skip&&!selected?['contracts/shapes.json']:[],...(['metadata','empty','business'].includes(name)?{records:1}:{}),...(valid?{}:{problemFile:'contracts/shapes.json'})});
 }
});

const object=names=>({type:'object',properties:Object.fromEntries(names.map(n=>[n,{type:'string'}])),required:[],additionalProperties:false});
test('followup formal D:48 authority and eligible copy cases',async()=>{
 const canonical=object(['a','b','c','d']);
 const placements=[['markdown','contracts/shapes.md',record(canonical),'Shape',true],['root','contracts/shapes.json',J(canonical),'',true],['pure','contracts/shapes.json',J({defs:{leaf:canonical}}),'/defs/leaf',false],['metadata','contracts/shapes.json',J({note:'business',leaf:canonical}),'/leaf',false],['resources','contracts/shapes.json',J({resources:{leaf:canonical}}),'/resources/leaf',false],['simulation','contracts/shapes.json',J({simulation:{leaf:canonical}}),'/simulation/leaf',false]];
 for(const [name,path,bytes,pointer,declared]of placements)for(const shape of ['two','exact','three','type'])for(const selected of [false,true]) {
  const copy=object(shape==='two'?['a','b']:shape==='three'?['a','b','c']:['a','b','c','d']);
  if(shape==='type')copy.properties.a.type='boolean';
  const expected=(declared||selected)&&['three','type'].includes(shape)?4:0;
  await check(`D/${name}/${shape}/${selected}`,{[path]:bytes,'contracts/legacy.json':J({copy}),'prompts/copy.prompt.md':iface([copy]),...(selected?{'prompts/select.prompt.md':iface([{$contract:path+'#'+pointer}])}:{})},expected,{worldValues:0,...(expected?{problemFile:'prompts/copy.prompt.md'}:{})});
 }
});

test('followup formal E:5 invalid JSON combinations',async()=>{
 const cwd=fs.mkdtempSync(join(tmpdir(),'pdd-followup-syntax-'));
 try {
  assert.equal(spawnSync('git',['init','-q'],{cwd}).status,0);
  for(const argv of [['contracts','--json'],['contracts','sync','--json'],['contracts','sync','--check','--json'],['contracts','--write','--check','--json'],['contracts','--write','--json']]) {
   let out='';const stream={write:s=>{out+=s;}};
   assert.equal(await runPdd(argv,{cwd,env:{...process.env,PDD_STATE_DIR:join(cwd,'.private-state')},stdout:stream,stderr:stream}),2,J(argv)+' '+out);
   assert.equal(fs.existsSync(join(cwd,'.private-state')),false);
  }
 }finally{fs.rmSync(cwd,{recursive:true,force:true});}
});
test('followup formal inventory:138 independently expected finite configurations',()=>assert.equal(configurations,138));
