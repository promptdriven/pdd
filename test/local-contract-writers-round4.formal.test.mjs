import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {spawnSync} from 'node:child_process';
import {tmpdir} from 'node:os';
import {dirname,join,resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
// Independent literal oracle frozen by Root before Code: 156 configurations, text + JSON.
const root=resolve(process.env.PDD_FORMAL_TARGET ?? new URL('..',import.meta.url).pathname);
const {runContracts}=await import(pathToFileURL(join(root,'src/contracts.mjs')));
const {observe,snapshot}=await import(pathToFileURL(join(root,'test/helpers/local-contract-observers.mjs')));
const J=JSON.stringify;
let configurations=0;
const table=(column,rows)=>'# Synthetic world\n| '+column+' | Writer | Schema |\n|---|---|---|\n'+rows.map(([p,w,s=""])=>'| '+p+' | '+w+' | '+s+' |\n').join('');
async function check(label,column,rows,seed,exit=0,uncovered=[],initial=[],schemas=null,records=0) {
 configurations++;
 const cwd=fs.mkdtempSync(join(tmpdir(),'pdd-writers-round3-'));
 try {
  const files={'contracts/world.md':table(column,rows),'contracts/seed-world.json':J(seed),...(records?{'contracts/shapes.md':'### number\n```json\n{"type":"number"}\n```\n'}:{})};
  for(const [path,bytes] of Object.entries(files)){fs.mkdirSync(dirname(join(cwd,path)),{recursive:true});fs.writeFileSync(join(cwd,path),bytes);}
  assert.equal(spawnSync('git',['init','-q'],{cwd}).status,0);
  assert.equal(spawnSync('git',['add','.'],{cwd}).status,0);
  const before=snapshot(cwd),state=join(cwd,'.private-state');
  for(const json of [false,true]) {
   let stdout='',stderr='';
   const observer=observe({state,symlinkTarget:join(cwd,'nonexistent-target')});
   let code;
   try {code=await runContracts({cwd,words:[],options:{'--check':true,...(json?{'--json':true}:{})}},{env:{...process.env,PDD_STATE_DIR:state},stdout:{write:s=>{stdout+=s;}},stderr:{write:s=>{stderr+=s;}}});}
   finally {observer.restore();}
   assert.equal(code,exit,label+' '+stdout+stderr);
   assert.deepEqual(observer.calls,{runtime:0,model:0,auth:0,slots:0,history:0,write:0,symlink_target_read:0},label+' read-only local boundary');
   if(json) {
    const got=JSON.parse(stdout);
    assert.equal(got.exit_code,exit,label);
    assert.equal(got.checked_records,records,label);
    assert.equal(got.checked_world_values,0,label);
    assert.deepEqual(got.skipped_files,[],label);
    assert.equal(got.diagnostics.some(d=>d.file==='contracts/world.md'&&d.field==='Writer'),exit===4,label+' Writer diagnostic');
    if(exit===0)assert.deepEqual(got.diagnostics,[],label);
    const keys=schemas??[...new Set(rows.map(([p])=>column==='Key'?'/'+p:p))].sort();
    const expected=[...(keys.length?[{kind:'world-schema-missing',file:'contracts/world.md',world_keys:keys}]:[]),...initial.map(path=>({kind:'world-writer-initial-only',file:'contracts/world.md',world_keys:[path]})),...(uncovered.length?[{kind:'world-writer-missing',file:'contracts/seed-world.json',world_keys:uncovered}]:[])];
    assert.deepEqual(got.warnings.map(({kind,file,world_keys})=>({kind,file,world_keys})),expected,label+' complete ordered warning oracle');
    for(const warning of got.warnings){assert.ok(typeof warning.message==='string'&&warning.message.trim().length,label+' finite advisory');if(warning.kind!=='world-schema-missing')for(const path of warning.world_keys)assert.ok(warning.message.includes(path),label+' named path');}
    if(exit===4){assert.equal(got.diagnostics.length,1,label);assert.equal(got.diagnostics[0].record,rows[0][0],label);assert.equal(got.diagnostics[0].field,'Writer',label);}
   } else {
    for(const path of uncovered)assert.ok((stdout+stderr).includes(path),label+' text uncovered path');
    for(const path of initial)assert.ok((stdout+stderr).includes(path),label+' text initial-only path');
   }
   assert.deepEqual(snapshot(cwd),before,label+' files unchanged');
   assert.equal(fs.existsSync(state),false,label+' no state');
  }
 }finally{fs.rmSync(cwd,{recursive:true,force:true});}
}

const values=[null,false,0,'',[],{}];
const H='/hosts/<id>';
const templates=[
 ['/hosts/<id>',v=>({hosts:{a:v,b:v,'':v}}),[]],
 ['/hosts/<id>/state',v=>({hosts:{a:{state:v,extra:v},b:{state:v}}}),['/hosts/a/extra']],
 ['/screens/<m>:<s>:<p>',v=>({screens:{'m:work:w1:p1':v,bad:v}}),['/screens/bad']],
 ['/pre/prefix-<id>-suffix',v=>({pre:{'prefix-a-suffix':v,'prefix-a-other':v}}),['/pre/prefix-a-other']],
 ['/hosts/<id>',v=>({hosts:v}),['/hosts']],
 ['/hosts/<id>',v=>({}),[]],
 ['/duo/<id>/<id>',v=>({duo:{a:{b:v}}}),[]],
 ['/a~1b/<id>/~0x',v=>({'a/b':{'c/d':{'~x':v,other:v}}}),['/a~1b/c~1d/other']],
 ['/hosts/<id>',v=>({hosts:JSON.parse('{"__proto__":'+J(v)+',"constructor":'+J(v)+',"toString":'+J(v)+'}')}),[]],
 ['/arr/<id>/state',v=>({arr:[{state:v},{other:v}]}),['/arr/1/other']],
 ['/r/a.+[x](y)$^-<id>',v=>({r:{'a.+[x](y)$^-z':v,'aaaxy-z':v}}),['/r/aaaxy-z']],
 ['/screens/<m>:<s>:<p>',v=>({screens:{'::':v,':':v}}),['/screens/:']],
 ['/pre/a<id>b<id>c',v=>({pre:{aXbYc:v,aXbYd:v}}),['/pre/aXbYd']],
 ['/hosts/<id>/state',v=>({hosts:{'a/state':v}}),['/hosts/a~1state']],
 ['/hosts/<id>/state',v=>({hosts:{a:v}}),['/hosts/a']],
 ['/hosts/<id>',v=>({hosts:{a:{nested:v}},outside:v}),['/outside']],
 ['/a~0b/pre<id>post',v=>({'a~b':{'pre/post':v,preXpost:v,preXno:v}}),['/a~0b/preXno']],
 ['/<id>',v=>({'':v,ordinary:v}),[]],
];
test('round4 formal T:108 literal segment-template cases',async()=>{
 for(let i=0;i<templates.length;i++)for(const v of values){const [path,seed,missing]=templates[i];await check(`T/${i}/${J(v)}`,'Path',[[path,'owner']],seed(v),0,missing);}
});
// Literal actor sets: [server,phone], [server], [search-AND-rescue bot], [server].
const andCells=['server AND phone','server AnD server','search-AND-rescue bot','server, through phone AND tablet'];
const andExits=[[4,4,4,4],[0,0,4,0],[0,4,4,0],[0,0,4,0]];
test('round4 formal A:16 case-insensitive standalone AND cases',async()=>{
 for(let i=0;i<4;i++)for(let c=0;c<4;c++){const cell=andCells[i],extra=[null,'server','phone',cell][c];await check(`A/${i}/${c}`,'Path',[['/item',cell],...(extra?[['/item',extra]]:[])],{item:0},andExits[i][c]);}
});
const initialRows=[
 [[[H,'seed']],[H],0],
 [[[H,'test data'],[H,'initial world'],[H,'seed']],[H],0],
 [[[H,'seed'],[H,'owner']],[],0],
 [[[H,'seed'],['/absent','INITIAL WORLD'],['/absent','test data']],['/absent',H],0],
 [[[H,''],[H,'seed']],[H],0],
 [[[H,' ']],[],4],
];
test('round4 formal I:24 exact aggregate initialization cases',async()=>{
 for(let i=0;i<6;i++)for(const [n,seed] of [{},{hosts:{a:0}},{hosts:{a:{}}},{hosts:{a:false}}].entries()){const [rows,initial,exit]=initialRows[i];await check(`I/${i}/${n}`,'Path',rows,seed,exit,[],initial);}
});
test('round4 formal L:8 literal ownership and schema boundaries',async()=>{
 for(const v of [0,'bad']){
  await check(`L/0/${J(v)}`,'Path',[[H,'owner'],['/hosts/a','phone']],{hosts:{a:v}});
  await check(`L/1/${J(v)}`,'Path',[[H,'owner'],[H,'phone']],{hosts:{a:v}},4);
  await check(`L/2/${J(v)}`,'Path',[[H,'owner','contracts/shapes.md#number']],{hosts:{a:v}},0,[],[],[],1);
  await check(`L/3/${J(v)}`,'Path',[[H,'seed','contracts/shapes.md#number'],['/hosts/a','owner']],{hosts:{a:v}},0,[],[H],['/hosts/a'],1);
 }
});
test('round4 formal inventory:156 configurations',()=>assert.equal(configurations,156));
