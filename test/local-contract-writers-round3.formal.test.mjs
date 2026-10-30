import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {spawnSync} from 'node:child_process';
import {tmpdir} from 'node:os';
import {dirname,join,resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
// Independent literal oracle: Root reviewed before Code; 240 configurations.
const root=resolve(process.env.PDD_FORMAL_TARGET ?? new URL('..',import.meta.url).pathname);
const {runContracts}=await import(pathToFileURL(join(root,'src/contracts.mjs')));
const {observe,snapshot}=await import(pathToFileURL(join(root,'test/helpers/local-contract-observers.mjs')));
const J=JSON.stringify;
let configurations=0;
const table=(column,rows)=>'# Synthetic world\n| '+column+' | Writer |\n|---|---|\n'+rows.map(([p,w])=>'| '+p+' | '+w+' |\n').join('');
async function check(label,column,rows,seed,exit,uncovered=[]) {
 configurations++;
 const cwd=fs.mkdtempSync(join(tmpdir(),'pdd-writers-round3-'));
 try {
  const files={'contracts/world.md':table(column,rows),'contracts/seed-world.json':J(seed)};
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
    assert.equal(got.checked_records,0,label);
    assert.equal(got.checked_world_values,0,label);
    assert.deepEqual(got.skipped_files,[],label);
    assert.equal(got.diagnostics.some(d=>d.file==='contracts/world.md'&&d.field==='Writer'),exit===4,label+' Writer diagnostic');
    if(exit===0)assert.deepEqual(got.diagnostics,[],label);
    const warnings=got.warnings.filter(w=>w.kind==='world-writer-missing');
    assert.equal(warnings.length,uncovered.length?1:0,label+' one aggregate missing-row warning');
    if(uncovered.length){assert.equal(warnings[0].file,'contracts/seed-world.json',label);assert.deepEqual(warnings[0].world_keys,uncovered,label);for(const path of uncovered)assert.ok(warnings[0].message.includes(path),label);}
    const keys=[...new Set(rows.map(([p])=>column==='Key'?'/'+p:p))].sort();
    const schema=got.warnings.filter(w=>w.kind==='world-schema-missing');
    assert.equal(schema.length,1,label+' separate unchecked-schema advisory');
    assert.deepEqual(schema[0].world_keys,keys,label);
    assert.ok(typeof schema[0].message==='string'&&schema[0].message.trim().length>0,label+' finite advisory');
    if(keys.length===1){assert.ok(schema[0].message.includes('1 world key'),label+' singular');assert.ok(!schema[0].message.includes('1 world keys'),label+' not plural');}
   } else {
    for(const path of uncovered)assert.ok((stdout+stderr).includes(path),label+' text uncovered path');
    if(new Set(rows.map(([p])=>p)).size===1){assert.ok((stdout+stderr).includes('1 world key'),label+' singular');assert.ok(!(stdout+stderr).includes('1 world keys'),label+' not plural');}
   }
   assert.deepEqual(snapshot(cwd),before,label+' files unchanged');
   assert.equal(fs.existsSync(state),false,label+' no state');
  }
 }finally{fs.rmSync(cwd,{recursive:true,force:true});}
}
const cells=[
 ['server',['server']],[' server ',['server']],['test data',[]],['seed',[]],['initial world',[]],[' TeSt DaTa ',[]],['`SEED`',[]],['`Initial World`',[]],
 ['server, seed',['server']],['test data and server',['server']],['server / initial world',['server']],
 ['server & phone',['server','phone']],['server; phone',['server','phone']],['server and phone',['server','phone']],['server / phone',['server','phone']],['server, phone',['server','phone']],
 ['server, through phone and tablet / watch & kiosk; queue',['server']],['server, via phone / tablet, phone',['server','phone']],['server, using phone & tablet; watch',['server']],['server, by phone and tablet, server',['server']],
 ['search-and-rescue bot',['search-and-rescue bot']],['seed-worker',['seed-worker']],['Byron',['Byron']],['   ',[]],
];
test('round3 formal A:144 literal writer and aggregate-context cases',async()=>{
 for(let i=0;i<cells.length;i++)for(const extra of [null,'server','phone'])for(const column of ['Key','Path']){
  const [cell,actors]=cells[i],path=column==='Key'?'item':'/item';
  const count=new Set([...actors,...(extra?[extra]:[])]).size;
  const expected=count>1||(i===23&&!extra)?4:0;
  await check(`A/${i}/${extra}/${column}`,column,[[path,cell],...(extra?[[path,extra]]:[])],{item:0},expected);
 }
});
const duplicate=[
 [['seed'],0],[['seed','server'],0],[['seed','server','phone'],4],[['test data','initial world'],0],[['server','server'],0],[['server','phone'],4],
 [['seed','server, through phone and tablet'],0],[['seed','server & phone'],4],[['server; via phone'],4],[['server / by phone'],4],[['server and using phone'],4],[['','seed'],0],
];
test('round3 formal B:24 literal duplicate-row cases',async()=>{
 for(let i=0;i<duplicate.length;i++)for(const reverse of [false,true]){
  const [writers,exit]=duplicate[i];
  await check(`B/${i}/${reverse}`,'Path',(reverse?[...writers].reverse():writers).map(w=>['/item',w]),{item:0},exit);
 }
});
const coverage=[
 [[['/kv/menu','server']],v=>({kv:{menu:v,orders:v,tickets:v}}),['/kv/orders','/kv/tickets']],
 [[['/kv','server']],v=>({kv:{menu:v,orders:v,tickets:v}}),[]],
 [[['/kv/menu','seed']],v=>({kv:{menu:v,orders:v,tickets:v}}),['/kv/orders','/kv/tickets']],
 [[['/kv/menu','server']],v=>({kv:{menu:v,orders:{tickets:v}}}),['/kv/orders']],
 [[['/kv/orders/tickets','server']],v=>({kv:{orders:{tickets:v,spare:v},menu:v}}),['/kv/menu','/kv/orders/spare']],
 [[['/kv/orders/tickets','server']],v=>({kv:{orders:v}}),['/kv/orders']],
 [[['/kv/missing','server']],v=>({kv:{present:v}}),['/kv/present']],
 [[['/kv/<id>','server']],v=>({kv:{real:v}}),['/kv']],
 [[['/kv/menu','server']],v=>({kv:{menu:v},outside:v}),['/outside']],
 [[['/a~1b','server']],v=>({'a/b':v,'a~b':v}),['/a~0b']],
 [[['/kv/0','server']],v=>({kv:[v,v]}),['/kv/1']],
 [[['/kv/menu','server'],['/kv/menu','server']],v=>({kv:{menu:v,orders:v},outside:v}),['/kv/orders','/outside']],
];
test('round3 formal C:72 exact coverage and present-value cases',async()=>{
 for(let i=0;i<coverage.length;i++)for(const v of [null,false,0,'',[],{}]){
  const [rows,seed,paths]=coverage[i];await check(`C/${i}/${J(v)}`,'Path',rows,seed(v),0,paths);
 }
});
test('round3 formal inventory:240 configurations',()=>assert.equal(configurations,240));
