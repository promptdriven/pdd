import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {spawn} from 'node:child_process';
import {once} from 'node:events';
import {openFallbackStore} from '../src/autopilot-store-fallback.mjs';
import {openAutopilotStore,readAutopilotState,saveAutopilotState,autopilotStateFiles} from '../src/autopilot-store.mjs';
const moduleUrl=new URL('../src/autopilot-store-fallback.mjs',import.meta.url).href;
function fixture(t){const root=fs.mkdtempSync(join(tmpdir(),'pdd-fallback-'));t.after(()=>fs.rmSync(root,{recursive:true,force:true}));return root;}
function child(t,code,root){const proc=spawn(process.execPath,['--input-type=module','-e',code,root],{stdio:['ignore','pipe','pipe','ipc']});const done=once(proc,'exit');let stderr='';proc.stderr.on('data',bytes=>{stderr+=bytes;});t.after(()=>{if(proc.exitCode===null&&proc.signalCode===null)proc.kill('SIGKILL');});return {proc,done,error:()=>stderr};}

test('fallback: JSON values, costs and migration marker commit together and rollback together',t=>{
 const root=fixture(t),s=openFallbackStore({root});
 s.transaction(tx=>{tx.put('queue','task',{state:'ready'});tx.migrate('old',()=>7,value=>tx.put('runs','run',value));});
 assert.throws(()=>s.transaction(tx=>{tx.put('queue','task',{state:'running'});tx.append('costs','repo',{usd:2});throw Error('fault');}));
 s.transaction(tx=>{assert.equal(tx.get('queue','task').state,'ready');assert.equal(tx.entries('costs').length,0);assert.equal(tx.get('runs','run'),7);tx.migrate('old',()=>assert.fail('import repeated'),()=>{});});
 assert.equal(fs.statSync(join(root,'machine-state.json')).mode&0o777,0o600);
});

test('fallback: an existing snapshot remains one backend after opening through the default factory',t=>{
 const root=fixture(t);openFallbackStore({root}).transaction(tx=>tx.put('control','a'.repeat(20)+'.json',{enabled:true}));
 const file=join(root,'a'.repeat(20)+'.json');assert.equal(readAutopilotState(file).enabled,true);
 saveAutopilotState(file,{enabled:false});assert.equal(readAutopilotState(file).enabled,false);
 assert.deepEqual(autopilotStateFiles(root),['a'.repeat(20)+'.json']);
 assert.equal(fs.existsSync(join(root,'machine.sqlite')),false);
});

test('fallback: independent processes serialize budget increments and retain every journal row',async t=>{
 const root=fixture(t);openFallbackStore({root}).transaction(tx=>tx.put('budgets','used',0));
 const children=Array.from({length:4},()=>child(t,`import {openFallbackStore} from ${JSON.stringify(moduleUrl)};
 const s=openFallbackStore({root:process.argv[1]});for(let i=0;i<10;i++)s.transaction(tx=>{tx.put('budgets','used',tx.get('budgets','used')+1);tx.append('events','repo',{i});});process.disconnect();`,root));
 for(const c of children){const [code]=await c.done;assert.equal(code,0,c.error());}
 openAutopilotStore({root}).transaction(tx=>{assert.equal(tx.get('budgets','used'),40);assert.equal(tx.entries('events').length,40);});
});

test('fallback: a killed writer is reclaimed without publishing its transaction',async t=>{
 const root=fixture(t);openFallbackStore({root}).transaction(tx=>tx.put('queue','task','ready'));
 const c=child(t,`import {openFallbackStore} from ${JSON.stringify(moduleUrl)};
 openFallbackStore({root:process.argv[1]}).transaction(tx=>{tx.put('queue','task','running');tx.put('leases','task','worker');process.send('written');Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0,30000);});`,root);
 await once(c.proc,'message');c.proc.kill('SIGKILL');await c.done;
 openFallbackStore({root}).transaction(tx=>{assert.equal(tx.get('queue','task'),'ready');assert.equal(tx.get('leases','task'),undefined);});
});

test('fallback: async, nested, escaped and newer-schema transactions refuse',t=>{
 const root=fixture(t),s=openFallbackStore({root});let escaped;
 assert.throws(()=>s.transaction(tx=>{tx.put('queue','bad',1);return Promise.resolve();}),TypeError);
 assert.throws(()=>s.transaction(()=>s.transaction(()=>{})));
 s.transaction(tx=>{escaped=tx;assert.equal(tx.get('queue','bad'),undefined);});assert.throws(()=>escaped.put('queue','bad',1));
 const file=join(root,'machine-state.json'),value=JSON.parse(fs.readFileSync(file,'utf8'));value.v=2;const bytes=JSON.stringify(value);fs.writeFileSync(file,bytes);assert.throws(()=>s.transaction(()=>{}));assert.equal(fs.readFileSync(file,'utf8'),bytes);
});

test('backend selection: unavailable SQLite uses fallback and a selected SQLite database never falls back',t=>{
 const root=fixture(t),fallback=openAutopilotStore({root},{sqlite:null});fallback.transaction(tx=>tx.put('queue','task',7));fallback.close();
 assert.equal(fs.readFileSync(join(root,'machine-backend'),'utf8'),'snapshot');
 openAutopilotStore({root}).transaction(tx=>assert.equal(tx.get('queue','task'),7));
 const other=fixture(t),sqlite=openAutopilotStore({root:other});sqlite.close();
 if(fs.readFileSync(join(other,'machine-backend'),'utf8')==='sqlite'){
  assert.throws(()=>openAutopilotStore({root:other},{sqlite:null}));
  assert.equal(fs.existsSync(join(other,'machine-state.json')),false);
 }
});

test('backend selection: simultaneous first opens choose one format across runtime capabilities',async t=>{
 const root=fixture(t),factory=new URL('../src/autopilot-store.mjs',import.meta.url).href;
 const code=capability=>`import {openAutopilotStore} from ${JSON.stringify(factory)};
 process.send('ready');process.once('message',()=>{try{const s=openAutopilotStore({root:process.argv[1]},${capability});s.transaction(tx=>tx.put('queue',${JSON.stringify(capability)},7));s.close();}catch(error){if(!error.message.includes('cannot open existing SQLite'))throw error;}process.disconnect();});`;
 const a=child(t,code('{}'),root),b=child(t,code('{sqlite:null}'),root);
 await Promise.all([once(a.proc,'message'),once(b.proc,'message')]);a.proc.send('go');b.proc.send('go');
 for(const c of [a,b]){const [exit]=await c.done;assert.equal(exit,0,c.error());}
 const chosen=fs.readFileSync(join(root,'machine-backend'),'utf8');
 assert.equal(fs.existsSync(join(root,'machine.sqlite')),chosen==='sqlite');
 assert.equal(fs.existsSync(join(root,'machine-state.json')),chosen==='snapshot');
});

test('port parity: both backends reject missing keys and scopes without changing state',t=>{
 for(const factory of [openAutopilotStore,openFallbackStore]){
  const root=fixture(t),s=factory({root});t.after(()=>s.close());
  for(const operation of [tx=>tx.put('control',undefined,7),tx=>tx.get('control'),tx=>tx.remove('control'),tx=>tx.append('events',undefined,7),tx=>tx.prune('events',undefined,1),tx=>tx.migrate(undefined,()=>7,()=>{})]){
   assert.throws(()=>s.transaction(operation),TypeError);
  }
  s.transaction(tx=>{assert.deepEqual(tx.list('control'),[]);assert.deepEqual(tx.entries('events'),[]);});
 }
});
