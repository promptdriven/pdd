import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawn } from 'node:child_process';
import { chmodSync, existsSync, lstatSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';

async function api() { let mod; try { mod = await import('../src/workflow-prove.mjs'); } catch (e) { if (e.code !== 'ERR_MODULE_NOT_FOUND') throw e; } assert.equal(typeof mod?.proveRun, 'function', '#2594 missing API: proveRun'); return mod; }
function fixture(t) {
 const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-prove-'))); t.after(() => rmSync(root, {recursive:true,force:true}));
 const git = (...args) => execFileSync('git', args, {cwd:root, encoding:'utf8', env:{...process.env,GIT_AUTHOR_NAME:'Proof fixture',GIT_AUTHOR_EMAIL:'proof@example.invalid',GIT_COMMITTER_NAME:'Proof fixture',GIT_COMMITTER_EMAIL:'proof@example.invalid'}}).trim();
 const put = (path, body, mode) => { mkdirSync(dirname(join(root,path)),{recursive:true});writeFileSync(join(root,path),body);if(mode)chmodSync(join(root,path),mode); };
 const bare=join(root,'..',root.split('/').at(-1)+'-origin.git');t.after(()=>rmSync(bare,{recursive:true,force:true}));git('init','--bare','-q',bare);git('init','-qb','main');git('remote','add','origin',bare);put('src/value.mjs','export default false;\n');git('add','.');git('commit','-qm','base');const baseSha=git('rev-parse','HEAD');git('push','-q','origin','main');git('switch','-qc','topic');
 const runDir=join(root,'.git/pdd/runs/2594');mkdirSync(runDir,{recursive:true});
 const run={v:1,number:2594,runId:'native-proof',runDir,root,baseSha,baseBranch:'main',repo:'fixture/proof'};writeFileSync(join(runDir,'status.json'),JSON.stringify(run));
 const commit = () => {git('add','.');git('commit','-qm','head');return git('rev-parse','HEAD');};
 const proof = () => JSON.parse(readFileSync(join(runDir,'old-code-proof.json')));
 return {root,runDir,git,put,commit,proof,baseSha,run};
}
const command = 'node --test test/new.test.mjs';
const regression = "import assert from 'node:assert/strict';import value from '../src/value.mjs';assert.equal(value,true,'defect-x');\n";
// Fixture commands that ignore SIGTERM carry this marker and exit once the process that runs proveRun is gone,
// so a killed test leaves nothing running (#3263). The owner is this file, or PDD_3263_OWNER when a test sets it.
const marker = `pdd-3263-fixture-${process.pid}`;
const untilGone = `/*${marker}*/const owner=Number(process.env.PDD_3263_OWNER)||${process.pid};setInterval(()=>{try{process.kill(owner,0)}catch{process.exit()}},200);`;
const stubbornBase = `node -e "/*${marker}*/if(!require('fs').readFileSync('src/value.mjs','utf8').includes('true')){process.on('SIGTERM',()=>{});${untilGone}}"`;
const fixtureProcesses = () => {
 const psEnv = {...process.env}; delete psEnv.COLUMNS;
 return execFileSync('ps',['-eo','pid=,args='],{encoding:'utf8',env:psEnv,maxBuffer:64*1024*1024}).split('\n').filter(row=>row.includes(marker)).map(row=>Number(row.trim().split(/\s+/)[0])).filter(pid=>pid>0&&pid!==process.pid);
};
const alive = pid => {try {process.kill(pid,0);return true;} catch {return false;}};
const wait = ms => new Promise(r => setTimeout(r, ms));
test.after(async () => {
 const signal=(pids,name)=>{for(const pid of pids){try{process.kill(pid,name)}catch{}}};
 const left=fixtureProcesses();signal(left,'SIGTERM');for(let n=0;n<100&&left.some(alive);n++)await wait(20);signal(fixtureProcesses(),'SIGKILL');
});
test('PROVE-NATIVE1: committed tests and binary fixtures overlay old code; dirty bytes stay isolated', async t => {
 const {proveRun}=await api(), f=fixture(t);f.put('src/value.mjs','export default true;\n');f.put('test/new.test.mjs',regression);f.put('test/seed\n雪.bin',Buffer.from([0,255,2]));f.put('test/exec.sh','#!/bin/sh\nexit 0\n',0o755);const head=f.commit();f.put('src/value.mjs','throw Error("dirty");');f.put('test/new.test.mjs','throw Error("dirty test");');f.put('test/untracked.test.mjs','throw Error("untracked");');
 const answer=await proveRun({ref:'2594',cwd:f.root,test:command,expect:'defect-x'});assert.equal(answer.exitCode,0,JSON.stringify(f.proof()));const r=f.proof();assert.equal(r.outcome,'proved');assert.equal(r.headSha,head);assert.equal(r.baseSha,f.baseSha);assert.deepEqual(r.paths,['test/exec.sh','test/new.test.mjs','test/seed\n雪.bin']);assert.equal(r.base.expectedFound,true);assert.equal(r.head.exitCode,0);assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);assert.match(readFileSync(join(f.root,'src/value.mjs'),'utf8'),/dirty/);
});
test('PROVE-NATIVE2: byte and executable fidelity, NUL-safe names, rename destinations and src exclusions', async t => {
 const {proveRun}=await api(),f=fixture(t);const binaryTest="import fs from 'node:fs';import assert from 'node:assert/strict';assert.deepEqual([...fs.readFileSync('fixtures/raw.bin')],[0,255,7]);assert.ok(fs.statSync('fixtures/run.sh').mode & 0o111);console.log('defect-x');process.exit(1);\n";f.put('test/old.test.mjs',binaryTest);f.commit();const saved=f.git('rev-parse','HEAD');f.git('push','-q','origin',`${saved}:refs/heads/main`);f.run.baseSha=saved;writeFileSync(join(f.runDir,'status.json'),JSON.stringify(f.run));f.git('mv','test/old.test.mjs','test/雪\nnew.test.mjs');f.put('test/雪\nnew.test.mjs',binaryTest+'// renamed regression\n');f.put('fixtures/raw.bin',Buffer.from([0,255,7]));f.put('fixtures/run.sh','#!/bin/sh\n',0o755);f.put('src/hidden.test.mjs','throw Error("excluded");');f.commit();const answer=await proveRun({ref:'2594',cwd:f.root,test:'node "test/雪\nnew.test.mjs"',expect:'defect-x'});assert.equal(answer.exitCode,1);const r=f.proof();assert.equal(r.outcome,'head-fails');assert.equal(r.base.expectedFound,true);assert.equal(r.base.setupError,'');assert.deepEqual(r.paths,['fixtures/raw.bin','fixtures/run.sh','test/雪\nnew.test.mjs']);
});
test('PROVE-NATIVE3: old passes, wrong reason with full-output code selector, and head failure precedence', async t => {
 const {proveRun}=await api(),f=fixture(t);f.put('test/new.test.mjs',"console.log('code: intent-invalid');console.log('noise\\n'.repeat(30));process.exit(1);");f.put('src/value.mjs','export default true;');f.commit();let answer=await proveRun({ref:'2594',cwd:f.root,test:"node -e \"if(!require('fs').readFileSync('src/value.mjs','utf8').includes('true'))require('./test/new.test.mjs')\"",expect:'body-unsafe'});assert.equal(answer.exitCode,1);assert.equal(f.proof().outcome,'wrong-reason');assert.equal(f.proof().base.observedError,'code: intent-invalid');assert.equal(f.proof().base.stdoutTail.includes('code: intent-invalid'),false);assert.match(answer.message,/intent-invalid/);
 answer=await proveRun({ref:'2594',cwd:f.root,test:'true',expect:'defect-x'});assert.equal(f.proof().outcome,'old-passes');answer=await proveRun({ref:'2594',cwd:f.root,test:'exit 1',expect:'defect-x'});assert.equal(f.proof().outcome,'head-fails');
});
test('PROVE-NATIVE4: setup diagnostics disqualify literal matches; stdout/stderr cannot combine a literal', async t => {
 const {proveRun}=await api(),f=fixture(t);f.put('test/new.test.mjs',regression);f.put('src/value.mjs','export default true;');f.commit();await proveRun({ref:'2594',cwd:f.root,test:"node -e \"console.error('Error: Cannot find module defect-x');process.exit(1)\"",expect:'defect-x'});assert.equal(f.proof().outcome,'setup-error');assert.match(f.proof().setupError,/Cannot find module/);
 await proveRun({ref:'2594',cwd:f.root,test:"node -e \"if(!require('fs').readFileSync('src/value.mjs','utf8').includes('true')){process.stdout.write('defect-');process.stderr.write('x');process.exit(1)}\"",expect:'defect-x'});assert.equal(f.proof().outcome,'wrong-reason');
});
test('PROVE-NATIVE5: fixture-only runs without overlay; symlink tests remain unsafe', async t => {
 const {proveRun}=await api(),f=fixture(t);f.put('fixtures/data','x');f.commit();await proveRun({ref:'2594',cwd:f.root,test:"node -e \"console.log(require('fs').existsSync('fixtures/data'))\"",expect:'x'});assert.equal(f.proof().outcome,'old-passes');assert.deepEqual(f.proof().paths,[]);assert.equal(f.proof().base.exitCode,0);assert.equal(f.proof().head.exitCode,0);assert.deepEqual(f.proof().base.stdoutTail,['false']);assert.deepEqual(f.proof().head.stdoutTail,['true']);assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);
 symlinkSync('../src/value.mjs',join(f.root,'test-link.test.mjs'));f.commit();await proveRun({ref:'2594',cwd:f.root,test:'true',expect:'x'});assert.equal(f.proof().outcome,'setup-error');
});
test('PROVE-NATIVE6: default readRun accepts real selection and rejects an absent run without a record', async t => {
 const {proveRun}=await api(),f=fixture(t);const result=await proveRun({ref:'9999',cwd:f.root,test:'true',expect:'x'});assert.equal(result.exitCode,1);assert.equal(result.message,'Old-code proof: ✗ setup-error (run unavailable).');assert.equal(existsSync(join(f.runDir,'old-code-proof.json')),false);
});
test('PROVE-NATIVE7: whole process group is killed on output overflow and both snapshots are removed', {timeout:20000}, async t => {
 const {proveRun}=await api(),f=fixture(t);f.put('test/new.test.mjs',regression);f.commit();const pidFile=join(f.runDir,'child.pid');const script=`/*${marker}*/const fs=require('fs');const {spawn}=require('child_process');let child=spawn(process.execPath,['-e',${JSON.stringify(`${untilGone}process.on("SIGTERM",()=>{});`)}],{stdio:'ignore'});fs.appendFileSync(${JSON.stringify(pidFile)},String(child.pid)+"\\n");process.on('SIGTERM',()=>{});${untilGone}setTimeout(()=>setInterval(()=>process.stdout.write('x'.repeat(65536)),1),100);`;
 const started=Date.now();const answer=await proveRun({ref:'2594',cwd:f.root,test:`node -e '${script.replaceAll("'", "'\\''")}'`,expect:'x'});assert.equal(answer.exitCode,1);assert.equal(f.proof().outcome,'output-limit');assert.equal(f.proof().base.outputLimited,true);assert.equal(f.proof().head.outputLimited,true);assert.ok(f.proof().base.stdoutTail.join('\n').length<=1048576);const pids=readFileSync(pidFile,'utf8').trim().split('\n').map(Number);assert.equal(pids.length,2);for(const pid of pids){let alive=false;try{const stat=readFileSync(`/proc/${pid}/stat`,'utf8');alive=!/\) Z /.test(stat);}catch{}assert.equal(alive,false);}assert.ok(Date.now()-started>=4000);assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);
});
test('PROVE-NATIVE8: a 1-minute --timeout deadline kills descendants then still executes committed head', {timeout:75000}, async t => {
 const {proveRun}=await api(),f=fixture(t);f.put('test/new.test.mjs',regression);f.put('src/value.mjs','export default true;');f.commit();const start=Date.now();await proveRun({ref:'2594',cwd:f.root,test:stubbornBase,expect:'defect-x',timeoutMinutes:1});const r=f.proof();assert.equal(r.outcome,'base-timeout');assert.equal(r.base.timedOut,true);assert.equal(r.head.exitCode,0);assert.ok(Date.now()-start>=60000);assert.ok(Date.now()-start<72000);assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);
});
test('3263: a base command that ignores SIGTERM stops when the process running proveRun is killed', {timeout:30000}, async t => {
 const f=fixture(t);f.put('test/new.test.mjs',regression);f.commit();const modulePath=new URL('../src/workflow-prove.mjs',import.meta.url).href;
 const childTmp=join(f.runDir,'tmp');mkdirSync(childTmp,{recursive:true});
 const script=`import {proveRun} from ${JSON.stringify(modulePath)};process.env.PDD_3263_OWNER=String(process.pid);await proveRun(${JSON.stringify({ref:'2594',cwd:f.root,test:stubbornBase,expect:'defect-x',timeoutMinutes:1})});`;
 const child=spawn(process.execPath,['--input-type=module','-e',script],{stdio:'ignore',env:{...process.env,TMPDIR:childTmp,TMP:childTmp,TEMP:childTmp}});const ended=new Promise(r=>child.on('close',r));
 const started=()=>fixtureProcesses().filter(pid=>pid!==child.pid);let base=[];
 try {for(let n=0;n<500&&!base.length;n++){base=started();if(!base.length)await wait(20);}assert.ok(base.length,'the base command starts');
  child.kill('SIGKILL');await ended;for(let n=0;n<150&&base.some(alive);n++)await wait(20);
  assert.deepEqual(base.filter(alive),[],'no fixture process outlives the killed proveRun process');}
 finally {
  child.kill('SIGKILL');await ended;
  for(const entry of f.git('worktree','list','--porcelain','-z').split('\0')){if(entry.startsWith('worktree ')&&entry.slice(9)!==f.root)rmSync(entry.slice(9),{recursive:true,force:true});}
  f.git('worktree','prune');
 }
});
test('PROVE-PORT1: blank-input validation has no host effects', async () => {
 const {proveRun}=await api();let called=0;assert.deepEqual(await proveRun({test:' ',expect:'x'},new Proxy({}, {get(){called++;throw Error('effect');}})),{exitCode:2,message:'pdd workflow prove requires nonblank --test and --expect.'});assert.equal(called,0);
});
test('PROVE-NATIVE9: base destination symlink ancestry fails safely and all worktrees are cleaned', async t => {
 const {proveRun}=await api(),f=fixture(t);symlinkSync('src',join(f.root,'test'));f.commit();f.run.baseSha=f.git('rev-parse','HEAD');f.git('push','-q','origin',`${f.run.baseSha}:refs/heads/main`);writeFileSync(join(f.runDir,'status.json'),JSON.stringify(f.run));rmSync(join(f.root,'test'));f.put('test/new.test.mjs',regression);f.commit();await proveRun({ref:'2594',cwd:f.root,test:command,expect:'defect-x'});assert.equal(f.proof().outcome,'setup-error');assert.match(f.proof().setupError,/symlink ancestry/i);assert.equal(f.proof().base.exitCode,null);assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);assert.equal(existsSync(join(f.root,'src/new.test.mjs')),false);
});
test('PROVE-NATIVE10: cleanup failures override proof; rename/save errors return failure atomically', async t => {
 const {proveRun}=await api(),f=fixture(t);f.put('test/new.test.mjs',regression);f.put('src/value.mjs','export default true;');f.commit();const result=await proveRun({ref:'2594',cwd:f.root,test:command,expect:'defect-x'},{cleanup:async({root,worktrees})=>{for(const path of worktrees)execFileSync('git',['worktree','remove','--force',path],{cwd:root});return {error:'deliberate cleanup failure'};}});assert.equal(result.exitCode,1);assert.equal(f.proof().outcome,'setup-error');assert.equal(f.proof().cleanupError,'deliberate cleanup failure');rmSync(join(f.runDir,'old-code-proof.json'));mkdirSync(join(f.runDir,'old-code-proof.json'));const saveFailure=await proveRun({ref:'2594',cwd:f.root,test:command,expect:'defect-x'});assert.deepEqual(saveFailure,{exitCode:1,message:'Old-code proof: ✗ setup-error (could not save result).'});assert.equal(lstatSync(join(f.runDir,'old-code-proof.json')).isDirectory(),true);
});
test('PROVE-NATIVE11: deletions never overlay and signalled execution never establishes proof', async t => {
 const {proveRun}=await api(),f=fixture(t);f.put('test/deleted.test.mjs','throw Error("deleted");');f.put('test/remaining.test.mjs',"import fs from 'node:fs';console.log(fs.existsSync('test/deleted.test.mjs'));\n");f.commit();f.run.baseSha=f.git('rev-parse','HEAD');f.git('push','-q','origin',`${f.run.baseSha}:refs/heads/main`);writeFileSync(join(f.runDir,'status.json'),JSON.stringify(f.run));f.git('rm','test/deleted.test.mjs');f.commit();await proveRun({ref:'2594',cwd:f.root,test:'node --test test/remaining.test.mjs',expect:'x'});assert.equal(f.proof().outcome,'old-passes');assert.deepEqual(f.proof().paths,[]);assert.equal(f.proof().base.exitCode,0);assert.equal(f.proof().head.exitCode,0);assert.ok(f.proof().base.stdoutTail.includes('# true'));assert.ok(f.proof().head.stdoutTail.includes('# false'));assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);f.put('test/new.test.mjs',regression);f.commit();await proveRun({ref:'2594',cwd:f.root,test:'kill -TERM $$',expect:'defect-x'});assert.equal(f.proof().outcome,'signalled');assert.equal(f.proof().base.signal,'SIGTERM');assert.equal(f.proof().head.signal,'SIGTERM');
});

test('2904: the per-phase limit is 10 minutes by default, a person sets 1 to 120 minutes, and a bad value runs nothing', async t => {
 const {proveRun,DEFAULT_PHASE_MINUTES}=await api();assert.equal(DEFAULT_PHASE_MINUTES,10);
 const limits=async extra=>{const f=fixture(t);f.put('test/new.test.mjs',regression);f.commit();const seen=[];
  await proveRun({ref:'2594',cwd:f.root,test:command,expect:'defect-x',...extra},{runProcess:async input=>{seen.push(input.timeoutMs);return {result:{exitCode:0,signal:'',timedOut:false,outputLimited:false,stdout:'',stderr:'',error:'',setupError:''}};}});return seen;};
 assert.deepEqual(await limits({}),[600000,600000]);
 assert.deepEqual(await limits({timeoutMinutes:45}),[2700000,2700000]);
 for(const timeoutMinutes of [0,121,1.5]){let called=0;assert.deepEqual(await proveRun({test:'x',expect:'y',timeoutMinutes},new Proxy({}, {get(){called++;throw Error('effect');}})),{exitCode:2,message:'pdd workflow prove --timeout takes whole minutes from 1 to 120.'});assert.equal(called,0);}
});

// Approved existing-test fallback: paths describe the overlay, never command authority.
test('2958-FALLBACK-EMPTY: an empty committed diff executes unchanged tests twice and cleans snapshots', async t => {
 const {proveRun}=await api(),f=fixture(t);
 f.put('test/remaining.test.mjs',"import assert from 'node:assert/strict';import fs from 'node:fs';assert.equal(fs.readFileSync('src/value.mjs','utf8'),'export default false;\\n');assert.equal(fs.existsSync('test/untracked.test.mjs'),false);console.log('committed existing test');\n");
 const base=f.commit();f.git('push','-q','origin',`${base}:refs/heads/main`);
 f.put('src/value.mjs','throw Error("dirty implementation");');f.put('test/remaining.test.mjs','throw Error("dirty test");');f.put('test/untracked.test.mjs','throw Error("untracked");');
 const result=await proveRun({ref:'2594',cwd:f.root,test:'node --test test/remaining.test.mjs',expect:'defect-x'}),r=f.proof();
 assert.equal(result.exitCode,1);assert.equal(r.outcome,'old-passes');assert.deepEqual(r.paths,[]);assert.equal(r.baseSha,base);assert.equal(r.headSha,base);
 for(const phase of [r.base,r.head]){assert.equal(phase.exitCode,0);assert.ok(phase.stdoutTail.includes('# committed existing test'));}
 assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);assert.match(readFileSync(join(f.root,'test/remaining.test.mjs'),'utf8'),/dirty test/);
});

test('2958-FALLBACK-LANDED: public CLI executes identical landed map, CSS and adapter assertions on computed snapshots', async t => {
 const {runPdd}=await import('../src/pdd-cli.mjs'),{validateProofRecord}=await api(),f=fixture(t);
 const files=['app/maps/checkout.json','app/styles/checkout.css','app/adapters/checkout.mjs'];
 const old=['{"destination":"/legacy"}\n','.confirm-target { min-height: 1px; }\n','export const destination = "/legacy";\n'];
 const fixed=['{"destination":"/checkout"}\n','.confirm-target { min-height: 44px; }\n','export const destination = "/checkout";\n'];
 files.forEach((path,i)=>f.put(path,old[i]));
 f.put('test/landed.test.mjs',`import test from 'node:test';import assert from 'node:assert/strict';import {readFileSync} from 'node:fs';import {destination} from '../app/adapters/checkout.mjs';
 test('map route',()=>assert.equal(JSON.parse(readFileSync('app/maps/checkout.json','utf8')).destination,'/checkout','code: map-route-defect'));
 test('CSS target size',()=>assert.ok(Number(/min-height:\\s*(\\d+)px/.exec(readFileSync('app/styles/checkout.css','utf8'))?.[1])>=44,'code: target-size-defect'));
 test('adapter route',()=>assert.equal(destination,'/checkout','code: adapter-route-defect'));
 `);
 const base=f.commit();f.git('push','-q','origin',`${base}:refs/heads/main`);files.forEach((path,i)=>f.put(path,fixed[i]));const head=f.commit();
 assert.deepEqual(f.git('diff','--name-only',base,head).split('\n'),[files[2],files[0],files[1]]);
 let stdout='',stderr='';const exit=await runPdd(['workflow','prove','2594','--test','node --test test/landed.test.mjs','--expect','code: map-route-defect','--timeout','1'],{cwd:f.root,stdout:{write:s=>stdout+=s},stderr:{write:s=>stderr+=s}});
 const r=f.proof();assert.equal(exit,0,stderr);assert.equal(stderr,'');assert.match(stdout,/Old-code proof: ✓/);assert.deepEqual(r.paths,[]);assert.equal(r.baseSha,base);assert.equal(r.headSha,head);assert.equal(r.base.exitCode,1);assert.equal(r.base.expectedFound,true);assert.equal(r.base.setupError,'');assert.equal(r.head.exitCode,0);assert.equal(validateProofRecord(r),true);assert.equal(JSON.parse(readFileSync(join(f.runDir,'status.json'))).baseSha,f.baseSha);
 const {readRunResults}=await import('../src/workflow-results.mjs');const {preparePrEvidence}=await import('../src/workflow-pr-evidence.mjs');
 assert.equal(readRunResults({root:f.root,runDir:f.runDir,runId:f.run.runId,baseBranch:'main'})[0].state,'current');
 assert.equal((await preparePrEvidence({run:{...f.run,steps:[]},isCode:true})).proofStatus,'proved');
 assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);
 for(let i=0;i<files.length;i++){
  const control=join(f.runDir,`control-${i}`);f.git('worktree','add','--detach',control,head);
  try{writeFileSync(join(control,files[i]),old[i]);let failed;const env={...process.env};delete env.NODE_TEST_CONTEXT;try{execFileSync(process.execPath,['--test','test/landed.test.mjs'],{cwd:control,encoding:'utf8',env});}catch(error){failed=error;}
   assert.equal(failed?.status,1,'semantic control must fail');assert.match(failed.stdout,/ERR_ASSERTION/);assert.match(failed.stdout,new RegExp(['map-route-defect','target-size-defect','adapter-route-defect'][i]));assert.match(failed.stdout,/# pass 2/);assert.doesNotMatch(failed.stdout,/ERR_MODULE_NOT_FOUND|SyntaxError/);
  }finally{f.git('worktree','remove','--force',control);}
 }
});

test('2958-FALLBACK-MISSING: changed test overlay never supplies the missing native implementation', async t=>{
 const {proveRun}=await api(),f=fixture(t);f.put('app/native/native-checkout-defect.mjs','export const enabled = true;\n');f.put('test/new.test.mjs',"import assert from 'node:assert/strict';import {enabled} from '../app/native/native-checkout-defect.mjs';assert.equal(enabled,true);\n");f.commit();
 const answer=await proveRun({ref:'2594',cwd:f.root,test:command,expect:'native-checkout-defect'}),r=f.proof();assert.equal(answer.exitCode,1);assert.equal(r.outcome,'setup-error');assert.deepEqual(r.paths,['test/new.test.mjs']);assert.equal(r.base.exitCode,1);assert.match(r.base.setupError,/ERR_MODULE_NOT_FOUND/);assert.equal(r.base.expectedFound,true);assert.equal(r.head.exitCode,0);assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);
});
