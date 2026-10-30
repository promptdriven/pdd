import test from 'node:test';
import assert from 'node:assert/strict';
import {execFileSync,spawn} from 'node:child_process';
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync,realpathSync,existsSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,dirname,resolve} from 'node:path';
const modulePath=resolve('src/workflow-prove.mjs');
const wait=ms=>new Promise(r=>setTimeout(r,ms));
async function api(){let mod;try{mod=await import('../src/workflow-prove.mjs')}catch(error){if(error.code!=='ERR_MODULE_NOT_FOUND')throw error;}assert.equal(typeof mod?.proveRun,'function','review proof API must exist');return mod;}
async function evidenceApi(){let mod;try{mod=await import('../src/workflow-pr-evidence.mjs')}catch(error){if(error.code!=='ERR_MODULE_NOT_FOUND')throw error;}assert.equal(typeof mod?.preparePrEvidence,'function','review evidence API must exist');return mod;}
function fixture(t){
 const parent=realpathSync(mkdtempSync(join(tmpdir(),'pdd-review-proof-'))),root=join(parent,'repo'),bare=join(parent,'origin.git');mkdirSync(root);
 t.after(()=>rmSync(parent,{recursive:true,force:true}));
 const git=(...a)=>execFileSync('git',a,{cwd:root,encoding:'utf8',stdio:['ignore','pipe','pipe']}).trim();
 const put=(p,s)=>{mkdirSync(dirname(join(root,p)),{recursive:true});writeFileSync(join(root,p),s)};
 git('init','--bare','-q',bare);git('init','-qb','main');git('config','user.name','Proof test');git('config','user.email','proof@example.invalid');git('remote','add','origin',bare);
 put('src/value.mjs','export default false;');git('add','.');git('commit','-qm','base');git('push','-q','origin','main');const savedBase=git('rev-parse','HEAD');git('switch','-qc','topic');
 const runDir=join(root,'.git/pdd/runs/2594');mkdirSync(runDir,{recursive:true});const run={v:1,number:2594,runId:'review-proof',root,runDir,baseBranch:'main',baseSha:savedBase};writeFileSync(join(runDir,'status.json'),JSON.stringify(run));
 const commit=()=>{git('add','.');git('commit','-qm','change');return git('rev-parse','HEAD')};
 const proof=()=>JSON.parse(readFileSync(join(runDir,'old-code-proof.json')));
 return {parent,root,bare,git,put,runDir,run,savedBase,commit,proof};
}
const regression="import assert from 'node:assert/strict';import value from '../src/value.mjs';assert.equal(value,true,'defect-x');";
test('REVIEW-PROVE-MERGE: fetched merge-base excludes tests merged from base and preserves saved run base',async t=>{
 const f=fixture(t),{proveRun}=await api();
 f.git('switch','-q','main');f.put('test/base-only.test.mjs','throw Error("unrelated base test");');const base=f.commit();f.git('push','-q','origin','main');f.git('switch','-q','topic');f.git('merge','-qm','merge base','main');f.put('src/value.mjs','export default true;');f.put('test/regression.test.mjs',regression);f.commit();
 const r=await proveRun({ref:'2594',cwd:f.root,test:'node --test test/regression.test.mjs',expect:'defect-x'});
 assert.equal(r.exitCode,0,r.message);assert.equal(f.proof().baseSha,base,'must use computed merge-base');assert.equal(f.proof().v,2);assert.deepEqual(f.proof().paths,['test/regression.test.mjs']);assert.equal(JSON.parse(readFileSync(join(f.runDir,'status.json'))).baseSha,f.savedBase);
 assert.match(r.message,/✓ `node --test test\/regression.test.mjs`: old-code exit `1`; output contains `defect-x`; new-code exit `0`/);
 f.git('remote','set-url','origin',join(f.parent,'missing-origin'));const unavailable=await proveRun({ref:'2594',cwd:f.root,test:'true',expect:'defect-x'});assert.equal(unavailable.exitCode,1);assert.equal(f.proof().outcome,'setup-error');assert.equal(f.proof().base.exitCode,null,'fetch failure cannot fall back to saved base');
});
test('REVIEW-PROVE-SETUP: successful setup-looking head output is allowed; 127 diagnoses setup with actual tail',async t=>{
 const f=fixture(t),{proveRun}=await api();f.put('src/value.mjs','export default true;');f.put('test/regression.test.mjs',regression);f.commit();
 const command=`node -e "if(require('fs').readFileSync('src/value.mjs','utf8').includes('true'))console.log('ENOENT: harmless');else{console.error('defect-x');process.exit(1)}"`;
 assert.equal((await proveRun({ref:'2594',cwd:f.root,test:command,expect:'defect-x'})).exitCode,0);
 const r=await proveRun({ref:'2594',cwd:f.root,test:'missing-pdd-command-2594',expect:'defect-x'});assert.equal(f.proof().outcome,'setup-error');assert.match(r.message,/127/);assert.match(r.message,/; tail .*missing-pdd-command-2594/);
});
for(const signal of ['SIGINT','SIGTERM','SIGHUP']) test(`REVIEW-PROVE-INTERRUPT-${signal}: actual parent signal kills descendants and removes both snapshots`, {timeout:20000},async t=>{
 const f=fixture(t);f.put('test/regression.test.mjs',regression);f.commit();const pidFile=join(f.runDir,'child.pid');
 const childScript=`const grandchild=require("child_process").spawn(process.execPath,["-e",'process.on("SIGTERM",()=>{});setInterval(()=>{},1000)'],{stdio:"ignore"});process.on("SIGTERM",()=>{});require("fs").writeFileSync(${JSON.stringify(pidFile)},JSON.stringify([process.pid,grandchild.pid]));setInterval(()=>{},1000)`;
 const command=`node -e '${childScript.replaceAll("'", "'\\''")}'`;
 const script=`import {proveRun} from ${JSON.stringify(modulePath)};const r=await proveRun(${JSON.stringify({ref:'2594',cwd:f.root,test:command,expect:'defect-x'})});console.log(JSON.stringify(r));process.exitCode=r.exitCode;`;
 const child=spawn(process.execPath,['--input-type=module','-e',script],{stdio:['ignore','pipe','pipe']});let out='',err='';child.stdout.on('data',s=>out+=s);child.stderr.on('data',s=>err+=s);const ended=new Promise(r=>child.on('close',(code,signal)=>r({code,signal})));
 let pid,descendants=[];
 try {for(let n=0;n<200&&!existsSync(pidFile);n++)await wait(20);assert.ok(existsSync(pidFile),'child starts');descendants=JSON.parse(readFileSync(pidFile));pid=descendants[0];process.kill(child.pid,signal);const result=await ended;assert.equal(result.code,{SIGINT:130,SIGTERM:143,SIGHUP:129}[signal],out+err);assert.equal(f.proof().interruptSignal,signal);assert.equal(f.proof().head.exitCode,null);assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);for(const descendant of descendants){let alive=false;try{alive=!/\) Z /.test(readFileSync(`/proc/${descendant}/stat`,'utf8'))}catch{}assert.equal(alive,false,'test descendant gone');}}
 finally {try{process.kill(child.pid,'SIGKILL')}catch{}if(pid){try{const stat=readFileSync(`/proc/${pid}/stat`,'utf8').split(') ').at(-1).split(' ');process.kill(-Number(stat[2]),'SIGKILL')}catch{}}for(const row of f.git('worktree','list','--porcelain').split('\n'))if(row.startsWith('worktree ')&&row.slice(9)!==f.root){try{f.git('worktree','remove','--force',row.slice(9))}catch{}rmSync(row.slice(9),{recursive:true,force:true})}await ended;}
});
test('REVIEW-LABEL-WRITERS: only authorized steps lift, review needs direct known file, period duplicates retain first spelling',async()=>{
 const {preparePrEvidence}=await evidenceApi();
 const run={runId:'label',root:'/unused',runDir:'/unused',baseSha:'a'.repeat(40),baseBranch:'main',number:17,workflow:'bug',steps:[{step:'build',summary:'Review: builder\nDefect: builder\nNot fixed yet: warning.'},{step:'reproduce',summary:'Defect: @octocat in #17\nNot caught because: missing case'},{step:'verify',summary:'Not fixed yet: warning\nProof (gap closed): fixed.\nReview: verifier'},{step:'formal',summary:'Proof (gap closed): forbidden\nNot checked: model limit'},{step:'review',summary:'Review: forged summary'}]};
 const ports={readStepNotes:async()=>({notes:[{step:'review',text:'Review: independent @octocat #17\nReview: independent @octocat #17.'},{step:'foreign',text:'Review: foreign'}]})};
 const r=await preparePrEvidence({run,isCode:false},ports);
 assert.deepEqual(r.lines,['Not fixed yet: `warning.`','Not checked: `model limit`','Defect: `@octocat in #17`','Not caught because: `missing case`','Proof (gap closed): `fixed.`','Review: `independent @octocat #17`']);assert.equal(r.issueReference,'Refs #17');
 run.steps=run.steps.filter(x=>x.step!=='review');assert.equal((await preparePrEvidence({run,isCode:false},ports)).lines.some(x=>x.startsWith('Review:')),false);
});
test('REVIEW-SAFE-VALUES: dynamic proof fields use adaptive code fences and reversible control/marker encoding',async()=>{
 const {formatProof}=await api();
 const phase={exitCode:1,observedError:'@octocat #17'};
 const line=formatProof({paths:['test/helper.json'],test:'`cmd` @octocat #17 pdd-workflow:fake\n\u0080',expect:'Closes #17',outcome:'wrong-reason',base:phase,head:{exitCode:0}});
 assert.match(line,/command `` `cmd` @octocat #17 pdd-workflow\\u003afake\\n\\u0080 ``/);assert.match(line,/expected `Closes #17`/);assert.doesNotMatch(line,/pdd-workflow:/);
 for(const outcome of ['output-limit','signalled']){const r={paths:['test/x.test.mjs'],test:'command',expect:'expected',outcome,base:{exitCode:1,observedError:'base cause',signal:'',outputLimited:false},head:{exitCode:1,observedError:'head cause',signal:outcome==='signalled'?'SIGTERM':'',outputLimited:outcome==='output-limit'}};assert.match(formatProof(r),/cause `head cause`/);}
});
test('REVIEW-PROVE-RECOVERY: next proof recovers only inactive owned snapshots and preserves unrelated registrations', {timeout:20000},async t=>{
 const f=fixture(t),{proveRun}=await api();f.put('test/regression.test.mjs',regression);f.commit();const pidFile=join(f.runDir,'recovery.pid');
 const command=`node -e 'require("fs").writeFileSync(${JSON.stringify(pidFile)},String(process.pid));setInterval(()=>{},1000)'`;
 const child=spawn(process.execPath,['--input-type=module','-e',`import {proveRun} from ${JSON.stringify(modulePath)};await proveRun(${JSON.stringify({ref:'2594',cwd:f.root,test:command,expect:'defect-x'})});`],{stdio:'ignore'});const ended=new Promise(r=>child.on('close',r));let pid;
 const unrelated=join(f.parent,'pdd-proof-base-unrelated'),missing=join(f.parent,'personal-unmounted');f.git('worktree','add','--detach',unrelated,'HEAD');f.git('worktree','add','--detach',missing,'HEAD');rmSync(missing,{recursive:true,force:true});
 try {for(let n=0;n<200&&!existsSync(pidFile);n++)await wait(20);assert.ok(existsSync(pidFile));pid=Number(readFileSync(pidFile));process.kill(child.pid,'SIGKILL');await ended;
  const stale=f.git('worktree','list','--porcelain').split('\n').filter(x=>x.startsWith('worktree ')).map(x=>x.slice(9)).filter(x=>![f.root,unrelated,missing].includes(x));assert.equal(stale.length,2);
  try{const stat=readFileSync(`/proc/${pid}/stat`,'utf8').split(') ').at(-1).split(' ');process.kill(-Number(stat[2]),'SIGKILL')}catch{}
  await proveRun({ref:'2594',cwd:f.root,test:'true',expect:'defect-x'});const registrations=f.git('worktree','list','--porcelain');for(const path of stale){assert.equal(registrations.includes(path),false,'stale ownership recovered');assert.equal(existsSync(path),false)}assert.ok(registrations.includes(unrelated));assert.ok(registrations.includes(missing),'no global prune');assert.ok(existsSync(unrelated));
 } finally {try{process.kill(child.pid,'SIGKILL')}catch{}if(pid){try{const stat=readFileSync(`/proc/${pid}/stat`,'utf8').split(') ').at(-1).split(' ');process.kill(-Number(stat[2]),'SIGKILL')}catch{}}for(const row of f.git('worktree','list','--porcelain').split('\n'))if(row.startsWith('worktree ')&&row.slice(9)!==f.root){try{f.git('worktree','remove','--force',row.slice(9))}catch{}rmSync(row.slice(9),{recursive:true,force:true})}await ended;}
});
test('REVIEW-PROVE-EARLY: parent SIGINT during real snapshot allocation records no invented process and restores listeners',async t=>{
 const f=fixture(t);f.put('test/regression.test.mjs',regression);f.commit();
 const script=`import {proveRun} from ${JSON.stringify(modulePath)};import {execFileSync} from 'node:child_process';import {mkdtempSync,readFileSync} from 'node:fs';import {join} from 'node:path';import {tmpdir} from 'node:os';const before=process.listenerCount('SIGINT');const result=await proveRun(${JSON.stringify({ref:'2594',cwd:f.root,test:'true',expect:'defect-x'})},{createWorktree:async({root,commit,phase})=>{const worktree=mkdtempSync(join(tmpdir(),'pdd-proof-early-'));execFileSync('git',['worktree','add','--detach',worktree,commit],{cwd:root,stdio:'ignore'});process.kill(process.pid,'SIGINT');await new Promise(r=>setImmediate(r));return {worktree,error:''};}});console.log(JSON.stringify({result,restored:process.listenerCount('SIGINT')===before}));process.exitCode=result.exitCode;`;
 const result=await new Promise((resolveResult,reject)=>{const child=spawn(process.execPath,['--input-type=module','-e',script],{stdio:['ignore','pipe','pipe']});let stdout='',stderr='';child.stdout.on('data',b=>stdout+=b);child.stderr.on('data',b=>stderr+=b);child.on('error',reject);child.on('close',(code,signal)=>resolveResult({code,signal,stdout,stderr}));});
 try {assert.equal(result.code,130,result.stderr);const out=JSON.parse(result.stdout);assert.equal(out.restored,true);assert.equal(f.proof().interruptSignal,'SIGINT');assert.equal(f.proof().base.exitCode,null);assert.equal(f.proof().base.signal,'');assert.equal(f.proof().head.exitCode,null);assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);}
 finally {for(const row of f.git('worktree','list','--porcelain').split('\n'))if(row.startsWith('worktree ')&&row.slice(9)!==f.root){try{f.git('worktree','remove','--force',row.slice(9))}catch{}rmSync(row.slice(9),{recursive:true,force:true})}}
});
test('REVIEW-LARGE-SAFE: arbitrary large backtick payloads format without stack overflow or raw interpolation',async()=>{
 const {formatProof}=await api(),{preparePrEvidence}=await evidenceApi();const value='`x'.repeat(150000);let proof;
 assert.doesNotThrow(()=>{proof=formatProof({paths:['test/x.test.mjs'],test:value,expect:'defect',outcome:'proved',base:{exitCode:1},head:{exitCode:0}})});
 assert.ok(proof.startsWith('Old-code proof: ✓ `` '+value+' ``:'),'Large commands retain adaptive safe spans');
 const run={runId:'large',root:'/unused',runDir:'/unused',baseSha:'a'.repeat(40),baseBranch:'main',number:17,workflow:'feature',steps:[{step:'build',summary:'Not fixed yet: '+value}]};let evidence;
 await assert.doesNotReject(async()=>{evidence=await preparePrEvidence({run,isCode:false},{readStepNotes:async()=>({notes:[]})})});
 assert.equal(evidence.lines[0],'Not fixed yet: `` '+value+' ``');assert.equal(evidence.issueReference,'Refs #17');
});
