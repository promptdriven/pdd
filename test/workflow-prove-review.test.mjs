import './helpers/test-home.mjs';
import {spawnOwned} from './helpers/owned-process.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {execFileSync,spawn} from 'node:child_process';
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync,realpathSync,existsSync,symlinkSync} from 'node:fs';
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
for(const signal of ['SIGINT','SIGTERM','SIGHUP']) test(`REVIEW-PROVE-INTERRUPT-${signal}: actual parent signal kills descendants and removes both snapshots`, {timeout:20000,skip:process.platform!=='linux'},async t=>{
 const f=fixture(t);f.put('test/regression.test.mjs',regression);f.commit();const pidFile=join(f.runDir,'child.pid');
 const childScript=`const grandchild=require("child_process").spawn(process.execPath,["-e",'process.on("SIGTERM",()=>{});setInterval(()=>{},1000)'],{stdio:"ignore"});process.on("SIGTERM",()=>{});const fs=require("fs");fs.writeFileSync(${JSON.stringify(pidFile+".tmp")},JSON.stringify([process.pid,grandchild.pid]));fs.renameSync(${JSON.stringify(pidFile+".tmp")},${JSON.stringify(pidFile)});setInterval(()=>{},1000)`;
 const command=`node -e '${childScript.replaceAll("'", "'\\''")}'`;
 const script=`import {proveRun} from ${JSON.stringify(modulePath)};const r=await proveRun(${JSON.stringify({ref:'2594',cwd:f.root,test:command,expect:'defect-x'})});console.log(JSON.stringify(r));process.exitCode=r.exitCode;`;
 const owned=spawnOwned(script),{child,ended}=owned;let out='',err='';child.stdout.on('data',s=>out+=s);child.stderr.on('data',s=>err+=s);
 let pid,descendants=[];
 try {for(let n=0;n<200&&!descendants.length;n++){try{descendants=JSON.parse(readFileSync(pidFile))}catch{await wait(20)}}assert.equal(descendants.length,2,'child publishes its complete PID record');pid=descendants[0];process.kill(child.pid,signal);const result=await ended;assert.equal(result.code,{SIGINT:130,SIGTERM:143,SIGHUP:129}[signal],out+err);assert.equal(f.proof().interruptSignal,signal);assert.equal(f.proof().head.exitCode,null);assert.equal(f.git('worktree','list','--porcelain').split('worktree ').length,2);for(const descendant of descendants){let alive=false;try{alive=!/\) Z /.test(readFileSync(`/proc/${descendant}/stat`,'utf8'))}catch{}assert.equal(alive,false,'test descendant gone');}}
 finally {await owned.cleanup();for(const row of f.git('worktree','list','--porcelain').split('\n'))if(row.startsWith('worktree ')&&row.slice(9)!==f.root){try{f.git('worktree','remove','--force',row.slice(9))}catch{}rmSync(row.slice(9),{recursive:true,force:true})}await ended;}
});
test('REVIEW-LABEL-WRITERS: only authorized steps lift, review needs direct known file, period duplicates retain first spelling',async()=>{
 const {preparePrEvidence}=await evidenceApi();
 const run={runId:'label',root:'/unused',runDir:'/unused',baseSha:'a'.repeat(40),baseBranch:'main',number:17,workflow:'bug',steps:[{step:'build',summary:'Review: builder\nDefect: builder\nNot fixed yet: warning.'},{step:'reproduce',summary:'Defect: @octocat in #17\nNot caught because: missing case'},{step:'verify',summary:'Not fixed yet: warning\nProof (gap closed): fixed.\nReview: verifier'},{step:'formal',summary:'Proof (gap closed): forbidden\nNot checked: model limit'},{step:'review',summary:'Review: forged summary'}]};
 const ports={readStepNotes:async()=>({notes:[{step:'review',text:'Review: independent @octocat #17\nReview: independent @octocat #17.'},{step:'foreign',text:'Review: foreign'}]})};
 const r=await preparePrEvidence({run,isCode:false},ports);
 assert.deepEqual(r.lines,['Not fixed yet: `warning.`','Not checked: `model limit`','Defect: `@octocat in #17`','Not caught because: `missing case`','Proof (gap closed): `fixed.`','Review: `independent @octocat #17`'].map(line=>'Agent note — not checked by pdd: '+line));assert.equal(r.issueReference,'Refs #17');
 run.steps=run.steps.filter(x=>x.step!=='review');assert.equal((await preparePrEvidence({run,isCode:false},ports)).lines.some(x=>x.startsWith('Agent note — not checked by pdd: Review:')),false);
});
test('REVIEW-SAFE-VALUES: dynamic proof fields use adaptive code fences and reversible control/marker encoding',async()=>{
 const {formatProof}=await api();
 const phase={exitCode:1,observedError:'@octocat #17'};
 const line=formatProof({paths:['test/helper.json'],test:'`cmd` @octocat #17 pdd-workflow:fake\n\u0080',expect:'Closes #17',outcome:'wrong-reason',base:phase,head:{exitCode:0}});
 assert.match(line,/command `` `cmd` @octocat #17 pdd-workflow\\u003afake\\n\\u0080 ``/);assert.match(line,/expected `Closes #17`/);assert.doesNotMatch(line,/pdd-workflow:/);
 for(const outcome of ['output-limit','signalled']){const r={paths:['test/x.test.mjs'],test:'command',expect:'expected',outcome,base:{exitCode:1,observedError:'base cause',signal:'',outputLimited:false},head:{exitCode:1,observedError:'head cause',signal:outcome==='signalled'?'SIGTERM':'',outputLimited:outcome==='output-limit'}};assert.match(formatProof(r),/cause `head cause`/);}
});
test('REVIEW-PROVE-RECOVERY: next proof recovers only inactive owned snapshots and preserves unrelated registrations', {timeout:20000,skip:process.platform!=='linux'},async t=>{
 const f=fixture(t),{proveRun}=await api();f.put('test/regression.test.mjs',regression);f.commit();const pidFile=join(f.runDir,'recovery.pid');
 const realTemp=join(f.parent,'proof-temp'),aliasTemp=join(f.parent,'proof-temp-alias');mkdirSync(realTemp);symlinkSync(realTemp,aliasTemp,'dir');
 const command=`node -e 'const fs=require("fs");fs.writeFileSync(${JSON.stringify(pidFile+".tmp")},String(process.pid));fs.renameSync(${JSON.stringify(pidFile+".tmp")},${JSON.stringify(pidFile)});setInterval(()=>{},1000)'`;
 const owned=spawnOwned(`import {proveRun} from ${JSON.stringify(modulePath)};await proveRun(${JSON.stringify({ref:'2594',cwd:f.root,test:command,expect:'defect-x'})});`,{env:{...process.env,TMPDIR:aliasTemp}}),{child,ended}=owned;let pid;
 const unrelated=join(f.parent,'pdd-proof-base-unrelated'),missing=join(f.parent,'personal-unmounted');f.git('worktree','add','--detach',unrelated,'HEAD');f.git('worktree','add','--detach',missing,'HEAD');rmSync(missing,{recursive:true,force:true});
 try {for(let n=0;n<200&&!(pid>0);n++){try{pid=Number(readFileSync(pidFile,'utf8'))}catch{}if(!(pid>0))await wait(20)}assert.ok(Number.isInteger(pid)&&pid>0,'child publishes its complete PID');process.kill(child.pid,'SIGKILL');await ended;
  const stale=f.git('worktree','list','--porcelain').split('\n').filter(x=>x.startsWith('worktree ')).map(x=>x.slice(9)).filter(x=>![f.root,unrelated,missing].includes(x));assert.equal(stale.length,2);
  await owned.cleanup();
  await proveRun({ref:'2594',cwd:f.root,test:'true',expect:'defect-x'});const registrations=f.git('worktree','list','--porcelain');for(const path of stale){assert.equal(registrations.includes(path),false,'stale ownership recovered');assert.equal(existsSync(path),false)}assert.ok(registrations.includes(unrelated));assert.ok(registrations.includes(missing),'no global prune');assert.ok(existsSync(unrelated));
 } finally {await owned.cleanup();for(const row of f.git('worktree','list','--porcelain').split('\n'))if(row.startsWith('worktree ')&&row.slice(9)!==f.root){try{f.git('worktree','remove','--force',row.slice(9))}catch{}rmSync(row.slice(9),{recursive:true,force:true})}await ended;}
});
for(const record of ['missing','empty','partial','malformed']) test(`REVIEW-PROVE-CLEANUP-${record}: real proof descendants stop without a complete PID record`,{timeout:20000,skip:process.platform!=='linux'},async t=>{
 const f=fixture(t);f.put('test/regression.test.mjs',regression);f.commit();
 const observed=join(f.runDir,'observed.json'),pidFile=join(f.runDir,'unreliable.pid');
 const nested=`const fs=require('fs');const {spawn}=require('child_process');const grand=spawn(process.execPath,['-e','process.on("SIGTERM",()=>{});setInterval(()=>{},1000)'],{stdio:'ignore'});fs.writeFileSync(${JSON.stringify(observed)},JSON.stringify([process.pid,grand.pid]));${record==='missing'?'':`fs.writeFileSync(${JSON.stringify(pidFile)},${JSON.stringify(record==='empty'?'':record==='partial'?'[':'not json')});`}process.on('SIGTERM',()=>{});setInterval(()=>{},1000)`;
 const command=`node -e '${nested.replaceAll("'", "'\\''")}'`;
 const owned=spawnOwned(`import {proveRun} from ${JSON.stringify(modulePath)};await proveRun(${JSON.stringify({ref:'2594',cwd:f.root,test:command,expect:'defect-x'})});`),{child,ended}=owned;
 let pids=[];
 try{for(let n=0;n<200&&!pids.length;n++){try{pids=JSON.parse(readFileSync(observed))}catch{}if(!pids.length)await wait(20)}assert.equal(pids.length,2);process.kill(child.pid,'SIGKILL');await ended;await owned.cleanup();for(const pid of pids){let alive=false;try{alive=!/\) Z /.test(readFileSync(`/proc/${pid}/stat`,'utf8'))}catch{}assert.equal(alive,false,`descendant ${pid} stopped`);}assert.doesNotThrow(()=>process.kill(process.pid,0));}
 finally{try{await owned.cleanup()}finally{for(const pid of pids)try{process.kill(pid,'SIGKILL')}catch{}}for(const row of f.git('worktree','list','--porcelain').split('\n'))if(row.startsWith('worktree ')&&row.slice(9)!==f.root){try{f.git('worktree','remove','--force',row.slice(9))}catch{}rmSync(row.slice(9),{recursive:true,force:true})}}
});
test('REVIEW-PROVE-CLEANUP-TIMEOUT: cleanup stops an unready proof without touching an unrelated process',{timeout:20000,skip:process.platform!=='linux'},async t=>{
 const f=fixture(t);f.put('test/regression.test.mjs',regression);f.commit();const observed=join(f.runDir,'started'),ready=join(f.runDir,'late');
 const code=`const fs=require('fs');fs.writeFileSync(${JSON.stringify(observed)},String(process.pid));setTimeout(()=>fs.writeFileSync(${JSON.stringify(ready)},'ready'),10000);process.on('SIGTERM',()=>{});setInterval(()=>{},1000)`;
 const command=`node -e '${code.replaceAll("'", "'\\''")}'`;
 const owned=spawnOwned(`import {proveRun} from ${JSON.stringify(modulePath)};await proveRun(${JSON.stringify({ref:'2594',cwd:f.root,test:command,expect:'defect-x'})});`);
 const unrelated=spawn(process.execPath,['-e','setInterval(()=>{},1000)'],{stdio:'ignore'});let pid;
 try{await assert.rejects(async()=>{try{for(let n=0;n<100;n++){try{pid=Number(readFileSync(observed))}catch{}if(existsSync(ready))return;await wait(20)}throw Error('readiness timeout');}finally{await owned.cleanup();}},/readiness timeout/);assert.ok(pid,'proof command started before timeout');assert.doesNotThrow(()=>process.kill(unrelated.pid,0));let alive=false;try{alive=!/\) Z /.test(readFileSync(`/proc/${pid}/stat`,'utf8'))}catch{}assert.equal(alive,false);}
 finally{try{await owned.cleanup()}finally{try{process.kill(unrelated.pid,'SIGKILL')}catch{}if(pid)try{process.kill(pid,'SIGKILL')}catch{}}for(const row of f.git('worktree','list','--porcelain').split('\n'))if(row.startsWith('worktree ')&&row.slice(9)!==f.root){try{f.git('worktree','remove','--force',row.slice(9))}catch{}rmSync(row.slice(9),{recursive:true,force:true})}}
});
test('REVIEW-PROVE-CLEANUP-LEADER: a retained proof group survives its leader',{timeout:20000,skip:process.platform!=='linux'},async t=>{
 const f=fixture(t);f.put('test/regression.test.mjs',regression);f.commit();const observed=join(f.runDir,'leader.json');
 const code=`const fs=require('fs');const p=require('child_process').spawn(process.execPath,['-e','process.on("SIGTERM",()=>{});setInterval(()=>{},1000)'],{stdio:'ignore'});fs.writeFileSync(${JSON.stringify(observed)},JSON.stringify([process.pid,p.pid]));setInterval(()=>{},1000)`;
 const command=`node -e '${code.replaceAll("'", "'\\''")}'`;
 const owned=spawnOwned(`import {proveRun} from ${JSON.stringify(modulePath)};await proveRun(${JSON.stringify({ref:'2594',cwd:f.root,test:command,expect:'defect-x'})});`);let pids=[];
 try{for(let n=0;n<200&&!pids.length;n++){try{pids=JSON.parse(readFileSync(observed))}catch{}if(!pids.length)await wait(20)}assert.equal(pids.length,2);const fields=readFileSync(`/proc/${pids[0]}/stat`,'utf8').split(') ').at(-1).split(' ');const leader=Number(fields[2]);process.kill(leader,'SIGKILL');process.kill(owned.child.pid,'SIGKILL');await owned.ended;await owned.cleanup();for(const pid of pids){let alive=false;try{alive=!/\) Z /.test(readFileSync(`/proc/${pid}/stat`,'utf8'))}catch{}assert.equal(alive,false);}}
 finally{try{await owned.cleanup()}finally{for(const pid of pids)try{process.kill(pid,'SIGKILL')}catch{}}}
});
test('REVIEW-PROVE-CLEANUP-LAUNCH: owner dies as the proof command starts before PID publication',{timeout:20000,skip:process.platform!=='linux'},async t=>{
 const f=fixture(t);f.put('test/regression.test.mjs',regression);f.commit();const observed=join(f.runDir,'launch.pid');
 const script=`import {proveRun} from ${JSON.stringify(modulePath)};const command=\`node -e 'process.kill(\${process.pid},"SIGKILL");require("fs").writeFileSync(${JSON.stringify(observed)},String(process.pid));setInterval(()=>{},1000)'\`;await proveRun({ref:'2594',cwd:${JSON.stringify(f.root)},test:command,expect:'defect-x'});`;
 const owned=spawnOwned(script);let pid;
 try{await owned.ended;for(let n=0;n<200&&!pid;n++){try{pid=Number(readFileSync(observed,'utf8'))}catch{}if(!pid)await wait(20)}assert.ok(pid,'proof command ran after killing its owner');await owned.cleanup();let alive=false;try{alive=!/\) Z /.test(readFileSync(`/proc/${pid}/stat`,'utf8'))}catch{}assert.equal(alive,false);}
 finally{try{await owned.cleanup()}finally{if(pid)try{process.kill(pid,'SIGKILL')}catch{}}}
});
test('REVIEW-PROVE-CLEANUP-EARLY: cleanup prevents a later proof spawn',{timeout:20000,skip:process.platform!=='linux'},async t=>{
 const marker=join(mkdtempSync(join(tmpdir(),'pdd-owned-')),'late');t.after(()=>rmSync(dirname(marker),{recursive:true,force:true}));
 const owned=spawnOwned(`import {spawn} from 'node:child_process';setTimeout(()=>spawn(process.execPath,['-e',${JSON.stringify(`require('fs').writeFileSync(${JSON.stringify(marker)},'late')`)}],{detached:true}),500);setInterval(()=>{},1000);`);
 await owned.cleanup();await wait(700);assert.equal(existsSync(marker),false);
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
 assert.equal(evidence.lines[0],'Agent note — not checked by pdd: Not fixed yet: `` '+value+' ``');assert.equal(evidence.issueReference,'Refs #17');
});
test('REVIEW-PROVE-COMMAND-DISPLAY: native shell command retains quotes and backslashes with visible controls',async t=>{
 const f=fixture(t),{proveRun,formatProof}=await api();f.put('src/value.mjs','export default true;');f.put('test/regression.test.mjs',regression);f.commit();
 const command='node -e "if(!require(\'fs\').readFileSync(\'src/value.mjs\',\'utf8\').includes(\'true\')){console.log(\'defect-x\\n\');process.exit(1)}"\n# pdd-workflow:fake `quoted`\t';
 const r=await proveRun({ref:'2594',cwd:f.root,test:command,expect:'defect-x'});
 assert.equal(r.exitCode,0,r.message);assert.equal(f.proof().test,command,'saved command remains exact');
 const span='``node -e "if(!require(\'fs\').readFileSync(\'src/value.mjs\',\'utf8\').includes(\'true\')){console.log(\'defect-x\\n\');process.exit(1)}"\\n# pdd-workflow\\u003afake `quoted`\\t``';
 assert.equal(r.message,'Old-code proof: ✓ '+span+': old-code exit `1`; output contains `defect-x`; new-code exit `0`.','command display must preserve literal quotes and backslashes');
 const line=formatProof({test:'"\\\0\b\t\n\f\r\x1f\x7f\x80\u2028\u2029',expect:'"\\',outcome:'wrong-reason',base:{exitCode:1,observedError:'"\\'},head:{exitCode:0}});
 assert.equal(line,'Old-code proof: ✗ wrong-reason; command `"\\\\u0000\\b\\t\\n\\f\\r\\u001f\\u007f\\u0080\\u2028\\u2029`; old-code exit `1`; new-code exit `0`; expected `\\"\\\\`; cause `\\"\\\\`.');
});
test('REVIEW-PROVE-TAP-TAIL: native TAP failure retains recent diagnostics instead of summary footer',async t=>{
 const f=fixture(t),{proveRun}=await api();
 f.put('test/regression.test.mjs',"console.log('TAP version 13\\nnot ok 1 - tap-tail-defect\\n  error: actual native diagnostic\\n  code: ERR_ASSERTION\\n  ...\\n1..1\\n# tests 1\\n# suites 0\\n# pass 0\\n# fail 1\\n# cancelled 0\\n# skipped 0\\n# todo 0\\n# duration_ms 1.25');process.exit(1);");f.commit();
 const r=await proveRun({ref:'2594',cwd:f.root,test:'node test/regression.test.mjs',expect:'tap-tail-defect'});
 assert.equal(r.exitCode,1);assert.equal(f.proof().outcome,'head-fails');assert.match(r.message,/cause `.*ERR_ASSERTION/);
 assert.ok(r.message.endsWith("; tail `  error: actual native diagnostic\\n  code: ERR_ASSERTION\\n  ...`."),'native TAP tail must retain failure diagnostic');
 assert.doesNotMatch(r.message,/; tail `[^`]*# (?:skipped|todo|duration_ms)/,'native TAP summary must not hide diagnostic');
 assert.ok(f.proof().head.stdoutTail.some(line=>line.startsWith('# duration_ms ')),'saved stream keeps original summary');
});
test('REVIEW-PROVE-TAP-BOUNDARIES: exact footer grammar, stderr priority, fallback and Unicode tail bound',async()=>{
 const {formatProof}=await api();
 const format=(stdoutTail,stderrTail=[],outcome='head-fails')=>formatProof({test:'run',expect:'defect',outcome,base:{exitCode:1,observedError:'old'},head:{exitCode:1,observedError:'diagnostic',stdoutTail,stderrTail}});
 const suffix=String.raw`; tail `;
 const message=format(['first','  diagnostic a  ','diagnostic b','diagnostic c','','  0..1  ','# tests 01','# suites 0','# pass 0','# fail 1','# cancelled 0','# skipped 0','# todo 0','# duration_ms 1.25','']);
 assert.ok(message.endsWith(suffix+'`  diagnostic a  \\ndiagnostic b\\ndiagnostic c`.'));
 assert.ok(format(['# tests 1','','# todo 0','# duration_ms 1']).endsWith(suffix+'`# tests 1\\n# todo 0\\n# duration_ms 1`.'));
 for(const line of ['# tests -1','# tests 1 extra','# duration_ms .5','# duration_ms 1.','# duration_ms -1','1..2 extra','# unknown 1'])assert.ok(format(['diagnostic',line,'# todo 0']).endsWith(suffix+'`diagnostic\\n'+line+'`.'));
 assert.ok(format(['diagnostic','# todo 0','ordinary final']).endsWith(suffix+'`diagnostic\\n# todo 0\\nordinary final`.'));
 assert.ok(format(['stdout diagnostic','# todo 0'],['stderr diagnostic','# todo 0']).endsWith(suffix+'`stderr diagnostic`.'));
 assert.ok(format(['diagnostic','# todo 0'],['','  ']).endsWith(suffix+'`diagnostic`.'));
 assert.ok(format(['😀'.repeat(241),'# todo 0']).endsWith(suffix+'`'+'😀'.repeat(240)+'`.'));
});
