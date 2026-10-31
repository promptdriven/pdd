import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join,resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
import {spawnSync,execFileSync} from 'node:child_process';
import {Readable} from 'node:stream';
const root=resolve(process.env.PDD_TEST_SOURCE_ROOT || new URL('../',import.meta.url).pathname);
const load=p=>import(pathToFileURL(join(root,p)));
const {fixture}=await load('test/helpers/workflow-delivery-fixture.mjs');
const {harbor,PLACE,sink}=await load('test/runtime-fake.mjs');
const {runApprove}=await load('src/prompt-approve.mjs');
const {stepDone,approveRun}=await load('src/workflow-runner.mjs');
const {proseSha256}=await load('src/runtime-preflight.mjs');
const {preparePrEvidence}=await load('src/workflow-pr-evidence.mjs');
const pports=extra=>({stdout:sink(),stderr:sink(),stdin:Readable.from([]),interactive:false,env:{CODEX_THREAD_ID:'synthetic-lead'},...extra});
const draft=(repo,path=PLACE)=>{const text=fs.readFileSync(join(root,'test/fixtures/harbor',PLACE),'utf8').replace('"status": "approved"','"status": "draft"');fs.mkdirSync(join(repo,'prompts'),{recursive:true});fs.writeFileSync(join(repo,path),text);return text;};
const journal=repo=>join(execFileSync('git',['rev-parse','--path-format=absolute','--git-common-dir'],{cwd:repo,encoding:'utf8'}).trim(),'pdd/approvals.json');
async function ready(t){
 const f=await fixture(t,{name:'feature'});assert.equal((await f.run()).exitCode,0);const r=f.record();
 const selected=['prompts/a.prompt.md','prompts/b.prompt.md'];for(const path of selected)draft(r.root,path);
 for(const step of ['understand','visual','prompt-story']){f.tick();const out=await stepDone({step,summary:'Review these drafts',cwd:r.root},f.agentPorts());assert.equal(out.exitCode,0,out.message);}
 f.herdr.idle();return {f,r:f.record(),selected};
}
for(const route of ['standalone','workflow'])test(`LEAD shell quoted heredoc ${route} preserves literal commands and trailing newlines`,async t=>{
 const f=route==='standalone'?harbor(t):(await ready(t)).f;
 const repo=route==='standalone'?f.repo:f.record().root;if(route==='standalone')draft(repo);
 const home=route==='standalone'?f.home:join(f.base,'home');const tools=join(home,'fake-bin');fs.mkdirSync(tools);
 // Any external chat request stops locally after approval is recorded. Never contact a real Herdr server.
 fs.writeFileSync(join(tools,'herdr'),'#!/bin/sh\nexit 1\n',{mode:0o755});
 const canary=join(home,'must-not-run');const words='yes, `touch '+canary+'` $(touch '+canary+') "double" \'single\'\nsecond line\n\n';
 const quote=s=>"'"+s.replaceAll("'","'\\''")+"'";
 const argv=route==='standalone'?'approve '+quote(PLACE):'workflow approve 17';
 const command=quote(process.execPath)+' '+quote(join(root,'bin/pdd.mjs'))+' '+argv+" --said - <<'PDD_SAID'\n"+words+'PDD_SAID\n';
 const out=spawnSync('/bin/sh',['-c',command],{cwd:repo,env:{PATH:tools+':'+process.env.PATH,HOME:home,CLAUDE_CONFIG_DIR:join(home,'.claude'),PDD_AGENT_SESSION:'1'},encoding:'utf8',timeout:20000});
 assert.equal(out.error,undefined,'shell route completes');assert.equal(fs.existsSync(canary),false,'person text must never execute');
 const saved=JSON.parse(fs.readFileSync(journal(repo),'utf8'));assert.equal(saved.approvals.at(-1).words,words,'stdin payload is exact, including final blank line');
 if(route==='standalone')assert.equal(out.status,0,out.stderr);
});
for(const route of ['standalone','workflow'])for(const mode of ['strict','blank','bad-config'])test(`LEAD ${route} dash ${mode} refuses without mutation`,async t=>{
 const data=route==='standalone'?{f:harbor(t)}:await ready(t), f=data.f, repo=route==='standalone'?f.repo:data.r.root;
 if(route==='standalone')draft(repo);
 if(mode!=='blank')fs.writeFileSync(join(repo,'pdd.json'),mode==='strict'?'{"strict_approvals":true}':'{bad json');
 let reads=0;const stdin={async *[Symbol.asyncIterator](){reads++;yield ' \n\n';}};
 const before=fs.readFileSync(join(repo,route==='standalone'?PLACE:data.selected[0]),'utf8');
 const out=route==='standalone'?await runApprove({words:[PLACE],cwd:repo,said:'-'},pports({stdin})):await approveRun({ref:'17',cwd:repo,said:'-'},f.agentPorts({stdin}));
 assert.notEqual(typeof out==='number'?out:out.exitCode,0);assert.equal(fs.readFileSync(join(repo,route==='standalone'?PLACE:data.selected[0]),'utf8'),before);assert.equal(fs.existsSync(journal(repo)),false);
 if(mode!=='blank')assert.equal(reads,0,'policy/config refusal occurs before reading stdin');
 if(route==='workflow')assert.equal(f.record().gate.id,data.r.gate.id);
});
for(const change of ['prose','added','removed'])test(`LEAD bound gate refuses ${change} drift and accepts only after re-show`,async t=>{
 const {f,r,selected}=await ready(t),path=join(r.root,selected[0]);
 if(change==='prose')fs.appendFileSync(path,'\nDifferent reviewed prose.\n');if(change==='added')draft(r.root,'prompts/c.prompt.md');if(change==='removed')fs.unlinkSync(path);
 const before=fs.readFileSync(join(r.runDir,'status.json'),'utf8');const out=await approveRun({ref:'17',cwd:r.root,said:'looks good'},f.agentPorts());
 assert.equal(out.exitCode,1,'changed review must be refused');assert.match(out.message,/show.*gate.*again/i);assert.equal(fs.readFileSync(join(r.runDir,'status.json'),'utf8'),before);assert.equal(fs.existsSync(journal(r.root)),false);
 const shown=await stepDone({step:'prompt-story',summary:'Show the changed review again',cwd:r.root},f.agentPorts());assert.equal(shown.exitCode,0,shown.message);f.herdr.idle();
 const approved=await approveRun({ref:'17',cwd:r.root,said:'approve this new review'},f.agentPorts());assert.equal(approved.exitCode,0,approved.message);
});
test('LEAD one terminal answer lists and approves gate and both draft hashes',async t=>{
 const {f,r,selected}=await ready(t);let answers=0;const display=[];
 const out=await approveRun({ref:'17',cwd:r.root},{...f.ports,say:text=>display.push(text),confirm:async question=>{answers++;display.push(question);return true;}});
 assert.equal(out.exitCode,0,out.message);assert.equal(answers,1,'one answer covers the complete batch');
 for(const path of selected){const text=fs.readFileSync(join(r.root,path),'utf8');assert.match(text,/"status": "approved"/);assert.ok(display.join('\n').includes(path));assert.ok(display.join('\n').includes(proseSha256(text)));}
 const saved=JSON.parse(fs.readFileSync(journal(r.root),'utf8'));assert.equal(saved.approvals.length,1);assert.equal(saved.approvals[0].prompts.length,2);assert.equal(saved.approvals[0].route,'terminal');
});
for(const bad of ['malformed','symlink'])test(`LEAD preservation ${bad} selected prompt never mutates another draft`,async t=>{
 const {f,r,selected}=await ready(t),good=fs.readFileSync(join(r.root,selected[0]),'utf8'),target=join(r.root,selected[1]);
 if(bad==='malformed')fs.writeFileSync(target,'<details><summary>Runtime interface</summary>\n```json\n{broken}\n```\n</details>\n');
 else{fs.unlinkSync(target);fs.symlinkSync(join(r.root,selected[0]),target);}
 const out=await approveRun({ref:'17',cwd:r.root,said:'approve'},f.agentPorts());assert.equal(out.exitCode,1);assert.equal(fs.readFileSync(join(r.root,selected[0]),'utf8'),good);assert.equal(f.record().area,r.area);assert.equal(fs.existsSync(journal(r.root)),false);
});
test('LEAD preservation approval words use adaptive code spans with ISO timestamp and separate top block',async()=>{
 const words='yes ```` @person #17\n"quoted"';const evidence={id:'synthetic-event',route:'said',actor:{kind:'agent',id:'synthetic'},at:1700000000000,words,prompts:[]};
 const out=await preparePrEvidence({run:{workflow:'feature',number:17,steps:[],decisions:[{decision:'approve',evidence}]},isCode:false},{readStepNotes:async()=>({notes:[]})});
 assert.deepEqual(out.lines,[],'approval must not displace Runtime/verdict top lines');assert.equal(out.approvalLines.length,1);const line=out.approvalLines[0];assert.ok(line.includes('2023-11-14T22:13:20.000Z'));
 const match=line.match(/(`{5,})\s*("yes ```` @person #17\\n\\"quoted\\"")\s*\1/);assert.ok(match,'JSON-quoted complete words stay inside an adaptive span longer than interior backticks');assert.equal(JSON.parse(match[2]),words);
});
test('LEAD current target checkout is the common policy authority for both commands',async t=>{
 const {f,r,selected}=await ready(t);fs.writeFileSync(join(f.source,'pdd.json'),'{"strict_approvals":true}');
 const out=await approveRun({ref:'17',cwd:f.source,said:'approve target checkout'},f.agentPorts());assert.equal(out.exitCode,0,out.message);
 const single=harbor(t);draft(single.repo);fs.mkdirSync(join(single.repo,'nested'));fs.writeFileSync(join(single.repo,'nested/pdd.json'),'{"strict_approvals":true}');
 const code=await runApprove({words:['../'+PLACE],cwd:join(single.repo,'nested'),said:'approve target checkout'},pports());assert.equal(code,0);
});
test('LEAD unbound legacy gate refuses said without effects',async t=>{
 const {f,r}=await ready(t);const {writeRun}=await load('src/workflow-runs.mjs');delete r.gate.promptSnapshot;writeRun(r,f.ports);
 const before=fs.readFileSync(join(r.runDir,'status.json'),'utf8');const out=await approveRun({ref:'17',cwd:r.root,said:'approve'},f.agentPorts());assert.equal(out.exitCode,1);assert.match(out.message,/show.*gate.*again/i);assert.equal(fs.readFileSync(join(r.runDir,'status.json'),'utf8'),before);assert.equal(fs.existsSync(journal(r.root)),false);
});
test('LEAD stale journal lock reclaims only after its actual local owner dies',async t=>{
 const {spawn}=await import('node:child_process');const {once}=await import('node:events');const {recordPromptApproval}=await load('src/approval-policy.mjs');const f=harbor(t);
 const commonDir=execFileSync('git',['rev-parse','--path-format=absolute','--git-common-dir'],{cwd:f.repo,encoding:'utf8'}).trim();
 const evidence={id:'child',route:'said',actor:{kind:'agent',id:'synthetic'},at:1700000000000,words:'approve',prompts:[]};
 const script=`const fs=await import('node:fs');const {recordPromptApproval}=await import(${JSON.stringify(pathToFileURL(join(root,'src/approval-policy.mjs')).href)});await recordPromptApproval(${JSON.stringify({commonDir,evidence})},{fs:{...fs,renameSync(a,b){if(b.endsWith('approvals.json')){process.send('ready');Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0);}return fs.renameSync(a,b);}}});`;
 const child=spawn(process.execPath,['--input-type=module','-e',script],{stdio:['ignore','ignore','pipe','ipc']});t.after(()=>child.kill('SIGKILL'));
 await Promise.race([once(child,'message'),new Promise((_,reject)=>setTimeout(()=>reject(Error('owned lock producer did not reach journal rename')),10000).unref())]);
 const lock=join(commonDir,'pdd/approvals.lock');const before=fs.readdirSync(lock).map(name=>[name,fs.readFileSync(join(lock,name),'utf8')]);
 await assert.rejects(recordPromptApproval({commonDir,evidence:{...evidence,id:'live-probe'}}),/busy|saving|lock/i);assert.deepEqual(fs.readdirSync(lock).map(name=>[name,fs.readFileSync(join(lock,name),'utf8')]),before,'alive owner remains untouched');
 const exited=once(child,'exit');child.kill('SIGKILL');await exited;
 let failure;try{await recordPromptApproval({commonDir,evidence:{...evidence,id:'after-death'}});}catch(error){failure=error;}
 assert.equal(failure,undefined,'dead local owner is reclaimable through public journal API');assert.equal(JSON.parse(fs.readFileSync(journal(f.repo),'utf8')).approvals.at(-1).id,'after-death');
});
test('LEAD preservation unverifiable legacy empty lock is not reclaimed',async t=>{
 const {recordPromptApproval}=await load('src/approval-policy.mjs');const f=harbor(t);const commonDir=execFileSync('git',['rev-parse','--path-format=absolute','--git-common-dir'],{cwd:f.repo,encoding:'utf8'}).trim();fs.mkdirSync(join(commonDir,'pdd/approvals.lock'),{recursive:true});
 await assert.rejects(recordPromptApproval({commonDir,evidence:{id:'probe',route:'said',actor:{kind:'agent',id:'synthetic'},at:1700000000000,words:'approve',prompts:[]}}),/busy|saving|lock/i);assert.equal(fs.existsSync(join(commonDir,'pdd/approvals.lock')),true);assert.equal(fs.existsSync(journal(f.repo)),false);
});
for(const mode of ['foreign','unverifiable','permission-denied'])test(`LEAD preservation ${mode} lock owner is never reclaimed`,async t=>{
 const {spawn}=await import('node:child_process');const {once}=await import('node:events');const {recordPromptApproval}=await load('src/approval-policy.mjs');const f=harbor(t);
 const commonDir=execFileSync('git',['rev-parse','--path-format=absolute','--git-common-dir'],{cwd:f.repo,encoding:'utf8'}).trim();
 const evidence={id:'lock-owner',route:'said',actor:{kind:'agent',id:'synthetic'},at:1700000000000,words:'approve',prompts:[]};
 const script=`const fs=await import('node:fs');const {recordPromptApproval}=await import(${JSON.stringify(pathToFileURL(join(root,'src/approval-policy.mjs')).href)});await recordPromptApproval(${JSON.stringify({commonDir,evidence})},{${mode==='foreign'?"hostname:'synthetic-foreign-host',":''}fs:{...fs,renameSync(a,b){if(b.endsWith('approvals.json')){process.send('ready');Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0);}return fs.renameSync(a,b);}}});`;
 const child=spawn(process.execPath,['--input-type=module','-e',script],{stdio:['ignore','ignore','pipe','ipc']});t.after(()=>child.kill('SIGKILL'));
 await Promise.race([once(child,'message'),new Promise((_,reject)=>setTimeout(()=>reject(Error('owned lock producer did not reach journal rename')),10000).unref())]);
 const lock=join(commonDir,'pdd/approvals.lock'),before=fs.readdirSync(lock).map(name=>[name,fs.readFileSync(join(lock,name),'utf8')]);
 const exited=once(child,'exit');child.kill('SIGKILL');await exited;
 const processIdentity=mode==='foreign'?()=>({alive:false}):mode==='unverifiable'?()=>({alive:undefined}):()=>{throw Object.assign(Error('denied'),{code:'EPERM'});};
 await assert.rejects(recordPromptApproval({commonDir,evidence:{...evidence,id:'probe'}},{processIdentity}),/busy|saving|lock/i);
 assert.deepEqual(fs.readdirSync(lock).map(name=>[name,fs.readFileSync(join(lock,name),'utf8')]),before);assert.equal(fs.existsSync(journal(f.repo)),false);
});
