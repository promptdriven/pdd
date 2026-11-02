import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join,resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
import {execFileSync} from 'node:child_process';
const root=resolve(process.env.PDD_TEST_SOURCE_ROOT || new URL('../',import.meta.url).pathname);
const load=p=>import(pathToFileURL(join(root,p)));
const {fixture}=await load('test/helpers/workflow-delivery-fixture.mjs');
const {harbor,PLACE}=await load('test/runtime-fake.mjs');
const {stepDone,approveRun,openRun,runStatus,changeRun}=await load('src/workflow-runner.mjs');
async function journalBoundary(){let policy;try{policy=await load('src/approval-policy.mjs');}catch(error){if(error.code!=='ERR_MODULE_NOT_FOUND')throw error;}assert.equal(typeof policy?.recordPromptApproval,'function','Required approval journal public contract is available');return policy;}
async function recordPromptApproval(...args){return (await journalBoundary()).recordPromptApproval(...args);}
async function readPromptApprovals(...args){return (await journalBoundary()).readPromptApprovals(...args);}
const draft=repo=>{const text=fs.readFileSync(join(root,'test/fixtures/harbor',PLACE),'utf8').replace('"status": "approved"','"status": "draft"');fs.mkdirSync(join(repo,'prompts'),{recursive:true});fs.writeFileSync(join(repo,PLACE),text);};
async function ready(t){const f=await fixture(t,{name:'feature'});assert.equal((await f.run()).exitCode,0);draft(f.record().root);for(const step of ['understand','visual','prompt-story']){f.tick();const out=await stepDone({step,summary:'Review the draft',cwd:f.record().root},f.agentPorts());assert.equal(out.exitCode,0,out.message);}f.herdr.idle();return {f,r:f.record()};}
for(const mode of ['strict','malformed'])test(`ROUND2 main checkout ${mode} policy cannot be bypassed in run worktree`,async t=>{
 const {f,r}=await ready(t);fs.writeFileSync(join(f.source,'pdd.json'),mode==='strict'?'{"strict_approvals":true}':'{broken');fs.writeFileSync(join(r.root,'pdd.json'),'{"strict_approvals":false}');
 const before=fs.readFileSync(join(r.runDir,'status.json'),'utf8'),prompt=fs.readFileSync(join(r.root,PLACE),'utf8');
 const out=await approveRun({ref:'17',cwd:r.root,said:'looks good'},f.agentPorts());assert.equal(out.exitCode,1,'main policy is authoritative');assert.match(out.message,mode==='strict'?/strict|terminal/i:/pdd\.json/i);assert.equal(fs.readFileSync(join(r.runDir,'status.json'),'utf8'),before);assert.equal(fs.readFileSync(join(r.root,PLACE),'utf8'),prompt);
});
test('ROUND2 edit and open preserve reviewed hashes until done re-shows gate',async t=>{
 const {f,r}=await ready(t),snapshot=structuredClone(r.gate.promptSnapshot);fs.appendFileSync(join(r.root,PLACE),'\nChanged prose after review.\n');
 const opened=await openRun({ref:'17',cwd:f.source},f.ports);assert.equal(opened.exitCode,0,opened.message);f.herdr.idle();assert.deepEqual(f.record().gate.promptSnapshot,snapshot,'opening the chat never rebinds the review');
 const refused=await approveRun({ref:'17',cwd:r.root,said:'looks good'},f.agentPorts());assert.equal(refused.exitCode,1);assert.match(refused.message,/show.*gate.*again/i);
 const shown=await stepDone({step:'prompt-story',summary:'Show changed draft',cwd:r.root},f.agentPorts());assert.equal(shown.exitCode,0,shown.message);f.herdr.idle();assert.equal((await approveRun({ref:'17',cwd:r.root,said:'approve this changed draft'},f.agentPorts())).exitCode,0);
});
function personLine(text){assert.doesNotMatch(text,/\/abs\/|\/bin\/pdd\.mjs|Show the gate|ask the person|Relay their|PDD_SAID|--said/i,'person text contains no agent instructions or local CLI path');}
test('ROUND2 changes approval reply speaks directly to person',async t=>{const {f,r}=await ready(t);const out=await changeRun({ref:'17',text:'I approve',cwd:r.root},f.ports);assert.equal(out.exitCode,2);personLine(out.message);assert.match(out.message,/approv/i);});
// Exercise the public status path for an existing ask-code gate without needing a real remote PR.
test('ROUND2 State and agent guidance keep person text separate and commands portable',async t=>{
 const {f,r}=await ready(t);const {writeRun}=await load('src/workflow-runs.mjs');const index=r.areas.findIndex(a=>a.then==='ask-code');assert.ok(index>=0);r.area=index;r.gate={...r.gate,kind:'ask-code',area:r.areas[index].name};r.pr=[{stage:r.areas[index].name,url:'https://github.com/example/project/pull/23',number:23}];writeRun(r,f.ports);
 const out=await runStatus({ref:'17',cwd:f.source},f.ports);assert.equal(out.exitCode,0,out.message);const state=out.message.match(/^State:.*$/m);assert.ok(state);personLine(state[0]);assert.doesNotMatch(out.message,/\/abs\/|\/bin\/pdd\.mjs/,'approval guidance uses a portable command');
});
const evidence={id:'round2',route:'said',actor:{kind:'agent',id:'synthetic'},at:1700000000000,words:'looks good',prompts:[]};
function lockFixture(t){const f=harbor(t);const commonDir=execFileSync('git',['rev-parse','--path-format=absolute','--git-common-dir'],{cwd:f.repo,encoding:'utf8'}).trim();const lock=join(commonDir,'pdd/approvals.lock');fs.mkdirSync(lock,{recursive:true});return {commonDir,lock};}
test('ROUND2 empty journal lock is recovered',async t=>{const {commonDir,lock}=lockFixture(t);let failure;try{await recordPromptApproval({commonDir,evidence});}catch(e){failure=e;}assert.equal(failure,undefined,'an empty lock cannot permanently prevent approvals');assert.deepEqual(await readPromptApprovals({commonDir}),[evidence]);assert.equal(fs.existsSync(lock),false);});
for(const phase of ['stat','list','owner-write'])test(`ROUND2 vanished journal lock retries after ${phase}`,async t=>{
 const {commonDir,lock}=lockFixture(t);if(phase==='owner-write')fs.rmdirSync(lock);let removed=false;const vanish=()=>{if(!removed){removed=true;fs.rmSync(lock,{recursive:true});}};
 const fake={...fs,renameSync(from,to){if(to.startsWith(lock+'/owner-')&&phase==='owner-write')vanish();return fs.renameSync(from,to);},lstatSync(path,...args){if(path===lock&&phase==='stat')vanish();return fs.lstatSync(path,...args);},readdirSync(path,...args){if(path===lock&&phase==='list')vanish();return fs.readdirSync(path,...args);}};
 let failure;try{await recordPromptApproval({commonDir,evidence},{fs:fake});}catch(e){failure=e;}assert.equal(removed,true);assert.equal(failure,undefined,'losing a disappearing lock retries acquisition');assert.deepEqual(await readPromptApprovals({commonDir}),[evidence]);
});
for(const kind of ['live','foreign','malformed'])test(`ROUND2 preserves ${kind} journal owner`,async t=>{const {commonDir,lock}=lockFixture(t);const {hostname}=await import('node:os');const bytes=kind==='malformed'?'{broken':JSON.stringify({pid:process.pid,hostname:kind==='foreign'?'foreign.invalid':hostname(),token:'held'});fs.writeFileSync(join(lock,'owner-held.json'),bytes);await assert.rejects(recordPromptApproval({commonDir,evidence}),/busy|lock|saving/i);assert.equal(fs.readFileSync(join(lock,'owner-held.json'),'utf8'),bytes);assert.deepEqual(await readPromptApprovals({commonDir}),[]);});

// Reach publication through the real done/approve API, with Git and gh isolated by the fixture.
async function prGate(t,{direct=false,drafts=false}={}){
 const {f}=await ready(t);let out=await approveRun({ref:'17',cwd:f.source},f.ports);assert.equal(out.exitCode,0,out.message);
 const r=f.record();if(direct){delete r.areas[r.area].before;const {writeRun}=await load('src/workflow-runs.mjs');writeRun(r,f.ports);}if(drafts)draft(r.root);fs.writeFileSync(join(r.root,'value.mjs'),'export const value = 2;\n');f.git(r.root,'add','.');f.git(r.root,'commit','-qm','Synthetic reviewed change');
 for(const step of r.areas[r.area].steps){f.tick();out=await stepDone({step,summary:'Synthetic checks complete',cwd:r.root},f.agentPorts());assert.equal(out.exitCode,0,out.message);}f.herdr.idle();assert.equal(f.record().gate.kind,direct?'ask-code':'approve-pr');return f;
}
function quotedPersonText(f){
 const messages=f.herdr.panes.flatMap(p=>p.agent?.prompts??[]);const texts=messages.flatMap(message=>[...message.matchAll(/Tell (?:them|the person) exactly: "([\s\S]*?)" (?:Then stop|Stop)/g)].map(m=>m[1]));assert.ok(texts.length,'publication sends actual person-facing text to the chat');for(const text of texts)personLine(text);return texts;
}
test('ROUND2 terminal publication stop reply and quoted chat text address the person',async t=>{
 const f=await prGate(t);let questions=0;const out=await approveRun({ref:'17',cwd:f.source},{...f.ports,confirm:async question=>{personLine(question);return ++questions===1;}});assert.equal(out.exitCode,0,out.message);assert.equal(questions,2);const stopped=out.message.match(/Stopped at PR 1\.[\s\S]*/);assert.ok(stopped);personLine(stopped[0]);quotedPersonText(f);assert.equal(f.record().gate.kind,'ask-code');
});
test('ROUND2 legacy unbound gate stays unbound after open',async t=>{
 const {f,r}=await ready(t);const {writeRun}=await load('src/workflow-runs.mjs');delete r.gate.promptSnapshot;writeRun(r,f.ports);assert.equal((await openRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);assert.equal(f.record().gate.promptSnapshot,undefined,'open cannot invent review evidence for old runs');
});
test('ROUND2 empty-lock recovery preserves an owner published during inspection',async t=>{
 const {commonDir,lock}=lockFixture(t);const {hostname}=await import('node:os');const bytes=JSON.stringify({pid:process.pid,hostname:hostname(),token:'replacement'});let published=false;
 const fake={...fs,readdirSync(path,...args){const names=fs.readdirSync(path,...args);if(path===lock&&!published){published=true;fs.writeFileSync(join(lock,'owner-replacement.json'),bytes);}return names;}};
 await assert.rejects(recordPromptApproval({commonDir,evidence},{fs:fake}),/busy|lock|saving/i);assert.equal(published,true);assert.equal(fs.readFileSync(join(lock,'owner-replacement.json'),'utf8'),bytes);assert.deepEqual(await readPromptApprovals({commonDir}),[]);
});

for(const drafts of [false,true])test(`ROUND2 publication exact person text with ${drafts?'draft prompts':'approved prompts'}`,async t=>{
 const f=await prGate(t,{direct:true,drafts});const r=f.record();const out=await stepDone({step:r.areas[r.area].steps.at(-1),summary:'Repeat completed publication step',cwd:r.root},f.agentPorts());assert.equal(out.exitCode,0,out.message);
 const quoted=[...out.message.matchAll(/(?:Tell the person exactly|ask exactly|tell them exactly): "([\s\S]*?)" (?:Stop|pdd never)/g)].map(m=>m[1]);assert.ok(quoted.length,'done contains exact text for the person');for(const text of quoted)personLine(text);assert.doesNotMatch(out.message,/\/abs\/|\/bin\/pdd\.mjs/);if(!drafts)assert.match(out.message,/<pdd> workflow approve 17 --said -/);
});
