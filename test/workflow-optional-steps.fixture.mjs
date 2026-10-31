import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {mkdtempSync,mkdirSync,readFileSync,writeFileSync,rmSync,realpathSync,existsSync,cpSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve,dirname} from 'node:path';
import {pathToFileURL} from 'node:url';
export const DEFECT='Defect: optional steps leave applicability, advice and try skips to the agent.';
export const packageRoot=process.env.PDD_TEST_PACKAGE_ROOT ?? resolve(import.meta.dirname,'..');
export const runner=await import(pathToFileURL(join(packageRoot,'src/workflow-runner.mjs')));
const store=await import(pathToFileURL(join(packageRoot,'src/workflow-runs.mjs')));
// Control alpha lacks this sibling; do not turn its absence into an import failure.
const helperPath=join(packageRoot,'src/simulate-command.mjs');
const commandHelper=existsSync(helperPath)?await import(pathToFileURL(helperPath)):null;
export const vectors=JSON.parse(readFileSync(join(packageRoot,'test/runtime/workflow-optional-steps.json'),'utf8'));
export const sha=text=>createHash('sha256').update(text,'utf8').digest('hex');
export const clone=value=>structuredClone(value);
let gitTemplate;
function scratchGitTemplate(){
 if(gitTemplate)return gitTemplate;
 gitTemplate=realpathSync(mkdtempSync(join(tmpdir(),'p2756-template-')));
 const git=(...args)=>execFileSync('git',args,{cwd:gitTemplate,encoding:'utf8',stdio:['ignore','pipe','pipe']});
 git('init','-q','-b','alpha','--template=');git('config','user.name','Optional Step Test');git('config','user.email','test@example.invalid');
 writeFileSync(join(gitTemplate,'seed.txt'),'synthetic\n');git('add','.');git('commit','-qm','synthetic');
 process.once('exit',()=>rmSync(gitTemplate,{recursive:true,force:true}));return gitTemplate;
}
export function fixture(t,seed,{snapshot,defaultReader=false,fastStore=false}={}) {
 const base=realpathSync(mkdtempSync(join(tmpdir(),'p2756-'))),root=join(base,'repo'),home=join(base,'home');
 mkdirSync(root);mkdirSync(home);t.after(()=>rmSync(base,{recursive:true,force:true}));
 const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8',stdio:['ignore','pipe','pipe']});
 // A copied real local Git seed avoids hundreds of redundant init/config/commit subprocesses.
 const template=scratchGitTemplate();cpSync(join(template,'.git'),join(root,'.git'),{recursive:true});cpSync(join(template,'seed.txt'),join(root,'seed.txt'));
 const originalRoot=seed.root,originalRunDir=seed.runDir,runDir=join(root,'.git','pdd','runs',String(seed.number));
 const relocate=value=>typeof value==='string'?value.replaceAll(originalRunDir,runDir).replaceAll(originalRoot,root):Array.isArray(value)?value.map(relocate):value&&typeof value==='object'?Object.fromEntries(Object.entries(value).map(([k,v])=>[k,relocate(v)])):value;
 const restore=value=>typeof value==='string'?value.replaceAll(runDir,originalRunDir).replaceAll(root,originalRoot):Array.isArray(value)?value.map(restore):value&&typeof value==='object'?Object.fromEntries(Object.entries(value).map(([k,v])=>[k,restore(v)])):value;
 const f={base,root,home,runDir,git,relocate,restore,clock:1000,saves:0,reads:0,personReads:0,chooserCalls:0,hashes:0,external:[]};
 f.statusPath=join(runDir,'status.json');f.put=(path,text)=>{mkdirSync(dirname(join(root,path)),{recursive:true});writeFileSync(join(root,path),text);};
 f.seed=run=>{mkdirSync(runDir,{recursive:true});writeFileSync(f.statusPath,JSON.stringify(relocate(run),null,2)+'\n');};
 f.record=()=>JSON.parse(readFileSync(f.statusPath,'utf8'));f.compact=()=>JSON.stringify(restore(f.record()));f.seed(seed);
 f.ports={env:{HOME:home,PDD_AGENT_SESSION:'1'},stateDir:join(base,'state'),layoutDirectory:join(base,'layout'),pdd:'pdd',isTTY:false,
 now:()=>f.clock,execFile:async(file,args,options)=>{if(file!=='git') {f.external.push([file,args]);assert.fail(`${DEFECT} Unexpected external program ${file}`);}return {stdout:execFileSync(file,args,{...options,encoding:'utf8',stdio:['ignore','pipe','pipe']})};},
 runForWorktree:async(cwd,p)=>fastStore?(assert.equal(cwd,root),store.readRun(runDir)):store.runForWorktree(cwd,p),writeRun:(run,p)=>{f.saves++;return store.writeRun(run,p);},
 hashUtf8:text=>{f.hashes++;return sha(text);},
 readApprovalEvidence:async()=>{f.personReads++;return f.reply??{ok:false,code:'no_user_reply',message:'No synthetic reply'};},
 chooseSimulationCommand:input=>{f.chooserCalls++;f.lastChooser=clone(input);assert.ok(commandHelper,`${DEFECT} Runner selected the production chooser`);return commandHelper.chooseSimulationCommand(input);},
 herdr:async(...args)=>{f.external.push(['herdr',args]);assert.fail(`${DEFECT} Unexpected Herdr operation`);}};
 if(defaultReader)delete f.ports.chooseSimulationCommand;
 if(!defaultReader)f.ports.readOptionalEvidence=async request=>{f.reads++;return {snapshot:clone(f.snapshotByPath?f.snapshotByPath(f.restore(request.notePath)):f.snapshot??snapshot??{note:'',error:'missing',complete:false,files:[]})};};
 f.done=(step,summary,extra={})=>runner.stepDone({step,summary,cwd:root,packageRoot}, {...f.ports,...extra});
 return f;
}
export function seedFor(id){const step=vectors.steps.find(row=>row.step_id===id);assert.ok(step,`Unknown fixture ${id}`);const row=vectors.initial_world.runs.find(row=>row.cwd===step.input.cwd);return {step,run:JSON.parse(row.record),snapshot:clone(vectors.initial_world.snapshots.find(row=>row.notePath.startsWith(`${step.input.cwd}/`))?.snapshot)};}
export function materializeSnapshot(f,snapshot,note='understand.md'){
 for(const file of snapshot.files){if(!file.error)f.put(file.path,file.text);}
 if(snapshot.note){mkdirSync(f.runDir,{recursive:true});writeFileSync(join(f.runDir,note),snapshot.note);}
}
export function jsonPointer(value,path){return path.split('/').slice(1).reduce((v,k)=>v?.[k.replaceAll('~1','/').replaceAll('~0','~')],value);}
export function assertCheck(actual,check,label){const message=`${DEFECT} ${label} ${check.criterion_id} ${check.target}${check.path} ${check.op}`;
 if(check.op==='equals')assert.deepEqual(actual,check.value,message);
 else if(check.op==='contains')assert.ok(actual?.includes(check.value),`${message}\nexpected ${JSON.stringify(check.value)} in ${JSON.stringify(actual)}`);
 else if(check.op==='not_contains')assert.ok(!actual?.includes(check.value),message);
 else assert.fail(`Not replayed: unsupported check operation ${check.op}`);
}
