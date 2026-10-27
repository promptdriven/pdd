import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import {runPdd} from '../src/pdd-cli.mjs';
import {resolveRun,formatStatus,formatAmbiguous} from '../src/workflow-shortcuts.mjs';
import {parseArgv} from '../src/argument-parser.mjs';
const id='11111111-1111-4111-8111-111111111111';
const other='22222222-2222-4222-8222-222222222222';
const capture=()=>({text:'',write(s){this.text+=s;}});
function fixture(t){
 const dir=mkdtempSync(join(tmpdir(),'short-regression-'));t.after(()=>rmSync(dir,{recursive:true,force:true}));
 const repos=['a','b'].map(name=>join(dir,name));
 for(const root of repos){mkdirSync(root);execFileSync('git',['init','-q',root]);execFileSync('git',['-C',root,'-c','user.name=Test','-c','user.email=test@example.test','commit','--allow-empty','-qm','init']);}
 const linked=join(dir,'issue-5');execFileSync('git',['-C',repos[0],'worktree','add','-qb','issue-5',linked]);
 const entries=repos.map((root,i)=>({runId:i?other:id,root,repo:i?'two/b':'one/a',issue:{number:2,title:i?'B two':'A two'},runDir:join(root,'.git','pdd','workflows',i?other:id)}));
 for(const entry of entries){mkdirSync(entry.runDir,{recursive:true});writeFileSync(join(entry.runDir,'journal.jsonl'),JSON.stringify({seq:7,state:{...entry,name:'small-change',seq:7,index:0,definitions:[{id:'change',kind:'human'}],waitingDecision:{stage:'change',seq:7,decisions:['approve']}}})+'\n');}
 const records={readRunIndex:async()=>({entries}),readJournalLast:async path=>({value:{state:entries.find(e=>e.runDir===path)}}),runStatusFromState:async s=>({...s,workflow:'small-change',state:'waiting',stage:{id:'change'},waitingFor:{decisions:['approve']}})};
 return {dir,repos,linked,entries,records};
}
test('real git main, other issue worktree and nested folders scope bare numbers without cross-repo fallback',async t=>{
 const f=fixture(t);const sub=join(f.repos[1],'src','nested');mkdirSync(sub,{recursive:true});
 for(const [cwd,expected] of [[f.repos[0],id],[f.linked,id],[sub,other]])assert.equal((await resolveRun('2',{cwd,records:f.records})).run.runId,expected);
 const missing={...f.records,readRunIndex:async()=>({entries:[f.entries[1]]})};
 assert.equal((await resolveRun('2',{cwd:f.repos[0],records:missing})).run,null);
 const outside=await resolveRun('2',{cwd:f.dir,records:f.records});assert.equal(outside.reason,'ambiguous');
 assert.match(formatAmbiguous(outside.runs,'approve'),/pdd workflow approve a#2/);
});
test('all selectors and no-operand watch resolve saved records',async t=>{
 const f=fixture(t);
 for(const ref of ['2','#2','a#2','one/a#2','https://github.com/one/a/issues/2',id.slice(0,8),id])assert.equal((await resolveRun(ref,{cwd:f.repos[0],records:f.records})).run.runId,id);
 const out=capture();assert.equal(await runPdd(['workflow','watch'],{cwd:f.repos[0],workflowRecords:f.records,stdout:out,stderr:capture()}),0);assert.match(out.text,/A two/);
});
test('outside-repository approve and legacy resume use the saved checkout and bound seam',async t=>{
 const f=fixture(t);
 for(const args of [['approve','a#2'],['resume','a#2','--decision','approve'],['resume',id,'--decision','approve']]){
  let calls=0;const out=capture();
  const code=await runPdd(['workflow',...args],{cwd:f.dir,stdout:out,stderr:capture(),workflowRecords:f.records,
   workflowRunner:{readWorkflowDecision:async i=>{assert.equal(i.cwd,f.repos[0]);return {state:'ready',stage:'change',journalSeq:7};},resumeWorkflow:()=>assert.fail('decision bypass')},
   workflowDecider:{decideWorkflow:async(i,p)=>{calls++;assert.equal(i.cwd,f.repos[0]);assert.equal(i.expectSeq,7);assert.equal(typeof p.onProgress,'function');return {state:'recorded',exitCode:0,message:'Recorded.'};}}});
  assert.equal(code,0,out.text);assert.equal(calls,1);
 }
});
test('status gives merge waits resume and --all omits ended runs',()=>{
 const run={runId:id,repo:'one/a',issue:{number:2,title:'A two'},workflow:'small-change',stage:{id:'wait-merge'},state:'waiting',waitingFor:{decisions:[]}};
 assert.match(formatStatus([run]),/pdd workflow resume/);assert.doesNotMatch(formatStatus([run]),/approve/);
 assert.doesNotMatch(formatStatus([run,{...run,state:'completed',issue:{number:3,title:'Ended'}}],{all:true}),/Ended/);
});
test('short phone decisions accept a complete token trio and reject partial mode',()=>{
 for(const action of ['approve','skip','changes']){
  assert.equal(parseArgv(['workflow',action,'2','--via','phone','--phone','device','--approval','token','--json']).options['--via'],'phone');
  assert.throws(()=>parseArgv(['workflow',action,'2','--phone','device']));
 }
});

test('bound decide also accepts an issue selector without changing explicit gate bindings', async t => {
 const f=fixture(t);let called=0;
 const result=await runPdd(['workflow','decide','2','--decision','approve','--id',other,'--expect-stage','change','--expect-seq','3','--json'],{
  cwd:f.repos[0],workflowRecords:f.records,stdout:capture(),stderr:capture(),
  workflowDecider:{decideWorkflow:async i=>{called++;assert.equal(i.runId,id);assert.equal(i.expectSeq,3);assert.equal(i.decisionId,other);return {state:'refused',code:'stale_decision',exitCode:1,message:'Stale decision.'};}}});
 assert.equal(result,1);assert.equal(called,1);
});
