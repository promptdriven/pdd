import test from 'node:test';
import assert from 'node:assert/strict';
import { proveRun, validateProofRecord } from '../src/workflow-prove.mjs';

// Oracle: approved workflow-prove and workflow-prove-existing-tests Rules to check.
// Bound: 2 overlay modes × 10 base states × 10 head states × 2 cleanup states.
// Each state represents one promised ordinary or abnormal process fact; this does
// not prove arbitrary flag combinations, real Git/process effects or causality.
const states = [
 ['pass', {exitCode:0}], ['defect', {exitCode:1,stdout:'defect-x'}], ['other', {exitCode:1,stderr:'other-error'}],
 ['126', {exitCode:126,stdout:'defect-x'}], ['127', {exitCode:127,stdout:'defect-x'}],
 ['timeout', {exitCode:1,timedOut:true,stdout:'defect-x'}], ['output-cap', {exitCode:1,outputLimited:true,stdout:'defect-x'}],
 ['signal', {exitCode:null,signal:'SIGTERM',stdout:'defect-x'}], ['setup', {exitCode:1,setupError:'missing module',stdout:'defect-x'}],
 ['spawn', {exitCode:null,error:'spawn refused',stdout:'defect-x'}]
];
const phase = facts => ({exitCode:null,signal:'',timedOut:false,outputLimited:false,stdout:'',stderr:'',error:'',setupError:'',...facts});
test('2958-FORMAL: success requires ordinary literal failure then head pass, independently of overlay selection', async()=>{
 let checked=0;
 for(const overlay of [false,true])for(const [baseName,base] of states)for(const [headName,head] of states)for(const cleanupFails of [false,true]){
  const context=JSON.stringify({overlay,baseName,headName,cleanupFails}),requests=[],phases=[base,head];let record;
  const result=await proveRun({ref:'2958',cwd:'/repo',test:'explicit unchanged command',expect:'defect-x'}, {
   readRun:async()=>({run:{runId:'bounded',runDir:'/run',root:'/repo',baseSha:'saved',baseBranch:'main'},error:''}),
   snapshot:async()=>({snapshot:{baseSha:'computed',headSha:'committed',baseAvailable:true,headAvailable:true,error:'',files:overlay?[{path:'test/new.test.mjs',status:'M',mode:'100644'}]:[]}}),
   createWorktree:async({phase})=>({worktree:`/snap/${phase}`,error:''}),
   overlay:async input=>{requests.push(input);return {error:''};},
   runProcess:async()=>({result:phase(phases.shift())}),
   cleanup:async()=>({error:cleanupFails?'cleanup refused':''}),
   saveProof:async input=>{record=input.record;return {error:''};}
  });
  // Requirement-derived truth table, independent of the implementation's classifier.
  const success=baseName==='defect' && headName==='pass' && !cleanupFails;
  assert.equal(result.exitCode===0,success,context);assert.equal(record.outcome==='proved',success,context);
  assert.equal(phases.length,0,`both commands execute: ${context}`);assert.equal(requests.length,Number(overlay),context);
  assert.equal(validateProofRecord(record),true,context);assert.notEqual(record.outcome,'no-changed-tests',context);checked++;
 }
 assert.equal(checked,400);
});
