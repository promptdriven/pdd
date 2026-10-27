import test from 'node:test';
import assert from 'node:assert/strict';
import {decideWorkflow} from '../src/workflow-decide.mjs';
import {parseArgv} from '../src/argument-parser.mjs';
const runId='11111111-1111-4111-8111-111111111111';
const decisionId='22222222-2222-4222-8222-222222222222';
const input={runId,decisionId,decision:'approve',expectStage:'change',expectSeq:7,cwd:'/repo',packageRoot:'/package'};
const state={runId,root:'/repo',agent:'codex',startedAt:100,repo:'example/project',issue:{number:17,title:'Use two'},waitingDecision:{stage:'change',seq:7,at:200,evidenceStage:{agent:'codex',root:'/repo',startedAt:100,endedAt:190}}};
function harness(overrides={}) {
  let admitted=0, questions=[];
  const ports={env:{},stdin:{isTTY:true},stderr:{isTTY:true,write(){}},now:()=>300,
    confirm:async q=>{questions.push(q);return true;},
    workflowRunner:{async applyWorkflowDecision(i,p){const auth=await p.authorizeDecision({input:i,state});if(!auth.ok)return {state:'refused',code:auth.code,message:auth.message,exitCode:1};admitted++;return {state:'recorded',exitCode:0,code:null,approvalRecord:auth.approvalRecord};}},...overrides};
  return {ports,get admitted(){return admitted;},questions};
}
test('malformed binding has no runner or authorization effect',async()=>{
 const h=harness(); for(const patch of [{expectSeq:0},{expectSeq:1.1},{decision:'other'},{text:'unexpected'},{decision:'changes',text:''}]) assert.equal((await decideWorkflow({...input,...patch},h.ports)).code,'bad_args');assert.equal(h.admitted,0);
});
test('terminal question names repo, issue and title; decline does not admit',async()=>{
 const h=harness();const r=await decideWorkflow(input,h.ports);assert.equal(r.state,'recorded');assert.match(h.questions[0],/example\/project#17.*Use two.*y\/N/);assert.equal(r.approvalRecord.kind,'terminal');
 const no=harness({confirm:async()=>false});assert.equal((await decideWorkflow(input,no.ports)).code,'person_required');assert.equal(no.admitted,0);
});
test('non-TTY yes cannot supply person authority',async()=>{
 const h=harness({stdin:{isTTY:false},readApprovalEvidence:async()=>({ok:false,code:'user_message_missing',message:'No user message after gate.'})});assert.equal((await decideWorkflow({...input,yes:true},h.ports)).code,'person_required');assert.equal(h.admitted,0);
});
test('authenticated phone path uses trusted host callback with no TTY',async()=>{
 const h=harness({stdin:{isTTY:false},authorizeDecision:async({state:s})=>{assert.equal(s,state);return {kind:'phone',authenticated:true,deviceId:'paired-device'};}});
 const r=await decideWorkflow(input,h.ports);assert.equal(r.state,'recorded');assert.equal(r.approvalRecord.kind,'phone');
 const no=harness({stdin:{isTTY:false},authorizeDecision:async()=>({kind:'phone',authenticated:false})});assert.equal((await decideWorkflow(input,no.ports)).code,'person_required');
});
test('agent marker requires actual W11 evidence, persists exact text and identity',async()=>{
 const h=harness({env:{PDD_AGENT_SESSION:'run/scope'},readApprovalEvidence:async request=>{assert.deepEqual(request,{stage:{agent:'codex',root:'/repo',startedAt:100,endedAt:190},gateAskedAt:200,decision:'approve'});return {ok:true,decision:'approve',agent:'codex',sessionId:decisionId,userMessage:'I approve this plan.',userMessageAt:250};}});
 const r=await decideWorkflow({...input,yes:true},h.ports);assert.equal(r.state,'recorded');assert.equal(r.approvalRecord.userMessage,'I approve this plan.');assert.equal(r.approvalRecord.sessionId,decisionId);assert.equal(h.questions.length,0);
});
test('missing, old and ambiguous chat evidence cannot admit a decision',async()=>{
 for(const code of ['user_message_missing','session_ambiguous','session_not_found']){const h=harness({env:{PDD_AGENT_SESSION:'run/scope'},readApprovalEvidence:async()=>({ok:false,code,message:'No current person evidence.'})});assert.equal((await decideWorkflow(input,h.ports)).code,'person_required');assert.equal(h.admitted,0);}
});
test('decide CLI requires canonical complete bindings and changes text',()=>{
 const base=['workflow','decide',runId,'--decision','approve','--id',decisionId,'--expect-stage','change','--expect-seq','7'];assert.equal(parseArgv(base).local,'workflow-decide');
 for(const args of [base.slice(0,-2),[...base,'--text','unexpected'],[...base,'--id',decisionId],[...base.slice(0,-1),'07'],[...base.slice(0,-1),'9007199254740992']])assert.throws(()=>parseArgv(args));
 assert.equal(parseArgv([...base.map(x=>x==='approve'?'changes':x),'--text','Please add a case.','--json']).options['--text'],'Please add a case.');
});

test('phone CLI options cannot activate an unchecked partial phone mode',()=>{
 const base=['workflow','decide',runId,'--decision','approve','--id',decisionId,'--expect-stage','change','--expect-seq','7'];
 for(const flags of [['--via','phone'],['--phone','device'],['--approval','token'],['--via','phone','--phone','device']])assert.throws(()=>parseArgv([...base,...flags]));
 const p=parseArgv([...base,'--via','phone','--phone','device','--approval','token']);assert.equal(p.options['--via'],'phone');
});
test('legacy resume decision enters the bound person seam instead of direct runner advance',async()=>{
 const {runPdd}=await import('../src/pdd-cli.mjs');let called=0;const stdout={text:'',write(x){this.text+=x;}};
 const code=await runPdd(['workflow','resume',runId,'--decision','approve'],{stdout,stderr:{write(){}},
 workflowRunner:{readWorkflowDecision:async()=>({state:'ready',stage:'change',journalSeq:7}),resumeWorkflow:()=>assert.fail('no direct decision resume')},
 workflowDecider:{decideWorkflow:async i=>{called++;assert.equal(i.expectSeq,7);assert.equal(i.expectStage,'change');return {exitCode:1,state:'refused',code:'person_required',message:'Person evidence required.'};}}});
 assert.equal(called,1);assert.equal(code,1);assert.match(stdout.text,/Person evidence/);
});

test('malformed decide replies fail finitely and cannot produce success JSON',async()=>{
 const {runPdd}=await import('../src/pdd-cli.mjs');
 const argv=['workflow','decide',runId,'--decision','approve','--id',decisionId,'--expect-stage','change','--expect-seq','7','--json'];
 for(const reply of [undefined,{state:'recorded'},{state:'recorded',exitCode:NaN,message:'ok'},{state:'recorded',exitCode:0,message:''}]){
  const stdout={text:'',write(x){this.text+=x;}},stderr={write(){}};
  assert.equal(await runPdd(argv,{stdout,stderr,workflowDecider:{decideWorkflow:async()=>reply}}),1);assert.equal(stdout.text,'');
 }
});

test('CLI composes the mobile lookup adapter with receiver intact and verifies a real signature',async()=>{
 const {webcrypto,randomUUID}=await import('node:crypto'),{runPdd}=await import('../src/pdd-cli.mjs');
 const key=await webcrypto.subtle.generateKey({name:'ECDSA',namedCurve:'P-256'},false,['sign','verify']);
 const phoneId='mobile-adapter-test',payload={runId,stage:'change',decision:'approve',expectSeq:7,phoneId,time:Date.now(),nonce:randomUUID()};
 const signature=Buffer.from(await webcrypto.subtle.sign({name:'ECDSA',hash:'SHA-256'},key.privateKey,new TextEncoder().encode(JSON.stringify(payload)))).toString('base64url');
 const token=Buffer.from(JSON.stringify({v:1,alg:'ES256',payload,signature})).toString('base64url');
 const publicKeyJwk=await webcrypto.subtle.exportKey('jwk',key.publicKey);let calls=0;
 const clientAdapter={async lookupPhone(id){calls++;assert.equal(this,clientAdapter);assert.equal(id,phoneId);return {phoneId,removed:false,state:'active',publicKeyJwk};}};
 const stdout={text:'',write(x){this.text+=x;}};
 const result=await runPdd(['workflow','decide',runId,'--decision','approve','--id',decisionId,'--expect-stage','change','--expect-seq','7','--via','phone','--phone',phoneId,'--approval',token,'--json'],{
 clientAdapter,stdout,stderr:{write(){}},stdin:{isTTY:false},workflowRunner:{async applyWorkflowDecision(i,p){const auth=await p.authorizeDecision({input:i,state});return {...auth,state:auth.ok?'recorded':'refused',exitCode:auth.ok?0:1,message:auth.ok?'Recorded.':auth.message};}}});
 assert.equal(result,0);assert.equal(calls,1);const answer=JSON.parse(stdout.text);assert.equal(answer.approvalRecord.phoneId,phoneId);assert.equal(answer.approvalRecord.kind,'phone');
});
