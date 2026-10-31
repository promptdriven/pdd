import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { hostname } from 'node:os';
import { fork } from 'node:child_process';
import { once } from 'node:events';
import { join } from 'node:path';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';
import { stepDone, approveRun, changeRun, runStatus } from '../src/workflow-runner.mjs';
import { sendToChat } from '../src/workflow-chat.mjs';
import { writeRun } from '../src/workflow-runs.mjs';

const vectors = JSON.parse(fs.readFileSync(new URL('./workflow-change-delivery/cases.json', import.meta.url), 'utf8'));
const changePrefix='The person asks for changes: ',changeSuffix=' Revise in this chat, run done again for the step you changed, then show the result and ask again.';
const answerPrefix='The person answers your question: ',answerSuffix=' Go on with the step.';
const deferred=()=>{let resolve;const promise=new Promise(r=>resolve=r);return {promise,resolve};};
const facts=(message,values=[])=>{for(const value of values)assert.ok(message.toLowerCase().includes(value.toLowerCase()),`message includes ${value}: ${message}`);};
const absent=(message,values=[])=>{for(const value of values)assert.ok(!message.toLowerCase().includes(value.toLowerCase()),`message excludes ${value}: ${message}`);};
const records=path=>fs.existsSync(path)?fs.readdirSync(path).filter(name=>name.endsWith('.json')):[];
const missing=()=>{throw Object.assign(Error('starting'),{code:'agent_not_found'});};

for(const vector of vectors.cases)test(`2677 vector: ${vector.id}`,{timeout:15000},async t=>{
 const given=vector.given,expected=vector.expect;
 if(given.custodyWriteFails&&process.geteuid?.()===0)return t.skip('chmod cannot deny writes to root; injected write-failure tests cover custody');
 const f=await fixture(t,{agent:'codex',name:'bug'});assert.equal((await f.run()).exitCode,0);
 for(const step of ['reproduce','prompt-story'])assert.equal((await stepDone({step,summary:'done',cwd:f.record().root},f.agentPorts())).exitCode,0);
 assert.equal((await approveRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
 const initial=f.record(),chat=initial.chats.at(-1),pane=f.herdr.paneOf(chat),originalPane=chat.paneId,started=f.elapsed;
 const approvals=initial.decisions.filter(r=>r.decision==='approve').length,healthy=f.ports.herdr;
 const journalPath=join(initial.runDir,'delivery-journal.json'),lock=join(initial.runDir,'.delivery-journal.lock');
 const readJournal=()=>fs.existsSync(journalPath)?JSON.parse(fs.readFileSync(journalPath,'utf8')).requests:[];
 const saveJournal=requests=>fs.writeFileSync(journalPath,JSON.stringify({requests}));
 const base={id:'seed-request',text:'',kind:'change',state:'pending',area:chat.area,paneId:originalPane,at:f.clock,question:null,gate:null};
 chat.startedAt=f.clock-(given.chatAgeMs??0);
 if(given.gateOpen){initial.gate={area:chat.area,at:f.clock,kind:'approve'};initial.state='waiting';}
 if(given.question){initial.question={text:given.question,at:f.clock,area:chat.area};initial.state='waiting';}
 if(given.concurrentWriter==='status')initial.chatFailure={area:chat.area,phase:'start',code:'server_unavailable',message:'Saved startup failure',at:f.clock};
 if(given.noChatRecord)initial.chats=initial.chats.filter(c=>c.area!==chat.area);
 writeRun(initial,f.ports);
 if(given.journalRequest)saveJournal([{...base,...given.journalRequest,...(given.journalRequest.inFlight?{owner:{pid:654321,hostname:hostname(),token:'dead-sender'}}:{})}]);
 f.ports.processIdentity=pid=>({alive:pid===process.pid?true:given.journalClaim?.owner==='confirmed-live-same-host'?true:given.journalClaim?.owner==='identity-unavailable-or-malformed'?null:false});
 const seedClaim=(claim,token=claim.token??'ack-owner')=>{fs.mkdirSync(lock,{recursive:true});const leaf=join(lock,`owner-${token}.json`);fs.writeFileSync(leaf,JSON.stringify({pid:claim.owner==='confirmed-live-same-host'?process.pid:654321,hostname:claim.owner==='foreign-host'?'another-host':hostname(),token}));return leaf;};
 if(given.journalClaim)seedClaim(given.journalClaim);
 const stray=given.journalClaimDirectoryStrayFile;
 if(stray){fs.mkdirSync(lock,{recursive:true});fs.writeFileSync(join(lock,stray.name),stray.content);fs.writeFileSync(join(lock,'notes.json'),'{unrelated-json');}
 let claimElapsed=0,claimRetries=0,claimAttempts=0,ackRetries=0,ackDeny=false;
 f.ports.journalElapsedNow=()=>claimElapsed;
 f.ports.journalSleep=async ms=>{claimRetries++;if(attempts)ackRetries++;claimElapsed+=ms;await new Promise(r=>setTimeout(r,ms));};
 f.ports.deliveryFiles={...fs,mkdirSync:(path,...args)=>{if(path===lock)claimAttempts++;return fs.mkdirSync(path,...args);},writeFileSync:(path,data,...args)=>{
   if(String(path).includes('delivery-journal.json')){
    const entries=JSON.parse(data).requests;
    if(ackDeny||given.intentWriteFails&&entries.some(e=>e.inFlight))throw Object.assign(Error('injected denied write'),{code:'EACCES'});
   }
   return fs.writeFileSync(path,data,...args);
 }};
 const launches=f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length;
 let ready=given.ready===true,readyAfter=given.readyAfterMs,baseline=started,waits=0,mutated=false,attempts=0,beforeReady=0,replacements=0,beforeSubmitCalls=0,jumped=false,errorUsed=false;
 let secondElapsed=0,questionAfterFirst,firstAccepted=0,firstWaits=0,sharedId,firstTask,firstComplete=false,statusTask;
 const outputs=[],submitted=[],answers=[],changes=[],custody=[],bound=new Set(),timers=[];
 t.after(()=>timers.forEach(clearTimeout));
 const firstWait=deferred(),bothWait=deferred(),release=deferred(),statusEntered=deferred(),statusRelease=deferred();let waiters=0;
 f.ports.sleep=async ms=>{
   assert.ok(ms>0&&ms<=250);waits++;f.tick(ms);
   if(given.wallClockJumpAtElapsedMs&&!jumped&&f.elapsed-started>=given.wallClockJumpAtElapsedMs){f.clock+=given.wallClockJumpMs;jumped=true;}
   if(given.captureRunBeforeSubmit&&!statusTask){statusTask=runStatus({ref:'17',cwd:f.source},{...f.ports,herdr:async args=>{if(args[0]==='agent'&&args[1]==='get'){statusEntered.resolve();await statusRelease.promise;}return f.ports.herdr(args);}});await statusEntered.promise;}
   if(vector.duringWait&&!mutated){mutated=true;const r=f.record(),u=vector.duringWait;if(u.doneStep)r.done[u.doneStep]={summary:'new progress',at:f.clock,area:chat.area};if(u.question)r.question={text:u.question,at:f.clock+1,area:chat.area};if(u.gateAt)r.gate={area:chat.area,at:u.gateAt,kind:'approve'};if(u.replacePane)r.chats.at(-1).paneId='replacement-pane';writeRun(r,f.ports);}
   if(given.overlapIdenticalWhileFirstWaits){if(++waiters===1)firstWait.resolve();if(waiters===2)bothWait.resolve();await release.promise;if(vector.phases)f.tick(40000);}
 };
 const knownReady=()=>ready||readyAfter!=null&&f.elapsed-baseline>=readyAfter||given.knownReadyAfterMs!=null&&f.elapsed-started>=given.knownReadyAfterMs;
 f.ports.herdr=async args=>{
   if(args[0]==='agent'&&args[1]==='get'){
    if(given.inspectError)throw Object.assign(Error(given.inspectError),{code:given.inspectError});
    if(!knownReady()&&!given.initialAgentAlive)return missing();
    pane.agent.agent_status=knownReady()?given.statusWhenReady??'working':given.initialAgentStatus;
   }
   if(args[0]==='agent'&&args[1]==='prompt'){
    attempts++;if(args[2]!==originalPane)replacements++;
    const answer=args[3].startsWith(answerPrefix),change=args[3].startsWith(changePrefix),text=answer?args[3].slice(answerPrefix.length,-answerSuffix.length):change?args[3].slice(changePrefix.length,-changeSuffix.length):args[3];
    if(!knownReady())beforeReady++;
    if(answer||change){const owned=readJournal().find(e=>e.text===text&&e.state==='pending'&&e.inFlight&&e.paneId===originalPane&&e.kind===(answer?'answer':'change'));custody.push(Boolean(owned));if(owned)bound.add(owned.paneId);}
    if(!knownReady()&&!given.initialAgentAlive)return missing();
    if(given.submitError&&(!given.submitErrorOnce||!errorUsed)){errorUsed=true;throw Object.assign(Error(given.submitError),{code:given.submitError});}
    submitted.push(text);if(answer)answers.push(text);if(change)changes.push(text);
    if(given.ackWriteFails)ackDeny=true;
    if(given.journalClaimDuringAck&&attempts===1){const leaf=seedClaim(given.journalClaimDuringAck);timers.push(setTimeout(()=>fs.unlinkSync(leaf),given.journalClaimDuringAck.releaseAfterMs));}
   }
   return healthy(args);
 };
 const invoke=async(text,ports=f.ports)=>{try{return await changeRun({ref:'17',text,cwd:f.source},ports);}catch(error){if(['EACCES','EPERM'].includes(error.code))return {exitCode:1,message:String(error)};throw error;}};
 if(vector.operation==='sendToChat'){
   const result=await sendToChat(chat,vector.requests[0],{...f.ports,beforeSubmit:()=>{beforeSubmitCalls++;return given.beforeSubmitResult;}});
   assert.equal(result.ok,expected.ok);assert.equal(result.code,expected.code);assert.equal(beforeSubmitCalls,expected.beforeSubmitCalls);assert.deepEqual(submitted,expected.submittedTexts);return;
 }
 if(given.privateOwnedChild){
   const child=fork(new URL('./helpers/workflow-owned-wait-child.mjs',import.meta.url),[f.source,f.state,String(f.clock),vector.requests[0]],{env:{...process.env,W:join(import.meta.dirname,'..'),HOME:f.ports.env.HOME},stdio:['ignore','pipe','pipe','ipc']});
   t.after(()=>{if(child.exitCode===null&&child.signalCode===null)child.kill('SIGKILL');});
   const [message]=await once(child,'message');assert.equal(message.waiting,true);sharedId=readJournal()[0]?.id;
   assert.equal(fs.readdirSync(initial.runDir).filter(name=>/^\.delivery-[a-f0-9]+\.lock$/.test(name)).length,expected.longDispatchClaims);
   const closed=once(child,'close');child.kill('SIGKILL');await closed;ready=true;outputs.push(await invoke(vector.requests[1]));assert.equal(readJournal()[0].id,sharedId);
 }else if(given.overlapIdenticalWhileFirstWaits){
   firstTask=invoke(vector.requests[0]).then(result=>{firstComplete=true;return result;});
   const entered=await Promise.race([firstWait.promise.then(()=>true),firstTask.then(()=>false)]);
   if(!entered){release.resolve();await firstTask;assert.fail('fresh startup must actually wait before a caller can join');}
   const second=invoke(vector.requests[1],{...f.ports,herdr:async args=>{if(!vector.phases&&knownReady()&&args[0]==='agent'&&args[1]==='get')await firstTask;return f.ports.herdr(args);}});
   await Promise.race([bothWait.promise,second]);sharedId=readJournal()[0]?.id;assert.equal(readJournal().length,1);
   if(!vector.phases)ready=true;release.resolve();outputs.push(...await Promise.all([firstTask,second]));
   assert.equal(readJournal()[0].id,sharedId);
   if(vector.phases){assert.ok(outputs.every(r=>r.exitCode!==0));ready=true;outputs.push(await invoke(vector.requests[2]));if(given.kind==='answer'){const r=f.record();r.question={text:'Continue again?',at:f.clock,area:chat.area};writeRun(r,f.ports);}outputs.push(await invoke(vector.requests[3]));}
   questionAfterFirst=f.record().question?.text??null;
 }else for(const [index,text]of vector.requests.entries()){
   if(index===1&&vector.beforeSecond?.explicitOpen){const r=f.record();r.chats.push({...chat,startedAt:f.clock});writeRun(r,f.ports);readyAfter=vector.beforeSecond.readyAfterMs;baseline=f.elapsed;}
   if(index===1&&vector.beforeSecond?.ready)ready=true;
   if(index===1&&vector.beforeSecond?.resumeNow){const r=f.record();r.chats.at(-1).resumedAt=f.clock;writeRun(r,f.ports);readyAfter=vector.beforeSecond.readyAfterMs;baseline=f.elapsed;}
   const before=f.elapsed;if(given.custodyWriteFails)fs.chmodSync(initial.runDir,0o500);
   try{outputs.push(await invoke(text));}finally{if(given.custodyWriteFails)fs.chmodSync(initial.runDir,0o700);}
   if(!index){firstAccepted=readJournal().length;firstWaits=waits;questionAfterFirst=f.record().question?.text??null;if(statusTask){statusRelease.resolve();assert.equal((await statusTask).exitCode,0);}}
   if(index===1)secondElapsed=f.elapsed-before;
 }
 const run=f.record(),requests=readJournal(),message=outputs.map(r=>r.message).join('\n');
 if('exitCode'in expected)assert.equal(outputs.at(-1).exitCode,expected.exitCode,message);
 if(expected.exitCodeNonzero)assert.notEqual(outputs.at(-1).exitCode,0,message);
 if(expected.firstExitCodeNonzero)assert.notEqual(outputs[0].exitCode,0);
 if('secondExitCode'in expected)assert.equal(outputs[1].exitCode,expected.secondExitCode);
 if(expected.exitCodes)assert.deepEqual(outputs.map(r=>r.exitCode),expected.exitCodes);
 facts(message,expected.messageFacts);absent(message,expected.messageAbsentFacts);facts(outputs[0].message,expected.firstMessageFacts);absent(outputs[0].message,expected.firstMessageAbsentFacts);facts(outputs.at(-1).message,expected.lastMessageFacts);
 if(expected.repeatedMessageFacts){const repeat=given.mayHaveDispatched?outputs[1]:outputs[0];facts(repeat.message,expected.repeatedMessageFacts);absent(repeat.message,expected.repeatedMessageAbsentFacts);}
 if(expected.cojoinedMessageAbsentFacts)absent(outputs[1].message,expected.cojoinedMessageAbsentFacts);
 for(const[key,actual]of[['submittedTexts',submitted],['submittedAnswerTexts',answers],['submittedChangeTexts',changes]])if(key in expected)assert.deepEqual(actual,expected[key],message);
 for(const[key,state]of[['pendingTexts','pending'],['uncertainTexts','uncertain']])if(key in expected)assert.deepEqual(requests.filter(r=>r.state===state).map(r=>r.text),expected[key]);
 if(expected.custodyBeforeSubmit||submitted.length)assert.ok(custody.length&&custody.every(Boolean),'original text, kind, pane and exclusive durable submission intent precede transport');
 if('deliveredRequestCount'in expected)assert.equal(requests.filter(r=>r.state==='delivered').length,expected.deliveredRequestCount);
 if('changeRoundCount'in expected)assert.equal(run.changes.length,expected.changeRoundCount);
 if('acceptedRequestIdsCount'in expected)assert.equal(new Set(requests.map(r=>r.id)).size,expected.acceptedRequestIdsCount);
 if(expected.deliveredRequestKinds)assert.deepEqual(requests.filter(r=>r.state==='delivered').map(r=>r.kind),expected.deliveredRequestKinds);
 if(expected.requestKinds)assert.deepEqual(requests.map(r=>r.kind),expected.requestKinds);
 if('firstAcceptedRequests'in expected)assert.equal(firstAccepted,expected.firstAcceptedRequests);
 if('firstWaitCalls'in expected)assert.equal(firstWaits,expected.firstWaitCalls);
 if('permanentUnboundEntries'in expected)assert.equal(requests.filter(r=>r.paneId===null).length,expected.permanentUnboundEntries);
 if('elapsedMsAtMost'in expected)assert.ok(f.elapsed-started<=expected.elapsedMsAtMost);
 if('elapsedMsAtLeast'in expected)assert.ok(f.elapsed-started>=expected.elapsedMsAtLeast);
 if('secondElapsedMsAtLeast'in expected)assert.ok(secondElapsed>=expected.secondElapsedMsAtLeast);
 if('secondElapsedMsAtMost'in expected)assert.ok(secondElapsed<=expected.secondElapsedMsAtMost);
 for(const[key,actual]of[['submitAttempts',attempts],['replacementSubmissions',replacements],['waitCalls',waits],['submittedBeforeReady',beforeReady]])if(key in expected)assert.equal(actual,expected[key]);
 if('repeatedUncertainSubmitAttempts'in expected)assert.equal(outputs[1].exitCode!==0?attempts-submitted.length-1:-1,expected.repeatedUncertainSubmitAttempts);
 if('gateOpen'in expected)assert.equal(Boolean(run.gate),expected.gateOpen);
 if('agentStarts'in expected)assert.equal(f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length-launches,expected.agentStarts);
 if(expected.doneStep)assert.equal(run.done[expected.doneStep]?.summary,'new progress');if(expected.question)assert.equal(run.question?.text,expected.question);if(expected.gateAt)assert.equal(run.gate?.at,expected.gateAt);
 if('questionAfterFirst'in expected)assert.equal(questionAfterFirst,expected.questionAfterFirst);
 if('questionAfterSecond'in expected)assert.equal(run.question??null,expected.questionAfterSecond);
 if('questionAfterLast'in expected)assert.equal(run.question??null,expected.questionAfterLast);
 if('answerRecordCount'in expected)assert.equal(run.changes.filter(r=>r.answer).length,expected.answerRecordCount);
 if('approvalCount'in expected)assert.equal(run.decisions.filter(r=>r.decision==='approve').length-approvals,expected.approvalCount);
 if(expected.exactText)assert.equal(run.changes.at(-1)?.text,expected.exactText);
 if(expected.journalClaimRemoved)assert.equal(records(lock).length,0);
 if(expected.claimToken)assert.ok(records(lock).includes(`owner-${expected.claimToken}.json`));
 if(expected.strayFilePreserved){assert.equal(fs.readFileSync(join(lock,stray.name),'utf8'),stray.content);assert.equal(fs.readFileSync(join(lock,'notes.json'),'utf8'),'{unrelated-json');}
 if(expected.boundedClaimRetry){assert.ok(claimRetries>0);assert.ok(claimElapsed<=expected.claimAcquisitionElapsedMsAtMost);}
 if(expected.ackClaimRetries)assert.ok(ackRetries>0,'successful acknowledgement must asynchronously retry a brief live claim');
 if('journalClaimAttempts'in expected)assert.equal(claimAttempts,expected.journalClaimAttempts);
 if(expected.authoritativeJournalFile)assert.ok(fs.existsSync(journalPath));
 if(expected.retryArgumentQuoted)assert.match(message,/workflow changes 17 'First'/);
 if(expected.adviceBeforeRetryCommand)assert.ok(message.toLowerCase().indexOf('wait')<message.indexOf('workflow changes'));
 if('retryLabelCount'in expected)assert.equal((message.match(/retry:/gi)??[]).length,expected.retryLabelCount);
 if(expected.genericTransportPreservesGateMessage){const control=expected.genericTransportPreservesGateMessage,sent=[];const result=await sendToChat(chat,control.input,{...f.ports,herdr:async args=>{if(args[1]==='prompt')sent.push(args[3]);return healthy(args);}});assert.equal(result.ok,true);assert.deepEqual(sent,[control.submitted]);}
 if(expected.sameTextRetryAttempts===0){const before=attempts;ackDeny=false;assert.notEqual((await invoke(vector.requests[0])).exitCode,0);assert.equal(attempts,before);}
 if('retryablePendingCount'in expected)assert.equal(readJournal().filter(r=>r.state==='pending'&&!r.inFlight).length,expected.retryablePendingCount);
 if(expected.falseRetryPromiseAfterInFlightOrDelivered===false)for(const result of outputs.slice(2))absent(result.message,['kept','Retry:']);
 if(vector.id==='approval-hint-before-journal-contention'){
   assert.equal(readJournal().length,0,'approval hints accept no custody even when journal is busy');
   for(const name of records(lock))fs.unlinkSync(join(lock,name));
   ready=false;readyAfter=500;baseline=f.elapsed;const before=f.elapsed;
   const result=await invoke('Add the concrete retry example');
   assert.equal(result.exitCode,0,'a real change at the same gate waits for fresh startup after the owner releases');
   assert.ok(f.elapsed-before>=500);assert.equal(readJournal().length,1);assert.equal(readJournal()[0].state,'delivered');assert.equal(submitted.at(-1),'Add the concrete retry example');assert.equal(f.record().gate?.kind,'approve');
 }
 if(expected.inFlightCompanion){
   const entered=deferred(),held=deferred();let submits=0;const before=attempts;
   const ports={...f.ports,herdr:async args=>{if(args[1]==='prompt'){submits++;entered.resolve();await held.promise;}return healthy(args);}};
   const first=invoke('Companion request',ports);await entered.promise;const joined=await invoke('Companion request',ports);facts(joined.message,expected.inFlightCompanion.messageFacts);absent(joined.message,expected.inFlightCompanion.messageAbsentFacts);held.resolve();assert.equal((await first).exitCode,0);assert.equal(submits,expected.inFlightCompanion.submitAttempts);assert.equal(attempts,before);
 }
 if(expected.uncertainKindCompanion){
   const companion=expected.uncertainKindCompanion;saveJournal([{...base,id:'uncertain-kind',text:companion.text,kind:companion.priorKind,state:companion.priorState}]);const r=f.record();r.question=null;writeRun(r,f.ports);const before=attempts;assert.equal((await invoke(companion.text)).exitCode,0);assert.equal(attempts-before,companion.newSubmissions);assert.equal(readJournal()[0].state,'uncertain');assert.equal(readJournal().filter(r=>r.kind===companion.priorKind&&r.state==='delivered').length,companion.priorResubmissions);
 }
});
