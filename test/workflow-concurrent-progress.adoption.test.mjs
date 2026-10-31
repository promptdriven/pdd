import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {Worker} from 'node:worker_threads';
import {adoptedCorpusRun} from './helpers/workflow-concurrent-adoption.mjs';
import * as runner from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {nativeCase,observations} from './helpers/workflow-concurrent-cases.mjs';
function stage(run){run.replayEvidence={outcome:'passed',reason:'Previous PASS'};run.done.verify={at:1,summary:'Prior verify',area:'code',replayEvidence:{outcome:'passed'}};}
function concurrentFacts(f){const latest=f.record();latest.done.independent={at:2000,summary:'Unrelated completed work',area:'other'};latest.decisions.push({stage:'other',decision:'changes',at:2000});latest.question={text:'Independent question',area:'code',at:2000};if(latest.pr[0])latest.pr[0].review={state:'approved',at:2000};writeRun(latest,f.ports);return latest;}
function guardEffects(f){
 let owned=false;const original=f.ports.execFile,herdr=f.ports.herdr;const events=[];
 const marker=join(f.base,'ordinary-owned'),bodies=[];
 const ports={...f.ports,acquireRunOwnership:()=>{assert.equal(owned,false);owned=true;fs.writeFileSync(marker,'owned');events.push('ordinary-enter');return()=>{owned=false;fs.unlinkSync(marker);events.push('ordinary-exit');};},execFile:async(file,args,opts)=>{assert.equal(owned,false,'Git/GitHub effects outside ordinary owner');events.push(`${file} ${args.slice(0,2).join(' ')}`);if(file==='gh'&&args[0]==='pr'&&args[1]==='edit')bodies.push({body:String(opts.input),index:events.length-1});return original(file,args,opts);},herdr:async args=>{assert.equal(owned,false,'Herdr outside ordinary owner');events.push(`herdr ${args[0]}`);return herdr(args);}};
 ports.deliveryFiles=Object.fromEntries(Object.entries(fs).filter(([,value])=>typeof value==='function').map(([name,operation])=>[name,(...args)=>{assert.equal(owned,false,'journal effects outside ordinary owner');return operation(...args);} ]));
 return {ports,events,marker,bodies};
}
const blocked=nativeCase('adopted-corpus-blocked-save-retains-own-intent');
for(const command of blocked.given.publicCommandVariants)for(const mode of blocked.given.validationFailureVariants)test(`2753 adopted blocked ${command}: ${mode}`,async t=>{
 const {f}=await adoptedCorpusRun(t),run=f.record();stage(run);
 if(command.startsWith('approveRun')){run.areas[0].before='approve';run.gate={area:'code',at:1,kind:'approve-pr'};}
 if(mode==='frozen provenance mismatch')run.replayAdoption.provenance.approval_reference='different-frozen-reference';
 if(mode==='adopted anchor mismatch')run.replayBaseline.vectors[0].sha256='0'.repeat(64);
 writeRun(run,f.ports);
 if(mode==='changed covered prompt/dependency/scenario')fs.writeFileSync(join(run.root,'rules/add.md'),'Changed covered requirement.\n');
 const authority=structuredClone(run.replayAdoption),anchor=structuredClone(run.replayBaseline),journal=join(run.runDir,'delivery-journal.json');fs.writeFileSync(journal,JSON.stringify({requests:[{id:'acked',text:'Keep ACK',kind:'change',area:'code',paneId:run.chats[0].paneId,state:'delivered',at:1,deliveredAt:2,ackedAt:3,ackSummary:'Own acknowledgement'}]}));const bytes=fs.readFileSync(journal,'utf8');
 // Hold the actual native validator's Git observation in a worker. The same
 // boundary exists on the old code even when approve validates before publishing.
 const bin=join(f.base,'blocked-git-bin'),held=join(f.base,'validator-held'),release=join(f.base,'validator-release');fs.mkdirSync(bin);
 fs.writeFileSync(join(bin,'git'),`#!/bin/sh
if [ "$1" = merge-base ] && [ "$2" = --is-ancestor ]; then
 : > '${held}'
 count=0
 while [ ! -e '${release}' ] && [ "$count" -lt 2000 ]; do /usr/bin/sleep 0.01; count=$((count+1)); done
fi
exec /usr/bin/git "$@"
`,{mode:0o755});
 const worker=new Worker(new URL('./helpers/workflow-concurrent-adoption-worker.mjs',import.meta.url),{workerData:{command,root:run.root,source:f.source,stateDir:f.ports.stateDir,env:f.ports.env},env:{...process.env,PATH:`${bin}:${process.env.PATH}`}});
 t.after(async()=>{if(fs.existsSync(f.base))fs.writeFileSync(release,'release');await worker.terminate();});
 const reply=new Promise((resolve,reject)=>{worker.once('message',resolve);worker.once('error',reject);});
 const deadline=Date.now()+20000;
 while(!fs.existsSync(held)&&Date.now()<deadline)await new Promise(resolve=>setTimeout(resolve,10));
 assert.ok(fs.existsSync(held),'actual native validator observation is held');
 const newer=concurrentFacts(f),injected=true;fs.writeFileSync(release,'release');
 const outcome=await reply;assert.equal(outcome.error,undefined);const out=outcome.result,saved=f.record();
 observations(`${blocked.id}-${command}-${mode}`,{injected:()=>assert.equal(injected,true),blocked:()=>assert.equal(out.exitCode,1,out.message),diagnostic:()=>assert.match(out.message,/ordinary approval workflow/),ownEvidence:()=>assert.equal(saved.replayEvidence.outcome,'blocked'),stepEvidence:()=>assert.equal(saved.done.verify.replayEvidence.outcome,'blocked'),done:()=>assert.deepEqual(saved.done.independent,newer.done.independent),decisions:()=>assert.deepEqual(saved.decisions,newer.decisions),question:()=>assert.deepEqual(saved.question,newer.question),authority:()=>assert.deepEqual(saved.replayAdoption,authority),anchor:()=>assert.deepEqual(saved.replayBaseline,anchor),journal:()=>assert.equal(fs.readFileSync(journal,'utf8'),bytes),noPush:()=>{assert.equal(f.pushes.length,0);assert.equal(f.prs.length,0);}});
});
const publication=nativeCase('adopted-corpus-publication-save-retains-own-intent');
for(const command of publication.given.publicCommandVariants)test(`2753 adopted ${command} retains publication and concurrent intent`,async t=>{
 const {f}=await adoptedCorpusRun(t),run=f.record();
 if(command==='approveRun publication'){stage(run);run.areas[0].before='approve';run.gate={area:'code',at:1,kind:'approve-pr'};writeRun(run,f.ports);}
 if(command==='existing publication retry'){fs.writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');const first=await runner.stepDone({step:'verify',summary:'First publication',cwd:run.root},f.ports);assert.equal(first.exitCode,0,first.message);}
 const before=f.record(),authority=structuredClone(before.replayAdoption),anchor=structuredClone(before.replayBaseline);fs.writeFileSync(join(run.root,'value.mjs'),'export const value=3;\n');
 const journal=join(run.runDir,'delivery-journal.json');fs.writeFileSync(journal,'{"requests":[]}\n');const bytes=fs.readFileSync(journal,'utf8');
 const {ports,events,marker,bodies}=guardEffects(f);let newer,injected=false;const external=ports.execFile;
 ports.execFile=async(file,args,opts)=>{if(!injected&&file==='git'&&args[0]==='status'){injected=true;newer=concurrentFacts(f);}return external(file,args,opts);};
 // Log actual native validator Git calls: one full corpus scan per publication,
 // after its automatic commit. No clock/barrier runs inside ordinary ownership.
 const bin=join(f.base,'git-bin'),log=join(f.base,'git.log');fs.mkdirSync(bin);fs.writeFileSync(join(bin,'git'),`#!/bin/sh\nif [ -e '${marker}' ]; then echo validator-under-owner >> '${log}'; exit 42; fi\nprintf '%s\\n' "$*" >> '${log}'\nexec /usr/bin/git "$@"\n`,{mode:0o755});const oldPath=process.env.PATH;process.env.PATH=`${bin}:${oldPath}`;
 let out;try{out=command==='approveRun publication'?await runner.approveRun({ref:'17',cwd:f.source},ports):await runner.stepDone({step:'verify',summary:'Own published verify',cwd:run.root},ports);}finally{process.env.PATH=oldPath;}
 const commands=fs.readFileSync(log,'utf8').trim().split('\n'),saved=f.record(),scan=commands.findIndex(line=>line.startsWith('merge-base --is-ancestor ')),commit=commands.findIndex(line=>line.startsWith('commit '));
 observations(`${publication.id}-${command}`,{injected:()=>assert.equal(injected,true),success:()=>assert.equal(out.exitCode,0,out.message),done:()=>assert.deepEqual(saved.done.independent,newer.done.independent),question:()=>assert.deepEqual(saved.question,newer.question),decision:()=>assert.ok(saved.decisions.some(item=>item.at===2000)),prField:()=>{if(newer.pr[0])assert.deepEqual(saved.pr[0].review,newer.pr[0].review);},ownReplay:()=>{assert.equal(saved.replayEvidence?.outcome,'blocked');assert.deepEqual(saved.done.verify.replayEvidence,saved.replayEvidence);},authority:()=>assert.deepEqual(saved.replayAdoption,authority),anchor:()=>assert.deepEqual(saved.replayBaseline,anchor),journal:()=>assert.equal(fs.readFileSync(journal,'utf8'),bytes),publication:()=>assert.equal(saved.pr.length,1),nativeLocalBoundary:()=>assert.ok(!commands.includes('validator-under-owner')),oneValidation:()=>assert.equal(commands.filter(line=>line.startsWith('merge-base --is-ancestor ')).length,1),commitBeforeValidation:()=>assert.ok(commit>=0&&commit<scan),pendingBeforePush:()=>{if(command==='existing publication retry'){const edit=events.indexOf('gh pr edit'),push=events.indexOf('git push origin');assert.ok(edit>=0&&edit<push);assert.ok(bodies.some(observation=>observation.index<push&&observation.body.includes('publication-pending')));}}});
});
