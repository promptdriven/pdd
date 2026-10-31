import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {hostname} from 'node:os';
import {fixture} from './helpers/workflow-delivery-fixture.mjs';
import * as storage from '../src/workflow-runs.mjs';
import {cancelRun,runStatus,changeRun} from '../src/workflow-runner.mjs';
const inventory=JSON.parse(fs.readFileSync(new URL('./workflow-concurrent-progress/cases.json',import.meta.url)));
const row=id=>assert.ok(inventory.cases.some(c=>c.id===id));
function owner(run,value){const path=join(run.runDir,'.ordinary-owner');fs.mkdirSync(path,{recursive:true});for(const name of fs.readdirSync(path))fs.rmSync(join(path,name));if(value)fs.writeFileSync(join(path,`owner-${value.token}.json`),JSON.stringify(value));return path;}
for(const kind of ['dead','live','foreign','unknown','missing','malformed'])test(`2753 ordinary ${kind} ownership recovery and visibility`,async t=>{
 row('ordinary-owner-recovery');const f=await fixture(t,{agent:'codex',name:'bug'});await f.run();const run=f.record(),token='held-owner';
 const value=kind==='missing'?null:{pid:kind==='live'?process.pid:2147483647,hostname:kind==='foreign'?'another-host':hostname(),token};
 const path=owner(run,value);if(kind==='malformed')fs.writeFileSync(join(path,`owner-${token}.json`),'{');
 const before=fs.readFileSync(join(run.runDir,'status.json'),'utf8'),entries=fs.readdirSync(path);
 const ports={...f.ports,...(kind==='unknown'?{processIdentity:()=>{throw Object.assign(Error('Denied'),{code:'EPERM'});}}:{})};
 for(const options of [{ref:'17'},{},{all:true},{ref:'17',json:true},{json:true},{all:true,json:true}]){
  const out=await runStatus({...options,cwd:f.source},ports);assert.equal(out.exitCode,0,out.message);assert.match(out.message,/ordinary-owner/);
  if(options.json){const snapshot=JSON.parse(out.message).runs[0].ordinaryOwnership;assert.equal(snapshot.path,path);assert.equal(snapshot.token,kind==='missing'||kind==='malformed'?null:token);}
 }
 assert.equal(fs.readFileSync(join(run.runDir,'status.json'),'utf8'),before);assert.deepEqual(fs.readdirSync(path),entries);
 const start=performance.now(),out=await cancelRun({ref:'17',cwd:f.source},ports);
 if(kind==='dead'){assert.equal(out.exitCode,0,out.message);assert.equal(f.record().state,'cancelled');}
 else {assert.equal(out.exitCode,1);assert.equal(fs.readFileSync(join(run.runDir,'status.json'),'utf8'),before);assert.deepEqual(fs.readdirSync(path),entries);assert.equal((out.message.match(/retry/gi)||[]).length,1);assert.ok(performance.now()-start<1000,'finite short contention');}
});
test('2753 native ownership advertises identity and old release preserves replacement token',async t=>{
 row('ordinary-owner-recovery');const f=await fixture(t,{agent:'codex',name:'bug'});await f.run();const run=f.record();assert.equal(typeof storage.readRunOwnership,'function');let observed,replacement;
 storage.updateRun(run.runDir,latest=>{
  observed=storage.readRunOwnership(run.runDir,f.ports);assert.equal(observed.pid,process.pid);assert.equal(observed.hostname,hostname());assert.ok(observed.token);assert.equal(observed.warning,null);
  const path=observed.path;fs.rmSync(path,{recursive:true});fs.mkdirSync(path);replacement={pid:process.pid,hostname:hostname(),token:'replacement'};fs.writeFileSync(join(path,'owner-replacement.json'),JSON.stringify(replacement));latest.message='Committed';return latest;
 },f.ports);
 assert.deepEqual(JSON.parse(fs.readFileSync(join(observed.path,'owner-replacement.json'),'utf8')),replacement);
});
test('2753 ordinary contention releases journal within its short budget',async t=>{
 row('ordinary-contention-under-journal');const f=await fixture(t,{agent:'codex',name:'bug'});await f.run();const run=f.record();const path=owner(run,{pid:process.pid,hostname:hostname(),token:'live'});
 const start=performance.now(),out=await changeRun({ref:'17',cwd:f.source,text:'Keep my request'},f.ports);
 assert.equal(out.exitCode,1);assert.ok(performance.now()-start<1000);assert.equal((out.message.match(/retry/gi)||[]).length,1);
 const journal=join(run.runDir,'.delivery-journal.lock');assert.equal(fs.readdirSync(journal).filter(name=>name.startsWith('owner-')).length,0);
 fs.rmSync(path,{recursive:true});const again=await changeRun({ref:'17',cwd:f.source,text:'Another independent request'},f.ports);assert.equal(again.exitCode,0,again.message);
});

for(const listing of [false,true])for(const json of [false,true])test(`status ownership appears during PR read listing=${listing} json=${json}`,async t=>{
 const f=await fixture(t,{agent:'codex',name:'bug'});assert.equal((await f.run()).exitCode,0);const run=f.record();run.state='waiting';run.pr=[{url:'https://github.com/example/project/pull/23',stage:'story',number:23,state:'open',ci:'pending'}];storage.writeRun(run,f.ports);
 const before=fs.readFileSync(join(run.runDir,'status.json'),'utf8');let injected=false;
 const out=await runStatus({...(listing?{}:{ref:'17'}),json,cwd:f.source},{...f.ports,readPrStatus:async()=>{injected=true;const path=join(run.runDir,'.ordinary-owner');fs.mkdirSync(path,{recursive:true});fs.writeFileSync(join(path,'owner-independent.json'),JSON.stringify({pid:process.pid,hostname:hostname(),token:'independent'}));return {state:'open',ci:'success'};}});
 assert.equal(injected,true,'schedule reached PR await');assert.equal(out.exitCode,0,out.message);assert.equal(fs.readFileSync(join(run.runDir,'status.json'),'utf8'),before);if(json)assert.equal(JSON.parse(out.message).runs[0].ordinaryOwnership.token,'independent');else assert.match(out.message,/independent/);
});

for(const listing of [false,true])for(const json of [false,true])test(`status ownership appears during chat recovery listing=${listing} json=${json}`,async t=>{
 const f=await fixture(t,{agent:'codex',name:'bug'});assert.equal((await f.run()).exitCode,0);const run=f.record();run.chatFailure={area:'story',code:'unknown',at:1};run.chats.at(-1).startUnconfirmed=true;storage.writeRun(run,f.ports);
 const before=fs.readFileSync(join(run.runDir,'status.json'),'utf8');let injected=false;
 const out=await runStatus({...(listing?{}:{ref:'17'}),json,cwd:f.source},{...f.ports,herdr:async args=>{const reply=await f.ports.herdr(args);if(args[0]==='agent'&&args[1]==='get'){injected=true;const path=join(run.runDir,'.ordinary-owner');fs.mkdirSync(path,{recursive:true});fs.writeFileSync(join(path,'owner-independent.json'),JSON.stringify({pid:process.pid,hostname:hostname(),token:'independent'}));}return reply;}});
 assert.equal(injected,true,'schedule reached chat await');assert.equal(out.exitCode,0,out.message);assert.equal(fs.readFileSync(join(run.runDir,'status.json'),'utf8'),before);if(json)assert.equal(JSON.parse(out.message).runs[0].ordinaryOwnership.token,'independent');else assert.match(out.message,/independent/);
});
