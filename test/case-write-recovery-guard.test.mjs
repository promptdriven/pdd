import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {pathToFileURL} from 'node:url';
import {fixture,closed,read,implementation} from './helpers/runtime-workspace-fixture.mjs';
import {acquireCaseWriteOwnership} from '../src/runtime-client.mjs';

async function abandonedOwner(t){
  const f=fixture(t);
  const first=await acquireCaseWriteOwnership({root:f.root,testPath:f.second,handoff:closed(f.second)},{env:f.env});
  t.after(()=>first.release());
  const area=join(f.state,'case-import');
  const lock=join(area,fs.readdirSync(area).find(name=>name.endsWith('.lock')));
  const ended=spawnSync(process.execPath,['-e',''],{encoding:'utf8',timeout:1500});
  assert.equal(ended.status,0,ended.stderr);
  assert.throws(()=>process.kill(ended.pid,0),{code:'ESRCH'},'the recorded owner must have exited');
  const owner=JSON.parse(fs.readFileSync(lock,'utf8'));
  fs.writeFileSync(lock,JSON.stringify({...owner,pid:ended.pid}));
  return{...f,area,lock,guard:lock+'.recover'};
}

function acquireInChild(f,{cancel=false}={}){
  const request={root:f.root,testPath:f.second,handoff:closed(f.second)};
  // Isolate the public native boundary: a synchronous retry bug cannot block
  // the test runner's own timeout or cleanup. Liveness uses the native adapter.
  const code=String.raw`
    import {acquireCaseWriteOwnership} from ${JSON.stringify(pathToFileURL(implementation).href)};
    const controller=new AbortController(),started=Date.now();
    const timer=${cancel}?setTimeout(()=>controller.abort(),35):undefined;
    process.stdout.write(JSON.stringify({entered:true})+'\n');
    try{
      const lease=await acquireCaseWriteOwnership({...${JSON.stringify(request)},signal:controller.signal},
        {env:process.env,maxWaitMs:${cancel?5000:35}});
      lease.release();
      process.stdout.write(JSON.stringify({outcome:'acquired',elapsed:Date.now()-started})+'\n');
    }catch(error){
      process.stdout.write(JSON.stringify({outcome:'refused',message:error.message,aborted:controller.signal.aborted,elapsed:Date.now()-started})+'\n');
    }finally{clearTimeout(timer);}
  `;
  const result=spawnSync(process.execPath,['--input-type=module','-e',code],{env:f.env,encoding:'utf8',timeout:1500});
  const lines=result.stdout.trim().split('\n');
  assert.deepEqual(JSON.parse(lines[0]),{entered:true},result.stderr);
  assert.equal(result.error?.code,undefined,'recovery acquisition must settle within the child timeout');
  assert.equal(result.status,0,result.stderr);
  const answer=JSON.parse(lines[1]);
  assert.ok(answer.elapsed<1000,'the local wait or cancellation must bound acquisition');
  return answer;
}

for(const kind of ['symlink','directory']){
  test(`abandoned owner with a ${kind} recovery guard refuses bounded acquisition`,async t=>{
    const f=await abandonedOwner(t);
    if(kind==='symlink')fs.symlinkSync(join(f.root,f.second),f.guard);
    else fs.mkdirSync(f.guard);
    const targetBefore=read(f.root,f.second),otherBefore=read(f.root,f.test);
    const lockBefore=fs.readFileSync(f.lock,'utf8'),guardBefore=fs.lstatSync(f.guard);
    const answer=acquireInChild(f);
    assert.equal(answer.outcome,'refused');
    assert.match(answer.message,/unsafe/);
    assert.equal(read(f.root,f.second),targetBefore);
    assert.equal(read(f.root,f.test),otherBefore);
    assert.equal(fs.readFileSync(f.lock,'utf8'),lockBefore);
    const guardAfter=fs.lstatSync(f.guard);
    assert.equal(guardAfter.ino,guardBefore.ino);
    assert.equal(guardAfter.mode,guardBefore.mode);
    if(kind==='symlink')assert.equal(fs.readlinkSync(f.guard),join(f.root,f.second));
    else assert.deepEqual(fs.readdirSync(f.guard),[]);
    assert.equal(fs.readdirSync(f.area).some(name=>name.endsWith('.tmp')),false);
  });
}

for(const stop of ['deadline','cancel']){
  test(`regular recovery guard contention honors ${stop}`,async t=>{
    const f=await abandonedOwner(t),guardBytes='another recovery owns this guard';
    fs.writeFileSync(f.guard,guardBytes);
    const before=read(f.root,f.second),lockBefore=fs.readFileSync(f.lock,'utf8');
    const answer=acquireInChild(f,{cancel:stop==='cancel'});
    assert.equal(answer.outcome,'refused');
    assert.equal(answer.aborted,stop==='cancel');
    assert.match(answer.message,stop==='cancel'?/cancelled/:/another saver or editor/);
    assert.equal(read(f.root,f.second),before);
    assert.equal(fs.readFileSync(f.lock,'utf8'),lockBefore);
    assert.equal(fs.readFileSync(f.guard,'utf8'),guardBytes);
    assert.equal(fs.readdirSync(f.area).some(name=>name.endsWith('.tmp')),false);
  });
}

test('an ended owner without a recovery guard can still hand over ownership',async t=>{
  const f=await abandonedOwner(t),before=read(f.root,f.second);
  assert.equal(acquireInChild(f).outcome,'acquired');
  assert.equal(read(f.root,f.second),before);
  assert.throws(()=>fs.lstatSync(f.lock),{code:'ENOENT'});
  assert.throws(()=>fs.lstatSync(f.guard),{code:'ENOENT'});
  assert.deepEqual(fs.readdirSync(f.area),[]);
});
