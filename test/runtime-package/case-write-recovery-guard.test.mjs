import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {pathToFileURL} from 'node:url';
import {fixture,closed,read,implementation} from '../helpers/runtime-workspace-fixture.mjs';
import {acquireCaseWriteOwnership} from '../../src/runtime-seam.mjs';

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

function acquireInChild(f,{cancel=false,maxWaitMs=cancel?5000:35,settleWithinMs=1000,disappearingGuard=false}={}){
  const request={root:f.root,testPath:f.second,handoff:closed(f.second)};
  // Isolate the public native boundary: a synchronous retry bug cannot block
  // the test runner's own timeout or cleanup. Liveness uses the native adapter.
  const code=String.raw`
    import * as fs from 'node:fs';
    import {acquireCaseWriteOwnership} from ${JSON.stringify(pathToFileURL(implementation).href)};
    const controller=new AbortController(),started=Date.now();
    let collisions=0;
    const guard=${JSON.stringify(f.guard)};
    const files=${disappearingGuard}?{
      lstat:fs.lstatSync,read:fs.readFileSync,open:fs.openSync,write:fs.writeFileSync,
      close:fs.closeSync,sync:fs.fsyncSync,stat:fs.fstatSync,mkdir:fs.mkdirSync,
      list:fs.readdirSync,rename:fs.renameSync,unlink:fs.unlinkSync,realpath:fs.realpathSync,
      link(from,to){
        if(to!==guard)return fs.linkSync(from,to);
        // Order a real peer collision, then remove its guard before inspection.
        fs.writeFileSync(guard,'peer recovery guard');
        try{return fs.linkSync(from,to);}
        catch(error){if(error.code==='EEXIST'){collisions++;fs.unlinkSync(guard);}throw error;}
      }
    }:undefined;
    const timer=${cancel}?setTimeout(()=>controller.abort(),35):undefined;
    process.stdout.write(JSON.stringify({entered:true})+'\n');
    try{
      const lease=await acquireCaseWriteOwnership({...${JSON.stringify(request)},signal:controller.signal},
        {env:process.env,files,maxWaitMs:${maxWaitMs}});
      lease.release();
      process.stdout.write(JSON.stringify({outcome:'acquired',collisions,elapsed:Date.now()-started})+'\n');
    }catch(error){
      process.stdout.write(JSON.stringify({outcome:'refused',message:error.message,aborted:controller.signal.aborted,collisions,elapsed:Date.now()-started})+'\n');
    }finally{clearTimeout(timer);}
  `;
  const result=spawnSync(process.execPath,['--input-type=module','-e',code],{env:f.env,encoding:'utf8',timeout:settleWithinMs+500});
  const lines=result.stdout.trim().split('\n');
  assert.deepEqual(JSON.parse(lines[0]),{entered:true},result.stderr);
  assert.equal(result.error?.code,undefined,'recovery acquisition must settle within the child timeout');
  assert.equal(result.status,0,result.stderr);
  const answer=JSON.parse(lines[1]);
  assert.ok(answer.elapsed<settleWithinMs,'the local wait or cancellation must bound acquisition');
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

for(const stop of ['deadline','cancel']){
  test(`recovery guard disappearing after native link collision honors ${stop}`,async t=>{
    const f=await abandonedOwner(t);
    const before=read(f.root,f.second),otherBefore=read(f.root,f.test),lockBefore=fs.readFileSync(f.lock,'utf8');
    const answer=acquireInChild(f,{cancel:stop==='cancel',disappearingGuard:true});
    assert.equal(answer.outcome,'refused');
    assert.equal(answer.aborted,stop==='cancel');
    assert.match(answer.message,stop==='cancel'?/cancelled/:/another saver or editor/);
    assert.ok(answer.collisions>=1,'acquisition must encounter a native recovery-guard collision');
    assert.equal(read(f.root,f.second),before);
    assert.equal(read(f.root,f.test),otherBefore);
    assert.equal(fs.readFileSync(f.lock,'utf8'),lockBefore);
    assert.throws(()=>fs.lstatSync(f.guard),{code:'ENOENT'});
    assert.equal(fs.readdirSync(f.area).some(name=>name.endsWith('.tmp')),false);
  });
}

test('an ended owner without a recovery guard can still hand over ownership',async t=>{
  const f=await abandonedOwner(t),before=read(f.root,f.second);
  const answer=acquireInChild(f,{maxWaitMs:5000,settleWithinMs:6000});
  assert.equal(answer.outcome,'acquired',JSON.stringify(answer));
  assert.equal(read(f.root,f.second),before);
  assert.throws(()=>fs.lstatSync(f.lock),{code:'ENOENT'});
  assert.throws(()=>fs.lstatSync(f.guard),{code:'ENOENT'});
  assert.deepEqual(fs.readdirSync(f.area),[]);
});
