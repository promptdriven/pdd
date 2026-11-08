import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {join} from 'node:path';
import {setTimeout as delay} from 'node:timers/promises';
import {fixture,closed,read,get,pendingId} from './helpers/runtime-workspace-fixture.mjs';
import {acquireCaseWriteOwnership,saveDoorCase,applyPendingCase} from '../src/runtime-client.mjs';

const nativeFiles={lstat:fs.lstatSync,read:fs.readFileSync,open:fs.openSync,write:fs.writeFileSync,close:fs.closeSync,sync:fs.fsyncSync,stat:fs.fstatSync,mkdir:fs.mkdirSync,list:fs.readdirSync,rename:fs.renameSync,unlink:fs.unlinkSync,realpath:fs.realpathSync,link:fs.linkSync};
const acquire=(f,ports={},signal)=>acquireCaseWriteOwnership({root:f.root,testPath:f.second,handoff:closed(f.second),signal},{env:f.env,...ports});
const lockPath=f=>join(f.state,'case-import',fs.readdirSync(join(f.state,'case-import')).find(name=>name.endsWith('.lock')));

test('owner release during the exclusive-create probe lets the next saver publish once',async t=>{
  const f=fixture(t),saved=f.saved(),other=read(f.root,f.test);
  const id=pendingId(saveDoorCase(f.root,saved,{env:f.env}));assert.ok(id);
  const first=await acquire(f);t.after(()=>first.release());
  const path=lockPath(f),receipt=join(f.state,'case-import',id.replace('.', '/')+'.received.json');
  const receiptBytes=fs.readFileSync(receipt,'utf8');let released=false;
  const release=()=>{first.release();released=true;};
  const files={...nativeFiles,
    lstat(target){const stat=fs.lstatSync(target);if(target===path&&!released)release();return stat;},
    link(from,to){if(to===path&&!released)release();return fs.linkSync(from,to);}
  };
  // A supported release after the leaf snapshot must not turn absence into an
  // unsafe-path refusal. An atomic creator can instead reach link directly.
  let second;
  await assert.doesNotReject(async()=>{second=await acquire(f,{files,maxWaitMs:10_000});});t.after(()=>second.release());
  assert.equal(released,true);
  assert.equal((await applyPendingCase({root:f.root,pendingId:id,writeOwnership:second},{env:f.env})).state,'committed');
  assert.equal((await applyPendingCase({root:f.root,pendingId:id,writeOwnership:second},{env:f.env})).duplicate,true);
  assert.equal(get(f.root,f.second).steps.filter(step=>step.step_id==='case-a').length,1);
  assert.deepEqual(get(f.root,f.second).steps[0],f.doc.steps[0]);
  assert.equal(read(f.root,f.test),other);assert.equal(fs.readFileSync(receipt,'utf8'),receiptBytes);
});

// These ports order real native operations. They neither manufacture EEXIST nor
// remove a lock directly: only the existing owner's supported release does that.
for(const window of ['after-collision','before-safe-read','before-open']){
  test(`normal lease release ${window} lets the next saver publish once`,async t=>{
    const f=fixture(t),saved=f.saved(),before=read(f.root,f.second),other=read(f.root,f.test);
    const id=pendingId(saveDoorCase(f.root,saved,{env:f.env}));
    assert.ok(id);
    const [identity,variant]=id.split('.');
    const receipt=join(f.state,'case-import',identity,variant+'.received.json');
    const receiptBytes=fs.readFileSync(receipt,'utf8');
    assert.deepEqual(JSON.parse(receiptBytes).saved,saved);
    const first=await acquire(f);t.after(()=>first.release());
    let collided=false,released=false,lock,lockStats=0;
    const release=()=>{first.release();released=true;assert.throws(()=>fs.lstatSync(lock),{code:'ENOENT'});};
    const files={...nativeFiles,
      link(from,to){try{return fs.linkSync(from,to);}catch(error){
        if(error.code==='EEXIST'&&to.endsWith('.lock')){collided=true;lock=to;if(window==='after-collision')release();}
        throw error;
      }},
      lstat(path){if(collided&&!released&&path===lock&&++lockStats===2&&window==='before-safe-read')release();return fs.lstatSync(path);},
      open(path,...args){if(collided&&!released&&path===lock&&window==='before-open')release();return fs.openSync(path,...args);}
    };
    const second=await acquire(f,{files,maxWaitMs:10_000});t.after(()=>second.release());
    assert.equal(collided,true,'must observe real EEXIST');assert.equal(released,true,'must release through the supported lease');
    assert.equal(read(f.root,f.second),before,'ownership acquisition does not publish');
    assert.equal((await applyPendingCase({root:f.root,pendingId:id,writeOwnership:second},{env:f.env})).state,'committed');
    assert.equal((await applyPendingCase({root:f.root,pendingId:id,writeOwnership:second},{env:f.env})).duplicate,true);
    const actual=get(f.root,f.second);assert.deepEqual(actual.steps[0],f.doc.steps[0]);
    assert.equal(actual.steps.filter(step=>step.step_id==='case-a').length,1);
    assert.equal(read(f.root,f.test),other);assert.equal(fs.readFileSync(receipt,'utf8'),receiptBytes);
  });
}

for(const kind of ['malformed','null','symlink','directory','read-error','read-enoent','foreign-owner','unknown-owner']){
  test(`present ${kind} lock never authorizes a contender`,async t=>{
    const f=fixture(t),before=read(f.root,f.second),first=await acquire(f);t.after(()=>first.release());
    const path=lockPath(f),original=fs.readFileSync(path,'utf8');let collisions=0;
    if(kind==='malformed')fs.writeFileSync(path,'{');
    if(kind==='null')fs.writeFileSync(path,'null');
    if(kind==='symlink'){fs.unlinkSync(path);fs.symlinkSync(join(f.root,f.second),path);}
    if(kind==='directory'){fs.unlinkSync(path);fs.mkdirSync(path);}
    if(kind==='foreign-owner')fs.writeFileSync(path,JSON.stringify({...JSON.parse(original),host:'another-host'}));
    const files={...nativeFiles,
      link(from,to){try{return fs.linkSync(from,to);}catch(error){if(error.code==='EEXIST'&&to===path)collisions++;throw error;}},
      read(fd,...args){if(['read-error','read-enoent'].includes(kind)&&fs.fstatSync(fd).ino===fs.lstatSync(path).ino){
        // Obtain a real native I/O error while the ownership record stays present.
        return fs.readFileSync(kind==='read-error'?f.root:join(f.parent,'missing-read-source'),'utf8');
      }return fs.readFileSync(fd,...args);}
    };
    await assert.rejects(acquire(f,{files,maxWaitMs:1500,...(kind==='unknown-owner'?{isAlive:()=>null}:{})}));
    assert.equal(read(f.root,f.second),before);assert.ok(fs.lstatSync(path));
    if(['malformed','null','read-error','read-enoent'].includes(kind))assert.equal(collisions,1,'a present unreadable record must refuse without retry');
    if(kind==='foreign-owner'||kind==='unknown-owner')assert.equal(fs.readFileSync(path,'utf8'),kind==='foreign-owner'?JSON.stringify({...JSON.parse(original),host:'another-host'}):original);
  });
}

test('a released lock under a newly unsafe ancestor still refuses ownership',async t=>{
  const f=fixture(t),before=read(f.root,f.second),first=await acquire(f);let collisions=0;
  const area=join(f.state,'case-import'),moved=area+'-moved';
  const files={...nativeFiles,link(from,to){try{return fs.linkSync(from,to);}catch(error){
    if(error.code==='EEXIST'&&to.endsWith('.lock')){
      collisions++;first.release();fs.renameSync(area,moved);fs.symlinkSync(moved,area);
    }
    throw error;
  }}};
  await assert.rejects(acquire(f,{files,maxWaitMs:10_000}));
  assert.equal(collisions,1);assert.equal(read(f.root,f.second),before);
});

for(const stop of ['deadline','cancel']){
  test(`repeated real release contention remains bounded by ${stop}`,{timeout:30_000},async t=>{
    const f=fixture(t),before=read(f.root,f.second),controller=new AbortController();
    let peer=await acquire(f),collisions=0; t.after(()=>peer?.release());
    const files={...nativeFiles,link(from,to){try{return fs.linkSync(from,to);}catch(error){
      if(error.code==='EEXIST'&&to.endsWith('.lock')){collisions++;peer.release();peer=null;if(stop==='cancel'&&collisions===3)controller.abort();}
      throw error;
    }}};
    const started=Date.now();
    await assert.rejects(acquire(f,{files,maxWaitMs:stop==='deadline'?2000:15_000,sleep:async ms=>{
      await delay(ms);if(!controller.signal.aborted)peer=await acquire(f);
    }},controller.signal),stop==='cancel'?/cancelled/:/another saver or editor/);
    assert.ok(collisions>=2,'must exercise repeated real release windows');
    assert.ok(Date.now()-started<20_000,'release retries must retain the existing finite wait/cancel bound');
    assert.equal(read(f.root,f.second),before);
  });
}
