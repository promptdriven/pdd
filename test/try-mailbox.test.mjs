import test from 'node:test';
import assert from 'node:assert/strict';
import {randomUUID} from 'node:crypto';
import {existsSync,mkdirSync,readFileSync,readdirSync,renameSync,rmSync,symlinkSync,writeFileSync,linkSync} from 'node:fs';
import {join} from 'node:path';
import {harbor,fakeRuntime,portsFor,TOKEN,PLACE} from './runtime-fake.mjs';
import {prepareMailbox,mailboxCall,watchMailbox} from '../src/try-mailbox.mjs';
const wait=ms=>new Promise(done=>setTimeout(done,ms));
async function until(fn){for(let n=0;n<100;n++){if(fn())return;await wait(10);}assert.fail('mailbox did not finish in time');}
async function fixture(t){
  let end=async()=>{};
  const setup=harbor({after:cleanup=>t.after(async()=>{await end();cleanup();})});
  const fake=await fakeRuntime(t,(e,f)=>{
    const result={stdout:'observed\n',stderr:'program error\n',exit_code:7};
    if(e.json){const j={...f.job(e.json.requestId,'call','passed',{program_result:result,report:{result}},1),session_id:d.sessionId};f.jobs.set(j.id,j);return {status:200,json:j};}
    return {status:200,json:f.jobs.get(e.url.split('/').at(-1))};
  });
  const d={root:setup.repo,sessionId:randomUUID(),origin:fake.origin,login:'octo',prompt:PLACE,operation:'main',promptHash:'pinned'};
  d.mailbox=prepareMailbox(d.root,d.sessionId);
  const ports=portsFor({}).ports,identity={login:'octo',token:TOKEN};
  const store={folder(name){const p=join(setup.state,name);mkdirSync(p,{recursive:true,mode:0o700});return p;},posted(folder,id){writeFileSync(join(folder,id+'.posted'),'sent',{flag:'wx',mode:0o600});},write(path,data){writeFileSync(path,JSON.stringify(data),{mode:0o600});}};
  let controller=new AbortController(),watching;
  const start=()=>{controller=new AbortController();watching=watchMailbox({ports,identity,store,signal:controller.signal},d);watching.catch(()=>{});};
  end=async()=>{controller.abort();try{await watching;}catch{}};start();
  return {setup,fake,d,start,stop:end,get watching(){return watching;}};
}

test('NEXT11 mailbox: no agent network, real streams/exit, restart claims never redispatch',async t=>{
  const f=await fixture(t);
  const answer=await mailboxCall(f.d,{argv:['add']},{fetch(){assert.fail('agent must not fetch');},gh(){assert.fail('agent must not read gh');}});
  assert.deepEqual(answer.result,{stdout:'observed\n',stderr:'program error\n',exit_code:7});
  assert.equal(f.fake.jsonPosts.length,1);
  const reply=readdirSync(join(f.d.mailbox,'replies')).find(p=>p.endsWith('.json'));
  await f.stop();rmSync(join(f.d.mailbox,'replies',reply));f.start();
  await until(()=>existsSync(join(f.d.mailbox,'replies',reply)));
  assert.match(JSON.parse(readFileSync(join(f.d.mailbox,'replies',reply))).error,/unknown.*previous dispatch/);
  assert.equal(f.fake.jsonPosts.length,1);
});

test('NEXT11 mailbox: reject added authority and hardlinked requests with zero dispatch',async t=>{
  const f=await fixture(t);
  for(const kind of ['authority','hardlink']){
    const id=randomUUID(),path=join(f.d.mailbox,'requests',id+'.json');
    writeFileSync(path,JSON.stringify({id,sessionId:f.d.sessionId,input:{argv:['add']},...(kind==='authority'?{origin:'https://other.example'}:{})}),{mode:0o600});
    if(kind==='hardlink')linkSync(path,join(f.setup.home,id));
    const reply=join(f.d.mailbox,'replies',id+'.json');await until(()=>existsSync(reply));
    assert.match(JSON.parse(readFileSync(reply)).error,/invalid|Unsafe/);
  }
  assert.equal(f.fake.jsonPosts.length,0);
});

test('NEXT11 mailbox: replaced reply directory is rejected before dispatch or outside write',async t=>{
  const f=await fixture(t),outside=join(f.setup.sandbox,'outside');mkdirSync(outside);
  renameSync(join(f.d.mailbox,'replies'),join(f.d.mailbox,'original-replies'));
  symlinkSync(outside,join(f.d.mailbox,'replies'));
  const id=randomUUID();writeFileSync(join(f.d.mailbox,'requests',id+'.json'),JSON.stringify({id,sessionId:f.d.sessionId,input:{argv:[]}}),{mode:0o600});
  await assert.rejects(f.watching,/Unsafe private Try folder/);
  assert.deepEqual(readdirSync(outside),[]);assert.equal(f.fake.jsonPosts.length,0);
});
