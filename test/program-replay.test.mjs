import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { runPdd } from '../src/pdd-cli.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { harbor, fakeRuntime, portsFor, PLACE, TOKEN } from './runtime-fake.mjs';

function entry(root,cli=true) {
  const schema=cli?{type:'object',properties:{argv:{type:'array',items:{type:'string'}}},required:['argv'],additionalProperties:false}:{type:'object',properties:{amount:{type:'integer',minimum:1}},required:['amount'],additionalProperties:false};
  const output=cli?{type:'object',properties:{stdout:{type:'string'},stderr:{type:'string'},exit_code:{type:'integer'}},required:['stdout','stderr','exit_code'],additionalProperties:false}:{type:'object',properties:{},additionalProperties:false};
  const iface={status:'draft',prose_sha256:'',entries:[{operation:'main',input_schema:schema,result_schema:output,errors:[]}],calls:[],resources:[],limits:{max_steps:1,max_model_calls:1},conventions:cli?['input_schema','result_schema'].map(k=>({path:'/entries/0/'+k,convention:'cli'})):[]};
  let text='# replay\n\nDeterministic fake program.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify(iface)+'\n```\n</details>\n';
  text=text.replace('"prose_sha256":""','"prose_sha256":"'+proseSha256(text)+'"');writeFileSync(join(root,PLACE),text);
}
async function setup(t, options={}) {
  const h=harbor(t,root=>entry(root,options.cli!==false));
  const fake=await fakeRuntime(t,(e,f)=>{
    if(e.command==='lint')return {status:200,json:f.lint(e.request.requestId)};
    if(e.command==='try')return {status:200,json:f.tryJob(e.request.requestId)};
    if(e.method==='DELETE')return {status:200,json:f.stopJob(e.headers['x-request-id'],e.url.split('/').at(-1))};
    if(e.json){
      const result={stdout:'replayed\n',stderr:'',exit_code:0};
      const report={result,...(options.world===false?{}:{world:{saved:true}}),...(options.action?{action_id:'exact-action'}:{})};
      const job={...f.job(e.json.requestId,'call','passed',{program_result:result,report},1),session_id:e.url.split('/')[3]};f.jobs.set(e.json.requestId,job);return {status:200,json:job};
    }
    if(e.url.endsWith('/state'))return {status:200,json:{world:{unrelated:'latest'},actions:[{action_id:'different',world:{wrong:true}},{action_id:'exact-action',input_world:{before:'exact'},world:{after:'exact'}}]}};
    if(f.jobs.has(e.url.split('/').at(-1))) {
      const job=f.jobs.get(e.url.split('/').at(-1));if(options.recovered)job.result.report.world={recovered:true};return {status:200,json:job};
    }
    return {status:404,json:{error:{message:'Not found'}}};
  });
  const env={HOME:h.home,PDD_STATE_DIR:h.state,PDD_RUNTIME_URL:fake.origin,PATH:'/usr/bin:/bin'};
  const invoke=async(args,prefix=[],extra={})=>{const io=portsFor(env,{stdin:Readable.from([]),...extra});const code=await runPdd([...prefix,PLACE,...args],{cwd:h.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});return {code,...io};};
  const stored=name=>{const run=join(h.repo,'.pdd/run');return JSON.parse(readFileSync(join(run,readdirSync(run)[0],name),'utf8'));};
  return {...h,fake,env,invoke,stored};
}

test('shell launcher executes argv[] once and carries selected starting data',async t=>{
  const h=await setup(t);const bin=join(h.home,'fake-bin');mkdirSync(bin);
  writeFileSync(join(bin,'gh'),`#!/bin/sh\nif [ "$1" = auth ]; then printf '%s\\n' '${TOKEN}'; else printf '%s\\n' 'octo 4242'; fi\n`,{mode:0o700});
  h.env.PATH=bin+':/usr/bin:/bin';writeFileSync(join(h.repo,'seed.json'),'{"selected":true}');
  let command;
  const r=await h.invoke([],['--data','seed.json'],{shell:async(shell,env)=>new Promise((done,reject)=>{
    const child=spawn('replay',[],{cwd:h.repo,env,stdio:['ignore','pipe','pipe']});let out='',err='';child.stdout.on('data',c=>out+=c);child.stderr.on('data',c=>err+=c);child.once('error',reject);child.once('exit',code=>{command={code,out,err};done(code);});
  })});
  assert.equal(r.code,0,r.ports.stderr.text+command?.err);assert.equal(command.out,'replayed\n');
  assert.equal(h.fake.jsonPosts.length,1);assert.deepEqual(h.fake.jsonPosts[0].json.input,{argv:[]});assert.deepEqual(h.fake.posts.find(p=>p.command==='try').request.initial_world,{selected:true});assert.equal(h.fake.posts.filter(p=>p.command==='try').length,1);
});

test('missing confirmed world blocks new calls until same-ID GET recovery',async t=>{
  const options={world:false};const h=await setup(t,options);
  const first=await h.invoke(['change']);assert.equal(first.code,125);assert.match(first.ports.stderr.text,/did not confirm the program data/);
  const session=h.stored('session.json');assert.equal(session.pending.id,h.fake.jsonPosts[0].json.requestId);
  const second=await h.invoke(['different']);assert.equal(second.code,125);assert.equal(h.fake.jsonPosts.length,1);
  options.recovered=true;const recovered=await h.invoke([],['--read',session.pending.id]);assert.equal(recovered.code,0,recovered.ports.stderr.text);assert.deepEqual(h.stored('data.json'),{recovered:true});assert.equal(h.fake.jsonPosts.length,1);assert.ok(h.fake.gets.some(g=>g.url.endsWith(session.pending.id)));
});

test('matched action snapshots win over unrelated latest state',async t=>{
  const h=await setup(t,{action:true});const r=await h.invoke(['change']);assert.equal(r.code,0,r.ports.stderr.text);
  assert.deepEqual(h.stored('data.json'),{after:'exact'});const last=h.stored('last.json');assert.deepEqual(last.data_before,{before:'exact'});assert.deepEqual(last.data_after,{after:'exact'});
});

test('literal input cannot bypass local schema validation with a Story reference',async t=>{
  const h=await setup(t,{cli:false});const r=await h.invoke(['--input','{"$step_result":1,"amount":0}']);assert.equal(r.code,2);assert.equal(r.clock.gh.length,0);assert.equal(h.fake.posts.length,0);
});

test('external saved-world edit replaces session instead of reusing stale runtime world',async t=>{
  const h=await setup(t);assert.equal((await h.invoke(['change'])).code,0);
  const run=join(h.repo,'.pdd/run');writeFileSync(join(run,readdirSync(run)[0],'data.json'),'{"external":"selection"}');
  const r=await h.invoke(['next']);assert.equal(r.code,0,r.ports.stderr.text);assert.equal(h.fake.posts.filter(p=>p.command==='try').length,2);assert.deepEqual(h.fake.posts.filter(p=>p.command==='try').at(-1).request.initial_world,{external:'selection'});assert.equal(h.fake.deletes.length,1);
});
