// Generated from prompts/test/autopilot-factory.prompt.md.
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {ordinaryCapabilities} from '../../runtime-fake.mjs';

// HTTP-shaped fetch port, entirely in memory. No socket or service is started.
export function factoryInterpreter() {
  const f={mode:'verdict',posts:[],gets:[],polls:new Map(),jobs:new Map(),origin:'https://factory.invalid'};
  const usage={calls:1,model:'unknown',requested_model:'unknown',seconds:0,input_tokens:0,output_tokens:0};
  const job=(id,command,state,result=null)=>({requestId:id,id,command,state,result,usage,engine_sha:'eae2202a68d00ab762fcbbf1eba0d8607a132a15',report_url:`${f.origin}/r/${createHash('sha256').update(id).digest('hex').slice(0,32)}`});
  const check=(id,state,actual=2)=>job(id,'check',state,['queued','running'].includes(state)?null:{exitCode:state==='passed'?0:1,outcome:state==='passed'?'Pass':state==='failed'?'Fail':'Inconclusive',refusals:state==='unknown'?[{code:'service-restarted'}]:state==='refused'?[{code:'graph-provider-failure'}]:[],
    report:{samples:[{sample:1,steps:[{checks:[{criterion_id:'AC1',target:'result',path:'/value',op:'equals',expected:2,actual,passed:actual===2}]}]}],criterion_results:['passed','failed'].includes(state)?[{criterion_id:'AC1',status:state}]:[]}});
  f.fetch=async (url,options={})=>{
    assert.equal(new URL(url).origin,f.origin,'external interpreter network is forbidden');
    let reply;
    if(options.method==='POST') {
      const request=JSON.parse(await options.body.get('request').text()),command=new URL(url).pathname.split('/').at(-1);
      f.posts.push({command,request});
      if(command==='lint') {
        const tar=Buffer.from(await options.body.get('source').arrayBuffer());
        const listing=spawnSync('tar',['-tf','-'],{input:tar,encoding:'utf8'});assert.equal(listing.status,0,listing.stderr);
        const sources=listing.stdout.trim().split('\n').filter(Boolean).map(path=>{const r=spawnSync('tar',['-xOf','-',path],{input:tar});assert.equal(r.status,0);return {path,bytes:r.stdout};});
        const tests=sources.filter(s=>{try{return JSON.parse(s.bytes).schema_version==='prompt-runtime.program-scenario.v1';}catch{return false;}}).map(s=>({path:s.path,verdict:'passed',capabilities:ordinaryCapabilities(sources,s.path)}));
        reply=job(request.requestId,'lint','passed',{exitCode:0,refusals:[],capabilities:tests.map(t=>({path:t.path,report:t.capabilities})),capabilities_complete:true,
          report:{verdict:'passed',lint:{complete:true,tests},program:{prompts:[{path:'value.prompt.md',state:'draft',admission_state:'draft',interface:{calls:[]}}],refused_prompts:[]}}});
      } else {
        assert.equal(command,'check');
        const tar=Buffer.from(await options.body.get('source').arrayBuffer());
        const selected=spawnSync('tar',['-xOf','-','value.prompt.md'],{input:tar,encoding:'utf8'});assert.equal(selected.status,0);
        const actual=Number(/Return the value (\d+)/.exec(selected.stdout)?.[1]);assert.ok(Number.isInteger(actual),'the fake knows only the synthetic constant-value language');
        const state={verdict:actual===2?'passed':'failed','no-verdict':'unknown',refused:'refused',slow:'running'}[f.mode];assert.ok(state,'unknown interpreter program');
        reply=check(request.requestId,state,actual);f.jobs.set(request.requestId,{mode:f.mode,actual});
      }
    } else {
      const id=new URL(url).pathname.split('/').at(-1);f.gets.push(id);
      const saved=f.jobs.get(id);assert.ok(saved,'only dispatched jobs can be polled');
      const polls=(f.polls.get(id)??0)+1;f.polls.set(id,polls);
      reply=check(id,saved.mode==='slow' && polls<3?'running':saved.mode==='no-verdict'?'unknown':saved.mode==='refused'?'refused':saved.actual===2?'passed':'failed',saved.actual);
    }
    return new Response(JSON.stringify(reply),{status:200,headers:{'content-type':'application/json'}});
  };
  return f;
}
