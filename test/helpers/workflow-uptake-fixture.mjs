import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { join } from 'node:path';
import { hostname } from 'node:os';
import { fixture } from './workflow-delivery-fixture.mjs';
import * as runner from '../../src/workflow-runner.mjs';
import { runPdd } from '../../src/pdd-cli.mjs';
export { runner, fs, hostname };
export async function uptakeFixture(t) {
 const f=await fixture(t,{agent:'codex',name:'bug'});assert.equal((await f.run()).exitCode,0);
 const run=f.record(),chat=run.chats.at(-1);
 f.path=join(run.runDir,'delivery-journal.json');
 f.entry=(id='r1',extra={})=>({id,text:'Explain the chosen value',kind:'change',area:chat.area,paneId:chat.paneId,state:'delivered',at:500,deliveredAt:1000,...extra});
 f.orphan=()=>f.entry('unrelated-orphan',{state:'pending',inFlight:true,owner:{pid:654321,hostname:hostname(),token:'dead'},ackedAt:17,ackSummary:'Preserve unrelated fields'});
 f.save=entries=>fs.writeFileSync(f.path,JSON.stringify({requests:entries},null,2)+'\n');
 f.bytes=()=>fs.readFileSync(f.path,'utf8');f.read=()=>JSON.parse(f.bytes()).requests;
 f.change=(text='Explain the chosen value',ports=f.ports)=>runner.changeRun({ref:'17',text,cwd:f.source},ports);
 f.status=(options={},ports=f.ports)=>runner.runStatus({ref:'17',cwd:f.source,...options},ports);
 f.row=async(options={},ports=f.ports)=>JSON.parse((await f.status({json:true,...options},ports)).message).runs[0];
 f.ack=async(...args)=>{
  const requestId=args.length?args[0]:'r1',summary=args.length>1?args[1]:'Added reason',options=args[2]??{};
  // Use the actual CLI route on the old control too: unsupported ACK is exit 2,
  // never an undefined export crash. Non-string module inputs use the injected binding
  // after the public route has admitted a valid command shape.
  const out=[],err=[];
  const code=await runPdd(['workflow','ack','r1','--summary','Added reason'],{cwd:options.cwd??f.record().root,env:f.ports.env,
   stdout:{write:s=>out.push(s)},stderr:{write:s=>err.push(s)},workflowRunner:{acknowledgeRequest:input=>runner.acknowledgeRequest({...input,requestId,summary},options.ports??f.ports)}});
  return {exitCode:code,message:[...out,...err].join('')};
 };
 f.positive=async()=>{f.save([f.entry(),f.orphan()]);assert.equal((await f.ack()).exitCode,0,'a valid delivered request must be acknowledged through the CLI');};
 f.done=(step='reproduce',ports=f.ports)=>runner.stepDone({step,summary:'All requested work is complete',cwd:f.record().root},ports);
 f.sent=()=>f.herdr.calls.filter(a=>a[0]==='agent'&&a[1]==='prompt');
 return f;
}
export const facts=(text,items)=>{for(const item of items)assert.ok(text.toLowerCase().includes(String(item).toLowerCase()),`missing ${item} in ${text}`);};
export const viewOptions=[{}, {json:true}, {ref:undefined}, {ref:undefined,all:true}, {ref:undefined,cancelled:true}];
