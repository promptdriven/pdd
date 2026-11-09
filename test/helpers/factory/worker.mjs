import * as doctorFiles from 'node:fs';
// Generated from prompts/test/autopilot-factory.prompt.md.
// A new native process for each command/tick. Only external ports cross IPC.
import net from 'node:net';
import tls from 'node:tls';
import http from 'node:http';
import https from 'node:https';
import {runPdd} from '../../../src/pdd-cli.mjs';
import * as runner from '../../../src/workflow-runner.mjs';
import {tickAutopilot} from '../../../src/autopilot-launcher.mjs';
import {healthyMachine} from '../healthy-machine.mjs';
import {isolatedCheckCapacity} from '../check-machine.mjs';

const denyNetwork=()=>{throw Error('factory-network-denied');};
net.Socket.prototype.connect=denyNetwork;tls.connect=denyNetwork;http.request=denyNetwork;https.request=denyNetwork;
globalThis.fetch=denyNetwork;

let serial=0;
const pending=new Map();
const rpc=(method,...args)=>new Promise((resolve,reject)=>{const id=++serial;pending.set(id,{resolve,reject});process.send({id,method,args});});
process.on('message',async m=>{
  if(m.reply) {const p=pending.get(m.reply);pending.delete(m.reply);if(m.error)p.reject(Object.assign(Error(m.error.message),m.error));else p.resolve(m.value);return;}
  if(!m.start)return;
  try {
    const {base,cwd,packageRoot,stateRoot,stateDir,layoutDirectory,env,argv,stdin,operation,stateFile,now}=m.start;
    let time=now,stdout='',stderr='';const epoch=performance.now();
    Date.now=()=>time+Math.floor(performance.now()-epoch);
    globalThis.fetch=async(url,opts={})=>{
      const payload=opts.body?{request:await opts.body.get('request').text(),tar:Buffer.from(await opts.body.get('source').arrayBuffer())}:null;
      const r=await rpc('fetch',String(url),{method:opts.method,payload});return new Response(r.body,{status:r.status,headers:r.headers});
    };
    const out={write:s=>{stdout+=s;return true;}},err={write:s=>{stderr+=s;return true;}};
    const ports={...healthyMachine,...isolatedCheckCapacity(base,{taskset:null}),queueRoot:env.PDD_SUITE_QUEUE,env,stateRoot,autopilotStateRoot:stateRoot,stateDir,layoutDirectory,now:()=>time,
      sleep:async ms=>{time+=ms;await rpc('sleep',ms);},
      execFile:(...a)=>rpc('exec',...a),run:(...a)=>rpc('exec',...a),
      herdr:(...a)=>rpc('herdr',...a),workflowHerdr:(...a)=>rpc('herdr',...a),
      findNativeSessions:(...a)=>rpc('sessions',...a),
      checkCapacityPorts:{...isolatedCheckCapacity(base,{taskset:null}),queueRoot:env.PDD_SUITE_QUEUE,now:()=>time},
      codexLimits:async()=>({state:'healthy'}),agentDefinitions:()=>[{kind:'codex',name:'codex',command:'codex',env:{}}],
      selectAgent:async()=>({id:'codex',kind:'codex',command:'codex',env:{}}),pathDiagnostic:()=>[],timer:async()=>true,
      allocationCheck:async()=>({state:'ready'}),isTTY:false,skipMetricsDelivery:true,stdin:(async function*(){if(stdin!==undefined)yield stdin;})(),
      armCoordinatorIdle:()=>{},wait:async()=>{},
      warn:s=>rpc('warning',s),sendAlert:input=>rpc('alert',input),sendDigest:async()=>({exitCode:0}),
      runtimeHealth:()=>rpc('runtimeHealth'),
      doctorPorts:{files:doctorFiles,run:(...a)=>rpc('doctorExec',...a),
        codexLimits:async()=>({state:'healthy'}),runtimeHealth:()=>rpc('runtimeHealth')},
    };
    const workflowRunner=Object.fromEntries(Object.entries(runner).map(([k,v])=>[k,typeof v==='function'?(input,p)=>v(input,{...ports,...p,env:p?.env??env}):v]));
    let code;
    if(operation==='hold-interpreter'||operation==='hold-interpreter-dispatched') {
      const {acquireInterpreterSlot,markInterpreterDispatch}=await import('../../../src/interpreter-queue.mjs');
      const slot=await acquireInterpreterSlot({cwd,origin:'https://factory.invalid',requestId:'dead-holder',kind:'check',env});
      if(operation==='hold-interpreter-dispatched')await markInterpreterDispatch(slot);code=0;
    } else if(operation==='tick') {const result=await tickAutopilot(stateFile,ports);code=result.exitCode;stdout=result.message;}
    else code=await runPdd(argv,{cwd,packageRoot,env,stdout:out,stderr:err,
      stdin:(async function*(){if(stdin!==undefined)yield stdin;})(),workflowRunner,
      workflowAgentPorts:{run:async()=>({code:0,stdout:'Logged in using ChatGPT',stderr:''})},
      autopilotLauncherPorts:ports,dependencyIntakePorts:ports,provePorts:ports,autopilotGithubPorts:ports,autopilotPorts:{...ports,cwd},pathDiagnostic:()=>[]});
    process.send({done:{code,stdout,stderr,time}});
  } catch(error) {process.send({failed:{message:error.message,stack:error.stack}});}
});
