import {parentPort,workerData} from 'node:worker_threads';
import {stepDone} from '../../src/workflow-runner.mjs';
const {root,commonDir,stateDir,env,barrier,step}=workerData;
let first=true;
try {
 const result=await stepDone({step,summary:`Completed ${step}`,cwd:root},{stateDir,env,
 execFile:async(file,args)=>{
  if(file!=='git')throw Error(`unexpected program ${file}`);
  if(args.join(' ')==='rev-parse --show-toplevel')return {stdout:root};
  if(args.join(' ')==='rev-parse --path-format=absolute --git-common-dir')return {stdout:commonDir};
  throw Error(`unexpected git ${args.join(' ')}`);
 },now:()=>{if(first){first=false;parentPort.postMessage({held:true});if(Atomics.wait(new Int32Array(barrier),0,0,10000)==='timed-out')throw Error('barrier timeout');}return 5000;}});
 parentPort.postMessage({result});
}catch(error){parentPort.postMessage({error:error.stack});}
