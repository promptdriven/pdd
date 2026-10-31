import {parentPort,workerData} from 'node:worker_threads';
import * as storage from '../../src/workflow-runs.mjs';
const {runDir,mode,barrier,record,stateDir}=workerData;
try{
 if(mode==='update'){
  const result=storage.updateRun(runDir,latest=>{latest.message='Callback committed first';parentPort.postMessage({held:true});Atomics.wait(new Int32Array(barrier),0,0,15000);return latest;},{stateDir,now:()=>4000});parentPort.postMessage({result});
 }else{parentPort.postMessage({attempting:true});const result=storage.writeRun(record,{stateDir,now:()=>5000});parentPort.postMessage({result});}
}catch(error){parentPort.postMessage({error:{code:error.code,message:error.message}});}
