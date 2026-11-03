import {parentPort,workerData} from 'node:worker_threads';
import {execFile as callbackExec} from 'node:child_process';
import {promisify} from 'node:util';
import * as runner from '../../src/workflow-runner.mjs';
const exec=promisify(callbackExec),{command,root,source,stateDir,env}=workerData;
const ports={stateDir,env,isTTY:true,confirm:async()=>true,now:()=>3000,
 execFile:async(file,args,options)=>{if(file!=='git')throw Error(`Unexpected outside program ${file}`);return exec('/usr/bin/git',args,{...options,encoding:'utf8'});},
 herdr:async()=>{throw Error('No Herdr before invalid corpus refusal');}};
try{const result=command.startsWith('stepDone')?await runner.stepDone({step:'verify',summary:'Own verify',cwd:root},ports):await runner.approveRun({ref:'17',cwd:source},ports);parentPort.postMessage({result});}
catch(error){parentPort.postMessage({error:{code:error.code,message:error.message}});}
