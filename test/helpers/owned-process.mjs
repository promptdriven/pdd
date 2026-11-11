import {spawn} from 'node:child_process';
import {randomBytes} from 'node:crypto';
import {readFileSync,readdirSync,statSync} from 'node:fs';

const pause=ms=>new Promise(resolve=>setTimeout(resolve,ms));
function stat(pid){try{const f=readFileSync(`/proc/${pid}/stat`,'utf8').split(') ').at(-1).split(' ');return {state:f[0],start:f[19]};}catch(error){if(error.code==='ENOENT'||error.code==='ESRCH')return null;throw error;}}
function signal(pid,start,sig){const current=stat(pid);if(!current||current.start!==start||current.state==='Z')return;try{process.kill(pid,sig)}catch(error){if(error.code!=='ESRCH')throw error;}}

export function spawnOwned(script,options={}) {
 const key='PDD_PROOF_FIXTURE_OWNER',token=randomBytes(32).toString('hex'),entry=Buffer.from(`${key}=${token}`);
 const child=spawn(process.execPath,['--input-type=module','-e',script],{...options,env:{...(options.env??process.env),[key]:token},stdio:['ignore','pipe','pipe']});
 let spawnError;child.once('error',error=>{spawnError=error;});
 const ended=new Promise(resolve=>child.once('close',(code,signal)=>resolve({code,signal})));
 const runner=child.pid&&stat(child.pid);
 const known=new Map(runner?[[child.pid,runner.start]]:[]);
 function matches(){
  const found=new Map();
  for(const name of readdirSync('/proc'))if(/^\d+$/.test(name)){
   const pid=Number(name);if(pid===process.pid)continue;
   try{
    if(statSync(`/proc/${pid}`).uid!==process.getuid())continue;
    const before=stat(pid);if(!before||before.state==='Z')continue;
    const env=readFileSync(`/proc/${pid}/environ`);
    if(env.indexOf(entry)!==-1&&env.toString('utf8').split('\0').some(part=>part===entry.toString())){
     const after=stat(pid);if(after&&after.start===before.start&&after.state!=='Z'){found.set(pid,after);known.set(pid,after.start);}
    }
   }catch(error){if((error.code==='EACCES'||error.code==='EPERM')&&!known.has(pid))continue;if(error.code!=='ENOENT'&&error.code!=='ESRCH')throw error;}
  }
  return found;
 }
 let cleanupPromise;
 return {child,ended,cleanup(){return cleanupPromise??=(async()=>{
  if(runner)signal(child.pid,runner.start,'SIGSTOP');
  // Wait for a concurrently spawned process to finish exec, then freeze every
  // token-bearing process. Repeat after all are stopped to close fork races.
  let stable=0;
  for(let n=0;n<500&&stable<5;n++){
   const found=matches();let active=false;
   for(const [pid,info] of found)if(!'Tt'.includes(info.state)){active=true;signal(pid,info.start,'SIGSTOP');}
   stable=active?0:stable+1;await pause(10);
  }
  const frozen=matches();
  if([...frozen.values()].some(info=>!'Tt'.includes(info.state)))throw Error('owned proof processes could not be stopped');
  for(const [pid,info] of frozen)signal(pid,info.start,'SIGKILL');
  if(runner)signal(child.pid,runner.start,'SIGKILL');
  await ended;if(spawnError)throw spawnError;
  for(let n=0;n<500;n++){if(matches().size===0)return;await pause(10);}
  throw Error('owned proof processes did not stop');
 })();}};
}
