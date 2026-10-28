// Generated from prompts/cli/agent-config.prompt.md (sha256: 156379ac070aad794ec2ce7c6bc67621f1ead349ec2a72440da6c660d574c1b7).
import {constants,lstatSync,openSync,fstatSync,readSync,closeSync} from 'node:fs';
import {resolve,join,dirname,isAbsolute} from 'node:path';
import {createHash} from 'node:crypto';
const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const controls = /[\u0000-\u001f\u007f-\u009f]/;
const bad = message => {throw new Error(`Invalid agents configuration: ${message}.`);};
function stat(path){try{return lstatSync(path);}catch(e){if(e.code==='ENOENT')return null;bad('cannot inspect configuration file');}}
function defaults(){return ['codex','claude','gemini'].map(kind=>({id:kind,name:kind[0].toUpperCase()+kind.slice(1),kind,command:kind,env:{}}));}
function expand(value,home){if(value==='~'||value.startsWith('~/')){if(typeof home!=='string'||!home)bad('HOME is required for tilde paths');return value==='~'?home:join(home,value.slice(2));}return value;}
function read(path){const info=stat(path);if(!info)return undefined;if(!info.isFile()||info.isSymbolicLink())bad('file must be regular and not a symlink');if(info.size>65536)bad('file exceeds 65536 bytes');let fd;try{fd=openSync(path,constants.O_RDONLY|constants.O_NOFOLLOW|constants.O_NONBLOCK);const actual=fstatSync(fd);if(!actual.isFile()||actual.size>65536)bad('file must be regular and at most 65536 bytes');const buffer=Buffer.alloc(65537);let length=0;while(length<buffer.length){const count=readSync(fd,buffer,length,buffer.length-length,null);if(!count)break;length+=count;}if(length>65536)bad('file exceeds 65536 bytes');try{return JSON.parse(buffer.subarray(0,length).toString('utf8'));}catch{bad('file must contain valid JSON');}}catch(e){if(e.message.startsWith('Invalid agents configuration:'))throw e;bad('cannot read configuration file');}finally{if(fd!==undefined)closeSync(fd);}}
export function loadAgentDefinitions({cwd,env=process.env}){
 const home=env.HOME;if(typeof home!=='string'||!home)return defaults();
 const path=join(home,'.config','pdd','agents.json');
 const selected=stat(path);if(!selected)return defaults();const config=read(path);if(config===undefined)bad('selected configuration file disappeared');
 if(!object(config)||Object.keys(config).some(k=>!['agents','include_defaults'].includes(k))||!Array.isArray(config.agents)||config.agents.length>24)bad('expected agents array with at most 24 entries');
 if('include_defaults' in config&&typeof config.include_defaults!=='boolean')bad('include_defaults must be boolean');
 const enabled=config.include_defaults!==false;const names=new Set(enabled?defaults().flatMap(x=>[x.name,x.id]):[]);
 const definitions=config.agents.map(item=>{
  if(!object(item)||Object.keys(item).some(k=>!['name','kind','command','env'].includes(k)))bad('invalid agent entry');
  if(typeof item.name!=='string'||!item.name.length||item.name.length>100||item.name!==item.name.trim()||controls.test(item.name))bad('invalid agent name');
  if(names.has(item.name))bad('duplicate agent name');names.add(item.name);
  if(!['codex','claude','gemini'].includes(item.kind))bad('unknown agent kind');
  if(typeof item.command!=='string'||!item.command.trim()||item.command.length>4096||controls.test(item.command))bad('missing or invalid agent command');
  const overrides=item.env===undefined?{}:item.env;
  if(!object(overrides)||Object.keys(overrides).length>64)bad('invalid agent env');
  const childEnv={};for(const [key,value] of Object.entries(overrides)){if(!/^[A-Za-z_][A-Za-z0-9_]*$/.test(key)||typeof value!=='string'||value.length>8192||value.includes('\0'))bad('invalid agent env value or key');Object.defineProperty(childEnv,key,{value:expand(value,home),enumerable:true,writable:true,configurable:true});}
  let command=expand(item.command,home);if(!isAbsolute(command)&&command.includes('/'))command=resolve(dirname(path),command);
  return {id:`custom-${createHash('sha256').update(item.name).digest('hex').slice(0,24)}`,name:item.name,kind:item.kind,command,env:childEnv};
 });
 return [...definitions,...(enabled?defaults():[])];
}
