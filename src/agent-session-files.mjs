// Generated from prompts/cli/agent-session-files.prompt.md (sha256: e6ae05b67c9f058ab067d74f79e044f4338b84330044aa121bd45e7a1d534bc1).
import {lstat,opendir,open,unlink} from 'node:fs/promises';
import {constants} from 'node:fs';
import {dirname,isAbsolute,join,parse,sep} from 'node:path';
import {homedir} from 'node:os';
import {validSessionId} from './workflow-chat.mjs';

const WARNING='Agent session files could not be safely removed; they were retained.';
const problem=()=>new Error(WARNING);
const same=(a,b)=>a.dev===b.dev&&a.ino===b.ino;
const epoch=value=>typeof value==='number'?value:typeof value==='string'?Date.parse(value):NaN;
const archive=name=>['archive','archives','archived_sessions'].includes(name);
function fileId(agent,name){
 const match=agent==='claude'?/^([0-9a-f-]+)\.jsonl$/i.exec(name):/^rollout-.+-([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})\.jsonl$/i.exec(name);
 // Native UUIDs are case-insensitive, extensions and the rollout prefix are not.
 if((agent==='codex'&&!name.startsWith('rollout-'))||!name.endsWith('.jsonl')||!match||!validSessionId(match[1]))return null;
 return match[1].toLowerCase();
}
async function ancestors(path,identities){
 const root=parse(path).root,parts=path.slice(root.length).split(sep).filter(Boolean);let current=root;
 for(const part of ['',...parts]){
  if(part)current=join(current,part);
  let stat;try{stat=await lstat(current);}catch(error){if(error.code==='ENOENT')return;throw problem();}
  if(!stat.isDirectory()||stat.isSymbolicLink())throw problem();
  const previous=identities.get(current);if(previous&&!same(previous,stat))throw problem();
  if(!previous)identities.set(current,{dev:stat.dev,ino:stat.ino});
 }
}
async function scan(root,agent,identities){
 const files=[],paths=new Set();let total=0;
 async function walk(path,depth){
  if(depth>8)throw problem();await ancestors(path,identities);
  let directory;try{directory=await opendir(path);}catch(error){if(error.code==='ENOENT'&&depth===0)return;throw problem();}
  for await(const entry of directory){
   if(++total>8192)throw problem();const child=join(path,entry.name);paths.add(child);
   if(entry.isSymbolicLink())throw problem();
   if(entry.isDirectory()){if(agent==='codex'&&!archive(entry.name))await walk(child,depth+1);}
   else if(entry.isFile())files.push({path:child,name:entry.name});
   else throw problem();
  }
 }
 await walk(root,0);return {files,paths};
}
function evidence(buffer,agent,id,cwd,start,end){
 const newline=buffer.lastIndexOf(10);if(newline<0)return false;
 let text;try{text=new TextDecoder('utf-8',{fatal:true}).decode(buffer.subarray(0,newline+1));}catch{return false;}
 let first=null;
 for(const line of text.split('\n')){
  if(!line.trim())continue;let row;try{row=JSON.parse(line);}catch{return false;}
  if(!row||typeof row!=='object'||Array.isArray(row))return false;
  let identity;
  if(agent==='codex'){if(row.type==='session_meta'){identity=row.payload;if(identity?.thread_source==='subagent'||identity?.parent_thread_id||identity?.source?.subagent)return false;}}
  else if(['user','assistant'].includes(row.type)&&row.isMeta!==true&&row.isSidechain!==true)identity={id:row.sessionId,cwd:row.cwd,timestamp:row.timestamp};
  if(identity===undefined)continue;
  if(!identity||!validSessionId(identity.id)||identity.id.toLowerCase()!==id||identity.cwd!==cwd)return false;
  const timestamp=epoch(identity.timestamp);
  if(!first){if(!Number.isFinite(timestamp)||timestamp<start||timestamp>end)return false;first={timestamp};}
  else if(agent==='codex'&&timestamp!==first.timestamp)return false;
 }
 return first!==null;
}
export function createSessionFiles({agent,cwd,env=process.env,now=Date.now}={}){
 const home=env.HOME??homedir(),nativeHome=agent==='codex'?(env.CODEX_HOME??join(home,'.codex')):(env.CLAUDE_CONFIG_DIR??join(home,'.claude'));
 if(!['codex','claude'].includes(agent)||typeof cwd!=='string'||!isAbsolute(cwd)||typeof nativeHome!=='string'||!isAbsolute(nativeHome)||typeof now!=='function')throw problem();
 const root=agent==='codex'?join(nativeHome,'sessions'):join(nativeHome,'projects',cwd.replace(/[^a-zA-Z0-9]/g,'-'));
 const identities=new Map(),owned=new Map();let prepared=null,snapshot=null,preparedAt=null,failed=false,closing=false,working=null;
 function prepare(){
  if(prepared)return prepared;
  prepared=(async()=>{preparedAt=now();if(!Number.isFinite(preparedAt))throw problem();snapshot=await scan(root,agent,identities);})().catch(()=>{failed=true;throw problem();});
  return prepared;
 }
 function own(id,startedAt){
  const current=now();
  if(closing||failed||!snapshot||!validSessionId(id)||!Number.isFinite(startedAt)||!Number.isFinite(current)||startedAt<preparedAt||startedAt>current)return false;
  id=id.toLowerCase();if(owned.has(id))return owned.get(id)===startedAt;if(owned.size>=64)return false;
  if(snapshot.files.some(file=>fileId(agent,file.name)===id))return false;
  owned.set(id,startedAt);return true;
 }
 async function remove(){
  const result={deleted:0,retained:0,errors:[]},warn=()=>{if(!result.errors.length)result.errors.push(WARNING);};
  if(!snapshot||failed){warn();return result;}
  const end=now();if(!Number.isFinite(end)){warn();return result;}
  let scanned;try{scanned=await scan(root,agent,identities);}catch{warn();return result;}
  for(const file of scanned.files){
   const id=fileId(agent,file.name);if(!id||!owned.has(id)||snapshot.paths.has(file.path))continue;
   let descriptor;
   try{
    await ancestors(dirname(file.path),identities);
    descriptor=await open(file.path,constants.O_RDONLY|constants.O_NOFOLLOW|constants.O_NONBLOCK);
    const stat=await descriptor.stat();
    if(!stat.isFile()||stat.nlink!==1||(typeof process.getuid==='function'&&stat.uid!==process.getuid()))throw problem();
    const buffer=Buffer.alloc(65536),read=await descriptor.read(buffer,0,buffer.length,0);
    if(!evidence(buffer.subarray(0,read.bytesRead),agent,id,cwd,owned.get(id),end))throw problem();
    await ancestors(dirname(file.path),identities);const current=await lstat(file.path);
    if(!current.isFile()||current.isSymbolicLink()||current.nlink!==1||!same(current,stat)||current.size!==stat.size||current.mtimeMs!==stat.mtimeMs||current.ctimeMs!==stat.ctimeMs)throw problem();
    await unlink(file.path);result.deleted++;
   }catch(error){if(error.code!=='ENOENT'){result.retained++;warn();}}
   finally{await descriptor?.close().catch(()=>{});}
  }
  return result;
 }
 async function cleanup(){closing=true;if(working)return working;working=remove();try{return await working;}finally{working=null;}}
 return {prepare,own,cleanup};
}
