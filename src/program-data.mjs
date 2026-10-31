// Generated from prompts/cli/program-data.prompt.md (sha256: a3e4451280ffe7e3da285dc2cf9c3c8855fffebe6f5eabcd0bc4444639a6a582).
import { constants, lstatSync, mkdirSync, readFileSync, openSync, closeSync, writeFileSync, renameSync, unlinkSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { hostname } from 'node:os';
import { randomUUID } from 'node:crypto';
export const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
export function localError(message) { return Object.assign(new Error(message), {exitCode:2}); }
export function safeDirectory(root, parts) {
  let path=root;
  for(const part of parts) {
    path=join(path,part);
    try { mkdirSync(path,{mode:0o700}); } catch(e) { if(e.code!=='EEXIST') throw e; }
    const st=lstatSync(path);if(!st.isDirectory()||st.isSymbolicLink()) throw localError('Refusing an unsafe program data directory.');
  }
  return path;
}
export function readPrivate(path, fallback) {
  let st;try {st=lstatSync(path);}catch(e){if(e.code==='ENOENT')return fallback;throw e;}
  if(!st.isFile()||st.isSymbolicLink()||st.nlink!==1)throw localError('Program data must be a regular file with one link.');
  return JSON.parse(readFileSync(path,'utf8'));
}
export function writePrivate(path,value) {
  readPrivate(path,undefined);
  const temp=path+'.'+randomUUID()+'.tmp';
  const fd=openSync(temp,constants.O_WRONLY|constants.O_CREAT|constants.O_EXCL|constants.O_NOFOLLOW,0o600);
  try {writeFileSync(fd,JSON.stringify(value,null,2)+'\n');}finally{closeSync(fd);}
  try {renameSync(temp,path);}finally{try{unlinkSync(temp);}catch{}}
}
export function programData({root,program,flags={}},ports={}) {
  if(!/^[A-Za-z0-9._-]+$/.test(program)||program==='.'||program==='..')throw localError('Invalid program identity.');
  const dir=safeDirectory(root,['.pdd','run',program]);
  const ignore=join(root,'.gitignore');let previous='';
  try {const st=lstatSync(ignore);if(!st.isFile()||st.nlink!==1)throw localError('Refusing unsafe .gitignore.');previous=readFileSync(ignore,'utf8');}catch(e){if(e.code!=='ENOENT')throw e;}
  if(!previous.split('\n').some(v=>['.pdd/','/.pdd/'].includes(v))) {
    const fd=openSync(ignore,constants.O_WRONLY|constants.O_APPEND|constants.O_CREAT|constants.O_NOFOLLOW,0o644);
    try{writeFileSync(fd,(previous&&!previous.endsWith('\n')?'\n':'')+'.pdd/\n');}finally{closeSync(fd);}
  }
  let world={},simulation;
  if(flags.data) {
    const doc=readPrivate(resolve(root,flags.data));
    if(object(doc)&&Object.hasOwn(doc,'initial_world')) {world=doc.initial_world;simulation=doc.simulation;}
    else world=doc;
  } else if(!flags.fresh)world=readPrivate(join(dir,'data.json'),{});
  if(!object(world))throw localError('Starting data must be a JSON world object.');
  if(simulation!==undefined&&!object(simulation))throw localError('Simulation must be a JSON object.');
  return {dir,fresh:!!flags.fresh,startingData:{initial_world:world,...(simulation===undefined?{}:{simulation})},explicit:!!flags.data};
}

// A dead native owner cannot prevent the saved request from being read after a crash.
export function acquireProgramLock(dir) {
  const path=join(dir,'active.lock'),owner={pid:process.pid,host:hostname(),token:randomUUID()};
  for(let attempt=0;attempt<2;attempt++) {
    try {const fd=openSync(path,constants.O_WRONLY|constants.O_CREAT|constants.O_EXCL|constants.O_NOFOLLOW,0o600);try{writeFileSync(fd,JSON.stringify(owner));}finally{closeSync(fd);}
      return ()=>{if(readPrivate(path,null)?.token===owner.token)unlinkSync(path);};
    }catch(error){
      if(error.code!=='EEXIST')throw error;
      const previous=readPrivate(path,null);let alive=true;
      if(previous?.host===owner.host&&Number.isInteger(previous.pid)&&previous.pid>0){try{process.kill(previous.pid,0);}catch(e){if(e.code==='ESRCH')alive=false;}}
      if(alive)throw Object.assign(new Error('Another program command is active. Wait for it to finish before running again.'),{exitCode:125});
      if(readPrivate(path,null)?.token===previous.token)unlinkSync(path);
    }
  }
  throw Object.assign(new Error('Could not acquire program data ownership. Try again after the other command finishes.'),{exitCode:125});
}
