// Generated from prompts/cli/program-data.prompt.md (sha256: 2ddc32f2137a6ffbe33adbfe1faadbbebbd5c22f5810c4708e89bfcd141e96fb).
import { constants, realpathSync, lstatSync, mkdirSync, readFileSync, openSync, closeSync, writeFileSync, renameSync, unlinkSync, readdirSync } from 'node:fs';
import { basename, dirname, join, resolve, isAbsolute } from 'node:path';
import { spawnSync } from 'node:child_process';
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
  const parts=typeof program==='string'?program.split('/'):[];
  if(!parts.length||isAbsolute(program)||parts.some(part=>!part||part==='.'||part==='..'||part.includes('\\')||part.includes('\0')))throw localError('Invalid program identity.');
  const files=spawnSync('git',['ls-files','-z','--cached','--others','--exclude-standard'],{cwd:root,encoding:'utf8'}).stdout.split('\0');
  const leaf=basename(program),duplicates=files.filter(f=>f.endsWith('.prompt.md')&&basename(f,'.prompt.md')===leaf).length>1;
  const encode=(part,flat=false)=>part==='active.lock'?'%61ctive.lock':part.replaceAll('%','%25').replace(flat?/__|^_|_$/g:/__/g,match=>'%5F'.repeat(match.length));
  const run=safeDirectory(root,['.pdd','run']);
  let dir;
  {
    const ownership=path=>{
      try {
        const recorded=readPrivate(join(path,'program.json'),undefined);
        const session=readPrivate(join(path,'session.json'),undefined);
        const validIdentity=value=>typeof value==='string'&&value.length>0&&!isAbsolute(value)&&!value.split('/').some(part=>!part||part==='.'||part==='..'||part.includes('\\')||part.includes('\0'));
        if(recorded!==undefined&&(!object(recorded)||!validIdentity(recorded.program)))throw localError('Invalid program ownership metadata.');
        if(session!==undefined&&(!object(session)||!validIdentity(session.file??session.program)))throw localError('Invalid program session metadata.');
        return recorded?.program??(session?.file??session?.program)?.replace(/\.prompt\.md$/,'');
      }catch(error){if(error.exitCode)throw error;throw localError(`Invalid program ownership/session metadata: ${error.message}`);}
    };
    for(const name of readdirSync(run)){
      const path=join(run,name),stat=lstatSync(path);
      if(!stat.isDirectory()||stat.isSymbolicLink())continue;
      try{if(ownership(path)===program){dir=safeDirectory(root,['.pdd','run',name]);break;}}catch{ /* An unrelated unusable record cannot identify this entry. Selected paths are checked below. */ }
    }
    if(!dir){
      const base=encode(leaf),flat=parts.map(part=>encode(part,true)).join('__');
      let selected=duplicates?flat:base;
      const basePath=join(run,base);
      if(selected===base)try{const st=lstatSync(basePath);if(!st.isDirectory()||st.isSymbolicLink())throw localError('Refusing an unsafe program data directory.');if(ownership(basePath)&&ownership(basePath)!==program)selected=flat;}catch(e){if(e.code!=='ENOENT')throw e;}
      dir=safeDirectory(root,['.pdd','run',selected]);
      const owner=ownership(dir);if(owner&&owner!==program)throw localError('Program data directory belongs to another entry.');
    }
    const releaseMapping=acquireProgramLock(dir);
    try{const owner=ownership(dir);if(owner&&owner!==program)throw localError('Program data directory belongs to another entry.');writePrivate(join(dir,'program.json'),{program});}finally{releaseMapping();}
  }
  if(flags.fresh){const release=acquireProgramLock(dir);try{const prior=readPrivate(join(dir,'world.json'),undefined);if(prior!==undefined)writePrivate(join(dir,'world.prev.json'),prior);}finally{release();}}
  const git=spawnSync('git',['rev-parse','--git-path','info/exclude'],{cwd:root,encoding:'utf8',stdio:['ignore','pipe','pipe']});
  if(git.status!==0)throw localError('Cannot locate local Git excludes.');
  const ignore=resolve(root,git.stdout.trim());let previous='';
  // Git may not have created info yet, particularly in linked worktrees.
  mkdirSync(dirname(ignore),{recursive:true});
  if(realpathSync(dirname(ignore))!==dirname(ignore))throw localError('Refusing a symbolic link in the Git exclude path.');
  try {const st=lstatSync(ignore);if(!st.isFile()||st.nlink!==1)throw localError('Refusing unsafe Git exclude file.');previous=readFileSync(ignore,'utf8');}catch(e){if(e.code!=='ENOENT')throw e;}
  if(!previous.split('\n').some(v=>['.pdd/','/.pdd/'].includes(v))) {
    const fd=openSync(ignore,constants.O_WRONLY|constants.O_APPEND|constants.O_CREAT|constants.O_NOFOLLOW,0o644);
    try{writeFileSync(fd,(previous&&!previous.endsWith('\n')?'\n':'')+'.pdd/\n');}finally{closeSync(fd);}
  }
  let world={},simulation;
  if(flags.data) {
    let doc;
    try {doc=readPrivate(resolve(root,flags.data));if(doc===undefined)throw new Error('file does not exist');}
    catch(e){throw localError(`Cannot read starting data ${flags.data}: ${e.message}.`);}
    if(object(doc)&&Object.hasOwn(doc,'initial_world')) {world=doc.initial_world;simulation=doc.simulation;}
    else world=doc;
  } else if(!flags.fresh)world=readPrivate(join(dir,'world.json'),{});
  if(!object(world))throw localError(`${flags.data??'Starting data'} must be a JSON world object.`);
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
