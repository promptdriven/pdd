// Generated from prompts/cli/runtime-workspace.prompt.md (sha256: 433a0b67c78602fbc28d766f441a5572b0f9e979312607465c49a7f44429ca10).
// Implements prompts/cli/runtime-workspace.prompt.md.
import {constants,lstatSync,openSync,fstatSync,readFileSync,closeSync,realpathSync} from 'node:fs';
import {join,resolve,parse,sep} from 'node:path';
import {spawnSync} from 'node:child_process';
const CONTROL='pdd-workspace.json', MAX=10_485_760;
export class RuntimeWorkspaceError extends Error {
  constructor(code,message){super(`${code}: ${message}`);this.code=code;this.exitCode=4;}
}
const fail=(code,reason)=>{throw new RuntimeWorkspaceError(code,`${CONTROL}: ${reason}. Correct this regular local policy file and retry.`);};
export function nativeWorkspaceFiles(root){
  let observed,canonicalRoot;
  return {
    stat({path}){
      try{
        canonicalRoot=realpathSync(root);
        const full=resolve(canonicalRoot,path);let at=parse(full).root;
        for(const part of full.slice(at.length).split(sep).filter(Boolean)){
          at=join(at,part);const st=lstatSync(at);
          if(st.isSymbolicLink())throw Error('symbolic link');
          if(at!==full&&!st.isDirectory())throw Error('non-directory ancestor');
          if(at===full){if(!st.isFile())throw Error('not regular');observed=st;}
        }
      }catch(error){if(error.code==='ENOENT')return{exists:false,is_symlink:false,size:0};throw error;}
      const git=spawnSync('git',['ls-files','-z','-co','--exclude-standard','--',path],{cwd:canonicalRoot});
      if(git.status!==0||!git.stdout.toString().split('\0').includes(path))throw Error('not Git-visible');
      return{exists:true,is_symlink:false,size:observed.size};
    },
    read({path}){
      const fd=openSync(join(canonicalRoot,path),constants.O_RDONLY|constants.O_NOFOLLOW|constants.O_NONBLOCK);
      try{const st=fstatSync(fd);if(!observed||!st.isFile()||st.size>MAX||st.ino!==observed.ino||st.dev!==observed.dev||st.mtimeMs!==observed.mtimeMs||st.ctimeMs!==observed.ctimeMs)throw Error('changed');
        const content=new TextDecoder('utf-8',{fatal:true}).decode(readFileSync(fd));
        const after=fstatSync(fd);if(after.size!==st.size||after.mtimeMs!==st.mtimeMs||after.ctimeMs!==st.ctimeMs)throw Error('changed');
        return{content};
      }finally{closeSync(fd);}
    }
  };
}
const valid=path=>typeof path==='string'&&!!path&&!/[\\\x00-\x1f\x7f*?\[\]{}:$%]/.test(path)&&!path.startsWith('~')&&!path.startsWith('/')&&!path.replace(/\/$/,'').split('/').some(p=>!p||p==='.'||p==='..'||p==='.git');
export function loadRuntimeWorkspace({root},files=nativeWorkspaceFiles(root)){
  let stat,text;
  try{stat=files.stat({path:CONTROL});if(!stat.exists)return Object.freeze({configured:false,allowed_paths:Object.freeze([])});if(stat.is_symlink||!Number.isInteger(stat.size)||stat.size<0||stat.size>MAX)fail('workspace-config-unsafe','unsafe or oversized policy');text=files.read({path:CONTROL}).content;}
  catch(error){if(error instanceof RuntimeWorkspaceError)throw error;fail('workspace-config-unsafe','cannot safely read policy');}
  let doc;try{doc=JSON.parse(text);}catch{fail('workspace-config-invalid','expected valid JSON');}
  if(!doc||Array.isArray(doc)||typeof doc!=='object'||Object.keys(doc).length!==1||!Array.isArray(doc.allowed_paths)||!doc.allowed_paths.every(valid))fail('workspace-config-invalid','expected only allowed_paths with safe repository-relative files or directory/ entries');
  return Object.freeze({configured:true,allowed_paths:Object.freeze([...new Set(doc.allowed_paths)])});
}
export function allowsRuntimePath(policy,path){return !policy.configured||typeof path==='string'&&policy.allowed_paths.some(p=>p.endsWith('/')?path.startsWith(p)&&path.length>p.length:path===p);}
export function requireRuntimePath(policy,{path,from='Source',chain=[],role='source'}){
  if(!allowsRuntimePath(policy,path))throw new RuntimeWorkspaceError('workspace-path-outside',`${[...chain,from,path].filter(Boolean).join(' -> ')}: required ${role} is outside ${CONTROL}. Correct or move the reference, or deliberately change allowed_paths.`);
  return path;
}
