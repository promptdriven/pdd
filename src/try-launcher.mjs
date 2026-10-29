// Generated from prompts/cli/try-launcher.prompt.md (sha256: e29addfeed0231925312f73fa2d90b25c8a9af2918d828a934987ab10b786da3).
import {accessSync,chmodSync,closeSync,constants,existsSync,lstatSync,mkdirSync,openSync,readFileSync,readlinkSync,realpathSync,renameSync,symlinkSync,unlinkSync,writeFileSync} from 'node:fs';
import {basename,dirname,join,relative,resolve,sep} from 'node:path';
import {cleanText} from './runtime-output.mjs';
const marker = '#!/bin/sh\n# PDD shared Try launcher v1\n';
const quote = word => `'${word.replaceAll("'", "'\\''")}'`;
const safeName = name => /^[A-Za-z][A-Za-z0-9._-]{0,63}$/.test(name) && !['pdd','node','gh','git','pdd-virtual'].includes(name.toLowerCase());
const fail = (text,localPath) => { throw Object.assign(new Error(text),{localPath}); };
function privatePath(root,path,create=false) {
  const rel=relative(root,path);
  if(!rel || rel.startsWith('..') || rel.startsWith(sep))fail('The Try pointer must stay in this workspace.');
  let current=root;
  for(const part of rel.split(sep)) {
    current=join(current,part);
    if(create)try{mkdirSync(current,{mode:0o700});}catch(e){if(e.code!=='EEXIST')throw e;}
    const st=lstatSync(current);
    if(st.isSymbolicLink())fail('Refusing a symbolic link in Try pointer files.');
    if(!st.isDirectory() && (!st.isFile() || st.nlink!==1))fail('Unsafe Try pointer file.');
  }
}
export function installNamedLauncher({root,name,descriptorPath,binDir,path='',cwd=process.cwd()}) {
  if(!safeName(name))fail('The virtual program name is reserved or invalid.');
  const launcher=join(binDir,'pdd-virtual'),alias=join(binDir,name);
  const ours = file => {try{return lstatSync(file).isSymbolicLink() && resolve(dirname(file),readlinkSync(file))===launcher;}catch{return false;}};
  for(const part of path.split(sep==='\\' ? ';' : ':')) {
    const candidate=resolve(cwd,part||'.',name);
    try{accessSync(candidate,constants.X_OK);}catch{continue;}
    if(!ours(candidate))fail(`The command ${name} already exists on PATH. Choose another program name; pdd will not overwrite it.`,candidate);
  }
  try { const st=lstatSync(alias);if(!ours(alias))fail(`A command already exists at ${alias}; pdd will not overwrite it.`); } catch(e){if(e.code!=='ENOENT')throw e;}
  try{const st=lstatSync(launcher);if(!st.isFile()||st.nlink!==1||!readFileSync(launcher,'utf8').startsWith(marker))fail(`Refusing to overwrite ${launcher}; it is not the shared PDD launcher.`);}catch(e){if(e.code!=='ENOENT')throw e;}
  const moduleUrl=new URL('try-launcher.mjs',import.meta.url).href;
  const js=`import(process.argv[1]).then(async({runNamedShim})=>{process.exitCode=await runNamedShim(process.argv[2],process.argv.slice(3));}).catch(()=>{process.stderr.write('pdd try: the installed launcher could not load. Run pdd try STORY --cli again.\\n');process.exitCode=125;});`;
  const text=`${marker}exec ${quote(process.execPath)} --input-type=commonjs -e ${quote(js)} -- ${quote(moduleUrl)} "$0" "$@"\n`;
  const temporary=`${launcher}.${process.pid}.tmp`,fd=openSync(temporary,constants.O_WRONLY|constants.O_CREAT|constants.O_EXCL|constants.O_NOFOLLOW,0o700);
  try{writeFileSync(fd,text);}finally{closeSync(fd);}
  renameSync(temporary,launcher);chmodSync(launcher,0o700);
  if(!ours(alias))symlinkSync(launcher,alias);
  const pointerFolder=join(root,'.pdd/try/programs');privatePath(root,pointerFolder,true);
  const pointer=join(pointerFolder,`${name}.json`);
  try{privatePath(root,pointer);}catch(e){if(e.code!=='ENOENT')throw e;}
  const rel=relative(root,descriptorPath);
  if(!rel.startsWith(`.pdd${sep}try${sep}sessions${sep}`)||rel.split(sep).includes('..'))fail('The Try descriptor must stay in the workspace session folder.');
  const temp=`${pointer}.${process.pid}.tmp`,pfd=openSync(temp,constants.O_WRONLY|constants.O_CREAT|constants.O_EXCL|constants.O_NOFOLLOW,0o600);
  try{writeFileSync(pfd,JSON.stringify({descriptor:rel}));}finally{closeSync(pfd);}
  renameSync(temp,pointer);
  const legacyFolder=join(root,'.pdd/try/bin');privatePath(root,legacyFolder,true);
  const legacy=join(legacyFolder,name);
  try{
    const st=lstatSync(legacy);
    if(st.isSymbolicLink()&&resolve(dirname(legacy),readlinkSync(legacy))===launcher)return alias;
    if(!st.isFile()||st.nlink!==1||!readFileSync(legacy,'utf8').startsWith('#!/bin/sh\n# PDD Try launcher v1\n'))fail('Refusing a symbolic link or non-PDD file at the old launcher path.');
    unlinkSync(legacy);
  }catch(e){if(e.code!=='ENOENT')throw e;}
  symlinkSync(launcher,legacy);
  return alias;
}
export async function runNamedShim(invoked,argv,ports={}) {
  const stderr=ports.stderr??process.stderr;
  try {
    const name=basename(invoked);
    if(!safeName(name))fail('Invalid virtual program name.');
    let root=realpathSync(ports.cwd??process.cwd());
    while(!existsSync(join(root,'.git'))) {const parent=dirname(root);if(parent===root)throw Object.assign(new Error(),{noTry:true});root=parent;}
    const pointer=join(root,'.pdd/try/programs',`${name}.json`);
    try{privatePath(root,pointer);}catch(e){if(e.code==='ENOENT')e.noTry=true;throw e;}
    const record=JSON.parse(readFileSync(pointer,'utf8'));
    if(typeof record.descriptor!=='string')fail('Invalid Try pointer.');
    const descriptor=resolve(root,record.descriptor),rel=relative(root,descriptor);
    if(!rel.startsWith(`.pdd${sep}try${sep}sessions${sep}`)||rel.split(sep).includes('..'))fail('The Try pointer escapes this workspace.');
    privatePath(root,descriptor);
    return await (await import('./try-doors.mjs')).runShim(descriptor,argv,ports);
  }catch(e){stderr.write(`pdd try: ${e.noTry?'no open Try here: run pdd try STORY --cli in your repo':e.code==='EPERM'||e.code==='EACCES'?`Workspace access blocked for ${JSON.stringify(e.path)}.`:cleanText(e.message||'The Try launcher could not run.')}\n`);return 125;}
}
