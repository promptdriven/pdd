// Generated from prompts/cli/program-session.prompt.md (sha256: 8b761772c7dc00458f3b8085546fa4b70ef5bfcf21e55f3a221e9efde8f38bd8).
import { join, posix } from 'node:path';
import { captureSource, gitFiles, readPrompt } from './runtime-preflight.mjs';
import { programTransport } from './runtime-client.mjs';
import { validLink } from './runtime-output.mjs';
import { readPrivate, writePrivate, localError } from './program-data.mjs';
export async function openProgramSession({root,file,program,data,appMap,overlay},ports={}) {
  if(appMap!==undefined&&(typeof appMap!=='string'||!appMap||appMap.includes('\\')||/[\0-\x1f]/.test(appMap)||appMap.startsWith('/')||/^[A-Za-z]:/.test(appMap)||appMap.split('/').includes('..')||['.','.git'].includes(posix.normalize(appMap))||posix.normalize(appMap).startsWith('.git/')))throw localError('App map must be a repository-relative file path with no traversal.');
  const path=join(data.dir,'session.json'),old=readPrivate(path,null);
  if(old?.pending)throw Object.assign(new Error(`A request is pending. Read it with pdd --read ${old.pending.id} ${file}; do not repeat it.`),{exitCode:125});
  const visible=new Set(gitFiles(root)), seen=new Set(), fakes=new Set(), simulation={...data.startingData.simulation}, explicit=new Set(Object.keys(simulation));
  const canonical=v=>JSON.stringify(v,(_,x)=>x&&typeof x==='object'&&!Array.isArray(x)?Object.fromEntries(Object.keys(x).sort().map(k=>[k,x[k]])):x);
  function discover(path){
    if(seen.has(path))return;seen.add(path);const prompt=readPrompt(root,visible,path);if(prompt.error)throw localError(prompt.error);
    for(const call of prompt.interface.calls??[])discover(call.target);
    for(const resource of prompt.interface.resources??[]){
      for(const op of resource.operations??[]){const binding=simulation[resource.name+'.'+op.name];if(explicit.has(resource.name+'.'+op.name)&&['http.prompt','port.prompt'].includes(binding?.action)){fakes.add(binding.target);discover(binding.target);}}
      if(!['http','port'].includes(resource.kind))continue;
      const automatic=(resource.operations??[]).filter(op=>!explicit.has(resource.name+'.'+op.name));if(!automatic.length)continue;
      const target=`prompts/fakes/${resource.name}.prompt.md`;if(!visible.has(target))continue;
      const fake=readPrompt(root,visible,target);if(fake.error)throw localError(fake.error);
      for(const op of automatic){
        const key=resource.name+'.'+op.name;
        const entries=fake.interface.entries??[],entry=entries.find(e=>e.operation===op.name)??(entries.length===1?entries[0]:null);
        if(!entry||canonical(op.arguments_schema)!==canonical(entry.input_schema)||canonical(op.result_schema)!==canonical(entry.result_schema))throw localError(`Custom fake ${target}: operation ${op.name} needs matching input/result schemas.`);
        const bound=Math.min(20,prompt.interface.limits.max_steps);
        if(simulation[key]&&(simulation[key].action!==resource.kind+'.prompt'||simulation[key].target!==target||simulation[key].operation!==entry.operation))throw localError(`Custom fake ${target}: ambiguous binding for ${key}.`);
        simulation[key]={action:resource.kind+'.prompt',target,operation:entry.operation,max_calls:Math.max(bound,simulation[key]?.max_calls??0),request_template:{},request_mapping:[{from:'',to:''}],response_template:{},response_mapping:[{from:'',to:''}]};
      }
      fakes.add(target);discover(target);
    }
  }
  const initialCapture=(ports.captureSource??captureSource)(root,{entry:file,...(appMap===undefined?{}:{appMap}),...(overlay?{prepareSource:overlay}:{})});
  for(const source of initialCapture.sources)if(source.path.endsWith('.prompt.md')&&visible.has(source.path))discover(source.path);
  if(Object.keys(simulation).length)data={...data,startingData:{...data.startingData,simulation}};
  const prepare=overlay||fakes.size?io=>{const files=overlay?overlay(io):[];return [...files,...[...fakes].filter(path=>!files.some(f=>f.path===path)).map(path=>({path,bytes:io.readFile(path)}))];}:undefined;
  const capture=fakes.size?(ports.captureSource??captureSource)(root,{entry:file,...(appMap===undefined?{}:{appMap}),...(prepare?{prepareSource:prepare}:{})}):initialCapture;
  const transport=programTransport({root},ports);
  if(old?.login!==undefined && old.login!==transport.login)throw Object.assign(new Error('The program session belongs to another GitHub login. Sign in as its owner.'),{exitCode:125});
  const selected=JSON.stringify(data.startingData);
  if(old?.id && old.origin===transport.origin&&old.source===capture.sha256&&JSON.stringify(old.world)===JSON.stringify(data.startingData.initial_world)&&old.simulation===JSON.stringify(data.startingData.simulation??null)&&old.appMap===JSON.stringify(appMap??null))return {...old,transport,capture,newSession:false,serve:{origin:transport.origin,request:(path,init)=>transport.request(path,init)},save:record=>writePrivate(path,transport.redact(record))};
  if(old?.id && old.origin!==transport.origin)throw Object.assign(new Error('The saved program belongs to another interpreter origin. Restore its origin before replacing it.'),{exitCode:125});
  if(old?.id){
    const stopId=transport.ports.randomUUID();
    writePrivate(path,{...old,pending:{id:stopId,command:'stop',sessionId:old.id}});
    await transport.stop(old.id,stopId);
  }
  const meta={file,program,appMap:JSON.stringify(appMap??null),simulation:JSON.stringify(data.startingData.simulation??null),world:data.startingData.initial_world,source:capture.sha256,origin:transport.origin,login:transport.login,selected};
  const lintId=transport.ports.randomUUID();
  writePrivate(path,transport.redact({...meta,pending:{id:lintId,command:'lint'}}));
  const lint=await transport.finish(await transport.multipart('lint',{requestId:lintId,source_sha256:capture.sha256},capture),lintId,'lint');
  if(lint.state!=='passed'||lint.result?.exitCode!==0){writePrivate(path,transport.redact(meta));throw Object.assign(new Error(transport.sanitize(lint.result?.report?.refusal?.message||'The interpreter refused the prompt graph. Fix the prompt before running again.')),{exitCode:125});}
  const id=transport.ports.randomUUID();
  writePrivate(path,transport.redact({...meta,pending:{id,command:'try',initial_world:data.startingData.initial_world}}));
  const request={requestId:id,source_sha256:capture.sha256,entry:file,...data.startingData,max_calls:300,...(appMap===undefined?{}:{app_map:appMap,tab:'screen'})};
  const answer=await transport.finish(await transport.multipart('try',request,capture),id,'try');
  if(answer.state!=='passed'||answer.result?.session?.state!=='running'){writePrivate(path,transport.redact(meta));throw Object.assign(new Error(transport.sanitize(answer.result?.report?.refusal?.message||'The interpreter could not start the program. Fix its reported refusal and try again.')),{exitCode:125});}
  if(!validLink(answer.result.url,transport.origin,'try')||!answer.result.session.id)throw Object.assign(new Error('The interpreter returned an invalid program session link. Read the saved setup; do not repeat it.'),{exitCode:125});
  const record={...meta,id:answer.result.session.id,url:answer.result.url,remaining:answer.result.session.remaining_calls,...Object.fromEntries(['kind','entries','expires_at'].filter(k=>answer.result[k]!==undefined||answer.result.session[k]!==undefined).map(k=>[k,answer.result[k]??answer.result.session[k]]))};
  writePrivate(path,transport.redact(record));
  writePrivate(join(data.dir,'world.json'),data.startingData.initial_world);
  return {...record,transport,capture,newSession:true,serve:{origin:transport.origin,request:(path,init)=>transport.request(path,init)},save:record=>writePrivate(path,transport.redact(record))};
}
export async function closeProgramSession(session,ports={}) {
  const transport=session.transport??programTransport({root:session.root,expectedLogin:session.login},ports);
  const id=transport.ports.randomUUID();
  const {transport:unused,capture,save,serve,newSession,...record}=session;
  if(save)save({...record,pending:{id,command:'stop',sessionId:session.id}});
  await transport.stop(session.id,id);
  if(save){delete record.id;save(record);}
}
