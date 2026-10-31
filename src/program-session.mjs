// Generated from prompts/cli/program-session.prompt.md (sha256: f0fec034310eb85ab47270fbfc06c2ea82fa22564f2ff64b478657d726d0ea7b).
import { join } from 'node:path';
import { captureSource } from './runtime-preflight.mjs';
import { programTransport } from './runtime-client.mjs';
import { validLink } from './runtime-output.mjs';
import { readPrivate, writePrivate } from './program-data.mjs';
export async function openProgramSession({root,file,program,data,appMap,overlay},ports={}) {
  const path=join(data.dir,'session.json'),old=readPrivate(path,null);
  if(old?.pending)throw Object.assign(new Error(`A request is pending. Read it with pdd --read ${old.pending.id} ${file}; do not repeat it.`),{exitCode:125});
  const capture=(ports.captureSource??captureSource)(root,{entry:file,...(overlay?{prepareSource:overlay}:{} )});
  const transport=programTransport({root},ports);
  if(old?.login!==undefined && old.login!==transport.login)throw Object.assign(new Error('The program session belongs to another GitHub login. Sign in as its owner.'),{exitCode:125});
  const selected=JSON.stringify(data.startingData);
  if(old?.id && old.origin===transport.origin&&old.source===capture.sha256&&!data.fresh&&JSON.stringify(old.world)===JSON.stringify(data.startingData.initial_world)&&old.simulation===JSON.stringify(data.startingData.simulation??null)&&old.appMap===JSON.stringify(appMap??null)&&(!data.explicit||old.selected===selected))return {...old,transport,capture,newSession:false,serve:{origin:transport.origin,request:(path,init)=>transport.request(path,init)},save:record=>writePrivate(path,transport.redact(record))};
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
  const request={requestId:id,source_sha256:capture.sha256,entry:file,...data.startingData,max_calls:1000,...(appMap===undefined?{}:{app_map:appMap})};
  const answer=await transport.finish(await transport.multipart('try',request,capture),id,'try');
  if(answer.state!=='passed'||answer.result?.session?.state!=='running'){writePrivate(path,transport.redact(meta));throw Object.assign(new Error(transport.sanitize(answer.result?.report?.refusal?.message||'The interpreter could not start the program. Fix its reported refusal and try again.')),{exitCode:125});}
  if(!validLink(answer.result.url,transport.origin,'try')||!answer.result.session.id)throw Object.assign(new Error('The interpreter returned an invalid program session link. Read the saved setup; do not repeat it.'),{exitCode:125});
  const record={...meta,id:answer.result.session.id,url:answer.result.url,remaining:answer.result.session.remaining_calls};
  writePrivate(path,transport.redact(record));
  writePrivate(join(data.dir,'data.json'),transport.redact(data.startingData.initial_world));
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
