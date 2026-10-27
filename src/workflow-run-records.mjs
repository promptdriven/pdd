// Derived status contract: prompts/cli/workflow-run-records.prompt.md.
// Narrowed from the fleet v1 run-record projection and atomic writer.
import * as nodeFs from 'node:fs/promises';
import { basename, join } from 'node:path';
import { randomBytes } from 'node:crypto';
const states = new Set(['completed','waiting','failed','recovery_required','running','unknown']);
const stepStates = new Set(['done','skipped','current','next','failed','unknown']);
const stageId = /^(?=.{1,64}$)[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/;
const object = v => v !== null && typeof v === 'object' && !Array.isArray(v);
const cut = (v,n) => typeof v === 'string' ? [...v].slice(0,n).join('') : null;
const choices = v => Array.isArray(v) ? v.filter(x=>['approve','skip','changes'].includes(x)) : null;
const timestamp = v => Number.isFinite(v) && v >= 0 ? v : null;
export function normalizeRunLinks(links, expectedStage = null) {
  return (Array.isArray(links) ? links : []).filter(link => {
    if (!object(link) || !stageId.test(link.stage ?? '') || expectedStage !== null && link.stage !== expectedStage
      || !['check','try','replay'].includes(link.kind) || typeof link.url !== 'string' || [...link.url].length > 2048
      || !['passed','failed','unknown',null].includes(link.verdict) || link.kind === 'try' && link.verdict !== null) return false;
    try {const url=new URL(link.url);return url.protocol==='https:' && !!url.hostname && !url.username && !url.password;} catch {return false;}
  }).slice(-20).map(({stage,kind,url,verdict})=>({stage,kind,url,verdict}));
}
function sessionOf(source, fallbackAgent) {
  const backend=source?.backend, native=backend?.nativeSession, agent=backend?.agentKind ?? backend?.agent ?? fallbackAgent;
  return native?.kind==='id' && typeof native.value==='string' && native.value && ['codex','claude'].includes(agent)
    ? {agent,id:native.value} : null;
}
function decisionsFromState(records) {
  return (Array.isArray(records)?records:[]).filter(object).map(row=>{
    const stage=row.stage??row.binding?.expectStage, decision=row.decision??row.binding?.decision;
    const via=row.via??row.approvalRecord?.kind, at=timestamp(row.at);
    if(typeof stage!=='string'||!stageId.test(stage)||!['approve','changes','skip'].includes(decision)||!['terminal','chat','phone'].includes(via)||at===null)return null;
    const text=row.text??row.binding?.text??row.approvalRecord?.userMessage??row.approvalRecord?.text;
    const phoneId=row.phoneId??row.approvalRecord?.phoneId;
    return {stage,decision,via,at,...(typeof text==='string'?{text:cut(text,4000)}:{}),...(typeof phoneId==='string'?{phoneId}:{})};
  }).filter(Boolean).slice(-5);
}
function herdrFromState(s, completed) {
  const source=[s.herdr,s.pending?.backend,...completed.toReversed().map(x=>x.backend)].find(x=>typeof x?.session==='string'&&x.session&&typeof x.workspaceId==='string'&&x.workspaceId);
  return typeof source?.session==='string'&&source.session&&typeof source.workspaceId==='string'&&source.workspaceId
    ? {session:source.session,workspaceId:source.workspaceId,label:source.label??source.workspaceName??null}:null;
}
export function runStatusFromState(state, extras = {}) {
  try {
    const s=object(state)?state:{}, phase=['record','exit','journal'].includes(extras.phase)?extras.phase:'journal';
    const valid=Array.isArray(s.definitions) && Number.isInteger(s.index) && s.index>=0 && s.definitions.every(object);
    const defs=valid?s.definitions:[], current=valid?defs[s.index]??null:null;
    const resultState=phase==='exit' ? (['completed','waiting','failed','recovery_required'].includes(extras.outcome?.state)?extras.outcome.state:'unknown')
      : valid && s.index>=defs.length?'completed':valid && phase==='record'?'running':'unknown';
    const completed=Array.isArray(s.completed)?s.completed.filter(object):[], completedById=new Map(completed.map(x=>[x.id,x]));
    const steps=defs.map((d,index)=>{
      const item=completedById.get(d.id), source=item ?? (s.pending?.stage===d.id?s.pending:null), session=sessionOf(source,s.agent);
      return {id:d.id??null,kind:d.kind??null,state:item?(item.skipped?'skipped':'done'):index===s.index?(resultState==='failed'?'failed':'current'):index>s.index?'next':'unknown',
        optional:d.optional===true,startedAt:timestamp(source?.startedAt),endedAt:timestamp(source?.endedAt),agent:session?.agent??source?.agent??null,session};
    });
    const optional=current?.optional===true && !s.optional?.[current.id];
    const nextAdvance=!!current && current.kind!=='merge' && !s.pending && s.proposal?.approval==='next-advance' && !s.accepted;
    const wait=s.waitingPerson ?? s.waitingDecision;
    const resumeDecisions=choices(wait?.decisions) ?? (optional?['approve','skip']:current?.kind==='human'||nextAdvance?['approve']:[]);
    let waitingFor=null;
    if(resultState==='waiting'){
      if(choices(wait?.decisions))waitingFor={decisions:choices(wait.decisions),what:cut(wait.what??extras.outcome?.what,200)};
      else if(choices(extras.outcome?.decisions))waitingFor={decisions:choices(extras.outcome.decisions),what:cut(extras.outcome?.what,200)};
      else if(optional)waitingFor={decisions:['approve','skip'],what:`Run or skip ${current.id}`};
      else if(current?.kind==='human'||nextAdvance)waitingFor={decisions:['approve'],what:'Approve the current proposal and test plan'};
      else if(current?.kind==='merge')waitingFor={decisions:[],what:'Merge the PR on GitHub'};
    }else if(resultState!=='unknown')waitingFor={decisions:[],what:null};
    const backend=['agent','cleanup'].includes(s.pending?.kind)?s.pending.backend:null;
    const native=sessionOf(backend?{backend}:null,s.agent), herdr=herdrFromState(s,completed);
    return {...Object.fromEntries(['runId','repo','issue','root','agent','approvalRecord','waitingDecision'].map(k=>[k,structuredClone(s[k]??null)])),v:1,workflow:s.name??null,
      number:Number.isSafeInteger(s.issue?.number??s.number)?s.issue?.number??s.number:null,
      cancelled:object(s.cancelled)?{state:s.cancelled.state??null,at:timestamp(s.cancelled.at)}:null,
      ...(herdr?{herdr}:{}),decisions:decisionsFromState(s.decisions),
      startedAt:timestamp(s.startedAt),state:resultState,stage:current?{id:current.id,kind:current.kind,index:s.index,total:defs.length}:null,
      waitingFor,resumeDecisions,steps,pr:completed.filter(x=>x.kind==='pr'&&Number.isSafeInteger(x.pr?.number)&&typeof x.pr?.url==='string').map(x=>({stage:x.id,number:x.pr.number,url:x.pr.url})),
      links:normalizeRunLinks(s.links),changes:(Array.isArray(s.changes)?s.changes:[]).filter(object).slice(-5).map(x=>({stage:x.stage,round:x.round,text:cut(x.text,4000),at:x.at})),
      stageAgent:backend?{kind:backend.agentKind??backend.agent??s.agent??null,nativeSessionId:native?.id??null,herdrSession:backend.session??null,paneId:backend.paneId??null}:null,
      controller:structuredClone(extras.controller??null),message:phase==='exit'?cut(extras.outcome?.message,300):null,
      journalSeq:Number.isSafeInteger(s.seq)&&s.seq>=0?s.seq:0,updatedAt:extras.now??null};
  }catch{return {v:1,runId:null,workflow:null,state:'unknown',stage:null,waitingFor:null,resumeDecisions:[],steps:[],pr:[],links:[],changes:[],number:null,cancelled:null,decisions:[],approvalRecord:null,waitingDecision:null,stageAgent:null,controller:null,message:null,journalSeq:0,updatedAt:extras?.now??null};}
}
export async function writeRunStatus(runDir, status, ports = {}) {
  const fs=ports.fs??nodeFs;let temporary,created=false;
  try {
    const bytes=JSON.stringify(status)+'\n';if(Buffer.byteLength(bytes)>256*1024)return {ok:false,code:'too_large'};
    if(await fs.realpath(runDir)!==runDir || !(await fs.lstat(runDir)).isDirectory())return {ok:false,code:'unsafe_directory'};
    temporary=join(runDir,`.status.json.${Buffer.from((ports.randomBytes??randomBytes)(8)).toString('hex')}.tmp`);
    const file=await fs.open(temporary,'wx',0o600);created=true;
    try {await file.writeFile(bytes);await file.sync();}finally{await file.close();}
    await fs.rename(temporary,join(runDir,'status.json'));created=false;
    try {const directory=await fs.open(runDir,'r');try{await directory.sync();}finally{await directory.close();}}catch{}
    return {ok:true};
  }catch(error){if(created)try{await fs.unlink(temporary);}catch{}return {ok:false,code:error?.code??'write_failed'};}
}
export async function readRunStatus(runDir, ports = {}) {
  try {
    const text=await (ports.fs??nodeFs).readFile(join(runDir,'status.json'),'utf8');
    if(Buffer.byteLength(text)>256*1024)return {value:null,warnings:['too_large']};
    let value;try{value=JSON.parse(text);}catch{return {value:null,warnings:['bad_json']};}
    if(!object(value)||value.v!==1||value.runId!==basename(runDir)||!Number.isSafeInteger(value.journalSeq)||value.journalSeq<0)return {value:null,warnings:['bad_record']};
    if(!states.has(value.state))value.state='unknown';value.waitingFor??=null;value.links=normalizeRunLinks(value.links);
    value.steps=(Array.isArray(value.steps)?value.steps:[]).filter(x=>object(x)&&typeof x.id==='string').map(x=>({...x,state:stepStates.has(x.state)?x.state:'unknown'}));
    return {value,warnings:[]};
  }catch(error){return {value:null,warnings:[error?.code==='ENOENT'?'missing':'read_failed']};}
}
