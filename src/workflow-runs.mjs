// Generated from prompts/cli/workflow-runs.prompt.md (sha256: a1d28b96c30184b3885c65dbd4a5d83b05a2e92a73e80e06d89962b3d038899a).
import { execFile as execFileCallback } from 'node:child_process';
import { randomBytes, randomUUID } from 'node:crypto';
import * as nativeRunFiles from 'node:fs';
import { mkdirSync, readFileSync, readdirSync, realpathSync, renameSync, writeFileSync } from 'node:fs';
import { homedir, hostname } from 'node:os';
import { join } from 'node:path';
import { promisify } from 'node:util';
// The chat owner derives a legacy chat's state; this record only projects it.
import { chatLifecycle } from './workflow-chat.mjs';
import { journalRunMutation, drainRunJournal } from './metrics-hooks.mjs';
import { appendEvents } from './metrics-store.mjs';
import { recordCaptureGap } from './metrics-gap.mjs';
import { captureCosts } from './cost-ledger.mjs';

const ordinary = promisify(execFileCallback);
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const sameRepo = (a, b) => typeof a === 'string' && typeof b === 'string' && a.toLowerCase() === b.toLowerCase();
const ended = run => ['cancelled', 'completed'].includes(run.state);

export const runDirFor = (commonDir, number) => join(commonDir, 'pdd', 'runs', String(number));
export const stateDirFor = (ports = {}) => ports.stateDir ?? join((ports.env ?? process.env).HOME || homedir(), '.local', 'state', 'pdd');
export const currentChat = run => [...(run.chats ?? [])].reverse().find(chat => chat.area === run.areas?.[run.area]?.name) ?? null;

export async function gitContext(cwd, ports = {}) {
  const exec = ports.execFile ?? ((file, args, options) => ordinary(file, args, { ...options, encoding: 'utf8' }));
  try {
    const read = async args => String((await exec('git', args, { cwd })).stdout ?? '').trim();
    return { toplevel: realpathSync(await read(['rev-parse', '--show-toplevel'])),
      commonDir: realpathSync(await read(['rev-parse', '--path-format=absolute', '--git-common-dir'])) };
  } catch { return null; }
}

function normalizeArchivedPath(run, directory) {
  const original = runDirFor(run.commonDir ?? '', run.number);
  if (run.runDir === original && directory === `${original}-cancelled-${String(run.runId).slice(0,8)}`) {
    const relocate = value => typeof value === 'string' && (value === original || value.startsWith(original + '/'))
      ? directory + value.slice(original.length) : Array.isArray(value) ? value.map(relocate)
      : object(value) ? Object.fromEntries(Object.entries(value).map(([key,v]) => [key,relocate(v)])) : value;
    Object.assign(run,relocate(run));
  }
}

export function readRun(runDir) {
  try {
    const run = JSON.parse(readFileSync(join(runDir, 'status.json'), 'utf8'));
    if (!object(run) || run.v !== 1 || !Number.isSafeInteger(run.number)) return null;
    normalizeArchivedPath(run, runDir);
    return run;
  } catch { return null; }
}

function runsIn(commonDir, { cancelled = false } = {}) {
  let names;
  try { names = readdirSync(join(commonDir, 'pdd', 'runs')); } catch { return []; }
  const folder = cancelled ? /^[1-9][0-9]*(?:-cancelled-[0-9a-f]+)?$/ : /^[1-9][0-9]*$/;
  return names.filter(name => folder.test(name)).map(name => readRun(runDirFor(commonDir, name))).filter(Boolean)
    .sort((a, b) => a.number - b.number);
}

// Every run on this machine: repositories come only from the run index.
export function allRuns({ cancelled = false } = {}, ports = {}) {
  const commonDirs = new Set(readIndex(ports).map(entry => typeof entry.runDir === 'string' ? join(entry.runDir, '..', '..', '..') : null).filter(Boolean));
  const seen = new Set();
  return [...commonDirs].flatMap(commonDir => runsIn(commonDir, { cancelled }))
    .filter(run => {
      const attempt = JSON.stringify([run.runDir, run.runId, run.startedAt]);
      if (seen.has(attempt)) return false;
      seen.add(attempt); return true;
    });
}

function readIndex(ports) {
  try {
    const index = JSON.parse(readFileSync(join(stateDirFor(ports), 'runs.json'), 'utf8'));
    return Array.isArray(index?.runs) ? index.runs.filter(entry => object(entry) && Number.isSafeInteger(entry.number)) : [];
  } catch { return []; }
}

function updateIndex(run, ports) {
  const directory = stateDirFor(ports);
  mkdirSync(directory, { recursive: true, mode: 0o700 });
  const entry = { repo: run.repo, number: run.number, workflow: run.workflow, state: run.state, runDir: run.runDir, root: run.root, updatedAt: run.updatedAt };
  const runs = [...readIndex(ports).filter(item => item.runDir !== run.runDir), entry].slice(-200);
  const temporary = join(directory, `.runs.json.${randomBytes(6).toString('hex')}.tmp`);
  writeFileSync(temporary, JSON.stringify({ version: 1, runs }, null, 2) + '\n', { mode: 0o600 });
  renameSync(temporary, join(directory, 'runs.json'));
}

// The C3 view (v:1) that phone clients read; it is derived from the saved run fields on every write.
export function statusView(run) {
  const areas = Array.isArray(run.areas) ? run.areas : [], area = areas[run.area] ?? null, done = object(run.done) ? run.done : {};
  const flat = areas.flatMap((item, index) => item.steps.map(step => ({ step, area: item.name, index, optional: item.optional.includes(step) })));
  const chatFor = name => [...(run.chats ?? [])].reverse().find(chat => chat.area === name) ?? null;
  const lastPr = (run.pr ?? []).some(pr => pr.stage === areas.at(-1)?.name);
  const gate = run.gate && run.state !== 'cancelled' && (run.state !== 'completed' || run.gate.kind === 'ask-code');
  const current = gate ? 'approve' : ended(run) ? null : lastPr ? 'merge' : area?.steps.find(step => !done[step]) ?? null;
  const total = flat.length;
  const stage = !current ? null : current === 'merge' ? { id: 'merge', kind: 'merge', index: total, total }
    : current === 'approve' ? { id: 'approve', kind: 'human', index: flat.filter(item => item.index <= run.area).length, total }
    : { id: current, kind: 'agent', index: flat.findIndex(item => item.index === run.area && item.step === current), total };
  const steps = flat.map((item, position) => {
    const record = done[item.step], chat = chatFor(item.area), previous = flat[position - 1];
    const state = record ? (/^skipped\b/i.test(record.summary ?? '') ? 'skipped' : 'done')
      : item.index < run.area ? (item.optional ? 'skipped' : 'unknown')
      : item.index === run.area && item.step === current ? 'current' : 'next';
    const startedAt = previous?.area === item.area ? done[previous.step]?.at ?? null : chat?.startedAt ?? null;
    return { id: item.step, kind: 'agent', area: item.area, optional: item.optional, state, startedAt: state === 'next' ? null : startedAt,
      endedAt: record?.at ?? null, agent: run.agent ?? null, session: chat?.session ?? null, summary: record?.summary ?? null };
  });
  const asked = run.question && !ended(run);
  const failure = !ended(run) && run.chatFailure?.area === area?.name ? run.chatFailure : null;
  const waitingFor = failure ? { decisions: [], what: `Chat ${failure.phase} not confirmed (${failure.code}): ${failure.message}. Run pdd workflow open ${run.number}.` } : asked ? { decisions: ['changes'], what: run.question.text.split('\n')[0].slice(0, 200) } : gate ? { decisions: ['approve', 'changes'], what: run.gate.kind === 'ask-code' ? 'Make the code PR now, or stop here and merge PR 1'
      : run.gate.kind === 'approve-pr' ? 'Try it, then approve to open the PR, or ask for changes' : `Approve the ${run.gate.area} area or ask for changes` }
    : run.state === 'waiting' && lastPr ? { decisions: [], what: 'Review and merge the PR on GitHub' } : { decisions: [], what: null };
  const chat = ended(run) ? null : currentChat(run);
  return { v: 1, stage, steps, waitingFor, resumeDecisions: gate ? ['approve', 'changes'] : [],
    waitingDecision: gate ? { ...(run.gate.id ? { id: run.gate.id } : {}), ...(Object.hasOwn(run.gate, 'promptSnapshot') ? { promptSnapshot: run.gate.promptSnapshot } : {}), stage: 'approve', area: run.gate.area, kind: run.gate.kind ?? 'approve', at: run.gate.at, decisions: ['approve', 'changes'] } : null,
    ...(chat?.workspaceId ? { herdr: { session: 'pdd', workspaceId: chat.workspaceId, label: `${String(run.repo).split('/')[1]}#${run.number} ${run.workflow}` } } : {}),
    stageAgent: chat && !failure && !chat.startUnconfirmed ? { kind: run.agent, nativeSessionId: chat.session?.id ?? null, herdrSession: 'pdd', paneId: chat.paneId ?? null, state: chatLifecycle(chat) } : null,
    links: Array.isArray(run.links) ? run.links : [], controller: null, message: run.message ?? null, cancelled: run.cancelled ?? null };
}

// One short local owner protects selecting latest state as well as publication.
// Busy owners are never reclaimed by age or by a guessed process identity.
const activeRunOwners = new Set();
const pauseBuffer = new Int32Array(new SharedArrayBuffer(4));
const identity = run => [run.v, run.runId, run.number, run.repo, run.root, run.commonDir, run.runDir];
const sameIdentity = (a, b) => JSON.stringify(identity(a)) === JSON.stringify(identity(b));
function saveError(error) {
  if (['workflow_run_save_failed', 'workflow_progress_refused'].includes(error?.code)) return error;
  return Object.assign(new Error(`Could not save workflow progress: ${error.message ?? error}${/retry/i.test(error.message ?? '') ? '' : '. Check the run folder and retry.'}`), {code:'workflow_run_save_failed',cause:error});
}
const ownershipFiles=ports=>({...nativeRunFiles,...ports.runFiles});
function ownerEntries(path,fs) { return fs.readdirSync(path).filter(name=>/^owner-[A-Za-z0-9_-]+\.json$/.test(name)); }
function readOwner(path,name,fs) {
  const text=fs.readFileSync(join(path,name),'utf8'),value=JSON.parse(text);
  if(!Number.isInteger(value.pid)||value.pid<1||typeof value.hostname!=='string'||!value.hostname||typeof value.token!=='string'||name!==`owner-${value.token}.json`)throw Error('Malformed owner');
  return {value,text};
}
export function readRunOwnership(runDir,ports={}) {
  const fs=ownershipFiles(ports),path=join(runDir,'.ordinary-owner'),empty={path,pid:null,hostname:null,token:null,warning:null};
  try {
    fs.lstatSync(path);
    const entries=ownerEntries(path,fs);
    if(!entries.length){if(fs.readdirSync(path).includes('.namespace'))return null;throw Error('Owner metadata is missing');}
    let value;
    try{value=JSON.parse(fs.readFileSync(join(path,entries[0]),'utf8'));}catch{return {...empty,warning:'Ownership metadata is malformed or unreadable'};}
    const snapshot={...empty,pid:Number.isInteger(value?.pid)&&value.pid>0?value.pid:null,hostname:typeof value?.hostname==='string'&&value.hostname?value.hostname:null,token:typeof value?.token==='string'&&value.token?value.token:null};
    snapshot.warning=!snapshot.pid||!snapshot.hostname||!snapshot.token||entries[0]!==`owner-${snapshot.token}.json`?'Ownership metadata is malformed':entries.length>1?'More than one ownership claim is present':null;
    return snapshot;
  } catch(error) {
    if(error.code==='ENOENT'){
      try{fs.lstatSync(path);}catch(missing){if(missing.code==='ENOENT')return null;}
    }
    return {...empty,warning:'Ownership metadata is missing, malformed or unreadable'};
  }
}
function claimRun(runDir, fs,ports) {
  const path=join(runDir,'.ordinary-owner');
  if(activeRunOwners.has(runDir))throw Error('A nested ordinary run save is not allowed');
  const host=typeof ports.hostname==='function'?ports.hostname():ports.hostname??hostname();
  const owner={pid:ports.ownerPid??process.pid,hostname:host,token:randomBytes(16).toString('hex')};
  const leaf=join(path,`owner-${owner.token}.json`),bytes=JSON.stringify(owner);
  const alive=pid=>{try{if(ports.processIdentity)return ports.processIdentity(pid)?.alive;process.kill(pid,0);return true;}catch(error){return error.code==='ESRCH'?false:null;}};
  const busy=()=>{const held=readRunOwnership(runDir,{...ports,runFiles:fs});return Object.assign(Error(`Another command owns workflow progress at ${path}${held?.pid ? ` (PID ${held.pid}, host ${held.hostname}, token ${held.token})` : ' (owner unknown)'}. Wait briefly; if no pdd command is running, inspect and remove this ownership folder, then retry`),{code:'workflow_run_busy'});};
  let created=false,acquired;
  try{fs.mkdirSync(path,{mode:0o700});created=true;}catch(error){if(error.code!=='EEXIST')throw error;}
  try{acquired=fs.lstatSync(path);}catch(error){if(created)try{fs.rmdirSync(path);}catch{}throw error;}
  if(!acquired.isDirectory())throw busy();
  if(created)fs.writeFileSync(join(path,'.namespace'),'v1',{mode:0o600,flag:'wx'});
  // Keep the namespace directory permanently. Token-specific leaves avoid the
  // empty-directory unlink race when another acquisition replaces an old owner.
  const ownDirectory=()=>{const current=fs.lstatSync(path);return current.dev===acquired.dev&&current.ino===acquired.ino;};
  const release=()=>{activeRunOwners.delete(runDir);try{if(ownDirectory()&&fs.readFileSync(leaf,'utf8')===bytes)fs.unlinkSync(leaf);}catch{}};
  for(let attempt=0;;attempt++){
    let protectedOwner=false;
    const entries=ownerEntries(path,fs);
    if(!entries.length&&!fs.readdirSync(path).includes('.namespace'))throw busy();
    for(const name of entries){
      let observed;try{observed=readOwner(path,name,fs);}catch{protectedOwner=true;continue;}
      if(observed.value.hostname!==host||alive(observed.value.pid)!==false){protectedOwner=true;continue;}
      // Each token has its own immutable leaf: removing a dead token cannot
      // unlink a different replacement token, even in the same namespace.
      if(ownDirectory()&&fs.readFileSync(join(path,name),'utf8')===observed.text)try{fs.unlinkSync(join(path,name));}catch(error){if(error.code!=='ENOENT')throw error;}
    }
    if(!protectedOwner){
      if(!ownDirectory())throw busy();
      try{fs.writeFileSync(join(path,'.namespace'),'v1',{mode:0o600,flag:'wx'});}catch(error){if(error.code!=='EEXIST')throw error;}
      const temporary=join(runDir,`.ordinary-${owner.token}.tmp`);
      try{fs.writeFileSync(temporary,bytes,{mode:0o600,flag:'wx'});fs.renameSync(temporary,leaf);}finally{try{fs.unlinkSync(temporary);}catch{}}
      if(ownerEntries(path,fs).every(name=>name===`owner-${owner.token}.json`)){activeRunOwners.add(runDir);return release;}
      release();
    }
    if(attempt===9)throw busy();
    Atomics.wait(pauseBuffer,0,0,10);
  }
}
function ownedRun(runDir, ports, action, {create=false}={}) {
  const fs={...nativeRunFiles,...ports.runFiles};
  let release;
  try {
    if (create) fs.mkdirSync(runDir,{recursive:true});
    release=(ports.acquireRunOwnership ?? (directory=>claimRun(directory,fs,ports)))(runDir);
    if (typeof release !== 'function') throw Error('Run ownership was not acquired');
    return action(fs);
  } catch (error) { throw saveError(error); }
  finally { if (release) {try{release();}catch{/* Release trouble cannot undo or misreport a published record. */}} }
}
// The status record is the retained outbox; measurement failures never own progress.
function metricsWarning(ports, message) {
  try { (ports.metricsWarning ?? (text => process.stderr.write(text + '\n')))(message); } catch { /* Observational only. */ }
}
export function metricsSource(run, fs = nativeRunFiles, now = Date.now) {
  const dir = join(run.commonDir, 'pdd', 'metrics'), file = join(dir, 'installation.json');
  fs.mkdirSync(dir, {recursive:true, mode:0o700});
  const temp = join(dir, `.identity-${randomUUID()}`);
  try {
    fs.writeFileSync(temp, JSON.stringify({source:`install:${randomUUID()}`,captureStartedAt:new Date(now()).toISOString()}), {mode:0o600,flag:'wx'});
    try { fs.linkSync(temp,file); } catch (error) { if (error.code !== 'EEXIST') throw error; }
  } finally { try { fs.unlinkSync(temp); } catch {} }
  const identity=JSON.parse(fs.readFileSync(file,'utf8'));
  if (typeof identity.source !== 'string' || !identity.source || !Number.isFinite(Date.parse(identity.captureStartedAt))) throw Error('Invalid installation identity');
  return identity.source;
}
function captureRunCosts(before, run, ports, fs) {
  try { run.cost = captureCosts(before, run, { ...ports, fs }); }
  catch { if (before?.cost) run.cost = structuredClone(before.cost); if (run.cost) run.cost.coverage = [...new Set([...(run.cost.coverage ?? []), 'capture-failed'])]; }
}
function captureMutation(before, run, ports, fs) {
  captureRunCosts(before, run, ports, fs);
  try {
    const observedAt = new Date((ports.now ?? Date.now)()).toISOString();
    const source = metricsSource(run,fs,ports.now ?? Date.now);
    Object.assign(run,journalRunMutation({before,after:run,source,observedAt,transitionId:randomUUID(),observations:run.metricsObservations ?? []}));
    delete run.metricsObservations;
  } catch {
    run.metrics = {...run.metrics, coverageGap:true, coverageGapAt:run.metrics?.coverageGapAt ?? (ports.now ?? Date.now)()};
    metricsWarning(ports,'Metrics capture incomplete; workflow progress continues.');
  }
}
function deliverMetrics(run, ports) {
  if (ports.skipMetricsDelivery || !run.metrics?.events?.length) return;
  let delivery;
  try { delivery=drainRunJournal({run,root:run.sourceRoot,store:{appendEvents:ports.metricsAppendEvents ?? (input=>appendEvents(input,{commonDir:async()=>run.commonDir}))}}); }
  catch { metricsWarning(ports,'Metrics journal delivery incomplete; retained events can be retried.');return; }
  void Promise.resolve(delivery).then(result=>{
    if (result.ok) return;
    metricsWarning(ports,'Metrics journal delivery incomplete; retained events can be retried.');
    try { updateRun(run.runDir, current => { current.metrics={...current.metrics,coverageGap:true,coverageGapAt:current.metrics?.coverageGapAt ?? (ports.now ?? Date.now)()}; return current; }, {...ports,skipMetricsDelivery:true}); }
    catch { try {(ports.metricsGap ?? recordCaptureGap)({commonDir:run.commonDir,repo:run.repo,issue:run.number,at:(ports.now ?? Date.now)()},ports.metricsFiles);} catch { /* Retained outbox still supplies retry. */ } }
  }).catch(() => { metricsWarning(ports,'Metrics journal delivery incomplete; retained events can be retried.'); });
}

function publishRun(run, ports, fs, { costOnly = false, preserveProgress = false } = {}) {
  if (!costOnly) {
    run.journalSeq = (Number.isSafeInteger(run.journalSeq) ? run.journalSeq : 0) + 1;
    run.updatedAt = (ports.now ?? Date.now)();
    if (!preserveProgress) delete run.progressAt;
    Object.assign(run, statusView(run));
  }
  const temporary = join(run.runDir, `.status.json.${randomBytes(6).toString('hex')}.tmp`);
  try {
    fs.writeFileSync(temporary, JSON.stringify(run, null, 2) + '\n', { mode: 0o600, flag:'wx' });
    fs.renameSync(temporary, join(run.runDir, 'status.json'));
  } finally { try { fs.unlinkSync(temporary); } catch { /* Published or not created. */ } }
  return run;
}
function indexed(run, ports) {
  try { updateIndex(run, ports); } catch { /* Selection index is best effort after commit. */ }
  return run;
}
export function writeRun(run, ports = {}) {
  ownedRun(run.runDir, ports, fs=>{let before;try{before=JSON.parse(fs.readFileSync(join(run.runDir,'status.json'),'utf8'));}catch{} captureMutation(before,run,ports,fs);return publishRun(run,ports,fs);}, {create:true});
  deliverMetrics(run,ports);
  return indexed(run,ports);
}
export function updateRun(runDir, update, ports = {}) {
  const committed=ownedRun(runDir,ports,fs=>{
    const run=JSON.parse(fs.readFileSync(join(runDir,'status.json'),'utf8'));
    if (object(run)) normalizeArchivedPath(run, runDir);
    if (!object(run) || run.v!==1 || !Number.isSafeInteger(run.number) || run.runDir!==runDir) throw Error('The existing run record is missing, unreadable or invalid');
    const original=structuredClone(run);
    const result=update(run);
    if (!object(result) || typeof result.then==='function' || !sameIdentity(original,result)) throw Error('An ordinary update must return the same run identity synchronously');
    captureMutation(original,result,ports,fs);
    return publishRun(result,ports,fs,{preserveProgress:ports.preserveProgress === true});
  });
  deliverMetrics(committed,ports);
  return indexed(committed,ports);
}

// Invoke the guarded submission while ordinary progress is excluded, but never
// retain ownership while waiting for the transport's asynchronous result.
export function inspectRunAndStart(runDir, action, ports = {}) {
  return ownedRun(runDir, ports, fs => {
    const run = JSON.parse(fs.readFileSync(join(runDir, 'status.json'), 'utf8'));
    if (!object(run) || run.v !== 1 || run.runDir !== runDir) throw Error('The existing run record is missing, unreadable or invalid');
    return action(run);
  });
}

// Persist observations without making a polling dashboard count as workflow activity.
export function updateRunCosts(runDir, update, ports = {}) {
  return ownedRun(runDir, ports, fs => {
    const run = JSON.parse(fs.readFileSync(join(runDir, 'status.json'), 'utf8'));
    if (!object(run) || run.v !== 1 || !Number.isSafeInteger(run.number) || run.runDir !== runDir) throw Error('The existing run record is missing, unreadable or invalid');
    const result = update(structuredClone(run));
    if (!object(result) || typeof result.then === 'function' || !sameIdentity(run, result)) throw Error('A cost update must return the same run identity synchronously');
    const observed = { ...run, cost: result.cost,
      progressAt: Number.isFinite(run.progressAt) ? run.progressAt : fs.statSync(join(runDir, 'status.json')).mtimeMs };
    captureRunCosts(run, observed, ports, fs);
    return publishRun(observed, ports, fs, { costOnly: true });
  });
}

export async function runForWorktree(cwd, ports = {}) {
  const context = await gitContext(cwd, ports);
  return context ? runsIn(context.commonDir, {cancelled:true}).find(run => run.root === context.toplevel) ?? null : null;
}

export async function listRuns({ cwd, cancelled = false }, ports = {}) {
  const context = await gitContext(cwd, ports);
  if (context) return runsIn(context.commonDir, { cancelled });
  return readIndex(ports).map(entry => readRun(entry.runDir)).filter(Boolean);
}

function parseRef(ref) {
  const text = String(ref).trim().replace(/\/$/, '');
  const match = /^#?([1-9][0-9]*)$/.exec(text) ?? /^([^/\s#]+\/[^/\s#]+)#([1-9][0-9]*)$/.exec(text)
    ?? /^https:\/\/github\.com\/([^/]+\/[^/]+)\/issues\/([1-9][0-9]*)$/.exec(text);
  if (!match) return null;
  return match.length === 2 ? { number: Number(match[1]) } : { repo: match[1], number: Number(match[2]) };
}

const choices = runs => runs.map(run => `  ${run.repo}#${run.number} ${run.workflow ?? ''} (${run.state ?? 'unknown'})`).join('\n');

export async function resolveRun(ref, { cwd }, ports = {}) {
  const context = await gitContext(cwd, ports);
  if (ref === undefined || ref === null || ref === '') {
    const runs = context ? runsIn(context.commonDir, {cancelled:true}) : readIndex(ports).map(entry => readRun(entry.runDir)).filter(Boolean);
    const own = context && runs.find(run => run.root === context.toplevel);
    if (own) return { run: own };
    const active = runs.filter(run => !ended(run)), waiting = active.filter(run => run.gate);
    const pick = waiting.length === 1 ? waiting[0] : active.length === 1 ? active[0] : null;
    if (pick) return { run: pick };
    return { error: active.length ? `More than one run is active. Name the issue:\n${choices(active)}` : 'No active pdd run here. Start one with: pdd workflow run NAME ISSUE' };
  }
  const wanted = parseRef(ref);
  if (!wanted) return { error: `"${String(ref).slice(0, 80)}" is not an issue number, owner/repo#N or issue URL.` };
  if (context) {
    const own = runsIn(context.commonDir, {cancelled:true}).find(run => run.root === context.toplevel);
    if (own && own.number === wanted.number && (!wanted.repo || sameRepo(own.repo,wanted.repo))) return {run:own};
    const run = readRun(runDirFor(context.commonDir, wanted.number));
    if (run && (!wanted.repo || sameRepo(run.repo, wanted.repo))) return { run };
    if (!wanted.repo) return { error: `This repository has no pdd run for #${wanted.number}. See the runs: pdd workflow status` };
  }
  const entries = readIndex(ports).filter(entry => entry.number === wanted.number && (!wanted.repo || sameRepo(entry.repo, wanted.repo)));
  const repos = [...new Map(entries.map(entry => [String(entry.repo).toLowerCase(), entry])).values()];
  if (repos.length > 1) return { error: `More than one repository has a run for #${wanted.number}. Use owner/repo#${wanted.number}:\n${repos.map(entry => `  ${entry.repo}#${entry.number}`).join('\n')}` };
  if (!repos.length) return { error: `No pdd run found for ${wanted.repo ? `${wanted.repo}#` : '#'}${wanted.number}.` };
  const run = readRun(repos[0].runDir);
  return run ? { run } : { error: `The run record for ${repos[0].repo}#${wanted.number} is missing at ${repos[0].runDir}.` };
}
