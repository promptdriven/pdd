// Generated from prompts/cli/workflow-prove.prompt.md (sha256: ea04b2e52eee9f432df280bd6738f573b0e2387ee0e0d45564b12a5da115091b).
import { execFile as execFileCallback, spawn } from 'node:child_process';
import { randomUUID, randomBytes } from 'node:crypto';
import { resolveRun, updateRun } from './workflow-runs.mjs';
import { applyCostMeasurement } from './cost-ledger.mjs';
import { formatAffectedTestsSummary, selectAffectedTests } from './test-selection.mjs';
import { constants, fchmodSync, closeSync, existsSync, lstatSync, mkdirSync, mkdtempSync, openSync, readFileSync, readdirSync, realpathSync, renameSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, isAbsolute, join } from 'node:path';
import { StringDecoder } from 'node:string_decoder';
import { promisify } from 'node:util';

const execFile = promisify(execFileCallback);
const diagnostic = error => String(error?.message ?? error ?? '').split(/[\r\n]/)[0].replace(/[\x00-\x1f\x7f]/g, ' ').slice(0, 1000);
const emptyPhase = () => ({ exitCode: null, signal: '', timedOut: false, outputLimited: false, stdoutTail: [], stderrTail: [], expectedFound: false, error: '', setupError: '', observedError: '' });
const EMPTY_PHASE = emptyPhase(), phaseKeys = Object.keys(EMPTY_PHASE);
const isEmptyPhase = phase => phaseKeys.every(key => JSON.stringify(phase[key]) === JSON.stringify(EMPTY_PHASE[key]));
const phaseRan = phase => phase.exitCode !== null || Boolean(phase.signal || phase.timedOut || phase.outputLimited);
const lines = value => { const parts = value.replace(/\r\n/g, '\n').split('\n'); if (parts.at(-1) === '') parts.pop(); return parts; };
const setupDiagnostic = value => lines(value).find(line => /^(?:# )?(?:Error: Cannot find module|Error \[ERR_MODULE_NOT_FOUND\]|ModuleNotFoundError:|ImportError:|FileNotFoundError:|Error: ENOENT|ENOENT:)/.test(line));
function observedError(stdout, stderr) {
  const err = lines(stderr), out = lines(stdout), all = [...err, ...out];
  const found = all.find(s => /^\s*(?:# )?\s*code:/.test(s)) ?? all.find(s => s.trim() && /error|code|assert|exception/i.test(s)) ?? err.find(s => s.trim()) ?? out.find(s => s.trim()) ?? 'no output';
  return [...found.trim()].slice(0, 240).join('');
}
function phaseRecord(result, expect) {
  return { exitCode: result.exitCode, signal: result.signal, timedOut: result.timedOut, outputLimited: result.outputLimited,
    stdoutTail: lines(result.stdout).slice(-20), stderrTail: lines(result.stderr).slice(-20), expectedFound: Boolean(expect) && (typeof result.expectedFound === 'boolean' ? result.expectedFound : (result.stdout.includes(expect) || result.stderr.includes(expect))), error: diagnostic(result.error), setupError: diagnostic(result.setupError), observedError: observedError(result.stdout, result.stderr) };
}
export function classifyProof(record) {
  if (record.setupError || record.cleanupError || record.base.error || record.head.error || record.base.setupError || record.head.setupError || [126,127].includes(record.base.exitCode) || [126,127].includes(record.head.exitCode)) return 'setup-error';
  if (record.interruptSignal) return 'signalled';
  // Preserve legacy unexecuted records; an empty overlay does not classify executed proofs.
  if (!record.paths.length && [record.base, record.head].every(isEmptyPhase)) return 'no-changed-tests';
  if (record.base.timedOut) return 'base-timeout';
  if (record.head.timedOut) return 'head-timeout';
  if (record.base.outputLimited || record.head.outputLimited) return 'output-limit';
  if (record.base.signal || record.head.signal) return 'signalled';
  if (record.head.exitCode !== 0) return 'head-fails';
  if (record.base.exitCode === 0) return 'old-passes';
  return record.base.expectedFound ? 'proved' : 'wrong-reason';
}
function safeValue(value, command = false) {
  const text = String(value);
  let content = (command ? text.replace(/[\x00-\x1f]/g, char => JSON.stringify(char).slice(1,-1)) : JSON.stringify(text).slice(1,-1)).replace(/[\u007f-\u009f\u2028\u2029]/g, char => '\\u'+char.charCodeAt(0).toString(16).padStart(4,'0')).replaceAll('pdd-workflow:', 'pdd-workflow\\u003a');
  let fenceLength = 1;
  for (const run of content.matchAll(/`+/g)) fenceLength = Math.max(fenceLength, run[0].length + 1);
  const fence = '`'.repeat(fenceLength);
  const padding = content.startsWith('`') || content.endsWith('`') || content.startsWith(' ') && content.endsWith(' ') && content.trim() ? ' ' : '';
  return fence+padding+content+padding+fence;
}
function actualTail(record) {
  const nonzero = phase => phase.exitCode !== null && phase.exitCode !== 0;
  const phase = record.outcome === 'head-fails' ? record.head : [record.base,record.head].find(p=>p.setupError || p.error || [126,127].includes(p.exitCode)) ?? [record.base,record.head].find(nonzero);
  if (!phase) return '';
  const source = phase.stderrTail.some(s=>s.trim()) ? phase.stderrTail : phase.stdoutTail;
  const nonblank = source.filter(s=>s.trim());
  const summary = /^(?:# (?:tests|suites|pass|fail|cancelled|skipped|todo) [0-9]+|# duration_ms [0-9]+(?:\.[0-9]+)?|[0-9]+\.\.[0-9]+)$/;
  let end = nonblank.length;
  while (end > 0 && summary.test(nonblank[end-1].trim())) end--;
  const selected = end > 0 && end < nonblank.length ? nonblank.slice(0,end) : nonblank;
  return [...selected.slice(-3).join('\n')].slice(-240).join('');
}
export function formatProof(record) {
  const command=safeValue(record.test, true), expected=safeValue(record.expect), base=safeValue(record.base.exitCode ?? 'none'), head=safeValue(record.head.exitCode ?? 'none');
  if(record.outcome==='proved') return `Old-code proof: ✓ ${command}: old-code exit ${base}; output contains ${expected}; new-code exit ${head}.`;
  let cause;
  if(record.outcome==='wrong-reason')cause=record.base.observedError;
  else if(record.outcome==='head-fails')cause=record.head.observedError;
  else if(record.outcome==='setup-error')cause=record.setupError || record.cleanupError || [record.base,record.head].flatMap(p=>[p.setupError,p.error]).find(Boolean) || 'setup failed';
  else if(record.outcome==='signalled' && record.interruptSignal)cause=`parent ${record.interruptSignal}`;
  else {const phase=record.outcome==='head-timeout' || record.outcome==='output-limit' && !record.base.outputLimited || record.outcome==='signalled' && !record.base.signal ? record.head : record.base;cause=phaseRan(phase) ? phase.observedError : record.outcome;}
  const tail=['head-fails','setup-error'].includes(record.outcome)?actualTail(record):'';
  return `Old-code proof: ✗ ${record.outcome}; command ${command}; old-code exit ${base}; new-code exit ${head}; expected ${expected}; cause ${safeValue(cause)}${tail?`; tail ${safeValue(tail)}`:''}.`;
}
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const exactKeys = (value, keys) => object(value) && Object.keys(value).length === keys.length && keys.every(key => Object.hasOwn(value, key));
export function validateProofRecord(record) {
  if (!exactKeys(record, ['v','origin','runId','baseSha','headSha','test','expect','paths','base','head','outcome','cleanupError','setupError','interruptSignal']) || record.v !== 2 || record.origin !== 'pdd.workflow-prove.v2') return false;
  if (!['','SIGINT','SIGTERM','SIGHUP'].includes(record.interruptSignal)) return false;
  if (!['runId','baseSha','headSha','test','expect','outcome','cleanupError','setupError'].every(key => typeof record[key] === 'string') || !record.runId || !record.test.trim() || !record.expect.trim()) return false;
  if (!Array.isArray(record.paths) || record.paths.some(path => typeof path !== 'string' || !safePath(path)) || new Set(record.paths).size !== record.paths.length) return false;
  for (const phase of [record.base, record.head]) {
    if (!exactKeys(phase, phaseKeys) || !(phase.exitCode === null || Number.isInteger(phase.exitCode) && phase.exitCode >= 0 && phase.exitCode <= 255)
      || !['signal','error','setupError','observedError'].every(key => typeof phase[key] === 'string') || !['timedOut','outputLimited','expectedFound'].every(key => typeof phase[key] === 'boolean')
      || !['stdoutTail','stderrTail'].every(key => Array.isArray(phase[key]) && phase[key].length <= 20 && phase[key].every(line => typeof line === 'string' && !line.includes('\n')))
      || [...phase.observedError].length > 240) return false;
    if (!phaseRan(phase) && !phase.error && !phase.setupError && (phase.expectedFound || phase.stdoutTail.length || phase.stderrTail.length || phase.observedError)) return false;
  }
  if (record.outcome !== classifyProof(record)) return false;
  if (!record.interruptSignal && !['setup-error','no-changed-tests'].includes(record.outcome) && (!phaseRan(record.base) || !phaseRan(record.head))) return false;
  if (record.outcome === 'no-changed-tests' && ![record.base, record.head].every(isEmptyPhase)) return false;
  return true;
}
const safePath = path => typeof path === 'string' && path.length > 0 && !isAbsolute(path) && !path.includes('\\') && !path.includes('\0') && path.split('/').every(part => part && part !== '.' && part !== '..' && part.toLowerCase() !== '.git');
const rootConvention = path => /^(?:test|tests|__tests__|fixtures)\//.test(path);
const testEntry = path => /(?:\.test\.|\.spec\.)(?:js|mjs|cjs|jsx|ts|tsx)$/.test(path) || /(?:^|\/)test_[^/]*\.py$/.test(path) || /_test\.(?:py|go)$/.test(path) || /^(?:test|tests)\/runtime\/.*\.json$/.test(path);
function selectFiles(files) {
  const paths = []; let entries = 0;
  for (const file of files) {
    if (file.status === 'D' || file.path.startsWith('src/')) continue;
    if (!['A','M','R'].includes(file.status) || !(rootConvention(file.path) || testEntry(file.path))) continue;
    if (!safePath(file.path)) throw Error('Unsafe overlay path.');
    if (file.mode === '120000') throw Error('Changed test or fixture is a symlink.');
    if (!['100644','100755'].includes(file.mode)) continue;
    if (!paths.includes(file.path)) { paths.push(file.path); if (testEntry(file.path)) entries++; }
  }
  return entries ? paths : [];
}
const git = async (root, args, encoding = 'utf8') => (await execFile('git', args, { cwd: root, encoding, maxBuffer: 64 * 1024 * 1024 })).stdout;
async function readRun({ ref, cwd }) {
  const result = await resolveRun(ref, { cwd });
  if (!result.run) return { run: null, error: diagnostic(result.error) };
  const { runId, runDir, root, baseSha, baseBranch } = result.run; return { run: { runId, runDir, root, baseSha, baseBranch }, error: '' };
}
async function snapshot({root, baseBranch}) {
  const snapshot = { baseSha: '', headSha: '', baseAvailable: false, headAvailable: false, files: [], error: '' };
  try {
    await recoverStale(root);
    await git(root,['check-ref-format',`refs/heads/${baseBranch}`]);
    await git(root,['fetch','origin',`refs/heads/${baseBranch}:refs/remotes/origin/${baseBranch}`]);
    snapshot.headSha = (await git(root, ['rev-parse','--verify','HEAD^{commit}'])).trim(); snapshot.headAvailable = true;
    const baseSha = (await git(root,['merge-base',snapshot.headSha,`refs/remotes/origin/${baseBranch}`])).trim(); snapshot.baseSha=baseSha; snapshot.baseAvailable = true;
    const buffer = await git(root, ['diff','--raw','-z','--no-abbrev','-M',baseSha,snapshot.headSha,'--'], null);
    const value = buffer.toString('utf8'); if (!Buffer.from(value).equals(buffer)) throw Error('Git inventory path encoding unavailable.');
    const fields = value.split('\0');
    for (let i=0; i<fields.length && fields[i];) {
      const row = /^:([0-9]+) ([0-9]+) ([0-9a-f]+) ([0-9a-f]+) ([AMDRT][0-9]*)$/.exec(fields[i++]);
      if (!row) throw Error('Git inventory unavailable.');
      let path = fields[i++]; if (row[5][0] === 'R') path = fields[i++];
      snapshot.files.push({ path, status: row[5][0] === 'T' ? 'M' : row[5][0], mode: row[2] });
    }
  } catch (error) { snapshot.error = diagnostic(error); }
  return {snapshot};
}
const ownerIdentity = pid => {try {return readFileSync(`/proc/${pid}/stat`,'utf8').split(') ').at(-1).split(' ')[19];}catch{return '';}};
const ownerAlive = row => {try {process.kill(row.pid,0);return !row.identity || ownerIdentity(row.pid)===row.identity;}catch(error){return error.code!=='ESRCH';}};
async function ledgerDir(root) {const common=(await git(root,['rev-parse','--path-format=absolute','--git-common-dir'])).trim();const directory=join(realpathSync(common),'pdd','proof-worktrees');mkdirSync(directory,{recursive:true});return directory;}
async function recoverStale(root) {
 const directory=await ledgerDir(root), common=dirname(dirname(directory));
 for(const name of readdirSync(directory)) {if(!/^[0-9a-f]+\.json$/.test(name))continue;const path=join(directory,name);let row;try{if(!lstatSync(path).isFile())continue;row=JSON.parse(readFileSync(path,'utf8'));}catch{continue;}
  if(row.origin!=='pdd.proof-worktree.v1'||row.common!==common||!Number.isInteger(row.pid)||row.pid<=0||typeof row.worktree!=='string'||!isAbsolute(row.worktree)||ownerAlive(row))continue;
  // The ledger token and exact registered path establish ownership, never a directory-name prefix.
  const registered=(await git(root,['worktree','list','--porcelain','-z'])).split('\0').includes(`worktree ${row.worktree}`);
  if(registered)await git(root,['worktree','remove','--force',row.worktree]);
  else if(existsSync(row.worktree))continue;
  rmSync(path,{force:true});
 }
}
const ownedWorktrees=new Map();
async function createWorktree({root,commit,phase}) {
  let worktree = '';
  try { worktree = realpathSync(mkdtempSync(join(tmpdir(), `pdd-proof-${phase}-`))); const directory=await ledgerDir(root), path=join(directory,`${randomBytes(16).toString('hex')}.json`);writeFileSync(path,JSON.stringify({origin:'pdd.proof-worktree.v1',common:dirname(dirname(directory)),pid:process.pid,identity:ownerIdentity(process.pid),worktree}),{flag:'wx',mode:0o600});ownedWorktrees.set(worktree,path);await git(root,['worktree','add','--detach',worktree,commit]); return {worktree,error:''}; }
  catch(error) { return {worktree,error:diagnostic(error)}; }
}
function checkedParents(worktree, path) {
  if (lstatSync(worktree).isSymbolicLink() || !lstatSync(worktree).isDirectory()) throw Error('Unsafe worktree root.');
  const base = realpathSync(worktree), parts=path.split('/');parts.pop();let at=base;
  for (const part of parts) { at=join(at,part);try {mkdirSync(at);} catch(error) {if(error.code!=='EEXIST')throw error;} const stat=lstatSync(at);if(!stat.isDirectory()||stat.isSymbolicLink()||realpathSync(at)!==at)throw Error('Unsafe symlink ancestry.'); }
  return base;
}
async function overlay({root,headSha,worktree,paths}) {
  try {
    for (const path of paths) {
      if (!safePath(path)) throw Error('Unsafe overlay path.');
      const base=checkedParents(worktree,path), target=join(base,path);
      if (existsSync(target) && lstatSync(target).isSymbolicLink()) throw Error('Unsafe overlay symlink.');
      const entry = await git(root,['--literal-pathspecs','ls-tree','-z',headSha,'--',path]);
      const match=/^(100644|100755) blob ([0-9a-f]+)\t/.exec(entry); if(!match || entry.slice(match[0].length)!==`${path}\0`)throw Error('Committed regular blob unavailable.');
      const bytes=await git(root,['cat-file','blob',match[2]],null), temporary=join(dirname(target),`.pdd-proof-${randomBytes(8).toString('hex')}`);
      try { const fd=openSync(temporary,constants.O_WRONLY|constants.O_CREAT|constants.O_EXCL|constants.O_NOFOLLOW,match[1]==='100755'?0o755:0o644);try {writeFileSync(fd,bytes);fchmodSync(fd,match[1]==='100755'?0o755:0o644);} finally {closeSync(fd);}checkedParents(worktree,path);renameSync(temporary,target); }
      finally {rmSync(temporary,{force:true});}
    }
    return {error:''};
  } catch(error) {return {error:diagnostic(error)};}
}
function groupAlive(pid) {
  if (process.platform === 'linux') {
    try { return readdirSync('/proc').some(name => {if(!/^\d+$/.test(name))return false;try { const fields=readFileSync(`/proc/${name}/stat`,'utf8').split(') ').at(-1).split(' ');return fields[0]!=='Z' && Number(fields[2])===pid;}catch{return false;} }); } catch { /* Fall back to process group signal. */ }
  }
  try {process.kill(-pid,0);return true;} catch{return false;}
}
async function runProcess({command,cwd,timeoutMs,killGraceMs,outputLimitBytes}, abortSignal, expect = '') {
  const result={exitCode:null,signal:'',timedOut:false,outputLimited:false,expectedFound:false,stdout:'',stderr:'',error:'',setupError:''};
  return await new Promise(resolveResult => {
    let child, closed=false, exited=false, stopping=false, hardTimer, timer, interval;
    const perStream=Math.max(1024,Math.floor((outputLimitBytes||1048576)/2)), headLimit=Math.floor(perStream/2), tailLimit=perStream-headLimit;
    const makeStream=()=>({head:[],headBytes:0,tail:Buffer.alloc(0),overflowed:false,decoder:new StringDecoder('utf8'),carry:'',linePrefix:'',setupError:'',matched:false});
    const streams={stdout:makeStream(),stderr:makeStream()};
    const scanText=(s,piece)=>{if(!piece)return;if(expect&&!s.matched){const window=s.carry+piece;if(window.includes(expect))s.matched=true;s.carry=expect.length>1?window.slice(-(expect.length-1)):'';}if(!s.setupError){const segs=piece.replace(/\r\n/g,'\n').split('\n');if(s.linePrefix.length<256)s.linePrefix+=segs[0].slice(0,256-s.linePrefix.length);if(segs.length>1){s.setupError=setupDiagnostic(s.linePrefix)??'';for(let i=1;!s.setupError&&i<segs.length-1;i++)s.setupError=setupDiagnostic(segs[i].slice(0,256))??'';s.linePrefix=segs.at(-1).slice(0,256);}}};
    const joinStream=s=>{scanText(s,s.decoder.end());if(!s.setupError&&s.linePrefix)s.setupError=setupDiagnostic(s.linePrefix)??'';const headText=Buffer.concat(s.head).toString('utf8');if(!s.overflowed)return headText;const tailText=s.tail.toString('utf8');const headCut=headText.includes('\n')?headText.slice(0,headText.lastIndexOf('\n')):headText;const tailCut=tailText.includes('\n')?tailText.slice(tailText.indexOf('\n')+1):tailText;return headCut&&tailCut?`${headCut}\n${tailCut}`:headCut||tailCut;};
    const signalGroup=signal=>{try {process.kill(-child.pid,signal);}catch{}};
    const finish=()=>{if(!closed || child?.pid && groupAlive(child.pid))return;clearTimeout(timer);clearTimeout(hardTimer);clearInterval(interval);abortSignal?.removeEventListener('abort',stop);result.stdout=joinStream(streams.stdout);result.stderr=joinStream(streams.stderr);result.expectedFound=streams.stdout.matched||streams.stderr.matched;if(result.exitCode!==null && result.exitCode!==0)result.setupError=diagnostic(streams.stderr.setupError || streams.stdout.setupError || setupDiagnostic(result.stderr) || setupDiagnostic(result.stdout) || ([126,127].includes(result.exitCode)?`Command exited ${result.exitCode}.`:''));resolveResult({result});};
    const stop=()=>{if(stopping)return;stopping=true;signalGroup('SIGTERM');hardTimer=setTimeout(()=>{signalGroup('SIGKILL');},killGraceMs);};
    abortSignal?.addEventListener('abort',stop,{once:true});
    if(abortSignal?.aborted){closed=true;result.error='Parent interrupted before spawn.';finish();return;}
    const env = { ...process.env }; delete env.NODE_TEST_CONTEXT;
    try { child=spawn(command,{cwd,env,shell:true,detached:true,stdio:['ignore','pipe','pipe']}); }
    catch(error){result.error=diagnostic(error);result.setupError=result.error;closed=true;finish();return;}
    const capture=name=>chunk=>{const s=streams[name];scanText(s,s.decoder.write(chunk));let rest=chunk;if(s.headBytes<headLimit){const take=Math.min(headLimit-s.headBytes,rest.length);s.head.push(rest.subarray(0,take));s.headBytes+=take;rest=rest.subarray(take);}if(rest.length){s.overflowed=true;s.tail=rest.length>=tailLimit?Buffer.from(rest.subarray(rest.length-tailLimit)):Buffer.concat([s.tail.subarray(Math.max(0,s.tail.length+rest.length-tailLimit)),rest]);}};
    child.stdout.on('data',capture('stdout'));child.stderr.on('data',capture('stderr'));
    child.on('error',error=>{result.error=diagnostic(error);result.setupError=result.error;});
    child.on('exit',(code,signal)=>{exited=true;result.exitCode=code;result.signal=signal??'';});
    child.on('close',()=>{closed=true;finish();});
    timer=setTimeout(()=>{result.timedOut=true;stop();},timeoutMs);
    interval=setInterval(()=>{if(exited && groupAlive(child.pid))stop();finish();},20);
  });
}
async function cleanup({root,worktrees}) {
  const errors=[];
  for(const worktree of worktrees) {try {await git(root,['worktree','remove','--force',worktree]);} catch(error) {errors.push(diagnostic(error));} finally {try {rmSync(worktree,{recursive:true,force:true});const ledger=ownedWorktrees.get(worktree);if(ledger){rmSync(ledger,{force:true});ownedWorktrees.delete(worktree);}}catch(error){errors.push(diagnostic(error));}}}
  return {error:errors.join('; ')};
}
async function saveProof({runDir,record}) {
  const temporary=join(runDir,`.old-code-proof-${randomBytes(8).toString('hex')}.tmp`);
  try {writeFileSync(temporary,JSON.stringify(record,null,2)+'\n',{flag:'wx',mode:0o600});renameSync(temporary,join(runDir,'old-code-proof.json'));return {error:''};}
  catch(error){return {error:diagnostic(error)};} finally {rmSync(temporary,{force:true});}
}
const defaults={readRun,snapshot,createWorktree,overlay,runProcess,cleanup,saveProof};
// The per-phase limit: 10 minutes by default (a changed test file can take minutes); the person sets 1 to 120 minutes.
export const DEFAULT_PHASE_MINUTES=10;
export async function proveRun({ref,test,expect,cwd,timeoutMinutes=DEFAULT_PHASE_MINUTES},ports={}) {
  if(typeof test!=='string'||!test.trim()||typeof expect!=='string'||!expect.trim())return {exitCode:2,message:'pdd workflow prove requires nonblank --test and --expect.'};
  if(!Number.isInteger(timeoutMinutes)||timeoutMinutes<1||timeoutMinutes>120)return {exitCode:2,message:'pdd workflow prove --timeout takes whole minutes from 1 to 120.'};
  const p={...defaults,...ports};let run;
  const controller=new AbortController();let interruptSignal='';
  const handlers=new Map(['SIGINT','SIGTERM','SIGHUP'].map(signal=>[signal,()=>{if(!interruptSignal){interruptSignal=signal;controller.abort();}}]));
  for(const [signal,handler] of handlers)process.on(signal,handler);
  const interruptExit=()=>({SIGINT:130,SIGTERM:143,SIGHUP:129}[interruptSignal]);
  try {
    try {const result=await p.readRun({ref,cwd});if(result.error || !result.run)throw Error('Run unavailable.');run=result.run;}catch{return {exitCode:interruptExit()??1,message:'Old-code proof: ✗ setup-error (run unavailable).'};}
  const record={v:2,origin:'pdd.workflow-prove.v2',runId:run.runId,baseSha:'',headSha:'',test,expect,paths:[],base:emptyPhase(),head:emptyPhase(),outcome:'setup-error',cleanupError:'',setupError:'',interruptSignal:''}, worktrees=[];
    try {
      const {snapshot:s}=await p.snapshot({root:run.root,baseBranch:run.baseBranch});record.headSha=s.headSha;record.baseSha=s.baseSha;
      if(s.error || !s.baseAvailable || !s.headAvailable)throw Error(s.error || 'Committed snapshots unavailable.');
      record.paths=selectFiles(s.files);
      if(!interruptSignal) {
        for(const [phase,commit] of [['base',record.baseSha],['head',record.headSha]]) {if(interruptSignal)break;const created=await p.createWorktree({root:run.root,commit,phase});if(created.worktree)worktrees.push(created.worktree);if(created.error || !created.worktree)throw Error(created.error || 'Worktree unavailable.');}
        if(record.paths.length && !interruptSignal){const copied=await p.overlay({root:run.root,headSha:record.headSha,worktree:worktrees[0],paths:record.paths});if(copied.error)throw Error(copied.error);}
        for(const [index,phase] of ['base','head'].entries()) {
          if(interruptSignal)break;
          const suiteNow = ports.suiteNow ?? (() => performance.now()), suiteStarted = suiteNow();
          let response;try {const input={command:test,cwd:worktrees[index],timeoutMs:timeoutMinutes*60000,killGraceMs:2000,outputLimitBytes:1048576};response=await (ports.runProcess ? p.runProcess(input) : runProcess(input,controller.signal,expect));}catch(error){response={result:{exitCode:null,signal:'',timedOut:false,outputLimited:false,stdout:'',stderr:'',error:diagnostic(error),setupError:''}};}
          try { const measurement = { id: `prove-${randomUUID()}`, suiteMinutes: Math.max(0, suiteNow() - suiteStarted) / 60000 };
            await (ports.recordSuiteCost ?? (input => updateRun(run.runDir, latest => applyCostMeasurement(latest, input, Date.now()))))(measurement); } catch {}
          record[phase]=phaseRecord(response.result,expect);record.setupError ||= record[phase].error || record[phase].setupError;
        }
      }
    }catch(error){record.setupError ||= diagnostic(error);}
    finally {if(worktrees.length)try {record.cleanupError=diagnostic((await p.cleanup({root:run.root,worktrees})).error);}catch(error){record.cleanupError=diagnostic(error);}}
    record.interruptSignal=interruptSignal;record.outcome=classifyProof(record);
    try {if((await p.saveProof({runDir:run.runDir,record})).error)throw Error('Save failed.');}catch{return {exitCode:interruptExit()??1,message:'Old-code proof: ✗ setup-error (could not save result).'};}
    // A signal arriving while saving still owns the native exit; keep its durable fact current.
    if(record.interruptSignal!==interruptSignal){record.interruptSignal=interruptSignal;record.outcome=classifyProof(record);try{await p.saveProof({runDir:run.runDir,record});}catch{}}
    return {exitCode:interruptExit()??(record.outcome==='proved'?0:1),message:formatProof(record)};
  } finally {for(const [signal,handler] of handlers)process.removeListener(signal,handler);}
}

// --- Iterative affected-tests-first verification and final suite separation (#3065) ---

const ITERATIVE_MODES = new Set(['iterative', 'verify', 'affected']);
const FINAL_MODES = new Set(['final', 'merge', 'full']);
const DEFAULT_MAX_COMMAND_LENGTH = 65536;
const PROD_CODE_PATH_RE = /^(?:src|lib|app)\//i;
const shellQuote = value => (/^[A-Za-z0-9_@%+=:,./-]+$/.test(value) ? value : `'${String(value).replaceAll("'", `'\\''`)}'`);

function filePresent(root, relPath, ports = {}) {
  const norm = relPath.replaceAll('\\', '/');
  if (Array.isArray(ports.files)) return ports.files.some(f => String(f).replaceAll('\\', '/').replace(/^(?:\.\/)+/, '') === norm);
  if (typeof ports.readFile === 'function') return (ports.readFile(norm, root) ?? ports.readFile(norm.replaceAll('/', '\\'), root)) !== null;
  try {
    return lstatSync(join(root, norm)).isFile();
  } catch {
    return false;
  }
}

function detectFullTestCommand(root, ports = {}) {
  const readText = relPath => {
    if (typeof ports.readFile === 'function') return ports.readFile(relPath, root);
    try {
      return readFileSync(join(root, relPath), 'utf8');
    } catch {
      return null;
    }
  };
  let pkg = null;
  const rawPkg = readText('package.json');
  if (typeof rawPkg === 'string') {
    try {
      pkg = JSON.parse(rawPkg);
    } catch {
      pkg = null;
    }
  }
  if (filePresent(root, 'pnpm-lock.yaml', ports) && pkg?.scripts?.test) return 'pnpm test';
  if (filePresent(root, 'yarn.lock', ports) && pkg?.scripts?.test) return 'yarn test';
  if (pkg?.scripts?.test) return 'npm test';
  return `${shellQuote(ports.execPath ?? process.execPath)} --test`;
}

function buildAffectedNodeCommand({ root, selectedTests, concurrency, ports = {} }) {
  const args = [shellQuote(ports.execPath ?? process.execPath)];
  for (const preload of ['test/helpers/test-home.mjs', 'test/helpers/test-net-guard.mjs']) {
    if (filePresent(root, preload, ports)) args.push('--import', `./${preload}`);
  }
  const cpus = Number(concurrency ?? ports.env?.PDD_CHECK_CPUS ?? process.env.PDD_CHECK_CPUS);
  if (Number.isInteger(cpus) && cpus >= 1) args.push(`--test-concurrency=${cpus}`);
  args.push('--test', ...selectedTests.map(shellQuote));
  return args.join(' ');
}

export function resolveVerifyPlan(options = {}, ports = {}) {
  const root = options.root ?? process.cwd();
  const baseBranch = options.baseBranch ?? 'main';
  const requestedMode = options.mode ?? 'iterative';
  const isFinal = FINAL_MODES.has(requestedMode);
  const maxCommandLength = Number.isInteger(options.maxCommandLength) && options.maxCommandLength > 0
    ? options.maxCommandLength
    : DEFAULT_MAX_COMMAND_LENGTH;
  const fullCommand =
    typeof options.fullTestCommand === 'string' && options.fullTestCommand.trim()
      ? options.fullTestCommand.trim()
      : detectFullTestCommand(root, { ...ports, files: options.files });

  if (isFinal) {
    const inventory = selectAffectedTests(
      { root, files: options.files, changedFiles: [], smokeTests: [] },
      ports,
    );
    return {
      mode: 'final',
      executionMode: 'full',
      selectionMode: 'full',
      selectedTests: inventory.totalTests,
      totalTests: inventory.totalTests,
      selectedCount: inventory.totalCount,
      totalCount: inventory.totalCount,
      changedFiles: Array.isArray(options.changedFiles) ? [...options.changedFiles] : [],
      smokeTests: [],
      fallbackReason: null,
      fallbackCategory: null,
      reasons: {},
      command: fullCommand,
      summary: `Full test suite (before merge): running all ${inventory.totalCount} of ${inventory.totalCount} test files.`,
    };
  }

  const selection = selectAffectedTests(
    {
      root,
      baseRef: options.baseRef ?? `origin/${baseBranch}`,
      changedFiles: options.changedFiles,
      files: options.files,
      smokeTests: options.smokeTests,
      coreInfrastructure: options.coreInfrastructure,
      dispatcherImportThreshold: options.dispatcherImportThreshold,
    },
    ports,
  );

  if (selection.mode === 'full') {
    return {
      ...selection,
      mode: 'iterative',
      executionMode: 'full',
      selectionMode: 'full',
      command: fullCommand,
    };
  }

  if (selection.selectedCount === 0) {
    const touchedProdCode = selection.changedFiles.find(f => PROD_CODE_PATH_RE.test(f));
    if (touchedProdCode) {
      const fallbackReason = `no isolated test mapping for changed code (${touchedProdCode})`;
      const fullPlan = {
        ...selection,
        mode: 'full',
        selectedTests: [...selection.totalTests],
        selectedCount: selection.totalCount,
        fallbackReason,
        fallbackCategory: 'unmapped-code-change',
      };
      return {
        ...fullPlan,
        mode: 'iterative',
        executionMode: 'full',
        selectionMode: 'full',
        summary: formatAffectedTestsSummary(fullPlan),
        command: fullCommand,
      };
    }
    return {
      ...selection,
      mode: 'iterative',
      executionMode: 'skip',
      selectionMode: 'affected',
      command: '',
    };
  }

  const affectedCommand = buildAffectedNodeCommand({
    root,
    selectedTests: selection.selectedTests,
    concurrency: options.concurrency,
    ports: { ...ports, files: options.files },
  });
  if (affectedCommand.length > maxCommandLength) {
    const fallbackReason = `affected command length (${affectedCommand.length} chars) exceeds ${maxCommandLength}-char command limit`;
    const fullPlan = {
      ...selection,
      mode: 'full',
      selectedTests: [...selection.totalTests],
      selectedCount: selection.totalCount,
      fallbackReason,
      fallbackCategory: 'command-length-limit',
    };
    return {
      ...fullPlan,
      mode: 'iterative',
      executionMode: 'full',
      selectionMode: 'full',
      summary: formatAffectedTestsSummary(fullPlan),
      command: fullCommand,
    };
  }

  return {
    ...selection,
    mode: 'iterative',
    executionMode: 'affected',
    selectionMode: 'affected',
    command: affectedCommand,
  };
}

async function saveAffectedVerify({ runDir, record }) {
  const temporary = join(runDir, `.affected-verify-${randomBytes(8).toString('hex')}.tmp`);
  try {
    writeFileSync(temporary, JSON.stringify(record, null, 2) + '\n', { flag: 'wx', mode: 0o600 });
    renameSync(temporary, join(runDir, 'affected-verify.json'));
    return { error: '' };
  } catch (error) {
    return { error: diagnostic(error) };
  } finally {
    rmSync(temporary, { force: true });
  }
}

export async function verifyAffected(options = {}, ports = {}) {
  const timeoutMinutes = options.timeoutMinutes ?? DEFAULT_PHASE_MINUTES;
  if (!Number.isInteger(timeoutMinutes) || timeoutMinutes < 1 || timeoutMinutes > 120) {
    return { exitCode: 2, message: 'pdd workflow prove --timeout takes whole minutes from 1 to 120.' };
  }
  const requestedMode = options.mode ?? 'iterative';
  if (!ITERATIVE_MODES.has(requestedMode) && !FINAL_MODES.has(requestedMode)) {
    return { exitCode: 2, message: `Unknown verify mode: ${String(requestedMode)}.` };
  }

  const p = { ...defaults, saveAffectedVerify, ...ports };
  let run = null;
  if (options.ref !== undefined && options.ref !== null && String(options.ref).trim()) {
    try {
      const resolved = await p.readRun({ ref: String(options.ref), cwd: options.cwd ?? options.root ?? process.cwd() });
      if (resolved.error || !resolved.run) throw Error('Run unavailable.');
      run = resolved.run;
    } catch {
      return { exitCode: 1, message: 'Affected tests: ✗ setup-error (run unavailable).' };
    }
  }

  const root = options.root ?? run?.root ?? options.cwd ?? process.cwd();
  const baseBranch = options.baseBranch ?? run?.baseBranch ?? 'main';
  const plan = resolveVerifyPlan({ ...options, root, baseBranch, mode: requestedMode }, ports);

  const persistRecord = async (extra = {}) => {
    if (!run?.runDir) return;
    try {
      await p.saveAffectedVerify({
        runDir: run.runDir,
        record: {
          v: 1,
          origin: 'pdd.workflow-verify-affected.v1',
          runId: run.runId,
          mode: plan.mode,
          executionMode: plan.executionMode,
          selectionMode: plan.selectionMode,
          selectedCount: plan.selectedCount,
          totalCount: plan.totalCount,
          selectedTests: plan.selectedTests,
          changedFiles: plan.changedFiles,
          fallbackReason: plan.fallbackReason,
          fallbackCategory: plan.fallbackCategory,
          command: plan.command,
          summary: plan.summary,
          ...extra,
        },
      });
    } catch {
      // Verification result still returns to caller if optional run-folder persistence fails.
    }
  };

  if (plan.executionMode === 'skip') {
    await persistRecord({ executed: false, exitCode: 0, durationMs: 0, observedError: '' });
    return {
      exitCode: 0,
      mode: plan.selectionMode,
      executionMode: 'skip',
      executed: false,
      selectedTests: [],
      totalTests: plan.totalTests,
      selectedCount: 0,
      totalCount: plan.totalCount,
      fallbackReason: null,
      fallbackCategory: null,
      command: '',
      durationMs: 0,
      summary: plan.summary,
      message: `${plan.summary} Skipped execution (0 affected test files).`,
    };
  }

  const controller = new AbortController();
  let interruptSignal = '';
  const handlers = new Map(
    ['SIGINT', 'SIGTERM', 'SIGHUP'].map(signal => [
      signal,
      () => {
        if (!interruptSignal) {
          interruptSignal = signal;
          controller.abort();
        }
      },
    ]),
  );
  for (const [signal, handler] of handlers) process.on(signal, handler);
  const interruptExit = () => ({ SIGINT: 130, SIGTERM: 143, SIGHUP: 129 }[interruptSignal]);

  try {
    const suiteNow = ports.suiteNow ?? (() => performance.now());
    const started = suiteNow();
    let response;
    try {
      const input = {
        command: plan.command,
        cwd: root,
        timeoutMs: timeoutMinutes * 60000,
        killGraceMs: 2000,
        outputLimitBytes: 1048576,
      };
      response = await (ports.runProcess ? p.runProcess(input) : runProcess(input, controller.signal, ''));
    } catch (error) {
      response = {
        result: {
          exitCode: null,
          signal: '',
          timedOut: false,
          outputLimited: false,
          stdout: '',
          stderr: '',
          error: diagnostic(error),
          setupError: '',
        },
      };
    }
    const durationMs = Math.max(0, suiteNow() - started);
    if (run?.runDir) {
      try {
        const measurement = { id: `verify-${randomUUID()}`, suiteMinutes: durationMs / 60000 };
        await (ports.recordSuiteCost ?? (input => updateRun(run.runDir, latest => applyCostMeasurement(latest, input, Date.now()))))(measurement);
      } catch {}
    }

    const phase = phaseRecord(response.result, '');
    const passed =
      !interruptSignal &&
      !phase.error &&
      !phase.setupError &&
      !phase.timedOut &&
      !phase.outputLimited &&
      !phase.signal &&
      phase.exitCode === 0;
    const exitCode = interruptExit() ?? (passed ? 0 : 1);
    const label = plan.mode === 'final' ? 'Full test suite (before merge)' : 'Affected tests';
    const countDetail =
      plan.mode === 'final'
        ? `${plan.totalCount} of ${plan.totalCount} test files`
        : plan.selectionMode === 'full'
          ? `${plan.totalCount} of ${plan.totalCount} test files; fallback: ${plan.fallbackReason}`
          : `${plan.selectedCount} of ${plan.totalCount} test files`;

    let message;
    if (passed) {
      const preview =
        plan.selectionMode === 'affected' && plan.selectedTests.length <= 5
          ? `: ${plan.selectedTests.join(', ')}`
          : '';
      message = `${label}: ✓ passed (${countDetail}${preview}).`;
    } else {
      const cause = interruptSignal
        ? `parent ${interruptSignal}`
        : phase.setupError || phase.error || (phase.timedOut ? 'timed out' : phase.observedError || 'failed');
      const tail = actualTail({ outcome: 'head-fails', base: emptyPhase(), head: phase });
      message = `${label}: ✗ failed (${countDetail}); command ${safeValue(plan.command, true)}; exit ${safeValue(phase.exitCode ?? 'none')}; cause ${safeValue(cause)}${tail ? `; tail ${safeValue(tail)}` : ''}.`;
    }

    await persistRecord({
      executed: true,
      exitCode,
      durationMs,
      interruptSignal,
      observedError: passed ? '' : phase.observedError,
    });

    return {
      exitCode,
      mode: plan.selectionMode,
      executionMode: plan.executionMode,
      executed: true,
      selectedTests: plan.selectedTests,
      totalTests: plan.totalTests,
      selectedCount: plan.selectedCount,
      totalCount: plan.totalCount,
      fallbackReason: plan.fallbackReason,
      fallbackCategory: plan.fallbackCategory,
      command: plan.command,
      durationMs,
      summary: plan.summary,
      message,
    };
  } finally {
    for (const [signal, handler] of handlers) process.removeListener(signal, handler);
  }
}

export async function proveAffectedRun(
  {
    ref,
    expect,
    cwd,
    test,
    files,
    baseRef,
    fullTestCommand,
    smokeTests = [],
    coreInfrastructure,
    dispatcherImportThreshold,
    maxCommandLength,
    concurrency,
    timeoutMinutes = DEFAULT_PHASE_MINUTES,
  } = {},
  ports = {},
) {
  if (typeof test === 'string' && test.trim() && test.trim() !== 'auto') {
    return proveRun({ ref, test, expect, cwd, timeoutMinutes }, ports);
  }
  if (typeof expect !== 'string' || !expect.trim()) {
    return { exitCode: 2, message: 'pdd workflow prove requires nonblank --test and --expect.' };
  }
  if (!Number.isInteger(timeoutMinutes) || timeoutMinutes < 1 || timeoutMinutes > 120) {
    return { exitCode: 2, message: 'pdd workflow prove --timeout takes whole minutes from 1 to 120.' };
  }

  const p = { ...defaults, ...ports };
  let runRes;
  try {
    runRes = await p.readRun({ ref, cwd });
    if (runRes.error || !runRes.run) throw Error('Run unavailable.');
  } catch {
    return { exitCode: 1, message: 'Old-code proof: ✗ setup-error (run unavailable).' };
  }

  const fallbackFullCmd =
    typeof fullTestCommand === 'string' && fullTestCommand.trim()
      ? fullTestCommand.trim()
      : detectFullTestCommand(runRes.run.root, { ...ports, files });

  let snapRes;
  try {
    snapRes = await p.snapshot({ root: runRes.run.root, baseBranch: runRes.run.baseBranch });
    if (snapRes.snapshot?.error || !snapRes.snapshot?.baseAvailable || !snapRes.snapshot?.headAvailable) {
      return proveRun({ ref, test: fallbackFullCmd, expect, cwd, timeoutMinutes }, { ...ports, readRun: async () => runRes, snapshot: async () => snapRes });
    }
  } catch (error) {
    return proveRun({ ref, test: fallbackFullCmd, expect, cwd, timeoutMinutes }, { ...ports, readRun: async () => runRes, snapshot: async () => { throw error; } });
  }

  const changedFiles = snapRes.snapshot.files.map(f => f.path);
  const plan = resolveVerifyPlan(
    {
      root: runRes.run.root,
      baseBranch: runRes.run.baseBranch,
      baseRef,
      files,
      fullTestCommand,
      changedFiles,
      smokeTests,
      coreInfrastructure,
      dispatcherImportThreshold,
      maxCommandLength,
      concurrency,
      mode: 'iterative',
    },
    ports,
  );

  let effectiveSelection;
  let resolvedCommand;
  if (plan.executionMode === 'skip') {
    const fallbackReason = '0 affected test files matched; running full suite for old-code proof';
    const fullPlan = {
      mode: 'full',
      selectedTests: [...plan.totalTests],
      totalTests: plan.totalTests,
      selectedCount: plan.totalCount,
      totalCount: plan.totalCount,
      fallbackReason,
      fallbackCategory: 'prove-requires-execution',
    };
    effectiveSelection = {
      mode: 'full',
      executionMode: 'full',
      selectedCount: plan.totalCount,
      totalCount: plan.totalCount,
      selectedTests: [...plan.totalTests],
      fallbackReason,
      fallbackCategory: 'prove-requires-execution',
      summary: formatAffectedTestsSummary(fullPlan),
    };
    resolvedCommand = fallbackFullCmd;
  } else {
    effectiveSelection = {
      mode: plan.selectionMode,
      executionMode: plan.executionMode,
      selectedCount: plan.selectedCount,
      totalCount: plan.totalCount,
      selectedTests: plan.selectedTests,
      fallbackReason: plan.fallbackReason,
      fallbackCategory: plan.fallbackCategory,
      summary: plan.summary,
    };
    resolvedCommand = plan.command;
  }

  const proof = await proveRun(
    { ref, test: resolvedCommand, expect, cwd, timeoutMinutes },
    { ...ports, readRun: async () => runRes, snapshot: async () => snapRes },
  );
  return {
    ...proof,
    selection: effectiveSelection,
    message: `${proof.message} (${effectiveSelection.summary})`,
  };
}
