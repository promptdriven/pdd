// Generated from prompts/cli/workflow-prove.prompt.md (sha256: 4cdd79111e2c52146c7f9b9df8d719c8e4ed69c225a27832a993e51da9394503).
import { execFile as execFileCallback, spawn } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { constants, fchmodSync, closeSync, existsSync, lstatSync, mkdirSync, mkdtempSync, openSync, readFileSync, readdirSync, realpathSync, renameSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, isAbsolute, join } from 'node:path';
import { promisify } from 'node:util';
import { resolveRun } from './workflow-runs.mjs';

const execFile = promisify(execFileCallback);
const diagnostic = error => String(error?.message ?? error ?? '').split(/[\r\n]/)[0].replace(/[\x00-\x1f\x7f]/g, ' ').slice(0, 1000);
const emptyPhase = () => ({ exitCode: null, signal: '', timedOut: false, outputLimited: false, stdoutTail: [], stderrTail: [], expectedFound: false, error: '', setupError: '', observedError: '' });
const lines = value => { const parts = value.replace(/\r\n/g, '\n').split('\n'); if (parts.at(-1) === '') parts.pop(); return parts; };
const setupDiagnostic = value => lines(value).find(line => /^(?:# )?(?:Error: Cannot find module|Error \[ERR_MODULE_NOT_FOUND\]|ModuleNotFoundError:|ImportError:|FileNotFoundError:|Error: ENOENT|ENOENT:)/.test(line));
function observedError(stdout, stderr) {
  const err = lines(stderr), out = lines(stdout), all = [...err, ...out];
  const found = all.find(s => /^\s*(?:# )?\s*code:/.test(s)) ?? all.find(s => s.trim() && /error|code|assert|exception/i.test(s)) ?? err.find(s => s.trim()) ?? out.find(s => s.trim()) ?? 'no output';
  return [...found.trim()].slice(0, 240).join('');
}
function phaseRecord(result, expect) {
  return { exitCode: result.exitCode, signal: result.signal, timedOut: result.timedOut, outputLimited: result.outputLimited,
    stdoutTail: lines(result.stdout).slice(-20), stderrTail: lines(result.stderr).slice(-20), expectedFound: result.stdout.includes(expect) || result.stderr.includes(expect), error: diagnostic(result.error), setupError: diagnostic(result.setupError), observedError: observedError(result.stdout, result.stderr) };
}
export function classifyProof(record) {
  if (record.setupError || record.cleanupError || record.base.error || record.head.error || record.base.setupError || record.head.setupError || [126,127].includes(record.base.exitCode) || [126,127].includes(record.head.exitCode)) return 'setup-error';
  if (record.interruptSignal) return 'signalled';
  if (!record.paths.length) return 'no-changed-tests';
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
  else {const phase=record.outcome==='head-timeout' || record.outcome==='output-limit' && !record.base.outputLimited || record.outcome==='signalled' && !record.base.signal ? record.head : record.base;cause=phase.exitCode!==null || phase.signal || phase.timedOut || phase.outputLimited ? phase.observedError : record.outcome;}
  const tail=['head-fails','setup-error'].includes(record.outcome)?actualTail(record):'';
  return `Old-code proof: ✗ ${record.outcome}; command ${command}; old-code exit ${base}; new-code exit ${head}; expected ${expected}; cause ${safeValue(cause)}${tail?`; tail ${safeValue(tail)}`:''}.`;
}
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const exactKeys = (value, keys) => object(value) && Object.keys(value).length === keys.length && keys.every(key => Object.hasOwn(value, key));
const phaseKeys = Object.keys(emptyPhase());
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
    if (phase.exitCode === null && !phase.signal && !phase.timedOut && !phase.outputLimited && !phase.error && !phase.setupError) {
      if (phase.expectedFound || phase.stdoutTail.length || phase.stderrTail.length || phase.observedError) return false;
    }
  }
  if (record.outcome !== classifyProof(record)) return false;
  if (!record.interruptSignal && !['setup-error','no-changed-tests'].includes(record.outcome) && (record.base.exitCode === null && !record.base.signal && !record.base.timedOut && !record.base.outputLimited || record.head.exitCode === null && !record.head.signal && !record.head.timedOut && !record.head.outputLimited)) return false;
  if (record.outcome === 'no-changed-tests' && [record.base, record.head].some(phase => phaseKeys.some(key => JSON.stringify(phase[key]) !== JSON.stringify(emptyPhase()[key])))) return false;
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
async function runProcess({command,cwd,timeoutMs,killGraceMs,outputLimitBytes}, abortSignal) {
  const result={exitCode:null,signal:'',timedOut:false,outputLimited:false,stdout:'',stderr:'',error:'',setupError:''};
  return await new Promise(resolveResult => {
    let child, bytes=0, closed=false, exited=false, stopping=false, hardTimer, timer, interval;
    const buffers={stdout:[],stderr:[]};
    const signalGroup=signal=>{try {process.kill(-child.pid,signal);}catch{}};
    const finish=()=>{if(!closed || child?.pid && groupAlive(child.pid))return;clearTimeout(timer);clearTimeout(hardTimer);clearInterval(interval);abortSignal?.removeEventListener('abort',stop);result.stdout=Buffer.concat(buffers.stdout).toString('utf8');result.stderr=Buffer.concat(buffers.stderr).toString('utf8');if(result.exitCode!==null && result.exitCode!==0)result.setupError=diagnostic(setupDiagnostic(result.stderr) ?? setupDiagnostic(result.stdout) ?? ([126,127].includes(result.exitCode)?`Command exited ${result.exitCode}.`:''));resolveResult({result});};
    const stop=()=>{if(stopping)return;stopping=true;signalGroup('SIGTERM');hardTimer=setTimeout(()=>{signalGroup('SIGKILL');},killGraceMs);};
    abortSignal?.addEventListener('abort',stop,{once:true});
    if(abortSignal?.aborted){closed=true;result.error='Parent interrupted before spawn.';finish();return;}
    const env = { ...process.env }; delete env.NODE_TEST_CONTEXT;
    try { child=spawn(command,{cwd,env,shell:true,detached:true,stdio:['ignore','pipe','pipe']}); }
    catch(error){result.error=diagnostic(error);result.setupError=result.error;closed=true;finish();return;}
    const capture=stream=>chunk=>{const room=Math.max(0,outputLimitBytes-bytes);if(room)buffers[stream].push(chunk.subarray(0,room));bytes+=chunk.length;if(bytes>outputLimitBytes){result.outputLimited=true;stop();}};
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
export async function proveRun({ref,test,expect,cwd},ports={}) {
  if(typeof test!=='string'||!test.trim()||typeof expect!=='string'||!expect.trim())return {exitCode:2,message:'pdd workflow prove requires nonblank --test and --expect.'};
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
      if(record.paths.length && !interruptSignal) {
        for(const [phase,commit] of [['base',record.baseSha],['head',record.headSha]]) {if(interruptSignal)break;const created=await p.createWorktree({root:run.root,commit,phase});if(created.worktree)worktrees.push(created.worktree);if(created.error || !created.worktree)throw Error(created.error || 'Worktree unavailable.');}
        if(!interruptSignal){const copied=await p.overlay({root:run.root,headSha:record.headSha,worktree:worktrees[0],paths:record.paths});if(copied.error)throw Error(copied.error);}
        for(const [index,phase] of ['base','head'].entries()) {
          if(interruptSignal)break;
          let response;try {const input={command:test,cwd:worktrees[index],timeoutMs:120000,killGraceMs:2000,outputLimitBytes:1048576};response=await (ports.runProcess ? p.runProcess(input) : runProcess(input,controller.signal));}catch(error){response={result:{exitCode:null,signal:'',timedOut:false,outputLimited:false,stdout:'',stderr:'',error:diagnostic(error),setupError:''}};}
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
