// Generated from prompts/cli/workflow-replay.prompt.md (sha256: 2406d5e5c3ef58e2a72556bf004023281a675767b309d5dec15efd246af42a98).
import { execFileSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { createHash } from 'node:crypto';
import { closeSync, constants, fstatSync, lstatSync, openSync, readFileSync, readlinkSync, readSync, mkdirSync, mkdtempSync, rmSync, writeFileSync, realpathSync, symlinkSync } from 'node:fs';
import { dirname, isAbsolute, join, relative, resolve, sep, basename } from 'node:path';
import { gitFiles } from './runtime-preflight.mjs';
import { cleanText } from './runtime-output.mjs';
export const REPLAY_POLICY = 'pdd.replay-evidence.v1';
const LIMIT = 2 * 1024 * 1024, MAX = 10000;
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const object = v => v !== null && typeof v === 'object' && !Array.isArray(v);
const text = v => typeof v === 'string' && v.trim().length > 0 && v.length <= 1000;
const parse = bytes => JSON.parse(new TextDecoder('utf-8',{fatal:true}).decode(bytes));
const sha = v => typeof v === 'string' && /^[a-f0-9]{64}$/.test(v);
const integer = v => Number.isSafeInteger(v) && v >= 0;
const exit = v => integer(v) && v <= 255;
const requireThat = (condition, message) => { if (!condition) throw Error(message); };
const key = row => JSON.stringify([row.vector, row.step_id, row.check_index]);
const stepKey = row => JSON.stringify([row.vector, row.step_id]);
const identity = ['entry_path','operation','criterion_id','target','path','op'];
const states = ['pass','fail','blocked','not_replayed'];
const controls = ['assertion_failure','crash','survived','not_run'];
const sanitize = value => cleanText(String(value ?? '')).replace(/[\r\n\x00-\x1f]/g,' ').slice(0,1000)
  .replace(/https?:\/\/[^\s]+\/s\/[^\s]+/g,'(Try link removed)');
const adoptionCause = value => sanitize(value).replace(/\b(?:Bearer|Basic)\s+[^\s]+/gi,'credential removed').replace(/\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+)\b/g,'credential removed').replace(/https?:\/\/[^\s]+/g,'(URL removed)').replace(/(?<![\w./-])(?:[A-Za-z]:[\\/]|\/)[^\s,;:]+/g,'(path removed)').replace(/(?:token|password|authorization|credential)[=: ]+[^\s]+/gi,'credential removed');
const render = value => sanitize(value).replace(/[\\`*_[\]()|]/g,'\\$&')
  .replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');

export function sourceFingerprint(root) {
  try {
    const files = gitFiles(root).sort().map(path => {
      const full = join(root, path);
      let stat; try { stat = lstatSync(full); } catch (error) { if (error.code === 'ENOENT') return [path, 'missing']; throw error; }
      if (stat.isSymbolicLink()) return [path, 'link', readlinkSync(full)];
      if (!stat.isFile()) throw Error('Not a regular source file');
      return [path, stat.mode & 0o111, hash(readFileSync(full))];
    });
    return hash(JSON.stringify(files));
  } catch { return null; }
}
function boundedFile(path, max = LIMIT, allowEmpty = false) {
  for (let parent = dirname(path); ; parent = dirname(parent)) {
    requireThat(!lstatSync(parent).isSymbolicLink(), 'Evidence paths cannot traverse symbolic links.');
    if (dirname(parent) === parent) break;
  }
  const fd = openSync(path, constants.O_RDONLY | constants.O_NOFOLLOW | constants.O_NONBLOCK);
  try {
    const stat = fstatSync(fd);
    requireThat(stat.isFile() && stat.nlink === 1, 'Evidence must be a regular single-link file.');
    requireThat((allowEmpty || stat.size > 0) && stat.size <= max, 'Evidence is empty or exceeds its byte limit.');
    const bytes = Buffer.alloc(Math.min(max + 1, stat.size + 1));
    let size = 0, read;
    while (size < bytes.length && (read = readSync(fd,bytes,size,bytes.length-size,null))) size += read;
    requireThat(size === stat.size && fstatSync(fd).size === size, 'Evidence changed while being read.');
    return bytes.subarray(0,size);
  } finally { closeSync(fd); }
}
function vectorFile(root, path, visible) {
  requireThat(text(path) && !isAbsolute(path) && !path.includes('\\') && !path.split('/').some(p => !p || p === '.' || p === '..'), 'Vector paths must be canonical repository-relative paths.');
  const rel = relative(root,resolve(root,path));
  requireThat(rel && !rel.startsWith('..') && !rel.startsWith(sep) && visible.has(path), 'An original vector is not Git-visible in this repository.');
  return boundedFile(join(root,path));
}
function scenario(path, bytes) {
  const doc = parse(bytes);
  requireThat(object(doc) && doc.schema_version === 'prompt-runtime.program-scenario.v1' && Array.isArray(doc.steps) && doc.steps.length > 0 && doc.steps.length <= MAX, 'Original vectors need nonempty versioned scenario steps.');
  const seen = new Set(), steps = [], checks = [];
  for (const step of doc.steps) {
    requireThat(object(step) && text(step.step_id) && !seen.has(step.step_id) && text(step.entry_path) && text(step.operation), 'Original step identities must be complete and unique.');
    seen.add(step.step_id);
    requireThat(Array.isArray(step.checks) && step.checks.length > 0 && step.checks.length <= MAX, 'Every original step needs assertion checks.');
    const base = {vector:path,step_id:step.step_id,entry_path:step.entry_path,operation:step.operation}; steps.push(base);
    step.checks.forEach((check,check_index) => {
      requireThat(object(check) && text(check.criterion_id) && ['result','error','world','calls'].includes(check.target) && typeof check.path === 'string' && check.path.length <= 1000 && text(check.op), 'Original assertion identities are incomplete or unsupported.');
      checks.push({...base,check_index,criterion_id:check.criterion_id,target:check.target,path:check.path,op:check.op});
    });
  }
  return {path,sha256:hash(bytes),steps,checks};
}
export function pinReplayVectors(root, paths) {
  const anchor = {schema_version:'pdd.replay-vectors.v1',vectors:[]};
  try {
    requireThat(Array.isArray(paths) && paths.length <= 200 && new Set(paths).size === paths.length, 'Original vector selection is invalid or too large.');
    if (!paths.length) return {...anchor,outcome:'not_replayed',reason:'The approved prompt area has no original scenario vectors.'};
    const visible = new Set(gitFiles(root)); let bytes = 0, count = 0, steps = 0;
    for (const path of paths) {
      const raw = vectorFile(root,path,visible); bytes += raw.length;
      requireThat(bytes <= 10*1024*1024, 'Original vectors exceed 10 MiB.');
      const vector = scenario(path,raw);count += vector.checks.length;steps += vector.steps.length;
      requireThat(count <= MAX && steps <= MAX, 'Original vectors exceed the step/check limit.');anchor.vectors.push(vector);
    }
    return anchor;
  } catch (e) { return {...anchor,outcome:'blocked',reason:sanitize(e.message)}; }
}
const canonicalPath = value => text(value) && !isAbsolute(value) && !value.includes('\\') && !value.includes('\0') && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');
const commitId = value => typeof value === 'string' && /^(?:[a-f0-9]{40}|[a-f0-9]{64})$/.test(value);
const repositoryId = value => typeof value === 'string' && /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(value);
function declarationCause(d) {
  if (!object(d)) return 'Declaration must be an object.';
  for (const name of ['prompts','scenarios']) {
    if (!Object.hasOwn(d,name)) return `${name}: missing key.`;
    const paths=d[name];
    if (!Array.isArray(paths) || !paths.length) return `${name}: expected a nonempty path list.`;
    if (paths.length>200) return `${name}: ${paths.length} paths, limit 200.`;
    const seen=new Set();
    for (const path of paths) {
      if (!canonicalPath(path)) return `${name}: noncanonical path ${typeof path==='string'?path:'(invalid path)'}.`;
      if (seen.has(path)) return `${name}: duplicate path ${path}.`;
      seen.add(path);
    }
  }
  return '';
}
function validDeclaration(d) {
  const keys=(value,names)=>object(value)&&Object.keys(value).sort().join(',')===names.sort().join(',');
  return keys(d,['schema_version','repository','commit','prompts','scenarios','approval']) && d.schema_version === 'pdd.replay-adoption.v1' && repositoryId(d.repository) && commitId(d.commit) &&
    Array.isArray(d.prompts) && d.prompts.length > 0 && d.prompts.length <= 200 && d.prompts.every(canonicalPath) && new Set(d.prompts).size === d.prompts.length &&
    Array.isArray(d.scenarios) && d.scenarios.length > 0 && d.scenarios.length <= 200 && d.scenarios.every(canonicalPath) && new Set(d.scenarios).size === d.scenarios.length &&
    keys(d.approval,['kind','reference','asserted_by']) && d.approval.kind === 'external-human-assertion' && text(d.approval.reference) && text(d.approval.asserted_by);
}
function gitEnvironment() {
  const env=Object.fromEntries(Object.entries(process.env).filter(([key])=>!key.startsWith('GIT_')));
  return {...env,GIT_CONFIG_NOSYSTEM:'1',GIT_CONFIG_GLOBAL:'/dev/null'};
}
function localGit(root, ...args) {
  return execFileSync('git', args, {cwd:root,env:gitEnvironment(),maxBuffer:128*1024*1024,stdio:['ignore','pipe','pipe']});
}
function repository(root) {
  const remote = localGit(root,'remote','get-url','origin').toString().trim();
  const match = /^(?:https:\/\/github\.com\/|git@github\.com:|ssh:\/\/git@github\.com\/)([^/]+\/[^/]+?)(?:\.git)?\/?$/.exec(remote);
  requireThat(match && repositoryId(match[1]), 'The repository needs a canonical GitHub origin.');
  return match[1];
}
// Read requested immutable blobs in one Git process per selection round.
function batchBlobs(root, rows) {
  if (!rows.length) return new Map();
  const output=execFileSync('git',['cat-file','--batch'],{cwd:root,env:gitEnvironment(),input:rows.map(r=>r.oid).join('\n')+'\n',maxBuffer:128*1024*1024,stdio:['pipe','pipe','pipe']});
  let offset=0;const result=new Map();
  for(const row of rows) {
    const end=output.indexOf(10,offset), header=output.subarray(offset,end).toString();
    const match=/^([a-f0-9]+) blob (\d+)$/.exec(header);
    requireThat(match && match[1]===row.oid,'Selected blob is unavailable.');
    const size=Number(match[2]);requireThat(size<=10*1024*1024,'Selected blob exceeds the source limit.');
    offset=end+1;requireThat(offset+size<output.length,'Incomplete Git blob response.');
    result.set(row.path,output.subarray(offset,offset+size));offset+=size+1;
  }
  return result;
}
// Build a disposable local view from exact tracked blobs or bounded current files.
// No worktree, index, branch, run, or claim in the source repository is changed.
function adoptionView(root, ref, scenarios, source) {
  const temp = realpathSync(mkdtempSync(join(tmpdir(),'pdd-adoption-')));
  try {
    const rows = ref ? localGit(root,'ls-tree','-r','-z','--full-tree',ref).toString('utf8').split('\0').filter(Boolean).map(row => {
      const match = /^(\d+) (blob|commit) ([a-f0-9]+)\t([\s\S]+)$/.exec(row);
      requireThat(match, 'Invalid Git tree inventory.'); return {mode:match[1],oid:match[3],path:match[4]};
    }) : [...new Set(localGit(root,'ls-files','-z','-co','--exclude-standard').toString('utf8').split('\0').filter(Boolean))].map(path=>({path}));
    // Validate the complete tree before creating any source-controlled path.
    const names = new Set(), sources=new Map(), loaded=new Set();
    for (const row of rows) {
      requireThat(canonicalPath(row.path) && !names.has(row.path), `Invalid or duplicate source path: ${row.path}.`);
      names.add(row.path);sources.set(row.path,row);
    }
    const links=ref ? batchBlobs(root,rows.filter(row=>row.mode==='120000')) : new Map();
    for (const row of rows) {
      const full=join(temp,row.path);mkdirSync(dirname(full),{recursive:true});
      if(ref && row.mode==='160000') {mkdirSync(full);continue;}
      let link;
      if(ref && row.mode==='120000')link=links.get(row.path).toString();
      if(!ref) {
        let stat;try{stat=lstatSync(join(root,row.path));}catch(error){if(error.code!=='ENOENT')throw error;}
        if(stat?.isDirectory()){mkdirSync(full);continue;}
        if(stat?.isSymbolicLink())link=readlinkSync(join(root,row.path));
      }
      if(link!==undefined)symlinkSync(link,full);else writeFileSync(full,'');
    }
    const loadMany=paths=>{
      const pending=[...new Set(paths)].filter(path=>!loaded.has(path));
      for(const path of pending) {
        requireThat(sources.has(path),`${source} source is missing ${path}.`);
        requireThat(lstatSync(join(temp,path)).isFile(),'Selected source must be regular.');
      }
      const blobs=ref ? batchBlobs(root,pending.map(path=>sources.get(path))) : null;
      for(const path of pending) {
        let bytes;
        try {bytes=ref ? blobs.get(path) : boundedFile(join(root,path),10*1024*1024,true);}
        catch(error) {if(error.code==='ENOENT')throw Error(`${source} source is missing ${path}.`);throw error;}
        writeFileSync(join(temp,path),bytes);loaded.add(path);
      }
      return pending.length>0;
    };
    loadMany(scenarios);

    localGit(temp,'init','-q');localGit(temp,'add','-f','--all');
    return {root:temp,names:[...names],loadMany};
  } catch(error) {rmSync(temp,{recursive:true,force:true});throw error;}
}
function selectedFiles(root, tests) {
  const script=`import {captureSource} from ${JSON.stringify(new URL('./runtime-preflight.mjs',import.meta.url).href)};try{process.stdout.write(JSON.stringify(captureSource(process.argv[1],{tests:JSON.parse(process.argv[2])}).files));}catch(error){process.stderr.write(String(error.message));process.exitCode=1;}`;
  try {return JSON.parse(execFileSync(process.execPath,['--input-type=module','-e',script,root,JSON.stringify(tests)],{env:gitEnvironment(),maxBuffer:16*1024*1024,stdio:['ignore','pipe','pipe']}).toString());}
  catch(error) {throw Error(`Required context selection failed: ${error.stderr?.toString().trim() || 'local selector failed'}`);}
}
function nativeFingerprint(root) {
  const names=[...new Set(localGit(root,'ls-files','-z','-co','--exclude-standard').toString('utf8').split('\0').filter(Boolean))].sort();
  return hash(JSON.stringify(names.map(path=>{
    requireThat(canonicalPath(path),'Invalid source path.');
    try {
      const stat=lstatSync(join(root,path),{bigint:true});
      return [path,...['dev','ino','mode','nlink','size','mtimeNs','ctimeNs'].map(key=>String(stat[key]))];
    } catch(error){if(error.code==='ENOENT')return [path,'missing'];throw error;}
  })));
}
function inspectAdoptionView(view, prompts, scenarios) {
  const vectors=[], seeds=[...prompts]; let total=0, checks=0, steps=0;
  for (const path of [...scenarios].sort()) {
    const raw=boundedFile(join(view.root,path),10*1024*1024); const doc=parse(raw);
    requireThat(doc?.schema_version === 'prompt-runtime.program-scenario.v1','Declared scenario has an invalid version.');
    requireThat(raw.length<=LIMIT,'Original vector exceeds its byte limit.');
    const vector=scenario(path,raw); total+=raw.length; checks+=vector.checks.length; steps+=vector.steps.length;
    requireThat(vectors.length < 200 && total<=10*1024*1024 && checks<=MAX && steps<=MAX, 'Corpus exceeds original vector bounds.');
    vectors.push(vector);
    seeds.push(...doc.steps.map(step=>step.entry_path));
    if(typeof doc.story_path==='string')seeds.push(doc.story_path);
    if(Array.isArray(doc.entry_paths))seeds.push(...doc.entry_paths);
    for(const item of doc.context??[]) {
      requireThat(object(item)&&canonicalPath(item.prompt_path)&&Array.isArray(item.paths)&&item.paths.every(canonicalPath),'Invalid scenario context.');
      seeds.push(item.prompt_path,...item.paths);
    }
  }
  // The source selector owns required links, explicit context and prompt call targets.
  // A private seed supplies declaration prompts without altering original scenarios.
  let seed='.pdd-adoption-seed';while(view.names.includes(seed))seed+='-';
  writeFileSync(join(view.root,seed),JSON.stringify({entry_paths:[...new Set(seeds)]}));localGit(view.root,'add','-f','--',seed);
  if(view.names.includes('pdd-source.json'))view.loadMany(['pdd-source.json']);
  const paths=vectors.map(v=>v.path);
  // Resolve with the canonical selector until all newly selected files have their
  // actual bytes. Unrelated implementation files remain placeholders in this view.
  let selected;
  for(;;) {
    selected=selectedFiles(view.root,[seed]).map(file=>file.path).filter(path=>path!==seed);
    const changed=view.loadMany(selected);
    if(!changed)break;
  }
  const context=selected.filter(path=>!paths.includes(path)).map(path=>({path,sha256:hash(boundedFile(join(view.root,path),10*1024*1024,true))}));
  // Detect required-context cycles using the selector's actual transitive relation.
  // Remove global includes only in this disposable cycle-analysis view.
  const config=join(view.root,'pdd-source.json');let configBytes;
  try {configBytes=readFileSync(config);rmSync(config);localGit(view.root,'rm','--cached','--','pdd-source.json');} catch(error) {if(error.code!=='ENOENT')throw error;}
  for(const {path} of context.filter(row=>row.path.endsWith('.md'))) {
    let index=0,alias;do{alias=join(dirname(path),`.pdd-adoption-cycle-${index++}`+(path.endsWith('.prompt.md')?'.prompt.md':'.md'));}while(view.names.includes(alias));
    writeFileSync(join(view.root,alias),readFileSync(join(view.root,path)));
    localGit(view.root,'add','-f','--',alias);
    writeFileSync(join(view.root,seed),JSON.stringify({entry_paths:[alias]}));
    requireThat(!selectedFiles(view.root,[seed]).some(file=>file.path===path),'Required context cycle.');
    rmSync(join(view.root,alias));localGit(view.root,'rm','--cached','--',alias);
  }
  if(configBytes)writeFileSync(config,configBytes);
  return {vectors:vectors.map(v=>({path:v.path,sha256:v.sha256,checks:v.checks.map(c=>JSON.stringify([c.vector,c.step_id,c.check_index,...identity.map(k=>c[k])]))})),context};
}
function readNativeAdoptionSnapshot({root,declarationPath}, options) {
  const requested=resolve(root,declarationPath);
  const raw=boundedFile(join(realpathSync(dirname(requested)),basename(requested)),64*1024), declaration=parse(raw);
  const snapshot={available:true,repository:repository(root),commit:declaration.commit,declaration,declaration_sha256:hash(raw),approved_vectors:[],current_vectors:[],approved_context:[],current_context:[],approved_commit_ancestor:false,cause:''};
  if(!validDeclaration(declaration)) return {snapshot,internal:{declarationBytes:raw}};
  try {
  const commit=localGit(root,'rev-parse','--verify','--end-of-options',`${declaration.commit}^{commit}`).toString().trim();
  requireThat(commit===declaration.commit,'Approved commit is unavailable.');snapshot.commit=commit;
  try {localGit(root,'merge-base','--is-ancestor',commit,options.currentRef || 'HEAD');snapshot.approved_commit_ancestor=true;} catch(error) {if(error.status!==1)throw Error('Approved commit ancestry could not be checked.');}
  if(!snapshot.approved_commit_ancestor)return {snapshot,internal:{declarationBytes:raw}};
  const before=options.currentRef ? null : nativeFingerprint(root);
  requireThat(options.currentRef || before,'Current source is unreadable.');
  const approved=adoptionView(root,commit,declaration.scenarios,'Approved');let current;
  try {
    current=adoptionView(root,options.currentRef,declaration.scenarios,'Current');
    const a=inspectAdoptionView(approved,declaration.prompts,declaration.scenarios),c=inspectAdoptionView(current,declaration.prompts,declaration.scenarios);
    requireThat(options.currentRef || nativeFingerprint(root)===before,'Current source changed while reading.');
    Object.assign(snapshot,{approved_vectors:a.vectors,current_vectors:c.vectors,approved_context:a.context,current_context:c.context});
    return {snapshot,internal:{declarationBytes:raw}};
  } finally {rmSync(approved.root,{recursive:true,force:true});if(current)rmSync(current.root,{recursive:true,force:true});}
  } catch(error) {snapshot.available=false;snapshot.cause=adoptionCause(error.message);return {snapshot,internal:{declarationBytes:raw}};}
}
export async function adoptReplayCorpus(root, declarationPath, ports = {}) {
  const provenance={repository:'',commit:'',reference:'',asserted_by:'',trust:'external-assertion-unverified',declaration_sha256:'',prompts:[],scenarios:[]};
  let cause='';
  const blocked=reason=>({outcome:'blocked',reason,cause,paths:[],provenance});
  try {
    const native=!ports.readAdoptionSnapshot;
    const {snapshot:s,internal}=await (ports.readAdoptionSnapshot ?? (args=>readNativeAdoptionSnapshot(args,ports)))({root,declarationPath});
    if(native && internal?.declarationBytes)ports.onNativeDeclaration?.(internal.declarationBytes);
    cause=adoptionCause(s?.cause);
    const d=s?.declaration;
    if(validDeclaration(d))Object.assign(provenance,{repository:d.repository,commit:d.commit,reference:d.approval.reference,asserted_by:d.approval.asserted_by,declaration_sha256:sha(s.declaration_sha256)?s.declaration_sha256:'',prompts:[...d.prompts],scenarios:[...d.scenarios]});
    if(!object(s) || s.available!==true)return blocked('unavailable');
    if(!validDeclaration(d)){cause=adoptionCause(declarationCause(d) || 'Declaration shape or approval assertion is invalid.');return blocked('invalid-approval');}
    if(d.repository!==s.repository || d.commit!==s.commit)return blocked('foreign-source');
    if(typeof s.approved_commit_ancestor!=='boolean' || typeof s.cause!=='string')return blocked('unavailable');
    if(!s.approved_commit_ancestor){cause=cause||'Approved commit is not an ancestor of the selected source.';return blocked('unrelated-commit');}
    const inventory=rows=>Array.isArray(rows) && rows.length>0 && rows.length<=200 && rows.every(r=>object(r)&&canonicalPath(r.path)) && new Set(rows.map(r=>r.path)).size===rows.length;
    if(!inventory(s.approved_vectors)||!inventory(s.current_vectors))return blocked('inventory-mismatch');
    const sorted=rows=>[...rows].sort((a,b)=>a.path.localeCompare(b.path));
    if([s.approved_vectors,s.current_vectors].some(rows=>JSON.stringify(sorted(rows).map(r=>r.path))!==JSON.stringify([...d.scenarios].sort((a,b)=>a.localeCompare(b)))))return blocked('inventory-mismatch');
    // Tuple strings encode several independently bounded identities; JSON escaping
    // can expand a valid component to six characters per original character.
    const facts=(rows,vector)=>Array.isArray(rows) && rows.length<=10000 &&
      new Set(rows.map(r=>r?.path)).size===rows.length && rows.every(r=>object(r) && canonicalPath(r.path) && sha(r.sha256) &&
        (!vector || (Array.isArray(r.checks) && r.checks.length>0 && r.checks.length<=MAX && new Set(r.checks).size===r.checks.length &&
          r.checks.every(value=>typeof value==='string' && value.trim().length>0 && value.length<=64*1024))));
    if(!sha(s.declaration_sha256)||!facts(s.approved_vectors,true)||!facts(s.current_vectors,true)||!facts(s.approved_context)||!facts(s.current_context))return blocked('unavailable');
    for(const kind of ['vectors','context']) {
      const normalized=rows=>sorted(rows).map(r=>[r.path,r.sha256,...(kind==='vectors'?[r.checks]:[])]);
      if(JSON.stringify(normalized(s[`approved_${kind}`]))!==JSON.stringify(normalized(s[`current_${kind}`])))return blocked('content-mismatch');
    }
    ports.onSnapshot?.(s);
    return {outcome:'adopted',reason:'',cause:'',paths:sorted(s.approved_vectors).map(r=>r.path),provenance};
  } catch(error) {cause=adoptionCause(error.message);return blocked('unavailable');}
}

const emptyCounts = (total=0) => ({total,pass:0,fail:0,blocked:0,not_replayed:total});
export function readReplayEvidence(run) {
  let result = {outcome:'blocked',reason:'Structured replay evidence is unavailable.',counts:emptyCounts(),vectors:[],source:null,manifest_sha256:null,operations:{total:0,executed:0},...(run.replayAdoption ? {adoption:run.replayAdoption.provenance} : {})};
  try {
    const baseline = run.replayBaseline;
    requireThat(baseline?.schema_version === 'pdd.replay-vectors.v1' && Array.isArray(baseline.vectors) && baseline.vectors.length <= 200, 'No approved original-vector anchor is saved; return to prompt space.');
    result.vectors = baseline.vectors.map(({path,sha256})=>({path,sha256}));
    if (baseline.outcome) return {...result,outcome:baseline.outcome === 'not_replayed' ? 'not_replayed':'blocked',reason:sanitize(baseline.reason)};
    requireThat(baseline.vectors.length > 0, 'The original vector set is empty.');
    const current = pinReplayVectors(run.root,baseline.vectors.map(v=>v.path));
    requireThat(!current.outcome && JSON.stringify(current.vectors) === JSON.stringify(baseline.vectors), 'Original vectors changed, are absent, empty, unreadable or no longer match their approved hashes.');
    const checks = baseline.vectors.flatMap(v=>v.checks), steps = baseline.vectors.flatMap(v=>v.steps);
    result.counts=emptyCounts(checks.length);result.operations.total=steps.length;
    const expected = new Map(checks.map(row=>[key(row),row])), expectedSteps = new Map(steps.map(row=>[stepKey(row),row]));
    requireThat(checks.length > 0 && checks.length <= MAX && expected.size === checks.length && steps.length <= MAX && expectedSteps.size === steps.length, 'Original assertion/operation identities are empty or duplicated.');
    const bytes = boundedFile(join(run.runDir,'replay-evidence.json'));result.manifest_sha256=hash(bytes);
    const doc = parse(bytes);
    requireThat(object(doc) && doc.schema_version === REPLAY_POLICY && doc.run_id === run.runId, 'The replay manifest version or run identity is invalid.');
    const fingerprint = sourceFingerprint(run.root);
    requireThat(object(doc.source) && doc.source.kind === 'git-content-v1' && sha(doc.source.sha256) && fingerprint !== null && doc.source.sha256 === fingerprint, 'Replay evidence is stale or its source fingerprint is invalid.');result.source={kind:'git-content-v1',sha256:doc.source.sha256};
    requireThat(Array.isArray(doc.vectors) && doc.vectors.length === baseline.vectors.length && new Set(doc.vectors.map(v=>v?.path)).size === doc.vectors.length, 'The manifest must name every original vector exactly once.');
    const originals = new Map(result.vectors.map(v=>[v.path,v.sha256]));
    requireThat(doc.vectors.every(v=>object(v) && sha(v.sha256) && originals.get(v.path) === v.sha256), 'The manifest changed or substituted an original vector hash.');
    requireThat(Array.isArray(doc.checks) && doc.checks.length <= MAX && Array.isArray(doc.operations) && doc.operations.length <= MAX, 'The manifest needs bounded check and operation rows.');
    const rows = new Map(), operations = new Map();
    for (const row of doc.checks) {
      requireThat(object(row) && integer(row.check_index) && states.includes(row.outcome), 'An assertion row has an invalid outcome or identity.');
      const original=expected.get(key(row));
      requireThat(original && !rows.has(key(row)) && identity.every(k=>row[k] === original[k]), 'An assertion row is unknown, duplicated or mismatches its original operation/target.');
      requireThat((row.reason === undefined || text(row.reason)) && (!['blocked','not_replayed'].includes(row.outcome) || text(row.reason)), 'Unmapped/blocked checks need a reason.');rows.set(key(row),row);
    }
    for (const row of doc.operations) {
      requireThat(object(row), 'Invalid public-operation row.');const original=expectedSteps.get(stepKey(row));
      requireThat(original && !operations.has(stepKey(row)) && ['entry_path','operation'].every(k=>row[k]===original[k]), 'A public operation is unknown, duplicated or substituted.');
      requireThat(typeof row.executed === 'boolean' && ['returned','expected_error','crash','not_run'].includes(row.outcome), 'Public execution flags/outcomes must be typed.');
      if (row.executed) requireThat(row.outcome !== 'not_run' && object(row.boundary) && ['function','command','route'].includes(row.boundary.kind) && text(row.boundary.name) && text(row.command) && exit(row.exit_code), 'Executed operations need a real public-boundary identity and command/exit record.');
      else requireThat(row.outcome === 'not_run' && row.exit_code === null, 'An unexecuted operation cannot claim completion.');
      operations.set(stepKey(row),row);
    }
    const counts = {total:checks.length,pass:0,fail:0,blocked:0,not_replayed:0};
    for (const original of checks) {
      const op=operations.get(stepKey(original)), row=rows.get(key(original));
      const outcome=(!op?.executed || !['returned','expected_error'].includes(op.outcome)) ? 'not_replayed' : row?.outcome ?? 'not_replayed';counts[outcome]++;
    }
    requireThat(object(doc.counts) && Object.keys(counts).every(k=>integer(doc.counts[k]) && doc.counts[k]===counts[k]), 'Replay counts do not equal the original assertion outcomes.');
    result.counts=counts;result.operations.executed=[...operations.values()].filter(op=>op.executed && ['returned','expected_error'].includes(op.outcome)).length;
    const mutation=doc.mutation;
    requireThat(object(mutation) && mutation.kind === 'semantic' && text(mutation.description) && controls.includes(mutation.outcome) && (mutation.outcome === 'not_run' ? text(mutation.reason) && mutation.exit_code === null && (mutation.command === null || text(mutation.command)) : text(mutation.command) && exit(mutation.exit_code)) && Array.isArray(mutation.failed_checks) && mutation.failed_checks.length <= MAX, 'A typed semantic mutation-control record is required.');
    const failed=new Set();for(const row of mutation.failed_checks) {requireThat(object(row) && integer(row.check_index) && expected.has(key(row)) && !failed.has(key(row)), 'Mutation failures must name unique original assertions.');failed.add(key(row));}
    result.mutation={outcome:mutation.outcome,failures:failed.size,description:sanitize(mutation.description)};
    const formal=doc.formal;
    requireThat(object(formal) && ['proved_bounded','proved_solver','failed','not_run','not_applicable'].includes(formal.result) && text(formal.scope) && text(formal.reason) && controls.includes(formal.control_outcome), 'A typed formal result, scope, reason and control outcome are required.');
    requireThat(formal.result !== 'failed' || Object.hasOwn(formal,'counterexample'), 'A failed formal check needs its counterexample.');
    result.formal={result:formal.result,scope:sanitize(formal.scope),reason:sanitize(formal.reason),control_outcome:formal.control_outcome};
    const detected=mutation.outcome === 'assertion_failure' && mutation.exit_code !== 0 && failed.size > 0;
    requireThat(!formal.result.startsWith('proved_') || (detected && formal.control_outcome === 'assertion_failure'), 'A proved formal check needs semantic assertion-failure control, not a crash.');
    const outcome=counts.blocked ? 'blocked' : counts.not_replayed ? 'not_replayed' : !detected ? 'blocked' : counts.fail || formal.result === 'failed' ? 'fail' : 'pass';
    return {...result,outcome,reason:counts.blocked ? 'Some checks are blocked.' : counts.not_replayed ? 'Some original assertions or public operations were not replayed.' : !detected ? 'The semantic mutation control did not detect an assertion failure; a crash is not detection.' : outcome==='fail' ? 'Assertion or formal failures were recorded.' : 'All original assertions have source-bound public-boundary replay evidence.'};
  } catch (e) { return {...result,outcome:'blocked',reason:e.code==='ENOENT' ? 'Missing replay-evidence.json or an original vector; code replay is blocked.' : sanitize(e.message || 'Malformed replay evidence.')}; }
}
export function formatReplayEvidence(result) {
  const counts=result.counts??emptyCounts(), label=String(result.outcome).replace('_',' ').toUpperCase();
  const formalLabel={proved_bounded:'Proved (bounded)',proved_solver:'Proved (solver)',failed:'Failed + counterexample',not_run:'Not run',not_applicable:'Not applicable'};
  return [ ...(counts.fail ? [`✗ ${counts.fail} replay assertions fail`] : []), ...(result.formal?.result==='failed' ? ['✗ Formal check failed (counterexample in replay-evidence.json).'] : []),
    `Code replay: ${label} — ${render(result.reason)}`,`${counts.total} checks: ${counts.pass} passed, ${counts.fail} failed, ${counts.blocked} blocked, ${counts.not_replayed} not replayed.`,
    ...(result.adoption ? [`Anchor adopted from ${render(result.adoption.repository)}@${render(result.adoption.commit)}; approval reference ${render(result.adoption.reference)} by ${render(result.adoption.asserted_by)}; external-assertion-unverified`] : []),
    `Public-boundary operations: ${result.operations?.executed??0}/${result.operations?.total??0} executed.`,
    `Semantic mutation control: ${result.mutation?.outcome??'not recorded'}${result.mutation ? ` (${result.mutation.failures} assertion failures)` : ''}.`,
    `Formal check (agent reported): ${formalLabel[result.formal?.result]??'not recorded'}${result.formal ? `; scope: ${render(result.formal.scope)}; reason: ${render(result.formal.reason)}` : ''}.`,
    `Source: ${result.source?.sha256??'unconfirmed'}. Manifest SHA256: ${result.manifest_sha256??'unavailable'}.`,
    ...(result.vectors??[]).slice(0,12).map(v=>`Original vector: ${render(v.path)} — ${sha(v.sha256)?v.sha256:'unconfirmed'}.`),
    ...((result.vectors?.length??0)>12 ? [`${result.vectors.length-12} more original vector identities are in the full manifest.`] : []),
    'Agents execute the tests and supply this record. pdd validates structure and identity; it does not independently prove execution or prompt/code equivalence.',
    'Full evidence: replay-evidence.json in the run folder.'].join('\n');
}
