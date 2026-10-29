// Generated from prompts/cli/workflow-inventory.prompt.md (sha256: 5f42aebeedccdd6e344550f7f5190e7e61d4d5e67d583ed2f4f81272172971fd).
import { execFile as callbackExec } from 'node:child_process';
import { promisify } from 'node:util';

const exec = promisify(callbackExec);
const MAX_FILES = 1000, MAX_BLOB = 1024 * 1024, MAX_BYTES = 16 * MAX_BLOB, BUDGET = 12000;
const DISCLAIMER = 'Static inventory only; tests were not run.';
const sha = value => typeof value === 'string' && /^(?:[a-f\d]{40}|[a-f\d]{64})$/i.test(value);
const size = value => [...value].length;
const quoted = value => JSON.stringify(value).replace(/[\x7f-\x9f\u061c\u200e\u200f\u202a-\u202e\u2066-\u2069]/g, c => `\\u${c.charCodeAt(0).toString(16).padStart(4, '0')}`)
  .replace(/[&<>`|:]/g, c => `&#${c.charCodeAt(0)};`);
const unavailable = reason => {
  const text = `Tests vs base: unavailable (${quoted(reason)}).\nChanged assertions in kept tests: unavailable.\nNew skips: unavailable.\n${DISCLAIMER}\n`;
  return { available: false, reason, text, details: text };
};
function language(path) {
  const base = path.split('/').at(-1);
  if (/\.(?:[cm]?[jt]s|[jt]sx)$/.test(base) && (/\.(?:test|spec)\./.test(base) || path.split('/').some(p => ['test','tests','__tests__'].includes(p)))) return 'js';
  if (/^(?:test_.*|.*_test)\.py$/.test(base)) return 'py';
  if (/_test\.go$/.test(base)) return 'go';
  return null;
}
const comment = (line, lang) => (lang === 'py' ? /^\s*#/ : /^\s*(?:\/\/|\/\*|\*)/).test(line);
// Static JavaScript strings only; interpreting escapes does not execute source.
function literal(source) {
  const quote = source[0];
  if (!['"', "'", '`'].includes(quote)) return null;
  let name = '';
  for (let i = 1; i < source.length; i++) {
    const c = source[i];
    if (c === quote) return { name, end: i + 1 };
    if (quote === '`' && c === '$' && source[i + 1] === '{') return null;
    if (c !== '\\') { name += c; continue; }
    const escaped = source[++i];
    if (escaped === undefined) return null;
    const special = { n:'\n',r:'\r',t:'\t',b:'\b',f:'\f',v:'\v','0':'\0' };
    if (Object.hasOwn(special, escaped)) name += special[escaped];
    else if (escaped === 'x' || escaped === 'u') {
      const rest = source.slice(i + 1), braced = escaped === 'u' && rest.startsWith('{');
      const match = braced ? /^\{([\da-f]{1,6})\}/i.exec(rest) : new RegExp(`^([\\da-f]{${escaped === 'x' ? 2 : 4}})`, 'i').exec(rest);
      if (!match || parseInt(match[1],16) > 0x10ffff) return null;
      name += String.fromCodePoint(parseInt(match[1],16)); i += match[0].length;
    } else name += escaped;
  }
  return null;
}
function cases(source, lang) {
  if (!lang) return [];
  const lines = source.split('\n'), found = [], occurrences = new Map();
  for (let at = 0; at < lines.length; at++) {
    const line = lines[at]; if (comment(line,lang)) continue;
    const indent = /^\s*/.exec(line)[0]; let name, end = at, tail = '', declaration;
    if (lang === 'js') {
      declaration = /^(\s*)(?:test|it)(?:\.(?:only|skip|todo))?\s*\(\s*/.exec(line);
      if (!declaration) continue;
      const parsed = literal(line.slice(declaration[0].length)); if (!parsed) continue;
      tail = line.slice(declaration[0].length + parsed.end);
      if (!/^\s*[,)]/.test(tail)) continue;
      name = parsed.name;
      // A conventional multiline callback ends at its declaration indentation.
      if (/(?:=>\s*\{|function\b[^{}]*\{)/.test(tail) && !/}\s*\)\s*;?\s*(?:\/\/.*)?$/.test(tail)) {
        end = lines.length - 1;
        for (let i = at + 1; i < lines.length; i++) if (lines[i].startsWith(indent) && /^}\);\s*(?:\/\/.*)?$/.test(lines[i].slice(indent.length))) { end = i; break; }
      }
    } else {
      const match = (lang === 'py' ? /^\s*(?:async\s+)?def\s+(test_\w+)\s*\(/ : /^\s*func\s+(Test\w*)\s*\(/).exec(line);
      if (!match) continue;
      name = match[1]; end = lines.length - 1;
      for (let i = at + 1; i < lines.length; i++) {
        if (lang === 'go' ? /^}/.test(lines[i]) : lines[i].trim() && !comment(lines[i],lang) && /^\s*/.exec(lines[i])[0].length <= indent.length) { end = lang === 'go' ? i : i - 1; break; }
      }
    }
    const occurrence = (occurrences.get(name) ?? 0) + 1; occurrences.set(name,occurrence);
    const body = lang === 'js' ? tail.match(/(?:=>|function\b[^{}]*\{)(.*)/)?.[1] ?? '' : line;
    const entry = { name, occurrence, at, end, body, options: tail.split(/=>|function\b/)[0], assertions: [], markers: [] };
    if (lang === 'py') for (let i = at - 1; i >= 0 && /^\s*@/.test(lines[i]); i--) {
      if (/^\s*@pytest\.mark\.(?:skip|skipif|xfail)\b/.test(lines[i])) entry.markers.unshift(lines[i]);
    }
    found.push(entry);
  }
  for (let at = 0; at < lines.length; at++) {
    const line = lines[at]; if (comment(line,lang)) continue;
    const owner = found.findLast(entry => entry.at <= at && entry.end >= at); if (!owner) continue;
    const content = lang === 'js' && at === owner.at ? owner.body : line;
    if (/\b(?:assert|expect)\b/.test(content)) owner.assertions.push(line);
    if (lang === 'js' && ((at === owner.at && (/^\s*(?:test|it)\.(?:skip|todo)\s*\(/.test(line) || /\b(?:skip|todo)\s*:\s*true\b/.test(owner.options))) || /\bt\.(?:skip|todo)\s*\(/.test(content))) owner.markers.push(line);
  }
  return found;
}
const key = entry => JSON.stringify([entry.name,entry.occurrence]);
const label = entry => `${quoted(entry.name)}${entry.occurrence > 1 ? ` [${entry.occurrence}]` : ''}`;
// Find the earliest old/new pair among maximum-length common subsequences.
// Rows retain only length and first-match identity, bounding auxiliary memory.
function common(a,b) {
  const matches=[];let oldAt=0,newAt=0;
  while(oldAt<a.length && newAt<b.length) {
    if(a[oldAt]===b[newAt]) {matches.push([oldAt++,newAt++]);continue;}
    const width=b.length-newAt,stride=b.length+1;
    let lengths=new Uint32Array(width+1),first=new Float64Array(width+1).fill(Infinity);
    for(let i=a.length-1;i>=oldAt;i--) {
      const next=new Uint32Array(width+1),pairs=new Float64Array(width+1).fill(Infinity);
      for(let j=width-1;j>=0;j--) {
        if(a[i]===b[newAt+j]) {next[j]=lengths[j+1]+1;pairs[j]=i*stride+newAt+j;}
        else if(lengths[j]>next[j+1]) {next[j]=lengths[j];pairs[j]=first[j];}
        else if(lengths[j]<next[j+1]) {next[j]=next[j+1];pairs[j]=pairs[j+1];}
        else {next[j]=lengths[j];pairs[j]=Math.min(first[j],pairs[j+1]);}
      }
      lengths=next;first=pairs;
    }
    if(!lengths[0])break;
    oldAt=Math.floor(first[0]/stride);newAt=first[0]%stride;
    matches.push([oldAt++,newAt++]);
  }
  return matches;
}
function assertionChanges(before,after) {
  const changes=[];let oldAt=0,newAt=0;
  for(const [oldEnd,newEnd] of [...common(before,after),[before.length,after.length]]) {
    const count=Math.max(oldEnd-oldAt,newEnd-newAt);
    for(let i=0;i<count;i++) changes.push([oldAt+i<oldEnd?before[oldAt+i]:null,newAt+i<newEnd?after[newAt+i]:null]);
    oldAt=oldEnd+1;newAt=newEnd+1;
  }
  return changes;
}
function introduced(before,after) {
  const counts=new Map();for(const line of before) counts.set(line,(counts.get(line)??0)+1);
  return after.filter(line=>{const n=counts.get(line)??0;if(n){counts.set(line,n-1);return false;}return true;});
}
function bounded(summaries,detailLines,details) {
  if(size(details)<=BUDGET)return details;
  const kept=[];let omittedFiles=0,omitted=detailLines.length;
  // Reserve room for the omission disclosure and disclaimer before retaining whole lines.
  const room=BUDGET-250-size(DISCLAIMER);
  let used=0;
  for(const line of summaries){if(used+size(line)+1<=room){kept.push(line);used+=size(line)+1;}else omittedFiles++;}
  for(const line of detailLines){if(used+size(line)+1>room)break;kept.push(line);used+=size(line)+1;omitted--;}
  return [...kept,`Inventory details omitted: ${omitted} lines;${omittedFiles?` ${omittedFiles} file summaries omitted;`:''} full report: test-inventory.json in the run folder.`,DISCLAIMER,''].join('\n');
}
export function analyzeTestChanges({files}) {
  if(!Array.isArray(files))return unavailable('snapshot unavailable');
  if(files.length>MAX_FILES)return unavailable('inventory limit exceeded');
  let bytes=0;const counts=[],summaries=[],assertions=[],skips=[];
  const selected=[];
  for(const file of files){
    if(!file || !['oldPath','newPath','before','after'].every(k=>typeof file[k]==='string'))return unavailable('snapshot unavailable');
    const oldLang=language(file.oldPath),newLang=language(file.newPath);if(!oldLang&&!newLang)continue;
    for(const [lang,source] of [[oldLang,file.before],[newLang,file.after]])if(lang){const n=Buffer.byteLength(source);bytes+=n;if(n>MAX_BLOB||bytes>MAX_BYTES)return unavailable('inventory limit exceeded');if(source.includes('\0')||/[\ud800-\udbff](?![\udc00-\udfff])|(?<![\ud800-\udbff])[\udc00-\udfff]/u.test(source))return unavailable('snapshot unavailable');}
    selected.push({...file,oldLang,newLang});
  }
  selected.sort((a,b)=>(a.newPath||a.oldPath)<(b.newPath||b.oldPath)?-1:(a.newPath||a.oldPath)>(b.newPath||b.oldPath)?1:0);
  for(const file of selected){
    const before=cases(file.before,file.oldLang),after=cases(file.after,file.newLang),oldMap=new Map(before.map(c=>[key(c),c])),newMap=new Map(after.map(c=>[key(c),c]));
    const removed=before.filter(c=>!newMap.has(key(c))),path=file.oldPath&&file.newPath&&file.oldPath!==file.newPath?`${quoted(file.oldPath)} → ${quoted(file.newPath)}`:quoted(file.newPath||file.oldPath);
    const prefix=`Tests vs base: ${path} ${before.length} → ${after.length} tests. Removed: `;
    counts.push(prefix+(removed.length?`${removed.length} (${removed.map(label).join(', ')}).`:'none.'));
    summaries.push(prefix+(removed.length?`${removed.length}.`:'none.'));
    for(const current of after){const previous=oldMap.get(key(current));
      if(previous)for(const [oldLine,newLine] of assertionChanges(previous.assertions,current.assertions)) assertions.push(`Changed assertions in kept tests: ${path} ${label(current)} ${oldLine===null?'(added)':quoted(oldLine)} → ${newLine===null?'(removed)':quoted(newLine)}.`);
      for(const line of introduced(previous?.markers??[],current.markers))skips.push(`New skips: ${path} ${label(current)} ${quoted(line)}.`);
    }
  }
  if(!counts.length){counts.push('Tests vs base: none.');summaries.push(counts[0]);}
  if(!assertions.length)assertions.push('Changed assertions in kept tests: none.');
  if(!skips.length)skips.push('New skips: none.');
  const details=[...counts,...assertions,...skips,DISCLAIMER,''].join('\n');
  // Full count lines become detail lines when names must be omitted from summaries.
  const detailLines=[...counts.filter((line,i)=>line!==summaries[i]),...assertions,...skips];
  return {available:true,reason:'',text:bounded(summaries,detailLines,details),details};
}
export async function collectTestInventory(input,ports={}) {
  const request={cwd:input.cwd,baseSha:input.baseSha,headSha:input.headSha};
  if(!sha(request.baseSha)||!sha(request.headSha))return unavailable('invalid commit identity');
  let snapshot;
  try{snapshot=await (ports.readSnapshot??(value=>readGitTestSnapshot(value,ports)))(request);}
  catch{return unavailable('snapshot read failed');}
  if(!snapshot?.available)return unavailable(snapshot?.reason==='inventory limit exceeded'?snapshot.reason:'snapshot unavailable');
  try { return analyzeTestChanges(snapshot); } catch { return unavailable('snapshot unavailable'); }
}
export async function readGitTestSnapshot(input,ports={}) {
  if(!sha(input.baseSha)||!sha(input.headSha))return {available:false,reason:'invalid commit identity',files:[]};
  const execute=ports.execFile??((file,args,opts)=>exec(file,args,{...opts,encoding:'buffer',maxBuffer:MAX_BYTES+MAX_BLOB}));
  const command=async args=>{const reply=await execute('git',args,{cwd:input.cwd});if(reply.code!==undefined&&reply.code!==0)throw Error('Git read failed');return Buffer.isBuffer(reply.stdout)?reply.stdout:Buffer.from(reply.stdout??'');};
  try{
    const raw=new TextDecoder('utf-8',{fatal:true}).decode(await command(['diff','--no-ext-diff','--no-textconv','--name-status','-z','--find-renames',input.baseSha,input.headSha,'--']));
    if(raw&&!raw.endsWith('\0'))throw Error('Invalid records');
    const fields=raw?raw.slice(0,-1).split('\0'):[],records=[];
    for(let i=0;i<fields.length;){const status=fields[i++];if(!/^(?:[AMDT]|R\d+)$/.test(status))throw Error('Invalid status');const first=fields[i++],second=status.startsWith('R')?fields[i++]:first;if(!first||!second)throw Error('Invalid paths');records.push({oldPath:status==='A'?'':first,newPath:status==='D'?'':second});}
    if(records.length>MAX_FILES)return {available:false,reason:'inventory limit exceeded',files:[]};
    let bytes=0;const files=[];
    for(const record of records){if(!language(record.oldPath)&&!language(record.newPath))continue;
      const file={...record,before:'',after:''};
      for(const [path,commit,side] of [[record.oldPath,input.baseSha,'before'],[record.newPath,input.headSha,'after']])if(path&&language(path)){
        const object=`${commit}:${path}`,length=Number((await command(['cat-file','-s',object])).toString('ascii').trim());
        if(!Number.isSafeInteger(length)||length<0)throw Error('Invalid blob size');bytes+=length;
        if(length>MAX_BLOB||bytes>MAX_BYTES)return {available:false,reason:'inventory limit exceeded',files:[]};
        const blob=await command(['cat-file','blob',object]);if(blob.length!==length||blob.includes(0))throw Error('Invalid blob');
        file[side]=new TextDecoder('utf-8',{fatal:true}).decode(blob);
      }
      files.push(file);
    }
    return {available:true,reason:'',files};
  }catch{return {available:false,reason:'snapshot unavailable',files:[]};}
}
