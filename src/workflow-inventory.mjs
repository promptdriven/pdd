// Generated from prompts/cli/workflow-inventory.prompt.md (sha256: c165ecc598ca0e5609a0005d1b14316fb2234c7c56f2931566c05ce3d8a16c3c).
import { execFile as callbackExec } from 'node:child_process';
import { promisify } from 'node:util';

const exec = promisify(callbackExec);
const MAX_FILES = 1000, MAX_BLOB = 1024 * 1024, MAX_BYTES = 16 * MAX_BLOB, BUDGET = 12000;
const BLOB_REASONS = ['candidate blob exceeds 1 MiB', 'binary candidate blob', 'non-UTF-8 candidate blob'];
const DISCLAIMER = 'Static inventory only; tests were not run.';
const sha = value => typeof value === 'string' && /^(?:[a-f\d]{40}|[a-f\d]{64})$/i.test(value);
const size = value => [...value].length;
const quoted = value => JSON.stringify(value).replace(/[\x7f-\x9f\u061c\u200e\u200f\u202a-\u202e\u2066-\u2069]/g, c => `\\u${c.charCodeAt(0).toString(16).padStart(4, '0')}`)
  .replace(/[&<>`|:@#]/g, c => `&#${c.charCodeAt(0)};`);
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
// Only the direct properties of the second-argument object are options.
// Keep quoted data and nested expressions opaque while separating properties.
function declarationSkip(source) {
  const opening = /^\s*,\s*\{/.exec(source);
  if (!opening) return false;
  const properties = [], nesting = [];
  let property = '';
  for (let at = opening[0].length; at < source.length; at++) {
    const c = source[at];
    if (["'", '"', '`'].includes(c)) {
      const start = at;
      for (at++; at < source.length; at++) {
        if (source[at] === '\\') at++;
        else if (source[at] === c) break;
      }
      if (at >= source.length) return false;
      property += source.slice(start, at + 1);
    } else if (source.startsWith('//', at)) return false;
    else if (source.startsWith('/*', at)) {
      const end = source.indexOf('*/', at + 2);
      if (end < 0) return false;
      property += ' '; at = end + 1;
    } else if ('([{'.includes(c)) { nesting.push(c); property += c; }
    else if (c === '}' && !nesting.length) {
      if (!/^\s*[,)]/.test(source.slice(at + 1))) return false;
      properties.push(property);
      return properties.some(part => {
        const match = /^\s*(skip|todo)\s*:\s*(.*?)\s*$/.exec(part);
        if (!match) return false;
        if (match[2] === 'true') return true;
        const value = match[1] === 'skip' ? literal(match[2]) : null;
        return Boolean(value?.name && value.end === match[2].length);
      });
    } else if (')]}'.includes(c)) {
      if (nesting.pop() !== {')':'(',']':'[','}':'{'}[c]) return false;
      property += c;
    } else if (c === ',' && !nesting.length) { properties.push(property); property = ''; }
    else property += c;
  }
  return false;
}
// Locate a callback argument, rather than an arrow/function anywhere in options.
// Mask quoted data, common regex literals and comments without changing offsets,
// then balance the conventional argument list. This is not a full JS parser.
function declarationBody(source) {
  const masked = source.split('');
  let previous = '';
  for (let at = 0; at < source.length; at++) {
    const c = source[at];
    if (["'", '"', '`'].includes(c)) {
      masked[at] = 'q';
      for (at++; at < source.length; at++) {
        masked[at] = ' ';
        if (source[at] === '\\') { if (++at < source.length) masked[at] = ' '; }
        else if (source[at] === c) break;
      }
      previous = 'q';
    } else if (source.startsWith('//', at)) {
      masked.fill(' ', at); break;
    } else if (source.startsWith('/*', at)) {
      const end = source.indexOf('*/', at + 2);
      masked.fill(' ', at, end < 0 ? source.length : end + 2);
      at = end < 0 ? source.length : end + 1;
    } else if (c === '/' && (!previous || /^[([{:;,=!?&|+*%~^<>-]$/.test(previous))) {
      // Literal regexes in call arguments, assignments and arrow expressions
      // can contain brackets and comment-looking slashes. Only an unescaped
      // slash outside a character class closes the literal. Division after an
      // operand stays visible. An unterminated literal is outside this grammar.
      let end = at + 1, characterClass = false;
      for (; end < source.length; end++) {
        if (source[end] === '\\') end++;
        else if (source[end] === '[') characterClass = true;
        else if (source[end] === ']') characterClass = false;
        else if (source[end] === '/' && !characterClass) break;
      }
      if (end < source.length) {
        masked.fill(' ', at, end + 1);masked[at] = 'q';at = end;previous = 'q';
      } else previous = c;
    } else if (!/\s/.test(c)) {
      previous = c;
    }
  }
  const code = masked.join(''), nesting = [];
  const bodyAt = start => {
    while (/\s/.test(code[start] ?? '') && start < code.length) start++;
    const block = code[start] === '{', bodyStart = start + (block ? 1 : 0), stack = [];
    for (let at = start; at < code.length; at++) {
      const c = code[at];
      if ('([{'.includes(c)) stack.push(c);
      else if (')]}'.includes(c)) {
        if (!stack.length) return { body: source.slice(bodyStart, at), multiline: false };
        if (stack.pop() !== {')':'(',']':'[','}':'{'}[c]) return { body: '', multiline: false };
        if (block && !stack.length) return { body: source.slice(bodyStart, at), multiline: false };
      } else if (c === ',' && !stack.length) return { body: source.slice(bodyStart, at), multiline: false };
    }
    return { body: source.slice(bodyStart), multiline: block };
  };
  let argumentStart = 0;
  for (let at = 0; at < code.length; at++) {
    const c = code[at];
    if (!nesting.length) {
      if (c === ',') { argumentStart = at + 1; continue; }
      if (c === ')') break;
      if (code.startsWith('=>', at) && /^(?:async\s*)?(?:[\w$]+|\([\s\S]*\))$/.test(code.slice(argumentStart, at).trim())) return bodyAt(at + 2);
      if (c === '{' && /^(?:async\s+)?function(?:\s*\*)?(?:\s+[\w$]+)?\s*\([\s\S]*\)$/.test(code.slice(argumentStart, at).trim())) return bodyAt(at);
    }
    if ('([{'.includes(c)) nesting.push(c);
    else if (')]}'.includes(c) && nesting.pop() !== {')':'(',']':'[','}':'{'}[c]) break;
  }
  return { body: '', multiline: false };
}
function cases(source, lang) {
  if (!lang) return [];
  const lines = source.split('\n'), found = [], occurrences = new Map();
  for (let at = 0; at < lines.length; at++) {
    const line = lines[at]; if (comment(line,lang)) continue;
    const indent = /^\s*/.exec(line)[0]; let name, end = at, tail = '', declaration, callback;
    if (lang === 'js') {
      declaration = /^(\s*)(?:(?:test|it)(?:\.(?:only|skip|todo))?|xit|describe(?:\.skip)?)\s*\(\s*/.exec(line);
      if (!declaration) continue;
      const parsed = literal(line.slice(declaration[0].length)); if (!parsed) continue;
      tail = line.slice(declaration[0].length + parsed.end);
      if (!/^\s*[,)]/.test(tail)) continue;
      name = parsed.name;
      callback = declarationBody(tail);
      // A conventional multiline callback ends at its declaration indentation.
      if (callback.multiline) {
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
    const suite = lang === 'js' && /^\s*describe\b/.test(line);
    const identity = JSON.stringify([suite,name]);
    const occurrence = (occurrences.get(identity) ?? 0) + 1; occurrences.set(identity,occurrence);
    const body = lang === 'js' ? callback.body : line;
    const entry = { name, occurrence, suite, at, end, body, optionSkip: declarationSkip(tail), assertions: [], markers: [] };
    if (lang === 'py') for (let i = at - 1; i >= 0 && /^\s*@/.test(lines[i]); i--) {
      if (/^\s*@pytest\.mark\.(?:skip|skipif|xfail)\b/.test(lines[i])) entry.markers.unshift(lines[i]);
    }
    found.push(entry);
  }
  for (let at = 0; at < lines.length; at++) {
    const line = lines[at]; if (comment(line,lang)) continue;
    const owner = found.findLast(entry => !entry.suite && entry.at <= at && entry.end >= at);
    const suite = found.find(entry => entry.suite && entry.at === at);
    if (suite && /^\s*describe\.skip\s*\(/.test(line)) suite.markers.push(line);
    if (!owner) continue;
    const content = lang === 'js' && at === owner.at ? owner.body : line;
    if (/\b(?:assert|expect)\b/.test(content)) owner.assertions.push(line);
    if (lang === 'js' && ((at === owner.at && (/^\s*(?:(?:test|it)\.(?:skip|todo)|xit)\s*\(/.test(line) || owner.optionSkip)) || /\bt\.(?:skip|todo)\s*\(/.test(content))) owner.markers.push(line);
    if (lang === 'py' && /\bpytest\.skip\s*\(/.test(content)) owner.markers.push(line);
  }
  return found;
}
const key = entry => JSON.stringify([entry.name,entry.occurrence]);
const label = entry => `${quoted(entry.name)}${entry.occurrence > 1 ? ` [${entry.occurrence}]` : ''}`;
// One bounded suffix table, then earliest old/new matches for each LCS suffix.
function common(a,b) {
  if (!a.length || !b.length) return [];
  const width=b.length+1, table=new Uint32Array((a.length+1)*width);
  for(let i=a.length-1;i>=0;i--) for(let j=b.length-1;j>=0;j--) {
    table[i*width+j]=a[i]===b[j]?1+table[(i+1)*width+j+1]:Math.max(table[(i+1)*width+j],table[i*width+j+1]);
  }
  const matches=[];let oldAt=0,newAt=0,left=table[0];
  while(left) {
    let matched=false;
    for(let i=oldAt;i<a.length&&!matched;i++) for(let j=newAt;j<b.length;j++) {
      if(a[i]===b[j] && table[(i+1)*width+j+1]===left-1) {
        matches.push([i,j]);oldAt=i+1;newAt=j+1;left--;matched=true;break;
      }
    }
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
  let bytes=0;const counts=[],summaries=[],assertions=[],skips=[];
  const selected=[];
  for(const file of files){
    if(!file || !['oldPath','newPath','before','after'].every(k=>typeof file[k]==='string'))return unavailable('snapshot unavailable');
    const oldLang=language(file.oldPath),newLang=language(file.newPath);if(!oldLang&&!newLang)continue;
    if(selected.length===MAX_FILES)return unavailable('inventory limit exceeded');
    let reason=file.unavailableReason, pairBytes=0;
    if(reason!==undefined&&!BLOB_REASONS.includes(reason))return unavailable('snapshot unavailable');
    if(!reason)for(const [lang,source] of [[oldLang,file.before],[newLang,file.after]])if(lang){
      const n=Buffer.byteLength(source);pairBytes+=n;
      if(n>MAX_BLOB)reason=BLOB_REASONS[0];
      else if(source.includes('\0'))reason=BLOB_REASONS[1];
      else if(/[\ud800-\udbff](?![\udc00-\udfff])|(?<![\ud800-\udbff])[\udc00-\udfff]/u.test(source))reason=BLOB_REASONS[2];
      if(reason)break;
    }
    if(!reason){bytes+=pairBytes;if(bytes>MAX_BYTES)return unavailable('inventory limit exceeded');}
    selected.push({...file,oldLang,newLang,unavailableReason:reason});
  }
  selected.sort((a,b)=>(a.newPath||a.oldPath)<(b.newPath||b.oldPath)?-1:(a.newPath||a.oldPath)>(b.newPath||b.oldPath)?1:0);
  for(const file of selected){
    const path=file.oldPath&&file.newPath&&file.oldPath!==file.newPath?`${quoted(file.oldPath)} → ${quoted(file.newPath)}`:quoted(file.newPath||file.oldPath);
    if(file.unavailableReason){
      const suffix=`${path} unavailable (${quoted(file.unavailableReason)}).`;
      counts.push(`Tests vs base: ${suffix}`);summaries.push(counts.at(-1));
      assertions.push(`Changed assertions in kept tests: ${suffix}`);skips.push(`New skips: ${suffix}`);continue;
    }
    const oldCases=cases(file.before,file.oldLang),newCases=cases(file.after,file.newLang);
    const before=oldCases.filter(c=>!c.suite),after=newCases.filter(c=>!c.suite);
    const oldMap=new Map(oldCases.map(c=>[JSON.stringify([c.suite,key(c)]),c])),newMap=new Map(after.map(c=>[key(c),c]));
    const removed=before.filter(c=>!newMap.has(key(c)));
    const prefix=`Tests vs base: ${path} ${before.length} → ${after.length} tests. Removed: `;
    counts.push(prefix+(removed.length?`${removed.length} (${removed.map(label).join(', ')}).`:'none.'));
    summaries.push(prefix+(removed.length?`${removed.length}.`:'none.'));
    for(const current of newCases){const previous=oldMap.get(JSON.stringify([current.suite,key(current)]));
      if(previous&&!current.suite&&previous.assertions.length*current.assertions.length>1000000)assertions.push(`Changed assertions in kept tests: ${path} ${label(current)} unavailable ("too many assertion lines to compare").`);
      else if(previous&&!current.suite)for(const [oldLine,newLine] of assertionChanges(previous.assertions,current.assertions)) assertions.push(`Changed assertions in kept tests: ${path} ${label(current)} ${oldLine===null?'(added)':quoted(oldLine)} → ${newLine===null?'(removed)':quoted(newLine)}.`);
      for(const line of introduced(previous?.markers??[],current.markers))skips.push(`New skips: ${path} ${current.suite?'suite ':''}${label(current)} ${quoted(line)}.`);
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
    const candidates=records.filter(record=>language(record.oldPath)||language(record.newPath));
    if(candidates.length>MAX_FILES)return {available:false,reason:'inventory limit exceeded',files:[]};
    let bytes=0;const files=[];
    for(const record of candidates){
      const file={...record,before:'',after:''};let pairBytes=0;
      for(const [path,commit,side] of [[record.oldPath,input.baseSha,'before'],[record.newPath,input.headSha,'after']])if(path&&language(path)){
        const object=`${commit}:${path}`,length=Number((await command(['cat-file','-s',object])).toString('ascii').trim());
        if(!Number.isSafeInteger(length)||length<0)throw Error('Invalid blob size');pairBytes+=length;
        if(length>MAX_BLOB){file.unavailableReason=BLOB_REASONS[0];break;}
        const blob=await command(['cat-file','blob',object]);if(blob.length!==length)throw Error('Invalid blob');
        if(blob.includes(0)){file.unavailableReason=BLOB_REASONS[1];break;}
        try{file[side]=new TextDecoder('utf-8',{fatal:true}).decode(blob);}
        catch{file.unavailableReason=BLOB_REASONS[2];break;}
      }
      if(file.unavailableReason){file.before='';file.after='';}
      else {bytes+=pairBytes;if(bytes>MAX_BYTES)return {available:false,reason:'inventory limit exceeded',files:[]};}
      files.push(file);
    }
    return {available:true,reason:'',files};
  }catch{return {available:false,reason:'snapshot unavailable',files:[]};}
}
