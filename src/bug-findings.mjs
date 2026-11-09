import { constants, lstatSync, openSync, closeSync, readFileSync, realpathSync } from 'node:fs';
import { isAbsolute, join, relative, sep } from 'node:path';

const invalid = field => { throw Object.assign(new Error(`bug-findings-invalid: ${field}`), { code: 'bug-findings-invalid' }); };
const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const keys = (x, list, field) => { if (!object(x) || Object.keys(x).length !== list.length || list.some(k => !Object.hasOwn(x,k))) invalid(field); };
const positive = x => Number.isSafeInteger(x) && x > 0;
const text = x => typeof x === 'string' && x.trim().length > 0;
const repository = x => typeof x === 'string' && /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(x);
function pathSafe(path, root, field) {
  if (!text(path) || isAbsolute(path) || path.includes('\\') || path.split('/').some(p => !p || p === '.' || p === '..')) invalid(field);
  let current = root;
  for (const part of path.split('/')) {
    current = join(current, part);
    try { const resolved = realpathSync(current), rel = relative(realpathSync(root), resolved); if (rel === '..' || rel.startsWith(`..${sep}`) || isAbsolute(rel)) invalid(field); }
    catch (error) { if (error.code === 'bug-findings-invalid') throw error; if (error.code !== 'ENOENT') invalid(field); try { if (lstatSync(current).isSymbolicLink()) invalid(field); } catch (e) { if (e.code === 'bug-findings-invalid') throw e; if (e.code !== 'ENOENT') invalid(field); } }
  }
}
// JSON.parse does not report repeated keys. Scan the JSON grammar before parsing it.
function uniqueJson(source) {
  let i=0; const ws=()=>{while (/\s/.test(source[i] ?? '') && i<source.length) i++;};
  function string(){const start=i++; while(i<source.length){if(source[i]==='\\'){i+=2;continue;} if(source[i++]==='"') return JSON.parse(source.slice(start,i));} throw Error();}
  function value(){ws(); if(source[i]==='"'){string();return;} if(source[i]==='{'){i++;ws();const seen=new Set();if(source[i]==='}'){i++;return;} while(true){ws();if(source[i]!== '"')throw Error();const k=string();if(seen.has(k)) invalid('json duplicate key');seen.add(k);ws();if(source[i++]!==':')throw Error();value();ws();const c=source[i++];if(c==='}')return;if(c!==',')throw Error();}} else if(source[i]==='['){i++;ws();if(source[i]===']'){i++;return;}while(true){value();ws();const c=source[i++];if(c===']')return;if(c!==',')throw Error();}} else {const m=/^(?:true|false|null|-?(?:0|[1-9]\d*)(?:\.\d+)?(?:[eE][+-]?\d+)?)/.exec(source.slice(i));if(!m)throw Error();i+=m[0].length;}}
  value();ws();if(i!==source.length)throw Error();return JSON.parse(source);
}
export function readBugFindings(run) {
  const file=join(run.runDir,'bug-findings.json'); let bytes;
  try { const st=lstatSync(file); if(!st.isFile() || st.isSymbolicLink()) invalid('file'); const fd=openSync(file,constants.O_RDONLY|constants.O_NOFOLLOW); try { bytes=readFileSync(fd); } finally { closeSync(fd); } }
  catch(e){if(e.code==='ENOENT')return null;if(e.code==='bug-findings-invalid')throw e;throw Object.assign(Error('bug-findings-unavailable'),{code:'bug-findings-unavailable'});}
  let input; try { input=uniqueJson(new TextDecoder('utf-8',{fatal:true}).decode(bytes)); } catch(e){if(e.code==='bug-findings-invalid')throw e;invalid('json');}
  keys(input,['version','runId','repository','issue','reproduced','cause','search','relations'],'input');
  if(input.version!==1)invalid('version'); if(input.runId!==run.runId)invalid('runId'); if(!repository(input.repository)||input.repository!==run.repo)invalid('repository'); if(input.issue!==run.number)invalid('issue');
  if(typeof input.reproduced!=='boolean')invalid('reproduced'); if(!['complete','unavailable'].includes(input.search))invalid('search'); if(!Array.isArray(input.relations))invalid('relations');
  if(input.reproduced){keys(input.cause,['file','function','flaw','class'],'cause');pathSafe(input.cause.file,run.root,'cause.file'); for(const k of ['function','flaw','class'])if(!text(input.cause[k]))invalid(`cause.${k}`);} else if(input.cause!==null||input.relations.length) invalid('cause');
  for(const r of input.relations){
    keys(r,['issue','classification','quote','source','effect'],'relations'); if(!positive(r.issue)||r.issue===run.number)invalid('relations.issue'); if(!['needs','same cause','same class','duplicate','related'].includes(r.classification))invalid('relations.classification'); if(!text(r.quote))invalid('relations.quote');
    const s=r.source; if(!object(s))invalid('relations.source'); const sk={issue:['kind','repository','issue','revision'],comment:['kind','repository','issue','comment','revision'],code:['kind','repository','path','revision']}[s.kind]; if(!sk)invalid('relations.source.kind');keys(s,sk,'relations.source');if(s.repository!==run.repo||!text(s.revision))invalid('relations.source');if(s.kind==='code')pathSafe(s.path,run.root,'relations.source.path'); else if(!positive(s.issue)||![run.number,r.issue].includes(s.issue)||(s.kind==='comment'&&!positive(s.comment)))invalid('relations.source.issue');
    const e=r.effect;if(!object(e))invalid('relations.effect');const ek={none:['kind'],'blocked-by':['kind','dependent','blocker'],'sub-issue':['kind','parent','child'],duplicate:['kind','duplicate','canonical']}[e.kind];if(!ek)invalid('relations.effect.kind');keys(e,ek,'relations.effect'); for(const k of ek.slice(1))if(!positive(e[k]))invalid(`relations.effect.${k}`);
  }
  return { input, bytes: bytes.toString('base64') };
}
