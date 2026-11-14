// Generated from prompts/cli/product-drafts.prompt.md (sha256: 10a9a4319d28745b35112fea62581c59b8ccac86675122f313d15d47c5b63d7e).
import { execFileSync } from 'node:child_process';
import { readdirSync, realpathSync } from 'node:fs';
import { join, posix } from 'node:path';
import { readRun } from '../workflow-runs.mjs';
import { gitFiles } from './runtime-preflight.mjs';
import { markdownDefinitions, markdownLinks, markdownSectionText } from './runtime-markdown.mjs';

const bad = message => { throw Object.assign(Error(message), {code:'invalid-product-map'}); };
const git = (root, args) => execFileSync('git', args, {cwd:root, encoding:'utf8', stdio:['ignore','pipe','pipe']}).trim();
const common = root => realpathSync(git(root, ['rev-parse','--path-format=absolute','--git-common-dir']));
const overlaps = (a,b) => a === b || a.startsWith(`${b}/`) || b.startsWith(`${a}/`);

export function withProductDrafts({root, parts, snapshot, parseProductDocuments, captureSource}, prepare) {
  const readOptional = path => snapshot.statFile(path).exists ? snapshot.readFile(path).toString('utf8') : '';
  const {product} = parseProductDocuments({mapText:readOptional('product/map.md'), planText:readOptional('product/plan.md')});
  const selected = parts === undefined ? product.parts.map(p=>p.part) : parts;
  if (!selected.length || new Set(selected).size !== selected.length || selected.some(p=>!product.parts.some(row=>row.part===p))) {
    throw Object.assign(Error(`Choose distinct product parts from: ${product.parts.map(p=>p.part).join(', ')}.`),{code:'invalid-product'});
  }
  const declared = product.parts.filter(p=>selected.includes(p.part)).map(p=>({...p,folder:p.folder.replace(/\/$/,'')}));
  let dir;
  try { dir=common(root); } catch { return prepare(snapshot, []); }
  let entries=[];
  try { entries=readdirSync(join(dir,'pdd','runs')); } catch (error) { if(error.code!=='ENOENT') throw error; }
  const drafts=[];
  for (const entry of entries.filter(name=>/^[1-9][0-9]*$/.test(name))) {
    const run=readRun(join(dir,'pdd','runs',entry));
    if (!run || run.workflow!=='feature' || ['completed','cancelled'].includes(run.state)) continue;
    const planned=product.runs.find(p=>run.productMarker===`<!-- pdd-product: run=${p.run} -->` && p.part!=='all' && selected.includes(p.part));
    if(!planned) continue;
    const part=declared.find(p=>p.part===planned.part);
    drafts.push({...part, run, map:`app/maps/${part.part}.json`});
  }
  for(const d of drafts) {
    const conflicts=drafts.filter(other=>other.part===d.part);
    if(conflicts.length>1) bad(`Part ${d.part} has multiple active drafts: ${conflicts.map(x=>`${x.run.runId} (${x.run.root})`).join(', ')}. Complete or end the drafts.`);
    try { if(common(d.run.root)!==dir) throw Error(); } catch { bad(`Part ${d.part}: checkout ${d.run.root} is not in this Git repository. Complete or end the draft.`); }
  }
  if(!drafts.length) return prepare(snapshot,[]);
  for (const [i,a] of declared.entries()) for (const b of declared.slice(i+1)) if (overlaps(a.folder,b.folder)) bad(`Parts ${a.part} (${a.folder}) and ${b.part} (${b.folder}) have overlapping prompt folders.`);
  const claims=new Map(), files=[];
  const own=(d,path) => {
    const prior=claims.get(path);
    if(prior && prior!==d.part) bad(`Parts ${prior} and ${d.part} both own ${path}. Complete or end the drafts.`);
    for(const other of declared) if(other.part!==d.part && (overlaps(path,other.folder) || overlaps(path,`app/maps/${other.part}.json`))) bad(`Parts ${d.part} and ${other.part} have conflicting paths ${path} and ${other.folder}.`);
    claims.set(path,d.part);
  };
  const enter = index => {
    if(index===drafts.length) {
      const overlay=new Map(files.map(f=>[f.path,f.bytes]));
      const owner=path=>drafts.find(d=>path===d.folder || path.startsWith(d.folder+'/') || path===d.map) || (claims.has(path) ? drafts.find(d=>d.part===claims.get(path)) : null);
      const combined={validateCapture(sources){ for(const file of sources) { const d=owner(file.path); if(d && !overlay.has(file.path)) bad(`Part ${d.part}: ${file.path} is missing from its draft. Complete or end the draft.`); } },statFile(path,options){if(overlay.has(path)) return {exists:true,is_symlink:false,size:overlay.get(path).length}; const d=owner(path); if(d) { if(path===d.map || path===`prompts/${d.part}/seed.json`) return {exists:false,is_symlink:false,size:0}; bad(`Part ${d.part}: ${path} is missing from its draft. Complete or end the draft.`); } return snapshot.statFile(path,options);},
        readFile(path){if(overlay.has(path)) return Buffer.from(overlay.get(path)); const d=owner(path); if(d) bad(`Part ${d.part}: ${path} is missing from its draft. Complete or end the draft.`); return snapshot.readFile(path);}};
      return prepare(combined,files);
    }
    const d=drafts[index]; let result;
    const savedFiles=files.slice(), savedClaims=new Map(claims);
    captureSource(d.run.root,{tests:[],appMap:null,prepareSource(source){
      files.splice(0,files.length,...savedFiles); claims.clear(); for(const [path,part] of savedClaims) claims.set(path,part);
      const visible=gitFiles(d.run.root), paths=visible.filter(path=>path.startsWith(`${d.folder}/`));
      const add=path=>{
        own(d,path);
        if(files.some(f=>f.path===path)) return;
        try { if(!source.statFile(path).exists) bad(`Part ${d.part}: ${path} is missing from its draft. Complete or end the draft.`); files.push({path,bytes:source.readFile(path)}); }
        catch(error) { if(error.code==='invalid-product-map') throw error; bad(`Part ${d.part}: ${path}: ${error.message} Complete or end the draft.`); }
      };
      for(const path of paths) { if(source.statFile(path).exists) add(path); }
      if(!paths.some(path=>path.endsWith('.prompt.md') && files.some(f=>f.path===path))) bad(`Part ${d.part}: ${d.folder} has no draft prompt. Complete or end the draft.`);
      if(source.statFile(d.map).exists) add(d.map); else if(snapshot.statFile(d.map).exists) bad(`Part ${d.part}: ${d.map} is missing from its draft. Complete or end the draft.`);
      const mapFile=files.find(f=>f.path===d.map);
      if(mapFile) { let map; try {map=JSON.parse(mapFile.bytes.toString('utf8'));} catch {bad(`Part ${d.part}: ${d.map} is invalid JSON. Complete or end the draft.`);}
        for(const path of [...(map.stylesheets ?? []),...(map.screens ?? []).filter(s=>s.source==='mockup').map(s=>s.prompt_path)]) if(typeof path==='string' && path.startsWith('views/')) add(path);
      }
      for(let i=0;i<files.length;i++) { const file=files[i]; if(claims.get(file.path)!==d.part || !file.path.endsWith('.md')) continue;
        const text=markdownSectionText(file.bytes.toString('utf8'));
        for(const raw of markdownLinks(text,markdownDefinitions(text))) { if(!raw || raw.startsWith('#') || /^(?:[a-z][a-z0-9+.-]*:|\/\/)/i.test(raw)) continue;
          let target; try {target=decodeURIComponent(raw.split('#')[0]);} catch {continue;}
          let path=posix.normalize(posix.join(posix.dirname(file.path),target));
          if(!visible.includes(path) && visible.includes(target.replace(/^\.\//,''))) path=target.replace(/^\.\//,'');
          if(path.startsWith('views/')) add(path);
        }
      }
      result=enter(index+1); return [];
    }});
    return result;
  };
  return enter(0);
}
