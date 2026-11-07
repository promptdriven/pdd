// Implements prompts/cli/interface-draft.prompt.md.
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join, relative, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { gitFiles, findTests, readPrompt, promptRefusal, interfaceBlocks, interfaceSchemaProblems, proseSha256, sourceFilePort, sha256 } from './runtime-preflight.mjs';
import { loadRuntimeWorkspace, allowsRuntimePath, nativeWorkspaceFiles } from './runtime-workspace.mjs';

function promptPaths(root) {
  const found = findTests({root, excludeFixtureProjects:true});
  return [...found.discoveryVisible].filter(path => path.endsWith('.prompt.md')).sort();
}
export function missingInterfaces(root) {
  return promptPaths(root).filter(path => !interfaceBlocks(sourceFilePort(root).read({path}).content).length);
}
export function interfaceFindings({root, paths = promptPaths(root)}) {
  const visible = new Set(gitFiles(root));
  return paths.flatMap(path => {
    try {
      const prompt = readPrompt(root, visible, path), problem = promptRefusal(prompt, 'interface');
      if (problem) return [{...problem, path}];
      return interfaceSchemaProblems(prompt.interface).map(item => ({code:item.code,path,section:item.pointer,message:`${path} ${item.pointer} ${item.rule}`}));
    } catch (error) { return [{code:error.code ?? 'interface-unreadable',path,message:error.message}]; }
  });
}
export function runtimeCoverage({root, paths = promptPaths(root)}) {
  const visible = new Set(gitFiles(root));
  let checkable = 0, native_only = 0;
  for (const path of paths) {
    try {
      const prompt = readPrompt(root,visible,path);
      if (promptRefusal(prompt,'interface') || interfaceSchemaProblems(prompt.interface).length) continue;
      if (prompt.interface.kind === 'native-only') native_only++;
      else if (Array.isArray(prompt.interface.entries) && prompt.interface.entries.length) checkable++;
    } catch { /* Missing and invalid source remains in the denominator. */ }
  }
  return {checkable,total:paths.length,native_only};
}

const git = (root,args,bytes=false) => {
  const result=spawnSync('git',args,{cwd:root,encoding:bytes ? undefined : 'utf8',stdio:['ignore','pipe','pipe'],maxBuffer:32*1024*1024});
  if (result.status !== 0) throw Error('Cannot read repository source.');
  return result.stdout;
};
function rootFor(cwd) { return git(cwd,['rev-parse','--show-toplevel']).trim(); }
const metadataFile = root => join(root,'.pdd/interface-drafts.json');
function drafts(root) {
  try { return JSON.parse(readFileSync(metadataFile(root),'utf8')); }
  catch(error) { if(error.code==='ENOENT') return {}; throw Error('Cannot read interface draft provenance.'); }
}
function saveDrafts(root, records) {
  mkdirSync(join(root,'.pdd'),{recursive:true});
  // This local folder must also stay ignored in projects that have not run setup.
  try { writeFileSync(join(root,'.pdd/.gitignore'),'*\n',{flag:'wx'}); } catch(error) {if(error.code!=='EEXIST') throw error;}
  writeFileSync(metadataFile(root),JSON.stringify(records,null,2)+'\n');
}
function jsonDeclarations(text) {
  const values=[];
  try {values.push(JSON.parse(text));} catch { /* Markdown is read below. */ }
  for(const match of text.matchAll(/```json\s*\n([\s\S]*?)\n```/g)) {
    try {values.push(JSON.parse(match[1]));} catch { /* Examples with placeholders are not schemas. */ }
  }
  return values.filter(value => value && typeof value==='object' && !Array.isArray(value));
}
function inferInterface(root,path,text) {
  const files=sourceFilePort(root), sources=[{path,text}];
  // Only declared dependencies can supply schema facts. Never read arbitrary links or code as context.
  const section=/^## Dependencies\s*\n([\s\S]*?)(?=^## |$(?![\s\S]))/m.exec(text)?.[1] ?? '';
  for(const link of section.matchAll(/\[([^\]]*)\]\(([^)\s]+)\)/g)) {
    if(/^[a-z]+:|^\//i.test(link[2]) || !/schema|contract|interface|api/i.test(link[1]+' '+link[2])) continue;
    const target=relative(root,resolve(root,join(path,'..'),link[2].split('#')[0])).split('\\').join('/');
    if(target.endsWith('.prompt.md')) continue; // Another module's interface is not this module's API.
    sources.push({path:target,text:files.read({path:target}).content});
  }
  const declarations=sources.flatMap(source=>jsonDeclarations(source.text));
  const candidates=declarations.filter(value=>Array.isArray(value.entries) && value.entries.length
    && value.entries.every(entry=>typeof entry?.operation==='string' && entry.input_schema && entry.result_schema));
  let iface;
  if(candidates.length===1) {
    const value=candidates[0];
    iface={...value,kind:value.kind ?? 'full',status:'draft',prose_sha256:'',calls:value.calls ?? [],resources:value.resources ?? [],limits:value.limits ?? {max_steps:1000,max_model_calls:1000}};
    if(iface.kind==='native-only') throw Error('Drafting cannot choose native-only. Declare and review its reason.');
  } else {
    const operations=[...text.matchAll(/\b(?:Export|export|exports)\s+(?:(?:async|module|function)\s+)*`?([A-Za-z_$][\w$]*)\s*\(/g)].map(match=>match[1]);
    // An explicitly owned source file can add clear exported function names, never schemas.
    const own=/`(src\/[\w./-]+\.[cm]js)`/.exec(text)?.[1];
    if(own) {
      const code=files.read({path:own}).content;
      for(const match of code.matchAll(/^export\s+(?:async\s+)?function\s+([\w$]+)\s*\(/gm)) operations.push(match[1]);
    }
    iface={kind:'partial',status:'draft',prose_sha256:'',entries:[...new Set(operations)].map(operation=>({operation})),calls:[],resources:[],limits:{max_steps:1000,max_model_calls:1000},
      draft_gaps:[candidates.length>1 ? 'More than one interface declaration is present; select the owning contract.' : 'Declare complete input_schema and result_schema for each public operation. Review calls, resources and limits against the prompt.']};
  }
  return iface;
}
export async function runInterfaceDraft({words=[],all=false,json=false,cwd=process.cwd()}={},ports={}) {
  const stdout=ports.stdout ?? process.stdout,stderr=ports.stderr ?? process.stderr;
  try {
    if(all && words.length || !all && !words.length) throw Error('Use pdd interface draft PROMPT... or pdd interface draft --all.');
    const root=rootFor(cwd),workspace=loadRuntimeWorkspace({root}),visible=new Set(gitFiles(root));
    const paths=all ? promptPaths(root) : [...new Set(words.map(word=>relative(root,resolve(cwd,word)).split('\\').join('/')))];
    const files=sourceFilePort(root,visible,workspace);
    // Validate the entire selection before any mutation.
    for(const path of paths) {
      if(!path.endsWith('.prompt.md') || !visible.has(path) || !allowsRuntimePath(workspace,path)) throw Error(`Not a workspace prompt: ${path}`);
      nativeWorkspaceFiles(root).stat({path});
      files.read({path});
    }
    const records=drafts(root),rows=[];
    for(const path of paths) {
      try {
        const text=files.read({path}).content;
        if(interfaceBlocks(text).length) {rows.push({path,state:'existing'});continue;}
        if(/<summary[^>]*>\s*(?:<strong[^>]*>\s*)?Runtime\s+interface/i.test(text)) throw Error('The Runtime interface block is malformed. Fix it before drafting.');
        const iface=inferInterface(root,path,text);
        // All whitespace outside the block is original prose, including its final newline.
        const render=()=>text+'<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify(iface,null,2)+'\n```\n</details>';
        iface.prose_sha256=proseSha256(render());
        const next=render();
        records[path]={head:git(root,['rev-parse','HEAD']).trim(),original_sha256:sha256(text),prose_sha256:iface.prose_sha256,interface_sha256:sha256(JSON.stringify(iface))};
        writeFileSync(join(root,path),next);
        rows.push({path,state:'drafted'});
      } catch(error) {rows.push({path,state:'refused',problems:[{code:error.code ?? 'interface-draft-failed',message:error.message}]});}
    }
    if(rows.some(row=>row.state==='drafted')) saveDrafts(root,records);
    for(const row of rows) {
      row.problems ??= interfaceFindings({root,paths:[row.path]});
      row.lint_clean=row.problems.length===0;
    }
    const summary={drafted:rows.filter(row=>row.state==='drafted').length,existing:rows.filter(row=>row.state==='existing').length,lint_clean:rows.filter(row=>row.lint_clean).length,refused:rows.filter(row=>row.problems.length).length,total:rows.length};
    const exit_code=summary.refused ? 4 : 0;
    stdout.write(json ? JSON.stringify({exit_code,summary,rows})+'\n' : [...rows.map(row=>`${row.path}: ${row.state}; ${row.lint_clean ? 'lint clean' : row.problems.map(item=>`${item.code}: ${item.message}`).join('; ')}`),`Interfaces: ${summary.drafted} drafted, ${summary.existing} existing, ${summary.lint_clean} lint clean, ${summary.refused} refused. 0 AI calls.`].join('\n')+'\n');
    return exit_code;
  } catch(error) {stderr.write(`${error.message}\n`);return 2;}
}

