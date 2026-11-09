// Generated from prompts/cli/interface-draft.prompt.md (sha256: 7741e4062edd0c8c7e06a97f545241fcf13c8b57d5060af6ad700aa32c69afb0).
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
      if (!prompt.interface) return [{...problem,path}];
      const schema=interfaceSchemaProblems(prompt.interface).map(item => ({code:item.code,path,section:item.pointer,message:`${path} ${item.pointer} ${item.rule}`}));
      return problem && !schema.some(item=>item.code===problem.code) ? [{...problem,path},...schema] : schema;
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
      else if (Array.isArray(prompt.interface.entries) && prompt.interface.entries.length && prompt.interface.entries.every(entry=>typeof entry?.operation==='string' && entry.operation.trim() && entry.input_schema && entry.result_schema)) checkable++;
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
    iface={...value,kind:Object.hasOwn(value,'kind') ? value.kind : 'full',status:'draft',prose_sha256:''};
    const missing=['calls','resources','limits'].filter(key=>!Object.hasOwn(value,key));
    if(missing.length) {
      iface.kind='partial';
      iface.draft_gaps=[...(Array.isArray(iface.draft_gaps) ? iface.draft_gaps : []),`Declare ${missing.join(', ')} from the owning contract.`];
    }
    if(iface.kind==='native-only') throw Error('Drafting cannot choose native-only. Declare and review its reason.');
  } else {
    const operations=[...text.matchAll(/\b(?:Export|export|exports)\s+(?:(?:async|module|function)\s+)*`?([A-Za-z_$][\w$]*)\s*\(/g)].map(match=>match[1]);
    // An explicitly owned source file can add clear exported function names, never schemas.
    const own=/`(src\/[\w./-]+\.[cm]js)`/.exec(text)?.[1];
    if(own) {
      const code=files.read({path:own}).content;
      for(const match of code.matchAll(/^export\s+(?:async\s+)?function\s+([\w$]+)\s*\(/gm)) operations.push(match[1]);
    }
    iface={kind:'partial',status:'draft',prose_sha256:'',entries:[...new Set(operations)].map(operation=>({operation})),
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

// Automatic approval runs its own native tests and prompt check; callers cannot supply a pass receipt.
function sourceSnapshot(root) {
  const files=sourceFilePort(root);
  return Object.fromEntries(gitFiles(root).filter(path=>!path.startsWith('.pdd/')).map(path=>{files.stat({path});return [path,sha256(readFileSync(join(root,path)))];}));
}
function nativeTestArgs(root,command,head) {
  if(typeof command!=='string' || !command.trim()) throw Error('Name the existing native tests with --tests COMMAND.');
  const words=command.trim().split(/\s+/);
  if(words[0]==='node' && words[1]==='--test' && words.length>2 && words.slice(2).every(path=>/^[\w./-]+\.(?:[cm]js|ts)$/.test(path) && !path.startsWith('-') && /(?:^|\/)tests?\/|\.(?:test|spec)\.[cm]?[jt]s$/.test(path))) {
    for(const path of words.slice(2)) git(root,['show',`${head}:${path}`]);
    return [process.execPath,['--test-reporter=tap',...words.slice(1)]];
  }
  if(words[0]==='npm' && (words.length===2 && words[1]==='test' || words.length===3 && words[1]==='run')) {
    const name=words[1]==='test' ? 'test' : words[2], pkg=JSON.parse(git(root,['show',`${head}:package.json`]));
    if(/^(?:test|test:.+)$/.test(name) && typeof pkg.scripts?.[name]==='string' && pkg.scripts[name].trim()) return ['npm',words.slice(1)];
  }
  throw Error('Use existing committed tests: node --test TEST... or npm test or npm run SCRIPT.');
}
export async function runAutomaticApproval({path,root,tests},ports={}) {
  const stdout=ports.stdout ?? process.stdout,stderr=ports.stderr ?? process.stderr;
  try {
    const {readApprovalPolicy,approvalActor,recordPromptApproval,readPromptApprovals}=await import('./approval-policy.mjs');
    const {approvePromptText,promptPath}=await import('./prompt-approve.mjs');
    const {runCheck}=await import('./runtime-client.mjs');
    const {randomUUID}=await import('node:crypto');
    if(readApprovalPolicy({root},ports).strictApprovals) throw Error('Strict approvals require a person at a terminal.');
    if(!promptPath(root,root,path)) throw Error('Name one Git-visible regular prompt.');
    const file=join(root,path),text=readFileSync(file,'utf8'),blocks=interfaceBlocks(text);
    if(blocks.length!==1) throw Error('Draft a Runtime interface before automatic approval.');
    const records=drafts(root),iface=JSON.parse(blocks[0][1]),record=records[path];
    if(!record || iface.status!=='draft' || iface.kind==='native-only' || interfaceFindings({root,paths:[path]}).length || !iface.entries?.length)
      throw Error('Automatic approval needs a complete draft made by pdd interface draft.');
    if(sha256(JSON.stringify(iface))!==record.interface_sha256 || proseSha256(text)!==record.prose_sha256 || record.original_sha256!==sha256(text.replace(blocks[0][0],'')))
      throw Error('The draft changed. Ask a person to approve the new contract.');
    const head=git(root,['rev-parse','HEAD']).trim();
    if(sha256(git(root,['show',`${record.head}:${path}`]))!==record.original_sha256)
      throw Error('The committed prompt changed or this draft includes new behavior. Ask a person.');
    const before=sourceSnapshot(root),committed=git(root,['ls-tree','-r','--name-only','-z',record.head]).split('\0').filter(Boolean);
    for(const name of new Set([...Object.keys(before),...committed])) {
      if(name.startsWith('.pdd/')) continue;
      let expected=name===path ? record.original_sha256 : before[name];
      const other=records[name];
      if(name!==path && other?.head===record.head && name.endsWith('.prompt.md') && before[name]) {
        const otherText=readFileSync(join(root,name),'utf8'),otherBlocks=interfaceBlocks(otherText);
        if(otherBlocks.length===1) {
          const value=JSON.parse(otherBlocks[0][1]);
          if(['draft','approved'].includes(value.status) && sha256(otherText.replace(otherBlocks[0][0],''))===other.original_sha256
            && sha256(JSON.stringify({...value,status:'draft'}))===other.interface_sha256) expected=other.original_sha256;
        }
      }
      if(!committed.includes(name) || expected===undefined || sha256(git(root,['show',`${record.head}:${name}`],true))!==expected)
        throw Error('Automatic approval needs unchanged committed source and existing tests.');
    }
    const [program,args]=nativeTestArgs(root,tests,head);
    const native=ports.runNativeTests ? await ports.runNativeTests(program,args,{cwd:root})
      : await new Promise((done,reject)=>{
        import('node:child_process').then(({execFile})=>execFile(program,args,{cwd:root,env:ports.env ?? process.env,maxBuffer:16*1024*1024},(error,out,err)=>{
          if(error && typeof error.code!=='number') reject(error);else done({code:error?.code ?? 0,stdout:out,stderr:err});
        }));
      });
    if(native.code!==0) throw Error('Existing native tests did not pass. No prompt was approved.');
    const count = key => {const matches=[...(native.stdout ?? '').matchAll(new RegExp(`^# ${key} (\\d+)\\s*$`,'gm'))];return matches.length===1 ? Number(matches[0][1]) : null;};
    const nativeCounts={total:count('tests'),passed:count('pass'),failed:count('fail')};
    if(!(nativeCounts.total>0) || nativeCounts.passed!==nativeCounts.total || nativeCounts.failed!==0) throw Error('The native command did not report a complete passing TAP test run.');
    if(JSON.stringify(sourceSnapshot(root))!==JSON.stringify(before)) throw Error('Source changed during native tests. No prompt was approved.');
    const found=findTests({root,excludeFixtureProjects:true});
    // Follow calls too: every scenario that can reach the drafted contract must pass in full.
    const reaches=(entry,seen=new Set())=>{
      if(entry===path) return true;
      if(typeof entry!=='string' || seen.has(entry)) return false;
      seen.add(entry);
      const prompt=readPrompt(root,found.visible,entry);
      return (prompt.interface?.calls ?? []).some(call=>reaches(call.target,seen));
    };
    const affected=found.tests.filter(test=>(test.doc?.steps ?? []).some(step=>reaches(step.entry_path)));
    const stories=new Set(affected.map(test=>test.storyPath ?? test.story));
    const selected=found.tests.filter(test=>stories.has(test.storyPath ?? test.story));
    if(!selected.length || selected.some(test=>test.error)) throw Error('No complete existing prompt tests cover this draft.');
    let output='';
    const checkPorts={...ports,stdout:{write:chunk=>{output+=chunk;}},stderr};
    const code=await runCheck({cwd:root,words:selected.map(test=>test.path),options:{'--json':true},cache:false},checkPorts);
    let result;try {result=JSON.parse(output);}catch {throw Error('Prompt check evidence is unavailable.');}
    const complete=code===0 && result.exit_code===0 && result.rows?.length===selected.length && selected.every(test=>{
      const row=result.rows.find(row=>row.test===test.path),checks=test.doc.steps.reduce((sum,step)=>sum+(step.checks?.length ?? 0),0);
      return row?.state==='passed' && !row.cached && !row.native_only?.length && !row.time_limit && !row.refusals?.length
        && row.criteria?.passed===test.doc.criteria.length && row.criteria?.total===test.doc.criteria.length
        && row.checks?.passed===checks && row.checks?.total===checks;
    });
    if(!complete) throw Error('The prompt check did not pass every current test, criterion and check.');
    if(JSON.stringify(sourceSnapshot(root))!==JSON.stringify(before) || git(root,['rev-parse','HEAD']).trim()!==head || readFileSync(file,'utf8')!==text)
      throw Error('Source changed during checking. No prompt was approved.');
    const commonDir=git(root,['rev-parse','--path-format=absolute','--git-common-dir']).trim();
    readPromptApprovals({commonDir},ports);
    const next=approvePromptText(text);
    if(!next) throw Error('The prompt could not be approved safely.');
    const evidence={id:(ports.randomUUID ?? randomUUID)(),route:'automatic-check-pass',actor:approvalActor(ports.env ?? process.env),at:(ports.now ?? Date.now)(),words:null,
      prompts:[{path,proseSha256:record.prose_sha256,kind:iface.kind ?? 'full'}],checks:{native:{command:tests,exit_code:native.code,counts:nativeCounts},prompt:result,head,source:before,draft:record}};
    try {
      writeFileSync(file,next);
      await recordPromptApproval({commonDir,evidence},ports);
    } catch(error) {writeFileSync(file,text);throw error;}
    stdout.write(`Approved ${path}. Approval route: automatic-check-pass.\n`);
    return 0;
  } catch(error) {stderr.write(`${error.message}\n`);return 4;}
}
