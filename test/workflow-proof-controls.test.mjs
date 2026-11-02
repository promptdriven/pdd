import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

function scratch(t) {
  let exists = false; try { exists = readFileSync('src/workflow-prove.mjs','utf8').includes('export async function proveRun'); } catch {}
  assert.equal(exists, true, '#2594 missing API: controls require proveRun');
  const root=mkdtempSync(join(tmpdir(),'pdd-proof-control-'));t.after(()=>rmSync(root,{recursive:true,force:true}));
  cpSync('package.json',join(root,'package.json'));
  cpSync('src',join(root,'src'),{recursive:true});mkdirSync(join(root,'test'),{recursive:true});
  cpSync('test/helpers',join(root,'test/helpers'),{recursive:true});mkdirSync(join(root,'test/runtime'),{recursive:true});
  for(const name of ['workflow-prove','workflow-proof-pr','workflow-pr-labels']) {cpSync(`test/runtime/${name}.json`,join(root,`test/runtime/${name}.json`));cpSync(`test/${name}.vectors.test.mjs`,join(root,`test/${name}.vectors.test.mjs`));}
  cpSync('test/workflow-prove.test.mjs',join(root,'test/workflow-prove.test.mjs'));
  cpSync('test/runtime-check.test.mjs',join(root,'test/runtime-check.test.mjs'));return root;
}
function run(root,path,pattern) {
  const env={...process.env};delete env.NODE_TEST_CONTEXT;
  return spawnSync(process.execPath,['--test',...(pattern?[`--test-name-pattern=${pattern}`]:[]),path],{cwd:root,env,encoding:'utf8',timeout:15000});
}
function replace(root,path,before,after) {const file=join(root,path),original=readFileSync(file,'utf8');assert.ok(original.includes(before),`Control target absent: ${before}`);writeFileSync(file,original.replace(before,after));}
const cases=[
 ['literal causality', 'workflow-prove', 'src/workflow-prove.mjs', "return record.base.expectedFound ? 'proved' : 'wrong-reason';", "return 'proved';"],
 ['head identity', 'workflow-proof-pr', 'src/workflow-pr-evidence.mjs', 'record.headSha !== head.headSha', 'false'],
 ['warning-light issue safety', 'workflow-pr-labels', 'src/workflow-pr-evidence.mjs', "grouped.get('Not fixed yet:').size ? 'Refs'", "false ? 'Refs'"]
];
for(const [label,name,path,before,after] of cases) test(`PROOF-CONTROL: actual ${label} mutation fails approved checks by assertion`,t=>{
  const root=scratch(t),file=`test/${name}.vectors.test.mjs`,baseline=run(root,file);assert.equal(baseline.status,0,baseline.stdout+baseline.stderr);
  replace(root,path,before,after);const mutant=run(root,file);assert.equal(mutant.status,1,mutant.stdout+mutant.stderr);assert.match(mutant.stdout,/ERR_ASSERTION/);assert.match(mutant.stdout,/exact checks failed/);assert.doesNotMatch(mutant.stdout+mutant.stderr,/ERR_MODULE_NOT_FOUND|SyntaxError/);
});
test('PROOF-CONTROL: restored whitespace tokenizer fails existing quoted-summary regression independently of prove admission',t=>{
  const root=scratch(t),file='test/runtime-check.test.mjs',baseline=run(root,file,'RUNTIME-RUNBOOK-QUOTES');assert.equal(baseline.status,0,baseline.stdout+baseline.stderr);
  const path=join(root,file),source=readFileSync(path,'utf8'),start=source.indexOf('function runbookWords(command) {'),end=source.indexOf("test('RUNTIME-RUNBOOK-QUOTES",start);assert.ok(start>=0 && end>start);writeFileSync(path,source.slice(0,start)+'function runbookWords(command) { return command.split(/\\s+/); }\n\n'+source.slice(end));
  const mutant=run(root,file,'RUNTIME-RUNBOOK-QUOTES');assert.equal(mutant.status,1,mutant.stdout+mutant.stderr);assert.match(mutant.stdout,/RUNTIME-RUNBOOK-QUOTES/);assert.match(mutant.stdout,/ERR_ASSERTION/);assert.doesNotMatch(mutant.stdout+mutant.stderr,/workflow prove|ERR_MODULE_NOT_FOUND/);
});

for (const [label, before, after] of [
  ['committed binary bytes', "await git(root,['cat-file','blob',match[2]],null)", "Buffer.from((await git(root,['cat-file','blob',match[2]],null)).toString('utf8'))"],
  ['executable mode', "match[1]==='100755'?0o755:0o644", '0o644']
]) test(`PROOF-CONTROL: native ${label} mutation fails the real-Git overlay assertion`,t=>{
  const root=scratch(t),file='test/workflow-prove.test.mjs',baseline=run(root,file,'PROVE-NATIVE2');assert.equal(baseline.status,0,baseline.stdout+baseline.stderr);
  const path=join(root,'src/workflow-prove.mjs'),source=readFileSync(path,'utf8');assert.ok(source.includes(before));writeFileSync(path,source.replaceAll(before,after));
  const mutant=run(root,file,'PROVE-NATIVE2');assert.equal(mutant.status,1,mutant.stdout+mutant.stderr);assert.match(mutant.stdout,/ERR_ASSERTION/);assert.doesNotMatch(mutant.stdout+mutant.stderr,/ERR_MODULE_NOT_FOUND|SyntaxError/);
});
