import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readdirSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { runPdd } from '../src/pdd-cli.mjs';

const bin=fileURLToPath(new URL('../bin/pdd.mjs',import.meta.url));
const capture=()=>({text:'',write(chunk){this.text+=chunk;}});
const forbidden=()=>assert.fail('Help must not invoke native/workflow/definition operations');

test('preview help is local and truthful for root and exact run/resume/attach without admitting a workflow',async()=>{
 const forms=[[],['--help'],['-h'],['help'],['workflow','--help']];
 for(const command of ['run','resume','attach'])forms.push(['workflow',command,'--help'],['workflow',command,'-h'],['help','workflow',command]);
 for(const words of forms){
  const stdout=capture(),stderr=capture();
  const exit=await runPdd(words,{stdout,stderr,cwd:'/missing/project',packageRoot:'/missing/package',nativeSession:forbidden,
   workflowRunner:new Proxy({},{get:forbidden}),workflowStages:new Proxy({},{get:forbidden}),workflowDefinitions:{listWorkflowDefinitions:forbidden}});
  assert.equal(exit,0,words.join(' '));assert.equal(stderr.text,'');
  assert.match(stdout.text,/workflow runner PREVIEW/i);assert.match(stdout.text,/real workflow PR is not yet proven/i);
  if(words[0]==='workflow'&&['run','resume','attach'].includes(words[1])){
   const description=stdout.text.split('\n').find(line=>line.startsWith('  pdd workflow '+words[1]+' '));
   assert.ok(description?.includes('PREVIEW:'),words.join(' '));
  }
  assert.match(stdout.text,/may push branches and create real PRs/);
 }
 const stdout=capture();assert.equal(await runPdd(['session','--help'],{stdout,stderr:capture(),nativeSession:forbidden}),0);
 assert.doesNotMatch(stdout.text,/workflow runner PREVIEW/i);
});

test('actual public bin preview help works offline in empty consumer folder; unrelated invalid input remains finite',t=>{
 const cwd=mkdtempSync(join(tmpdir(),'pdd-preview-help-'));t.after(()=>rmSync(cwd,{recursive:true,force:true}));
 const before=readdirSync(cwd);
 for(const words of [['--help'],['workflow','run','--help'],['workflow','resume','--help'],['workflow','attach','--help']]){
  const result=spawnSync(process.execPath,[bin,...words],{cwd,env:{...process.env,HOME:cwd,PATH:''},encoding:'utf8',timeout:5000});
  assert.equal(result.status,0,result.stderr);assert.equal(result.stderr,'');assert.match(result.stdout,/PREVIEW/);assert.match(result.stdout,/real workflow PR is not yet proven/);
 }
 const unknown=spawnSync(process.execPath,[bin,'not-a-command','--help'],{cwd,env:{...process.env,HOME:cwd,PATH:''},encoding:'utf8',timeout:5000});
 assert.equal(unknown.status,2);assert.equal(unknown.stdout,'');assert.match(unknown.stderr,/unsupported|unknown/i);
 assert.deepEqual(readdirSync(cwd),before);
});
