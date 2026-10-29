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

test('launch help is local and keeps the PR warning for root and every runner route without admitting a workflow',async()=>{
 const forms=[[],['--help'],['-h'],['help'],['workflow','--help']];
 for(const command of ['run','done','approve','changes','cancel','status','open'])forms.push(['workflow',command,'--help'],['workflow',command,'-h'],['help','workflow',command]);
 for(const words of forms){
  const stdout=capture(),stderr=capture();
  const exit=await runPdd(words,{stdout,stderr,cwd:'/missing/project',packageRoot:'/missing/package',
   workflowRunner:new Proxy({},{get:forbidden}),workflowAreas:{listWorkflowAreas:forbidden,formatWorkflowList:forbidden}});
  assert.equal(exit,0,words.join(' '));assert.equal(stderr.text,'');
  assert.doesNotMatch(stdout.text,/PREVIEW|real workflow PR is not yet proven/i);
  if(words[0]==='workflow'&&words[1]&&words[1]!=='--help'){
   const description=stdout.text.split('\n').find(line=>line.startsWith('  pdd workflow '+words[1]+' '));
   assert.ok(description,words.join(' '));assert.doesNotMatch(description,/PREVIEW:/);
  }
  assert.match(stdout.text,/opens a real PR/);assert.match(stdout.text,/never merges/);
 }
 for(const words of [['session','--help'],['workflow','bug','--help']])assert.equal(await runPdd(words,{stdout:capture(),stderr:capture(),workflowRunner:new Proxy({},{get:forbidden})}),2,words.join(' '));
});

test('actual public bin launch help works offline in empty consumer folder; unrelated invalid input remains finite',t=>{
 const cwd=mkdtempSync(join(tmpdir(),'pdd-preview-help-'));t.after(()=>rmSync(cwd,{recursive:true,force:true}));
 const home=mkdtempSync(join(tmpdir(),'pdd-preview-home-'));t.after(()=>rmSync(home,{recursive:true,force:true}));
 const before=readdirSync(cwd);
 for(const words of [['--help'],['workflow','run','--help'],['workflow','approve','--help'],['workflow','open','--help']]){
  const result=spawnSync(process.execPath,[bin,...words],{cwd,env:{...process.env,HOME:home,CLAUDE_CONFIG_DIR:'',PATH:''},encoding:'utf8',timeout:5000});
  assert.equal(result.status,0,result.stderr);assert.equal(result.stderr,'');assert.doesNotMatch(result.stdout,/PREVIEW|real workflow PR is not yet proven/);
  assert.equal(result.stdout.split('\n')[0],'PDD: prompt-driven development for your coding agent.');
 }
 const unknown=spawnSync(process.execPath,[bin,'not-a-command','--help'],{cwd,env:{...process.env,HOME:home,CLAUDE_CONFIG_DIR:'',PATH:''},encoding:'utf8',timeout:5000});
 assert.equal(unknown.status,2);assert.equal(unknown.stdout,'');assert.match(unknown.stderr,/unsupported|unknown/i);
 assert.deepEqual(readdirSync(cwd),before);
});
