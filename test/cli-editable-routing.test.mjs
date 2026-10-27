import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, existsSync, rmSync, mkdirSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { spawnSync } from 'node:child_process';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { renderCompletion } from '../src/completion.mjs';
const uuid='a1234567-1234-4123-8123-123456789abc';
const capture=()=>({text:'',write(s){this.text+=s;}});
const temp=t=>{const p=mkdtempSync(join(tmpdir(),'pdd-caller-'));t.after(()=>rmSync(p,{recursive:true,force:true}));return p;};

test('a free safe NAME reaches startRun; the areas module decides whether that workflow exists',async t=>{
 const calls=[],stdout=capture(),stderr=capture();
 const runner={startRun:async input=>{calls.push(input);return {exitCode:1,message:'There is no my-team-workflow workflow. Workflows: bug, feature, small-change.'};}};
 assert.equal(await runPdd(['workflow','run','my-team-workflow','octo/repo#12','--agent','claude'],{workflowRunner:runner,cwd:'/assigned invoker',packageRoot:'/package',stdout,stderr}),1);
 assert.deepEqual(calls,[{name:'my-team-workflow',issue:'octo/repo#12',agent:'claude',cwd:'/assigned invoker',packageRoot:'/package'}]);
 assert.equal(stdout.text,'');assert.match(stderr.text,/no my-team-workflow workflow/);
 for(const name of ['../bad','/bad','Bad','a--b','a-','a'.repeat(65)])assert.throws(()=>parseArgv(['workflow','run',name,'1']));
 const project=temp(t);
 const real=await import('../src/workflow-runner.mjs');
 const answer=await real.startRun({name:'my-team-workflow',issue:'1',agent:'codex',cwd:project,packageRoot:join(import.meta.dirname,'..')},{env:{HOME:project},execFile:()=>assert.fail('No git or gh before the workflow exists')});
 assert.equal(answer.exitCode,1);assert.match(answer.message,/Workflows: bug, feature, small-change/);
});

test('workflow list reads the bundled areas once and refuses a broken package without fallback',async t=>{
 const stdout=capture(),stderr=capture();
 const home=temp(t);
 assert.equal(await runPdd(['workflow','list','--json'],{packageRoot:join(import.meta.dirname,'..'),cwd:'/project',env:{HOME:home},stdout,stderr,workflowRunner:{startRun:()=>assert.fail('No start')}}),0);
 const listed=JSON.parse(stdout.text);
 assert.deepEqual(listed.workflows.map(w=>w.name),['bug','feature','small-change']);assert.equal(listed.default,null);
 assert.deepEqual(listed.workflows.find(w=>w.name==='small-change').areas.map(a=>[a.name,a.gate]),[['plan','approve'],['build','pr']]);
 const broken=temp(t);mkdirSync(join(broken,'skills/pdd-bug'),{recursive:true});writeFileSync(join(broken,'skills/pdd-bug/workflow.json'),'{"version":1}');
 const errors=capture();assert.equal(await runPdd(['workflow','list'],{packageRoot:broken,env:{HOME:home},stdout:capture(),stderr:errors}),1);assert.ok(errors.text.trim());
});

test('bash/zsh NAME completion reads local definition listing as data, including custom names without evaluating hostile text',t=>{
 const cwd=temp(t),bin=join(cwd,'bin');mkdirSync(bin);const marker=join(cwd,'must-not-exist'),receipt=join(cwd,'calls.jsonl');
 writeFileSync(join(bin,'pdd'),`#!${process.execPath}\nimport fs from 'node:fs';const args=process.argv.slice(2);fs.appendFileSync(${JSON.stringify(receipt)},JSON.stringify(args)+'\\n');if(JSON.stringify(args)!==JSON.stringify(['workflow','list','--json']))process.exit(9);console.log(JSON.stringify({workflows:[{name:'team-review',source:'project'},{name:'feature',source:'bundled'},{name:${JSON.stringify('$(touch '+marker+')')},source:'project'}],default:null}));`,{mode:0o755});
 for(const shell of ['bash','zsh']){
  const file=join(cwd,'completion.'+shell);writeFileSync(file,renderCompletion(shell));
  const code=shell==='bash'?'source "$1"; COMP_WORDS=(pdd workflow run ""); COMP_CWORD=3; _pdd_complete; printf "%s\\n" "${COMPREPLY[@]}"':'autoload -Uz compinit; compinit -D; source "$1"; _describe() { print -rl -- "${choices[@]}"; }; words=(pdd workflow run ""); CURRENT=4; _pdd';
  const result=spawnSync(shell,shell==='bash'?['--noprofile','--norc','-c',code,'test',file]:['-f','-c',code,'test',file],{cwd,env:{PATH:bin+':'+dirname(process.execPath)+':'+process.env.PATH,HOME:cwd},encoding:'utf8',timeout:5000});
  assert.equal(result.status,0,result.stderr);assert.deepEqual(result.stdout.trim().split('\n').sort(),['feature','team-review']);
 }
 assert.equal(existsSync(marker),false);assert.deepEqual(readFileSync(receipt,'utf8').trim().split('\n').map(JSON.parse),[['workflow','list','--json'],['workflow','list','--json']]);
});
