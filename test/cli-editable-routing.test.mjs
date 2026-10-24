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
const transport=Object.fromEntries(['runHerdrStage','inspectHerdrStage','attachHerdrStage','closeHerdrStage'].map(name=>[name,()=>assert.fail('Caller must not dispatch stage directly')]));
const temp=t=>{const p=mkdtempSync(join(tmpdir(),'pdd-caller-'));t.after(()=>rmSync(p,{recursive:true,force:true}));return p;};

test('editable free NAME reaches one real runner interface with exact four native ports, no guessed snapshot',async()=>{
 const calls=[],stdout=capture(),stderr=capture();
 const runner={runWorkflow:async(input,ports)=>{calls.push({input,ports});return {exitCode:2,state:'waiting',runId:uuid,stage:'human-review',message:'waiting '+uuid+' human-review'};}};
 assert.equal(await runPdd(['workflow','run','my-team-workflow','octo/repo#12','--agent','claude'],{workflowRunner:runner,workflowStages:transport,cwd:'/assigned invoker',packageRoot:'/package',stdout,stderr}),2);
 assert.equal(calls.length,1);assert.deepEqual(calls[0].input,{name:'my-team-workflow',issue:'octo/repo#12',agent:'claude',cwd:'/assigned invoker',packageRoot:'/package'});
 for(const [name,fn] of Object.entries(transport))assert.equal(calls[0].ports[name],fn);
 assert.equal('context' in calls[0].input,false);assert.equal(stdout.text,'waiting '+uuid+' human-review\n');assert.equal(stderr.text,'');
 for(const name of ['../bad','/bad','Bad','a--b','a-','a'.repeat(65)])assert.throws(()=>parseArgv(['workflow','run',name,'1']));
});

test('workflow list delegates once to authoritative definition discovery, exposes source, refuses invalid override without fallback',async()=>{
 const calls=[],stdout=capture(),stderr=capture();
 const defs={listWorkflowDefinitions:input=>{calls.push(input);return [{name:'feature',source:'bundled'},{name:'team-review',source:'project'}];}};
 const dependencies={workflowDefinitions:defs,workflowRunner:{runWorkflow:()=>assert.fail('No start')},cwd:'/project',packageRoot:'/installed',stdout,stderr};
 assert.equal(await runPdd(['workflow','list','--json'],dependencies),0);
 assert.deepEqual(JSON.parse(stdout.text),{workflows:[{name:'feature',source:'bundled'},{name:'team-review',source:'project'}],default:null});
 assert.deepEqual(calls,[{cwd:'/project',packageRoot:'/installed'}]);
 stdout.text='';defs.listWorkflowDefinitions=()=>{throw Error('Invalid override');};
 assert.equal(await runPdd(['workflow','list'],dependencies),1);assert.equal(stdout.text,'');assert.ok(stderr.text);
});

test('attach calls main exact saved-run binding only; archive/result/uncertainty never starts a stage or retries',async()=>{
 for(const [state,exitCode] of [['waiting',2],['completed',0],['recovery_required',1]]){
  const calls=[],stdout=capture(),stderr=capture();
  const workflowRunner={attachWorkflow:async(input,ports)=>{calls.push(input);assert.equal(ports.attachHerdrStage,transport.attachHerdrStage);return {state,exitCode,runId:uuid,stage:'check',message:state+' '+uuid};}};
  assert.equal(await runPdd(['workflow','attach',uuid],{workflowRunner,workflowStages:transport,cwd:'/lookup',packageRoot:'/pkg',stdout,stderr}),exitCode);
  assert.deepEqual(calls,[{runId:uuid,cwd:'/lookup',packageRoot:'/pkg'}]);assert.equal(stdout.text,state+' '+uuid+'\n');
 }
 for(const argv of [['workflow','attach',uuid,'--agent','codex'],['workflow','attach','not-a-uuid'],['workflow','attach',uuid,'--decision','approve']]){
  assert.equal(await runPdd(argv,{stdout:capture(),stderr:capture(),workflowRunner:{attachWorkflow:()=>assert.fail('No call')}}),2);
 }
 let count=0;assert.equal(await runPdd(['workflow','attach',uuid],{stdout:capture(),stderr:capture(),workflowStages:transport,workflowRunner:{attachWorkflow:()=>{count++;throw Error('unknown');}}}),1);assert.equal(count,1);
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
