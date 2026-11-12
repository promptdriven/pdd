import './test-home.mjs';
import assert from 'node:assert/strict';
import {appendFileSync,existsSync,mkdirSync,readFileSync,rmSync,writeFileSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {spawn,spawnSync} from 'node:child_process';
import {harbor,fakeRuntime,portsFor,root as packageRoot} from '../runtime-fake.mjs';
import {runCheck} from '../../src/runtime-client.mjs';
import {associateEvidenceWorkspace} from '../../src/workflow-runner.mjs';
import {interfaceBlocks,proseSha256} from '../../src/runtime-preflight.mjs';
export const disclaimer='Affected checks only; this is not a full workflow pass. Required full-pass gates still apply.';
export const vectors=name=>JSON.parse(readFileSync(new URL(`../affected-checks/${name}-cases.json`,import.meta.url),'utf8'));
export const git=(cwd,...args)=>{const r=spawnSync('git',args,{cwd,encoding:'utf8'});assert.equal(r.status,0,r.stderr);return r.stdout.trim();};
export const put=(root,path,value)=>{const absolute=join(root,path);mkdirSync(resolve(absolute,'..'),{recursive:true});writeFileSync(absolute,typeof value==='string'?value:JSON.stringify(value));};
export const commit=root=>{git(root,'add','.');git(root,'-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','fixture');};
export function affectedFixture(t,{transitive=false}={}) {
  const setup=harbor(t,repo=>{
    const story=readFileSync(join(repo,'user_stories/place-order.md'),'utf8'),test=JSON.parse(readFileSync(join(repo,'tests/place-order.json'),'utf8'));
    const prompt=readFileSync(join(repo,'prompts/place_order.prompt.md'),'utf8');
    for(const dir of ['user_stories','tests','prompts'])rmSync(join(repo,dir),{recursive:true});
    put(repo,'docs/shared.md',transitive?'Shared dependency.\n\n## Dependencies\n\n[Transitive](transitive-to-A-and-B.md)\n':'Shared fixture dependency.\n');
    if(transitive)put(repo,'docs/transitive-to-A-and-B.md','Transitive fixture dependency.\n');
    for(const name of ['A','B','C']) {
      put(repo,`user_stories/${name}.md`,story);
      let source=prompt.replace('None.',name==='C'?'None.':'[Shared](../docs/shared.md)');
      const block=interfaceBlocks(source)[0],definition=JSON.parse(block[1]);definition.status='draft';definition.prose_sha256=proseSha256(source);
      source=source.replace(block[1],JSON.stringify(definition));put(repo,`prompts/${name}.prompt.md`,source);
      const doc={...test,story_path:`user_stories/${name}.md`,steps:test.steps.map(step=>({...step,entry_path:`prompts/${name}.prompt.md`}))};
      put(repo,`test/runtime/${name}.json`,doc);
      if(name==='A')put(repo,'test/runtime/A.recorded.json',doc);
    }
  });
  setup.tests=['test/runtime/A.json','test/runtime/A.recorded.json','test/runtime/B.json','test/runtime/C.json'];
  setup.selected=setup.tests.slice(0,3);setup.change=path=>{appendFileSync(join(setup.repo,path),'\n');if(path.endsWith('.prompt.md')){const file=join(setup.repo,path),source=readFileSync(file,'utf8'),block=interfaceBlocks(source)[0];if(block){const doc=JSON.parse(block[1]);doc.status='draft';doc.prose_sha256=proseSha256(source);writeFileSync(file,source.replace(block[1],JSON.stringify(doc)));}}};
  return setup;
}
export async function affectedRuntime(t,setup,{fail=[],answer}={}) {
  const fake=await fakeRuntime(t,(entry,f)=>{
    if(answer){const result=answer(entry,f);if(result)return result;}
    if(entry.command==='lint')return {status:200,json:f.lint(entry.request.requestId,['A','B','C'].map(name=>({path:`prompts/${name}.prompt.md`,state:'draft',admission_state:'draft',interface:{calls:[]}})))};
    if(entry.command==='check'){
      const test=JSON.parse(readFileSync(join(setup.repo,entry.request.scenario),'utf8'));
      const passed=!fail.includes(entry.request.scenario),checks=test.steps.flatMap(step=>step.checks).map(check=>({...check,expected:check.value,actual:passed?check.value:'fixture failure',passed}));
      return {status:200,json:f.check(entry.request.requestId,passed?'passed':'failed',checks)};
    }
    return f.normal(entry);
  });
  fake.failTests=fail;
  return fake;
}
export const environment=(setup,fake)=>({HOME:setup.home,XDG_CONFIG_HOME:join(setup.home,'config'),PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
export async function check(setup,fake,{words=[],options={'--affected':true,'--json':true},cache=false,extra={},advance=0}={}) {
  const {ports,clock}=portsFor(environment(setup,fake),extra);clock.now+=advance;
  const code=await runCheck({cwd:setup.repo,words,options,cache},ports);
  return {code,ports,clock,output:ports.stdout.text.trim()?JSON.parse(ports.stdout.text):null};
}
export const batch=(setup,id)=>JSON.parse(readFileSync(join(setup.state,'batches',id,'batch.json'),'utf8'));
export const checks=fake=>fake.posts.filter(entry=>entry.command==='check');
export async function cli(setup,args,{env={},entry=process.env.PDD_AFFECTED_CLI??join(packageRoot,'bin/pdd.mjs')}={}) {
  return new Promise((done,reject)=>{
    const child=spawn(process.execPath,[entry,...args],{cwd:setup.repo,env:{...process.env,HOME:setup.home,PDD_STATE_DIR:setup.state,...env},stdio:['ignore','pipe','pipe']});
    let stdout='',stderr='';child.stdout.on('data',chunk=>stdout+=chunk);child.stderr.on('data',chunk=>stderr+=chunk);child.on('error',reject);child.on('close',code=>done({code,stdout,stderr}));
  });
}
export function installGh(setup) {
  const directory=join(setup.sandbox,'bin');mkdirSync(directory,{recursive:true});
  const path=join(directory,'gh');writeFileSync(path,'#!/usr/bin/env node\nconst a=process.argv.slice(2);process.stdout.write(a[0]==="auth"?"gho_affected_fixture\\n":"octo 4242\\n");\n',{mode:0o700});
  return `${directory}:${process.env.PATH}`;
}
export const hasState=setup=>existsSync(setup.state);

// Register a real isolated historical association using the production owner and retained source.
export async function historicalAssociation(setup,stage) {
  git(setup.repo,'remote','add','origin','https://github.com/example/affected-fixture.git');
  const head=git(setup.repo,'rev-parse','HEAD'),commonDir=join(setup.repo,'.git'),runDir=join(commonDir,'pdd/runs/17');
  const run={v:1,number:17,repo:'example/affected-fixture',runId:'synthetic-affected-history',root:setup.repo,sourceRoot:setup.repo,commonDir,runDir,
    issue:{number:17,title:'Synthetic historical receipt',url:'https://github.com/example/affected-fixture/issues/17'},workflow:'bug',agent:'codex',branch:git(setup.repo,'branch','--show-current'),baseBranch:'main',baseSha:head,state:'waiting',area:0,
    areas:[{name:'prompt-pr',steps:['check'],optional:[],gate:'pr',then:'ask-code'},{name:'code',steps:['build','verify'],optional:[],gate:'pr'}],
    done:{},gate:null,question:null,decisions:[],chats:[],pr:stage==='pr1'?[{stage:'prompt-pr',number:23,url:'https://github.com/example/affected-fixture/pull/23',branch:git(setup.repo,'branch','--show-current'),publishedHeadSha:head,state:'open'}]:[],startedAt:1,updatedAt:2};
  put(setup.repo,'.git/pdd/runs/17/status.json',run);
  const ports={env:{HOME:setup.home},now:()=>1000,readPrStatus:async()=>({}),
    herdr:async()=>assert.fail('No chats for fixture association'),confirm:async()=>assert.fail('No approval for fixture association'),
    execFile:async(program,args,options)=>{
      assert.equal(program,'git');assert.ok(['rev-parse','ls-files','ls-tree','cat-file','init','update-index'].includes(args[0]));
      const result=spawnSync(program,args,{...options,encoding:options.encoding==='buffer'?null:options.encoding??'utf8'});if(result.status!==0)throw Error(String(result.stderr));return {stdout:result.stdout,stderr:result.stderr};
    }};
  const result=await associateEvidenceWorkspace({ref:'17',workspace:setup.repo,stage,tests:['test/runtime/C.json'],...(stage==='before'?{commit:head}:{}),cwd:setup.repo},ports);
  assert.equal(result.exitCode,0,result.message);
  const saved=JSON.parse(readFileSync(join(runDir,'status.json'),'utf8'));
  return {run:saved,association:saved.evidenceAssociations.at(-1),runDir};
}
