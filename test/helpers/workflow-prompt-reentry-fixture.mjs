// Real temporary Git. The repo fixture fakes GitHub, Herdr and native launches.
import assert from 'node:assert/strict';
import {mkdirSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {openRun,stepDone,approveRun,runStatus} from '../../src/workflow-runner.mjs';
import {legacyManualGates} from './legacy-manual-gates.mjs';
import {fixture,packageRoot} from './workflow-runner-fixture.mjs';

export const vector = value => ({schema_version:'prompt-runtime.program-scenario.v1',steps:[{step_id:'value',entry_path:'value.prompt.md',operation:'value',checks:[{criterion_id:'AC1',target:'result',path:'/value',op:'equals',value}]}]});
export const save=(f,run)=>writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
export async function prepared(t,{code=true,nested=false,realRemote=false,publishCode=true}={}) {
  const f=await fixture(t,{name:'bug',agent:'codex'});
  f.ports.skipMetricsDelivery=true;
  if(realRemote) {
    const {execFile}=await import('node:child_process');
    const {promisify}=await import('node:util'), actual=promisify(execFile);
    f.remote=join(f.base,'remote.git');f.git(f.source,'clone','--bare',f.source,f.remote);
    const fake=f.ports.execFile;
    f.ports.execFile=async(file,args,options)=>{
      if(file==='git' && ['fetch','push','ls-remote'].includes(args[0])) {
        if(args[0]==='push')f.pushes.push(args);
        return actual(file,['-c',`url.${f.remote}.insteadOf=https://github.com/example/project.git`,...args],{...options,encoding:'utf8'});
      }
      return fake(file,args,options);
    };
  }
  const execute=f.ports.execFile;
  f.ports.execFile=async(file,args,options)=>{
    const result=await execute(file,args,options);
    if(file==='git' && args[0]==='push') {
      const branch=args[2].split(':refs/heads/')[1];
      const pr=f.prs.find(pr=>pr.headRefName===branch);
      if(pr)pr.headRefOid=f.git(options.cwd,'rev-parse',`refs/remotes/origin/${branch}`);
    }
    return result;
  };
  const skill=join(f.source,'.agents/skills/pdd-bug');mkdirSync(skill,{recursive:true});
  writeFileSync(join(skill,'workflow.json'),JSON.stringify({version:2,areas:[
    {name:'story',steps:['prompt-story'],gate:'approve'},
    {name:'prompt-pr',steps:['check'],gate:'pr',before:'approve',then:'ask-code'},
    {name:'code',steps:['build','verify'],gate:'pr',replay_evidence:'pdd.replay-evidence.v1'}]}));
  assert.equal((await f.run()).exitCode,0);
  f.done=async step=>{f.tick();const out=await stepDone({step,summary:step,cwd:f.record().root},f.agentPorts());assert.equal(out.exitCode,0,out.message);return out;};
  f.approve=async()=>{f.tick();const out=await approveRun({ref:'17',cwd:f.source,packageRoot},f.ports);assert.equal(out.exitCode,0,out.message);legacyManualGates(f);};
  const run=f.record();mkdirSync(join(run.root,'tests'));mkdirSync(join(run.root,'user_stories'));
  writeFileSync(join(run.root,'value.prompt.md'),'# Value\nReturn the selected value.\n');
  writeFileSync(join(run.root,'user_stories/value.md'),'I can select a value.\n');
  writeFileSync(join(run.root,'tests/value.json'),JSON.stringify(vector(2)));
  if(nested) {
    mkdirSync(join(run.root,'packages/widget/user_stories'),{recursive:true});
    writeFileSync(join(run.root,'packages/widget/user_stories/value.md'),'I can select a nested value.\n');
  }
  await f.done('prompt-story');await f.approve();legacyManualGates(f);await f.done('check');
  if(!code)return f;
  await f.approve();
  assert.equal(f.record().area,2);
  writeFileSync(join(run.root,'value.mjs'),'export const value = 2;\n');
  await f.done('build');
  if(!publishCode)return f;
  await f.done('verify');
  assert.equal(f.prs.length,2);
  return f;
}
export const reopen=(f,area='prompt-pr',extra={})=>openRun({ref:'17',area,cwd:f.source,packageRoot,...extra},f.ports);
