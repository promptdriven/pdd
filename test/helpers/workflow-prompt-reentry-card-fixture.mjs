import assert from 'node:assert/strict';
import {cpSync,mkdirSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {execFile} from 'node:child_process';
import {promisify} from 'node:util';
import {fixture,packageRoot} from './workflow-runner-fixture.mjs';
import {approveRun,stepDone} from '../../src/workflow-runner.mjs';
import {fakeRuntime,portsFor} from '../runtime-fake.mjs';
import {runCheck} from '../../src/runtime-seam.mjs';

export const PROMPT='prompts/place_order.prompt.md',TEST='tests/place-order.json',STORY='user_stories/place-order.md';
export async function preparedCard(t,{through='code'}={}) {
  const f=await fixture(t,{name:'bug',agent:'codex'}),actual=promisify(execFile);
  f.ports.skipMetricsDelivery=true;f.ports.env.PDD_STATE_DIR=join(f.state,'runtime');
  f.remote=join(f.base,'remote.git');f.git(f.source,'clone','-q','--bare',f.source,f.remote);
  const execute=f.ports.execFile;
  f.ports.execFile=async(file,args,options)=>{
    if(file==='git'&&['fetch','push','ls-remote'].includes(args[0])) {
      if(args[0]==='push')f.pushes.push(args);
      const result=await actual(file,['-c',`url.${f.remote}.insteadOf=https://github.com/example/project.git`,...args],options);
      if(args[0]==='push') {
        const branch=args[2].split(':refs/heads/')[1],pr=f.prs.find(pr=>pr.headRefName===branch);
        if(pr)pr.headRefOid=f.git(options.cwd,'rev-parse',`refs/remotes/origin/${branch}`);
      }
      return result;
    }
    return execute(file,args,options);
  };
  const skill=join(f.source,'.agents/skills/pdd-bug');mkdirSync(skill,{recursive:true});
  writeFileSync(join(skill,'workflow.json'),JSON.stringify({version:2,areas:[
    {name:'story',steps:['prompt-story'],gate:'approve'},
    {name:'prompt-pr',steps:['check','try'],optional:['try'],gate:'pr',before:'approve',then:'ask-code'},
    {name:'code',steps:['build','verify'],gate:'pr',replay_evidence:'pdd.replay-evidence.v1'}]}));
  mkdirSync(join(skill,'steps'));writeFileSync(join(skill,'steps/autopilot.md'),'Synthetic scoped delegation fixture.');
  assert.equal((await f.run()).exitCode,0);
  const run=f.record();
  for(const dir of ['prompts','tests','user_stories'])mkdirSync(join(run.root,dir));
  for(const path of [PROMPT,TEST,STORY])cpSync(join(packageRoot,'test/fixtures/harbor',path),join(run.root,path));
  f.done=async(step)=>{f.tick();const out=await stepDone({step,summary:step,cwd:run.root},f.agentPorts());assert.equal(out.exitCode,0,out.message);return out;};
  f.check=async()=>{
    f.tick();
    const fake=await fakeRuntime(t,(entry,runtime)=>{
      if(entry.command==='lint')return {status:200,json:runtime.lint(entry.request.requestId)};
      const id=entry.request?.requestId??entry.url.split('/').at(-1);
      return {status:200,json:runtime.check(id,'passed',['AC1','AC2','AC3'].map(criterion_id=>({criterion_id,target:'result',path:'/totalCents',op:'equals',expected:900,actual:900,passed:true})))};
    });
    const made=portsFor({...f.ports.env,PDD_RUNTIME_URL:fake.origin});made.clock.now=f.clock;
    assert.equal(await runCheck({cwd:run.root,words:[],options:{'--json':true}},made.ports),0,made.ports.stderr.text);
  };
  await f.done('prompt-story');
  f.tick();assert.equal((await approveRun({ref:'17',cwd:f.source,said:'This Story is right.',through},f.agentPorts())).exitCode,0);
  await f.check();await f.done('check');
  assert.equal(f.record().area,through==='code'?2:1);
  if(through==='code') {
    writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');await f.done('build');await f.done('verify');
    assert.equal(f.prs.length,2);
  }
  return f;
}
