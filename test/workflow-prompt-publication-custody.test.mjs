import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {approveRun,stepDone} from '../src/workflow-runner.mjs';
import {prepared,reopen} from './helpers/workflow-prompt-reentry-fixture.mjs';

for (const existing of [false,true]) test(`2897 publication: owned path selection pins the pushed head (${existing})`,async t=>{
  const f=await prepared(t,{code:existing,realRemote:true});
  if (existing) assert.equal((await reopen(f)).exitCode,0);
  const before=f.record(),execute=f.ports.execFile,pushes=f.pushes.length;
  let injected=false;
  f.ports.execFile=async(file,args,options)=>{
    const out=await execute(file,args,options);
    if (!injected && file==='git' && args[0]==='diff' && args[1]==='--name-only' && args[2]==='-z' && args.length===5 && (args[4]==='HEAD' || /^[a-f0-9]{40}$/.test(args[4]))) {
      injected=true;
      writeFileSync(join(before.root,'late-owned.prompt.md'),'# Late owned prompt\nReturn a value.\n');
      f.git(before.root,'add','late-owned.prompt.md'); f.git(before.root,'commit','-qm','Concurrent prompt addition');
    }
    return out;
  };
  f.tick();
  const out=existing?await stepDone({step:'check',summary:'check',cwd:before.root},f.agentPorts())
    :await approveRun({ref:'17',cwd:f.source,said:'Publish PR 1.'},f.ports);
  assert.equal(injected,true,'scope-race-reached');
  assert.notEqual(out.exitCode,0,'publication-head-custody');
  assert.equal(f.pushes.length,pushes,'no-source-push');
  assert.equal(f.record().area,1);
});
