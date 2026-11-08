import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { fixture } from './helpers/workflow-runner-fixture.mjs';

const capture = () => ({ text: '', write(value) { this.text += value; } });
async function baseWorld(t, changes = {}) {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  run.baseBranch = 'integration/topic';
  run.pr = [{ number: 23, url: 'https://github.com/example/project/pull/23', base: run.baseBranch, stage: 'change' }];
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
  const calls = [], world = {
    pull: { number:23, state:'open', base:{ref:run.baseBranch, repo:{full_name:run.repo}} },
    metadata: {default_branch:'trunk'},
    releases: [[{draft:false,tag_name:'v1.0',published_at:'2026-01-01T00:00:00Z'}], [
      {draft:true,tag_name:'v3',published_at:null},
      {draft:false,prerelease:true,tag_name:'alpha-v2',published_at:'2026-02-01T00:00:00Z'}]],
    defaultCompare: {behind_by:0,status:'ahead'}, releaseCompare:{behind_by:0,status:'ahead'},
    ...changes,
  };
  const execute = async (file,args,opts) => {
    if(file!=='gh') return f.ports.execFile(file,args,opts);
    calls.push(args);
    assert.equal(args[0],'api');
    assert.equal(args.some(a=>['POST','PATCH','PUT','DELETE'].includes(a)),false);
    const path=args[1]; let value;
    if (world.failure && path.includes(world.failure)) throw Error('synthetic unavailable read');
    if(path===`repos/${run.repo}/pulls/23`)value=world.pull;
    else if(path===`repos/${run.repo}`)value=world.metadata;
    else if(path===`repos/${run.repo}/releases?per_page=100`) { assert.ok(args.includes('--paginate'));assert.ok(args.includes('--slurp'));value=world.releases; }
    else if(path.includes('/compare/trunk...'))value=world.defaultCompare;
    else if(path.includes('/compare/alpha-v2...'))value=world.releaseCompare;
    else assert.fail(`Unexpected fake read: ${path}`);
    return {code:0,stdout:JSON.stringify(value),stderr:''};
  };
  f.check = async (pr='23') => {
    const stdout=capture(),stderr=capture();
    const code=await runPdd(['autopilot','check-base','17',pr],{cwd:f.source,stdout,stderr,env:f.ports.env,autopilotLauncherPorts:{...f.ports,run:async(file,args,opts)=>{const result=await execute(file,args,opts);return {code:result.code ?? 0,stdout:result.stdout ?? '',stderr:result.stderr ?? ''};}}});
    return {code,text:stdout.text+stderr.text,stdout:stdout.text,stderr:stderr.text};
  };
  return {...f,world,calls,run};
}

test('3071 merge guard accepts the saved target and newest published prerelease',async t=>{
  const f=await baseWorld(t),out=await f.check();
  assert.equal(out.code,0,out.text);assert.equal(out.stderr,'');
  assert.ok(out.text.includes('integration/topic'));assert.ok(out.text.includes('alpha-v2'));
  assert.equal(f.calls.length,5);
  assert.ok(f.calls.some(args=>args[1].endsWith('alpha-v2...integration%2Ftopic')));
});
for (const [name,changes,reason] of [
  ['wrong target',{pull:{number:23,base:{ref:'alpha',repo:{full_name:'example/project'}}}},'integration/topic'],
  ['behind default',{defaultCompare:{behind_by:431,status:'behind'}},'trunk'],
  ['diverged default',{defaultCompare:{behind_by:1,status:'diverged'}},'trunk'],
  ['missing release',{releaseCompare:{behind_by:1,status:'diverged'}},'alpha-v2'],
  ['unknown ancestry',{defaultCompare:{}},'ancestry'],
  ['release read failure',{failure:'/releases?'},'releases'],
  ['unknown default',{metadata:{}},'default'],
  ['malformed releases',{releases:[[{draft:false,tag_name:'v3',published_at:null}]]},'release'],
  ['foreign target',{pull:{number:23,base:{ref:'integration/topic',repo:{full_name:'other/project'}}}},'target'],
]) test(`3071 merge guard refuses ${name}`,async t=>{
  const f=await baseWorld(t,changes),out=await f.check();
  assert.equal(out.code,1,out.text);assert.equal(out.stdout,'');assert.ok(out.text.includes(reason));
});
test('3071 no releases still checks default ancestry',async t=>{
  const f=await baseWorld(t,{releases:[[]]}),out=await f.check();assert.equal(out.code,0,out.text);assert.equal(f.calls.length,4);
});
test('3071 post-merge audit reads actual base again and detects wrong target',async t=>{
  const f=await baseWorld(t); assert.equal((await f.check()).code,0);
  f.world.pull.state='closed'; f.world.pull.merged=true; f.world.pull.base.ref='alpha';
  const out=await f.check();assert.equal(out.code,1,out.text);assert.ok(out.text.includes('alpha'));assert.equal(f.calls.length,6);
});
test('3071 safety reads do not reuse an earlier ancestry result',async t=>{
  const f=await baseWorld(t); assert.equal((await f.check()).code,0);
  f.world.defaultCompare={behind_by:1,status:'behind'};
  const out=await f.check();assert.equal(out.code,1,out.text);assert.ok(out.text.includes('trunk'));assert.equal(f.calls.length,9);
});
test('3071 unknown PR refuses before GitHub reads',async t=>{
  const f=await baseWorld(t),out=await f.check('99');assert.equal(out.code,1);assert.equal(f.calls.length,0);
});
