// Generated from prompts/test/autopilot-factory.prompt.md (sha256: 1e63cdda15ec0d34499b1a62a4e6664b040d3a8ff76de2435d17a01988e09b29).
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {randomUUID,createHash} from 'node:crypto';
import {interfaceBlocks,proseSha256} from '../src/runtime-preflight.mjs';
import {scriptedAgent} from './helpers/factory/agent.mjs';
import {existsSync,readdirSync,readFileSync,writeFileSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {factoryWorld,put,readJson,valuePrompt,scenario} from './helpers/factory/world.mjs';

test('factory 3114: full native check retains baseline scope and blocks missing-interface dispatch',async t=>{
  const w=await factoryWorld(t);
  put(w.cwd,'value.prompt.md',valuePrompt(2));
  for(const name of ['value','baseline']) {
    put(w.cwd,`user_stories/${name}.md`,'# Value\n\n## Acceptance criteria\n\n1. The value is 2.\n');
    put(w.cwd,`tests/${name}.json`,{...scenario,story_path:`user_stories/${name}.md`});
  }
  await w.command(['test','--fill-hash']);
  w.git(w.cwd,'add','.');w.git(w.cwd,'commit','-qm','Synthetic full check obligations');
  put(w.cwd,'user_stories/value.md',readFileSync(join(w.cwd,'user_stories/value.md'),'utf8')+'\n');
  const checked=await w.command(['test','--json']);
  const result=JSON.parse(checked.stdout);
  assert.ok(result.check_plan,'3114_FACTORY_PLAN_MISSING');
  assert.equal(result.check_plan.stories.find(row=>row.story_path==='user_stories/value.md').role,'target');
  assert.equal(result.check_plan.stories.find(row=>row.story_path==='user_stories/baseline.md').role,'baseline');
  assert.equal(result.check_scope.target.state,'passed');assert.equal(result.check_scope.baseline.state,'passed');
  const saved=await w.command(['test','--read',result.batch,'--json']);
  assert.deepEqual(JSON.parse(saved.stdout).check_plan,result.check_plan);
  const sent=w.interpreter.posts.filter(row=>row.command==='check').length;
  put(w.cwd,'value.prompt.md','# Missing interface\n');
  const blocked=await w.command(['test','--json'],{allowFailure:true});
  assert.equal(blocked.code,4);
  assert.equal(JSON.parse(blocked.stdout).check_plan.prerequisites.length,1);
  assert.equal(w.interpreter.posts.filter(row=>row.command==='check').length,sent);
  assert.ok(w.commands.every(row=>!row.argv.includes('approve')));
});

for(const kind of ['missing-interface','missing-bound','missing-call-bound','recursive-call'])
  test(`factory 3114 repair: ${kind} retains local history on CLI retry and recovers with a fresh check`,async t=>{
    const w=await factoryWorld(t),original=valuePrompt(2);
    put(w.cwd,'value.prompt.md',original);
    put(w.cwd,'user_stories/value.md','# Value\n\n## Acceptance criteria\n\n1. The value is 2.\n');
    put(w.cwd,'tests/value.json',scenario);
    await w.command(['test','--fill-hash']);
    const repaired=readFileSync(join(w.cwd,'value.prompt.md'),'utf8');
    if(kind==='missing-interface')put(w.cwd,'value.prompt.md','# Missing interface\n');
    else {
      const block=interfaceBlocks(repaired)[0],iface=JSON.parse(block[1]);
      if(kind==='missing-bound')delete iface.limits.max_model_calls;
      else {
        if(kind==='missing-call-bound')put(w.cwd,'nested.prompt.md',repaired);
        iface.calls=[{operation:'nested',target:kind==='recursive-call'?'value.prompt.md':'nested.prompt.md',target_operation:'value',...(kind==='recursive-call'?{max_calls:1}:{})}];
      }
      put(w.cwd,'value.prompt.md',repaired.replace(block[1],JSON.stringify(iface)));
    }
    const blocked=await w.command(['test','--json'],{allowFailure:true});assert.equal(blocked.code,4);
    const result=JSON.parse(blocked.stdout),folder=join(w.env.PDD_STATE_DIR,'batches',result.batch);
    const history=readFileSync(join(folder,'batch.json'),'utf8');
    assert.match(result.check_scope.guidance,/fresh.*pdd test/i,'3114_FACTORY_LOCAL_REPAIR_MISSING');
    for(const argv of [['test','--read',result.batch,'--json'],['test','--retry',result.batch,'--json']]) {
      const saved=await w.command(argv,{allowFailure:true});assert.equal(saved.code,4,'3114_FACTORY_LOCAL_RETRY_UNCONTROLLED');
      const view=JSON.parse(saved.stdout);assert.equal(view.batch,result.batch);
      assert.deepEqual(view.check_plan,result.check_plan);assert.deepEqual(view.rows,result.rows);
      assert.match(view.check_scope.guidance,/repair/i);assert.match(view.check_scope.guidance,/fresh.*pdd test/i);
    }
    assert.equal(w.interpreter.posts.length,0);
    assert.equal(readFileSync(join(folder,'batch.json'),'utf8'),history);
    put(w.cwd,'value.prompt.md',repaired);
    const fresh=await w.command(['test','--json']);assert.notEqual(JSON.parse(fresh.stdout).batch,result.batch);
    assert.equal(w.interpreter.posts.filter(row=>row.command==='check').length,1);
    assert.equal(readFileSync(join(folder,'batch.json'),'utf8'),history);
    assert.ok(w.commands.every(row=>!row.argv.includes('approve')));
  });

async function eventually(check,message) {
  for(let n=0;n<500;n++){if(check())return;await new Promise(r=>setTimeout(r,10));}
  assert.fail(message);
}
function queueRows(root) {return existsSync(root)?readdirSync(root).filter(p=>/^ticket-\d+\.json$/.test(p)).map(p=>readJson(join(root,p))):[];}

