import test from 'node:test';
import assert from 'node:assert/strict';
import {fixture} from './helpers/workflow-delivery-fixture.mjs';
import {approveRun} from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';

test('2897 terminal override binds the current contract of an incomplete legacy gate',async t=>{
 const f=await fixture(t,{name:'bug'});
 assert.equal((await f.run()).exitCode,0);
 const run=f.record();
 run.done={reproduce:{at:1,summary:'ready',area:'story'}};
 run.gate={area:'story',at:1,kind:'approve'};
 writeRun(run,f.ports);
 const refused=await approveRun({ref:'17',cwd:f.source,said:'audit-0127'},f.agentPorts());
 assert.equal(refused.exitCode,1);
 assert.equal(f.record().decisions.length,0);
 let injected=false;
 const out=await approveRun({ref:'17',cwd:f.source},{...f.ports,now:()=>{
  if(!injected){
   injected=true;const latest=f.record();
   latest.decisions.push({stage:'another',decision:'changes',at:2000});
   (latest.evidence??=[]).push({at:2000,summary:'audit-independent-0127'});
   writeRun(latest,f.ports);
  }
  return f.clock;
 }});
 assert.equal(out.exitCode,0,out.message);
 assert.equal(f.record().area,1);
 assert.equal(typeof f.record().decisions.at(-1).storyContract,'string');
 assert.ok(Array.isArray(f.record().decisions.at(-1).storyPaths));
 assert.ok(f.record().decisions.some(row=>row.at===2000));
 assert.ok(f.record().evidence.some(row=>row.summary==='audit-independent-0127'));
});
