import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-delivery-fixture.mjs';
import {stepDone} from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {renderHelp} from '../src/pdd-cli.mjs';

// Regressions from the #2755 merge with #2753: commitRun reloads the saved run, so another command can clear the gate
// between the save and the next read. Long-term owner: one owner for the run record (greg-lead class 6).

test('2755 MERGE-RACE finishPr: a concurrent area advance that clears the gate does not crash the last done', async t => {
  const f=await fixture(t,{agent:'codex',name:'bug'});assert.equal((await f.run()).exitCode,0);
  const run=f.record();run.areas[0].optional=[];run.areas[0].gate='pr';delete run.areas[0].before;
  run.areas[0].then='ask-code';run.areas[0].steps=['finish'];
  writeRun(run,f.ports);writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
  let injected=false;const original=f.ports.execFile;
  const ports={...f.ports,execFile:async(file,args,opts)=>{
    if(!injected&&file==='git'&&args[0]==='status'){
      injected=true;const newer=f.record();newer.area=1;newer.gate=null;newer.state='running';
      newer.decisions.push({stage:newer.areas[0].name,decision:'approve',via:'terminal',at:9000});writeRun(newer,f.ports);
    }
    return original(file,args,opts);
  }};
  const out=await stepDone({step:'finish',summary:'Own publication\nRuntime check: ✓ 1/1 criteria',cwd:run.root},ports);
  assert.ok(injected,'the concurrent writer ran');
  assert.equal(out.exitCode,0,out.message);
  assert.equal(f.record().gate,null,'the newer record keeps its cleared gate');
  assert.ok(f.record().pr?.length,'PR 1 was saved before the guarded read');
});

test('2755 MERGE-RACE showGate: a concurrent writer that clears the open gate does not fail the repeated done', async t => {
  const f=await fixture(t,{agent:'codex',name:'bug'});assert.equal((await f.run()).exitCode,0);
  const run=f.record();run.areas[0].optional=[];run.areas[0].gate='approve';delete run.areas[0].before;delete run.areas[0].then;
  run.areas[0].steps=['finish'];run.done={finish:{at:1,summary:'first',area:run.areas[0].name}};
  run.gate={id:'00000000-0000-4000-8000-0000000000aa',area:run.areas[0].name,at:1,kind:'approve'};run.state='waiting';
  writeRun(run,f.ports);
  let injected=false;
  const ports={...f.ports,now:()=>{if(!injected){injected=true;const newer=f.record();newer.gate=null;newer.state='running';writeRun(newer,f.ports);}return 5000;}};
  const out=await stepDone({step:'finish',summary:'second',cwd:run.root},ports);
  assert.ok(injected,'the concurrent writer ran');
  assert.doesNotMatch(out.message,/Cannot show selected prompts|Could not save/);
  assert.equal(out.exitCode,0,out.message);
  assert.equal(f.record().gate,null,'no snapshot is written into a cleared gate');
});

test('2755 help path lines keep $ patterns in the package root literally', () => {
  const root="/opt/a$&b$$c$'d$`e";
  const help=renderHelp([],root).split('\n');
  assert.ok(help.includes(`Prompting guide: ${root}/docs/prompting-guide.md`),help.join('\n'));
  assert.ok(help.includes(`RUNBOOK: ${root}/RUNBOOK.md`),help.join('\n'));
});
