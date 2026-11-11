import test from 'node:test';
import assert from 'node:assert/strict';
import {readdirSync, readFileSync, lstatSync} from 'node:fs';
import {join} from 'node:path';
import {approveRun, changeRun, cancelRun, openRun} from '../src/workflow-runner.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
import {statusView, writeRun} from '../src/workflow-runs.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

function tree(path) {
  return Object.fromEntries(readdirSync(path, {recursive:true}).sort().filter(p => !p.includes('/pdd/metrics/') && lstatSync(join(path,p)).isFile()).map(p => [p,readFileSync(join(path,p)).toString('base64')]));
}
const actions = [['approve',approveRun,[]], ['changes',changeRun,['A change']], ['cancel',cancelRun,[]], ['open',openRun,[]]];
async function invoke(f, verb, fn, tail, flag, value) {
  let output = ''; const stream = {write(s) { output += s; }};
  const runner = {approveRun, changeRun, cancelRun, openRun};
  for (const key of Object.keys(runner)) { const action = runner[key]; runner[key] = args => action(args, f.ports); }
  const code = await runPdd(['workflow',verb,'17',...tail,...(flag ? [flag,value] : [])], {stdout:stream,stderr:stream,cwd:f.source,packageRoot,workflowRunner:runner});
  return {code, output};
}
test('bounded public commands preserve ordinary outcomes and refuse stale positions', async t => {
  for (const [verb,fn,tail] of actions) {
    // Fresh runs permit comparison without effects from earlier actions.
    let ordinary;
    for (const mode of ['absent','right-step','right-gate','wrong-step','wrong-gate','terminal-wrong-gate']) {
      const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
      if (mode === 'right-gate') { const run=f.record(); run.state='waiting'; run.gate={id:'gate-1',area:run.areas[run.area].name,kind:'approve',at:1}; writeRun(run,f.ports); }
      if (mode === 'terminal-wrong-gate') { const run=f.record(); run.state='completed'; run.gate=null; writeRun(run,f.ports); }
      const view = statusView(f.record());
      const flag = mode.endsWith('step') ? '--expect-step' : mode.endsWith('gate') ? '--expect-gate' : null;
      const value = mode === 'right-step' ? view.stage.id : mode === 'right-gate' ? view.waitingDecision.id : 'stale-position';
      const before = tree(f.base), calls = JSON.stringify(f.herdr.calls);
      const result = await invoke(f,verb,fn,tail,flag,value);
      if (mode === 'absent') ordinary = result.code;
      else if (mode === 'right-step') assert.equal(result.code,ordinary,`${verb} matching step`);
      else if (mode === 'right-gate') assert.notEqual(result.code,6,`${verb} matching gate`);
      else {
        assert.equal(result.code,6,`${verb} ${mode}`);
        assert.match(result.output,/current gate: .*current step:/);
        assert.deepEqual(tree(f.base),before,`${verb} ${mode} files`);
        assert.equal(JSON.stringify(f.herdr.calls),calls,`${verb} ${mode} chat`);
      }
    }
  }
});

test('parked open rechecks position after its initial read', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run = f.record();
  run.automaticOrigin = {repository:run.repo,coordinatorId:'owner-a',machine:'machine-a',claim:{commentId:'11',labelEventId:'12'}};
  run.state = 'waiting'; run.gate = {id:'old-gate',kind:'approve',area:run.areas[run.area].name,at:1};
  run.parking = {phase:'parked',at:1,blocker:{kind:'dependency',until:'18'}};
  writeRun(run,f.ports);
  let resolutions = 0, afterTransition;
  const exec = f.ports.execFile;
  f.ports.execFile = async (file,args,options) => {
    if (file === 'git' && args[0] === 'rev-parse' && args[1] === '--show-toplevel' && ++resolutions === 2) {
      const updated = f.record(); updated.gate.id = 'new-gate'; writeRun(updated,f.ports);
      afterTransition = tree(f.base);
    }
    return exec(file,args,options);
  };
  const calls = JSON.stringify(f.herdr.calls);
  const result = await openRun({ref:'17',cwd:f.source,packageRoot,expectGate:'old-gate'},f.ports);
  assert.equal(result.exitCode,6); assert.match(result.message,/current gate: new-gate/);
  assert.deepEqual(tree(f.base),afterTransition); assert.equal(JSON.stringify(f.herdr.calls),calls);
});
