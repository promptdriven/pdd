import test from 'node:test';
import assert from 'node:assert/strict';
import {startRun, approveRun, changeRun, cancelRun, openRun} from '../src/workflow-runner.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
import {readdirSync, readFileSync, lstatSync} from 'node:fs';
import {join} from 'node:path';
import {statusView} from '../src/workflow-runs.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const files = root => {
  const rows = {};
  const walk = (path, rel='') => { for (const name of readdirSync(path)) { const child=join(path,name), key=join(rel,name), stat=lstatSync(child); if (stat.isDirectory()) walk(child,key); else if (stat.isFile()) rows[key]=readFileSync(child).toString('base64'); } };
  walk(root); return rows;
};

test('stale actions refuse without changing the run or chat', async t => {
  const f = await fixture(t, {name:'small-change'});
  assert.equal((await startRun({name:'small-change',issue:'17',cwd:f.source,packageRoot},f.ports)).exitCode,0);
  for (const [fn, extra] of [[approveRun,{}],[changeRun,{text:'Change this'}],[cancelRun,{}],[openRun,{}]]) {
    for (const expectation of [{expectGate:'obsolete'}, {expectStep:'obsolete'}]) {
      const before = JSON.stringify(f.record()), tree = files(f.base), calls = f.herdr.calls.length;
      const out = await fn({ref:'17',cwd:f.source,...extra,...expectation},f.ports);
      assert.equal(out.exitCode,6,out.message);
      assert.match(out.message,/current gate: .*current step:/);
      assert.equal(JSON.stringify(f.record()),before);
      assert.equal(f.herdr.calls.length,calls);
      assert.deepEqual(files(f.base),tree);
    }
  }
});

test('CLI forwards expected position to all actions', async () => {
  for (const [verb,method,tail] of [['approve','approveRun',[]],['changes','changeRun',['text']],['cancel','cancelRun',[]],['open','openRun',[]]]) {
    let received; const stream={write(){}};
    const code=await runPdd(['workflow',verb,'17',...tail,'--expect-gate','gate-1','--expect-step','approve'],{stdout:stream,stderr:stream,cwd:'/tmp',packageRoot,workflowRunner:{[method]:async args => {received=args;return {exitCode:6,message:'stale'};}}});
    assert.equal(code,6); assert.equal(received.expectGate,'gate-1'); assert.equal(received.expectStep,'approve');
  }
});

test('matching step retains each command’s ordinary result', async t => {
  for (const [fn, extra] of [[approveRun,{}],[changeRun,{text:'Use the requested value'}],[cancelRun,{}],[openRun,{}]]) {
    const results=[];
    for (const guarded of [false,true]) {
      const f=await fixture(t,{name:'small-change'});
      assert.equal((await startRun({name:'small-change',issue:'17',cwd:f.source,packageRoot},f.ports)).exitCode,0);
      const step=statusView(f.record()).stage.id;
      results.push(await fn({ref:'17',cwd:f.source,...extra,...(guarded?{expectStep:step}:{})},f.ports));
    }
    assert.equal(results[1].exitCode,results[0].exitCode,results[1].message);
  }
});
