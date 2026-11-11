import test from 'node:test';
import assert from 'node:assert/strict';
import {startRun, approveRun, changeRun, cancelRun, openRun, parkAutomaticRun} from '../src/workflow-runner.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
import {readdirSync, readFileSync, lstatSync} from 'node:fs';
import {join} from 'node:path';
import {statusView} from '../src/workflow-runs.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {environmentRun} from './helpers/environment-retry-fixture.mjs';
import {environmentWakeTag} from '../src/autopilot-environment.mjs';

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

test('a completed ordinary change invalidates a guarded action before its command read', async t => {
  for (const [fn, extra] of [[approveRun,{}],[changeRun,{text:'Stale request'}],[cancelRun,{}],[openRun,{}]]) {
    const f = await fixture(t, {name:'small-change'});
    assert.equal((await startRun({name:'small-change',issue:'17',cwd:f.source,packageRoot},f.ports)).exitCode,0);
    const run = f.record(); run.state = 'waiting'; run.gate = {id:'old-gate',kind:'approve',area:run.areas[run.area].name,at:1}; writeRun(run,f.ports);
    const exec = f.ports.execFile; let resolutions = 0, transitioned = false, after, calls;
    f.ports.execFile = async (file,args,options) => {
      if (!transitioned && file === 'git' && args[0] === 'rev-parse' && args[1] === '--show-toplevel' && ++resolutions === (fn === openRun ? 2 : 3)) {
        transitioned = true;
        const ordinary = await changeRun({ref:'17',cwd:f.source,text:'Ordinary request'},f.ports);
        assert.equal(ordinary.exitCode,0,ordinary.message);
        assert.notEqual(f.record().gate.id,'old-gate');
        after = files(f.base); for (const key of Object.keys(after)) if (key.endsWith('/chat-replacement.lock')) delete after[key]; calls = JSON.stringify(f.herdr.calls);
      }
      return exec(file,args,options);
    };
    const result = await fn({ref:'17',cwd:f.source,...extra,expectGate:'old-gate'},f.ports);
    assert.equal(transitioned,true);
    assert.equal(result.exitCode,6,result.message);
    assert.deepEqual(files(f.base),after);
    assert.equal(JSON.stringify(f.herdr.calls),calls);
  }
});

test('open refuses when an ordinary request moves the gate during chat inspection', async t => {
  const f = await fixture(t, {name:'small-change'});
  assert.equal((await startRun({name:'small-change',issue:'17',cwd:f.source,packageRoot},f.ports)).exitCode,0);
  const run = f.record(); run.state = 'waiting'; run.gate = {id:'old-gate',kind:'approve',area:run.areas[run.area].name,at:1}; writeRun(run,f.ports);
  const herdr = f.ports.herdr; let transitioned = false, after;
  f.ports.herdr = async args => {
    const result = await herdr(args);
    if (!transitioned && args[0] === 'tab' && args[1] === 'get') {
      transitioned = true;
      const ordinary = await changeRun({ref:'17',cwd:f.source,text:'Ordinary request'}, {...f.ports,herdr});
      assert.equal(ordinary.exitCode,0,ordinary.message);
      after = files(f.base); for (const key of Object.keys(after)) if (key.endsWith('/chat-replacement.lock')) delete after[key];
    }
    return result;
  };
  const result = await openRun({ref:'17',cwd:f.source,expectGate:'old-gate'},f.ports);
  assert.equal(transitioned,true);
  assert.equal(result.exitCode,6,result.message);
  assert.deepEqual(files(f.base),after);
});

test('terminal approval refuses when a competing request changes the gate during confirmation', async t => {
  const f = await fixture(t, {name:'small-change'});
  assert.equal((await startRun({name:'small-change',issue:'17',cwd:f.source,packageRoot},f.ports)).exitCode,0);
  const run = f.record(); run.state='waiting'; run.gate={id:'old-gate',kind:'approve',area:run.areas[run.area].name,at:1}; writeRun(run,f.ports);
  let after, calls, confirmed=false;
  f.ports.confirm = async () => {
    const result = await changeRun({ref:'17',cwd:f.source,text:'Ordinary request'},f.ports);
    assert.equal(result.exitCode,0,result.message); confirmed=true;
    after=files(f.base); for (const key of Object.keys(after)) if (key.endsWith('/chat-replacement.lock')) delete after[key]; calls=JSON.stringify(f.herdr.calls);
    return true;
  };
  const result=await approveRun({ref:'17',cwd:f.source,expectGate:'old-gate'},f.ports);
  assert.equal(confirmed,true,result.message); assert.equal(result.exitCode,6,result.message);
  assert.deepEqual(files(f.base),after); assert.equal(JSON.stringify(f.herdr.calls),calls);
});

test('cancel refuses when a competing request changes the gate during screen inspection', async t => {
  const f = await fixture(t, {name:'small-change'});
  assert.equal((await startRun({name:'small-change',issue:'17',cwd:f.source,packageRoot},f.ports)).exitCode,0);
  const run = f.record(); run.state='waiting'; run.gate={id:'old-gate',kind:'approve',area:run.areas[run.area].name,at:1}; writeRun(run,f.ports);
  const herdr=f.ports.herdr; let after, changed=false;
  f.ports.herdr=async args => {
    const result=await herdr(args);
    if (!changed && args[0]==='pane' && args[1]==='read' && args.includes('recent-unwrapped')) {
      changed=true; const ordinary=await changeRun({ref:'17',cwd:f.source,text:'Ordinary request'},{...f.ports,herdr});
      assert.equal(ordinary.exitCode,0,ordinary.message);
      after=files(f.base); for (const key of Object.keys(after)) if (key.endsWith('/chat-replacement.lock')) delete after[key];
    }
    return result;
  };
  const result=await cancelRun({ref:'17',cwd:f.source,expectGate:'old-gate'},f.ports);
  assert.equal(changed,true,result.message); assert.equal(result.exitCode,6,result.message);
  assert.deepEqual(files(f.base),after);
});


test('changes refuses when the gate moves during an unhealthy environment check', async t => {
  const {f, ports, root} = await environmentRun(t);
  const reason = 'Native full suite timeout';
  const parked = await parkAutomaticRun({reason, step:'verify', cwd:root}, ports());
  assert.equal(parked.exitCode,0,parked.message);
  const run=f.record(); run.gate={id:'old-gate',kind:'approve',area:run.areas[run.area].name,at:1}; writeRun(run,f.ports);
  f.tick(15 * 60_000);
  let checked=false, after;
  const result=await changeRun({ref:'17',cwd:f.source,expectGate:'old-gate',text:environmentWakeTag(run.environmentRetry)}, ports({
    environmentHealthy: async () => {
      const ordinary=await changeRun({ref:'17',cwd:f.source,text:'Ordinary request'},ports());
      assert.equal(ordinary.exitCode,0,ordinary.message); checked=true;
      after=files(f.base); for (const key of Object.keys(after)) if (key.endsWith('/chat-replacement.lock')) delete after[key];
      return false;
    },
  }));
  assert.equal(checked,true); assert.equal(result.exitCode,6,result.message);
  assert.deepEqual(files(f.base),after);
});
