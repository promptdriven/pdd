import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync,writeFileSync,readFileSync,existsSync} from 'node:fs';
import {join,dirname} from 'node:path';
import {coreWorld} from './helpers/core-world.mjs';
import {tickAutopilot} from '../src/autopilot-launcher.mjs';
import {runAutopilotAlerts} from '../src/autopilot-alerts.mjs';
const MIN=60000;
async function world(t){
  const w=await coreWorld(t);w.root=w.state.stateFile.replace(/\.json$/,'-core');
  Object.assign(w.state,{enabled:true,engine:'core',defaultBranch:'main',timerMinutes:10});
  writeFileSync(join(w.cwd,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',engine:'core',report:'off'}}));
  writeFileSync(w.state.stateFile,JSON.stringify(w.state));
  w.env={HOME:join(w.dir,'home'),XDG_CONFIG_HOME:join(w.dir,'config')};w.messages=[];
  const cp=w.ports();delete cp.root;
  w.launcherPorts={env:w.env,now:w.now,stateRoot:dirname(w.state.stateFile),corePorts:cp,
    run:async(file,args,options)=>file==='git'?cp.git(args,options):cp.gh(args,options),
    alertPorts:{http:async r=>{w.messages.push(r.body.text);return {status:200,text:'ok'};}},warn:()=>{}};
  await runAutopilotAlerts({action:'set',env:w.env,text:'https://hooks.slack.com/services/synthetic/test/core'});
  w.tickLauncher=()=>tickAutopilot(w.state.stateFile,w.launcherPorts);
  return w;
}
test('repair: real launcher adapter delivers exhausted core END as one decision',async t=>{
  const w=await world(t);mkdirSync(join(w.root,'jobs'),{recursive:true});
  writeFileSync(join(w.root,'jobs','17.json'),JSON.stringify({issue:17,phase:'ending',started:w.now(),end:{at:w.now(),tries:6,cause:{text:'Synthetic failure'}}}));
  await w.tickLauncher();assert.equal(w.messages.length,1);assert.match(w.messages[0],/needs you: decision/);
  assert.match(w.messages[0],/issues\/17/);assert.match(w.messages[0],/Ask:.*END/);assert.match(w.messages[0],/If no answer:/);
  assert.equal(existsSync(join(w.root,'jobs','17.json')),false);
  await w.tickLauncher();assert.equal(w.messages.length,1);
});
test('repair: real launcher observes persistent core machine pause on later ticks and after restart',async t=>{
  const w=await world(t);w.issue(17);await w.tickLauncher();
  writeFileSync(join(w.root,'core.json'),JSON.stringify({streak:2,hours:1}));w.kill(17,'build');
  await w.tickLauncher();assert.equal(w.messages.length,0,'first pause observation is quiet');
  w.advance(10*MIN);await w.tickLauncher();assert.equal(w.messages.length,0);
  w.advance(5*MIN);await w.tickLauncher();assert.equal(w.messages.length,1);
  assert.match(w.messages[0],/needs you: usage-limit/);assert.match(w.messages[0],/Ask: Run pdd autopilot doctor/);
  w.advance(10*MIN);await w.tickLauncher();assert.equal(w.messages.length,1);
  assert.ok(JSON.parse(readFileSync(w.state.stateFile,'utf8')).coreAlertPause);
  w.advance(60*MIN);await w.tickLauncher();
  assert.equal(JSON.parse(readFileSync(w.state.stateFile,'utf8')).coreAlertPause,undefined);
});
