import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {mkdirSync, realpathSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {promisify} from 'node:util';
import {execFile as callback} from 'node:child_process';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {acquireRunLock, startRun} from '../src/workflow-runner.mjs';

const origin={repository:'example/project',coordinatorId:'coordinator-a',machine:'machine-a',claim:{commentId:'11',labelEventId:'12'}};
const envelope={version:'pdd.autopilot-coordinator.v1',repository:origin.repository,coordinatorId:origin.coordinatorId,machine:origin.machine,activation:'activation'};
for (const caller of ['owner','other','stopped']) test(`native ${caller} caller respects coordinator ownership`,async t=>{
  const f=await fixture(t,{name:'bug',agent:'codex'});
  const root=realpathSync(f.source), stateRoot=join(f.state,'autopilot'); mkdirSync(stateRoot,{recursive:true});
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',trust:[]}}));
  const state={enabled:caller!=='stopped',repo:origin.repository,cwd:root,coordinatorId:origin.coordinatorId,machine:origin.machine,activatedAt:'activation',startAction:{command:'pdd autopilot start',repository:origin.repository,mode:'auto'},paneId:'coordinator-pane',ownerLaunch:{paneId:'coordinator-pane',coordinator:envelope}};
  writeFileSync(join(stateRoot,`${createHash('sha256').update(root).digest('hex').slice(0,20)}.json`),JSON.stringify(state));
  const fixturePath=join(f.base,'reader.json'), logPath=join(f.base,'gh.log');
  writeFileSync(fixturePath,JSON.stringify({labels:['pdd:working'],events:[{id:12,event:'labeled',label:{name:'pdd:working'},actor:{login:'example'}}],comments:[{id:11,user:{login:'example'},body:JSON.stringify({repository:origin.repository,coordinatorId:origin.coordinatorId,machine:origin.machine,labelEventId:'12'})}]}));
  const exec=promisify(callback), original=f.ports.execFile;
  const execFile=(file,args,opts)=>file==='gh' && args[0]==='api' && args[1]==='--include' ? exec(process.execPath,[join(packageRoot,'test/helpers/continuation-fake-gh.mjs'),...args],{...opts,env:{...process.env,READER_FIXTURE_FILE:fixturePath,READER_GH_LOG:logPath}}) : original(file,args,opts);
  let admissions=0;
  const ports={...f.ports,env:{...f.ports.env,HERDR_SOCKET_PATH:'/fixture/sessions/pdd-autopilot/socket',HERDR_PANE_ID:caller==='other'?'other-pane':'coordinator-pane'},execFile,autopilotStateRoot:stateRoot,checkDependencyStart:async value=>{admissions++; assert.deepEqual(value.coordinator,{...origin,activation:'activation'}); return {allowed:true,reason:'ok'};}};
  const lockDir=join(f.source,'.git','pdd'); mkdirSync(lockDir,{recursive:true});
  const release=caller==='other' ? acquireRunLock(lockDir,'autopilot-admission.lock') : () => {};
  t.after(release);
  const result=await startRun({name:'bug',issue:'17',agent:'codex',cwd:f.source,packageRoot,origin:'autopilot',decisionId:'11234567-89ab-4cde-8fab-123456789abc'},ports);
  if(caller==='stopped') {
    assert.equal(result.exitCode,1); assert.match(result.message,/ownership does not match/i); assert.equal(admissions,0);
    const home=f.ports.env.HOME, defaultState=join(home,'.local','state','pdd','autopilot');
    mkdirSync(defaultState,{recursive:true});
    writeFileSync(join(defaultState,`${createHash('sha256').update(root).digest('hex').slice(0,20)}.json`),JSON.stringify(state));
    const keys=['HOME','HERDR_SOCKET_PATH','HERDR_PANE_ID','PDD_AUTOPILOT_CONTEXT'];
    const before=Object.fromEntries(keys.map(key=>[key,process.env[key]]));
    t.after(()=>{for(const key of keys) {if(before[key]===undefined) delete process.env[key]; else process.env[key]=before[key];}});
    process.env.HOME=home; process.env.HERDR_SOCKET_PATH='/fixture/sessions/pdd-autopilot/socket'; process.env.HERDR_PANE_ID='coordinator-pane'; delete process.env.PDD_AUTOPILOT_CONTEXT;
    const defaultResult=await startRun({name:'bug',issue:'17',agent:'codex',cwd:f.source,packageRoot});
    assert.equal(defaultResult.exitCode,1); assert.match(defaultResult.message,/ownership does not match/i);
    return;
  }
  assert.equal(result.exitCode,0,result.message);
  assert.equal(admissions,caller==='owner'?1:0);
  assert.deepEqual(f.record().automaticOrigin,caller==='owner'?origin:undefined);
});
