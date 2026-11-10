import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdtempSync, mkdirSync, rmSync, readdirSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import * as queue from '../src/test-suite-queue.mjs';
import { checkMachine, GiB } from './helpers/check-machine.mjs';

const until = async predicate => {
  for (let i=0;i<1000;i++) { if (predicate()) return; await new Promise(done=>setTimeout(done,2)); }
  assert.fail('controlled queue did not reach expected state');
};
function fixture(t, values={}) {
  const root=mkdtempSync(join(tmpdir(),'pdd-machine-checks-')), fake=checkMachine(values), calls=[], jobs=[];
  mkdirSync(join(root,'queue'));
  const f={root,env:{PDD_SUITE_QUEUE:join(root,'queue')},calls,jobs,...fake,time:1000,stop:false};
  f.ports={...fake.ports,now:()=>f.time,alive:()=>true,say:()=>{},sleep:()=>new Promise(done=>setTimeout(done,2)),
    execute:async(command,options)=>{const call={command,options};calls.push(call);options.onChild(100+calls.length);if(f.stop)return {exitCode:0};return new Promise(done=>call.finish=()=>done({exitCode:0}));}};
  f.run=()=>{const job=queue.runTestSuite({cwd:join(root,`repo-${jobs.length}`),command:'full-build',env:f.env},f.ports);jobs.push(job);return job;};
  f.records=()=>readdirSync(f.env.PDD_SUITE_QUEUE).filter(n=>/^ticket-.*json$/.test(n)).map(n=>JSON.parse(readFileSync(join(f.env.PDD_SUITE_QUEUE,n))));
  t.after(async()=>{f.stop=true;f.machine.load=0;for(const call of calls)call.finish?.();await Promise.all(jobs);rmSync(root,{recursive:true,force:true});});
  return f;
}

for(const [count,slots,share] of [[4,1,4],[8,1,8],[16,1,16],[32,2,16],[64,5,12],[96,8,12]]) {
  test(`machine ${count} cores admits ${slots} checks with ${share} CPUs each`,async t=>{
    const f=fixture(t,{count});
    for(let i=0;i<slots+1;i++){f.run();await until(()=>f.records().length===i+1);}
    await new Promise(done=>setTimeout(done,20));
    assert.equal(f.calls.length,slots,'heavy admission must match machine slots');
    assert.deepEqual(f.calls.map(c=>c.options.env.PDD_CHECK_CPUS),Array(slots).fill(String(share)),'each check sees its CPU share');
    const lists=f.calls.map(c=>c.options.cpuIds);
    assert.equal(new Set(lists.flat()).size,lists.flat().length,'simultaneous affinity shares are disjoint');
    assert.equal((await queue.readSuiteProgress({cwd:join(f.root,`repo-${slots}`),env:f.env},f.ports)).state,'waiting');
  });
}

test('low free memory reduces heavy admission',async t=>{
  const f=fixture(t,{count:96,free:8*GiB});
  for(let i=0;i<3;i++){f.run();await until(()=>f.records().length===i+1);}
  await new Promise(done=>setTimeout(done,20));
  assert.equal(f.calls.length,2,'memory limits check slots');
  assert.equal(f.calls[0].options.env.PDD_CHECK_CPUS,'48');
});

test('busy machine keeps FIFO waiting and pauses time until load falls',async t=>{
  const f=fixture(t,{count:8,load:9});f.run();await until(()=>f.records().length===1);
  await new Promise(done=>setTimeout(done,20));assert.equal(f.calls.length,0,'busy machine must defer heavy work');
  f.time+=7_200_000;
  const progress=queue.readSuiteProgress({cwd:join(f.root,'repo-0'),since:1000,env:f.env},f.ports);
  assert.equal(progress.state,'waiting');assert.equal(progress.position,1);assert.equal(progress.pausedMs,7_200_000);
  f.machine.load=8;await until(()=>f.calls.length===1);assert.equal(f.calls[0].options.timeoutMs,1_800_000);
});

for(const values of [{platform:'darwin'},{battery:true},{taskset:null}])test(`personal or hint-only check policy ${JSON.stringify(values)}`,async t=>{
  const f=fixture(t,{count:64,...values});f.run();await until(()=>f.calls.length===1);
  const expected=values.platform==='darwin'?32:values.battery?16:64;
  assert.equal(f.calls[0].options.env.PDD_CHECK_CPUS,String(expected),'default core budget is polite and hint fallback is serial');
});

test('capacity refresh scales admission and preserves existing CPU ownership after shrink',async t=>{
  const f=fixture(t,{count:64,offset:8});
  await queue.configureCheckCapacity({env:f.env},f.ports);
  for(let i=0;i<6;i++){f.run();await until(()=>f.records().length===i+1);}
  await until(()=>f.calls.length===5);
  f.machine.count=8;await queue.configureCheckCapacity({env:f.env},f.ports);
  f.calls[0].finish();await f.jobs[0];await new Promise(done=>setTimeout(done,20));
  assert.equal(f.calls.length,5,'shrinking does not admit more checks or stop running checks');
  f.machine.count=96;await queue.configureCheckCapacity({env:f.env},f.ports);await until(()=>f.calls.length===6);
  assert.equal(f.calls.at(-1).options.cpuIds.length,12);
  assert.ok(f.calls.at(-1).options.cpuIds.every(id=>id>=8),'CPU IDs retain the parent allowed mask');
});

test('overrides choose shared capacity and status is read-only',async t=>{
  const f=fixture(t,{count:64});
  const capacity=await queue.configureCheckCapacity({env:f.env,checks:3,runs:17},f.ports);
  assert.deepEqual([capacity.calculatedChecks,capacity.checks,capacity.calculatedRuns,capacity.runs,capacity.coresPerCheck],[5,3,6,17,21]);
  for(let i=0;i<4;i++){f.run();await until(()=>f.records().length===i+1);}
  await until(()=>f.calls.length===3);
  const before=readFileSync(join(f.env.PDD_SUITE_QUEUE,'capacity.json'));
  const status=queue.readCheckStatus({env:f.env,checks:3,runs:17},f.ports);
  assert.deepEqual([status.busyChecks,status.waitingChecks,status.checks],[3,1,3]);
  assert.deepEqual(readFileSync(join(f.env.PDD_SUITE_QUEUE,'capacity.json')),before);
});

test('native execution passes the CPU list and hint through an injected spawner',async()=>{
  const {EventEmitter}=await import('node:events');
  for(const affinity of [true,false]) {
    let observed;
    const result=await queue.executeSuite('literal $COMMAND',{cwd:'/synthetic',env:{PDD_CHECK_CPUS:'12'},timeoutMs:1000,onChild:()=>{},cpuIds:[8,9,10],taskset:affinity?'/fake/taskset':null},{
      spawn:(file,args,options)=>{observed={file,args,options};const child=new EventEmitter();setImmediate(()=>child.emit('close',0,null));return child;},
    });
    assert.equal(result.exitCode,0);assert.equal(observed.file,affinity?'/fake/taskset':'/bin/bash');
    assert.deepEqual(observed.args,affinity?['--cpu-list','8,9,10','/bin/bash','-c','literal $COMMAND']:['-c','literal $COMMAND']);
    assert.deepEqual([observed.options.env.PDD_CHECK_CPUS,observed.options.detached,observed.options.stdio[0]],['12',true,'ignore']);
  }
});

test('native run admission enforces calculated capacity while coordinator identity stays current',async()=>{
  const {checkDependencyStart}=await import('../src/issue-dependencies-intake.mjs');
  const repository='example/repo', issue=`https://github.com/${repository}/issues/99`;
  const coordinator={repository,coordinatorId:'c',machine:'m',activation:'a',claim:{commentId:'1',labelEventId:'2'}};
  const claim={issue,active:true,owner:'c',coordinatorId:'c',machine:'m',commentId:'1',labelEventId:'2'};
  for(const [cap,explicit,expected] of [[1,undefined,false],[2,undefined,false],[3,undefined,true],[3,1,false],[1,3,true]]) {
    const ports={
      github:{issue:async args=>({json:JSON.stringify(args.repository===repository&&args.issue===99?{number:99,labels:[]}: {error:'not-found'})})},
      settings:{read:async()=>({mode:'auto',activation:'a',capacityRuns:cap,...(explicit?{runs:explicit}:{})})},
      owners:{read:async()=>({json:JSON.stringify({localOwner:'c',runsKnown:true,claims:[claim],runs:[{issue:'https://github.com/example/repo/issues/1',runId:'one',state:'working'},{issue:'https://github.com/example/repo/issues/2',runId:'two',state:'working'}]})})},
      snapshots:{read:async()=>({snapshot:{repository,complete:true,issues:[{key:issue,nodeId:'99',title:'Ready',revision:'a'.repeat(64),state:'open',authority:'trusted',assignees:[],conditions:[],execution:'idle',holds:[]}],edges:[],reviews:[{id:'review',issue,authority:'trusted',intact:true,outcome:'complete',analysis:'Independent work',base:[],continuation:'',inputs:[{key:issue,revision:'a'.repeat(64)}],candidates:[{key:issue,revision:'a'.repeat(64)}],dependencies:[],questions:[],effects:'none'}],impacts:[],inputs:[]}})},
    };
    const result=await checkDependencyStart({repository,issue,coordinator:{...coordinator,...(explicit?{runs:explicit}:{})}},ports);
    assert.deepEqual(result,{allowed:expected,reason:expected?'ok':'runs'},'current machine capacity controls native admission');
  }
});

test('enabling affinity waits for an unconstrained running check to finish',async t=>{
  const f=fixture(t,{count:64,taskset:null});
  await queue.configureCheckCapacity({env:f.env},f.ports);f.run();await until(()=>f.calls.length===1);
  f.machine.taskset='/fake/taskset';await queue.configureCheckCapacity({env:f.env},f.ports);
  f.run();await until(()=>f.records().length===2);await new Promise(done=>setTimeout(done,20));
  assert.equal(f.calls.length,1,'unconstrained checks retain exclusive CPU ownership');
  f.calls[0].finish();await until(()=>f.calls.length===2);assert.equal(f.calls[1].options.cpuIds.length,12);
});

for(const damage of [value=>delete value.checks,value=>delete value.runs,value=>value.affinity=false,value=>value.busy='no'])
  test(`malformed saved capacity fails closed ${damage}`,async t=>{
    const f=fixture(t,{count:64}), path=join(f.env.PDD_SUITE_QUEUE,'capacity.json');
    const value=await queue.configureCheckCapacity({env:f.env},f.ports);damage(value);
    const {writeFileSync}=await import('node:fs');writeFileSync(path,JSON.stringify(value));
    assert.equal((await f.run()).exitCode,1);assert.equal(f.calls.length,0);
  });

test('invalid observations fail before heavy execution',async t=>{
  for(const ports of [{cores:()=>[]},{memory:()=>NaN},{load:()=>-1},{battery:()=> 'yes'},{taskset:()=> 'relative'}]) {
    const f=fixture(t);Object.assign(f.ports,ports);
    assert.equal((await f.run()).exitCode,1);assert.equal(f.calls.length,0);
  }
});

test('native settings reads the saved machine run cap separately from an explicit override',async t=>{
  const {fixture:workflowFixture}=await import('./helpers/workflow-runner-fixture.mjs');
  const {createDependencyReadPorts}=await import('../src/issue-dependencies-github.mjs');
  const {createHash}=await import('node:crypto');
  const {writeFileSync}=await import('node:fs');
  const f=await workflowFixture(t), stateRoot=join(f.base,'autopilot'), repository='example/project';mkdirSync(stateRoot);
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto'}}));
  const path=join(stateRoot,`${createHash('sha256').update(f.source).digest('hex').slice(0,20)}.json`);
  const state={repo:repository,cwd:f.source,enabled:true,activatedAt:'a',checkCapacity:{runs:10}};
  const read=()=>createDependencyReadPorts({cwd:f.source},{...f.ports,autopilotStateRoot:stateRoot}).settings.read({cwd:f.source,repository});
  writeFileSync(path,JSON.stringify(state));
  assert.deepEqual(await read(),{mode:'auto',activation:'a',capacityRuns:10});
  state.checkCapacity.runs=2;state.runs=7;writeFileSync(path,JSON.stringify(state));
  assert.deepEqual(await read(),{mode:'auto',activation:'a',capacityRuns:2,runs:7});
  state.checkCapacity.runs='invalid';writeFileSync(path,JSON.stringify(state));
  await assert.rejects(read());
});

test('expired busy state and override fall back to current machine capacity',async t=>{
  const f=fixture(t,{count:64,load:65});
  const saved=await queue.configureCheckCapacity({env:f.env,checks:1,owner:'lost-timer'},f.ports);
  f.run();await until(()=>f.records().length===1);f.machine.load=0;f.machine.count=8;
  f.time=saved.expiresAt-1;await new Promise(done=>setTimeout(done,20));assert.equal(f.calls.length,0);
  f.time=saved.expiresAt;await until(()=>f.calls.length===1);
  assert.equal(f.calls[0].options.env.PDD_CHECK_CPUS,'8','expired snapshots cannot hold busy state or an old CPU share');
});

test('stop releases only its own snapshot and retains running queue records',async t=>{
  const f=fixture(t,{count:64,load:65});
  await queue.configureCheckCapacity({env:f.env,checks:1,owner:'owner-a'},f.ports);
  f.run();await until(()=>f.records().length===1);f.machine.load=0;
  assert.equal(await queue.releaseCheckCapacity({env:f.env,owner:'owner-b'},f.ports),false);
  await new Promise(done=>setTimeout(done,20));assert.equal(f.calls.length,0);
  assert.equal(await queue.releaseCheckCapacity({env:f.env,owner:'owner-a'},f.ports),true);
  await until(()=>f.calls.length===1);assert.equal(f.calls[0].options.env.PDD_CHECK_CPUS,'12','stopped override cannot govern standalone work');
  await queue.configureCheckCapacity({env:f.env,owner:'owner-b'},f.ports);
  assert.equal(await queue.releaseCheckCapacity({env:f.env,owner:'owner-a'},f.ports),false);
  assert.equal(await queue.releaseCheckCapacity({env:f.env,owner:'owner-b'},f.ports),true);
  assert.equal(f.records()[0].state,'running');assert.equal(await queue.releaseCheckCapacity({env:f.env,owner:'owner-b'},f.ports),false);
});

// Repair 1: personal desktops and status must use the shared admission policy.
test('repair 1: Linux desktop without a battery reserves half the CPUs while a VM keeps its budget',async t=>{
  for(const [virtualized,usable,slots,share] of [[false,32,2,16],[true,64,5,12]]) {
    const f=fixture(t,{count:64,battery:false,virtualized});
    const capacity=await queue.configureCheckCapacity({env:f.env},f.ports);
    assert.deepEqual([capacity.personal,capacity.usableCores,capacity.checks],[!virtualized,usable,slots]);
    f.run();await until(()=>f.calls.length===1);
    assert.equal(f.calls[0].options.cpuIds.length,share);
    assert.ok(f.calls[0].options.cpuIds.every(id=>id<usable));
    const status=queue.readCheckStatus({env:f.env},f.ports);
    assert.deepEqual([status.cores,status.personal,status.usableCores],[64,!virtualized,usable]);
  }
});

test('repair 1: shared status follows the active owner across overrides, resize and expiry',async t=>{
  const f=fixture(t,{count:64}), path=join(f.env.PDD_SUITE_QUEUE,'capacity.json');
  let saved=await queue.configureCheckCapacity({env:f.env,checks:1,runs:7,owner:'repository-A'},f.ports);
  const status=()=>queue.readCheckStatus({env:f.env,checks:3,runs:19},f.ports);
  const limits=value=>[value.checks,value.runs,value.coresPerCheck,value.busyChecks,value.waitingChecks];
  f.run();await until(()=>f.calls.length===1);f.run();await until(()=>f.records().length===2);
  const before=readFileSync(path);
  assert.deepEqual(limits(status()),[1,7,64,1,1],'repository B sees the policy that keeps its check waiting');
  assert.equal(f.calls[0].options.env.PDD_CHECK_CPUS,'64');
  f.machine.count=96;
  assert.deepEqual(limits(status()),[1,7,64,1,1],'a resize takes effect only after refresh or expiry');
  assert.deepEqual(readFileSync(path),before,'status never refreshes the snapshot');
  saved=await queue.configureCheckCapacity({env:f.env,checks:2,runs:9,owner:'repository-B'},f.ports);
  assert.deepEqual(limits(status()),[2,9,48,1,1]);
  f.calls[0].finish();await until(()=>f.calls.length===2);
  assert.equal(f.calls[1].options.env.PDD_CHECK_CPUS,'48');
  f.time=saved.expiresAt;f.machine.count=8;
  assert.deepEqual(limits(status()),[1,2,8,1,0],'expired overrides do not govern status');
  assert.equal(JSON.parse(readFileSync(path)).expiresAt,saved.expiresAt,'status does not replace an expired snapshot');
  assert.equal(await queue.releaseCheckCapacity({env:f.env,owner:'repository-B'},f.ports),true);
  assert.deepEqual(limits(status()),[1,2,8,1,0],'missing snapshot uses defaults, not repository overrides');
});

test('repair 1: shared status rejects a malformed active snapshot',async t=>{
  const f=fixture(t,{count:64}), {writeFileSync}=await import('node:fs');
  await queue.configureCheckCapacity({env:f.env},f.ports);
  writeFileSync(join(f.env.PDD_SUITE_QUEUE,'capacity.json'),'{');
  assert.throws(()=>queue.readCheckStatus({env:f.env},f.ports));
});

test('repair 1: native Linux classification reserves desktop capacity when virtualization is absent or unknown',()=>{
  for(const result of [{status:1},{status:0},{status:null,error:{code:'ENOENT'}},{status:null,error:{code:'ETIMEDOUT'}}]) {
    const {ports}=checkMachine({count:64,battery:false});delete ports.virtualized;
    const calls=[];ports.spawnSync=(command,args,options)=>{calls.push({command,args,options});return result;};
    const got=queue.calculateCheckCapacity({},ports);
    assert.equal(got.usableCores,result.status===0?64:32);
    assert.equal(calls.length,1);assert.equal(calls[0].command,'systemd-detect-virt');
    assert.deepEqual(calls[0].args,['--quiet']);assert.equal(calls[0].options.timeout,1000);
  }
});

test('repair 1: Linux desktop child receives its reserved affinity share',async t=>{
  const {EventEmitter}=await import('node:events');
  const fake=checkMachine({count:4,offset:8,battery:false,virtualized:false});
  const root=mkdtempSync(join(tmpdir(),'pdd-desktop-affinity-'));
  t.after(()=>rmSync(root,{recursive:true,force:true}));
  const env={PDD_SUITE_QUEUE:join(root,'queue'),PDD_CHECK_CPUS:'999',FIXTURE:'desktop'},calls=[];
  const ports={...fake.ports,say:()=>{},spawn:(file,args,options)=>{
    calls.push({file,args,options});
    const running=JSON.parse(readFileSync(join(env.PDD_SUITE_QUEUE,'ticket-1.json')));
    assert.equal(running.state,'running');assert.deepEqual(running.cpuIds,[8,9]);
    // No native child or kernel affinity probe. Observe the complete spawn boundary.
    const child=new EventEmitter();setImmediate(()=>child.emit('close',0,null));return child;
  }};
  const result=await queue.runTestSuite({cwd:root,env,command:'controlled-build --fixture'},ports);
  assert.equal(result.exitCode,0);
  assert.equal(calls.length,1);
  assert.equal(calls[0].file,'/fake/taskset');
  assert.deepEqual(calls[0].args,['--cpu-list','8,9','/bin/bash','-c','controlled-build --fixture']);
  const childEnv=calls[0].options.env;
  assert.equal(childEnv.PDD_CHECK_CPUS,'2');
  assert.equal(childEnv.FIXTURE,undefined);assert.equal(childEnv.PDD_SUITE_QUEUE,undefined);
  assert.equal(childEnv.PATH,'/usr/bin:/bin');
  const environmentRoot=join(root,'queue');
  for(const key of ['HOME','PDD_STATE_DIR','XDG_CONFIG_HOME','TMPDIR']) {
    assert.ok(childEnv[key].startsWith(environmentRoot+'/suite-env-'));
    assert.equal(existsSync(childEnv[key]),false,'suite folders are removed after execution');
  }
  assert.deepEqual(calls[0].options,{cwd:root,env:childEnv,detached:true,stdio:['ignore','inherit','inherit']});
  const ticket=JSON.parse(readFileSync(join(env.PDD_SUITE_QUEUE,'ticket-1.json')));
  assert.equal(ticket.state,'finished');assert.deepEqual(ticket.cpuIds,[8,9]);
  assert.equal(ticket.coresPerCheck,2);assert.equal(ticket.taskset,'/fake/taskset');assert.equal(ticket.reason,null);
});

test('high machine load from processes outside Autopilot reduces check slots for that tick while Autopilot load does not',async t=>{
  const f=fixture(t,{count:64,load:36});
  const reduced=await queue.configureCheckCapacity({env:f.env},f.ports);
  assert.equal(reduced.calculatedChecks,2,'64 usable cores minus 36 outside load leaves 28 cores -> 2 check slots');
  assert.equal(reduced.outsideLoad,36);
  assert.equal(reduced.checks,2);
  for(let i=0;i<3;i++){f.run();await until(()=>f.records().length===i+1);}
  await until(()=>f.calls.length===2);
  await new Promise(done=>setTimeout(done,20));
  assert.equal(f.calls.length,2,'third check waits when outside load reduces check slots to 2');
  assert.equal((await queue.readSuiteProgress({cwd:join(f.root,'repo-2'),env:f.env},f.ports)).state,'waiting');

  // When the machine load equals only Autopilot's own running check reservations (2 * 32 = 64, or load=24 with 2 running checks), outside load is 0.
  f.machine.load=24;
  const ownOnly=await queue.configureCheckCapacity({env:f.env},f.ports);
  assert.equal(ownOnly.outsideLoad,0);
  assert.equal(ownOnly.calculatedChecks,5,'Autopilot own running check load does not reduce calculated check slots');
  assert.equal(ownOnly.checks,5);
});
