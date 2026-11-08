import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, rmSync, readdirSync, readFileSync } from 'node:fs';
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
