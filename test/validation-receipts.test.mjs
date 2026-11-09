import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
import {EventEmitter} from 'node:events';
import {spawn,execFileSync} from 'node:child_process';
import {runTestSuite,readSuiteProgress,executeSuite} from '../src/test-suite-queue.mjs';
import {checkMachine,withCheckLifetime} from './helpers/check-machine.mjs';
import {calculateCheckCapacity} from '../src/test-suite-queue.mjs';

const quote = s => `'${s.replaceAll("'", "'\\''")}'`;
const until = async (predicate, message) => {
  for (let n=0;n<1000;n++) { if (predicate()) return; await new Promise(r=>setTimeout(r,10)); }
  assert.fail(message);
};
function fixture(t) {
  const root=fs.mkdtempSync(join(tmpdir(),'pdd-validation-receipt-'));
  const env={PATH:process.env.PATH,HOME:join(root,'home'),XDG_CONFIG_HOME:join(root,'config'),PDD_INTERPRETER_QUEUE:join(root,'interpreter'),PDD_SUITE_QUEUE:join(root,'queue')};
  for (const dir of Object.values(env).slice(1)) fs.mkdirSync(dir,{recursive:true});
  const ports={...checkMachine({taskset:null}).ports,say:()=>{}};
  fs.writeFileSync(join(env.PDD_SUITE_QUEUE,'capacity.json'),JSON.stringify(withCheckLifetime(calculateCheckCapacity({checks:1},ports))));
  const cleanups=[];t.after(async()=>{for(const cleanup of cleanups)await cleanup();fs.rmSync(root,{recursive:true,force:true});});
  return {root,env,ports,cleanups,receipt:join(env.PDD_SUITE_QUEUE,'ticket-1.json')};
}
const read = path => JSON.parse(fs.readFileSync(path,'utf8'));
const summary = 'TAP version 13\n1..2\n# tests 2\n# suites 0\n# pass 1\n# fail 1\n# cancelled 0\n# skipped 0\n# todo 0\n';

test('validation saves full output, source and terminal counts before forwarding or returning',async t=>{
  const f=fixture(t),cwd=join(f.root,'repo');fs.mkdirSync(cwd);
  const git=(...args)=>execFileSync('git',args,{cwd,env:f.env,stdio:['ignore','pipe','pipe']}).toString().trim();
  git('init','-q');git('config','user.name','Test');git('config','user.email','test@example.invalid');
  fs.writeFileSync(join(cwd,'tracked'),'base');git('add','.');git('commit','-qm','Base');
  const head=git('rev-parse','HEAD');fs.writeFileSync(join(cwd,'tracked'),'changed');
  fs.writeFileSync(join(cwd,'untracked'),'new');
  const data='stdout-marker-'+ 'x'.repeat(180_000)+'\nstderr-marker\n'+summary;
  const program=join(f.root,'emit.cjs');
  fs.writeFileSync(program,`const fs=require('node:fs');const row=JSON.parse(fs.readFileSync(${JSON.stringify(f.receipt)}));if(!row.childPid||!row.recorderPid||!row.command||!row.source.head)process.exitCode=99;else {process.stdout.write(${JSON.stringify(data)});process.stderr.write('# pass 999\\nstderr-end\\n');process.exitCode=7;}`);
  let forwarded='';
  const output={write(bytes){const row=read(f.receipt);assert.ok(fs.readFileSync(row.logPath).includes(bytes));forwarded+=bytes;}};
  const command=`${quote(process.execPath)} ${quote(program)}`;
  const result=await runTestSuite({cwd,command,env:f.env},{...f.ports,stdout:output,stderr:output});
  assert.equal(result.exitCode,7);
  const row=read(f.receipt),log=fs.readFileSync(row.logPath,'utf8');
  assert.ok(log.includes(data));assert.ok(log.includes('stderr-end'));assert.ok(forwarded.includes(data));
  assert.equal(row.command,command);assert.equal(row.source.head,head);assert.match(row.source.fingerprint,/^[a-f0-9]{64}$/);
  assert.equal(row.source.error,null);assert.equal(row.source.runId,null);
  assert.equal(row.exitCode,7);assert.equal(row.outcome,'completed');assert.equal(row.signal,null);
  assert.deepEqual(row.counts,{tests:2,suites:0,pass:1,fail:1,cancelled:0,skipped:0,todo:0});
  assert.equal(fs.statSync(row.logPath).mode & 0o777,0o600);
  const before=fs.readFileSync(f.receipt);const progress=readSuiteProgress({cwd,env:f.env},f.ports);
  assert.equal(progress.logPath,row.logPath);assert.deepEqual(progress.counts,row.counts);
  assert.deepEqual(fs.readFileSync(f.receipt),before);
  // A nested validation must retain untracked input anywhere in the checkout.
  const nested=join(cwd,'sub');fs.mkdirSync(nested);
  const first=await runTestSuite({cwd:nested,command:'true',env:f.env},{...f.ports,stdout:{write(){}}});
  assert.equal(first.exitCode,0);const firstSource=read(join(f.env.PDD_SUITE_QUEUE,'ticket-2.json')).source;
  fs.writeFileSync(join(cwd,'untracked'),'different input outside validation cwd');
  const next=await runTestSuite({cwd:nested,command:'true',env:f.env},{...f.ports,stdout:{write(){}}});
  assert.equal(next.exitCode,0);const nextSource=read(join(f.env.PDD_SUITE_QUEUE,'ticket-3.json')).source;
  assert.equal(firstSource.head,nextSource.head);assert.notEqual(firstSource.fingerprint,nextSource.fingerprint);
});

test('validation custody survives caller loss and a fresh session observes the same command',async t=>{
  const f=fixture(t),release=join(f.root,'release'),started=join(f.root,'started'),invocations=join(f.root,'invocations');
  const program=join(f.root,'hold.cjs');
  fs.writeFileSync(program,`const fs=require('node:fs');fs.appendFileSync(${JSON.stringify(invocations)},'once\\n');process.stdout.write('before-session-change\\n'+'z'.repeat(140000)+'\\n');fs.writeFileSync(${JSON.stringify(started)},'1');const timer=setInterval(()=>{if(fs.existsSync(${JSON.stringify(release)})){clearInterval(timer);process.stderr.write('after-session-change\\n');process.stdout.write(${JSON.stringify(summary)});process.exitCode=7;}},10);`);
  const module=resolve('src/test-suite-queue.mjs'),machine=resolve('test/helpers/check-machine.mjs');
  const command=`${quote(process.execPath)} ${quote(program)}`;
  const caller=spawn(process.execPath,['--input-type=module','-e',`import {runTestSuite} from ${JSON.stringify(module)};import {checkMachine} from ${JSON.stringify(machine)};const r=await runTestSuite({cwd:${JSON.stringify(f.root)},command:${JSON.stringify(command)},env:process.env},{...checkMachine({taskset:null}).ports,say:()=>{}});process.exitCode=r.exitCode;`],{env:f.env,stdio:['ignore','pipe','pipe']});
  caller.stdout.resume();caller.stderr.resume();
  const ended=new Promise(done=>caller.once('close',(code,signal)=>done({code,signal})));
  // Cleanup always releases our command, including when the base assertion fails.
  f.cleanups.push(async()=>{fs.writeFileSync(release,'1');if(caller.exitCode===null&&caller.signalCode===null)caller.kill('SIGTERM');await ended;await until(()=>!fs.existsSync(started)||readSuiteProgress({cwd:f.root,env:f.env},f.ports).state==='finished','owned validation must settle');});
  await until(()=>fs.existsSync(started),'controlled command starts');
  const before=read(f.receipt);assert.ok(before.logPath,'durable full-output path must exist while validation runs');
  assert.ok(before.recorderPid);assert.ok(before.childPid);assert.equal(before.command,command);
  await until(()=>fs.readFileSync(before.logPath,'utf8').includes('before-session-change'),'output is durable before session ends');
  caller.kill('SIGKILL');assert.equal((await ended).signal,'SIGKILL');
  const observed=readSuiteProgress({cwd:f.root,env:{...f.env,HOME:join(f.root,'next-session')}},f.ports);
  assert.equal(observed.state,'running');assert.equal(observed.recorderPid,before.recorderPid);assert.equal(observed.childPid,before.childPid);
  fs.writeFileSync(release,'1');await until(()=>read(f.receipt).state==='finished','recorder saves terminal result without caller');
  const after=read(f.receipt);assert.equal(after.exitCode,7);assert.equal(after.outcome,'completed');assert.equal(after.counts.fail,1);
  assert.ok(fs.readFileSync(after.logPath,'utf8').includes('after-session-change'));
  assert.equal(fs.readFileSync(invocations,'utf8'),'once\n');
  assert.equal(fs.readdirSync(f.env.PDD_SUITE_QUEUE).filter(p=>/^ticket-.*\.json$/.test(p)).length,1);
  assert.equal(fs.readdirSync(f.env.PDD_SUITE_QUEUE).some(p=>p.startsWith('suite-env-')),false);
});

test('missing complete counts and dead recorder identity never invent a passing receipt',async t=>{
  const f=fixture(t);
  const r=await runTestSuite({cwd:f.root,command:"printf '# tests 2\\n# pass 2\\n'",env:f.env},{...f.ports,stdout:{write(){}}});
  assert.equal(r.exitCode,0);assert.equal(read(f.receipt).counts,null);
  const row=read(f.receipt);Object.assign(row,{state:'running',finishedAt:null,pid:9001,recorderPid:9002,recorderIdentity:'old',childPid:9003,exitCode:null,outcome:'running'});
  fs.writeFileSync(f.receipt,JSON.stringify(row));const before=fs.readFileSync(f.receipt);
  const status=readSuiteProgress({cwd:f.root,env:f.env},{...f.ports,alive:pid=>pid===9002,processIdentity:()=> 'replacement'});
  assert.equal(status.outcome,'unknown');assert.equal(status.exitCode,null);assert.equal(status.counts,null);
  assert.deepEqual(fs.readFileSync(f.receipt),before);
});

test('child start gate refuses validation when saving custody fails',async t=>{
  const f=fixture(t),marker=join(f.root,'must-not-run');
  const result=await executeSuite(`touch ${quote(marker)}`,{cwd:f.root,env:f.env,timeoutMs:2000,startGate:true,onChild:()=>{Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0,100);throw Object.assign(Error('denied'),{code:'EACCES'});}});
  assert.equal(result.exitCode,1);assert.equal(fs.existsSync(marker),false);
});


test('count receipt rejects stdout summaries without TAP framing or followed by unfinished output',async t=>{
  for(const output of [summary.replace('TAP version 13\n1..2\n',''),summary+'not ok 3 - unfinished\n',summary+'truncated']) {
    const f=fixture(t),program=join(f.root,'misleading.cjs');
    fs.writeFileSync(program,`process.stdout.write(${JSON.stringify(output)});`);
    const result=await runTestSuite({cwd:f.root,command:`${quote(process.execPath)} ${quote(program)}`,env:f.env},{...f.ports,stdout:{write(){}}});
    assert.equal(result.exitCode,0);assert.equal(read(f.receipt).counts,null);
  }
});


for (const uncertain of [false,true]) test(`validation confirms descendant termination before completion (uncertain=${uncertain})`,async()=>{
  let probes=0,sleeps=0;const signals=[];
  const result=await executeSuite('controlled-validation',{cwd:'/synthetic',env:{},timeoutMs:5000,onChild:()=>{}},{
    spawn:()=>{const child=new EventEmitter();child.pid=987654;setImmediate(()=>child.emit('close',0,null));return child;},
    kill:(pid,signal)=>signals.push({pid,signal}),
    groupAlive:()=>{probes++;return uncertain?null:probes<3?true:false;},sleep:async()=>{sleeps++;},
  });
  assert.equal(result.ownershipConfirmed,!uncertain);assert.equal(result.exitCode,uncertain?1:0);
  assert.equal(probes,uncertain?101:3);assert.equal(sleeps,uncertain?100:2);
  assert.deepEqual(signals,[{pid:-987654,signal:'SIGKILL'}]);
});


test('native injected spawner retains its ticket and environment when descendants are uncertain',async t=>{
  const f=fixture(t);let environment;
  const result=await runTestSuite({cwd:f.root,command:'controlled-validation',env:f.env},{...f.ports,
    spawn:(_file,_args,options)=>{environment=options.env;const child=new EventEmitter();child.pid=987654;setImmediate(()=>child.emit('close',0,null));return child;},
    kill:()=>{},groupAlive:()=>null,sleep:async()=>{},alive:()=>true,
  });
  assert.equal(result.exitCode,1);
  const row=read(f.receipt);assert.equal(row.state,'running');assert.equal(row.outcome,'unknown');
  assert.equal(row.exitCode,null);assert.equal(row.finishedAt,null);assert.equal(row.childPid,987654);
  for(const key of ['HOME','PDD_STATE_DIR','XDG_CONFIG_HOME','TMPDIR','PDD_INTERPRETER_QUEUE']) assert.equal(fs.existsSync(environment[key]),true,key);
  const progress=readSuiteProgress({cwd:f.root,env:f.env},{...f.ports,alive:()=>true});
  assert.equal(progress.state,'running');assert.equal(progress.outcome,'unknown');
});
