import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
import {createHash} from 'node:crypto';
import {EventEmitter} from 'node:events';
import {spawn,execFileSync} from 'node:child_process';
import {runTestSuite,readSuiteProgress,executeSuite} from '../src/test-suite-queue.mjs';
import {checkMachine,withCheckLifetime} from './helpers/check-machine.mjs';
import {calculateCheckCapacity} from '../src/test-suite-queue.mjs';
import {checkRuntimeHealth} from '../src/runtime-client.mjs';
import {runAutopilotDoctor} from '../src/autopilot-doctor.mjs';
import {doctorFixture} from './helpers/doctor-fixture.mjs';
import {redactSecrets} from '../src/secret-redaction.mjs';
import {loadAgentDefinitions} from '../src/agent-config.mjs';
import {redactingLines,MAX_EVIDENCE_LINE_BYTES,MAX_VALIDATION_LOG_BYTES,MAX_VALIDATION_RECEIPT_BYTES} from '../src/validation-evidence.mjs';

const quote = s => `'${s.replaceAll("'", "'\\''")}'`;
const until = async (predicate, message) => {
  for (let n=0;n<1000;n++) { if (predicate()) return; await new Promise(r=>setTimeout(r,10)); }
  assert.fail(message);
};
function fixture(t) {
  const root=fs.mkdtempSync(join(tmpdir(),'pdd-validation-receipt-'));
  const env={PATH:process.env.PATH,HOME:join(root,'home'),XDG_CONFIG_HOME:join(root,'config'),PDD_SUITE_QUEUE:join(root,'queue')};
  for (const dir of Object.values(env).slice(1)) fs.mkdirSync(dir,{recursive:true});
  const ports={...checkMachine({taskset:null}).ports,say:()=>{}};
  fs.writeFileSync(join(env.PDD_SUITE_QUEUE,'capacity.json'),JSON.stringify(withCheckLifetime(calculateCheckCapacity({checks:1},ports))));
  const cleanups=[];t.after(async()=>{for(const cleanup of cleanups)await cleanup();fs.rmSync(root,{recursive:true,force:true});});
  return {root,env,ports,cleanups,receipt:join(env.PDD_SUITE_QUEUE,'ticket-1.json')};
}
const read = path => JSON.parse(fs.readFileSync(path,'utf8'));
const summary = 'TAP version 13\n1..2\n# tests 2\n# suites 0\n# pass 1\n# fail 1\n# cancelled 0\n# skipped 0\n# todo 0\n';

test('012 fix-ups 2: agents.json child environment credentials are safe without doctor',async t=>{
  const f=fixture(t),prefix='opaque-agent-config-child-',tail='PRIVATE-SUFFIX',secret=prefix+tail,program=join(f.root,'agent-env.cjs'),writes=[];
  const folder=join(f.env.HOME,'.config','pdd');fs.mkdirSync(folder,{recursive:true});
  fs.writeFileSync(join(folder,'agents.json'),JSON.stringify({include_defaults:false,
    agents:[{name:'Custom',kind:'codex',command:process.execPath,env:{CUSTOM_TOKEN:prefix,CUSTOM_API_KEY:secret}}]}));
  const [agent]=loadAgentDefinitions({cwd:f.root,env:f.env});
  assert.equal(agent.env.CUSTOM_API_KEY,secret);assert.equal(f.env.CUSTOM_API_KEY,undefined);
  // The launcher passes the loaded override to the real validation child.
  // The child reads the value only from its own environment.
  fs.writeFileSync(program,`const value=process.env.CUSTOM_API_KEY;(async()=>{for(const stream of ['stdout','stderr']){for(let i=0;i<value.length;i+=7)await new Promise(done=>process[stream].write(value.slice(i,i+7),done));await new Promise(done=>process[stream].write('\\nchild-env-safe\\n',done));}})();`);
  let forwarded='';const capture={write(bytes){forwarded+=bytes;}};
  const disk={...fs,writeFileSync(path,data,options){if(String(path).includes('ticket-'))writes.push(String(data));return fs.writeFileSync(path,data,options);}};
  const result=await runTestSuite({cwd:f.root,command:`CUSTOM_TOKEN=${quote(agent.env.CUSTOM_TOKEN)} CUSTOM_API_KEY=${quote(agent.env.CUSTOM_API_KEY)} ${quote(agent.command)} ${quote(program)}`,env:f.env},
    {...f.ports,fs:disk,stdout:capture,stderr:capture,source:()=>({head:null,fingerprint:null,runId:null,issue:null,error:secret})});
  assert.equal(result.exitCode,0);assert.ok(writes.length>=3);
  const row=read(f.receipt),log=fs.readFileSync(row.logPath,'utf8');
  assert.equal(row.outcome,'completed');
  for(const saved of [log,forwarded,fs.readFileSync(f.receipt,'utf8'),...writes]) {
    assert.equal(saved.includes(secret),false);assert.equal(saved.includes(tail),false);
  }
  for(const saved of [log,forwarded])assert.equal(saved.split('child-env-safe').length-1,2);
});

test('012 fix-ups 2: overlapping values stay safe in all receipt writes and returned errors',async t=>{
  for(const reverse of [false,true]) {
    const f=fixture(t),short=`opaque-error-${reverse}-prefix`,long=short+'CONFIDENTIAL-TAIL',writes=[];
    Object.assign(f.env,reverse?{LONG_PASSWORD:long,SHORT_TOKEN:short}:{SHORT_TOKEN:short,LONG_PASSWORD:long});
    const disk={...fs,writeFileSync(path,data,options){if(String(path).includes('ticket-'))writes.push(String(data));return fs.writeFileSync(path,data,options);}};
    const result=await runTestSuite({cwd:f.root,command:'true',env:f.env},{...f.ports,fs:disk,
      source:()=>({head:null,fingerprint:null,runId:null,issue:null,error:long}),alive:pid=>pid===process.pid,
      execute:async(_command,options)=>{options.onChild(987654321);throw Error('provider reply '+long);}});
    assert.equal(result.exitCode,1);assert.ok(writes.length>=3);
    for(const saved of [result.message,fs.readFileSync(f.receipt,'utf8'),...writes])assert.equal(saved.includes('CONFIDENTIAL-TAIL'),false);
    assert.equal(read(f.receipt).outcome,'completed');
  }
});

test('012 fix-ups 2: queue reset preserves both logs and permits validation again',async t=>{
  const f=fixture(t),capture={write(){}};
  const run=()=>runTestSuite({cwd:f.root,command:'printf "retained-log\\n"',env:f.env},{...f.ports,stdout:capture,stderr:capture});
  assert.equal((await run()).exitCode,0);
  const before=read(f.receipt),original=fs.readFileSync(before.logPath);
  fs.rmSync(f.env.PDD_SUITE_QUEUE,{recursive:true});
  assert.equal((await run()).exitCode,0,'queue reset must permit a new attempt');
  const after=read(f.receipt);
  assert.equal(before.ticket,after.ticket);assert.notEqual(before.logPath,after.logPath);
  assert.deepEqual(fs.readFileSync(before.logPath),original);assert.deepEqual(fs.readFileSync(after.logPath),original);
  for(const row of [before,after])assert.equal(fs.statSync(row.logPath).mode&0o777,0o600);
});

test('012 fix-ups 2: an existing log file selects a fresh attempt name',async t=>{
  const f=fixture(t),attempts=[],capture={write(){}};
  const disk={...fs,writeFileSync(path,data,options){
    if(options?.flag==='wx'&&String(path).endsWith('.log')) {
      attempts.push(String(path));
      if(attempts.length===1)fs.writeFileSync(path,'prior-attempt',{mode:0o600,flag:'wx'});
    }
    return fs.writeFileSync(path,data,options);
  }};
  const result=await runTestSuite({cwd:f.root,command:'printf "fresh-attempt\\n"',env:f.env},
    {...f.ports,fs:disk,stdout:capture,stderr:capture});
  assert.equal(result.exitCode,0,'existing evidence must not block validation');
  assert.equal(attempts.length,2);assert.notEqual(attempts[0],attempts[1]);
  assert.equal(fs.readFileSync(attempts[0],'utf8'),'prior-attempt');
  assert.equal(fs.readFileSync(read(f.receipt).logPath,'utf8'),'fresh-attempt\n');
});

test('integration fix-up: pending sensitive fields cover the assignment grammar on both streams',async t=>{
  const f=fixture(t),rows=[];
  const fields=['key','token','password','secret','api_key','api-key','apikey','authorization','cookie','credential'];
  // Every ECMAScript whitespace character allowed by the shared \s grammar.
  const whitespace=['',' ', '\t','\r','\n','\v','\f','\u00a0','\u1680',
    ...Array.from({length:11},(_,i)=>String.fromCodePoint(0x2000+i)),
    '\u2028','\u2029','\u202f','\u205f','\u3000','\ufeff',' \t\r\n', '\n\n'];
  const gaps=whitespace.map(space=>[space,space]).concat([['\n',''],['','\n'],['\r\n\t',' \n\r']]);
  for(const field of fields) for(const [before,after] of gaps)
    for(const [left,right,separator] of [['','','='],['"','"',':'],["'","'",'=']])
      for(const valueQuote of ['', '"', "'"]) {
        const secret=`synthetic-pending-${rows.length}-credential`;
        const assignment=`${left}${field.toUpperCase()}${right}${before}${separator}${after}${valueQuote}${secret}${valueQuote}\n`;
        rows.push({assignment,secret,omitted:0});
      }
  const regularRows=rows.length;
  // Overflow before the separator or value, on the same or an earlier line.
  for(const beforeSeparator of [false,true]) for(const multiline of [false,true]) for(const valueQuote of ['', '"', "'"]) {
    const secret=`synthetic-pending-${rows.length}-credential`;
    const space=' '.repeat(MAX_EVIDENCE_LINE_BYTES)+(multiline?'\n\t\r\n':'');
    const assignment=`"password"${beforeSeparator?space:''}:${beforeSeparator?'':space}${valueQuote}${secret}${valueQuote}\n`;
    const omitted=assignment.split(/(?<=\n)/).reduce((sum,line)=>sum+(Buffer.byteLength(line)>MAX_EVIDENCE_LINE_BYTES?Buffer.byteLength(line):0),0);
    rows.push({assignment,secret,omitted});
  }
  const safe='safe-after-field\n';
  let splits=0,overflowWrites=0;
  for(const [index,row] of rows.entries()) {
    assert.equal(redactSecrets(row.assignment).includes(row.secret),false,`shared grammar row ${index}`);
    const input=Buffer.from(row.assignment+safe);
    const check=parts=>{
      let saved='',omitted=0;
      const stream=redactingLines((text,count)=>{
        assert.equal(text.includes(row.secret),false,`stream credential exposure at row ${index}`);
        saved+=text;omitted+=count;
      });
      for(const part of parts)stream.write(part);
      stream.end();
      assert.equal(saved.includes(row.secret),false,`stream credential exposure at row ${index}`);
      assert.ok(saved.endsWith(safe));assert.equal(omitted,row.omitted);
    };
    if(index<regularRows) {
      // Include splits inside UTF-8 whitespace and either end of the transport.
      for(let split=0;split<=input.length;split++) {
        check([input.subarray(0,split),input.subarray(split)]);splits++;
      }
    } else for(const width of [1,4093,65536]) {
      const parts=[];for(let offset=0;offset<input.length;offset+=width)parts.push(input.subarray(offset,offset+width));
      check(parts);overflowWrites++;
    }
  }
  assert.equal(regularRows,2790);assert.equal(rows.length,2802);
  assert.equal(splits,186969);assert.equal(overflowWrites,36);
  // Real recorder boundary: the same grammar corpus reaches disk and caller.
  // A field pending on one stream must not suppress the other stream's sentinel.
  for(const channel of ['stdout','stderr']) {
    const program=join(f.root,`pending-${channel}.cjs`),inputPath=join(f.root,`pending-${channel}.input`);
    const data=rows.map(row=>row.assignment+safe).join('');fs.writeFileSync(inputPath,data);
    const other=channel==='stdout'?'stderr':'stdout',sentinel=`independent-${other}\n`;
    fs.writeFileSync(program,`const fs=require('node:fs');const data=fs.readFileSync(${JSON.stringify(inputPath)});const write=(stream,bytes)=>new Promise(done=>process[stream].write(bytes,done));(async()=>{await write(${JSON.stringify(channel)},'password=\\n');await write(${JSON.stringify(other)},${JSON.stringify(sentinel)});await write(${JSON.stringify(channel)},'"synthetic-isolated-credential"\\n');for(let i=0;i<data.length;i+=4093)await write(${JSON.stringify(channel)},data.subarray(i,i+4093));await write('stdout',${JSON.stringify(summary)});process.exitCode=7;})();`);
    let forwarded='';const capture={write(bytes){
      const row=read(f.receipt);assert.ok(fs.readFileSync(row.logPath).includes(bytes));
      assert.doesNotMatch(String(bytes),/synthetic-(?:pending-\d+|isolated)-credential/);
      forwarded+=bytes;
    }};
    const result=await runTestSuite({cwd:f.root,command:`${quote(process.execPath)} ${quote(program)}`,env:f.env},
      {...f.ports,stdout:capture,stderr:capture});
    const row=read(f.receipt),log=fs.readFileSync(row.logPath,'utf8');
    assert.equal(result.exitCode,7);assert.equal(row.exitCode,7);assert.equal(row.outcome,'completed');
    assert.equal(row.state,'finished');assert.equal(row.signal,null);
    assert.deepEqual(row.counts,{tests:2,suites:0,pass:1,fail:1,cancelled:0,skipped:0,todo:0});
    for(const text of [log,forwarded,fs.readFileSync(f.receipt,'utf8')])
      assert.doesNotMatch(text,/synthetic-(?:pending-\d+|isolated)-credential/);
    assert.equal(forwarded,log);assert.ok(log.includes(sentinel));
    assert.equal(log.split(safe).length-1,rows.length);
    assert.ok(Buffer.byteLength(log)<=MAX_VALIDATION_LOG_BYTES);
    assert.ok(fs.statSync(f.receipt).size<=MAX_VALIDATION_RECEIPT_BYTES);
    assert.deepEqual(row.evidence,{outputBytes:Buffer.byteLength('password=\n"synthetic-isolated-credential"\n'+sentinel+data+summary),
      logBytes:Buffer.byteLength(log),omittedBytes:rows.reduce((sum,row)=>sum+row.omitted,0),truncated:true});
    // Select the next native attempt's receipt for its forwarding assertions.
    f.receipt=join(f.env.PDD_SUITE_QUEUE,'ticket-2.json');
  }
  t.diagnostic(JSON.stringify({regularRows,overflowRows:rows.length-regularRows,splits,overflowWrites,nativeRuns:2}));
});

for (const kind of ['quoted secret','private key']) for (const split of [false,true])
test(`repair 2: overflow retains ${kind} state (transport splits=${split})`,async t=>{
  const f=fixture(t),program=join(f.root,'overflow-secret.cjs');
  const secret='synthetic-overflow-continuation-value';
  const opener=kind==='quoted secret'?'password="':'-----BEGIN PRIVATE KEY-----';
  const closing=kind==='quoted secret'?'"\n':'\n-----END PRIVATE KEY-----\n';
  const opening=opener+'x'.repeat(262144)+'\n';
  const continuation=secret+closing;
  const safe='safe-after-secret\n',data=opening+continuation+safe+summary;
  const input=join(f.root,'input');fs.writeFileSync(input,data);
  // Await each write and yield between awkward boundaries. The helper tests
  // also force these exact boundaries without depending on OS pipe batching.
  const boundaries=split?[0,3,opener.length-2,opener.length,262143,262144,
    opening.length-1,opening.length,opening.length+secret.length+1,data.length-7,data.length]:[0,data.length];
  fs.writeFileSync(program,`const fs=require('node:fs');const data=fs.readFileSync(${JSON.stringify(input)});const boundaries=${JSON.stringify(boundaries)};(async()=>{for(let i=1;i<boundaries.length;i++){await new Promise(done=>process.stdout.write(data.subarray(boundaries[i-1],boundaries[i]),done));await new Promise(done=>setTimeout(done,5));}process.exitCode=7;})();`);
  let forwarded='';const output={write(bytes){
    const row=read(f.receipt);
    assert.ok(fs.readFileSync(row.logPath).includes(bytes));
    assert.equal(String(bytes).includes(secret),false);
    forwarded+=bytes;
  }};
  const result=await runTestSuite({cwd:f.root,command:`${quote(process.execPath)} ${quote(program)}`,env:f.env},
    {...f.ports,stdout:output,stderr:output});
  const row=read(f.receipt),log=fs.readFileSync(row.logPath,'utf8');
  assert.equal(result.exitCode,7);assert.equal(row.exitCode,7);
  assert.equal(row.outcome,'completed');assert.equal(row.state,'finished');assert.equal(row.signal,null);
  assert.deepEqual(row.counts,{tests:2,suites:0,pass:1,fail:1,cancelled:0,skipped:0,todo:0});
  for(const saved of [log,forwarded,fs.readFileSync(f.receipt,'utf8')])assert.equal(saved.includes(secret),false);
  assert.ok(log.includes('[redacted]'));assert.ok(log.includes(safe));assert.ok(forwarded.includes(safe));
  assert.match(log,new RegExp(`\\[${Buffer.byteLength(opening)} bytes omitted\\]`));
  assert.equal(forwarded,log);
  assert.deepEqual(row.evidence,{outputBytes:Buffer.byteLength(data),logBytes:Buffer.byteLength(log),
    omittedBytes:Buffer.byteLength(opening),truncated:true});
});

test('recorder exit waits for its remaining IPC messages and close',async t=>{
  const f=fixture(t),child=new EventEmitter();child.pid=process.pid;child.connected=true;
  let started;const ready=new Promise(resolve=>{started=resolve;});
  child.send=message=>{if(message.start)started(message.start);};
  const run=runTestSuite({cwd:f.root,command:'false',env:f.env},{...f.ports,spawnRecorder:()=>{
    queueMicrotask(()=>child.emit('spawn'));return child;
  }});
  const start=await ready;
  let settled=false;run.then(()=>{settled=true;});
  child.emit('exit',0,null);
  await new Promise(resolve=>setImmediate(resolve));
  assert.equal(settled,false,'exit must not discard pending IPC');
  const record={...start.record,state:'finished',outcome:'completed',exitCode:7,signal:null,finishedAt:Date.now()};
  fs.writeFileSync(record.receiptPath,JSON.stringify(record));
  fs.rmSync(start.environmentRoot,{recursive:true,force:true});
  child.emit('message',{result:{exitCode:7,record}});
  child.emit('close',0,null);
  assert.equal((await run).exitCode,7);
});

test('recorder close without a terminal message reports failure',async t=>{
  const f=fixture(t),child=new EventEmitter();child.pid=process.pid;child.connected=true;
  let started;const ready=new Promise(resolve=>{started=resolve;});
  child.send=message=>{if(message.start)started(message.start);};
  const run=runTestSuite({cwd:f.root,command:'false',env:f.env},{...f.ports,spawnRecorder:()=>{
    queueMicrotask(()=>child.emit('spawn'));return child;
  }});
  const start=await ready;
  child.emit('exit',1,null);child.emit('close',1,null);
  const result=await run;
  assert.equal(result.exitCode,1);
  assert.match(result.message,/Validation recorder ended without a terminal receipt/);
  fs.rmSync(start.environmentRoot,{recursive:true,force:true});
});

test('recorder drains a queued terminal report before disconnecting',async t=>{
  const f=fixture(t),logPath=join(f.root,'output.log');fs.writeFileSync(logPath,'');
  // Delay the terminal transport write for one event-loop turn. This models a
  // write queued behind output without timing assumptions or large buffers.
  const module=resolve('src/test-suite-recorder.mjs');
  const child=spawn(process.execPath,['--input-type=module','-e',`
    const send=process.send.bind(process);
    process.send=(message,callback)=>{
      if(message.result){setImmediate(()=>send(message,callback));return false;}
      return send(message,callback);
    };
    await import(${JSON.stringify(module)});
  `],{cwd:f.root,env:f.env,stdio:['ignore','ignore','pipe','ipc']});
  let terminal=null,stderr='';
  child.stderr.on('data',bytes=>{stderr+=bytes;});
  child.on('message',message=>{if(message.result)terminal=message.result;});
  const ended=new Promise((done,reject)=>{child.once('error',reject);child.once('close',(code,signal)=>done({code,signal}));});
  child.once('spawn',()=>child.send({start:{
    command:`printf %s ${quote(summary)}; exit 7`,cwd:f.root,env:f.env,timeoutMs:2000,
    record:{receiptPath:f.receipt,logPath,state:'running',outcome:'running'},
  }}));
  const exit=await ended;
  const row=read(f.receipt);
  assert.equal(exit.code,0,stderr);assert.equal(row.exitCode,7);
  assert.ok(terminal,'saved terminal receipt must reach a connected caller after queued output');
  assert.equal(terminal.exitCode,7);assert.equal(terminal.record.outcome,'completed');
  assert.deepEqual(terminal.record,row);assert.equal(fs.readFileSync(logPath,'utf8'),summary);
});

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
  assert.equal(result.exitCode,7,JSON.stringify(result));
  const row=read(f.receipt),log=fs.readFileSync(row.logPath,'utf8');
  assert.ok(log.includes(data));assert.ok(log.includes('stderr-end'));assert.ok(forwarded.includes(data));
  assert.equal(row.command.includes(command),false);assert.equal(row.commandFingerprint,createHash('sha256').update(command).digest('hex'));assert.equal(row.source.head,head);assert.match(row.source.fingerprint,/^[a-f0-9]{64}$/);
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
  assert.ok(before.recorderPid);assert.ok(before.childPid);assert.equal(before.command.includes(command),false);assert.equal(before.commandFingerprint,createHash('sha256').update(command).digest('hex'));
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
  for(const key of ['HOME','PDD_STATE_DIR','XDG_CONFIG_HOME','TMPDIR']) assert.equal(fs.existsSync(environment[key]),true,key);
  const progress=readSuiteProgress({cwd:f.root,env:f.env},{...f.ports,alive:()=>true});
  assert.equal(progress.state,'running');assert.equal(progress.outcome,'unknown');
});

test('repair 1: synthetic credentials are absent from logs, forwarded output and every receipt write',async t=>{
  const f=fixture(t), program=join(f.root,'credentials.cjs');
  const positional='review-only-credential-'+'ab'.repeat(20);
  const values=[positional,'pair-token-value','pair-key-value','pair-password-value',
    'ghp_'+'x'.repeat(36),'github_pat_'+'y'.repeat(42),'sk-proj-'+'z'.repeat(40),
    'AIza'+'a'.repeat(35),'ya29.'+'b'.repeat(40),'url-user','url-password','url-query'];
  const lines=[`Authorization: Bearer ${positional}`, 'token='+values[1], 'key='+values[2],
    'password="'+values[3]+'"',...values.slice(4,9),
    `https://${values[9]}:${values[10]}@example.invalid/test?key=${values[11]}`];
  fs.writeFileSync(program,`process.stdout.write(${JSON.stringify(lines.join('\n')+'\n')});process.stderr.write('Authorization: Custom '+process.argv[2]+'\\n');`);
  const writes=[]; const disk={...fs,writeFileSync(path,data,options){if(String(path).includes('ticket-'))writes.push(String(data));return fs.writeFileSync(path,data,options);}};
  let forwarded='';const output={write(bytes){forwarded+=bytes;}};
  const command=`${quote(process.execPath)} ${quote(program)} ${quote(positional)}`;
  const result=await runTestSuite({cwd:f.root,command,env:f.env},{...f.ports,fs:disk,stdout:output,stderr:output,
    source:()=>({head:'a'.repeat(40),fingerprint:'b'.repeat(64),runId:null,issue:3117,error:`password=${values[3]}`})});
  assert.equal(result.exitCode,0);
  const row=read(f.receipt),log=fs.readFileSync(row.logPath,'utf8');
  assert.ok(log.includes('[redacted]'));assert.ok(writes.length>=3);
  for (const value of values) for(const saved of [log,forwarded,fs.readFileSync(f.receipt,'utf8'),...writes])
    assert.equal(saved.includes(value),false,'synthetic credential must be absent');
  assert.equal(row.commandFingerprint,createHash('sha256').update(command).digest('hex'));
});

test('repair 1: split credentials never reach disk while a partial line is pending',async t=>{
  const f=fixture(t),program=join(f.root,'split.cjs'),release=join(f.root,'release'),ready=join(f.root,'ready');
  const secret='split-only-credential-'+'xy'.repeat(20),prefix=secret.slice(0,32);
  fs.writeFileSync(program,`const fs=require('node:fs');process.stdout.write('Authorization: Bea');process.stderr.write('password="'+${JSON.stringify(prefix)});fs.writeFileSync(${JSON.stringify(ready)},'1');const timer=setInterval(()=>{if(fs.existsSync(${JSON.stringify(release)})){clearInterval(timer);process.stdout.write('rer '+${JSON.stringify(secret)}+'\\n');process.stderr.write(${JSON.stringify(secret.slice(32))}+'"\\n');}},10);`);
  const running=runTestSuite({cwd:f.root,command:`${quote(process.execPath)} ${quote(program)}`,env:f.env},{...f.ports,stdout:{write(){}},stderr:{write(){}}});
  f.cleanups.push(async()=>{fs.writeFileSync(release,'1');await running;});
  await until(()=>fs.existsSync(ready),'split command reaches the partial-line boundary');
  // Give the parent pipe reader time to receive the first writes.
  await new Promise(done=>setTimeout(done,100));
  const row=read(f.receipt);
  assert.equal(fs.readFileSync(row.logPath,'utf8').includes(prefix),false);
  fs.writeFileSync(release,'1');assert.equal((await running).exitCode,0);
  const saved=fs.readFileSync(row.logPath,'utf8');
  assert.equal(saved.includes(secret),false);assert.equal(saved.includes(prefix),false);
  assert.ok(saved.includes('[redacted]'));
});

test('repair 1: large output keeps bounded ends, exact omissions, counts and exit status',async t=>{
  const f=fixture(t),program=join(f.root,'large.cjs');
  const data='begin-evidence\n'+('x'.repeat(4095)+'\n').repeat(1024)+'end-evidence\n'+summary;
  fs.writeFileSync(program,`process.stdout.write(${JSON.stringify(data)});process.exitCode=7;`);
  const result=await runTestSuite({cwd:f.root,command:`${quote(process.execPath)} ${quote(program)}`,env:f.env},{...f.ports,stdout:{write(){}},stderr:{write(){}}});
  assert.equal(result.exitCode,7);
  const row=read(f.receipt),log=fs.readFileSync(row.logPath),part=(1048576-128)/2;
  assert.ok(log.length<=1048576);assert.ok(fs.statSync(f.receipt).size<=65536);
  assert.deepEqual(log.subarray(0,part),Buffer.from(data).subarray(0,part));
  assert.deepEqual(log.subarray(-part),Buffer.from(data).subarray(-part));
  const omitted=Buffer.byteLength(data)-2*part;
  assert.match(log.toString(),new RegExp(`\\[${omitted} bytes omitted\\]`));
  assert.deepEqual(row.evidence,{outputBytes:Buffer.byteLength(data),logBytes:log.length,omittedBytes:omitted,truncated:true});
  assert.deepEqual(row.counts,{tests:2,suites:0,pass:1,fail:1,cancelled:0,skipped:0,todo:0});
  assert.equal(row.outcome,'completed');assert.equal(row.source.error!==undefined,true);
  const previous=fs.readFileSync(f.receipt);
  assert.equal((await runTestSuite({cwd:f.root,command:'true',env:f.env},{...f.ports,stdout:{write(){}}})).exitCode,0);
  assert.deepEqual(fs.readFileSync(f.receipt),previous);assert.deepEqual(fs.readFileSync(row.logPath),log);
});

test('repair 1: oversized unterminated lines are suppressed and final counts remain exact',async t=>{
  const f=fixture(t),program=join(f.root,'oversized.cjs'),n=4194304;
  fs.writeFileSync(program,`process.stdout.write(Buffer.alloc(${n},120));process.stdout.write('\\n'+${JSON.stringify(summary)});`);
  const result=await runTestSuite({cwd:f.root,command:`${quote(process.execPath)} ${quote(program)}`,env:f.env},{...f.ports,stdout:{write(){}}});
  assert.equal(result.exitCode,0);
  const row=read(f.receipt),log=fs.readFileSync(row.logPath);
  assert.ok(log.length<=1048576);assert.equal(row.evidence.omittedBytes,n+1);
  assert.equal(row.evidence.outputBytes,n+1+Buffer.byteLength(summary));assert.equal(row.evidence.truncated,true);
  assert.equal(row.counts.tests,2);assert.equal(row.counts.fail,1);
  assert.match(log.toString(),new RegExp(`\\[${n+1} bytes omitted\\]`));
});

test('repair 1: receipts and error text are redacted and capped before temporary writes',async t=>{
  const f=fixture(t),secret='receipt-only-synthetic-credential',writes=[];
  const error=`token=${secret}\n`+'e'.repeat(200000);
  const disk={...fs,writeFileSync(path,data,options){if(String(path).includes('ticket-'))writes.push(String(data));return fs.writeFileSync(path,data,options);}};
  const result=await runTestSuite({cwd:f.root,command:`password=${secret} `+'x'.repeat(200000),env:f.env},{...f.ports,fs:disk,
    source:()=>({head:'a'.repeat(40),fingerprint:'b'.repeat(64),runId:'r'.repeat(100000),issue:3117,error}),
    execute:async(_command,options)=>{options.onChild(987654);throw Error(error);},alive:pid=>pid===process.pid});
  assert.equal(result.exitCode,1);assert.equal(result.message.includes(secret),false);assert.ok(Buffer.byteLength(result.message)<=4096);
  assert.ok(writes.length>=4);
  for(const text of [...writes,fs.readFileSync(f.receipt,'utf8')]) {
    assert.ok(Buffer.byteLength(text)<=65536);assert.equal(text.includes(secret),false);
    const row=JSON.parse(text);assert.equal(row.source.head,'a'.repeat(40));assert.equal(row.source.fingerprint,'b'.repeat(64));
    assert.ok(Buffer.byteLength(row.source.error)<=4096);assert.ok(Buffer.byteLength(row.source.runId)<=4096);
  }
  assert.equal(read(f.receipt).state,'finished');assert.equal(read(f.receipt).exitCode,1);
});

test('repair 1: oversized required metadata fails closed before execution',async t=>{
  const f=fixture(t);let executions=0;
  const result=await runTestSuite({cwd:f.root,command:'true',env:f.env},{...f.ports,
    source:()=>({head:'x'.repeat(100000),fingerprint:null,runId:null,issue:null,error:null}),
    execute:async()=>{executions++;return {exitCode:0};}});
  assert.equal(executions,0);assert.equal(result.exitCode,1);
  assert.equal(fs.existsSync(f.receipt),false);
});


for(const channel of ['stdout','stderr']) for(const scheme of ['Bearer','Basic'])
test(`012 fix-ups: ${scheme} and known values reach ${channel} storage and forwarding safely`,async t=>{
  const f=fixture(t),program=join(f.root,'known.cjs'),dataPath=join(f.root,'known.input');
  const values=['opaque-synthetic-a','opaque-synthetic-b\nopaque-synthetic-c','opaque-synthetic-d','opaque-synthetic-e','opaque-synthetic-f'];
  for(const [index,name] of ['CUSTOM_TOKEN','SERVICE_SECRET','APP_PASSWORD','SERVICE_KEY','GH_TOKEN'].entries())f.env[name]=values[index];
  // Credentials learned through real PDD read boundaries are transferred to
  // the recorder in memory, even when they have no recognizable token prefix.
  const ghCredential='opaque-gh-read-value',agentCredential='opaque-agent-read-value';
  const health=await checkRuntimeHealth({env:{PDD_RUNTIME_URL:'https://runtime.example.test'}},
    {gh:()=>({status:0,stdout:ghCredential}),fetch:async()=>new Response('{}',{status:200})});
  assert.equal(health.state,'healthy');
  const doctor=doctorFixture({kind:'gemini'}),unusedCredential='opaque-unused-profile-value';
  doctor.ports.agentDefinitions=()=>[{id:'unused',kind:'claude',command:'missing-agent',env:{UNSELECTED_API_KEY:unusedCredential}},{id:'gemini',kind:'gemini',command:'gemini',env:{}}];
  doctor.paths.set(join(doctor.input.env.HOME,'.gemini','oauth_creds.json'),JSON.stringify({refresh_token:agentCredential}));
  assert.equal((await runAutopilotDoctor(doctor.input,doctor.ports)).exitCode,0);
  values.push(ghCredential,agentCredential,unusedCredential);
  const credential=scheme==='Basic'?'c3ludGhldGljOnJldmlldzAxMg==':'synthetic-review012-bearer-credential';
  const safe='safe-recovery\n';
  const data=values.map(value=>value+'\n').join('')+scheme+'\n'+credential+'\n'+safe+
    'x'.repeat(MAX_EVIDENCE_LINE_BYTES+1)+values[1]+'\n'+safe+
    (safe.repeat(Math.ceil(MAX_VALIDATION_LOG_BYTES/safe.length)))+values[0]+'\n'+safe;
  fs.writeFileSync(dataPath,data);
  const other=channel==='stdout'?'stderr':'stdout';
  fs.writeFileSync(program,`const fs=require('node:fs');const data=fs.readFileSync(${JSON.stringify(dataPath)});const send=(stream,bytes)=>new Promise(done=>process[stream].write(bytes,done));(async()=>{await send(${JSON.stringify(channel)},${JSON.stringify(scheme+'\n')});await send(${JSON.stringify(other)},${JSON.stringify('independent-stream\n')});await send(${JSON.stringify(channel)},${JSON.stringify(credential+'\n')});for(let offset=0;offset<data.length;offset+=4093)await send(${JSON.stringify(channel)},data.subarray(offset,offset+4093));})();`);
  let forwarded='';const capture={write(bytes){forwarded+=bytes;}};
  const result=await runTestSuite({cwd:f.root,command:`${quote(process.execPath)} ${quote(program)}`,env:f.env},{...f.ports,stdout:capture,stderr:capture});
  const row=read(f.receipt),log=fs.readFileSync(row.logPath,'utf8');
  assert.equal(result.exitCode,0,result.message+'\n'+forwarded.slice(0,2000));assert.equal(row.outcome,'completed');
  for(const text of [log,forwarded]) {
    for(const value of [...values,credential,'opaque-synthetic-b','opaque-synthetic-c'])assert.equal(text.includes(value),false,'credential must not reach evidence');
    assert.ok(text.includes(safe));assert.ok(text.includes('independent-stream'));
  }
  assert.ok(fs.statSync(row.logPath).size<=MAX_VALIDATION_LOG_BYTES);assert.equal(fs.statSync(row.logPath).mode&0o777,0o600);
  assert.ok(row.logPath.startsWith(join(f.env.HOME,'.local','state','pdd','validation')));
  assert.equal(row.evidence.outputBytes,Buffer.byteLength(data+scheme+'\n'+credential+'\n'+'independent-stream\n'));
  assert.equal(row.evidence.truncated,true);
});
