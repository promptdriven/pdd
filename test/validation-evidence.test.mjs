import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { fork } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, statSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import {redactingLines,validationLog,serializeValidationReceipt,safeEvidenceText,MAX_VALIDATION_LOG_BYTES,MAX_EVIDENCE_LINE_BYTES} from '../src/validation-evidence.mjs';
import {redactSecrets,rememberSecrets,redactingValues} from '../src/secret-redaction.mjs';

test('012 fix-ups 2: scalar and stream exact matches use original input and longest match first',()=>{
  const cases=[
    {values:['opaque-prefix','opaque-prefixPRIVATE-TAIL'],input:'opaque-prefixPRIVATE-TAIL',expected:'[redacted]'},
    {values:['inside','opaque-inside-private'],input:'opaque-inside-private',expected:'[redacted]'},
    {values:['opaque-abc','abc-tail'],input:'opaque-abc-tail',expected:'[redacted]-tail'},
  ];
  for(const {values,input,expected} of cases) for(const secrets of [values,[...values].reverse()]) {
    const text='safe-before '+input+' safe-after',want='safe-before '+expected+' safe-after';
    assert.equal(redactSecrets(text,secrets),want);
    for(let split=0;split<=text.length;split++) {
      let saved='';const stream=redactingValues(value=>saved+=value,secrets);
      stream.write(text.slice(0,split));stream.write(text.slice(split));stream.end();
      assert.equal(saved,want);
    }
  }
  // Receipt and bounded error consumers use the same scalar rule before clipping.
  const short='opaque-receipt-prefix',long=short+'PRIVATE-TAIL';
  rememberSecrets(short,long);
  for(const saved of [safeEvidenceText(long),serializeValidationReceipt({reason:long,source:{error:long}})])
    assert.equal(saved.includes('PRIVATE-TAIL'),false);
});

for(const kind of ['quoted secret','private key'])
test(`repair 2: bounded scanning retains ${kind} across overflow and awkward windows`,()=>{
  const secret='synthetic-overflow-secret-body';
  const opener=kind==='quoted secret'?'password="':'-----BEGIN PRIVATE KEY-----';
  const end=kind==='quoted secret'?'"':'-----END PRIVATE KEY-----';
  const n=MAX_EVIDENCE_LINE_BYTES;
  const openings=[opener+'x'.repeat(n), 'x'.repeat(n)+' '+opener,
    'x'.repeat(4091)+' '+opener+'x'.repeat(n),
    kind==='quoted secret'?'password'+ ' '.repeat(n)+'= "':
      '-----BEGIN '+ ' '.repeat(n)+'PRIVATE KEY-----'];
  for(const opening of openings) for(const width of [1,4093,65536]) for(const eof of [false,true]) {
    const continuation=kind==='quoted secret'?'\\"'+secret:secret;
    const input=Buffer.from(opening+'\n'+continuation+'\n'+end+(eof?'':'\nsafe-after-secret\n'));
    let saved='',omitted=0;
    const stream=redactingLines((text,count)=>{
      assert.equal(text.includes(secret),false);saved+=text;omitted+=count;
    });
    for(let offset=0;offset<input.length;offset+=width)stream.write(input.subarray(offset,offset+width));
    stream.end();
    assert.equal(saved.includes(secret),false);assert.ok(saved.includes('[redacted]'));
    assert.equal(omitted,Buffer.byteLength(opening+'\n'));
    if(!eof)assert.ok(saved.endsWith('safe-after-secret\n'));
  }
  // End and reopen on an omitted line, including an oversized continuation.
  for(const prefix of [opener,opener+'\n']) {
    const input=prefix+'x'.repeat(n)+end+' '+opener+'\n'+secret+'\n'+end+'\nsafe-after-secret\n';
    let saved='';const stream=redactingLines(text=>{saved+=text;});
    stream.write(Buffer.from(input));stream.end();
    assert.equal(saved.includes(secret),false);assert.ok(saved.endsWith('safe-after-secret\n'));
  }
  // Closing inside an omitted line must allow safe output to resume.
  let saved='';const stream=redactingLines(text=>{saved+=text;});
  stream.write(Buffer.from(opener+'x'.repeat(n)+end+'\nsafe-after-secret\n'));stream.end();
  assert.ok(saved.endsWith('safe-after-secret\n'));
});

test('stream redaction covers every two-chunk split of supported synthetic credentials',()=>{
  const cases=[
    ['Authorization: Bearer arbitrary-test-value\n','arbitrary-test-value'],
    ['Authorization: Custom arbitrary-test-value\n','arbitrary-test-value'],
    ['Bearer arbitrary-test-value\n','arbitrary-test-value'],
    ['Basic arbitrary-test-value\n','arbitrary-test-value'],
    ['api_key="arbitrary-test-value"\n','arbitrary-test-value'],
    ['cookie="arbitrary-test-value"\n','arbitrary-test-value'],
    ['password="multi-line\narbitrary-test-value"\n','arbitrary-test-value'],
    ['password="prefix\\"arbitrary-test-value"\n','arbitrary-test-value'],
    ['password="multi-line\n\\"arbitrary-test-value"\n','arbitrary-test-value'],
    ['key="arbitrary-test-value"\n','arbitrary-test-value'],
    ["password='arbitrary-test-value'\n",'arbitrary-test-value'],
    ['token=arbitrary-test-value\n','arbitrary-test-value'],
    ['https://person:arbitrary-test-value@example.invalid/?key=query-value\n','arbitrary-test-value'],
    ['ghp_abc123456789\n','ghp_abc123456789'],
    ['github_pat_abc123456789\n','github_pat_abc123456789'],
    ['sk-proj-abc123456789123456789\n','sk-proj-abc123456789123456789'],
    ['AIzaabc123456789\n','AIzaabc123456789'],
    ['ya29.abc123456789\n','ya29.abc123456789'],
    ['-----BEGIN PRIVATE KEY-----\nprivate-key-body\n-----END PRIVATE KEY-----\n','private-key-body'],
  ];
  let checked=0;
  for(const [text,secret] of cases) for(const suffix of ['', 'without-final-newline']) {
    const input=Buffer.from(suffix?text.trimEnd():text);
    for(let split=0;split<=input.length;split++) {
      let saved='';const stream=redactingLines(value=>{assert.equal(value.includes(secret),false);saved+=value;});
      stream.write(input.subarray(0,split));stream.write(input.subarray(split));stream.end();
      assert.equal(saved.includes(secret),false);assert.ok(saved.includes('[redacted]'));checked++;
    }
  }
  assert.ok(checked>1000);
});

test('log budget includes the marker at each overflow boundary and counts exact omitted bytes',()=>{
  for(const n of [MAX_VALIDATION_LOG_BYTES-1,MAX_VALIDATION_LOG_BYTES,MAX_VALIDATION_LOG_BYTES+1,2*MAX_VALIDATION_LOG_BYTES]) {
    let saved=Buffer.alloc(0),max=0;
    const store=bytes=>{saved=Buffer.from(bytes);max=Math.max(max,saved.length);};
    const log=validationLog(store,bytes=>store(Buffer.concat([saved,bytes])));
    const input=Buffer.alloc(n,120);
    for(let offset=0;offset<n;offset+=65536)log.add(input.subarray(offset,offset+65536).toString());
    assert.ok(max<=MAX_VALIDATION_LOG_BYTES);assert.equal(log.evidence.logBytes,saved.length);
    assert.equal(log.evidence.truncated,n>MAX_VALIDATION_LOG_BYTES);
    assert.equal(log.evidence.omittedBytes,n>MAX_VALIDATION_LOG_BYTES?n-(MAX_VALIDATION_LOG_BYTES-128):0);
    if(n<=MAX_VALIDATION_LOG_BYTES)assert.deepEqual(saved,input);
  }
});

test('P0-8: post-overflow chunk stream batches checkpoints instead of rewriting 1 MiB per chunk and flush() commits exact final tail',()=>{
  let saved=Buffer.alloc(0), writes=0, appends=0;
  const log=validationLog(
    bytes=>{writes++;saved=Buffer.from(bytes);},
    bytes=>{appends++;saved=Buffer.concat([saved,bytes]);},
  );
  const totalChunks=1280; // 1280 * 4 KiB = 5 MiB (>1000 post-overflow chunks)
  for(let i=0;i<totalChunks;i++) {
    const tag=`CHUNK-${String(i).padStart(4,'0')}-`;
    log.add(tag+'a'.repeat(4096-tag.length));
  }
  log.flush();
  assert.ok(appends<=256,'pre-overflow chunks use append');
  assert.ok(writes<=12,`post-overflow full writes stay bounded (got ${writes} for ${totalChunks} chunks)`);
  assert.ok(saved.length<=MAX_VALIDATION_LOG_BYTES);
  assert.equal(log.evidence.logBytes,saved.length);
  assert.equal(log.evidence.truncated,true);
  const text=saved.toString('utf8');
  assert.ok(text.startsWith('CHUNK-0000-'),'retains exact head');
  assert.match(text,/bytes omitted\]/,'includes omission marker');
  assert.ok(text.includes('CHUNK-1279-'),'flush commits exact final tail chunk');
});

test('P0-8 review fix: test-suite-recorder flushes buffered post-overflow tail on nonzero exit, SIGTERM, and thrown error paths', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-recorder-flush-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const recorderPath = fileURLToPath(new URL('../src/test-suite-recorder.mjs', import.meta.url));

  const runRecorder = ({ command, record, cancelOnSentinel = null, execArgv = [] }) => new Promise((resolve, reject) => {
    const child = fork(recorderPath, [], { execArgv, stdio: ['ignore', 'ignore', 'pipe', 'ipc'] });
    t.after(() => { try { child.kill('SIGKILL'); } catch {} });
    let resultMsg = null;
    let stderr = '';
    let seenStream = '';
    let canceled = false;
    child.stderr?.on('data', d => { stderr += d; });
    child.on('message', msg => {
      if (msg.stream && cancelOnSentinel && !canceled) {
        seenStream = (seenStream + Buffer.from(msg.bytes, 'base64').toString('utf8')).slice(-4096);
        if (seenStream.includes(cancelOnSentinel)) {
          canceled = true;
          child.send({ cancel: 'SIGTERM' });
        }
      }
      if (msg.result) resultMsg = msg.result;
    });
    child.once('error', reject);
    child.once('exit', code => resolve({ code, result: resultMsg, stderr }));
    child.send({ start: { command, cwd: dir, env: { PATH: process.env.PATH, HOME: dir }, timeoutMs: 15000, record } });
  });

  // 1. Nonzero failure emitting >1.1 MiB with final sentinel buffered past last checkpoint.
  const logFail = join(dir, 'fail.log'), receiptFail = join(dir, 'fail.json');
  const failCmd = `${JSON.stringify(process.execPath)} -e "for (let i = 0; i < 300; i++) process.stdout.write('F' + String(i).padStart(4, '0') + '-' + 'x'.repeat(4090) + '\\n'); process.stdout.write('TAIL-FLUSH-FAIL-SENTINEL\\n'); process.exitCode = 1;"`;
  const failRun = await runRecorder({ command: failCmd, record: { ticket: 1, pid: process.pid, cwd: dir, state: 'running', queuedAt: 1, startedAt: 2, finishedAt: null, receiptPath: receiptFail, logPath: logFail } });
  assert.equal(failRun.result?.record?.exitCode, 1, failRun.stderr);
  const failLogText = readFileSync(logFail, 'utf8');
  assert.ok(failLogText.includes('TAIL-FLUSH-FAIL-SENTINEL'), 'nonzero exit flushes buffered post-overflow tail');
  assert.equal(failRun.result.record.evidence.logBytes, statSync(logFail).size);

  // 2. SIGTERM cancellation after >1.1 MiB + sentinel output flushes buffered tail.
  const logSig = join(dir, 'sig.log'), receiptSig = join(dir, 'sig.json');
  const sigCmd = `${JSON.stringify(process.execPath)} -e "for (let i = 0; i < 300; i++) process.stdout.write('S' + String(i).padStart(4, '0') + '-' + 'y'.repeat(4090) + '\\n'); process.stdout.write('TAIL-FLUSH-SIGTERM-SENTINEL\\n' + 'r'.repeat(512) + '\\n'); setInterval(() => {}, 1000);"`;
  const sigRun = await runRecorder({ command: sigCmd, cancelOnSentinel: 'TAIL-FLUSH-SIGTERM-SENTINEL', record: { ticket: 2, pid: process.pid, cwd: dir, state: 'running', queuedAt: 1, startedAt: 2, finishedAt: null, receiptPath: receiptSig, logPath: logSig } });
  assert.equal(sigRun.result?.record?.signal, 'SIGTERM', sigRun.stderr);
  assert.equal(sigRun.result?.record?.exitCode, 143, 'explicit SIGTERM cancel exits 143 (not timeout 124)');
  const sigLogText = readFileSync(logSig, 'utf8');
  assert.ok(sigLogText.includes('TAIL-FLUSH-SIGTERM-SENTINEL'), 'SIGTERM cancellation flushes buffered post-overflow tail');
  assert.equal(sigRun.result.record.evidence.logBytes, statSync(logSig).size);

  // 3. Thrown exception inside executeSuite still flushes buffered post-overflow tail via finally!
  const logErr = join(dir, 'err.log'), receiptErr = join(dir, 'err.json');
  const hookCode = `
    import { registerHooks } from 'node:module';
    registerHooks({
      load(url, context, nextLoad) {
        if (url.endsWith('/src/autopilot/suite-executor.mjs')) {
          return {
            format: 'module',
            shortCircuit: true,
            source: 'export async function executeSuite(_cmd, opts) { for (let i = 0; i < 300; i++) opts.onOutput("stdout", Buffer.from("E" + String(i).padStart(4, "0") + "-" + "z".repeat(4090) + "\\\\n")); opts.onOutput("stdout", Buffer.from("TAIL-FLUSH-THROW-SENTINEL\\\\n")); throw new Error("simulated-recorder-crash"); }',
          };
        }
        return nextLoad(url, context);
      },
    });
  `;
  const errRun = await runRecorder({
    command: 'ignored',
    execArgv: ['--import', `data:text/javascript,${encodeURIComponent(hookCode)}`],
    record: { ticket: 3, pid: process.pid, cwd: dir, state: 'running', queuedAt: 1, startedAt: 2, finishedAt: null, receiptPath: receiptErr, logPath: logErr },
  });
  assert.equal(errRun.result?.record?.outcome, 'unknown', errRun.stderr);
  const errLogText = readFileSync(logErr, 'utf8');
  assert.ok(errLogText.includes('TAIL-FLUSH-THROW-SENTINEL'), 'finally block flushes buffered post-overflow tail even when executeSuite throws');
  assert.equal(errRun.result.record.evidence.logBytes, statSync(logErr).size);
});

test('line budget suppresses the whole oversized value including an EOF continuation',()=>{
  for(const n of [MAX_EVIDENCE_LINE_BYTES-1,MAX_EVIDENCE_LINE_BYTES,MAX_EVIDENCE_LINE_BYTES+1]) {
    let saved='',omitted=0;
    const stream=redactingLines((text,count)=>{saved+=text;omitted+=count;});
    for(let i=0;i<n;i+=1024)stream.write(Buffer.alloc(Math.min(1024,n-i),120));stream.end();
    if(n<=MAX_EVIDENCE_LINE_BYTES)assert.equal(saved,'x'.repeat(n));
    else {assert.equal(saved.includes('x'),false);assert.equal(omitted,n);}
  }
});

test('receipt redaction precedes byte clipping even for a long synthetic quoted secret',()=>{
  const secret='a'.repeat(100000),raw={reason:`password="${secret}"`,source:{error:'key='+secret}};
  const saved=serializeValidationReceipt(raw);
  assert.equal(saved.includes('a'.repeat(100)),false);assert.ok(Buffer.byteLength(saved)<=65536);
});


test('known values are hidden at every two-chunk and line split before overflow',()=>{
  const value='synthetic-known-prefix-€\nsynthetic-known-suffix-🔑';
  const huge='h'.repeat(MAX_EVIDENCE_LINE_BYTES)+'synthetic-known-ending';
  for(const secret of [value,huge]) {
    const input=Buffer.from('safe-before\n'+secret+'\nsafe-after\n');
    const splits=secret===value?Array.from({length:input.length+1},(_,i)=>i):[1,4093,MAX_EVIDENCE_LINE_BYTES-1,MAX_EVIDENCE_LINE_BYTES+1,input.length-1];
    for(const split of splits) {
      let saved='';const stream=redactingLines(text=>saved+=text,[secret]);
      stream.write(input.subarray(0,split));stream.write(input.subarray(split));stream.end();
      assert.doesNotMatch(saved,/synthetic-known/);assert.ok(saved.includes('safe-before'));assert.ok(saved.endsWith('safe-after\n'));
    }
  }
});

for(const scheme of ['Bearer','Basic']) test(`multiline ${scheme} recognition survives chunks and omitted whitespace`,()=>{
  const credential='synthetic-scheme-credential';
  for(const gap of ['\n','\r\n\t',' '.repeat(MAX_EVIDENCE_LINE_BYTES)+'\n']) {
    const input=Buffer.from(scheme+gap+credential+'\nsafe-after\n');
    for(const width of [1,4093,65536]) {
      let saved='';const stream=redactingLines(text=>saved+=text);
      for(let offset=0;offset<input.length;offset+=width)stream.write(input.subarray(offset,offset+width));
      stream.end();assert.equal(saved.includes(credential),false);assert.ok(saved.endsWith('safe-after\n'));
    }
  }
});
