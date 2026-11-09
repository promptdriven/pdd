import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {redactingLines,validationLog,serializeValidationReceipt,MAX_VALIDATION_LOG_BYTES,MAX_EVIDENCE_LINE_BYTES} from '../src/validation-evidence.mjs';

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
