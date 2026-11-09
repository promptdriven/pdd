import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {redactingLines,validationLog,serializeValidationReceipt,MAX_VALIDATION_LOG_BYTES,MAX_EVIDENCE_LINE_BYTES} from '../src/validation-evidence.mjs';

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
