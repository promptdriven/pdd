import test from 'node:test';
import assert from 'node:assert/strict';
import { expandSource, catalogRecords } from '../src/contract-refs.mjs';

// Oracles follow shared-seed AC6 and shared-records/shared-source-limits Rules.
// The closed domains below use only the public boundary and injected file ports.
const LIMIT = 10_485_760;
function expand(text, files, format = 'scenario') {
  return expandSource({path:'bounded.json', text, format}, {
    stat:({path}) => ({exists:Object.hasOwn(files,path),is_symlink:false,size:Buffer.byteLength(files[path] ?? '')}),
    read:({path}) => ({content:files[path]}),
  });
}
const selector = '{"$seed":"contracts/world.json"}';
const consumer = ` { "initial_world" : ${selector}, "literal" : [2,1] }\n`;
function checkWorld(authored, canonical) {
  const got = expand(consumer, {'contracts/world.json':authored});
  assert.equal(got.text, consumer.replace(selector, authored));
  assert.equal(got.references.length, 1);
  assert.equal(got.references[0].value_json, canonical);
  assert.deepEqual(JSON.parse(got.references[0].value_json), JSON.parse(authored));
}

test('FORMAL arrays: every binary sequence length 0..16 retains all three nested occurrences', () => {
  let cases = 0;
  for (let length=0;length<=16;length++) for (let mask=0;mask<2**length;mask++) {
    const sequence = Array.from({length}, (_,i) => (mask >>> i) & 1);
    const forward = JSON.stringify(sequence), reverse = JSON.stringify([...sequence].reverse());
    // Authored z-before-a layout and canonical a-before-z are separate promises.
    checkWorld(`{ "z" : ${forward}, "a" : [${reverse},[${forward}]] }`,
      `{"a":[${reverse},[${forward}]],"z":${forward}}`);
    cases++;
  }
  assert.equal(cases, 131071);
});

test('FORMAL arrays: every ternary literal sequence length 0..4 in three nested shapes', () => {
  const alphabet = ['null','false','"x"'];
  let cases = 0;
  for (let length=0;length<=4;length++) for (let number=0;number<3**length;number++) {
    let digits=number;
    const values=Array.from({length},()=>{const value=alphabet[digits%3];digits=Math.floor(digits/3);return value;});
    const sequence=`[${values.join(',')}]`;
    for (const value of [sequence, `[${sequence},[]]`, `[{"z":${sequence},"a":[${sequence}]}]`]) {
      const sorted=value.replace('{"z":'+sequence+',"a":['+sequence+']}', '{"a":['+sequence+'],"z":'+sequence+'}');
      checkWorld(`{ "z": ${value}, "a": 0 }`, `{"a":0,"z":${sorted}}`);
      cases++;
    }
  }
  assert.equal(cases,363);
});

function permutations(values) {
  return values.length ? values.flatMap((value,i)=>permutations(values.filter((_,j)=>i!==j)).map(rest=>[value,...rest])) : [[]];
}
test('FORMAL arrays: all 24 object member orders canonicalize keys while preserving array and number tokens', () => {
  const members=['"z":[0,1,2,3,4,5,6,7,8,9,10,11]','"a":{"z":[[2,1],[0]],"a":false}',
    '"n":9007199254740993','"m":1e400'];
  const expected='{"a":{"a":false,"z":[[2,1],[0]]},"m":1e400,"n":9007199254740993,"z":[0,1,2,3,4,5,6,7,8,9,10,11]}';
  for (const order of permutations(members)) {
    const authored='{ '+order.join(', ')+' }';
    const got=expand(consumer,{'contracts/world.json':authored});
    assert.equal(got.text,consumer.replace(selector,authored));
    assert.equal(got.references[0].value_json,expected);
    const catalog=catalogRecords([{path:'contracts/world.json',text:authored}]);
    assert.deepEqual(catalog.warnings,[]);
    assert.equal(catalog.records[0].value_json,expected);
  }
});

test('FORMAL source limits: four stat sizes decide refusal before reading, including above Buffer range', () => {
  for (const size of [LIMIT-1,LIMIT,LIMIT+1,2_147_483_649]) {
    let reads=0;
    const invoke=()=>expandSource({path:'bounded.json',text:'{"$contract":"contracts/value.json#"}',format:'json-schema'}, {
      stat:()=>({exists:true,is_symlink:false,size}),
      read:()=>{reads++;return {content:'{"type":"string"}'};},
    });
    if (size>LIMIT) {
      assert.throws(invoke,error=>error.code==='contract-invalid' && /too big/.test(error.message)
        && error.message.includes('bounded.json') && error.message.includes('contracts/value.json#') && error.message.length<4000);
      assert.equal(reads,0);
    } else {
      assert.equal(invoke().text,'{"type":"string"}');
      assert.equal(reads,1);
    }
  }
});

test('FORMAL source limits: all 36 bounded fanout graphs compare exact expanded byte counts with 10 MiB', () => {
  let cases=0,refusals=0;
  for (const width of [2,3]) for (let depth=0;depth<=5;depth++) for (const padding of [0,31,65535]) {
    const files={'contracts/0.json':JSON.stringify({type:'string',default:'x'.repeat(padding)})};
    let bytes=Buffer.byteLength(files['contracts/0.json']);
    for(let level=1;level<=depth;level++) {
      const fields=Array.from({length:width},(_,i)=>`"f${i}":{"$contract":"contracts/${level-1}.json#"}`);
      files[`contracts/${level}.json`]='{"type":"object","properties":{'+fields.join(',')+'}}';
      bytes=Buffer.byteLength('{"type":"object","properties":{}}') + width*bytes
        + Array.from({length:width},(_,i)=>Buffer.byteLength(`"f${i}":`)).reduce((a,b)=>a+b,0) + width-1;
    }
    const input=`{"$contract":"contracts/${depth}.json#"}`;
    if(bytes>LIMIT) {
      assert.throws(()=>expand(input,files,'json-schema'),error=>error.code==='contract-invalid' && /too big/.test(error.message) && error.message.length<4000);
      refusals++;
    } else {
      const got=expand(input,files,'json-schema');
      assert.equal(Buffer.byteLength(got.text),bytes);
      assert.equal(got.references.length,depth+1);
    }
    cases++;
  }
  assert.equal(cases,36);
  assert.equal(refusals,1);
});
