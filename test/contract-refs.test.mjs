import test from 'node:test';
import assert from 'node:assert/strict';
import { expandSource, catalogRecords, compareCopies, planSync } from '../src/contract-refs.mjs';

const filePort = sources => ({
  stat: ({path}) => ({ exists: Object.hasOwn(sources,path), is_symlink:false, size:Buffer.byteLength(sources[path] ?? '') }),
  read: ({path}) => ({content:sources[path]}),
});
const schema = properties => ({type:'object',properties,required:Object.keys(properties),additionalProperties:false});
const prompt = value => `# Preserved\r\n\r\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${typeof value === 'string' ? value : JSON.stringify(value)}\n\`\`\`\n</details>\n\nTrailing exact bytes.\n`;
const source = input => ({path:'prompts/consumer.prompt.md',text:prompt({status:'approved',prose_sha256:'original-hash',entries:[{operation:'main',input_schema:input,result_schema:{type:'string'}}],resources:[]})});
const record = (target,value) => ({path:target.split('#')[0],target,value_json:typeof value === 'string' ? value : JSON.stringify(value)});
const expand = (text,files={},format='json-schema') => expandSource({path:'prompts/consumer.prompt.md',text,format},filePort(files));

test('REF lossless JSON retains authored numeric-looking keys and preserves tokens and prototypes', () => {
  const files = {'contracts/x.json':'{"type":"object","properties":{"10":{"type":"number","default":1e400},"2":{"type":"number","default":-0},"__proto__":{"type":"number","default":9007199254740993},"constructor":{"type":"number","default":1.0}},"required":[],"additionalProperties":false}'};
  const result = expand('{"$contract":"contracts/x.json#"}',files);
  assert.equal(result.text,files['contracts/x.json']);
  assert.equal(Object.prototype.default,undefined);
  assert.equal(Object.getPrototypeOf(JSON.parse(result.text)),Object.prototype);
});

test('REF roots and nested resource schemas expand; prose, literal annotations and real $ref stay literal', () => {
  const src = prompt({status:'draft',entries:[],resources:[{operations:[{arguments_schema:{type:'array',items:{$contract:'contracts/x.json#'}},result_schema:{oneOf:[{$contract:'contracts/x.json#'},{type:'string',default:{$contract:'missing'}}]}}]}]});
  const result = expand(src,{'contracts/x.json':'{"type":"boolean"}'},'prompt');
  assert.match(result.text,/"items":\{"type":"boolean"\}/);
  assert.match(result.text,/"default":\{"\$contract":"missing"\}/);
  assert.equal(result.references.length,2);
  for (const literal of [' {"$ref":"contracts/nope.json#/x"}\n', ' {"type":"string","examples":[{"$contract":"missing"}]}\n', 'malformed no reference {']) assert.equal(expand(literal).text,literal);
  assert.ok(result.text.startsWith('# Preserved\r\n\r\n'));
  assert.ok(result.text.endsWith('Trailing exact bytes.\n'));
});

test('REF pointer/target errors are finite, preserve originating consumer and never read unsafe paths', () => {
  assert.throws(()=>expandSource({path:'consumer.prompt.md',text:'{"$contract":"contracts/unsafe.json#"}',format:'json-schema'}, {
    stat(){throw Object.assign(new Error('native refusal'),{code:4});},read(){assert.fail('must not read');},
  }),error=>error.code==='contract-unsafe' && error.message.includes('consumer.prompt.md') && error.message.includes('contracts/unsafe.json#'));
  for (const path of ['../x.json#','/x.json#','~x.json#','https:x.json#','a//x.json#','a/./x.json#','a\\x.json#','a\u0000x.json#']) {
    let reads=0;
    assert.throws(()=>expandSource({path:'consumer',text:JSON.stringify({$contract:path}),format:'json-schema'},{stat(){reads++;},read(){reads++;}}),e=>e.code==='contract-unsafe'&&e.message.includes('consumer')&&e.message.length<=4000);
    assert.equal(reads,0);
  }
  const files={'contracts/x.json':'{"a":[{"type":"string"}]}'};
  for (const [selection,code] of [['/a/00','contract-missing'],['/a/-','contract-missing'],['/a/1','contract-missing'],['/a/~2','contract-invalid'],['not-pointer','contract-invalid'],['/constructor','contract-missing']]) assert.throws(()=>expand(JSON.stringify({$contract:`contracts/x.json#${selection}`}),files),e=>e.code===code);
});

test('REF Markdown fenced headings and descriptive sections do not corrupt record selection', () => {
  const text='### About\ntext\n### Request In\n~~~json\n{"type":"string","default":"### Example"}\n~~~\n### Broken\n```json\n{\n```\n### Many\n```json\n{}\n```\n```json\n{}\n```';
  const files={'contracts/x.md':text};
  assert.equal(expand('{"$contract":"contracts/x.md#request-in"}',files).references[0].target,'contracts/x.md#Request In');
  assert.throws(()=>expand('{"$contract":"contracts/x.md#About"}',files),e=>e.code==='contract-missing');
  for (const heading of ['Broken','Many']) assert.throws(()=>expand(JSON.stringify({$contract:`contracts/x.md#${heading}`}),files),e=>e.code==='contract-invalid');
  const catalog=catalogRecords([{path:'contracts/x.md',text}]);
  assert.deepEqual(catalog.records.map(x=>x.target),['contracts/x.md#Request In']);
  assert.equal(catalog.warnings.length,2);
});

test('REF independent reuse is allowed while transitive seeds keep path# identities and cycles refuse', () => {
  const files={'contracts/a.json':'{"$seed":"contracts/b.json","set":{"/a":1}}','contracts/b.json':'{"base":true}'};
  const result=expand('{"initial_world":{"$seed":"contracts/a.json","set":{"/b":false}}}',files,'scenario');
  assert.equal(result.text,'{"initial_world":{"base":true,"a":1,"b":false}}');
  assert.deepEqual(result.references.map(x=>x.target),['contracts/a.json#','contracts/b.json#']);
  files['contracts/b.json']='{"$seed":"contracts/a.json"}';
  assert.throws(()=>expand('{"initial_world":{"$seed":"contracts/a.json"}}',files,'scenario'),e=>e.code==='contract-cycle'&&e.message.includes('contracts/a.json# -> contracts/b.json# -> contracts/a.json#'));
  for (const value of [{$seed:'contracts/a.json#'},{$seed:'contracts/a.json',other:1}]) assert.throws(()=>expand(JSON.stringify({initial_world:value}),files,'scenario'),e=>e.code==='seed-invalid');
});

test('REF catalog includes used JSON leaf pointers, root worlds and nested schema records', () => {
  const text=JSON.stringify({world:{count:0},definitions:{item:schema({name:{type:'string'}})},leaf:{type:'boolean'}});
  const result=catalogRecords([{path:'contracts/x.json',text}],['contracts/x.json#/leaf']);
  assert.deepEqual(result.records.map(x=>x.target),['contracts/x.json#','contracts/x.json#/definitions/item','contracts/x.json#/leaf']);
  assert.deepEqual(result.warnings,[]);
});

test('REF compare preserves nested annotations/constraints, field distance and exact numeric values', () => {
  const canonical=schema({count:{type:'number',minimum:1,description:'nested canonical'},name:{type:'string'},kind:{type:'string'},active:{type:'boolean'}});
  const records=[record('contracts/x.json#',canonical)];
  const local={...canonical,title:'local',description:'local'};
  assert.deepEqual(compareCopies([source(local)],records).matches[0].differences,[]);
  const nested=structuredClone(local); nested.properties.count.minimum=0; nested.properties.count.description='different nested';
  const matched=compareCopies([source(nested)],records).matches[0];
  assert.equal(matched.kind,'near');
  assert.ok(matched.differences.some(x=>x.includes('/properties/count/minimum')));
  assert.ok(matched.differences.some(x=>x.includes('/properties/count/description')));
  const far=schema({other:{type:'string'},name:{type:'string'},kind:{type:'string'},active:{type:'boolean'}});
  assert.deepEqual(compareCopies([source(far)],records).matches,[]);
  for (const number of ['1','1.0','1e0','1.000e+0']) {
    const input=`{"type":"object","properties":{"count":{"type":"number","minimum":${number}},"name":{"type":"string"},"kind":{"type":"string"},"active":{"type":"boolean"}},"required":["count"],"additionalProperties":false}`;
    const src={path:'p.prompt.md',text:prompt(`{"entries":[{"input_schema":${input}}]}`)};
    assert.equal(compareCopies([src],[record('contracts/n.json#',input.replace(number,'1'))]).matches[0].kind,'exact');
  }
  for (const number of ['0','-0','0.0','0e0']) {
    const input=`{"type":"object","properties":{"n":{"type":"number","minimum":${number}},"name":{"type":"string"},"kind":{"type":"string"},"active":{"type":"boolean"}},"required":[],"additionalProperties":false}`;
    assert.equal(compareCopies([{path:'p',text:prompt(`{"entries":[{"input_schema":${input}}]}`)}],[record('contracts/n.json#',input.replace(number,'0'))]).matches[0].kind,'exact');
  }
  const input='{"type":"object","properties":{"n":{"type":"number","minimum":9007199254740993},"name":{"type":"string"},"kind":{"type":"string"},"active":{"type":"boolean"}},"required":[],"additionalProperties":false}';
  const mismatch=compareCopies([{path:'p',text:prompt(`{"entries":[{"input_schema":${input}}]}`)}],[record('contracts/n.json#',input.replace('9007199254740993','9007199254740992'))]).matches[0];
  assert.equal(mismatch.kind,'near');
  assert.match(mismatch.differences[0],/9007199254740993 -> 9007199254740992/);
});

test('REF equivalent exact candidates remain ambiguous; unique exact wins over near', () => {
  const value=schema({n:{type:'number',minimum:1},name:{type:'string'},kind:{type:'string'},active:{type:'boolean'}}), src=source(value);
  const first=record('contracts/a.json#',JSON.stringify(value).replace('"minimum":1','"minimum":1.0'));
  const second=record('contracts/b.json#',value);
  const ambiguous=compareCopies([src],[first,second]);
  assert.deepEqual(ambiguous.matches,[]); assert.match(ambiguous.warnings[0],/ambiguous/);
  second.value_json=second.value_json.replace('"minimum":1','"minimum":2');
  assert.equal(compareCopies([src],[first,second]).matches[0].target,first.target);
});

test('REF sync previews preserve prose/hash, adopt constraints, retain local annotations and become idempotent', () => {
  const canonical=schema({name:{type:'string'},kind:{type:'string'},active:{type:'boolean'},run_id:{type:'string'}}), inline=schema({name:{type:'string'},kind:{type:'string'},active:{type:'boolean'}});
  inline.title='CLI request'; inline.description='local';
  const src=source(inline), records=[record('contracts/x.json#',canonical)], matches=compareCopies([src],records).matches;
  const result=planSync([src],matches);
  assert.equal(result.edits.length,1);
  const edit=result.edits[0];
  assert.equal(edit.before,src.text);
  assert.ok(edit.after.startsWith('# Preserved\r\n\r\n'));
  assert.ok(edit.after.endsWith('Trailing exact bytes.\n'));
  assert.match(edit.after,/"status":"draft"/);
  assert.match(edit.after,/"prose_sha256":"original-hash"/);
  assert.match(edit.after,/"input_schema":\{"\$contract":"contracts\/x.json#","title":"CLI request","description":"local"\}/);
  assert.deepEqual(planSync([{path:src.path,text:edit.after}],compareCopies([{path:src.path,text:edit.after}],records).matches).edits,[]);
  const expanded=expandSource({path:src.path,text:edit.after,format:'prompt'},filePort({'contracts/x.json':JSON.stringify(canonical)}));
  assert.match(expanded.text,/"required":\["name","kind","active","run_id"\]/);
  const unmatched={path:'unmatched.prompt.md',text:'# no interface\n'};
  assert.equal(planSync([unmatched],matches).edits.length,0);
});
