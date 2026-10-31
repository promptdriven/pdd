import test from 'node:test';
import assert from 'node:assert/strict';
import * as refs from '../src/contract-refs.mjs';
import * as preflight from '../src/runtime-preflight.mjs';

// These native expectations come from the approved public helper declarations;
// they neither replace nor modify the separately approved command vectors.
test('lossless native codec preserves tokens, own keys and container layout', () => {
  const text = '{ "z":9007199254740993, "__proto__":{"n":0.10}, "2":1e0, "a":[-0,false,null] }';
  const value = refs.parseJsonValue(text);
  assert.equal(refs.stringifyJsonValue(value), text);
  assert.equal(refs.jsonNumberText(value.z), '9007199254740993');
  assert.equal(refs.jsonNumberText(value.__proto__.n), '0.10');
  assert.equal(refs.jsonNumberText(value['2']), '1e0');
  assert.equal(refs.jsonNumberText(value.a[0]), '-0');
  assert.equal(refs.jsonNumberText(value.a[1]), null);
  assert.equal(refs.jsonNumberText(value.a), null);
  assert.ok(Object.hasOwn(value, '__proto__'));
  assert.equal(refs.stringifyJsonValue(value.a), '[-0,false,null]');
});

test('native JSON equality is exact literal equality at all numeric sizes', () => {
  const same = (a,b) => refs.jsonValuesEqual(refs.parseJsonValue(a), refs.parseJsonValue(b));
  assert.equal(same('1', '1e0'), true);
  assert.equal(same('-0', '0.00'), true);
  assert.equal(same('9007199254740993', '9007199254740992'), false);
  assert.equal(same('{"a":1,"b":2}', '{"b":2,"a":1.0}'), true);
  assert.equal(same('{"description":"a"}', '{"description":"b"}'), false);
  assert.equal(same('{"enum":[1,2]}', '{"enum":[2,1]}'), false);
  assert.equal(same('[1,2]', '[2,1]'), false);
});

test('native parsing rejects malformed JSON and non-string input by public error kind', () => {
  for (const text of ['{', '[1,]', 'NaN', 'undefined']) assert.throws(() => refs.parseJsonValue(text), SyntaxError);
  for (const value of [null, undefined, 1, {}, []]) assert.throws(() => refs.parseJsonValue(value), TypeError);
});

test('canonical schema keyword vocabulary is fresh and excludes annotations', () => {
  const names = preflight.schemaKeywordNames();
  assert.ok(Array.isArray(names)); assert.ok(names.every(name => typeof name === 'string'));
  for (const name of ['type', 'oneOf', 'properties', 'enum', 'minimum', 'items', '$ref', 'anyOf']) assert.ok(names.includes(name), name);
  for (const name of ['title', 'description', 'default', 'examples', 'format']) assert.equal(names.includes(name), false, name);
  const original = [...names]; names.length = 0;
  assert.deepEqual(preflight.schemaKeywordNames(), original);
});

const valid = result => assert.deepEqual(result, {schema_problems: [], value_problems: [], unproved: []});
const validate = (schema_json, value_json) => preflight.validateContract(value_json === undefined ? {schema_json} : {schema_json, value_json});
test('native contract validator supports component roots and omitted versus null values', () => {
  valid(validate('{"type":"array","items":{"type":"boolean"}}', '[false,true]'));
  valid(validate('{"type":"number","minimum":0.1,"maximum":0.3}', '0.2'));
  valid(validate('{"type":"number","enum":[0.1]}', '1e-1'));
  valid(validate('{"type":"string"}'));
  const result = validate('{"type":"string"}', 'null');
  assert.equal(result.value_problems[0].code, 'invalid-input');
  assert.equal(result.value_problems[0].pointer, '');
});

test('native validation preserves uncertainty without losing independent problems', () => {
  const uncertain = validate('{"type":"number","const":9007199254740993}', '9007199254740992');
  assert.deepEqual(uncertain.schema_problems, []); assert.deepEqual(uncertain.value_problems, []);
  assert.ok(uncertain.unproved.some(item => item.code === 'contract-validation-unavailable' && item.pointer === ''));
  const schema = '{"type":"object","properties":{"n":{"type":"integer","minimum":1},"s":{"type":"string","pattern":"(?<=a)b"}},"required":["n","s"],"additionalProperties":false}';
  const mixed = validate(schema, '{"n":0,"s":"b"}');
  assert.ok(mixed.value_problems.some(item => item.pointer === '/n'));
  assert.ok(mixed.unproved.some(item => item.pointer === '/s'));
  for (const result of [uncertain, mixed]) for (const items of Object.values(result)) for (const item of items) {
    assert.deepEqual(Object.keys(item).sort(), ['code','pointer','rule']);
    assert.ok(typeof item.rule === 'string' && item.rule.length > 0);
  }
});

test('native validation rejects bad arguments with finite named TypeErrors', () => {
  for (const args of [{schema_json: null}, {schema_json: '{'}, {schema_json: '{"type":"null"}', value_json: null}, {schema_json: '{"type":"null"}', value_json: '{'}]) {
    const name = args.schema_json === null || args.schema_json === '{' ? 'schema_json' : 'value_json';
    assert.throws(() => preflight.validateContract(args), error => error instanceof TypeError && error.message.includes(name) && error.message.length <= 4000);
  }
});

// Root-approved independent evidence aggregation cases, added before execution.
test('known enum membership and duplicates survive other unavailable numeric comparisons', () => {
  valid(validate('{"type":"integer","enum":[1,9007199254740993]}', '1'));
  const result = validate('{"type":"array","items":{"type":"integer"},"uniqueItems":true}', '[1,1,9007199254740993]');
  assert.ok(result.value_problems.some(item => item.code === 'invalid-input' && item.pointer === ''));
});
