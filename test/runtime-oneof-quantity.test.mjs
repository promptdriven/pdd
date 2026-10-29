import test from 'node:test';
import assert from 'node:assert/strict';
import { checkInput, numberWarnings } from '../src/runtime-preflight.mjs';

// Original A25 address domain, before pocket's workaround commit 4a13573e5.
const address = { oneOf: [
  { type: 'string', pattern: '^ws://127\\.0\\.0\\.1:[1-9][0-9]{0,3}/?$' },
  { type: 'string', pattern: '^unix://[^\\s]+$' },
  { type: 'string', pattern: '^[^\\s:]+$' },
] };
const object = properties => ({ type: 'object', properties, required: Object.keys(properties), additionalProperties: false });

test('ONEOF2500: each original address pattern passes without overlap or irrelevant alternative warnings', () => {
  for (const value of ['ws://127.0.0.1:8080', 'ws://127.0.0.1:9/', 'unix:///tmp/pocket.sock', 'pocket']) {
    assert.deepEqual(checkInput({ address: value }, object({ address }), 0), { refusals: [], warnings: [] }, value);
  }
});

test('ONEOF2500: actual matching pattern overlap is still refused at the nested field', () => {
  const schema = object({ address: { oneOf: [
    { type: 'string', pattern: '^unix://' }, { type: 'string', pattern: 'sock$' },
  ] } });
  const result = checkInput({ address: 'unix:///tmp/pocket.sock' }, schema, 0);
  assert.equal(result.refusals.length, 1);
  assert.equal(result.refusals[0].section, 'steps[0].input.address');
  assert.match(result.refusals[0].message, /more than one/);
});

test('ONEOF2500: recursive branch membership honors patterns in object fields and array items', () => {
  const schema = { oneOf: ['a', 'b'].map(prefix => object({
    addresses: { type: 'array', items: { type: 'string', pattern: `^${prefix}:` } },
  })) };
  assert.deepEqual(checkInput({ addresses: ['a:one', 'a:two'] }, schema, 0), { refusals: [], warnings: [] });
  const overlapping = { oneOf: [object({ addresses: { type: 'array', items: { type: 'string', pattern: '^a:' } } }),
    object({ addresses: { type: 'array', items: { type: 'string', pattern: 'one$' } } })] };
  assert.match(checkInput({ addresses: ['a:one'] }, overlapping, 0).refusals[0].message, /more than one/);
});

test('ONEOF2500: invalid or unjudged patterns cannot prove overlap', () => {
  for (const pattern of ['[', '(?P<address>unix://).*']) {
    const result = checkInput('unix:///tmp/pocket.sock', { oneOf: [
      { type: 'string', pattern: '^unix://' }, { type: 'string', pattern },
    ] }, 0);
    assert.deepEqual(result.refusals, [], pattern);
  }
});

test('ONEOF2500: all-pattern misses remain advisory; definite structural failures still refuse', () => {
  const miss = checkInput({ address: 'not an address' }, object({ address }), 0);
  assert.deepEqual(miss.refusals, []);
  assert.ok(miss.warnings.length > 0);
  const wrongType = checkInput({ address: 42 }, object({ address }), 0);
  assert.ok(wrongType.refusals.length > 0);
  const simple = checkInput('bad', { type: 'string', pattern: '^good$' }, 0);
  assert.deepEqual(simple.refusals, []);
  assert.equal(simple.warnings.length, 1);
});

const criterion = 'Starting from seed 42, I can play the fixed 30 moves and get the established replay result.';
const scoreDoc = (text = criterion, path = '/score', value = 28, op = 'equals') => ({
  story_path: 'user_stories/same-seed-same-game.md', criteria: [{ id: 'AC2', text }],
  steps: [{ step_id: 'replay-through-move-10', checks: [{ criterion_id: 'AC2', target: 'result', path, op, value }] }],
});

test('NUMERIC2500: original replay score28 after move10 is a different quantity from 30 moves', () => {
  const source = scoreDoc(), before = structuredClone(source);
  assert.deepEqual(numberWarnings(source), []);
  assert.deepEqual(numberWarnings(scoreDoc(criterion, '/state/score', [28, 29], 'one_of')), []);
  assert.deepEqual(source, before);
});

test('NUMERIC2500: same quantity contradictions still warn for scores and move counts', () => {
  for (const [text, path] of [['The score is 30 after move 10.', '/score'], [criterion, '/moves']]) {
    const warnings = numberWarnings(scoreDoc(text, path), { testPath: 'tests/replay.json' });
    assert.equal(warnings.length, 1);
    assert.match(warnings[0], /possible numeric mismatch.*tests\/replay.json.*result.*28.*AC2.*30/);
  }
});

test('NUMERIC2500: an equal number belonging to another quantity cannot hide a score typo', () => {
  const warnings = numberWarnings(scoreDoc('After 28 moves, the score is 30.'));
  assert.equal(warnings.length, 1);
  assert.match(warnings[0], /28.*AC2.*30/);
});

test('NUMERIC2500: ambiguous paths retain advice instead of silently assuming a different quantity', () => {
  assert.equal(numberWarnings(scoreDoc(criterion, '/x')).length, 1);
});
