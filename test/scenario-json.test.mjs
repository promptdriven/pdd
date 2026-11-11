import './helpers/test-home.mjs';
import assert from 'node:assert/strict';
import test from 'node:test';
import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { parseScenarioJson, stringifyScenarioJson, exactNumber, exactValue, exactIntegerLeaves, withExactIntegers, jsonSafe } from '../src/scenario-json.mjs';
import { formatDuration, formatDurationWithNumberHours } from './fixtures/large-integers/duration.mjs';

const root = resolve(import.meta.dirname, '..');
const fixture = join(root, 'test/fixtures/large-integers/format-duration.json');
const LARGE = '4250129834582680692326400'; // 3600 x 2^70, an exact Number value above 2^53
const ABOVE = '9007199254740993'; // 2^53 + 1, no Number has this value

test('SJ1: an exact integer literal above 2^53 is read and written digit for digit', () => {
  const value = parseScenarioJson(`{"seconds": ${LARGE}, "next": ${ABOVE}, "small": 90000, "negative": -${ABOVE}}`);
  assert.equal(value.seconds, 4250129834582680692326400n);
  assert.equal(value.next, 9007199254740993n);
  assert.equal(value.negative, -9007199254740993n);
  assert.equal(value.small, 90000);
  assert.equal(stringifyScenarioJson(value), `{"seconds":${LARGE},"next":${ABOVE},"small":90000,"negative":-${ABOVE}}`);
  assert.equal(stringifyScenarioJson(value, 2), `{\n  "seconds": ${LARGE},\n  "next": ${ABOVE},\n  "small": 90000,\n  "negative": -${ABOVE}\n}`);
  // The edges: 2^53 - 1 stays a Number, 2^53 is already outside the exact range.
  assert.equal(parseScenarioJson('9007199254740991'), 9007199254740991);
  assert.equal(parseScenarioJson('9007199254740992'), 9007199254740992n);
  assert.equal(parseScenarioJson('-9007199254740991'), -9007199254740991);
});

test('SJ2: a value just above 2^53 has no exact Number and is refused, never rounded', () => {
  const value = parseScenarioJson(ABOVE);
  assert.throws(() => exactNumber(value), error => error instanceof RangeError && error.code === 'scenario-number-inexact'
    && error.message.includes(ABOVE) && error.message.includes('9007199254740992'));
  assert.notDeepStrictEqual(exactValue(9007199254740992), exactValue(value));
  assert.throws(() => exactNumber('9007199254740993'), error => error instanceof TypeError && error.code === 'scenario-number-inexact');
  // 3600 x 2^70 has an exact Number, so a Number parameter receives it unchanged.
  assert.equal(exactNumber(parseScenarioJson(LARGE)), 3600 * 2 ** 70);
  assert.equal(exactNumber(42), 42);
  assert.deepStrictEqual(exactValue(3600 * 2 ** 70), 4250129834582680692326400n);
  assert.deepStrictEqual(exactValue({ a: [12n, 3600 * 2 ** 70, 'x'] }), { a: [12, 4250129834582680692326400n, 'x'] });
});

test('SJ3: fractions, exponents, negative zero and invalid JSON keep JSON.parse meaning', () => {
  for (const text of ['1e21', '2.5', '9007199254740993.0', '-0', '[1e300, -1.5e-7, 0.1]', '{"a":"9007199254740993"}', 'true', 'null', '"x"'])
    assert.deepStrictEqual(parseScenarioJson(text), JSON.parse(text), text);
  assert.ok(Object.is(parseScenarioJson('-0'), -0));
  assert.equal(typeof parseScenarioJson('9007199254740993.0'), 'number');
  for (const text of ['', '{', '[1,]', '01', '{"a":1}x']) {
    let expected; try { JSON.parse(text); } catch (error) { expected = error; }
    assert.throws(() => parseScenarioJson(text), error => error instanceof SyntaxError && error.message === expected.message, text);
  }
  assert.equal(stringifyScenarioJson(undefined), undefined);
});

test('SJ4: every existing scenario file in this package means exactly what JSON.parse gives', () => {
  const files = execFileSync('git', ['ls-files', '-z', '*.json'], { cwd: root, encoding: 'utf8' }).split('\0').filter(Boolean);
  let scenarios = 0;
  for (const path of files) {
    if (path.startsWith('test/fixtures/large-integers/')) continue;
    const text = readFileSync(join(root, path), 'utf8');
    if (!text.includes('prompt-runtime.program-scenario.v1')) continue;
    let ordinary; try { ordinary = JSON.parse(text); } catch { continue; }
    scenarios += 1;
    const exact = parseScenarioJson(text);
    assert.deepStrictEqual(exact, ordinary, path);
    assert.deepStrictEqual(exactIntegerLeaves(exact), [], path);
    assert.equal(stringifyScenarioJson(exact, 2), JSON.stringify(ordinary, null, 2), path);
  }
  assert.ok(scenarios >= 20, `found ${scenarios} scenario files`);
});

test('SJ5: a JSON-only record keeps exact digits beside its ordinary copy', () => {
  const exact = parseScenarioJson(`{"steps":[{"input":{"a/b":${ABOVE},"c~d":[1,${LARGE}]}}]}`);
  const leaves = exactIntegerLeaves(exact);
  assert.deepStrictEqual(leaves, [{ pointer: '/steps/0/input/a~1b', value: ABOVE }, { pointer: '/steps/0/input/c~0d/1', value: LARGE }]);
  const safe = jsonSafe(exact);
  assert.deepStrictEqual(safe, JSON.parse(`{"steps":[{"input":{"a/b":${ABOVE},"c~d":[1,${LARGE}]}}]}`));
  const saved = JSON.parse(JSON.stringify({ snapshot: safe, exact_integers: leaves }));
  assert.deepStrictEqual(withExactIntegers(saved.snapshot, saved.exact_integers), exact);
  // A pointer that no longer holds the rounded Number is ignored rather than invented.
  assert.deepStrictEqual(withExactIntegers({ a: 1 }, [{ pointer: '/a', value: ABOVE }, { pointer: '/b', value: ABOVE }]), { a: 1 });
});

test('SJ6: a vector with 3600 x 2^70 seconds replays exactly through the documented reviver', () => {
  const text = readFileSync(fixture, 'utf8');
  // The one-line reader that a repository's own vector test uses (docs/replay-evidence.md).
  const scenario = JSON.parse(text, (key, value, context) =>
    typeof value === 'number' && /^-?(?:0|[1-9][0-9]*)$/.test(context.source) && !Number.isSafeInteger(value) ? BigInt(context.source) : value);
  assert.deepStrictEqual(scenario, parseScenarioJson(text));
  assert.equal(scenario.steps[1].input.seconds, 4250129834582680692326400n);
  const replay = format => scenario.steps.map(step => {
    const actual = { text: format(exactNumber(step.input.seconds)) };
    return step.checks.every(check => {
      const value = actual[check.path.slice(1)];
      try { assert.deepStrictEqual(exactValue(value), exactValue(check.value)); return true; } catch { return false; }
    });
  });
  assert.deepStrictEqual(replay(formatDuration), [true, true, true]);
  // The same vector catches the defect: Number hour arithmetic loses the exact digits.
  assert.deepStrictEqual(replay(formatDurationWithNumberHours), [true, false, false]);
});
