import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, mkdtempSync, writeFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join, resolve} from 'node:path';
import {spawnSync} from 'node:child_process';

const command = resolve('examples/native-replay/replay.mjs');
const cases = resolve('examples/native-replay/cases.json');
const target = resolve('examples/native-replay/count-words.mjs');
const run = (file, module) => spawnSync(process.execPath, [command, file, module], {encoding:'utf8'});

test('native recipe executes the public function and detects return and error controls', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-native-recipe-'));
  t.after(() => rmSync(dir, {recursive:true, force:true}));
  assert.ok(existsSync(command), 'native replay command is available');
  const good = run(cases, target);
  assert.equal(good.status, 0, good.stderr);
  assert.match(good.stdout, /2\/2 passed/);
  for (const [name, source, failed] of [
    ['wrong return', "export function countWords(x) { if (x === 42) throw new TypeError('text must be a string'); return 3; }", 'two-words'],
    ['wrong error', "export function countWords(x) { if (x === 42) throw new TypeError('wrong'); return 2; }", 'non-string'],
    ['wrong error class', "export function countWords(x) { if (x === 42) throw new Error('text must be a string'); return 2; }", 'non-string'],
    ['missing error', 'export function countWords() { return 2; }', 'non-string'],
    ['unexpected error', "export function countWords() { throw new Error('unexpected'); }", 'two-words']
  ]) {
    {
      const file = join(dir, name.replaceAll(' ', '-') + '.mjs');
      writeFileSync(file, source);
      const result = run(cases, file);
      assert.equal(result.status, 1, name);
      assert.match(result.stdout, new RegExp(`FAIL ${failed}`), name);
    }
  }
  const missing = join(dir, 'missing.mjs'); writeFileSync(missing, 'export const other = 1;');
  const result = run(cases, missing);
  assert.equal(result.status, 1);
  assert.match(result.stderr, /missing countWords export/);
  assert.doesNotMatch(result.stdout, /PASS/);
  const malformed = join(dir, 'bad.json'); writeFileSync(malformed, '{"cases":[{"id":"bad"}]}');
  const invalid = run(malformed, target);
  assert.equal(invalid.status, 1);
  assert.match(invalid.stderr, /invalid case/);
  assert.doesNotMatch(invalid.stdout, /PASS/);
});
