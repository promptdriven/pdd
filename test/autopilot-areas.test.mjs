import test from 'node:test';
import assert from 'node:assert/strict';
import { parseCodeowners, resolveArea, resolveAreas } from '../src/autopilot-areas.mjs';

const areasFor = pattern => [{ name: 'literal', owner: 'literal-owner', match: { paths: [pattern] } }];
const resolve = (pattern, path) => resolveArea({ areas: areasFor(pattern), evidence: { paths: [path] } });

test('path rules treat regex punctuation as literal in explicit maps and CODEOWNERS', () => {
  for (const text of ['.', '+', '^', '$', '{', '}', '(', ')', '|', 'a.b+c^d$e{2}(f|g)']) {
    const pattern = `/src/${text}.mjs`, path = pattern.slice(1);
    assert.deepEqual(resolve(pattern, path), { state: 'resolved', area: 'literal', owner: 'literal-owner', source: 'config' });
    assert.equal(resolve(pattern, 'src/other.mjs').state, 'unsure');
    const codeowners = `/src/** @fallback\n${pattern} @literal-owner`;
    assert.equal(resolveArea({ codeowners, evidence: { paths: [path] } }).owner, 'literal-owner');
    assert.equal(resolveArea({ codeowners, evidence: { paths: ['src/other.mjs'] } }).owner, 'fallback');
  }
});

test('backslashes, brackets and negation remain unsupported in both owner sources', () => {
  for (const text of ['\\', '\\d', '\\.', '\\\\', '[x]', ']', '!']) {
    const pattern = `/src/${text}.mjs`;
    for (const path of [pattern.slice(1), 'src/d.mjs', 'src/1.mjs', 'src/x.mjs']) {
      assert.equal(resolve(pattern, path).state, 'unsure');
      assert.deepEqual(resolveAreas({ areas: areasFor(pattern), evidence: { paths: [path] } }), []);
      assert.equal(resolveArea({ codeowners: `/src/** @fallback\n${pattern} @unsafe`, evidence: { paths: [path] } }).owner, 'fallback');
    }
    assert.deepEqual(parseCodeowners(`${pattern} @unsafe`), []);
  }
});

test('literal encoding preserves wildcard, directory and anchor behavior', () => {
  const cases = [
    ['/src/a+b?.*', 'src/a+b1.mjs', true], ['/src/a+b?.*', 'src/ab1.mjs', false],
    ['/src/a+b?.*', 'nested/src/a+b1.mjs', false],
    ['/src/**/a+b.mjs', 'src/a+b.mjs', true], ['/src/**/a+b.mjs', 'src/deep/a+b.mjs', true],
    ['/src/**/a+b.mjs', 'src/deep/ab.mjs', false],
    ['a+b.mjs', 'nested/a+b.mjs', true], ['a+b.mjs', 'nested/ab.mjs', false],
    ['/src/a+b/', 'src/a+b/deep/file', true], ['/src/a+b/', 'src/ab/deep/file', false],
  ];
  for (const [pattern, path, matches] of cases) assert.equal(resolve(pattern, path).state === 'resolved', matches);
});
