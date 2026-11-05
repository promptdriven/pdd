import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzeTestChanges } from '../src/workflow-inventory.mjs';
const file = (path, before, after) => ({oldPath:path,newPath:path,before,after});
test('dynamic pairs disclose uncertainty while healthy and empty pairs retain evidence', () => {
  const report = analyzeTestChanges({files:[
    file('test/dynamic.js', 'test("old", () => {});', 'test(name, () => {});'),
    file('test/healthy.js', 'test("old", () => {});', 'test("new", () => {});'),
    file('test/empty.js', '/* only comments */', '')
  ]});
  assert.equal(report.available,true);
  assert.match(report.details,/dynamic\.js" unavailable \("unknown dynamic test inventory"\)/);
  assert.match(report.details,/healthy\.js" 1 → 1 tests\. Removed: 1/);
  assert.match(report.details,/empty\.js" 0 → 0 tests/);
});
test('recognizes bounded alias and loop signals but ignores a loop in a test body', () => {
  for (const source of ['import { test as check } from "node:test";\ncheck("x", () => {});', 'for (const x of xs) {\n  test("x", () => {});\n}']) {
    assert.match(analyzeTestChanges({files:[file('test/a.js','',source)]}).details,/unknown dynamic test inventory/);
  }
  const source = 'test("x", () => {\n  for (const x of xs) {\n    expect(x);\n  }\n});';
  assert.doesNotMatch(analyzeTestChanges({files:[file('test/a.js','',source)]}).details,/unknown dynamic/);
});
