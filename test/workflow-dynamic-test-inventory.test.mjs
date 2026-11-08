import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { analyzeTestChanges, collectTestInventory } from '../src/workflow-inventory.mjs';
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
test('multiline import alias makes a committed mixed static pair unknown in every category', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-alias-'));
  t.after(() => rmSync(root, {recursive:true, force:true}));
  const git = (...args) => execFileSync('git', args, {cwd:root, encoding:'utf8'}).trim();
  git('init', '-q');
  git('config', 'user.email', 'test@example.invalid');
  git('config', 'user.name', 'Test');
  mkdirSync(join(root, 'test'));
  const before = 'test("static", () => {});\n';
  const after = 'import {\n  test as check\n} from "node:test";\ntest("static", () => {});\ncheck("generated", () => {});\n';
  writeFileSync(join(root, 'test/a.js'), before);
  git('add', '.'); git('commit', '-qm', 'base');
  const baseSha = git('rev-parse', 'HEAD');
  writeFileSync(join(root, 'test/a.js'), after);
  git('add', '.'); git('commit', '-qm', 'head');
  const headSha = git('rev-parse', 'HEAD');
  const report = await collectTestInventory({cwd:root, baseSha, headSha});
  for (const category of ['Tests vs base', 'Changed assertions in kept tests', 'New skips']) {
    assert.ok(report.details.includes(`${category}: "test/a.js" unavailable ("unknown dynamic test inventory").`), report.details);
  }
});
