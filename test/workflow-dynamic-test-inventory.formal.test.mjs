import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzeTestChanges } from '../src/workflow-inventory.mjs';

// The labels are the Story oracle: uncertainty is an input property, not
// inferred from the analyzer's report. Every ordered pair is enumerated.
const states = [
  {name:'absent', source:'', present:false, unknown:false, count:0},
  {name:'empty', source:'/* empty */', present:true, unknown:false, count:0},
  {name:'static', source:'test("kept", () => {});', present:true, unknown:false, count:1},
  {name:'computed', source:'test(name, () => {});', present:true, unknown:true},
  {name:'import', source:'import "./must-not-load.js";', present:true, unknown:true},
  {name:'loop', source:'for (const x of xs) {\n test("generated", () => {});\n}', present:true, unknown:true},
  {name:'mixed', source:'test("kept", () => {});\ntest(name, () => {});', present:true, unknown:true},
];
const categories = ['Tests vs base:', 'Changed assertions in kept tests:', 'New skips:'];
test('bounded dynamic pairs preserve uncertainty and independent evidence without execution', t => {
  let pairs = 0;
  for (const before of states) for (const after of states) {
    // Both absent is represented by a present empty path; all other pairs
    // include additions, deletions and renames where both sides exist.
    const file = {oldPath:before.present ? 'test/new.js' : '', newPath:after.present ? 'test/new.js' : '', before:before.source, after:after.source};
    if (!file.oldPath && !file.newPath) file.newPath = 'test/new.js';
    const healthy = {oldPath:'test/healthy.js',newPath:'test/healthy.js',before:'test("old", () => {});',after:'test("new", () => {});'};
    const report = analyzeTestChanges({files:[file, healthy]});
    assert.equal(report.available, true, `${before.name}/${after.name}`);
    const path = file.newPath || file.oldPath;
    const lines = report.details.split('\n');
    if (before.unknown || after.unknown) {
      for (const category of categories) {
        const matching = lines.filter(line => line.startsWith(`${category} "${path}"`));
        assert.deepEqual(matching, [`${category} "${path}" unavailable ("unknown dynamic test inventory").`], `${before.name}/${after.name}`);
      }
    } else {
      assert.ok(lines.some(line => line.startsWith(`Tests vs base: "${path}" ${before.count} → ${after.count} tests.`)), `${before.name}/${after.name}`);
    }
    assert.ok(lines.some(line => line.startsWith('Tests vs base: "test/healthy.js" 1 → 1 tests. Removed: 1')), `${before.name}/${after.name}`);
    pairs++;
  }
  // A source evaluation or import resolution would throw; analysis must remain static.
  const poison = 'import "./must-not-load.js";\nthrow new Error("source executed");';
  const report = analyzeTestChanges({files:[{oldPath:'',newPath:'test/poison.js',before:'',after:poison}]});
  assert.match(report.details, /unknown dynamic test inventory/);
  t.diagnostic(`Story domain: ${states.length} states, ${pairs} ordered pairs, one poison source`);
});
