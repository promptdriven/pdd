import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { compareScreen } from '../src/screen-compare.mjs';
import { temp } from './runtime-fake.mjs';

// Story oracle: user_stories/screen-label-ownership.md, Rules to check.
// Exhaustive part-snapshot domain: 2 reference ownership states × 3 states
// (absent/visible/hidden) independently for self/nested/outside × 2 page orders
// = 108 configurations. One label, one uniquely matched painted box, fixed valid
// geometry. This does not prove DOM capture, repeated-label consumption or CLI.
const states = ['absent', 'visible', 'hidden'];
const viewport = { width: 400, height: 400 };
const regionBox = { x: 20, y: 20, width: 100, height: 80 };
const labelBox = { x: 30, y: 45, width: 55, height: 20 };
const part = (kind, value, node, ancestors, visible, region = null) => ({
  kind, value, node, ancestors, visible, region,
  box: kind === 'id' ? regionBox : labelBox,
});

for (const owned of [true, false]) test(`FORMAL label ownership: ${owned ? 'owned' : 'unowned'}, all 54 configurations`, async t => {
  const cwd = temp(t), drawingPath = 'bounded.ui.svg';
  const text = '<text x="30" y="60">READY</text>';
  const source = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><g id="box"><rect x="20" y="20" width="100" height="80" fill="silver"/>${owned ? text : ''}</g>${owned ? '' : text}</svg>`;
  writeFileSync(join(cwd, drawingPath), source);
  const reference = [part('id', 'box', 1, [], true),
    part('text', 'READY', 2, owned ? [1] : [], true, owned ? 'box' : null)];
  let cases = 0, browserCalls = 0;
  for (const self of states) for (const nested of states) for (const outside of states) for (const reverse of [false, true]) {
    // Independent requirement oracle: outside states are irrelevant when owned.
    const eligible = owned ? [self, nested] : [self, nested, outside];
    const expected = eligible.includes('visible') ? 'pass' : eligible.includes('hidden') ? 'hidden' : 'missing';
    const occurrences = [
      [self, 10, []], [nested, 12, [11, 10]], [outside, 13, []],
    ].filter(([state]) => state !== 'absent').map(([state, node, ancestors]) =>
      part('text', 'READY', node, ancestors, state === 'visible'));
    const actual = [part('id', 'box', 10, [], true), ...occurrences];
    if (reverse) actual.reverse();
    const report = await compareScreen({ url: 'https://example.test/bounded', drawingPath, cwd }, {
      browser: async request => {
        browserCalls++;
        assert.equal(request.source, source);
        return structuredClone({ viewport, reference, actual });
      },
    });
    const context = JSON.stringify({ owned, self, nested, outside, reverse });
    assert.equal(report.rows.length, 2, context);
    assert.equal(report.rows[0].kind, 'id', context);
    assert.equal(report.rows[0].status, 'pass', context);
    assert.equal(report.rows[1].kind, 'text', context);
    assert.equal(report.rows[1].status, expected, context);
    assert.equal(report.passed, expected === 'pass', context);
    cases++;
  }
  assert.equal(cases, 54);
  assert.equal(browserCalls, 54);
});
