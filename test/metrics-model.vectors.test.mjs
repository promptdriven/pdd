import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { applyMetricsToggle, calculateAutopilotMetrics } from '../src/metrics-model.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/metrics-shared-report.json', import.meta.url), 'utf8'));
const storyText = readFileSync(new URL('../user_stories/metrics-shared-report.md', import.meta.url), 'utf8');

function pointerGet(root, pointer) {
  if (!pointer || pointer === '/') return root;
  const parts = pointer.slice(1).split('/').map(p => p.replaceAll('~1', '/').replaceAll('~0', '~'));
  let cur = root;
  for (const part of parts) {
    assert.notEqual(cur, undefined, `Missing parent at ${pointer}`);
    assert.notEqual(cur, null, `Null parent at ${pointer}`);
    cur = Array.isArray(cur) ? cur[Number(part)] : cur[part];
  }
  return cur;
}

test('Story criteria in metrics-shared-report.json match user_stories/metrics-shared-report.md word for word', () => {
  const numbered = [...storyText.matchAll(/^\d+\.\s+(.+)$/gm)].map(m => m[1].trim());
  assert.equal(numbered.length, scenario.criteria.length);
  for (let i = 0; i < numbered.length; i++) {
    assert.equal(scenario.criteria[i].id, `AC${i + 1}`);
    assert.equal(scenario.criteria[i].text, numbered[i]);
  }
});

for (const step of scenario.steps) {
  test(`metrics-shared-report.json: ${step.step_id}`, () => {
    const fn = step.operation === 'applyMetricsToggle' ? applyMetricsToggle : calculateAutopilotMetrics;
    const result = fn(structuredClone(step.input));
    for (const check of step.checks) {
      assert.equal(check.target, 'result');
      assert.equal(check.op, 'equals');
      assert.deepEqual(
        pointerGet(result, check.path),
        check.value,
        `${step.step_id} ${check.criterion_id} ${check.path}`,
      );
    }
  });
}
