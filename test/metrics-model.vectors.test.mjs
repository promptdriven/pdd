import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { applyMetricsToggle, calculateAutopilotMetrics } from '../src/metrics-model.mjs';

const OPERATIONS = {
  applyMetricsToggle,
  calculateAutopilotMetrics,
};

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

function registerScenarioTests(name, scenarioPath, storyPath, { expectAcIds = false } = {}) {
  const scenario = JSON.parse(readFileSync(new URL(scenarioPath, import.meta.url), 'utf8'));
  const storyText = readFileSync(new URL(storyPath, import.meta.url), 'utf8');

  test(`Story criteria in ${name} match ${storyPath.replace(/^\.\.\//, '')} word for word`, () => {
    const numbered = [...storyText.matchAll(/^\d+\.\s+(.+)$/gm)].map(m => m[1].trim());
    assert.equal(numbered.length, scenario.criteria.length);
    for (let i = 0; i < numbered.length; i++) {
      if (expectAcIds) assert.equal(scenario.criteria[i].id, `AC${i + 1}`);
      assert.equal(scenario.criteria[i].text, numbered[i]);
    }
  });

  for (const step of scenario.steps) {
    test(`${name}: ${step.step_id}`, () => {
      const fn = OPERATIONS[step.operation];
      assert.ok(fn, `Unsupported operation ${step.operation}`);
      const result = fn(structuredClone(step.input));
      for (const check of step.checks) {
        assert.equal(check.target, 'result');
        const actual = pointerGet(result, check.path);
        const label = `${step.step_id} ${check.criterion_id} ${check.path}`;
        if (check.op === 'equals') {
          assert.deepEqual(actual, check.value, label);
        } else if (check.op === 'contains') {
          assert.ok(String(actual ?? '').includes(check.value), label);
        } else {
          assert.fail(`Unsupported check op ${check.op} on ${label}`);
        }
      }
    });
  }
}

registerScenarioTests(
  'metrics-shared-report.json',
  './runtime/metrics-shared-report.json',
  '../user_stories/metrics-shared-report.md',
  { expectAcIds: true },
);
registerScenarioTests(
  'metrics-v2-scorecard.json',
  './runtime/metrics-v2-scorecard.json',
  '../user_stories/metrics-v2-scorecard.md',
);
