import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { compileScenario } from '../src/scenario-compile.mjs';
import {
  MAX_VALIDATION_REPAIRS,
  detectChangedSurfaces,
  evaluateValidationOutcome,
  formatHumanVerificationCard,
  lintValidationCode,
  planValidationResume,
  shouldClaimWithCooldowns,
} from '../src/autopilot-validator.mjs';

const OPERATIONS = {
  detectChangedSurfaces,
  evaluateValidationOutcome,
  formatHumanVerificationCard,
  shouldClaimWithCooldowns,
  planValidationResume,
  lintValidationCode,
};

function resolvePointer(root, pointer) {
  if (!pointer || pointer === '') return root;
  const parts = pointer.split('/').slice(1).map((p) => p.replace(/~1/g, '/').replace(/~0/g, '~'));
  let cur = root;
  for (const part of parts) {
    if (cur === null || cur === undefined) return undefined;
    cur = Array.isArray(cur) ? cur[Number(part)] : cur[part];
  }
  return cur;
}

function assertCheck(actual, check, label) {
  switch (check.op) {
    case 'equals':
      assert.deepEqual(actual, check.value, label);
      return;
    case 'not_equals':
      assert.notDeepEqual(actual, check.value, label);
      return;
    case 'count':
      assert.equal(Array.isArray(actual) || typeof actual === 'string' ? actual.length : Object.keys(actual).length, check.value, label);
      return;
    case 'at_least': {
      const measured = check.measure === 'length'
        ? (Array.isArray(actual) || typeof actual === 'string' ? actual.length : Object.keys(actual).length)
        : actual;
      assert.ok(measured >= check.value, `${label}: expected >= ${check.value}, got ${measured}`);
      return;
    }
    case 'at_most': {
      const measured = check.measure === 'length'
        ? (Array.isArray(actual) || typeof actual === 'string' ? actual.length : Object.keys(actual).length)
        : actual;
      assert.ok(measured <= check.value, `${label}: expected <= ${check.value}, got ${measured}`);
      return;
    }
    case 'contains':
      assert.ok(typeof actual === 'string' && actual.includes(check.value), `${label}: expected "${actual}" to contain "${check.value}"`);
      return;
    default:
      throw new Error(`Unsupported check op ${check.op} in ${label}`);
  }
}

const rawDoc = JSON.parse(readFileSync(join(process.cwd(), 'test/runtime/autopilot-validator.json'), 'utf8'));
const storySource = readFileSync(join(process.cwd(), 'user_stories/autopilot-validator.md'), 'utf8');
const compiled = compileScenario(rawDoc, {
  path: 'test/runtime/autopilot-validator.json',
  storyPath: 'user_stories/autopilot-validator.md',
  storySource,
});

assert.equal(compiled.refusal, null, `scenario compile failed: ${JSON.stringify(compiled.refusal)}`);

for (const step of compiled.doc.steps) {
  test(`vector replay: ${step.step_id} (${step.checks.length} checks)`, () => {
    const fn = OPERATIONS[step.operation];
    assert.equal(typeof fn, 'function', `missing export for operation ${step.operation}`);
    const result = fn(step.input);
    for (const check of step.checks) {
      assert.equal(check.target, 'result');
      const actual = resolvePointer(result, check.path);
      assertCheck(actual, check, `${step.step_id} ${check.path} (${check.op})`);
    }
  });
}

test('contract constant and surface/card edge cases', () => {
  assert.equal(MAX_VALIDATION_REPAIRS, 3);
  const docs = detectChangedSurfaces({ changedFiles: ['docs/cli.md', 'README.md', 'CHANGELOG.md'] });
  assert.equal(docs.docsOnly, true);
  assert.equal(docs.requiresRealE2e, false);
  assert.deepEqual(docs.requiredProofKinds, []);

  const mixed = detectChangedSurfaces({ changedFiles: ['README.md', 'src/worker.mjs'] });
  assert.equal(mixed.docsOnly, false);
  assert.equal(mixed.requiresRealE2e, true);
  assert.deepEqual(mixed.requiredProofKinds, ['real-execution']);

  const card = formatHumanVerificationCard({
    offlineSummary: 'unit 12/12',
    unverifiedBoundary: '2FA login prompt',
    verifyCommand: 'npm run verify:2fa',
  });
  assert.deepEqual(card, [
    'Passed offline: unit 12/12',
    'Unverified boundary: 2FA login prompt',
    'Verify command: npm run verify:2fa',
  ]);
});
