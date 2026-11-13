import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { findTests, preflight, projectAnswer, renderJson, renderText } from '../src/runtime-seam.mjs';
import { storyCard } from '../src/workflow-story-card.mjs';
import { harbor } from './runtime-package/runtime-fake.mjs';

test('ISSUE869: preflight admits relational ref_target checks, lt/lte/gt/gte, and integer_relation as exact criterion coverage', t => {
  for (const check of [
    { criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'lte', value: 1000 },
    { criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'lt', value: 1000 },
    { criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'gt', value: 100 },
    { criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'gte', value: 100 },
    { criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'at_most', ref_target: 'input', ref_path: '/capCents' },
    { criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'equals', value: { ref_target: 'input', ref_path: '/expectedCents' } },
    {
      criterion_id: 'AC1',
      target: 'result',
      path: '',
      op: 'integer_relation',
      value: {
        left: { sum: [{ field: '/subtotalCents' }, { field: '/taxCents' }] },
        compare: 'eq',
        right: { ref_target: 'result', ref_path: '/totalCents' },
      },
    },
  ]) {
    const setup = harbor(t), file = join(setup.repo, 'tests/place-order.json');
    const source = JSON.parse(readFileSync(file, 'utf8'));
    source.criteria = [source.criteria[0]];
    writeFileSync(join(setup.repo, source.story_path), `# Place order\n\n## Acceptance criteria\n\n1. ${source.criteria[0].text}\n`);
    source.steps[0].checks = [check];
    writeFileSync(file, `${JSON.stringify(source, null, 2)}\n`);
    const found = findTests({ root: setup.repo });
    const selected = found.tests.filter(item => item.path === 'tests/place-order.json');
    const result = preflight({ root: setup.repo, found, selected });
    assert.deepEqual(result.rows[0].refusals, [], JSON.stringify(check));
    assert.deepEqual(result.rows[0].not_checked ?? [], [], JSON.stringify(check));
  }
});

test('ISSUE869: runtime-output preserves relational reference metadata and renders failed relational checks clearly', () => {
  const secret = 'ghp_1234567890abcdefghijklmnopqrstuvwx12';
  const answer = {
    command: 'check',
    state: 'failed',
    accounting_complete: true,
    usage: { calls: 1, seconds: 1.2, input_tokens: 100, cached_input_tokens: 20, output_tokens: 15 },
    result: {
      report: {
        criterion_results: [{ criterion_id: 'AC1', status: 'failed' }],
        samples: [{
          steps: [{
            step_id: 's1',
            result: { fee_cents: 650 },
            checks: [{
              criterion_id: 'AC1',
              target: 'result',
              path: '/fee_cents',
              op: 'at_most',
              ref_target: 'input',
              ref_path: '/cap_cents',
              expected: 500,
              actual: 650,
              passed: false,
            }],
          }],
        }],
      },
    },
  };
  const projected = projectAnswer(answer, {
    origin: 'https://runtime.example',
    secrets: [secret],
    steps: [{ step_id: 's1' }],
    criterionTexts: { AC1: 'Fee stays within cap.' },
    test: 'tests/settlement.json',
  });
  assert.equal(projected.failed_checks.length, 1);
  assert.equal(projected.failed_checks[0].op, 'at_most');
  assert.equal(projected.failed_checks[0].ref_target, 'input');
  assert.equal(projected.failed_checks[0].ref_path, '/cap_cents');

  const row = {
    story: 'settlement',
    title: 'Settlement',
    test: 'tests/settlement.json',
    phase: 'server',
    request_ids: ['req-1'],
    seconds: 1.2,
    ...projected,
  };
  const text = renderText({ batch: '20261113-030000-abcd', rows: [row], exitCode: 1, secrets: [secret] });
  assert.match(text, /AC1  step s1  result \/fee_cents  expected at_most input \/cap_cents \(500\), got 650/);
  const json = renderJson({ batch: '20261113-030000-abcd', repo: 'demo/repo', rows: [row], exitCode: 1 });
  assert.equal(json.rows[0].failed_checks[0].ref_target, 'input');
  assert.equal(json.rows[0].failed_checks[0].ref_path, '/cap_cents');
});

test('ISSUE869: workflow story card formats inline ref_target and integer_relation checks cleanly', t => {
  const setup = harbor(t), file = join(setup.repo, 'tests/place-order.json');
  const source = JSON.parse(readFileSync(file, 'utf8'));
  source.steps[0].checks = [
    { criterion_id: 'AC1', target: 'result', path: '/fee_cents', op: 'at_most', ref_target: 'input', ref_path: '/cap_cents' },
    {
      criterion_id: 'AC2',
      target: 'result',
      path: '',
      op: 'integer_relation',
      value: {
        left: { field: '/total_cents' },
        compare: 'eq',
        right: { ref_target: 'input', ref_path: '/gross_cents' },
      },
    },
  ];
  writeFileSync(file, `${JSON.stringify(source, null, 2)}\n`);
  const card = storyCard({ run: { repo: 'demo/repo', number: 869, issue: { title: 'Relational checks', url: 'https://example.test/869' } }, root: setup.repo, changed: ['tests/place-order.json'] });
  assert.match(card, /input \/cap_cents/);
  assert.match(card, /integer_relation/);
});
