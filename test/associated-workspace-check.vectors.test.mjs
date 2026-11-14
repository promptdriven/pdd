import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fullCheckPass } from '../src/workflow-story-card.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/associated-workspace-check.json', import.meta.url)));
const cases = scenario.steps.map((step, index) => ({ step, index }));
cases.push({ step: scenario.steps[1], index: 0, stage: 'before', label: 'before-stage evidence' });
cases.push({ step: scenario.steps[1], index: 0, stage: 'pr1', label: 'PR 1 evidence' });
cases.push({ step: scenario.steps[1], index: 0, mismatch: true, label: 'mismatched summary producer' });
for (const { step, index, stage, mismatch, label } of cases) test(`scenario: ${label ?? step.step_id}`, t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-associated-vector-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const translate = path => join(dir, path);
  for (const [path, file] of Object.entries(scenario.initial_world.files)) {
    const target = translate(path);
    mkdirSync(dirname(target), { recursive: true });
    const content = path.endsWith('/batch.json') || path.endsWith('/summary.json')
      ? file.content.replaceAll('/producer', translate('/producer')) : file.content;
    writeFileSync(target, content);
  }
  if (mismatch) {
    const path = translate('/state/batches/20261027-170004-0001/summary.json');
    const summary = JSON.parse(readFileSync(path));
    summary.repo = translate('/run');
    writeFileSync(path, JSON.stringify(summary));
  }
  const fixture = scenario.simulation['workspace.eligible'].cases[index];
  const result = fullCheckPass({ ...step.input, root: translate(step.input.root) }, {
    env: { PDD_STATE_DIR: translate('/state') },
    capture: () => JSON.parse(scenario.simulation['source.capture'].result_template.json),
    findTests: () => JSON.parse(scenario.simulation['source.findTests'].result_template.json),
    workspace: input => {
      assert.deepEqual({ ...input, root: '/run', producerRoot: '/producer' }, fixture.args);
      assert.equal(input.root, translate('/run'));
      assert.equal(input.producerRoot, translate('/producer'));
      return fixture.result.eligible ? { state: 'eligible', stage: stage ?? 'current' } : { state: 'unavailable' };
    },
  });
  assert.equal(result.pass, step.checks[0].value, JSON.stringify(result));
});
