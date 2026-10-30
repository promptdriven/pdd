import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { approveRun, runStatus, stepDone } from '../src/workflow-runner.mjs';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';

test('empty workflow status gives the public startup command', async t => {
  const f = await fixture(t);
  const result = await runStatus({ cwd: f.source }, f.ports);
  assert.equal(result.exitCode, 0, result.message);
  assert.match(result.message, /Start one with: pdd workflow start NAME ISSUE/);
});

test('published workflow PR identifies the public startup command', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  let run = f.record();
  assert.equal((await stepDone({ step: 'scope', summary: 'Use value two.', cwd: run.root }, f.agentPorts())).exitCode, 0);
  assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  run = f.record();
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n');
  f.git(run.root, 'commit', '-qam', 'Use value two');
  const workflow = JSON.parse(readFileSync(resolve(import.meta.dirname, '../skills/pdd-small-change/workflow.json'), 'utf8'));
  for (const step of workflow.areas.at(-1).steps) {
    const result = await stepDone({ step, summary: `${step} done`, cwd: run.root }, f.agentPorts());
    assert.equal(result.exitCode, 0, result.message);
  }
  assert.equal(f.prs.length, 1);
  assert.match(f.prs[0].body, /Made with `pdd workflow start small-change`/);
});
