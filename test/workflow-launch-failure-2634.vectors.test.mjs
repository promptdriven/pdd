import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
import { runStatus } from '../src/workflow-runner.mjs';
const scenario = JSON.parse(readFileSync(join(packageRoot, 'test/runtime/area-launch-failure-2634.json'), 'utf8'));
for (const step of scenario.steps) test(`replay ${step.step_id}`, async t => {
  const f = await fixture(t, {agent:'codex',name:'feature'}); await f.run();
  const run = f.record(), sample = JSON.parse(scenario.simulation['runs.resolveRun'].result_template.json).run;
  const chat = run.chats.at(-1); Object.assign(chat, {state:'failed',code:'agent_launch_exited'});
  run.chatFailure = {...sample.chatFailure, area:chat.area};
  writeFileSync(join(run.runDir,'status.json'), JSON.stringify(run));
  f.herdr.paneOf(chat).agent = null;
  const result = await runStatus({ref:'17',cwd:f.source},f.ports);
  for (const check of step.checks) {
    const actual = result[check.path.slice(1)];
    const expected = typeof check.value === 'string' ? check.value.replace('2634', '17') : check.value;
    if (check.op === 'equals') assert.equal(actual, expected);
    else if (check.op === 'contains') assert.ok(actual.includes(expected), `${actual} lacks ${expected}`);
    else assert.fail(`Unsupported check ${check.op}`);
  }
});
