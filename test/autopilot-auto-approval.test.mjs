import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {cpSync, mkdirSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {automaticFixture} from './helpers/autopilot-run-base-fixture.mjs';
import {packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {advanceAutomaticPr1, runStatus, stepDone} from '../src/workflow-runner.mjs';
import {captureSource} from '../src/runtime-preflight.mjs';
import {renderJson} from '../src/runtime-output.mjs';
import {readPromptApprovals} from '../src/approval-policy.mjs';
import {approvalRecords} from '../src/workflow-pr-evidence.mjs';

const STORY = 'user_stories/place-order.md', TEST = 'tests/place-order.json', PROMPT = 'prompts/place_order.prompt.md';
let batches = 0;

function saveCheck(f, {state = 'passed', criteria = {passed: 3, total: 3}} = {}) {
  const batch = `20261110-040000-${String(++batches).padStart(4, '0')}`;
  const folder = join(f.ports.env.PDD_STATE_DIR, 'batches', batch);
  const capture = captureSource(f.run.root, {tests: [TEST], appMap: null});
  mkdirSync(folder, {recursive: true});
  writeFileSync(join(folder, 'batch.json'), JSON.stringify({
    version: 1, batch, root: f.run.root, created_at: new Date(f.clock).toISOString(), intent: 'check',
    source_sha256: capture.sha256, files: capture.files.map(file => file.path), contract_snapshots: capture.stories,
    rows: [{test: TEST, state, request_ids: []}],
  }));
  writeFileSync(join(folder, 'summary.json'), JSON.stringify(renderJson({
    batch, repo: f.run.root, sourceSha256: capture.sha256,
    exitCode: state === 'passed' ? 0 : 1,
    rows: [{test: TEST, story: STORY, state, criteria}],
    summaryLine: 'synthetic check',
  })));
  return batch;
}

async function createAutoFixture(t, {workflow = 'bug'} = {}) {
  const f = await automaticFixture(t);
  assert.equal((await f.begin({name: workflow})).exitCode, 0);
  f.run = f.record();
  f.ports.env.PDD_STATE_DIR = join(f.state, 'runtime');
  f.automaticPorts.env.PDD_STATE_DIR = f.ports.env.PDD_STATE_DIR;
  f.done = async (step, extra = {}) => {
    f.tick();
    const result = await stepDone({step, summary: `synthetic ${step}`, cwd: f.run.root, ...extra}, f.automaticPorts);
    assert.equal(result.exitCode, 0, result.message);
    return result;
  };
  return f;
}

test('#3145 auto mode auto-approves Story, PR 1 and PR 2 gates when required checks pass and fresh draft review has no must-fix', async t => {
  const f = await createAutoFixture(t, {workflow: 'bug'});
  await f.done('reproduce', {summary: 'Verdict: the bug is in the PROMPT (its check fails on the issue case).\nSynthetic reproduce'});
  const harbor = join(packageRoot, 'test/fixtures/harbor');
  for (const path of [STORY, TEST, PROMPT]) {
    mkdirSync(join(f.run.root, path.slice(0, path.lastIndexOf('/'))), {recursive: true});
    cpSync(join(harbor, path), join(f.run.root, path));
  }
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Synthetic Story and prompt');
  writeFileSync(join(f.run.runDir, 'story-review.md'), 'Review: no must-fix\n');

  const storyDone = await f.done('prompt-story');
  assert.match(storyDone.message, /Autopilot auto-approved the story gate in auto mode/);
  const afterStory = f.record();
  assert.equal(afterStory.area, 1, 'Story gate should auto-advance to prompt-pr area without person wait');
  assert.equal(afterStory.gate, null);
  assert.equal(afterStory.through, 'code');
  assert.ok(afterStory.storyApproval?.fingerprint);
  const storyDecision = afterStory.decisions.find(d => d.stage === 'story' && d.decision === 'approve');
  assert.ok(storyDecision);
  assert.equal(storyDecision.via, 'autopilot-auto');
  assert.equal(storyDecision.evidence.route, 'autopilot-auto');
  assert.equal(storyDecision.evidence.basis.mode, 'auto');
  assert.ok(storyDecision.evidence.basis.checks.includes('story-contract'));
  assert.ok(storyDecision.evidence.basis.checks.includes('scenario-tests'));
  assert.ok(storyDecision.evidence.basis.checks.includes('fresh-draft-review: no must-fix'));
  assert.equal(readPromptApprovals({commonDir: f.run.commonDir}, f.automaticPorts).some(r => r.route === 'autopilot-auto' && r.basis?.mode === 'auto'), true);

  const batch = saveCheck(f);
  await f.done('try', {skipped: 'Autopilot optional default'});
  const checkDone = await f.done('check', {summary: 'Prompt tests: 1 of 1 pass'});
  assert.equal(f.prs.length, 1, checkDone.message);
  const afterPr1 = f.record();
  assert.equal(afterPr1.area, 2, 'PR 1 and ask-code should auto-advance to code area in auto mode');
  assert.equal(afterPr1.gate, null);
  const pr1Decision = afterPr1.decisions.find(d => d.stage === 'prompt-pr' && d.decision === 'approve');
  assert.ok(pr1Decision);
  assert.equal(pr1Decision.evidence.basis.mode, 'auto');
  assert.deepEqual(pr1Decision.evidence.basis.batches, [batch]);
  assert.ok(pr1Decision.evidence.basis.checks.includes('prompt-tests'));
  assert.ok(pr1Decision.evidence.basis.checks.includes('fresh-draft-review: no must-fix'));

  const records = approvalRecords(afterPr1);
  assert.ok(records.some(r => r.route === 'autopilot-auto' && r.basis?.mode === 'auto'));
  assert.match(f.prs[0].body, /Approved by Autopilot \(no person asked\):/);
  assert.match(f.prs[0].body, /mode `"auto"`/);
  assert.match(f.prs[0].body, /checks `"/);

  writeFileSync(join(f.run.root, 'order.mjs'), 'export const order = 1;\n');
  f.git(f.run.root, 'add', 'order.mjs');
  f.git(f.run.root, 'commit', '-qm', 'Synthetic code implementation');
  await f.done('build');
  await f.done('verify');
  writeFileSync(join(f.run.runDir, 'replay-evidence.json'), JSON.stringify({
    schema_version: 'pdd.replay-evidence.v1',
    run_id: f.run.runId,
    source: {kind: 'git-content-v1', sha256: 'a'.repeat(64)},
    formal: {result: 'not_applicable', scope: 'Constant', reason: 'No separate rules', control_outcome: 'not_run'},
  }));
  await f.done('formal');
  writeFileSync(join(f.run.runDir, 'review.md'), 'Review: no must-fix\n');
  await f.done('review');
  assert.equal(f.prs.length, 2);
  const afterPr2 = f.record();
  const pr2Decision = afterPr2.decisions.find(d => d.stage === 'code' && d.decision === 'approve');
  assert.ok(pr2Decision);
  assert.equal(pr2Decision.via, 'autopilot-auto');
  assert.equal(pr2Decision.evidence.route, 'autopilot-auto');
  assert.equal(pr2Decision.evidence.basis.mode, 'auto');
  assert.ok(pr2Decision.evidence.basis.checks.includes('verify'));
  assert.ok(pr2Decision.evidence.basis.checks.includes('code-review: no must-fix'));

  const statusJson = JSON.parse((await runStatus({ref: '17', cwd: f.source, json: true}, f.automaticPorts)).message).runs[0];
  assert.ok(Array.isArray(statusJson.autoApprovals) && statusJson.autoApprovals.length >= 3);
});

test('#3145 auto mode auto-approves small-change plan and PR gates with mode and checks recorded', async t => {
  const f = await createAutoFixture(t, {workflow: 'small-change'});
  writeFileSync(join(f.run.root, 'README.md'), 'Updated guide.\n');
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Synthetic small-change scope');
  writeFileSync(join(f.run.runDir, 'plan-review.md'), 'Review: no must-fix\n');

  const scopeDone = await f.done('scope');
  assert.match(scopeDone.message, /Autopilot auto-approved the plan gate in auto mode/);
  const afterPlan = f.record();
  assert.equal(afterPlan.area, 1);
  assert.equal(afterPlan.gate, null);
  const planDecision = afterPlan.decisions.find(d => d.stage === 'plan' && d.decision === 'approve');
  assert.ok(planDecision);
  assert.equal(planDecision.via, 'autopilot-auto');
  assert.equal(planDecision.evidence.route, 'autopilot-auto');
  assert.equal(planDecision.evidence.basis.mode, 'auto');
  assert.ok(planDecision.evidence.basis.checks.includes('fresh-draft-review: no must-fix'));

  await f.done('change');
  await f.done('verify');
  writeFileSync(join(f.run.runDir, 'replay-evidence.json'), JSON.stringify({
    schema_version: 'pdd.replay-evidence.v1',
    run_id: f.run.runId,
    source: {kind: 'git-content-v1', sha256: 'a'.repeat(64)},
    formal: {result: 'not_applicable', scope: 'docs', reason: 'Docs only', control_outcome: 'not_run'},
  }));
  await f.done('formal');
  assert.equal(f.prs.length, 1);
  const afterPr = f.record();
  const prDecision = afterPr.decisions.find(d => d.stage === 'build' && d.decision === 'approve');
  assert.ok(prDecision);
  assert.equal(prDecision.via, 'autopilot-auto');
  assert.equal(prDecision.evidence.route, 'autopilot-auto');
  assert.equal(prDecision.evidence.basis.mode, 'auto');
  assert.ok(prDecision.evidence.basis.checks.includes('verify'));
  assert.ok(prDecision.evidence.basis.checks.includes('fresh-draft-review: no must-fix'));
});

test('#3145 fresh draft review with must-fix holds auto-approval until repaired', async t => {
  const f = await createAutoFixture(t, {workflow: 'bug'});
  await f.done('reproduce');
  const harbor = join(packageRoot, 'test/fixtures/harbor');
  for (const path of [STORY, TEST, PROMPT]) {
    mkdirSync(join(f.run.root, path.slice(0, path.lastIndexOf('/'))), {recursive: true});
    cpSync(join(harbor, path), join(f.run.root, path));
  }
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Synthetic Story with must-fix');
  writeFileSync(join(f.run.runDir, 'story-review.md'), 'Review: 2 must-fix\n- Missing edge case\n');

  const heldDone = await f.done('prompt-story');
  assert.match(heldDone.message, /did not auto-approve the story gate: fresh Story draft review has 2 must-fix/);
  const held = f.record();
  assert.equal(held.area, 0);
  assert.equal(held.gate?.kind, 'approve');
  assert.equal(held.gate?.automaticHold, 'fresh Story draft review has 2 must-fix');
  assert.equal(held.decisions.length, 0);

  const statusText = (await runStatus({ref: '17', cwd: f.source}, f.automaticPorts)).message;
  assert.match(statusText, /story gate waits: fresh Story draft review has 2 must-fix/);

  writeFileSync(join(f.run.runDir, 'story-review.md'), 'Review: no must-fix\n');
  const advanced = await advanceAutomaticPr1({
    ref: '17', cwd: f.source, packageRoot,
    coordinatorId: held.automaticOrigin.coordinatorId, machine: held.automaticOrigin.machine,
  }, f.automaticPorts);
  assert.equal(advanced.exitCode, 0, advanced.message);
  const after = f.record();
  assert.equal(after.area, 1);
  assert.equal(after.gate, null);
  assert.equal(after.decisions[0]?.via, 'autopilot-auto');
  assert.equal(after.decisions[0]?.evidence?.route, 'autopilot-auto');
  assert.equal(after.decisions[0]?.evidence?.basis?.mode, 'auto');
});

test('#3145 user-facing contract change asks one person question and holds auto-approval', async t => {
  const f = await createAutoFixture(t, {workflow: 'feature'});
  await f.done('understand');
  await f.done('visual', {skipped: 'Autopilot optional default'});
  const harbor = join(packageRoot, 'test/fixtures/harbor');
  for (const path of [STORY, TEST, PROMPT]) {
    mkdirSync(join(f.run.root, path.slice(0, path.lastIndexOf('/'))), {recursive: true});
    cpSync(join(harbor, path), join(f.run.root, path));
  }
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Synthetic Story with contract question');
  writeFileSync(join(f.run.runDir, 'story-review.md'), 'Review: no must-fix\nContract change question: Should the public CLI flag be --order or --place-order?\n');

  const result = await f.done('prompt-story');
  assert.match(result.message, /stops for one person question \(user-facing contract change\)/);
  const held = f.record();
  assert.equal(held.area, 0);
  assert.equal(held.gate?.kind, 'approve');
  assert.equal(held.question?.kind, 'contract-change');
  assert.match(held.question?.text ?? '', /--order or --place-order/);
  assert.equal(held.decisions.length, 0);
});

test('#3145 manual/observe mode and strict_approvals keep person gate behavior', async t => {
  for (const config of [{autopilot: {mode: 'observe'}}, {autopilot: {mode: 'auto'}, strict_approvals: true}]) {
    const f = await createAutoFixture(t, {workflow: 'bug'});
    writeFileSync(join(f.source, 'pdd.json'), JSON.stringify(config));
    await f.done('reproduce');
    const harbor = join(packageRoot, 'test/fixtures/harbor');
    for (const path of [STORY, TEST, PROMPT]) {
      mkdirSync(join(f.run.root, path.slice(0, path.lastIndexOf('/'))), {recursive: true});
      cpSync(join(harbor, path), join(f.run.root, path));
    }
    f.git(f.run.root, 'add', '.');
    f.git(f.run.root, 'commit', '-qm', 'Synthetic Story');
    writeFileSync(join(f.run.runDir, 'story-review.md'), 'Review: no must-fix\n');

    await f.done('prompt-story');
    const held = f.record();
    assert.equal(held.area, 0);
    assert.equal(held.gate?.kind, 'approve');
    assert.equal(held.decisions.length, 0);

    // Restoring non-strict auto mode allows Autopilot to auto-approve the held gate.
    writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto'}}));
    const advanced = await advanceAutomaticPr1({
      ref: '17', cwd: f.source, packageRoot,
      coordinatorId: held.automaticOrigin.coordinatorId, machine: held.automaticOrigin.machine,
    }, f.automaticPorts);
    assert.equal(advanced.exitCode, 0, advanced.message);
    assert.equal(f.record().area, 1);
    assert.equal(f.record().decisions[0]?.via, 'autopilot-auto');
  }
});
