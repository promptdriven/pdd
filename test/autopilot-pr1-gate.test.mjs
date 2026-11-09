import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {cpSync, mkdirSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {createHash} from 'node:crypto';
import {automaticFixture} from './helpers/autopilot-run-base-fixture.mjs';
import {packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {approveRun, runStatus, stepDone, cancelRun, askPerson} from '../src/workflow-runner.mjs';
import {tickAutopilot} from '../src/autopilot-launcher.mjs';
import {captureSource} from '../src/runtime-preflight.mjs';
import {renderJson} from '../src/runtime-output.mjs';
import {readPromptApprovals} from '../src/approval-policy.mjs';

const STORY = 'user_stories/place-order.md', TEST = 'tests/place-order.json', PROMPT = 'prompts/place_order.prompt.md';
let batches = 0;
function saveCheck(f, {state = 'passed', criteria = {passed: 3, total: 3}} = {}) {
  const batch = `20261027-170000-${String(++batches).padStart(4, '0')}`, folder = join(f.ports.env.PDD_STATE_DIR, 'batches', batch);
  const capture = captureSource(f.run.root, {tests: [TEST], appMap: null});
  mkdirSync(folder, {recursive: true});
  writeFileSync(join(folder, 'batch.json'), JSON.stringify({version: 1, batch, root: f.run.root, created_at: new Date(f.clock).toISOString(), intent: 'check',
    source_sha256: capture.sha256, files: capture.files.map(file => file.path), contract_snapshots: capture.stories, rows: [{test: TEST, state, request_ids: []}]}));
  writeFileSync(join(folder, 'summary.json'), JSON.stringify(renderJson({batch, repo: f.run.root, sourceSha256: capture.sha256,
    exitCode: state === 'passed' ? 0 : 1, rows: [{test: TEST, story: STORY, state, criteria}], summaryLine: 'synthetic check'})));
  return batch;
}
async function setup(t) {
  const f = await automaticFixture(t);
  assert.equal((await f.begin()).exitCode, 0);
  f.run = f.record();
  f.ports.env.PDD_STATE_DIR = join(f.state, 'runtime');
  f.automaticPorts.env.PDD_STATE_DIR = f.ports.env.PDD_STATE_DIR;
  f.done = async (step, extra = {}) => {
    f.tick();
    const result = await stepDone({step, summary: `synthetic ${step}`, cwd: f.run.root, ...extra}, f.automaticPorts);
    assert.equal(result.exitCode, 0, result.message);
    return result;
  };
  await f.done('reproduce');
  const harbor = join(packageRoot, 'test/fixtures/harbor');
  for (const path of [STORY, TEST, PROMPT]) {
    mkdirSync(join(f.run.root, path.slice(0, path.lastIndexOf('/'))), {recursive: true});
    cpSync(join(harbor, path), join(f.run.root, path));
  }
  f.git(f.run.root, 'add', '.'); f.git(f.run.root, 'commit', '-qm', 'Synthetic Story');
  await f.done('prompt-story');
  const approved = await approveRun({ref: '17', cwd: f.run.root, packageRoot}, f.automaticPorts);
  assert.equal(approved.exitCode, 0, approved.message);
  await f.done('check');
  await f.done('try', {skipped: 'Autopilot optional default'});
  assert.equal(f.record().gate.kind, 'approve-pr');
  const id = createHash('sha256').update(f.source).digest('hex').slice(0, 20);
  f.stateFile = join(f.automaticPorts.autopilotStateRoot, `${id}.json`);
  const state = JSON.parse(readFileSync(f.stateFile, 'utf8'));
  Object.assign(state, {stateFile: f.stateFile, defaultBranch: 'main', baseBranch: 'main', packageRoot,
    agent: {id: 'codex', kind: 'codex', command: 'codex'}, environment: f.automaticPorts.env, recipeDelivered: true});
  writeFileSync(f.stateFile, JSON.stringify(state));
  f.warnings = []; f.intakes = 0;
  f.tickPorts = {...healthyMachine, ...f.automaticPorts, checkCapacityPorts: isolatedCheckCapacity(f.base),
    run: async (file, args, opts) => ({code: 0, ...await f.automaticPorts.execFile(file, args, opts)}),
    warn: text => f.warnings.push(text), sendDigest: async () => ({exitCode: 0}),
    reconcileDependencyIntake: async () => {f.intakes++; f.onIntake?.(); return {eligible: [], queued: [], skipped: []};},
    queryIssues: async () => ({status: 304, issues: []}),
  };
  f.scan = () => tickAutopilot(f.stateFile, f.tickPorts);
  f.status = async () => JSON.parse((await runStatus({ref: '17', cwd: f.source, json: true}, f.automaticPorts)).message).runs[0];
  return f;
}

test('#3099 next tick opens automatic PR 1 before dependency review, using full-pass evidence once', async t => {
  const f = await setup(t), batch = saveCheck(f), before = f.record();
  const calls = f.herdr.calls.length;
  f.onIntake = () => assert.equal(f.prs.length, 1, 'automatic PR 1 must open before dependency intake');
  const result = await f.scan();
  assert.equal(f.prs.length, 1, `${result.message}\n${f.warnings.join('\n')}`);
  assert.equal(f.intakes, 1);
  const after = f.record(), decision = after.decisions.at(-1);
  assert.equal(decision.via, 'automatic-check-pass'); assert.equal(decision.evidence.words, null);
  assert.equal(decision.evidence.basis.origin, 'automatic');
  assert.deepEqual(decision.evidence.basis.automaticOrigin, before.automaticOrigin);
  assert.deepEqual(decision.evidence.basis.batches, [batch]);
  assert.equal(decision.evidence.basis.storyEvidenceId, before.decisions.at(-1).storyCoverage.evidenceId);
  assert.equal(decision.evidence.basis.headSha, f.prs[0].headRefOid);
  assert.equal(after.gate.kind, 'ask-code'); assert.equal(after.area, before.area);
  assert.deepEqual(after.done, before.done); assert.equal(after.question, before.question);
  assert.equal(f.herdr.calls.slice(calls).filter(args => args[0] === 'pane' && args[1] === 'run' || args[0] === 'agent' && args[1] === 'prompt').length, 0, 'the native decision needs no AI turn');
  const decisions = after.decisions.length, pushes = f.pushes.length;
  await f.scan();
  assert.equal(f.prs.length, 1); assert.equal(f.record().decisions.length, decisions); assert.equal(f.pushes.length, pushes);
});

for (const kind of ['failed', 'partial', 'no-verdict', 'missing', 'stale', 'Story', 'expected', 'strict', 'scope', 'custody']) {
  test(`#3099 ${kind} holds automatic PR 1 with a status reason`, async t => {
    const f = await setup(t), before = f.record();
    if (kind !== 'missing') saveCheck(f, kind === 'failed' ? {state: 'failed'} : kind === 'partial' ? {criteria: {passed: 2, total: 3}} : kind === 'no-verdict' ? {state: 'unknown', criteria: null} : {});
    if (kind === 'stale') writeFileSync(join(f.run.root, PROMPT), readFileSync(join(f.run.root, PROMPT), 'utf8').replace('Return the order:', 'Return the priced order:'));
    if (kind === 'Story') writeFileSync(join(f.run.root, STORY), readFileSync(join(f.run.root, STORY), 'utf8') + '\nAn added product rule.\n');
    if (kind === 'expected') {const file = join(f.run.root, TEST), doc = JSON.parse(readFileSync(file)); doc.steps[0].checks[0].value = 'changed expectation'; writeFileSync(file, JSON.stringify(doc));}
    if (kind === 'strict') writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto'}, strict_approvals: true}));
    if (kind === 'scope') {const state = JSON.parse(readFileSync(f.stateFile)); delete state.startAction; writeFileSync(f.stateFile, JSON.stringify(state));}
    if (kind === 'custody') {const file = join(f.base, 'reader.json'), doc = JSON.parse(readFileSync(file)); doc.comments = []; writeFileSync(file, JSON.stringify(doc));}
    await f.scan();
    const after = f.record();
    assert.equal(f.prs.length, 0); assert.equal(f.pushes.length, 0); assert.deepEqual(after.decisions, before.decisions);
    assert.equal(after.gate.kind, 'approve-pr');
    assert.ok(after.gate.automaticHold, f.warnings.join('\n'));
    const expected = kind === 'strict' ? /strict/ : kind === 'Story' || kind === 'expected' ? /Story/ : kind === 'scope' ? /scope/ : kind === 'custody' ? /ownership/ : /check/;
    assert.match((await f.status()).words, expected);
    if (kind === 'Story' || kind === 'expected') assert.ok(after.gate.storyChanges.length);
  });
}

for (const kind of ['prompt-repair', 'no-coverage', 'observe', 'off', 'question', 'unfinished', 'foreign-owner']) {
  test(`#3099 gate scope: ${kind}`, async t => {
    const f = await setup(t);
    if (kind === 'prompt-repair') writeFileSync(join(f.run.root, PROMPT), readFileSync(join(f.run.root, PROMPT), 'utf8').replace('Return the order:', 'Return the priced order:'));
    saveCheck(f);
    const run = f.record(), before = run.decisions.length;
    if (kind === 'no-coverage') for (const decision of run.decisions) delete decision.storyCoverage;
    if (kind === 'question') run.question = {text: 'Which product scope?', at: f.clock};
    if (kind === 'unfinished') delete run.done.check;
    if (kind === 'foreign-owner') run.automaticOrigin.coordinatorId = 'another-coordinator';
    writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
    if (kind === 'observe' || kind === 'off') writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: kind}}));
    await f.scan();
    assert.equal(f.prs.length, kind === 'prompt-repair' ? 1 : 0, f.warnings.join('\n'));
    if (kind !== 'prompt-repair') {assert.equal(f.pushes.length, 0); assert.equal(f.record().decisions.length, before);}
    if (kind === 'no-coverage') assert.match((await f.status()).words, /Story.*coverage/);
  });
}

for (const kind of ['strict', 'scope', 'custody', 'Story']) test(`#3099 publication revalidates ${kind} after preparation`, async t => {
  const f = await setup(t);
  // A checked draft makes preparation commit the approval metadata.
  const path = join(f.run.root, PROMPT);
  writeFileSync(path, readFileSync(path, 'utf8').replace(/"status":\s*"approved"/, '"status":"draft"'));
  f.git(f.run.root, 'add', '.'); f.git(f.run.root, 'commit', '-qm', 'Synthetic checked draft');
  saveCheck(f);
  const original = f.tickPorts.execFile;
  let changed = false;
  f.tickPorts.execFile = async (file, args, opts) => {
    const result = await original(file, args, opts);
    if (!changed && file === 'git' && args[0] === 'commit') {
      changed = true;
      if (kind === 'strict') writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto'}, strict_approvals: true}));
      if (kind === 'scope') {const state = JSON.parse(readFileSync(f.stateFile)); delete state.startAction; writeFileSync(f.stateFile, JSON.stringify(state));}
      if (kind === 'custody') {const file = join(f.base, 'reader.json'), doc = JSON.parse(readFileSync(file)); doc.comments = []; writeFileSync(file, JSON.stringify(doc));}
      if (kind === 'Story') writeFileSync(join(f.run.root, STORY), readFileSync(join(f.run.root, STORY), 'utf8') + '\nChanged during preparation.\n');
    }
    return result;
  };
  const decisions = f.record().decisions.length;
  await f.scan();
  assert.equal(changed, true, 'the control must reach publication preparation');
  assert.equal(f.prs.length, 0); assert.equal(f.pushes.length, 0); assert.equal(f.record().decisions.length, decisions);
});

for (const boundary of ['preparation', 'pre-push', 'post-push'])
for (const kind of ['cancelled', 'question']) test(`#3099 ${kind} during ${boundary} stops further publication`, async t => {
  const f = await setup(t);
  const path = join(f.run.root, PROMPT);
  writeFileSync(path, readFileSync(path, 'utf8').replace(/"status":\s*"approved"/, '"status":"draft"'));
  f.git(f.run.root, 'add', '.'); f.git(f.run.root, 'commit', '-qm', 'Synthetic checked draft');
  saveCheck(f);
  const before = f.record(), original = f.tickPorts.execFile;
  const approvals = () => readPromptApprovals({commonDir: before.commonDir}, f.automaticPorts);
  const beforeApprovals = approvals(), checkedPrompt = readFileSync(path, 'utf8');
  const command = {preparation: 'commit', 'pre-push': 'ls-remote', 'post-push': 'push'}[boundary];
  let changed = false, blocker, blockerApprovals;
  f.tickPorts.execFile = async (file, args, opts) => {
    const result = await original(file, args, opts);
    if (!changed && file === 'git' && args[0] === command) {
      changed = true; f.tick();
      const action = kind === 'cancelled'
        ? await cancelRun({ref: '17', cwd: f.source}, f.automaticPorts)
        : await askPerson({text: 'Which product scope?', cwd: f.run.root}, f.automaticPorts);
      assert.equal(action.exitCode, 0, action.message);
      blocker = f.record();
      blockerApprovals = approvals();
    }
    return result;
  };
  await f.scan();
  assert.equal(changed, true, 'the race must reach its publication boundary');
  assert.equal(f.prs.length, 0, 'a saved blocker must prevent PR creation');
  assert.equal(f.pushes.length, boundary === 'post-push' ? 1 : 0, 'a saved blocker must prevent further pushes');
  const after = f.record();
  if (boundary === 'preparation') {
    assert.deepEqual(blocker.decisions, before.decisions);
    assert.deepEqual(blockerApprovals, beforeApprovals);
    assert.equal(readFileSync(path, 'utf8'), checkedPrompt, 'unrecorded prompt approval edits must be restored');
  }
  assert.deepEqual(approvals(), blockerApprovals);
  assert.deepEqual(after.decisions, blocker.decisions, 'a saved blocker must prevent further automatic approval');
  assert.deepEqual(after.approvalRecord, blocker.approvalRecord);
  assert.equal(after.state, blocker.state);
  assert.deepEqual(after.cancelled, blocker.cancelled);
  assert.deepEqual(after.question, blocker.question);
  assert.deepEqual(after.gate, blocker.gate);
});
