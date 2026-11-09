import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as nativeFs from 'node:fs';
import {cpSync, mkdirSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {hostname} from 'node:os';
import {createHash, randomUUID} from 'node:crypto';
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
async function setup(t, {registered = false, beforeApproval} = {}) {
  const f = await automaticFixture(t);
  assert.equal((await f.begin()).exitCode, 0);
  f.run = f.record();
  f.ports.env.PDD_STATE_DIR = join(f.state, 'runtime');
  f.automaticPorts.env.PDD_STATE_DIR = f.ports.env.PDD_STATE_DIR;
  f.done = async (step, extra = {}) => {
    f.tick();
    if (registered) await runStatus({ref: '17', cwd: f.source}, f.automaticPorts);
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
  beforeApproval?.(f);
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
  f.herdr.idle(); // The saved gate follows the worker's completed turn.
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
    if (kind === 'no-coverage') {
      for (const decision of run.decisions) { delete decision.storyCoverage; delete decision.storyContract; delete decision.storyPaths; }
      for (const step of Object.values(run.done)) delete step.worktreeSha256;
    }
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

// Synthetic saved records use only shapes from the pre-card workflow. They do
// not copy operational run files or ask the CLI to approve a prompt.
function preCardRecord(f, {contract = false} = {}) {
  const run = f.record(), decision = run.decisions.at(-1);
  const expected = structuredClone(decision.storyCoverage);
  delete decision.storyCoverage;
  if (!contract) { delete decision.storyContract; delete decision.storyPaths; }
  delete run.storyApproval;
  writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
  return {run, decision, expected};
}

test('#3103 derives missing automatic Story coverage from its recorded contract once', async t => {
  const f = await setup(t), {run, decision, expected} = preCardRecord(f, {contract: true});
  const journal = readPromptApprovals({commonDir: run.commonDir}, f.automaticPorts);
  // First tick has no check. It may recover coverage, but cannot publish.
  await f.scan();
  const coverage = f.record().storyApproval;
  assert.ok(coverage?.fingerprint, 'recorded automatic Story approval must recover coverage');
  assert.deepEqual(coverage.fingerprint, expected.fingerprint);
  assert.deepEqual(coverage.prompts, [PROMPT]);
  assert.equal(coverage.evidenceId, decision.evidence.id);
  assert.equal(coverage.gateId, decision.gateId);
  assert.equal(coverage.at, decision.at);
  assert.equal(coverage.source, 'derived from the recorded approval');
  assert.deepEqual(coverage.derivedFrom, {storyContract: decision.storyContract});
  assert.equal(f.prs.length, 0); assert.equal(f.pushes.length, 0);
  assert.deepEqual(f.record().decisions, run.decisions);
  assert.deepEqual(readPromptApprovals({commonDir: run.commonDir}, f.automaticPorts), journal);
  // A prompt-only repair and fresh full pass use that same approval.
  writeFileSync(join(run.root, PROMPT), readFileSync(join(run.root, PROMPT), 'utf8').replace('Return the order:', 'Return the priced order:'));
  const batch = saveCheck(f);
  await f.scan();
  assert.equal(f.prs.length, 1, f.warnings.join('\n'));
  assert.deepEqual(f.record().storyApproval, coverage);
  assert.deepEqual(f.record().decisions[0], decision);
  assert.equal(f.record().decisions.at(-1).evidence.basis.storyEvidenceId, decision.evidence.id);
  assert.deepEqual(f.record().decisions.at(-1).evidence.basis.batches, [batch]);
  const decisions = f.record().decisions.length, pushes = f.pushes.length;
  await f.scan();
  assert.equal(f.record().decisions.length, decisions); assert.equal(f.pushes.length, pushes);
});

for (const kind of ['Story', 'plan', 'expected', 'prompt-list']) test(`#3103 pre-card ${kind} change reopens Story approval despite a full check pass`, async t => {
  const f = await setup(t), {run} = preCardRecord(f, {contract: true});
  if (kind === 'Story') writeFileSync(join(run.root, STORY), readFileSync(join(run.root, STORY), 'utf8') + '\nAdded product rule.\n');
  if (kind === 'plan') writeFileSync(join(run.root, 'user_stories/PLAN.md'), 'New scope\n');
  if (kind === 'expected') {const doc = JSON.parse(readFileSync(join(run.root, TEST))); doc.steps[0].checks[0].value = 950; writeFileSync(join(run.root, TEST), JSON.stringify(doc));}
  if (kind === 'prompt-list') cpSync(join(run.root, PROMPT), join(run.root, 'prompts/another.prompt.md'));
  saveCheck(f);
  await f.scan();
  const after = f.record();
  assert.ok(after.gate.storyChanges?.length, 'a changed pre-card Story must reopen its gate');
  assert.notEqual(after.gate.id, run.gate.id);
  assert.ok(after.gate.storySnapshot);
  assert.equal(after.storyApproval, undefined);
  assert.deepEqual(after.decisions, run.decisions);
  assert.equal(f.prs.length, 0); assert.equal(f.pushes.length, 0);
  await f.scan();
  assert.equal(f.record().gate.id, after.gate.id);
  assert.equal(f.prs.length, 0);
});

test('#3103 coverage recovery requires the recorded approval, source and current authority', async t => {
  for (const kind of ['journal', 'wrong-stage', 'no-contract', 'git-unavailable', 'strict', 'scope', 'custody']) await t.test(kind, async t => {
    const f = await setup(t), {run, decision} = preCardRecord(f, {contract: kind !== 'no-contract'});
    if (kind === 'journal') writeFileSync(join(run.commonDir, 'pdd/approvals.json'), JSON.stringify({v: 1, approvals: []}));
    if (kind === 'wrong-stage') decision.stage = 'prompt-pr';
    writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
    if (kind === 'git-unavailable') {
      const original = f.tickPorts.execFile;
      let inventories = 0;
      f.tickPorts.execFile = (file, args, opts) => file === 'git' && args[0] === 'ls-files' && ++inventories === 2
        ? Promise.resolve({code: 1, stdout: '', stderr: 'synthetic unavailable tree'}) : original(file, args, opts);
    }
    if (kind === 'strict') writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto'}, strict_approvals: true}));
    if (kind === 'scope') {const state = JSON.parse(readFileSync(f.stateFile)); delete state.startAction; writeFileSync(f.stateFile, JSON.stringify(state));}
    if (kind === 'custody') {const file = join(f.base, 'reader.json'), doc = JSON.parse(readFileSync(file)); doc.comments = []; writeFileSync(file, JSON.stringify(doc));}
    saveCheck(f);
    await f.scan();
    assert.equal(f.record().storyApproval, undefined);
    assert.deepEqual(f.record().decisions, run.decisions);
    assert.ok(f.record().gate.automaticHold);
    assert.equal(f.prs.length, 0); assert.equal(f.pushes.length, 0);
  });
});

test('#3103 repair 1 an earlier step cannot cover a different Story approved later', async t => {
  let storyA;
  const f = await setup(t, {beforeApproval(f) {
    storyA = readFileSync(join(f.run.root, STORY), 'utf8');
    writeFileSync(join(f.run.root, STORY), storyA + '\nStory B is the scope approved at the terminal.\n');
  }});
  const {run} = preCardRecord(f);
  const journal = readPromptApprovals({commonDir: run.commonDir}, f.automaticPorts);
  // The source hash belongs to A. The unchanged decision and journal approved B.
  assert.ok(run.done['prompt-story'].worktreeSha256);
  writeFileSync(join(run.root, STORY), storyA);
  saveCheck(f);
  await f.scan();
  assert.equal(f.record().storyApproval, undefined, 'an earlier step must not supply approval-bound Story coverage');
  await f.scan();
  assert.equal(f.record().gate.kind, 'approve-pr');
  assert.ok(f.record().gate.automaticHold);
  assert.deepEqual(f.record().decisions, run.decisions);
  assert.deepEqual(readPromptApprovals({commonDir: run.commonDir}, f.automaticPorts), journal);
  assert.equal(f.prs.length, 0); assert.equal(f.pushes.length, 0);
});

for (const kind of ['Story', 'expected', 'prompt-list']) test(`#3103 repair 1 a ${kind} edit during contract recovery saves no coverage`, async t => {
  const f = await setup(t);
  preCardRecord(f, {contract: true});
  await f.scan();
  assert.ok(f.record().storyApproval?.fingerprint, 'contract-backed recovery must work before testing its concurrent edit');
  const {run} = preCardRecord(f, {contract: true}), original = f.tickPorts.execFile;
  const journal = readPromptApprovals({commonDir: run.commonDir}, f.automaticPorts);
  let inventories = 0, changed = false;
  f.tickPorts.execFile = async (file, args, opts) => {
    const result = await original(file, args, opts);
    // Gate prompt inventory, contract inventory, then fingerprint inventory.
    // The old implementation has already read the approved contract here.
    if (file === 'git' && args[0] === 'ls-files' && ++inventories === 3) {
      changed = true;
      if (kind === 'Story') writeFileSync(join(run.root, STORY), readFileSync(join(run.root, STORY), 'utf8') + '\nChanged during recovery.\n');
      if (kind === 'expected') {const doc = JSON.parse(readFileSync(join(run.root, TEST))); doc.steps[0].checks[0].value = 950; writeFileSync(join(run.root, TEST), JSON.stringify(doc));}
      if (kind === 'prompt-list') cpSync(join(run.root, PROMPT), join(run.root, 'prompts/another.prompt.md'));
      // A current full pass cannot authorize the edit.
      saveCheck(f);
    }
    return result;
  };
  saveCheck(f);
  await f.scan();
  assert.equal(changed, true);
  assert.equal(f.record().storyApproval, undefined, 'a concurrent contract edit must not become approved Story coverage');
  assert.ok(f.record().gate.storyChanges?.length);
  await f.scan();
  assert.equal(f.record().storyApproval, undefined);
  assert.equal(f.record().gate.kind, 'approve-pr');
  assert.deepEqual(f.record().decisions, run.decisions);
  assert.deepEqual(readPromptApprovals({commonDir: run.commonDir}, f.automaticPorts), journal);
  assert.equal(f.prs.length, 0); assert.equal(f.pushes.length, 0);
});

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

for (const kind of ['cancelled', 'question']) test(`#3099 ${kind} during journal contention prevents durable approval`, async t => {
  const f = await setup(t), path = join(f.run.root, PROMPT);
  const checkedPrompt = readFileSync(path, 'utf8').replace(/"status":\s*"approved"/, '"status":"draft"');
  writeFileSync(path, checkedPrompt);
  f.git(f.run.root, 'add', '.'); f.git(f.run.root, 'commit', '-qm', 'Synthetic checked draft');
  saveCheck(f);
  const before = f.record(), dir = join(before.commonDir, 'pdd'), journal = join(dir, 'approvals.json');
  const initialJournal = readFileSync(journal, 'utf8'), lock = join(dir, 'approvals.lock'), token = randomUUID();
  const holder = join(lock, `owner-${token}.json`);
  mkdirSync(lock);
  writeFileSync(holder, JSON.stringify({pid: process.pid, hostname: hostname(), token}));
  const releaseHolder = () => {
    if (nativeFs.existsSync(holder)) nativeFs.unlinkSync(holder);
    if (nativeFs.existsSync(lock) && !nativeFs.readdirSync(lock).length) nativeFs.rmdirSync(lock);
  };
  t.after(releaseHolder);
  let contended = false, blockerTask, blockerError, blocker, blockerJournal;
  // Observe a real live owner inspection. Every filesystem operation still uses
  // native fs. The public blocker runs while acquisition awaits its next retry.
  f.tickPorts.fs = {...nativeFs, readFileSync(file, ...args) {
    const value = nativeFs.readFileSync(file, ...args);
    if (file === holder && !contended) {
      contended = true;
      blockerTask = Promise.resolve().then(async () => {
        try {
          f.tick();
          const action = kind === 'cancelled'
            ? await cancelRun({ref: '17', cwd: f.source}, f.automaticPorts)
            : await askPerson({text: 'Which product scope?', cwd: f.run.root}, f.automaticPorts);
          assert.equal(action.exitCode, 0, action.message);
          blocker = f.record();
          blockerJournal = readFileSync(journal, 'utf8');
        } finally { releaseHolder(); }
      }).catch(error => { blockerError = error; });
    }
    return value;
  }};
  await f.scan();
  await blockerTask;
  if (blockerError) throw blockerError;
  assert.equal(contended, true, 'the race must inspect the real journal holder');
  if (kind === 'cancelled') assert.equal(blocker.state, 'cancelled');
  else assert.ok(blocker.question?.text, 'the public question must be saved before releasing journal custody');
  assert.equal(f.prs.length, 0, 'a saved blocker must prevent PR creation');
  assert.equal(f.pushes.length, 0, 'a saved blocker must prevent pushes');
  const after = f.record();
  assert.deepEqual(blocker.decisions, before.decisions);
  assert.deepEqual(after.decisions, blocker.decisions);
  assert.deepEqual(after.approvalRecord, blocker.approvalRecord);
  assert.equal(after.state, blocker.state);
  assert.deepEqual(after.cancelled, blocker.cancelled);
  assert.deepEqual(after.question, blocker.question);
  assert.deepEqual(after.gate, blocker.gate);
  assert.equal(blockerJournal, initialJournal);
  assert.equal(readFileSync(journal, 'utf8'), blockerJournal, 'a saved blocker must prevent a later approval journal write');
  assert.equal(readFileSync(path, 'utf8'), checkedPrompt, 'unrecorded prompt approval edits must be restored');
  assert.equal(nativeFs.existsSync(lock), false, 'refusal must release journal custody');
  assert.deepEqual(nativeFs.readdirSync(dir).filter(name => /^\.approvals\..*\.tmp$/.test(name)), [], 'refusal must remove its temporary journal');
});

for (const kind of ['strict', 'scope', 'custody']) test(`#3099 ${kind} authority withdrawn during journal contention prevents durable approval`, async t => {
  const f = await setup(t), path = join(f.run.root, PROMPT);
  const checkedPrompt = readFileSync(path, 'utf8').replace(/"status":\s*"approved"/, '"status":"draft"');
  writeFileSync(path, checkedPrompt);
  f.git(f.run.root, 'add', '.'); f.git(f.run.root, 'commit', '-qm', 'Synthetic checked draft');
  saveCheck(f);
  const before = f.record(), dir = join(before.commonDir, 'pdd'), journal = join(dir, 'approvals.json');
  const initialJournal = readFileSync(journal, 'utf8'), lock = join(dir, 'approvals.lock'), token = randomUUID();
  const holder = join(lock, `owner-${token}.json`);
  mkdirSync(lock);
  writeFileSync(holder, JSON.stringify({pid: process.pid, hostname: hostname(), token}));
  const releaseHolder = () => {
    if (nativeFs.existsSync(holder)) nativeFs.unlinkSync(holder);
    if (nativeFs.existsSync(lock) && !nativeFs.readdirSync(lock).length) nativeFs.rmdirSync(lock);
  };
  t.after(releaseHolder);
  let contended = false, blockerTask, blockerError, blocker, blockerJournal;
  // Observe a real live owner inspection. Every filesystem operation still uses
  // native fs. The public blocker runs while acquisition awaits its next retry.
  f.tickPorts.fs = {...nativeFs, readFileSync(file, ...args) {
    const value = nativeFs.readFileSync(file, ...args);
    if (file === holder && !contended) {
      contended = true;
      blockerTask = Promise.resolve().then(async () => {
        try {
          f.tick();
          if (kind === 'strict') writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto'}, strict_approvals: true}));
          if (kind === 'scope') {const state = JSON.parse(readFileSync(f.stateFile)); delete state.startAction; writeFileSync(f.stateFile, JSON.stringify(state));}
          if (kind === 'custody') {const file = join(f.base, 'reader.json'), doc = JSON.parse(readFileSync(file)); doc.comments = []; writeFileSync(file, JSON.stringify(doc));}
          blocker = f.record();
          blockerJournal = readFileSync(journal, 'utf8');
        } finally { releaseHolder(); }
      }).catch(error => { blockerError = error; });
    }
    return value;
  }};
  await f.scan();
  await blockerTask;
  if (blockerError) throw blockerError;
  assert.equal(contended, true, 'the race must inspect the real journal holder');
  assert.equal(readFileSync(journal, 'utf8'), initialJournal, 'withdrawn authority must prevent durable automatic approval');
  assert.equal(f.prs.length, 0, 'withdrawn authority must prevent PR creation');
  assert.equal(f.pushes.length, 0, 'a saved blocker must prevent pushes');
  const after = f.record();
  assert.deepEqual(blocker.decisions, before.decisions);
  assert.deepEqual(after.decisions, blocker.decisions);
  assert.deepEqual(after.approvalRecord, blocker.approvalRecord);
  assert.equal(after.state, blocker.state);
  assert.deepEqual(after.cancelled, blocker.cancelled);
  assert.deepEqual(after.question, blocker.question);
  assert.deepEqual(after.gate, blocker.gate);
  assert.equal(blockerJournal, initialJournal);
  assert.equal(readFileSync(journal, 'utf8'), blockerJournal, 'a saved blocker must prevent a later approval journal write');
  assert.equal(readFileSync(path, 'utf8'), checkedPrompt, 'unrecorded prompt approval edits must be restored');
  assert.equal(nativeFs.existsSync(lock), false, 'refusal must release journal custody');
  assert.deepEqual(nativeFs.readdirSync(dir).filter(name => /^\.approvals\..*\.tmp$/.test(name)), [], 'refusal must remove its temporary journal');
});

for (const parked of [false, true]) test(`#3099 registered ${parked ? 'parked' : 'waiting'} full-pass gate reconciles before parking`, async t => {
  const f = await setup(t, {registered: true});
  f.herdr.idle();
  await f.status();
  const before = f.record();
  assert.ok(before.chats.every(chat => chat.session), 'ordinary status must register native sessions');
  assert.equal(before.parking, undefined);
  if (parked) {
    saveCheck(f, {criteria: {passed: 2, total: 3}});
    await f.scan();
    const held = f.record();
    assert.equal(f.prs.length, 0);
    assert.equal(held.parking.phase, 'parked');
    assert.equal(held.parking.blocker.kind, 'person');
    assert.equal(held.parking.personWait.gate.id, before.gate.id);
  }
  saveCheck(f);
  f.onIntake = () => assert.equal(f.prs.length, 1, 'full-pass reconciliation must precede intake');
  await f.scan();
  const after = f.record();
  assert.equal(f.prs.length, 1, 'registered full-pass gate must publish PR 1');
  assert.equal(after.gate.kind, 'ask-code');
  assert.equal(after.parking.phase, 'parked');
  assert.equal(after.parking.personWait.gate.kind, 'ask-code', 'parking must bind the remaining code gate');
  assert.deepEqual(after.chats.map(chat => chat.session), before.chats.map(chat => chat.session));
  assert.deepEqual(after.done, before.done);
  assert.equal(after.area, before.area);
  assert.equal(after.decisions.at(-1).via, 'automatic-check-pass');
  const decisions = after.decisions.length;
  await f.scan();
  assert.equal(f.prs.length, 1);
  assert.equal(f.record().decisions.length, decisions);
});

for (const change of ['Story', 'expected']) test(`#3099 registered parked ${change} revision replaces check guidance across ticks`, async t => {
  const f = await setup(t, {registered: true});
  f.herdr.idle();
  await f.status();
  assert.ok(f.record().chats.every(chat => chat.session), 'status must register native sessions');
  saveCheck(f, {criteria: {passed: 2, total: 3}});
  await f.scan();
  const before = f.record();
  assert.equal(before.parking.phase, 'parked');
  assert.equal(before.parking.blocker.kind, 'person');
  assert.equal(before.parking.personWait.gate.id, before.gate.id);
  assert.match(before.gate.automaticHold, /check.*full pass/i);
  const calls = f.herdr.calls.length;
  f.tick();
  if (change === 'Story') writeFileSync(join(f.run.root, STORY), readFileSync(join(f.run.root, STORY), 'utf8') + '\nAn added product rule.\n');
  else {
    const path = join(f.run.root, TEST), scenario = JSON.parse(readFileSync(path));
    scenario.steps[0].checks[0].value = 'changed expectation';
    writeFileSync(path, JSON.stringify(scenario));
  }
  saveCheck(f);
  let reopened;
  for (let tick = 0; tick < 3; tick++) {
    f.tick();
    await f.scan();
    const after = f.record();
    assert.equal(after.state, 'waiting');
    assert.equal(after.gate.kind, 'approve-pr');
    assert.ok(after.gate.storyChanges.length, 'the revised contract must reopen Story approval');
    assert.notEqual(after.gate.id, before.gate.id, 'the old approval identity must not cover the revision');
    assert.match(after.gate.automaticHold, /Story.*approval/i, 'the revised Story must replace the obsolete check hold');
    assert.notEqual(after.gate.automaticHold, before.gate.automaticHold);
    assert.equal(after.parking.phase, 'parked');
    assert.equal(after.parking.at, before.parking.at);
    assert.deepEqual(after.parking.blocker, before.parking.blocker);
    assert.equal(after.parking.personWait.gate.id, after.gate.id, 'the reservation must bind the revised gate');
    assert.deepEqual(after.chats, before.chats, 'the saved chats must stay closed with the same sessions');
    assert.deepEqual(after.done, before.done);
    assert.deepEqual(after.decisions, before.decisions);
    assert.deepEqual(after.automaticOrigin, before.automaticOrigin);
    assert.equal(f.prs.length, 0); assert.equal(f.pushes.length, 0);
    if (reopened) assert.equal(after.gate.id, reopened.id, 'later ticks must retain the revised gate');
    reopened = after.gate;
    const status = await runStatus({ref: '17', cwd: f.source}, f.automaticPorts);
    assert.equal(status.exitCode, 0, status.message);
    const next = status.message.split('\n').find(line => line.startsWith('Next:'));
    assert.match(next, /Story.*approval/i, 'public guidance must ask for the revised Story approval');
    assert.ok(!next.includes(before.gate.automaticHold), 'public guidance must drop the obsolete check failure');
    assert.ok((await f.status()).words.includes(after.gate.automaticHold), 'parked summary retains the current hold');
  }
  const effects = f.herdr.calls.slice(calls).filter(args => args[0] === 'pane' && args[1] === 'run' || args[0] === 'agent' && args[1] === 'prompt');
  assert.deepEqual(effects, [], 'the held gate must not wake or message a worker');
  assert.deepEqual(f.warnings, []);
});


test('PR 1 refreshed interpreter wait reconciles before intake and preserves independent blockers', async t => {
  for (const boundary of ['inferred', 'dependency', 'busy']) {
    const f = await setup(t, {registered: true});
    if (boundary === 'busy') f.herdr.paneOf(f.record().chats.at(-1)).agent.agent_status = 'working';
    if (boundary === 'dependency') {
      const run = f.record(); run.blockedOn = {kind: 'dependency', until: '18'};
      writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
    }
    await f.scan();
    const before = f.record();
    assert.equal(before.parking.phase, boundary === 'busy' ? 'closing' : 'parked');
    assert.equal(before.parking.blocker.kind, boundary === 'dependency' ? 'dependency' : 'interpreter');
    saveCheck(f);
    f.onIntake = () => assert.equal(f.prs.length, boundary === 'inferred' ? 1 : 0, 'refresh is reconciled before intake');
    await f.scan();
    assert.equal(f.prs.length, boundary === 'inferred' ? 1 : 0, boundary);
    assert.equal(f.record().gate.kind, boundary === 'inferred' ? 'ask-code' : 'approve-pr');
    assert.equal(f.record().parking.at, before.parking.at);
    assert.deepEqual(f.record().automaticOrigin, before.automaticOrigin);
    if (boundary === 'dependency') assert.deepEqual(f.record().blockedOn, before.blockedOn);
    if (boundary === 'busy') assert.ok(f.herdr.paneOf(before.chats.at(-1)), 'busy native work remains open');
  }
});
