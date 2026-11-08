import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, nativeCase, success, assertReviewCosts} from './helpers/recover-guidance-cli-fixture.mjs';

// Independent oracle: user_stories/recover-guidance-code-review.md,
// Rules to check and AC2--AC5, plus the unchanged native case inventory.
// The complete finite domain is:
//   selection {empty, one unchanged prompt}
//   x review {reviewed, absent, stale, revoked}
//   x lifecycle {completed-pr1, cancelled, completed-code, incomplete-pr1}
//   x operation {recovery, approval}: 64 worlds.
// Add selection x operation x concurrent replacement {cancelled, run, gate,
// completed-code}: 16 worlds; selection x wrong-run approval: 2 worlds.
// Total: 82 independently seeded worlds. Snapshot hash algorithms are outside
// this rule: review presence, selected paths, full non-review state, preserved
// bytes/effects, and acceptance of later independent consent are observed.
const selections = ['empty', 'one'];
const reviews = ['reviewed', 'absent', 'stale', 'revoked'];
const lifecycles = ['completed-pr1', 'cancelled', 'completed-code', 'incomplete-pr1'];
const operations = ['recovery', 'approval'];
const recovery = () => [...nativeCase('recover-current-review').commands[0]];
const approval = () => [...nativeCase('approve-after-recovery').commands[0]];
const words = () => nativeCase('approve-after-recovery').approval_input;
const currentPaths = selection => selection === 'empty' ? [] : ['prompts/current.prompt.md'];

function world(t, selection, review, lifecycle = 'completed-pr1') {
  const f = fixture(t);
  if (selection === 'one') {
    mkdirSync(join(f.root, 'prompts'));
    writeFileSync(join(f.root, 'prompts/current.prompt.md'), '# Current\nSynthetic unchanged policy.\n');
  }
  // Establish real PR1 and its separate displayed code-choice review through
  // ordinary public commands. These observations seed inputs, never the oracle.
  success(f.cli(nativeCase('reviewed-empty-pr1').commands[0]));
  success(f.cli(nativeCase('reviewed-empty-pr1').commands[1], nativeCase('reviewed-empty-pr1').approval_input));
  if (review === 'revoked') success(f.cli(nativeCase('invalidate-and-complete').commands[0]));
  else if (review === 'absent' || review === 'stale') {
    const run = f.read();
    if (review === 'absent') delete run.gate.promptSnapshot;
    else if (selection === 'empty') run.gate.promptSnapshot = [{path:'prompts/removed.prompt.md', proseSha256:'0'.repeat(64), reviewSha256:'0'.repeat(64)}];
    else run.gate.promptSnapshot[0].reviewSha256 = '0'.repeat(64);
    f.save(run);
  }
  f.merge(); success(f.cli(nativeCase('invalidate-and-complete').commands[1]));
  const run = f.read();
  if (lifecycle === 'cancelled') run.state = 'cancelled';
  if (lifecycle === 'completed-code') {run.area = 1; run.doneAt = 'code'; run.gate = null;}
  if (lifecycle === 'incomplete-pr1') delete run.done.check;
  // An unrelated pending question/evidence must survive a snapshot-only refresh.
  run.question = {text:'Synthetic pending question', area:'prompt-pr', at:1};
  f.save(run);
  return f;
}

// Save metadata and the two documented review locations are the entire allowed
// refresh delta. All other nested fields, including completion and evidence,
// are compared, rather than a selected list of progress fields.
function withoutReviewSaveMetadata(run) {
  const copy = structuredClone(run);
  delete copy.updatedAt; delete copy.journalSeq; delete copy.cost;
  if (copy.gate) delete copy.gate.promptSnapshot;
  if (copy.waitingDecision) delete copy.waitingDecision.promptSnapshot;
  return copy;
}
function prompts(f) {
  return currentPaths('one').map(path => {
    try {return [path, readFileSync(join(f.root, path), 'utf8')];} catch {return [path, null];}
  });
}
function assertContinuation(f, before) {
  const after = f.read();
  assert.equal(after.area, 1); assert.equal(after.gate, null);
  for (const field of ['runId','root','sourceRoot','baseSha','baseBranch','pr','done','changes']) assert.deepEqual(after[field], before[field], field);
  assert.deepEqual(after.decisions.slice(0, -1), before.decisions);
  assert.equal(after.decisions.length, before.decisions.length + 1);
  const decision = after.decisions.at(-1);
  assert.equal(decision.gateId, before.gate.id); assert.equal(decision.gateAt, before.gate.at);
  assert.equal(decision.evidence.prompts.length, before.gate.promptSnapshot.length);
  assert.equal(after.branch, 'guidance-topic-code');
  assert.equal(f.git('rev-parse','HEAD'), f.git('rev-parse','refs/remotes/origin/main'));
  const effects = f.effects();
  assert.equal(f.herdr().calls.filter(a => a[0] === 'pane' && a[1] === 'run').length, 1);
  assert.equal(f.git('branch','--list','*-code').trim().split('\n').length, 1);
  const bytes = f.bytes();
  assert.equal(f.cli(approval(), words()).status, 1);
  assert.deepEqual(f.bytes(), bytes); assert.deepEqual(f.effects(), effects);
}

for (const selection of selections) for (const review of reviews) for (const lifecycle of lifecycles) for (const operation of operations) {
  test(`bounded guidance rule: ${selection}/${review}/${lifecycle}/${operation}`, t => {
    const f = world(t, selection, review, lifecycle), before = f.read(), bytes = f.bytes(), effects = f.effects(), prose = prompts(f);
    // This Boolean oracle is the Story rule, independent of implementation:
    const mayRefresh = operation === 'recovery' && lifecycle === 'completed-pr1';
    const mayContinue = operation === 'approval' && lifecycle === 'completed-pr1' && review === 'reviewed';
    const out = f.cli(operation === 'recovery' ? recovery() : approval(), operation === 'approval' ? words() : undefined);
    if (mayRefresh) {
      assert.equal(out.status, 0, out.stderr);
      assert.ok(Array.isArray(f.read().gate.promptSnapshot), 'FORMAL2979: eligible recovery must save present current review evidence');
      assert.deepEqual(f.read().gate.promptSnapshot.map(row => row.path), currentPaths(selection));
      assertReviewCosts(before, f.read());
      assert.deepEqual(withoutReviewSaveMetadata(f.read()), withoutReviewSaveMetadata(before));
      assert.deepEqual(f.effects(), effects); assert.deepEqual(prompts(f), prose);
      assert.match(out.stdout, /Do you want the code PR now/);
      if (selection === 'empty') assert.match(out.stdout, /Selected prompts: none\./);
      else assert.match(out.stdout, /Prompt: prompts\/current\.prompt\.md /);
      // This separate, later explicit approval must be usable exactly once.
      const displayed = f.read();
      success(f.cli(approval(), words())); assertContinuation(f, displayed);
    } else if (mayContinue) {
      assert.equal(out.status, 0, out.stderr); assertContinuation(f, before);
    } else {
      assert.equal(out.status, operation === 'recovery' ? 0 : 1, out.stderr || out.stdout);
      assert.deepEqual(f.bytes(), bytes); assert.deepEqual(f.effects(), effects);
      assert.deepEqual(prompts(f), prose);
    }
  });
}

for (const selection of selections) for (const operation of operations) for (const replacement of ['cancelled','run','gate','completed-code']) {
  test(`bounded guidance concurrency: ${selection}/${operation}/${replacement}`, t => {
    const f = world(t, selection, operation === 'approval' ? 'reviewed' : 'absent'), run = f.read(), effects = f.effects(), prose = prompts(f);
    const patch = replacement === 'cancelled' ? {state:'cancelled'} : replacement === 'run' ? {runId:'synthetic-replacement'} :
      replacement === 'gate' ? {gate:{...run.gate,id:'synthetic-replacement-gate',at:run.gate.at+1}} : {area:1,gate:null,doneAt:'code'};
    f.race(patch);
    const out = f.cli(operation === 'recovery' ? recovery() : approval(), operation === 'approval' ? words() : undefined);
    assert.equal(out.status, 1, out.stdout); assert.deepEqual(f.bytes(), f.racedBytes());
    assert.deepEqual(f.effects(), effects); assert.deepEqual(prompts(f), prose);
  });
}

for (const selection of selections) test(`bounded guidance wrong-run: ${selection}`, t => {
  const f = world(t, selection, 'reviewed'), bytes = f.bytes(), effects = f.effects(), prose = prompts(f), args = approval();
  args[2] = '18';
  assert.equal(f.cli(args, words()).status, 1);
  assert.deepEqual(f.bytes(), bytes); assert.deepEqual(f.effects(), effects); assert.deepEqual(prompts(f), prose);
});
