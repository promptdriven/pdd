import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync, readFileSync, renameSync, symlinkSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture, inventory, nativeCase, reviewedPr1, missingCompletedReview, success, assertReviewCosts} from './helpers/recover-guidance-cli-fixture.mjs';

const recovery = () => [...nativeCase('recover-current-review').commands[0]];
const approval = () => [...nativeCase('approve-after-recovery').commands[0]];
const words = () => nativeCase('approve-after-recovery').approval_input;
const unchanged = (f, before, effects) => {assert.deepEqual(f.bytes(), before);assert.deepEqual(f.effects(), effects);};
function prompt(f, path='current.prompt.md', text='# Current\nSubstantive current policy.\n') {
  mkdirSync(join(f.root, 'prompts'), {recursive:true});
  writeFileSync(join(f.root, 'prompts', path), text);
}

test('approved native guidance recovery cases replay through bin/pdd.mjs', async t => {
  const f=fixture(t);
  await t.test('reviewed-empty-pr1 (AC1)', () => {
    const row=nativeCase('reviewed-empty-pr1'); reviewedPr1(f);
    assert.equal(f.git('branch', '--list', '*-code').length, row.expected.code_branches);
    assert.equal(f.herdr().calls.filter(a=>a[0]==='pane'&&a[1]==='run').length, row.expected.code_chats);
    assert.equal(f.read().area, 0);
  });
  await t.test('invalidate-and-complete (AC2, AC4)', () => {
    const row=nativeCase('invalidate-and-complete');
    success(f.cli(row.commands[0])); assert.equal(Object.hasOwn(f.read().gate, 'promptSnapshot'), row.expected.current_review_present);
    f.merge(); success(f.cli(row.commands[1]));
    assert.equal(f.read().state, row.expected.state);assert.equal(f.read().doneAt, row.expected.done_at);
    const before=f.bytes(), effects=f.effects(), decisions=f.read().decisions;
    const out=f.cli(row.commands[2], row.approval_input);
    assert.equal(out.status, row.expected.exit_codes[2]);assert.match(out.stderr, /no saved review/);
    unchanged(f,before,effects);assert.deepEqual(f.read().decisions,decisions);
  });
  let reviewed;
  await t.test('recover-current-review (AC2)', () => {
    const row=nativeCase('recover-current-review'), before=f.read(), effects=f.effects();
    // A pending question is intentionally preserved by review-only recovery.
    before.question={text:'Retain this pending question',area:'prompt-pr',at:before.gate.at+1};f.save(before);
    const out=f.cli(row.commands[0]);
    assert.equal(out.status,row.expected.exit_codes[0],out.stderr);
    reviewed=f.read();
    assert.deepEqual(reviewed.gate.promptSnapshot,row.expected.reviewed_selection,
      'RECOVER2979: current code-choice review was not refreshed by the advertised supported recovery');
    assert.match(out.stdout,/Selected prompts: none\./);assert.match(out.stdout,/Do you want the code PR now/);
    assert.equal(reviewed.state,row.expected.state);assert.equal(reviewed.doneAt,row.expected.done_at);
    const expected=structuredClone(before);expected.gate.promptSnapshot=row.expected.reviewed_selection;
    // The run-record owner mirrors gate review into its status projection.
    expected.waitingDecision.promptSnapshot=row.expected.reviewed_selection;
    // Only ordinary save metadata and the review itself may change.
    assertReviewCosts(before, reviewed);
    delete expected.updatedAt;delete expected.journalSeq;delete expected.cost;
    const actual=structuredClone(reviewed);delete actual.updatedAt;delete actual.journalSeq;delete actual.cost;
    assert.deepEqual(actual,expected);assert.deepEqual(f.effects(),effects);
    assert.equal(f.git('rev-parse','HEAD'),f.git('rev-parse','guidance-topic'));
    assert.equal(readFileSync(join(f.root,'guidance.md'),'utf8'),'Reviewed guidance.\n');
  });
  await t.test('approve-after-recovery (AC3)', () => {
    const row=nativeCase('approve-after-recovery'), before=reviewed;
    const out=f.cli(row.commands[0],row.approval_input);assert.equal(out.status,row.expected.exit_codes[0],out.stderr);
    const after=f.read();assert.equal(after.runId,before.runId);assert.equal(after.root,before.root);
    assert.deepEqual(after.pr,before.pr);assert.deepEqual(after.done,before.done);
    assert.deepEqual(after.decisions.slice(0,-1),before.decisions);
    assert.equal(after.decisions.length-before.decisions.length,row.expected.new_code_decisions);
    assert.equal(after.decisions.at(-1).gateId,before.gate.id);assert.equal(after.decisions.at(-1).gateAt,before.gate.at);
    assert.deepEqual(after.decisions.at(-1).evidence.prompts,row.expected.decision_selection);
    assert.equal(after.branch,'guidance-topic-code');assert.equal(after.prBase,'main');assert.equal(after.area,1);assert.equal(after.gate,null);
    assert.equal(f.git('rev-parse','HEAD'),f.git('rev-parse','refs/remotes/origin/main'));
    assert.equal(f.git('branch','--list','*-code').split('\n').length,row.expected.code_branches);
    assert.equal(f.herdr().calls.filter(a=>a[0]==='pane'&&a[1]==='run').length,row.expected.code_chats);
    const effects=f.effects(),decisionCount=after.decisions.length;
    assert.equal(f.cli(approval(),words()).status,1);
    assert.deepEqual(f.effects(),effects);assert.equal(f.read().decisions.length,decisionCount);
  });
  // Inventory is read at test time; no Interpreter schema or verdict is invented.
  assert.equal(inventory.cases.length,7);
});

for (const control of ['absent-empty','absent-nonempty','stale-digest','changed-path','changed-prose','revoked-review']) {
  test(`review-refusal-controls: ${control} (AC4)`, t => {
    const row=nativeCase('review-refusal-controls'), f=fixture(t);
    if(control==='revoked-review') {
      reviewedPr1(f);success(f.cli(nativeCase('invalidate-and-complete').commands[0]));
    } else {
      missingCompletedReview(f);
      if(control!=='absent-empty')prompt(f);
      if(['stale-digest','changed-path','changed-prose'].includes(control)) {
        success(f.cli(recovery()));
        if(control==='stale-digest') {const run=f.read();run.gate.promptSnapshot[0].reviewSha256='0'.repeat(64);f.save(run);}
        if(control==='changed-path')renameSync(join(f.root,'prompts/current.prompt.md'),join(f.root,'prompts/other.prompt.md'));
        if(control==='changed-prose')prompt(f,'current.prompt.md','# Current\nChanged substantive policy.\n');
      }
    }
    const before=f.bytes(),effects=f.effects(),files=f.git('status','--porcelain'),prose=control==='absent-empty'||control==='revoked-review'?null:
      readFileSync(join(f.root,control==='changed-path'?'prompts/other.prompt.md':'prompts/current.prompt.md'));
    const out=f.cli(row.commands[0],row.approval_input);assert.equal(out.status,row.expected.exit_codes[0],out.stdout);
    assert.match(out.stderr,/no saved review|selected prompts changed/i);unchanged(f,before,effects);
    assert.equal(f.git('status','--porcelain'),files);
    if(prose)assert.deepEqual(readFileSync(join(f.root,control==='changed-path'?'prompts/other.prompt.md':'prompts/current.prompt.md')),prose);
  });
}

for (const state of ['cancelled','completed-code']) test(`ended-controls: ${state} (AC5)`, t => {
  const row=nativeCase('ended-controls'),f=fixture(t);missingCompletedReview(f);
  if(state==='cancelled')f.patch({state:'cancelled'});else f.patch({area:1,gate:null,doneAt:'code'});
  for(let i=0;i<row.commands.length;i++) {
    const before=f.bytes(),effects=f.effects(),out=f.cli(row.commands[i],i?row.approval_input:undefined);
    assert.equal(out.status,row.expected.exit_codes[i],out.stderr);unchanged(f,before,effects);
  }
});

test('preservation-controls: ordinary ready code choice still continues (AC3)', t => {
  nativeCase('preservation-controls');const f=fixture(t),before=reviewedPr1(f);
  success(f.cli(approval(),words()));const after=f.read();
  assert.equal(after.area,1);assert.equal(after.prBase,'guidance-topic');assert.deepEqual(after.done,before.done);
  assert.equal(after.decisions.length,before.decisions.length+1);
  assert.equal(f.herdr().calls.filter(a=>a[0]==='pane'&&a[1]==='run').length,1);
});

test('preservation-controls: ordinary prompt approval still reviews and approves selected prose (AC4)', t => {
  nativeCase('preservation-controls');const f=fixture(t);prompt(f);
  success(f.cli(nativeCase('reviewed-empty-pr1').commands[0]));
  assert.equal(f.read().gate.promptSnapshot[0].path,'prompts/current.prompt.md');
  success(f.cli(nativeCase('reviewed-empty-pr1').commands[1],nativeCase('reviewed-empty-pr1').approval_input));
  assert.equal(f.read().decisions[0].evidence.prompts[0].path,'prompts/current.prompt.md');
  assert.equal(f.read().gate.kind,'ask-code');assert.equal(f.read().area,0);
});

for (const control of ['strict','wrong-run','missing-config']) test(`preservation-controls: ${control} approval refuses`, t => {
  nativeCase('preservation-controls');const f=fixture(t);missingCompletedReview(f);success(f.cli(recovery()));
  if(control==='strict')writeFileSync(join(f.root,'pdd.json'),'{"strict_approvals":true}');
  if(control==='missing-config')f.patch({configDir:join(f.base,'absent-config')});
  const before=f.bytes(),effects=f.effects(),args=approval();if(control==='wrong-run')args[2]='18';
  const out=f.cli(args,words());assert.equal(out.status,1,out.stdout);unchanged(f,before,effects);
  assert.match(out.stderr,control==='strict'?/Only the person can approve in a terminal/:control==='wrong-run'?/no.*run|not.*found/i:/folder does not exist/);
});

for (const operation of ['recovery','approval']) for (const control of ['cancelled','replacement','gate-replaced','completed-code']) {
  test(`preservation-controls: ${operation} racing ${control}`, t => {
    nativeCase('preservation-controls');const f=fixture(t);missingCompletedReview(f);
    if(operation==='approval')success(f.cli(recovery()));
    const run=f.read(),effects=f.effects();
    const patch=control==='cancelled'?{state:'cancelled'}:control==='replacement'?{runId:'replacement-run'}:
      control==='gate-replaced'?{gate:{...run.gate,id:'new-current-gate',at:run.gate.at+1}}:{area:1,gate:null,doneAt:'code'};
    f.race(patch);const out=f.cli(operation==='recovery'?recovery():approval(),operation==='approval'?words():undefined);
    assert.equal(out.status,1,out.stdout);assert.deepEqual(f.bytes(),f.racedBytes());assert.deepEqual(f.effects(),effects);
    assert.match(out.stderr,/replaced|gate changed|run ended/i);
  });
}

test('preservation-controls: legacy recovery cannot refresh a newly identified gate', t => {
  nativeCase('preservation-controls');const f=fixture(t);missingCompletedReview(f);
  const legacy=f.read();delete legacy.gate.id;f.save(legacy);
  const effects=f.effects();f.race({gate:{...legacy.gate,id:'a-different-current-gate'}});
  const out=f.cli(recovery());assert.equal(out.status,1,out.stdout);assert.match(out.stderr,/gate changed/);
  assert.deepEqual(f.bytes(),f.racedBytes());assert.deepEqual(f.effects(),effects);
});

test('recovery inspection failure preserves a previously shown review and every prompt byte', t => {
  const f=fixture(t);missingCompletedReview(f);success(f.cli(recovery()));
  const outside=join(f.base,'outside.prompt.md');writeFileSync(outside,'# Outside\nDo not follow.\n');
  mkdirSync(join(f.root,'prompts'),{recursive:true});symlinkSync(outside,join(f.root,'prompts/unsafe.prompt.md'));
  const before=f.bytes(),effects=f.effects(),out=f.cli(recovery());assert.equal(out.status,1,out.stdout);
  assert.match(out.stderr,/Cannot refresh.*unsafe prompt/);unchanged(f,before,effects);
  assert.equal(readFileSync(outside,'utf8'),'# Outside\nDo not follow.\n');
});

for (const control of ['unknown-step','incomplete-area','wrong-gate-area','not-done-at-pr1']) test(`recovery readiness: ${control} keeps ended reply`, t => {
  const f=fixture(t);missingCompletedReview(f);const run=f.read();let args=recovery();
  if(control==='unknown-step')args=[...args.slice(0,2),'build',...args.slice(3)];
  if(control==='incomplete-area'){delete run.done.check;f.save(run);}
  if(control==='wrong-gate-area'){run.gate.area='code';f.save(run);}
  if(control==='not-done-at-pr1')f.patch({doneAt:'code'});
  const before=f.bytes(),effects=f.effects(),out=f.cli(args);assert.equal(out.status,0,out.stderr);
  assert.match(out.stdout,/complete\. Stop\./);unchanged(f,before,effects);
});
