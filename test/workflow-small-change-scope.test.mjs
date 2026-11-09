import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync, readFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-runner-fixture.mjs';
import {stepDone, approveRun, runStatus} from '../src/workflow-runner.mjs';
import {sourceFingerprint} from '../src/workflow-replay.mjs';
import {readablePrTop, prStatus, DETAILS_OPEN} from '../src/workflow-pr-body.mjs';
import {smallChange} from './helpers/readable-pr-fixtures.mjs';
import {reviewSmallChangeChecklist, readSmallChangeChecklist} from '../src/workflow-small-change.mjs';

// Independent synthetic issue and trusted follow-up. Expectations precede the plan.
const requests = [
  {id: 'R1', request: 'Correct the guide', source: 'https://github.com/example/project/issues/17', quote: 'Correct the guide'},
  {id: 'R2', request: 'Correct generated setup', source: 'https://github.com/example/project/issues/17#issuecomment-1', quote: 'Also correct generated setup'},
];
const completed = () => requests.map(item => ({...item, state: 'done', evidence: `fixture/${item.id}`}));
const exemption = {result: 'not_applicable', scope: 'documentation-only', reason: 'DOCSSCOPE3139', control_outcome: 'not_run'};
const render = checklist => {
  const facts = smallChange(); facts.records.ci = 'passing';
  facts.records.checklist = checklist; return facts;
};

test('3139 checker must-fix for a dropped request or unsupported exclusion blocks readiness', () => {
  for (const items of [completed().slice(0, 1), [...completed().slice(0, 1), {...requests[1], state: 'excluded', exclusion: {reason: 'plan scope', quote: 'out of scope'}}]]) {
    const checklist = {status: 'recorded', items};
    checklist.mustFix = reviewSmallChangeChecklist(checklist, requests);
    assert.equal(checklist.mustFix.length, 1);
    assert.equal(checklist.mustFix[0].id, 'R2');
    assert.ok(['missing-request','unsupported-exclusion'].includes(checklist.mustFix[0].code));
    assert.match(prStatus(render(checklist)), /^⛔/);
  }
});

test('3139 supported optional exclusions and completion evidence are checked independently', () => {
  const optional = {...requests[1], exclusion_quote: 'Optionally correct generated setup'};
  const items = [completed()[0], {...requests[1], state: 'excluded', exclusion: {reason: 'optional', quote: optional.exclusion_quote}}];
  assert.deepEqual(reviewSmallChangeChecklist({items}, [requests[0], optional]), []);
  assert.equal(reviewSmallChangeChecklist({items}, requests)[0].code, 'unsupported-exclusion');
  assert.equal(reviewSmallChangeChecklist({items: [{...requests[0], state: 'pending'}]}, [requests[0]])[0].code, 'pending-request');
  assert.equal(reviewSmallChangeChecklist({items: [{...requests[0], state: 'done'}]}, [requests[0]])[0].code, 'missing-evidence');
});

test('3139 PR checklist retains every item, state, source and exclusion quote', () => {
  const items = completed(); items[1] = {...requests[1], state: 'excluded', exclusion: {reason: 'optional', quote: 'OPTIONAL_3139'}};
  const body = readablePrTop(render({status: 'recorded', items, mustFix: []})).text;
  const table = body.split('## Issue checklist')[1]?.split('##')[0];
  assert.ok(table, 'CHECKLIST_3139');
  for (const item of items) for (const value of [item.id, item.request, item.source, item.state, item.exclusion?.quote ?? item.evidence]) assert.ok(table.replaceAll('\u200b', '').includes(value), value);
});

test('3139 completed formal step cannot replace missing formal evidence', () => {
  const facts = render({status: 'recorded', items: completed(), mustFix: []});
  delete facts.records.formal; facts.records.formalDone = true;
  facts.fields.result = 'documentation-only; formal not applicable';
  assert.match(prStatus(facts), /^⛔/, 'FORMAL_MISSING_3139');
});

test('3139 native publication shares docs exemption in body, proof and saved status', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
  let run = f.record();
  const saveEvidence = () => {
    run = f.record();
    const source = {kind: 'git-content-v1', sha256: sourceFingerprint(run.root)};
    writeFileSync(join(run.runDir, 'small-change-checklist.json'), JSON.stringify({schema_version: 'pdd.small-change-checklist.v1', run_id: run.runId, source, items: completed()}));
    writeFileSync(join(run.runDir, 'replay-evidence.json'), JSON.stringify({schema_version: 'pdd.replay-evidence.v1', run_id: run.runId, source, formal: exemption}));
  };
  saveEvidence();
  assert.equal((await stepDone({step: 'scope', cwd: run.root, summary: 'All requests retained'}, f.ports)).exitCode, 0);
  assert.equal((await approveRun({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  writeFileSync(join(run.root, 'README.md'), 'Synthetic documentation\n');
  f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'Documentation fixture');
  saveEvidence();
  for (const step of ['change', 'verify', 'formal']) {
    f.tick();
    assert.equal((await stepDone({step, cwd: run.root, summary: 'Source evidence saved'}, f.ports)).exitCode, 0);
  }
  const saved = f.record(), facts = saved.pr[0].readable.facts;
  assert.equal(facts.records.formal.result, 'not_applicable');
  assert.ok(saved.done.formal.smallChange, 'SAVED_EXEMPTION_3139');
  assert.deepEqual(saved.done.formal.smallChange.formal, facts.records.formal);
  const body = f.prs[0].body, visible = body.split(DETAILS_OPEN)[0];
  const row = visible.split('\n').find(line => line.startsWith('| Formal check'));
  assert.ok(row?.includes(exemption.reason), 'EXEMPTION_3139');
  assert.ok(body.split(DETAILS_OPEN)[1].includes(exemption.reason));
  assert.equal(facts.records.checklist.items.length, 2);
  const status = await runStatus({ref: '17', cwd: f.source, json: true}, f.ports);
  assert.equal(status.exitCode, 0);
  const shown = JSON.parse(status.message).runs[0].smallChange;
  assert.deepEqual(shown.formal, facts.records.formal);
  assert.deepEqual(shown.checklist, facts.records.checklist);
  const text = await runStatus({ref: '17', cwd: f.source}, f.ports);
  assert.ok(text.message.includes(exemption.reason));
  const path = join(run.runDir, 'small-change-checklist.json');
  const record = JSON.parse(readFileSync(path)); record.items[1].state = 'pending';
  writeFileSync(path, JSON.stringify(record));
  assert.equal(readSmallChangeChecklist(run).mustFix[0].code, 'pending-request');
  writeFileSync(join(run.root, 'README.md'), 'Changed source\n');
  assert.equal(readSmallChangeChecklist(run).status, 'stale');
});

test('3139 oversized checklist refuses publication without dropping requests', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  writeFileSync(join(run.root, 'README.md'), 'Synthetic documentation\n');
  f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'Documentation fixture');
  const source = {kind: 'git-content-v1', sha256: sourceFingerprint(run.root)};
  const items = [{...completed()[0], quote: 'q'.repeat(57000)}];
  writeFileSync(join(run.runDir, 'small-change-checklist.json'), JSON.stringify({schema_version: 'pdd.small-change-checklist.v1', run_id: run.runId, source, items}));
  writeFileSync(join(run.runDir, 'replay-evidence.json'), JSON.stringify({schema_version: 'pdd.replay-evidence.v1', run_id: run.runId, source, formal: exemption}));
  await stepDone({step: 'scope', cwd: run.root}, f.ports);
  await approveRun({ref: '17', cwd: f.source}, f.ports);
  for (const step of ['change', 'verify']) await stepDone({step, cwd: run.root}, f.ports);
  const out = await stepDone({step: 'formal', cwd: run.root}, f.ports);
  assert.notEqual(out.exitCode, 0, 'CHECKLIST_BUDGET_3139');
  assert.equal(f.pushes.length, 0);
  assert.equal(f.prs.length, 0);
  assert.equal(JSON.parse(readFileSync(join(run.runDir, 'small-change-checklist.json'))).items[0].quote.length, 57000);
});
