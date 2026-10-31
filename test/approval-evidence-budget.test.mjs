import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';
import { stepDone, approveRun } from '../src/workflow-runner.mjs';

// Oracles: workflow-runner's whole-body 60,000 Unicode-code-point limit and
// workflow-pr-evidence's whole approval records, explicit omission and header order.
// Scratch Git and injected gh/Herdr only; no interpreter or provider.
const verdict = 'Verdict: budget publication reviewed';
const runtime = 'Runtime check (Budget): ✓ 1 of 1 criteria · 1/1 checks · 0 AI calls';
const report = 'Report (Budget): https://runtime.example/r/budget';
const summary = `${verdict}\n${runtime}\n${report}\nNot checked: external service`;
const saidPorts = f => f.agentPorts({ readApprovalEvidence: async () => assert.fail('required --said relay must approve without reading native-chat evidence') });
const success = (out, label) => assert.equal(out.exitCode, 0, `${label}: ${out.message?.slice(0, 700)}`);
async function finish(f) {
  const run = f.record();
  for (const step of run.areas[run.area].steps) {
    f.tick();
    const out = await stepDone({ step, summary, cwd: run.root }, f.agentPorts());
    success(out, `finish ${step}`);
  }
  f.herdr.idle();
}
async function ready(t, storyWords = 'reviewed story') {
  const f = await fixture(t, { name: 'feature' });
  success(await f.run(), 'start feature');
  await finish(f);
  success(await approveRun({ ref: '17', cwd: f.source, said: storyWords }, saidPorts(f)), 'approve story');
  writeFileSync(join(f.record().root, 'value.mjs'), 'export const value = 2;\n');
  await finish(f);
  assert.equal(f.record().gate?.kind, 'approve-pr', 'PR1 is ready for explicit approval');
  return f;
}
function saved(f) {
  const run = f.record();
  assert.ok(Array.isArray(run.decisions), 'required durable workflow decisions array');
  const path = join(run.commonDir, 'pdd', 'approvals.json');
  assert.ok(existsSync(path), 'required durable approval journal exists after said approval');
  const journal = JSON.parse(readFileSync(path, 'utf8'));
  assert.ok(Array.isArray(journal.approvals), 'required durable journal approvals array');
  return { run, decisions: run.decisions, approvals: journal.approvals };
}
function exactWords(f, expected) {
  const state = saved(f);
  assert.equal(state.decisions.length, expected.length, 'one decision per approved gate');
  assert.equal(state.approvals.length, expected.length, 'one journal event per approved gate');
  expected.forEach((words, i) => {
    assert.ok(state.decisions[i].evidence?.words === words, `history event ${i} preserves all ${[...words].length} code points`);
    assert.ok(state.approvals[i].words === words, `journal event ${i} preserves all ${[...words].length} code points`);
    assert.equal(state.decisions[i].evidence.id, state.approvals[i].id, 'history and journal retain the same event');
  });
  return state;
}
function bounded(body, expectedWords, { code = false } = {}) {
  assert.equal(typeof body, 'string', 'successful publication supplies a description');
  const size = [...body].length;
  assert.ok(size <= 60000, `complete published description has ${size} Unicode code points; maximum 60000`);
  assert.equal((body.match(/pdd-workflow:/g) ?? []).length, 1, 'one canonical ownership marker');
  const rows = body.split('\n').filter(row => /^Approved in (?:chat|terminal|area chat):/.test(row));
  const omission = body.match(/(\d+) approval evidence records? omitted/i);
  assert.ok(omission, 'budget omission explicitly names and counts omitted approval evidence records');
  assert.equal(Number(omission[1]), expectedWords.length - rows.length, 'omitted record count accounts for every saved event');
  for (const row of rows) {
    assert.ok(expectedWords.some(words => row.includes(JSON.stringify(words))), 'a displayed approval contains complete exact words, never a truncated full-words claim');
  }
  const positions = ['Not checked:', verdict, runtime, 'Report (Budget):', code ? 'Closes #17' : 'Part of #17'].map(text => body.indexOf(text));
  positions.forEach((at, i) => assert.ok(at >= 0 && (!i || at > positions[i - 1]), `retained top label and ordinary header order: item ${i}`));
  assert.ok(/\n\n(?:Part of|Closes) #17\n/.test(body), 'ordinary Runtime/report header retains blank separator before issue reference');
  for (const row of rows) assert.ok(body.indexOf(row) > positions.at(-1) && body.indexOf(row) < body.indexOf('## Steps'), 'approval follows ordinary header and precedes step prose');
  assert.match(body, /report links expire after 7 days/);
  assert.match(body, /## Steps/);
}

test('APPROVAL-BUDGET initial PR1 and same-gate retry publish despite one oversized approval without duplicating durable evidence', async t => {
  const words = `person-start ${'😀'.repeat(70000)} person-end`;
  const f = await ready(t, words);
  f.createError = 'synthetic one-time GitHub refusal';
  const first = await approveRun({ ref: '17', cwd: f.source, said: 'publish PR1' }, saidPorts(f));
  const before = exactWords(f, [words, 'publish PR1']);
  const pushes = f.pushes.length;
  const retry = await approveRun({ ref: '17', cwd: f.source, said: 'retry words must not replace consent' }, saidPorts(f));
  success(retry, 'same approved gate can retry publication with oversized evidence');
  assert.match(first.message, /synthetic one-time GitHub refusal/, 'first body reached gh rather than failing its budget guard');
  assert.deepEqual(f.record().decisions, before.decisions, 'retry creates no new gate or approval event');
  assert.deepEqual(saved(f).approvals, before.approvals, 'retry leaves the durable journal unchanged');
  assert.equal(f.pushes.length, pushes, 'unchanged retry does not push again');
  assert.equal(f.prs.length, 1, 'retry creates exactly one PR');
  bounded(f.prs[0].body, [words, 'publish PR1']);
  exactWords(f, [words, 'publish PR1']);
});

test('APPROVAL-BUDGET existing PR1 refresh bounds several individually fitting approval records and counts omissions', async t => {
  const words = ['story', 'publish', 'code'].map(label => `${label}-start ${'x'.repeat(21000)} ${label}-end`);
  const f = await ready(t, words[0]);
  success(await approveRun({ ref: '17', cwd: f.source, said: words[1] }, saidPorts(f)), 'publish initially fitting PR1');
  assert.equal(f.prs.length, 1);
  const beforeEdits = f.edits.length;
  success(await approveRun({ ref: '17', cwd: f.source, said: words[2] }, saidPorts(f)), 'approve code and refresh PR1');
  assert.ok(f.edits.length > beforeEdits, 'existing PR1 is refreshed through gh edit');
  bounded(f.prs[0].body, words);
  exactWords(f, words);
});

test('APPROVAL-BUDGET code PR creation and changed-source update preserve bounded approvals and pending-before-push', async t => {
  const words = ['reviewed story', 'publish PR1', `code-start ${'x'.repeat(70000)} code-end`];
  const f = await ready(t, words[0]);
  success(await approveRun({ ref: '17', cwd: f.source, said: words[1] }, saidPorts(f)), 'publish PR1');
  success(await approveRun({ ref: '17', cwd: f.source, said: words[2] }, saidPorts(f)), 'approve code');
  writeFileSync(join(f.record().root, 'value.mjs'), 'export const value = 3;\n');
  await finish(f);
  assert.equal(f.prs.length, 2, 'code publication creates PR2');
  bounded(f.prs[1].body, words, { code: true });
  assert.ok(f.prs[1].body.indexOf('Not checked:') < f.prs[1].body.indexOf('Code replay:'), 'all top evidence precedes replay status');
  const state = exactWords(f, words);
  const events = [], original = f.ports.execFile;
  f.ports.execFile = async (file, args, opts) => {
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'edit' && args[2] === f.prs[1].url) events.push({ kind: 'edit', body: opts.input });
    if (file === 'git' && args[0] === 'push') events.push({ kind: 'push' });
    return original(file, args, opts);
  };
  writeFileSync(join(f.record().root, 'value.mjs'), 'export const value = 4;\n');
  success(await stepDone({ step: 'review', summary, cwd: f.record().root }, f.agentPorts()), 'refresh PR2 after source changes');
  const pending = events.findIndex(event => event.kind === 'edit' && /publication.pending/i.test(event.body));
  const push = events.findIndex(event => event.kind === 'push');
  assert.ok(pending >= 0 && push > pending, 'publication-pending description is written before changed-source push');
  bounded(f.prs[1].body, words, { code: true });
  assert.deepEqual(f.record().decisions, state.decisions, 'code publication changes no approval decision');
  assert.deepEqual(saved(f).approvals, state.approvals, 'code publication changes no journal words or events');
});
