// #3029: a code PR said "Formal check (agent reported): not recorded." while its formal step had proved the Story's
// rules. pdd read the formal block only after a full scenario replay, so an area with no scenario vectors (PR 1
// changed no scenario file) lost it. These cases read real replay-evidence.json files in temporary Git
// repositories and render the PR body builders. See user_stories/formal-evidence-status.md.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import * as replay from '../src/workflow-replay.mjs';
import { prStatus, readablePrTop } from '../src/workflow-pr-body.mjs';
import { pr2Fix6 } from './helpers/readable-pr-fixtures.mjs';

const hash = value => createHash('sha256').update(value).digest('hex');
// The text that GitHub shows: the replay report escapes Markdown in agent values with a backslash.
const shown = text => text.replace(/\\([\\`*_[\]()|])/g, '$1');
// Modeled on prompt-runtime PR #670: 5 Story rules over 5192 bounded inputs, and the old code fails by assertion.
const PROVED = () => ({ result: 'proved_bounded', scope: 'All 5 rules of Story 532 over 5192 bounded inputs', reason: 'FORMAL_CHECK_PASSED: total=5192',
  control_outcome: 'assertion_failure', control_command: 'python formal_check_532.py --old-code', control_exit_code: 1 });
const REPAIR = /Repair: [^\n]*docs\/replay-evidence\.md, then run pdd workflow done formal again\./;
// The formal status that pdd read. When pdd gives none (the #670 bug: the block is lost at an early exit), the case
// fails here by an assertion with the value that pdd gave, not by a TypeError on a later field.
const formalOf = (result, label = 'formal status') => {
  assert.ok(result?.formal !== null && typeof result?.formal === 'object' && typeof result.formal.status === 'string',
    `${label}: pdd gives no formal status (result.formal is ${JSON.stringify(result?.formal)}; the replay says ${result?.outcome}: ${result?.reason})`);
  return result.formal;
};

function fixture(t, { vectors = false } = {}) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-formal-'))); t.after(() => rmSync(base, { recursive: true, force: true }));
  const root = join(base, 'repo'), runDir = join(base, 'run'); mkdirSync(join(root, 'tests'), { recursive: true }); mkdirSync(runDir);
  const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8' }).trim(); git('init', '-q');
  writeFileSync(join(root, 'code.mjs'), 'export const add=(a,b)=>a+b;\n');
  const checks = [{ criterion_id: 'AC1', target: 'result', path: '/total', op: 'equals', value: 3 }];
  if (vectors) writeFileSync(join(root, 'tests/add.json'), JSON.stringify({ schema_version: 'prompt-runtime.program-scenario.v1', steps: [{ step_id: 'sum', entry_path: 'prompts/add.prompt.md', operation: 'add', checks }] }));
  git('add', '.'); git('-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'fixture');
  // pdd pins the prompt area's changed scenario files at PR 1; no changed file gives an empty anchor (not_replayed).
  const run = { root, runDir, runId: 'formal-run', replayBaseline: replay.pinReplayVectors(root, vectors ? ['tests/add.json'] : []) };
  const manifest = { schema_version: 'pdd.replay-evidence.v1', run_id: run.runId, source: { kind: 'git-content-v1', sha256: replay.sourceFingerprint(root) },
    vectors: [], checks: [], operations: [], counts: { total: 0, pass: 0, fail: 0, blocked: 0, not_replayed: 0 }, formal: PROVED() };
  if (vectors) Object.assign(manifest, {
    vectors: [{ path: 'tests/add.json', sha256: hash(readFileSync(join(root, 'tests/add.json'))) }],
    checks: [{ vector: 'tests/add.json', step_id: 'sum', check_index: 0, entry_path: 'prompts/add.prompt.md', operation: 'add', criterion_id: 'AC1', target: 'result', path: '/total', op: 'equals', outcome: 'pass' }],
    operations: [{ vector: 'tests/add.json', step_id: 'sum', entry_path: 'prompts/add.prompt.md', operation: 'add', executed: true, outcome: 'returned', boundary: { kind: 'function', name: 'add' }, command: 'node test/add.vectors.test.mjs', exit_code: 0 }],
    counts: { total: 1, pass: 1, fail: 0, blocked: 0, not_replayed: 0 },
    mutation: { kind: 'semantic', description: 'Subtract instead of add', command: 'node test/add.vectors.test.mjs --mutant', exit_code: 1, outcome: 'assertion_failure', failed_checks: [{ vector: 'tests/add.json', step_id: 'sum', check_index: 0 }] } });
  const path = join(runDir, 'replay-evidence.json');
  const save = (doc = manifest) => writeFileSync(path, typeof doc === 'string' ? doc : JSON.stringify(doc));
  const read = () => replay.readReplayEvidence(run);
  const formalLine = result => shown(replay.formatReplayEvidence(result).split('\n').find(line => line.startsWith('Formal check')) ?? '');
  return { root, runDir, run, manifest, path, save, read, formalLine, git };
}

test('FORMAL1 #670: with no scenario vectors pdd still reads a proved formal block; the code replay stays NOT REPLAYED', t => {
  const f = fixture(t); f.save();
  const result = f.read();
  assert.equal(result.outcome, 'not_replayed');
  assert.equal(result.reason, 'The approved prompt area has no original scenario vectors.', 'The scenario replay reason is the same as before.');
  assert.equal(formalOf(result).status, 'recorded'); assert.equal(result.formal.result, 'proved_bounded');
  const report = replay.formatReplayEvidence(result);
  assert.match(report, /^Code replay: NOT REPLAYED — /m); assert.doesNotMatch(report, /Code replay: PASS/);
  assert.equal(f.formalLine(result), 'Formal check (agent reported): recorded — Proved (bounded); scope: All 5 rules of Story 532 over 5192 bounded inputs; reason: FORMAL_CHECK_PASSED: total=5192; control: assertion failure (exit 1).');
  // pdd read and hashed the file, and the recorded block confirmed the current source.
  assert.ok(report.includes(`Manifest SHA256: ${hash(readFileSync(f.path))}.`), report);
  assert.ok(report.includes(`Source: ${f.manifest.source.sha256}.`), report);
  assert.deepEqual(replay.readFormalEvidence(f.run).status, 'recorded', 'The formal read works alone too.');
});

test('FORMAL2: with no scenario vectors a Proved result needs its own assertion-failure control; other results need none', t => {
  for (const [change, field] of [
    [formal => { delete formal.control_command; }, 'formal.control_command'],
    [formal => { formal.control_exit_code = 0; }, 'formal.control_exit_code'],
    [formal => { delete formal.control_exit_code; formal.result = 'proved_solver'; }, 'formal.control_exit_code'],
    [formal => { formal.control_outcome = 'crash'; }, 'formal.control_outcome'],
  ]) {
    const f = fixture(t); change(f.manifest.formal); f.save();
    const result = f.read(), line = f.formalLine(result), said = f.manifest.formal.result === 'proved_solver' ? 'Proved (solver)' : 'Proved (bounded)';
    assert.equal(result.outcome, 'not_replayed', field);
    const formal = formalOf(result, field);
    assert.deepEqual([formal.status, formal.field, formal.reported], ['malformed', field, f.manifest.formal.result], field);
    assert.ok(line.startsWith(`Formal check (agent reported): malformed (${field}) — evidence not accepted: the record says ${said}, but `), line);
    assert.match(line, REPAIR); assert.doesNotMatch(line, /has no formal result|recorded —/);
  }
  for (const [formal, words] of [
    [{ result: 'not_run', scope: 'Rounding rule', reason: 'No bounded runner for this module', control_outcome: 'not_run' }, 'Not run'],
    [{ result: 'not_applicable', scope: 'Help text', reason: 'No precise rule in the Story', control_outcome: 'not_run' }, 'Not applicable'],
    [{ result: 'failed', scope: 'Rounding rule', reason: 'Counterexample found', control_outcome: 'assertion_failure', counterexample: { cents: 1205 } }, 'Failed + counterexample'],
  ]) {
    const f = fixture(t); f.manifest.formal = formal; f.save();
    const result = f.read();
    assert.equal(formalOf(result, words).status, 'recorded', words); assert.equal(result.outcome, 'not_replayed', words);
    assert.ok(f.formalLine(result).startsWith(`Formal check (agent reported): recorded — ${words}; scope: ${formal.scope}; reason: ${formal.reason}; control: `), f.formalLine(result));
    if (formal.result === 'failed') assert.match(replay.formatReplayEvidence(result), /^✗ Formal check failed/m);
  }
});

test('FORMAL3: a missing file or a file without a formal block is "missing" with its reason and one repair step', t => {
  const f = fixture(t);
  let result = f.read();
  assert.equal(formalOf(result, 'no file').status, 'missing');
  assert.equal(f.formalLine(result), 'Formal check (agent reported): missing — evidence not recorded: replay-evidence.json is missing in the run folder. Repair: write the formal block per docs/replay-evidence.md, then run pdd workflow done formal again.');
  assert.doesNotMatch(f.formalLine(result), /not recorded\.$/, 'Never a bare "not recorded" formal line.');
  delete f.manifest.formal; f.save(); result = f.read();
  assert.equal(formalOf(result, 'no formal key').status, 'missing');
  assert.ok(f.formalLine(result).startsWith('Formal check (agent reported): missing — evidence not recorded: replay-evidence.json has no formal block. Repair: '), f.formalLine(result));
  assert.ok(replay.formatReplayEvidence(result).includes(`Manifest SHA256: ${hash(readFileSync(f.path))}.`), 'pdd read the file, so it shows its hash.');
});

test('FORMAL4: a malformed file or field names the field, says what pdd did not accept and how to repair it', t => {
  for (const [change, field, said] of [
    [m => { m.formal.scope = ''; }, 'formal.scope', 'Proved (bounded)'],
    [m => { m.formal.reason = 7; }, 'formal.reason', 'Proved (bounded)'],
    [m => { m.formal.result = 'proved'; }, 'formal.result', null],
    [m => { m.formal = { result: 'failed', scope: 'Rounding', reason: 'Counterexample found', control_outcome: 'assertion_failure' }; }, 'formal.counterexample', 'Failed + counterexample'],
    [m => { m.formal.control_command = ''; m.formal.result = 'not_run'; m.formal.control_outcome = 'not_run'; }, 'formal.control_command', 'Not run'],
    [m => { m.run_id = 'another-run'; }, 'run_id', null],
    [m => { m.schema_version = 'pdd.replay-evidence.v9'; }, 'schema_version', null],
    [m => { m.source = { kind: 'git-content-v1', sha256: 'short' }; }, 'source', 'Proved (bounded)'],
    [() => '{"formal":', 'JSON', null],
  ]) {
    const f = fixture(t), text = change(f.manifest); f.save(text ?? f.manifest);
    const result = f.read(), line = f.formalLine(result);
    const formal = formalOf(result, field);
    assert.deepEqual([formal.status, formal.field], ['malformed', field], field);
    const start = `Formal check (agent reported): malformed (${field}) — evidence not accepted: ${said ? `the record says ${said}, but ` : ''}`;
    assert.ok(line.startsWith(start), `${field}: ${line}`);
    assert.match(line, REPAIR, field); assert.doesNotMatch(line, /has no formal result|SyntaxError|Unexpected/, field);
    assert.notEqual(result.outcome, 'pass', field);
  }
});

test('FORMAL5: a source change after the formal check makes the record stale, never Proved', t => {
  for (const vectors of [false, true]) {
    const f = fixture(t, { vectors }); f.save();
    assert.equal(formalOf(f.read(), `vectors=${vectors}`).status, 'recorded', `vectors=${vectors}`);
    writeFileSync(join(f.root, 'code.mjs'), 'export const add=(a,b)=>a-b;\n');
    const result = f.read(), line = f.formalLine(result);
    assert.equal(formalOf(result, `stale vectors=${vectors}`).status, 'stale'); assert.equal(result.formal.reported, 'proved_bounded');
    assert.ok(line.startsWith('Formal check (agent reported): stale (source changed) — evidence not accepted: the record says Proved (bounded), but the source changed after the record was written'), line);
    assert.match(line, /Repair: run the formal check on the current source and write its formal block with the current fingerprint, then run pdd workflow done formal again\./);
    assert.doesNotMatch(line, /recorded —/);
    // The scenario replay keeps its own honest outcome and reason.
    if (vectors) assert.deepEqual([result.outcome, result.reason], ['blocked', 'Replay evidence is stale or its source fingerprint is invalid.']);
    else assert.equal(result.outcome, 'not_replayed');
  }
});

test('FORMAL6: with scenario vectors a Proved result keeps the semantic mutation rule, also when the replay stops early', t => {
  let f = fixture(t, { vectors: true }); f.save();
  let result = f.read();
  assert.equal(result.outcome, 'pass', result.reason); assert.equal(formalOf(result, 'full replay').status, 'recorded');
  // The replay stops at a substituted vector list; pdd still reads the formal block from the same bytes.
  f.manifest.vectors = []; f.save(); result = f.read();
  assert.equal(result.outcome, 'blocked'); assert.equal(result.reason, 'The manifest changed or substituted an original vector hash.');
  assert.equal(formalOf(result, 'early exit').status, 'recorded');
  // A survived mutation is no control, even when the formal block names its own command and exit code.
  f = fixture(t, { vectors: true }); f.manifest.mutation.outcome = 'survived'; f.manifest.mutation.failed_checks = []; f.save(); result = f.read();
  assert.equal(result.outcome, 'blocked'); assert.equal(result.reason, 'A proved formal check needs semantic assertion-failure control, not a crash.');
  assert.deepEqual([formalOf(result, 'survived').status, result.formal.field, result.formal.reported], ['malformed', 'mutation', 'proved_bounded']);
  assert.ok(f.formalLine(result).startsWith('Formal check (agent reported): malformed (mutation) — evidence not accepted: the record says Proved (bounded), but '), f.formalLine(result));
  // No saved anchor: the replay is BLOCKED as before, and the formal status still says what the file holds.
  f = fixture(t); f.save(); delete f.run.replayBaseline; result = f.read();
  assert.equal(result.outcome, 'blocked'); assert.equal(formalOf(result, 'no anchor').status, 'recorded');
});

test('FORMAL7: without Rules to check in the Story the header says "not needed"; with rules it gives the status', t => {
  const f = fixture(t);
  const line = rules => shown(replay.formatReplayEvidence(f.read(), { rules }).split('\n').find(row => row.startsWith('Formal check')));
  assert.equal(line(false), 'Formal check: not needed (no Rules to check in the Story).');
  assert.match(line(true), /^Formal check \(agent reported\): missing — /); assert.match(line(undefined), /^Formal check \(agent reported\): missing — /);
  f.manifest.formal.scope = ''; f.save();
  assert.equal(line(false), 'Formal check: not needed (no Rules to check in the Story). The formal block is not accepted: malformed (formal.scope) — formal.scope must be nonblank text of at most 1000 characters.');
  f.manifest.formal.scope = 'All rules'; f.save();
  assert.match(line(false), /^Formal check \(agent reported\): recorded — Proved \(bounded\)/, 'A recorded result shows, rules or not.');
});

// The Proof table row and the status line of a code PR use the same status words as the header.
const green = (formal, records = {}) => {
  const facts = pr2Fix6(); facts.records.ci = 'passing'; facts.records.checker = { verdict: 'PASS' }; facts.pr1.merged = true;
  facts.records.replay.formal = formal; Object.assign(facts.records, records); return facts;
};
const formalRow = facts => readablePrTop(facts).text.split('\n').find(line => line.startsWith('| Formal check'));
const MISSING = { status: 'missing', cause: 'replay-evidence.json is missing in the run folder' };
const MALFORMED = { status: 'malformed', field: 'formal.scope', cause: 'formal.scope must be nonblank text of at most 1000 characters', reported: 'proved_bounded' };
const STALE = { status: 'stale', cause: 'the source changed after the record was written', reported: 'proved_bounded' };
const RECORDED = result => ({ status: 'recorded', result, scope: 'all amounts', reason: 'the reason', control_outcome: result.startsWith('proved') ? 'assertion_failure' : 'not_run' });

test('FORMAL8: with Rules to check the PR is ready only with a recorded Proved or Not applicable result', () => {
  for (const [formal, records, status] of [
    [RECORDED('proved_bounded'), {}, '✅ Ready to merge'],
    [RECORDED('proved_solver'), {}, '✅ Ready to merge'],
    [RECORDED('not_applicable'), {}, '✅ Ready to merge'],
    [RECORDED('not_run'), {}, '⛔ Blocked: formal check not run'],
    [MISSING, { formalDone: false }, '⏳ Waiting for the formal result'],
    [MISSING, { formalDone: true }, '⛔ Blocked: formal check missing'],
    [MALFORMED, { formalDone: true }, '⛔ Blocked: formal check malformed (formal.scope)'],
    [STALE, { formalDone: true }, '⛔ Blocked: formal check stale (source changed)'],
  ]) assert.equal(prStatus(green(formal, { rulesToCheck: true, ...records })), status, `${formal.status} ${formal.result ?? ''}`);
  assert.equal(formalRow(green(MISSING, { rulesToCheck: true, formalDone: true })),
    '| Formal check | missing — evidence not recorded: replay-evidence.json is missing in the run folder. Repair: write the formal block per docs/replay-evidence.md, then run pdd workflow done formal again. | — |');
  const malformed = formalRow(green(MALFORMED, { rulesToCheck: true }));
  assert.ok(malformed.startsWith('| Formal check | malformed (formal.scope) — evidence not accepted: the record says Proved (bounded), but formal.scope must be nonblank text'), malformed);
  assert.doesNotMatch(malformed, /has no formal result|Not recorded/);
  assert.ok(formalRow(green(STALE, { rulesToCheck: true })).startsWith('| Formal check | stale (source changed) — evidence not accepted: the record says Proved (bounded), but the source changed'));
  assert.equal(formalRow(green(RECORDED('proved_bounded'), { rulesToCheck: true })), '| Formal check (all amounts) | Proved (bounded) | ✗ fails (as expected) |');
});

test('FORMAL9: without Rules to check the formal check is "not needed" and does not hold the PR; a Failed result still does', () => {
  assert.equal(formalRow(green(MISSING, { rulesToCheck: false, formalDone: true })), '| Formal check | not needed (no Rules to check in the Story) | — |');
  for (const formal of [MISSING, MALFORMED, STALE, RECORDED('not_run')]) assert.equal(prStatus(green(formal, { rulesToCheck: false, formalDone: true })), '✅ Ready to merge', formal.status);
  assert.equal(formalRow(green(RECORDED('not_run'), { rulesToCheck: false })), '| Formal check (all amounts) | Not run: the reason | — |');
  const failed = green({ ...RECORDED('failed'), control_outcome: 'assertion_failure' }, { rulesToCheck: false }); failed.records.replay.counterexample = '1205';
  assert.equal(prStatus(failed), '⛔ Blocked: formal check failed at `1205`');
});
