import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync, symlinkSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { freezeReplayVectors, sourceFingerprint, readCodeReplay, codeReplayLine } from '../src/code-replay.mjs';

function fixture(t) {
  const base = mkdtempSync(join(tmpdir(), 'pdd-replay-')), root = join(base, 'repo'), runDir = join(base, 'run');
  mkdirSync(root); mkdirSync(runDir); t.after(() => rmSync(base, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: root });
  const check = { criterion_id: 'AC1', target: 'result', path: '/value', op: 'equals', value: 2 };
  const step = { step_id: 'get-value', entry_path: 'prompts/value.prompt.md', operation: 'read', input: {}, checks: [check] };
  const scenario = { schema_version: 'prompt-runtime.program-scenario.v1', criteria: [{ id: 'AC1', text: 'Get two' }], initial_world: {}, steps: [step] };
  writeFileSync(join(root, 'vectors.json'), JSON.stringify(scenario));
  writeFileSync(join(root, 'code.mjs'), 'export const value = 2;\n');
  const baseline = freezeReplayVectors(root), mutation = { kind: 'semantic', command: 'node --test mutated.test.mjs', assertion_failures: 1, crashed: false };
  const doc = { schema_version: 'code-replay-v1', source_sha256: sourceFingerprint(root),
    vectors: [{ ...baseline.vectors[0], steps: [{ step_id: step.step_id, operation: step.operation,
      execution: { executed: true, boundary: 'code.mjs:value', command: 'node --test vectors.test.mjs' }, checks: [{ ...check, status: 'pass', actual: 2 }] }] }],
    mutation, formal: { status: 'proved_bounded', rule: 'Value is two', bounds: 'Every integer from 0 through 3', command: 'node --test formal.test.mjs', control: mutation } };
  const f = { root, runDir, baseline, doc, scenario };
  f.save = () => writeFileSync(join(runDir, 'code-replay.json'), JSON.stringify(doc));
  f.read = () => { f.save(); return readCodeReplay(f); };
  return f;
}

test('complete unchanged vectors and source produce exact agent-reported counts, independent of commits', t => {
  const f = fixture(t), out = f.read();
  assert.equal(out.status, 'pass'); assert.equal(out.execution_evidence, 'agent_reported');
  assert.deepEqual(out.counts, { pass: 1, fail: 0, blocked: 0, not_replayed: 0, total: 1, operations: 1, executed: 1 });
  assert.match(codeReplayLine(out), /^Code replay: PASS.*agent-reported/);
  execFileSync('git', ['add', '.'], { cwd: f.root });
  assert.equal(f.read().status, 'pass');
});

test('assertion and formal failures remain publishable FAIL outcomes', t => {
  const f = fixture(t); f.doc.vectors[0].steps[0].checks[0].status = 'fail'; f.doc.vectors[0].steps[0].checks[0].reason = 'Expected two, got three';
  assert.equal(f.read().status, 'fail'); assert.equal(f.read().counts.fail, 1);
  f.doc.vectors[0].steps[0].checks[0].status = 'pass'; f.doc.formal = { status: 'failed', rule: 'Value is two', counterexample: 'input=0 returns 3' };
  assert.equal(f.read().status, 'fail');
});

for (const [name, change] of [
  ['missing execution', f => { f.doc.vectors[0].steps[0].execution.executed = false; }],
  ['unmapped check', f => { f.doc.vectors[0].steps[0].checks[0].status = 'not_replayed'; f.doc.vectors[0].steps[0].checks[0].reason = 'No world binding'; }],
]) test(`${name} is NOT REPLAYED even beside a PASS claim`, t => { const f = fixture(t); change(f); assert.equal(f.read().status, 'not_replayed'); assert.equal(f.read().counts.pass, 0); });

for (const [name, change] of [
  ['missing observed value', f => { delete f.doc.vectors[0].steps[0].checks[0].actual; }],
  ['empty report', f => { f.doc.vectors = []; }],
  ['missing check', f => { f.doc.vectors[0].steps[0].checks = []; }],
  ['duplicate vector', f => { f.doc.vectors.push(f.doc.vectors[0]); }],
  ['wrong operation', f => { f.doc.vectors[0].steps[0].operation = 'other'; }],
  ['wrong check', f => { f.doc.vectors[0].steps[0].checks[0].path = '/other'; }],
  ['stale source', f => { writeFileSync(join(f.root, 'code.mjs'), 'export const value = 3;'); }],
  ['changed original vector', f => { writeFileSync(join(f.root, 'vectors.json'), JSON.stringify({ ...f.scenario, initial_world: { altered: true } })); f.doc.source_sha256 = sourceFingerprint(f.root); }],
  ['missing original vector', f => { rmSync(join(f.root, 'vectors.json')); f.doc.source_sha256 = sourceFingerprint(f.root); }],
  ['mutation crash', f => { f.doc.mutation = { ...f.doc.mutation, crashed: true }; }],
  ['empty mutation command', f => { f.doc.mutation = { ...f.doc.mutation, command: '' }; }],
  ['no semantic detection', f => { f.doc.mutation = { ...f.doc.mutation, assertion_failures: 0 }; }],
  ['formal missing', f => { delete f.doc.formal; }],
  ['formal control crash', f => { f.doc.formal.control = { ...f.doc.formal.control, crashed: true }; }],
  ['formal not run', f => { f.doc.formal = { status: 'not_run', rule: 'Value is two', reason: 'No checker' }; }],
  ['blocked check', f => { f.doc.vectors[0].steps[0].checks[0].status = 'blocked'; f.doc.vectors[0].steps[0].checks[0].reason = 'Unavailable'; }],
]) test(`${name} cannot produce PASS`, t => { const f = fixture(t); change(f); assert.equal(f.read().status, 'blocked'); });

test('missing or oversized manifests, symlink vectors and absent baselines cannot pass', t => {
  const f = fixture(t);
  assert.equal(readCodeReplay(f).status, 'blocked');
  f.baseline = null; assert.equal(f.read().status, 'blocked'); f.baseline = freezeReplayVectors(f.root);
  f.save(); writeFileSync(join(f.runDir, 'code-replay.json'), ' '.repeat(2 * 1024 * 1024 + 1)); assert.equal(readCodeReplay(f).status, 'blocked');
  const original = readFileSync(join(f.root, 'vectors.json')); rmSync(join(f.root, 'vectors.json')); writeFileSync(join(f.runDir, 'outside.json'), original); symlinkSync(join(f.runDir, 'outside.json'), join(f.root, 'vectors.json'));
  assert.equal(freezeReplayVectors(f.root).vectors.length, 0);
});

test('formal not-applicable with reason is honest and does not imply proof', t => {
  const f = fixture(t); f.doc.formal = { status: 'not_applicable', rule: 'Plain constant wiring', reason: 'No approved formal rule' };
  assert.equal(f.read().status, 'pass'); assert.equal(f.read().formal_status, 'not_applicable');
});

test('committed baseline ignores dirty and untracked expectations; later reads block their changed bytes', t => {
  const f = fixture(t);
  execFileSync('git', ['add', '.'], { cwd: f.root });
  execFileSync('git', ['-c', 'user.name=Replay Test', '-c', 'user.email=replay@example.invalid', 'commit', '-qm', 'original vectors'], { cwd: f.root });
  const original = freezeReplayVectors(f.root, { committed: true });
  writeFileSync(join(f.root, 'vectors.json'), JSON.stringify({ ...f.scenario, initial_world: { dirty: true } }));
  writeFileSync(join(f.root, 'extra.json'), JSON.stringify(f.scenario));
  const frozen = freezeReplayVectors(f.root, { committed: true });
  assert.deepEqual(frozen, original); assert.equal(frozen.vectors.length, 1);
  f.baseline = frozen; f.doc.source_sha256 = sourceFingerprint(f.root);
  assert.equal(f.read().status, 'blocked');
  rmSync(join(f.root, 'vectors.json'));
  assert.deepEqual(freezeReplayVectors(f.root, { committed: true }), original);
});

test('malformed original check fields cannot match absent replay fields to produce PASS', t => {
  const f = fixture(t);
  f.scenario.steps[0].checks = [{ target: 'result' }];
  writeFileSync(join(f.root, 'vectors.json'), JSON.stringify(f.scenario));
  f.baseline = freezeReplayVectors(f.root);
  f.doc.vectors[0].sha256 = f.baseline.vectors[0].sha256;
  f.doc.vectors[0].steps[0].checks = [{ target: 'result', status: 'pass', actual: 2 }];
  f.doc.source_sha256 = sourceFingerprint(f.root);
  assert.equal(f.read().status, 'blocked');
});

test('numeric overflow in parsed JSON observations and unsupported original schema never pass', t => {
  const f = fixture(t); f.save();
  const path = join(f.runDir, 'code-replay.json');
  writeFileSync(path, readFileSync(path, 'utf8').replace('"actual":2', '"actual":1e999'));
  assert.equal(readCodeReplay(f).status, 'blocked');
  f.scenario.schema_version = 'prompt-runtime.program-scenario.v999';
  writeFileSync(join(f.root, 'vectors.json'), JSON.stringify(f.scenario));
  assert.equal(freezeReplayVectors(f.root).vectors.length, 0);
});

test('unrelated committed JSON mentioning scenario terminology does not poison original inventory', t => {
  const f = fixture(t);
  writeFileSync(join(f.root, 'metadata.json'), JSON.stringify({ description: 'prompt-runtime.program-scenario' }));
  execFileSync('git', ['add', '.'], { cwd: f.root });
  execFileSync('git', ['-c', 'user.name=Replay Test', '-c', 'user.email=replay@example.invalid', 'commit', '-qm', 'original vectors and metadata'], { cwd: f.root });
  const baseline = freezeReplayVectors(f.root, { committed: true });
  assert.equal(baseline.error, undefined); assert.equal(baseline.vectors.length, 1);
  assert.equal(baseline.vectors[0].path, 'vectors.json');
});
