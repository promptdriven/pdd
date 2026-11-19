import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-runner-fixture.mjs';
import {compileScenario} from '../src/scenario-compile.mjs';
import {sourceFingerprint} from '../src/workflow-replay.mjs';
import {approveRun, runStatus, stepDone} from '../src/workflow-runner.mjs';
import {readSmallChangeChecklist, stampSmallChangeChecklist} from '../src/workflow-small-change.mjs';

const CHECKLIST_FILE = 'small-change-checklist.json';
const SCHEMA_VERSION = 'pdd.small-change-checklist.v1';
const EXEMPTION = {result: 'not_applicable', scope: 'documentation-only', reason: 'DOCSSCOPE3358', control_outcome: 'not_run'};

const doneItem = (overrides = {}) => ({
  id: 'R1',
  request: 'Document the auto-stamp behavior',
  source: 'https://github.com/example/project/issues/3358',
  quote: 'Stamp run_id and source automatically on small-change-checklist.json',
  state: 'done',
  evidence: 'Verified via unit tests',
  ...overrides,
});

function pointerGet(root, pointer) {
  if (!pointer || pointer === '/') return root;
  const parts = pointer.split('/').slice(1).map(part => part.replaceAll('~1', '/').replaceAll('~0', '~'));
  let current = root;
  for (const part of parts) {
    if (current == null || typeof current !== 'object') return undefined;
    current = Array.isArray(current) ? current[Number(part)] : current[part];
  }
  return current;
}

function makeChecklistRun(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-autostamp-'));
  t.after(() => rmSync(dir, {recursive: true, force: true}));
  return dir;
}

test('3358 replays all 6 Story scenarios and 34 checks from workflow-small-change-autostamp.json', () => {
  const scenarioDoc = JSON.parse(readFileSync(new URL('./runtime/workflow-small-change-autostamp.json', import.meta.url), 'utf8'));
  const storySource = readFileSync(new URL('../user_stories/workflow-small-change-autostamp.md', import.meta.url), 'utf8');
  const {doc: compiled, refusal} = compileScenario(scenarioDoc, {
    path: 'test/runtime/workflow-small-change-autostamp.json',
    storyPath: 'user_stories/workflow-small-change-autostamp.md',
    storySource,
  });
  assert.equal(refusal, null);

  const world = structuredClone(compiled.initial_world);
  let checked = 0;

  for (const step of compiled.steps) {
    assert.equal(step.operation, 'stampSmallChangeChecklist');
    const resources = {
      'workflow-small-change-checklist-read': 0,
      'workflow-small-change-checklist-write': 0,
      'workflow-small-change-source-fingerprint': 0,
    };
    const ports = {
      checklist: {
        read({runDir}) {
          resources['workflow-small-change-checklist-read'] += 1;
          return {content: Object.hasOwn(world.raw, runDir) ? world.raw[runDir] : null};
        },
        write({runDir, record}) {
          resources['workflow-small-change-checklist-write'] += 1;
          world.stamped[runDir] = structuredClone(record);
          return {};
        },
      },
      source: {
        fingerprint({root}) {
          resources['workflow-small-change-source-fingerprint'] += 1;
          return {sha256: Object.hasOwn(world.fingerprints, root) ? world.fingerprints[root] : null};
        },
      },
    };

    const result = stampSmallChangeChecklist(step.input, ports);
    for (const check of step.checks) {
      checked += 1;
      const root = check.target === 'result' ? result
        : check.target === 'world' ? world
          : check.target === 'calls' ? {resources}
            : assert.fail(`Unsupported check target: ${check.target}`);
      const raw = pointerGet(root, check.path);
      const actual = check.op === 'count' || check.measure === 'length' ? raw?.length : raw;
      assert.ok(['equals', 'count'].includes(check.op), `${step.name ?? step.id}: unsupported check op ${check.op}`);
      assert.deepEqual(actual, check.value, `${step.name ?? step.id}: ${check.target} ${check.path}`);
    }
  }

  assert.equal(compiled.steps.length, 6);
  assert.equal(checked, 34);
});

test('3358 native filesystem stamping handles fresh, valid, stale, missing, symlink, malformed, fail-closed, and skipped cases', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  const checklistPath = join(run.runDir, CHECKLIST_FILE);
  const expectedSha = sourceFingerprint(run.root);

  // Missing file: fail-closed and never creates a checklist file.
  const missing = stampSmallChangeChecklist(run);
  assert.deepEqual(missing, {status: 'missing', stamped: false, items: [], mustFix: [{id: 'checklist', code: 'missing'}]});
  assert.equal(existsSync(checklistPath), false);

  // Fresh items-only file: auto-stamps envelope and passes readSmallChangeChecklist.
  const items = [doneItem()];
  writeFileSync(checklistPath, JSON.stringify({items}));
  const fresh = stampSmallChangeChecklist(run);
  assert.deepEqual(fresh, {status: 'recorded', stamped: true, items, mustFix: []});
  assert.deepEqual(JSON.parse(readFileSync(checklistPath, 'utf8')), {
    schema_version: SCHEMA_VERSION,
    run_id: run.runId,
    source: {kind: 'git-content-v1', sha256: expectedSha},
    items,
  });
  assert.deepEqual(readSmallChangeChecklist(run), {status: 'recorded', items, mustFix: []});

  // Already-valid envelope: no rewrite (preserve custom single-line formatting verbatim).
  const compactValid = JSON.stringify({
    schema_version: SCHEMA_VERSION,
    run_id: run.runId,
    source: {kind: 'git-content-v1', sha256: expectedSha},
    items,
  });
  writeFileSync(checklistPath, compactValid);
  const unchanged = stampSmallChangeChecklist(run);
  assert.deepEqual(unchanged, {status: 'recorded', stamped: false, items, mustFix: []});
  assert.equal(readFileSync(checklistPath, 'utf8'), compactValid);

  // Stale fingerprint + wrong run_id: refreshes envelope while keeping items verbatim.
  writeFileSync(checklistPath, JSON.stringify({
    schema_version: SCHEMA_VERSION,
    run_id: 'old-run-id',
    source: {kind: 'git-content-v1', sha256: '0'.repeat(64)},
    items,
  }));
  const refreshed = stampSmallChangeChecklist(run);
  assert.deepEqual(refreshed, {status: 'recorded', stamped: true, items, mustFix: []});
  assert.equal(JSON.parse(readFileSync(checklistPath, 'utf8')).run_id, run.runId);
  assert.equal(JSON.parse(readFileSync(checklistPath, 'utf8')).source.sha256, expectedSha);

  // Fail-closed item and evidence findings remain visible after stamping mechanical fields.
  for (const [badItem, code] of [
    [doneItem({evidence: '   '}), 'missing-evidence'],
    [doneItem({state: 'pending', evidence: undefined}), 'pending-request'],
    [doneItem({state: 'excluded', evidence: undefined, exclusion: {reason: 'later', quote: ''}}), 'unsupported-exclusion'],
  ]) {
    writeFileSync(checklistPath, JSON.stringify({items: [badItem]}));
    const checked = stampSmallChangeChecklist(run);
    assert.equal(checked.status, 'recorded');
    assert.equal(checked.stamped, true);
    assert.deepEqual(checked.mustFix, [{id: 'R1', code}]);
    assert.deepEqual(readSmallChangeChecklist(run).mustFix, [{id: 'R1', code}]);
  }

  // Malformed cases leave file bytes untouched and return malformed with 0 writes.
  for (const [label, payload, runOverride] of [
    ['invalid JSON', '{broken json', {}],
    ['empty items', JSON.stringify({items: []}), {}],
    ['duplicate id', JSON.stringify({items: [doneItem(), doneItem({request: 'Other'})]}), {}],
    ['missing quote', JSON.stringify({items: [doneItem({quote: ' '})]}), {}],
    ['invalid state', JSON.stringify({items: [doneItem({state: 'skipped'})]}), {}],
    ['unsupported schema_version', JSON.stringify({schema_version: 'pdd.small-change-checklist.v2', items}), {}],
    ['blank runId', JSON.stringify({items}), {runId: '   '}],
    ['oversized > 1 MiB', JSON.stringify({items: [doneItem({evidence: 'e'.repeat(1024 * 1024 + 32)})]}), {}],
  ]) {
    writeFileSync(checklistPath, payload);
    const bad = stampSmallChangeChecklist({...run, ...runOverride});
    assert.deepEqual(bad, {status: 'malformed', stamped: false, items: [], mustFix: [{id: 'checklist', code: 'malformed'}]}, label);
    assert.equal(readFileSync(checklistPath, 'utf8'), payload, `${label} must not rewrite file`);
  }

  // Symlink refusal: never follow or overwrite symlink target.
  const outsideDir = makeChecklistRun(t);
  const targetPath = join(outsideDir, 'target.json');
  const targetRaw = JSON.stringify({items});
  writeFileSync(targetPath, targetRaw);
  const linkDir = makeChecklistRun(t);
  symlinkSync(targetPath, join(linkDir, CHECKLIST_FILE));
  const symlinkResult = stampSmallChangeChecklist({...run, runDir: linkDir});
  assert.deepEqual(symlinkResult, {status: 'malformed', stamped: false, items: [], mustFix: [{id: 'checklist', code: 'malformed'}]});
  assert.equal(readFileSync(targetPath, 'utf8'), targetRaw);

  // Unreadable git fingerprint fails closed as stale without mutating file.
  const nonGitRoot = makeChecklistRun(t);
  const itemsOnly = JSON.stringify({items});
  writeFileSync(checklistPath, itemsOnly);
  const unreadable = stampSmallChangeChecklist({...run, root: nonGitRoot});
  assert.deepEqual(unreadable, {status: 'stale', stamped: false, items: [], mustFix: [{id: 'checklist', code: 'stale'}]});
  assert.equal(readFileSync(checklistPath, 'utf8'), itemsOnly);

  // Non-small-change workflows skip without reading or writing disk.
  for (const workflow of ['feature', 'bug']) {
    const skipped = stampSmallChangeChecklist({...run, workflow});
    assert.deepEqual(skipped, {status: 'skipped', stamped: false, items: [], mustFix: []});
    assert.equal(readFileSync(checklistPath, 'utf8'), itemsOnly);
  }
});

test('3358 stepDone auto-stamps small-change checklist on scope and refreshes after late edits before formal publication', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  const checklistPath = join(run.runDir, CHECKLIST_FILE);
  const items = [doneItem()];

  writeFileSync(join(run.root, 'README.md'), 'Initial small-change doc\n');
  f.git(run.root, 'add', '.');
  f.git(run.root, 'commit', '-qm', 'Initial doc edit');
  const firstSha = sourceFingerprint(run.root);

  // Write items-only checklist (no schema_version, run_id, or source).
  writeFileSync(checklistPath, JSON.stringify({items}));
  assert.equal((await stepDone({step: 'scope', cwd: run.root, summary: 'Scoped requests'}, f.ports)).exitCode, 0);

  const afterScope = JSON.parse(readFileSync(checklistPath, 'utf8'));
  assert.equal(afterScope.schema_version, SCHEMA_VERSION);
  assert.equal(afterScope.run_id, run.runId);
  assert.deepEqual(afterScope.source, {kind: 'git-content-v1', sha256: firstSha});
  assert.deepEqual(afterScope.items, items);

  assert.equal((await approveRun({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  assert.equal((await stepDone({step: 'change', cwd: run.root, summary: 'Applied change'}, f.ports)).exitCode, 0);
  assert.equal((await stepDone({step: 'verify', cwd: run.root, summary: 'Verified change'}, f.ports)).exitCode, 0);

  // Late edit after verify: update replay-evidence.json, intentionally leave small-change-checklist.json stale.
  writeFileSync(join(run.root, 'README.md'), 'Initial small-change doc\nLate clarification\n');
  f.git(run.root, 'add', '.');
  f.git(run.root, 'commit', '-qm', 'Late doc tweak');
  const lateSha = sourceFingerprint(run.root);
  assert.notEqual(lateSha, firstSha);
  assert.equal(readSmallChangeChecklist(run).status, 'stale');

  writeFileSync(join(run.runDir, 'replay-evidence.json'), JSON.stringify({
    schema_version: 'pdd.replay-evidence.v1',
    run_id: run.runId,
    source: {kind: 'git-content-v1', sha256: lateSha},
    formal: EXEMPTION,
  }));

  const formal = await stepDone({step: 'formal', cwd: run.root, summary: 'Formal exemption saved'}, f.ports);
  assert.equal(formal.exitCode, 0, formal.message);
  assert.equal(f.prs.length, 1);

  // Disk file refreshed to lateSha and saved status reports recorded with 0 must-fix findings.
  assert.equal(JSON.parse(readFileSync(checklistPath, 'utf8')).source.sha256, lateSha);
  const status = await runStatus({cwd: f.source, json: true}, f.ports);
  assert.equal(status.exitCode, 0, status.message);
  const checklist = JSON.parse(status.message).runs[0].smallChange.checklist;
  assert.equal(checklist.status, 'recorded');
  assert.deepEqual(checklist.mustFix, []);

  // A post-done edit without re-running stepDone still turns read-only readSmallChangeChecklist stale without mutating disk.
  writeFileSync(join(run.root, 'README.md'), 'Post-done edit\n');
  assert.equal(readSmallChangeChecklist(run).status, 'stale');
  assert.equal(JSON.parse(readFileSync(checklistPath, 'utf8')).source.sha256, lateSha);
});

test('3358 stepDone keeps fail-closed missing-evidence findings on small-change and leaves feature runs untouched', async t => {
  // Small-change fail-closed on missing evidence.
  const sc = await fixture(t);
  assert.equal((await sc.run()).exitCode, 0);
  const scRun = sc.record();
  writeFileSync(join(scRun.runDir, CHECKLIST_FILE), JSON.stringify({items: [doneItem({evidence: ''})]}));
  assert.equal((await stepDone({step: 'scope', cwd: scRun.root, summary: 'Scoped'}, sc.ports)).exitCode, 0);
  const scStatus = await runStatus({cwd: sc.source, json: true}, sc.ports);
  const scChecklist = JSON.parse(scStatus.message).runs[0].smallChange.checklist;
  assert.equal(scChecklist.status, 'recorded');
  assert.deepEqual(scChecklist.mustFix, [{id: 'R1', code: 'missing-evidence'}]);

  // Feature workflow: stepDone does not touch small-change-checklist.json.
  const feat = await fixture(t, {name: 'feature'});
  assert.equal((await feat.run()).exitCode, 0);
  const featRun = feat.record();
  const untouched = JSON.stringify({items: [doneItem()]});
  const featChecklistPath = join(featRun.runDir, CHECKLIST_FILE);
  writeFileSync(featChecklistPath, untouched);
  const featDone = await stepDone({step: 'story', cwd: featRun.root, summary: 'Drafted story'}, feat.ports);
  assert.equal(featDone.exitCode, 0, featDone.message);
  assert.equal(readFileSync(featChecklistPath, 'utf8'), untouched);
});
