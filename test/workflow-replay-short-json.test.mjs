import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { linkSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { pinReplayVectors, pinRunAnchor, readReplayEvidence, sourceFingerprint, adoptReplayCorpus } from '../src/workflow-replay.mjs';

const hash = bytes => createHash('sha256').update(bytes).digest('hex');

function makeRepo(t, entries, { commitMessage = 'init' } = {}) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-short-replay-')));
  t.after(() => rmSync(base, { recursive: true, force: true }));
  const root = join(base, 'repo');
  const runDir = join(base, 'run');
  mkdirSync(root, { recursive: true });
  mkdirSync(runDir, { recursive: true });
  const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8' }).trim();
  git('init', '-q');
  for (const [rel, body] of Object.entries(entries)) {
    const abs = join(root, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, typeof body === 'string' ? body : `${JSON.stringify(body, null, 2)}\n`);
  }
  git('add', '.');
  git('-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '-qm', commitMessage);
  return { base, root, runDir, git };
}

test('3576: pinReplayVectors, readReplayEvidence, and pinRunAnchor accept native Short JSON scenarios with omitted schema_version/story_path/criteria and BigInt values', t => {
  const shortScenario = `{
  "entry_path": "prompts/counter.prompt.md",
  "seeds": { "base": { "count": 9007199254740993 } },
  "steps": [
    {
      "id": "inc",
      "op": "increment",
      "from": "base",
      "checks": {
        "1": [["result", "/count", "=", 9007199254740994]]
      }
    }
  ]
}
`;
  const f = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync increment({ count }) -> { count }`.\n\n## Domain decisions\n\nAdd 1 to `count`.\n\n## Dependencies\n\nNone.\n',
    'user_stories/counter.md': '# Increment counter\n\nAs a clerk counting items, I want to add 1 to the count, so that the total stays exact.\n\n## Acceptance criteria\n\n1. Adding 1 to 9007199254740993 returns 9007199254740994.\n',
    'tests/counter.json': shortScenario,
    'src/counter.mjs': '// Generated from prompts/counter.prompt.md\nexport const increment = ({ count }) => ({ count: count + 1n });\n',
  });

  const anchor = pinReplayVectors(f.root, ['tests/counter.json']);
  assert.equal(anchor.outcome, undefined, anchor.reason);
  assert.equal(anchor.vectors.length, 1);
  const vec = anchor.vectors[0];
  assert.equal(vec.sha256, hash(readFileSync(join(f.root, 'tests/counter.json'))));
  assert.equal(vec.steps.length, 1);
  assert.equal(vec.steps[0].step_id, 'inc');
  assert.equal(vec.steps[0].entry_path, 'prompts/counter.prompt.md');
  assert.equal(vec.steps[0].operation, 'increment');
  assert.equal(vec.checks.length, 1);
  assert.match(vec.checks[0].criterion_id, /^ac-sha256-[a-f0-9]{48}$/);
  assert.deepEqual(
    vec.exact_integers.map(r => r.value).sort(),
    ['9007199254740993', '9007199254740994'],
    'exact BigInt strings retained across Short JSON compile',
  );

  const run = { root: f.root, runDir: f.runDir, runId: 'short-replay-1', replayBaseline: anchor };
  const checkRow = { ...vec.checks[0], outcome: 'pass' };
  const manifest = {
    schema_version: 'pdd.replay-evidence.v1',
    run_id: run.runId,
    source: { kind: 'git-content-v1', sha256: sourceFingerprint(f.root) },
    vectors: [{ path: 'tests/counter.json', sha256: vec.sha256 }],
    checks: [checkRow],
    operations: [{
      vector: 'tests/counter.json',
      step_id: 'inc',
      entry_path: 'prompts/counter.prompt.md',
      operation: 'increment',
      executed: true,
      outcome: 'returned',
      boundary: { kind: 'function', name: 'increment' },
      command: 'node test/counter.vectors.test.mjs',
      exit_code: 0,
    }],
    counts: { total: 1, pass: 1, fail: 0, blocked: 0, not_replayed: 0 },
    mutation: {
      kind: 'semantic',
      description: 'Add 2 instead of 1',
      command: 'node test/counter.vectors.test.mjs --mutant',
      exit_code: 1,
      outcome: 'assertion_failure',
      failed_checks: [{ vector: 'tests/counter.json', step_id: 'inc', check_index: 0 }],
    },
    formal: {
      result: 'not_applicable',
      scope: 'Counter increment',
      reason: 'No additional formal rule approved',
      control_outcome: 'not_run',
    },
  };
  writeFileSync(join(f.runDir, 'replay-evidence.json'), JSON.stringify(manifest));
  const replay = readReplayEvidence(run);
  assert.equal(replay.outcome, 'pass', replay.reason);

  const baseCommit = f.git('rev-parse', 'HEAD');
  const runAnchor = pinRunAnchor(f.root, {
    paths: [],
    commit: baseCommit,
    changed: ['src/counter.mjs'],
    scenarios: [],
    codeSpace: true,
  });
  assert.equal(runAnchor.outcome, undefined, runAnchor.reason);
  assert.equal(runAnchor.vectors.length, 1);
  assert.equal(runAnchor.vectors[0].path, 'tests/counter.json');
  assert.equal(runAnchor.vectors[0].base, baseCommit);
});

test('3576: pinReplayVectors and adoptReplayCorpus fail closed on invalid JSON and malformed Short JSON', async t => {
  const fSyntax = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\nAs a clerk, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.json': '{ not valid json',
  });
  fSyntax.git('remote', 'add', 'origin', 'https://github.com/promptdriven/pdd.git');
  const badPin = pinReplayVectors(fSyntax.root, ['tests/counter.json']);
  assert.equal(badPin.outcome, 'blocked');
  assert.match(badPin.reason, /JSON|property name|token|Expected/i);

  const declSyntax = join(fSyntax.base, 'adoption-syntax.json');
  writeFileSync(declSyntax, JSON.stringify({
    schema_version: 'pdd.replay-adoption.v1',
    repository: 'promptdriven/pdd',
    commit: fSyntax.git('rev-parse', 'HEAD'),
    prompts: ['prompts/counter.prompt.md'],
    scenarios: ['tests/counter.json'],
    approval: { kind: 'external-human-assertion', reference: 'PR #1', asserted_by: 'alice' },
  }));
  const badAdopt = await adoptReplayCorpus(fSyntax.root, declSyntax);
  assert.equal(badAdopt.outcome, 'blocked');

  const fBadShort = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\nAs a clerk, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '9': [['result', '/count', '=', 1]] } }],
    },
  });
  const anchor = pinReplayVectors(fBadShort.root, ['tests/counter.json']);
  assert.equal(anchor.outcome, 'blocked');
  assert.match(anchor.reason, /exceeds/i);
});

test('3576: adoptReplayCorpus accepts native Short JSON scenarios and pins paired Story into context', async t => {
  const f = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc({ count }) -> { count }`.\n\n## Domain decisions\n\nReturn `count + 1`.\n\n## Dependencies\n\nNone.\n',
    'user_stories/counter.md': '# Increment\n\nAs a clerk, I want to increment, so that the count rises.\n\n## Acceptance criteria\n\n1. Incrementing 0 returns 1.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', input: { count: 0 }, checks: { '1': [['result', '/count', '=', 1]] } }],
    },
  });
  f.git('remote', 'add', 'origin', 'https://github.com/promptdriven/pdd.git');
  const commit = f.git('rev-parse', 'HEAD');
  const declPath = join(f.base, 'adoption.json');
  writeFileSync(declPath, JSON.stringify({
    schema_version: 'pdd.replay-adoption.v1',
    repository: 'promptdriven/pdd',
    commit,
    prompts: ['prompts/counter.prompt.md'],
    scenarios: ['tests/counter.json'],
    approval: { kind: 'external-human-assertion', reference: 'PR #1', asserted_by: 'alice' },
  }));
  const adopted = await adoptReplayCorpus(f.root, declPath);
  assert.equal(adopted.outcome, 'adopted', `${adopted.reason} ${adopted.cause}`);
  assert.deepEqual(adopted.paths, ['tests/counter.json']);

  writeFileSync(join(f.root, 'user_stories/counter.md'), '# Increment\n\nAs a clerk, I want to increment, so that totals differ.\n\n## Acceptance criteria\n\n1. Incrementing 0 returns 2.\n');
  const afterStoryEdit = await adoptReplayCorpus(f.root, declPath);
  assert.equal(afterStoryEdit.outcome, 'blocked');
  assert.match(`${afterStoryEdit.reason} ${afterStoryEdit.cause}`, /changed|mismatch|drift/i);
});

test('3576: Short JSON replay fails closed on symlinked, hardlinked, missing, invalid story_path, and preserves legacy v1 verbatim', t => {
  const fLegacy = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\nAs a clerk, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.json': {
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/counter.md',
      steps: [{ step_id: 's1', entry_path: 'prompts/counter.prompt.md', operation: 'inc', input: {}, checks: [{ criterion_id: 'AC1', target: 'result', path: '/count', op: 'equals', value: 1 }] }],
    },
  });
  const legacyAnchor = pinReplayVectors(fLegacy.root, ['tests/counter.json']);
  assert.equal(legacyAnchor.outcome, undefined, legacyAnchor.reason);
  assert.equal(legacyAnchor.vectors[0].checks[0].criterion_id, 'AC1');

  const fBadStoryPath = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\nAs a clerk, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.json': {
      story_path: '../outside.md',
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '1': [['result', '/count', '=', 1]] } }],
    },
  });
  const badPathAnchor = pinReplayVectors(fBadStoryPath.root, ['tests/counter.json']);
  assert.equal(badPathAnchor.outcome, 'blocked');
  assert.match(badPathAnchor.reason, /story_path|canonical/i);

  const fMissingStory = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '1': [['result', '/count', '=', 1]] } }],
    },
  });
  const missingStoryAnchor = pinReplayVectors(fMissingStory.root, ['tests/counter.json']);
  assert.equal(missingStoryAnchor.outcome, 'blocked');
  assert.match(missingStoryAnchor.reason, /paired Story/i);

  const fSymlink = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '1': [['result', '/count', '=', 1]] } }],
    },
  });
  const externalStory = join(fSymlink.base, 'ext-story.md');
  writeFileSync(externalStory, '# Counter\n\n## Acceptance criteria\n\n1. Inc returns 1.\n');
  mkdirSync(join(fSymlink.root, 'user_stories'), { recursive: true });
  symlinkSync(externalStory, join(fSymlink.root, 'user_stories/counter.md'));
  fSymlink.git('add', 'user_stories/counter.md');
  const symlinkAnchor = pinReplayVectors(fSymlink.root, ['tests/counter.json']);
  assert.equal(symlinkAnchor.outcome, 'blocked');

  const fHardlink = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '1': [['result', '/count', '=', 1]] } }],
    },
  });
  linkSync(join(fHardlink.root, 'user_stories/counter.md'), join(fHardlink.base, 'hardlink-story.md'));
  const hardlinkAnchor = pinReplayVectors(fHardlink.root, ['tests/counter.json']);
  assert.equal(hardlinkAnchor.outcome, 'blocked');

  const fNested = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/sub/counter.md': '# Counter\n\nAs a clerk, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.edge.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '1': [['result', '/count', '=', 1]] } }],
    },
  });
  const nestedAnchor = pinReplayVectors(fNested.root, ['tests/counter.edge.json']);
  assert.equal(nestedAnchor.outcome, undefined, nestedAnchor.reason);
  assert.equal(nestedAnchor.vectors[0].snapshot.story_path, 'user_stories/sub/counter.md');
  writeFileSync(join(fNested.root, 'user_stories/sub/counter.md'), '# Counter\n\nAs a clerk, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Inc returns 2.\n');
  const replay = readReplayEvidence({ root: fNested.root, runDir: fNested.runDir, runId: 'story-edit-1', replayBaseline: nestedAnchor });
  assert.ok(replay.warnings.length > 0, 'editing paired Story in code space must emit saved-value warning even when Short JSON bytes are unchanged');

  const fAmbiguous = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/a.md': '# A\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'user_stories/a.b.md': '# A B\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/a.b.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '1': [['result', '/count', '=', 1]] } }],
    },
  });
  const ambAnchor = pinReplayVectors(fAmbiguous.root, ['tests/a.b.json']);
  assert.equal(ambAnchor.outcome, 'blocked');
  assert.match(ambAnchor.reason, /multiple Stories/i);

  const fPadded = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.json': {
      story_path: ' user_stories/counter.md ',
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '1': [['result', '/count', '=', 1]] } }],
    },
  });
  const paddedAnchor = pinReplayVectors(fPadded.root, ['tests/counter.json']);
  assert.equal(paddedAnchor.outcome, 'blocked');
  assert.match(paddedAnchor.reason, /canonical/i);

  const fBrokenBase = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.json': {
      schema_version: 'pdd.scenario.short.v1',
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '9': [['result', '/count', '=', 1]] } }],
    },
    'src/counter.mjs': '// Generated from prompts/counter.prompt.md\nexport const inc = () => ({ count: 1 });\n',
  });
  const baseSha = fBrokenBase.git('rev-parse', 'HEAD');
  const linkedBroken = pinRunAnchor(fBrokenBase.root, {
    paths: [],
    commit: baseSha,
    changed: ['src/counter.mjs'],
    scenarios: [],
    codeSpace: true,
  });
  assert.equal(linkedBroken.outcome, 'blocked');
  assert.match(linkedBroken.reason, /exceeds|counter\.json/i);

  writeFileSync(join(fBrokenBase.root, 'pdd.json'), JSON.stringify({ replay: { base_scenarios: 'all' } }));
  writeFileSync(join(fBrokenBase.root, 'tests/counter.json'), JSON.stringify({
    schema_version: 'prompt-runtime.program-scenario.v1',
    entry_path: 'prompts/counter.prompt.md',
    steps: [{ id: 's1', op: 'inc', checks: { '9': [['result', '/count', '=', 1]] } }],
  }));
  fBrokenBase.git('add', 'pdd.json', 'tests/counter.json');
  fBrokenBase.git('-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'all-mode-hybrid-v1');
  const allBaseSha = fBrokenBase.git('rev-parse', 'HEAD');
  const allBroken = pinRunAnchor(fBrokenBase.root, {
    paths: [],
    commit: allBaseSha,
    changed: ['README.md'],
    scenarios: [],
    codeSpace: true,
  });
  assert.equal(allBroken.outcome, 'blocked');
  assert.match(allBroken.reason, /exceeds|counter\.json/i);
});

test('3576 R1-1: broken schema-versionless native Short JSON on base commit fails closed on code and Story-only changes while skipping unrelated JSON', t => {
  const fNativeBroken = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\nAs a clerk, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '9': [['result', '/count', '=', 1]] } }],
    },
    'tests/unrelated-wizard.json': {
      steps: [{ name: 'welcome' }],
    },
    'src/counter.mjs': '// Generated from prompts/counter.prompt.md\nexport const inc = () => ({ count: 1 });\n',
  });
  const baseSha = fNativeBroken.git('rev-parse', 'HEAD');

  const codeChangeBlocked = pinRunAnchor(fNativeBroken.root, {
    paths: [],
    commit: baseSha,
    changed: ['src/counter.mjs'],
    scenarios: [],
    codeSpace: true,
  });
  assert.equal(codeChangeBlocked.outcome, 'blocked');
  assert.match(codeChangeBlocked.reason, /tests\/counter\.json.*exceeds/i);

  const storyOnlyBlocked = pinRunAnchor(fNativeBroken.root, {
    paths: [],
    commit: baseSha,
    changed: ['user_stories/counter.md'],
    scenarios: [],
    codeSpace: true,
  });
  assert.equal(storyOnlyBlocked.outcome, 'blocked');
  assert.match(storyOnlyBlocked.reason, /tests\/counter\.json.*exceeds/i);

  const fUnrelatedOnly = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\nAs a clerk, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '1': [['result', '/count', '=', 1]] } }],
    },
    'tests/unrelated-wizard.json': {
      steps: [{ name: 'welcome' }],
    },
    'src/counter.mjs': '// Generated from prompts/counter.prompt.md\nexport const inc = () => ({ count: 1 });\n',
  });
  const okSha = fUnrelatedOnly.git('rev-parse', 'HEAD');
  const okAnchor = pinRunAnchor(fUnrelatedOnly.root, {
    paths: [],
    commit: okSha,
    changed: ['src/counter.mjs'],
    scenarios: [],
    codeSpace: true,
  });
  assert.equal(okAnchor.outcome, undefined, okAnchor.reason);
  assert.deepEqual(okAnchor.vectors.map(v => v.path), ['tests/counter.json']);
});

test('3576 R1-2: compileIfShort fails closed on 0-AC Stories, missing-Story shorthand criteria, duplicate Story criteria, and stale/mismatched ac-sha256 hashes', t => {
  const fZeroAc = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\nAs a clerk, I want to count, so that totals match.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '1': [['result', '/count', '=', 1]] } }],
    },
  });
  const zeroAnchor = pinReplayVectors(fZeroAc.root, ['tests/counter.json']);
  assert.equal(zeroAnchor.outcome, 'blocked');
  assert.match(zeroAnchor.reason, /no acceptance criteria/i);

  const fShorthandStr = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      criteria: ['AC1'],
      steps: [{ id: 's1', op: 'inc', checks: [{ criterion_id: 'AC1', target: 'result', path: '/count', op: '=', value: 1 }] }],
    },
  });
  const shorthandStrAnchor = pinReplayVectors(fShorthandStr.root, ['tests/counter.json']);
  assert.equal(shorthandStrAnchor.outcome, 'blocked');
  assert.match(shorthandStrAnchor.reason, /shorthand criteria|invalid|unbound/i);

  const fShorthandIdObj = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      criteria: [{ id: 'AC1' }],
      steps: [{ id: 's1', op: 'inc', checks: [{ criterion_id: 'AC1', target: 'result', path: '/count', op: '=', value: 1 }] }],
    },
  });
  const shorthandObjAnchor = pinReplayVectors(fShorthandIdObj.root, ['tests/counter.json']);
  assert.equal(shorthandObjAnchor.outcome, 'blocked');
  assert.match(shorthandObjAnchor.reason, /shorthand criteria|invalid|unbound/i);

  const fDupStory = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\nAs a clerk, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Inc returns 1.\n2. Inc returns 1.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      steps: [{ id: 's1', op: 'inc', checks: { '1': [['result', '/count', '=', 1]] } }],
    },
  });
  const dupAnchor = pinReplayVectors(fDupStory.root, ['tests/counter.json']);
  assert.equal(dupAnchor.outcome, 'blocked');
  assert.match(dupAnchor.reason, /duplicate/i);

  const fStaleHash = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\nAs a clerk, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      criteria: [{ id: 'ac-sha256-000000000000000000000000000000000000000000000000', text: 'Inc returns 1.' }],
      steps: [{ id: 's1', op: 'inc', checks: [{ criterion_id: 'ac-sha256-000000000000000000000000000000000000000000000000', target: 'result', path: '/count', op: '=', value: 1 }] }],
    },
  });
  const staleHashAnchor = pinReplayVectors(fStaleHash.root, ['tests/counter.json']);
  assert.equal(staleHashAnchor.outcome, 'blocked');
  assert.match(staleHashAnchor.reason, /stale criterion/i);

  const fTextMismatch = makeRepo(t, {
    'prompts/counter.prompt.md': '# Counter\n\nExpose `sync inc()`.\n',
    'user_stories/counter.md': '# Counter\n\nAs a clerk, I want to count, so that totals match.\n\n## Acceptance criteria\n\n1. Inc returns 1.\n',
    'tests/counter.json': {
      entry_path: 'prompts/counter.prompt.md',
      criteria: [{ id: 'AC1', text: 'Inc returns 99.' }],
      steps: [{ id: 's1', op: 'inc', checks: [{ criterion_id: 'AC1', target: 'result', path: '/count', op: '=', value: 1 }] }],
    },
  });
  const textMismatchAnchor = pinReplayVectors(fTextMismatch.root, ['tests/counter.json']);
  assert.equal(textMismatchAnchor.outcome, 'blocked');
  assert.match(textMismatchAnchor.reason, /do not match/i);
});
