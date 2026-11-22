import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import test from 'node:test';
import { lintRepoProject } from '../src/repo-hygiene-lint.mjs';
import { runtimePreflightSlice } from '../src/runtime-seam.mjs';

function makeGitRepo(t, files) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-untested-prompt-3571-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: root });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: root });
  execFileSync('git', ['config', 'user.name', 'Test User'], { cwd: root });
  for (const [relPath, content] of Object.entries(files)) {
    const abs = join(root, relPath);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, content, 'utf8');
  }
  execFileSync('git', ['add', '.'], { cwd: root });
  return root;
}

const checkablePrompt = (title, deps = 'None.') => [
  `# ${title}`,
  '',
  `Implements ${title} domain rules cleanly.`,
  '',
  '## Dependencies',
  deps,
  '',
].join('\n');

const nativeOnlyFrontmatterPrompt = (title, deps = 'None.') => [
  '---',
  'kind: native-only',
  'reason: Live OS socket and process boundary',
  '---',
  `# ${title}`,
  '',
  '## Boundary',
  'Binds local socket and delegates to checkable domain operations.',
  '',
  '## Errors',
  'Maps bind failures to exit code 1.',
  '',
  '## Verification',
  'Real-host smoke test verifies bind and error handling.',
  '',
  '## Dependencies',
  deps,
  '',
].join('\n');

const nativeOnlyInterfacePrompt = (title, deps = 'None.') => [
  `# ${title}`,
  '',
  '## Boundary',
  'Wraps native filesystem sync calls.',
  '',
  '## Errors',
  'Returns structured failure on EACCES.',
  '',
  '## Verification',
  'Real-host probe exercises fsync on a temp file.',
  '',
  '## Dependencies',
  deps,
  '',
  '<details>',
  '<summary>Runtime interface</summary>',
  '',
  '```json',
  JSON.stringify({ kind: 'native-only', reason: 'Direct fsync boundary' }, null, 2),
  '```',
  '</details>',
  '',
].join('\n');

const v1Scenario = (entryPaths, storyPath = 'user_stories/sample.md') => JSON.stringify({
  schema_version: 'prompt-runtime.program-scenario.v1',
  story_path: storyPath,
  criteria: [{ id: 'AC1', text: 'Runs cleanly' }],
  initial_world: {},
  steps: entryPaths.map((entry_path, i) => ({
    step_id: `s${i + 1}`,
    entry_path,
    operation: 'run',
    input: {},
    checks: [{ criterion_id: 'AC1', target: 'result', path: '/ok', op: 'equals', expected: true }],
  })),
}, null, 2);

const shortScenario = ({ schemaVersion = 'pdd.scenario.short.v1', entryPath, entryPaths, appMaps } = {}) => JSON.stringify({
  ...(schemaVersion ? { schema_version: schemaVersion } : {}),
  ...(entryPath ? { entry_path: entryPath } : {}),
  ...(entryPaths ? { entry_paths: entryPaths } : {}),
  ...(appMaps ? { app_maps: appMaps } : {}),
  steps: [{ op: 'run', input: {}, checks: [['result', '/ok', '=', true]] }],
}, null, 2);

const sampleStory = [
  '# Sample story',
  '',
  '## Acceptance Criteria',
  '1. Runs cleanly.',
  '',
].join('\n');

test('3571: direct v1 & Short JSON scenarios, transitive ## Dependencies (relative, root-relative, cyclic), and app_maps mark checkable prompts reached', (t) => {
  const repo = makeGitRepo(t, {
    'user_stories/s1.md': sampleStory,
    'user_stories/s2.md': sampleStory,
    'user_stories/s3.md': sampleStory,
    'prompts/v1/entry.prompt.md': checkablePrompt('V1 Entry', '- [Middle](../mid/middle.prompt.md)'),
    'prompts/mid/middle.prompt.md': checkablePrompt('Middle', '- [Leaf](prompts/leaf/leaf.prompt.md)\n- [Cycle back](../v1/entry.prompt.md)'),
    'prompts/leaf/leaf.prompt.md': checkablePrompt('Leaf', '- [Back to middle](../mid/middle.prompt.md)'),
    'prompts/short/single.prompt.md': checkablePrompt('Short Single'),
    'prompts/short/multi-a.prompt.md': checkablePrompt('Short Multi A'),
    'prompts/short/multi-b.prompt.md': checkablePrompt('Short Multi B'),
    'prompts/ui/screen.prompt.md': checkablePrompt('UI Screen'),
    'app/maps/main.json': JSON.stringify({
      schema_version: 'prompt-runtime.app-map.v1',
      screens: [{ id: 'home', prompt_path: 'prompts/ui/screen.prompt.md', operation: 'render' }],
    }, null, 2),
    'tests/s1.json': v1Scenario(['./prompts/v1/entry.prompt.md'], 'user_stories/s1.md'),
    'tests/s2.json': shortScenario({ entryPath: 'prompts/short/single.prompt.md' }),
    'tests/s3.json': shortScenario({
      schemaVersion: null,
      entryPaths: ['prompts/short/multi-a.prompt.md', 'prompts/short/multi-b.prompt.md'],
      appMaps: ['app/maps/main.json'],
    }),
  });

  const report = lintRepoProject({ root: repo });
  assert.equal(report.ok, true);
  assert.deepEqual(report.errors, []);
  const coverageFindings = report.findings.filter(f => f.code === 'untested-checkable-prompt');
  assert.deepEqual(coverageFindings, []);
});

test('3571: unreached checkable orphan prompt warns by default (exit-safe), native-only prompts are exempt and never bridge coverage to their deps', (t) => {
  const repo = makeGitRepo(t, {
    'user_stories/s1.md': sampleStory,
    'prompts/tested.prompt.md': checkablePrompt('Tested'),
    'prompts/orphan.prompt.md': checkablePrompt('Orphan'),
    'prompts/native-linked.prompt.md': checkablePrompt('Native Linked Only'),
    'prompts/adapter-fm.prompt.md': nativeOnlyFrontmatterPrompt('Adapter FM', '- [Native Linked](native-linked.prompt.md)'),
    'prompts/adapter-if.prompt.md': nativeOnlyInterfacePrompt('Adapter IF', '- [Orphan](orphan.prompt.md)'),
    'prompts/examples/demo.prompt.md': checkablePrompt('Example Prompt'),
    'tests/s1.json': v1Scenario(['prompts/tested.prompt.md', 'prompts/adapter-fm.prompt.md'], 'user_stories/s1.md'),
  });

  const report = lintRepoProject({ root: repo });
  assert.equal(report.ok, true, 'default severity is warn so errors stay empty');
  assert.deepEqual(report.errors, []);
  const coverage = report.findings.filter(f => f.code === 'untested-checkable-prompt');
  assert.deepEqual(
    coverage.map(f => ({ path: f.path, line: f.line, severity: f.severity, category: f.category })),
    [
      { path: 'prompts/native-linked.prompt.md', line: 1, severity: 'warn', category: 'prompt test coverage' },
      { path: 'prompts/orphan.prompt.md', line: 1, severity: 'warn', category: 'prompt test coverage' },
    ],
  );
  for (const f of coverage) {
    assert.match(f.formatted, /^Warning: prompt test coverage: prompts\/.*\.prompt\.md:1 \[untested-checkable-prompt\] /);
  }
});

test('3571: zero-scenario repo stays quiet by default, runs when configured in pdd.json, and honors off/disable/error overrides', (t) => {
  const repo = makeGitRepo(t, {
    'prompts/solo.prompt.md': checkablePrompt('Solo'),
    // Non-scenario JSON in tests/ must NOT trip the zero-scenario gate.
    'tests/native-cases.json': JSON.stringify({ schema_version: 'pdd.native-cases.v1', cases: [] }, null, 2),
  });

  // 1. Default with 0 scenarios -> quiet
  const defaultReport = lintRepoProject({ root: repo });
  assert.equal(defaultReport.ok, true);
  assert.deepEqual(defaultReport.findings.filter(f => f.code === 'untested-checkable-prompt'), []);

  // 2. Explicitly configured as warn in pdd.json -> emits warning even with 0 scenarios
  const warnReport = lintRepoProject({ root: repo, config: { rules: { 'untested-checkable-prompt': 'warn' } } });
  assert.equal(warnReport.ok, true);
  assert.deepEqual(
    warnReport.findings.filter(f => f.code === 'untested-checkable-prompt').map(f => f.path),
    ['prompts/solo.prompt.md'],
  );

  // 3. Explicitly promoted to error -> emits error and ok: false
  const errorReport = lintRepoProject({ root: repo, config: { rules: { 'untested-checkable-prompt': 'error' } } });
  assert.equal(errorReport.ok, false);
  assert.equal(errorReport.errors.filter(e => e.includes('[untested-checkable-prompt]')).length, 1);

  // 4. Add a scenario + orphan and verify off and disable suppress
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  writeFileSync(join(repo, 'prompts/tested.prompt.md'), checkablePrompt('Tested'), 'utf8');
  writeFileSync(join(repo, 'user_stories/s1.md'), sampleStory, 'utf8');
  writeFileSync(join(repo, 'tests/s1.json'), shortScenario({ entryPath: 'prompts/tested.prompt.md' }), 'utf8');
  execFileSync('git', ['add', '.'], { cwd: repo });

  const offReport = lintRepoProject({ root: repo, config: { rules: { 'untested-checkable-prompt': 'off' } } });
  assert.deepEqual(offReport.findings.filter(f => f.code === 'untested-checkable-prompt'), []);

  const disabledReport = lintRepoProject({ root: repo, config: { disable: ['untested-checkable-prompt'] } });
  assert.deepEqual(disabledReport.findings.filter(f => f.code === 'untested-checkable-prompt'), []);
});

test('3571: nested parts/*/tests scenarios, Runtime interface calls[].target, and native-only intermediary barrier', (t) => {
  const entryWithCalls = [
    '# Billing Entry',
    '',
    'Delegates to billing calc and links native adapter.',
    '',
    '## Dependencies',
    '- [Native Adapter](adapter.prompt.md)',
    '',
    '<details>',
    '<summary>Runtime interface</summary>',
    '',
    '```json',
    JSON.stringify({
      kind: 'partial',
      calls: [{ target: 'prompts/billing/calc.prompt.md', operation: 'compute' }],
    }, null, 2),
    '```',
    '</details>',
    '',
  ].join('\n');

  const repo = makeGitRepo(t, {
    'parts/billing/user_stories/b1.md': sampleStory,
    'prompts/billing/entry.prompt.md': entryWithCalls,
    'prompts/billing/calc.prompt.md': checkablePrompt('Billing Calc'),
    'prompts/billing/adapter.prompt.md': nativeOnlyFrontmatterPrompt('Billing Adapter', '- [Hidden Behind Native](hidden.prompt.md)'),
    'prompts/billing/hidden.prompt.md': checkablePrompt('Hidden Behind Native'),
    'parts/billing/tests/b1.json': shortScenario({ entryPath: 'prompts/billing/entry.prompt.md' }),
  });

  const report = lintRepoProject({ root: repo });
  assert.equal(report.ok, true);
  assert.deepEqual(
    report.findings.filter(f => f.code === 'untested-checkable-prompt').map(f => f.path),
    ['prompts/billing/hidden.prompt.md'],
  );
});

test('3571: scoped single-prompt lint scans all repo scenarios, scoped tests array skips rule, and malformed/symlinked JSON never crashes', (t) => {
  const repo = makeGitRepo(t, {
    'user_stories/s1.md': sampleStory,
    'prompts/entry.prompt.md': checkablePrompt('Entry', '- [Helper](helper.prompt.md)'),
    'prompts/helper.prompt.md': checkablePrompt('Helper'),
    'prompts/orphan.prompt.md': checkablePrompt('Orphan'),
    'tests/s1.json': v1Scenario(['prompts/entry.prompt.md'], 'user_stories/s1.md'),
    'tests/broken.json': '{not valid json',
  });

  // Add a symlinked JSON file in tests/ to verify symlink safety (never followed or crashes).
  symlinkSync(join(repo, 'tests/s1.json'), join(repo, 'tests/link.json'));
  execFileSync('git', ['add', 'tests/link.json'], { cwd: repo });

  // 1. Scoped single-prompt lint on reached transitive helper -> 0 warnings
  const reachedScoped = lintRepoProject({ root: repo, promptPaths: ['prompts/helper.prompt.md'] });
  assert.deepEqual(reachedScoped.findings.filter(f => f.code === 'untested-checkable-prompt'), []);

  // 2. Scoped single-prompt lint on orphan -> flags only orphan
  const orphanScoped = lintRepoProject({ root: repo, promptPaths: ['prompts/orphan.prompt.md'] });
  assert.deepEqual(
    orphanScoped.findings.filter(f => f.code === 'untested-checkable-prompt').map(f => f.path),
    ['prompts/orphan.prompt.md'],
  );

  // 3. Scoped tests array (as used by pdd test --affected via lintLocalHygiene) -> skips untested-checkable-prompt
  const affectedReport = lintRepoProject({
    root: repo,
    promptPaths: ['prompts/orphan.prompt.md'],
    tests: ['tests/s1.json'],
  });
  assert.deepEqual(affectedReport.findings.filter(f => f.code === 'untested-checkable-prompt'), []);

  const hygieneWarnings = runtimePreflightSlice().lintLocalHygiene({
    root: repo,
    promptPaths: ['prompts/orphan.prompt.md'],
    tests: ['tests/s1.json'],
  });
  assert.equal(hygieneWarnings.some(w => w.includes('[untested-checkable-prompt]')), false, hygieneWarnings.join('\n'));
});

test('3571: CLI pdd lint --local exits 0 on untested-checkable-prompt warn and exits 1 when promoted to error in pdd.json', (t) => {
  const repo = makeGitRepo(t, {
    'user_stories/s1.md': sampleStory,
    'prompts/tested.prompt.md': checkablePrompt('Tested'),
    'prompts/orphan.prompt.md': checkablePrompt('Orphan'),
    'tests/s1.json': shortScenario({ entryPath: 'prompts/tested.prompt.md' }),
  });

  const bin = join(process.cwd(), 'bin/pdd.mjs');
  const warnRaw = execFileSync(process.execPath, [bin, 'lint', '--local', '--json'], {
    cwd: repo,
    encoding: 'utf8',
  });
  const warnJson = JSON.parse(warnRaw);
  assert.equal(warnJson.exit_code, 0);
  assert.deepEqual(warnJson.problems, []);
  assert.ok(
    warnJson.warnings.some(w => w.includes('prompts/orphan.prompt.md:1 [untested-checkable-prompt]')),
    warnJson.warnings.join('\n'),
  );

  writeFileSync(join(repo, 'pdd.json'), JSON.stringify({
    lint: { rules: { 'untested-checkable-prompt': 'error' } },
  }, null, 2), 'utf8');
  execFileSync('git', ['add', 'pdd.json'], { cwd: repo });

  let errOut = '';
  let exitStatus = 0;
  try {
    execFileSync(process.execPath, [bin, 'lint', '--local', '--json'], {
      cwd: repo,
      encoding: 'utf8',
    });
  } catch (err) {
    exitStatus = err.status;
    errOut = err.stdout;
  }
  assert.equal(exitStatus, 1);
  const errJson = JSON.parse(errOut);
  assert.equal(errJson.exit_code, 1);
  assert.ok(
    errJson.problems.some(p => p.includes('prompts/orphan.prompt.md:1 [untested-checkable-prompt]')),
    JSON.stringify(errJson),
  );
});
