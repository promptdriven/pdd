import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync, symlinkSync, unlinkSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { detectTestCommand, readCoreSettings, boundSuiteCommand } from '../src/autopilot-core.mjs';
import { forensicsCommand } from '../src/autopilot-forensics.mjs';
import { cardCommand } from '../src/autopilot-intake.mjs';
import { lintSvgLayouts } from '../src/svg-layout.mjs';
import { refusalView, renderText } from '../src/runtime-seam.mjs';
import { coreWorld } from './helpers/core-world.mjs';

test('pdd#3488 (1): detectTestCommand auto-detects zero-manifest node:test and pytest suites while preserving manifest precedence', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-3488-detect-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));

  assert.equal(detectTestCommand(dir), null, 'empty greenfield directory has no test command yet');

  mkdirSync(join(dir, 'test', 'nested'), { recursive: true });
  writeFileSync(join(dir, 'test', 'nested', 'hub.test.mjs'), 'import test from "node:test"; test("ok", () => {});\n');
  assert.equal(detectTestCommand(dir), 'node --test');
  assert.equal(readCoreSettings(dir).testCommand, 'node --test');
  assert.match(boundSuiteCommand(detectTestCommand(dir), {}, 4), /^node --test --test-concurrency=4$/);

  const pyDir = mkdtempSync(join(tmpdir(), 'pdd-3488-py-'));
  t.after(() => rmSync(pyDir, { recursive: true, force: true }));
  mkdirSync(join(pyDir, 'tests'), { recursive: true });
  writeFileSync(join(pyDir, 'tests', 'test_worker.py'), 'def test_ok(): assert True\n');
  assert.equal(detectTestCommand(pyDir), 'pytest');

  // Manifest still takes precedence when package.json exists.
  writeFileSync(join(dir, 'package.json'), JSON.stringify({ name: 'demo', scripts: { test: 'npm run unit' } }));
  assert.equal(detectTestCommand(dir), 'npm test');
});

test('pdd#3488 (2): keptPr resumes an open end-pr Draft PR on release, marks it ready, runs checks, and merges without rebuilding', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(3, { title: 'hub-1: private fleets and pairing' });
  await w.tick();
  const buildJob = w.job(3, 'build');
  assert.ok(buildJob, 'initial build starts');

  mkdirSync(join(buildJob.cwd, 'test'), { recursive: true });
  writeFileSync(join(buildJob.cwd, 'test', 'hub.test.mjs'), 'import test from "node:test"; test("hub", () => {});\n');
  const { pr } = w.build(3);

  // Simulate an earlier run that ended and parked PR as a draft with <!-- pdd:autopilot-core:end-pr:3:... -->, then operator ran release.
  pr.draft = true;
  pr.comments.push({
    id: 777,
    user: { login: 'acme' },
    body: `Autopilot ended the run for issue #3: no full test command.\n\nThis PR stays open as a draft. It is not merged.\n\n<!-- pdd:autopilot-core:end-pr:3:${buildJob.id} -->`,
  });
  rmSync(join(w.root, 'jobs', '3.json'), { force: true });
  w.github.unlabel(3, 'pdd:working', 'acme');
  w.github.unlabel(3, 'pdd:stuck', 'acme');

  const buildsBefore = w.started.filter(j => j.issue === 3 && j.role === 'build').length;
  await w.tick();
  assert.equal(w.started.filter(j => j.issue === 3 && j.role === 'build').length, buildsBefore, 'resumes PR in phase pr without starting a second build');
  assert.equal(pr.draft, false, 'resumed draft PR is marked ready for review');

  // Even if PR became draft again before merge, mergeCheck marks it ready before calling gh pr merge.
  pr.draft = true;
  w.github.setChecks(pr.head, 'success');
  await w.tick();
  w.review(3, 'PASS');
  w.suite(3, 0);
  await w.tick();

  assert.equal(pr.draft, false, 'mergeCheck marks draft PR ready before merge');
  assert.deepEqual(w.github.merges, [pr.number], 'resumed end-pr Draft PR merges cleanly without rebuild');
});

test('pdd#3488 (3): forensicsCommand keeps Codex code_mode_host enabled while cardCommand stays toolless', () => {
  const fCmd = forensicsCommand({ kind: 'codex', command: 'codex' }, { resultFile: '/tmp/f.json' });
  assert.ok(!fCmd.args.includes('features.code_mode_host=false'), 'forensicsCommand must not disable Codex stable code_mode_host');
  assert.ok(fCmd.args.includes('features.code_mode=false'), 'forensicsCommand still disables code_mode');
  assert.equal(fCmd.args[fCmd.args.indexOf('--sandbox') + 1], 'read-only');

  const cCmd = cardCommand({ kind: 'codex', command: 'codex' }, { result: '/tmp/c.json' });
  assert.ok(cCmd.args.includes('features.shell_tool=false'));
  assert.ok(cCmd.args.includes('features.code_mode_host=false'));
});

test('pdd#3488 (4): local lint catches excluded result_value_pointer and missing result_template placeholder, and refusalView gives an actionable fix', t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-3488-simlint-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: root });
  mkdirSync(join(root, 'prompts'), { recursive: true });
  mkdirSync(join(root, 'user_stories'), { recursive: true });
  mkdirSync(join(root, 'test', 'runtime'), { recursive: true });

  writeFileSync(join(root, 'user_stories', 'H01-story.md'), '# Pair machine\n\n1. Sam pairs a machine.\n');
  const badIface = {
    status: 'draft',
    entries: [{ operation: 'pair', kind: 'function', input_schema: { type: 'object' }, output_schema: { type: 'object' } }],
    resources: [{ name: 'store', kind: 'port', access: 'read_write', operations: [{ name: 'load', access: 'read', result_schema: { type: 'array', items: { type: 'object' } } }] }],
  };
  writeFileSync(
    join(root, 'prompts', 'hub.prompt.md'),
    `# Hub\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(badIface, null, 2)}\n\`\`\`\n</details>\n`,
  );
  const scenario = {
    schema_version: 'prompt-runtime.program-scenario.v1',
    story_path: 'user_stories/H01-story.md',
    criteria: [{ id: 'C1', text: 'Sam pairs a machine.' }],
    initial_world: { store: [] },
    simulation: {
      'store.load': {
        action: 'key-value.get',
        world_pointer: '',
        key_argument_pointer: '/key',
        result_template: {},
        result_value_pointer: '/value',
      },
    },
    steps: [
      {
        step_id: 's1',
        entry_path: 'prompts/hub.prompt.md',
        operation: 'pair',
        input: {},
        checks: [{ criterion_id: 'C1', surface: 'result', pointer: '/ok', op: 'equals', expected: true }],
      },
    ],
  };
  writeFileSync(join(root, 'test', 'runtime', 'H01-story.json'), JSON.stringify(scenario, null, 2));
  const files = ['prompts/hub.prompt.md', 'user_stories/H01-story.md', 'test/runtime/H01-story.json'];

  const warnings = lintSvgLayouts({ root, files });
  assert.ok(
    warnings.some(w => w.includes('impossible-result-value-pointer')),
    `expected impossible-result-value-pointer warning, got: ${warnings.join('\n')}`,
  );
  assert.ok(
    warnings.some(w => w.includes('missing-result-placeholder')),
    `expected missing-result-placeholder warning, got: ${warnings.join('\n')}`,
  );

  // Declare /value in result_schema and result_template -> zero simulation warnings!
  const goodIface = {
    status: 'draft',
    entries: [{ operation: 'pair', kind: 'function', input_schema: { type: 'object' }, output_schema: { type: 'object' } }],
    resources: [{ name: 'store', kind: 'port', access: 'read_write', operations: [{ name: 'load', access: 'read', result_schema: { type: 'object', properties: { value: { type: 'array' } }, required: ['value'], additionalProperties: false } }] }],
  };
  writeFileSync(
    join(root, 'prompts', 'hub.prompt.md'),
    `# Hub\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(goodIface, null, 2)}\n\`\`\`\n</details>\n`,
  );
  scenario.simulation['store.load'].result_template = { value: null };
  writeFileSync(join(root, 'test', 'runtime', 'H01-story.json'), JSON.stringify(scenario, null, 2));
  const cleanWarnings = lintSvgLayouts({ root, files });
  assert.deepEqual(cleanWarnings.filter(w => w.includes('result_value_pointer')), []);

  // Verify refusalView & renderText enrich impossible-result-value-pointer with actionable guidance.
  const view = refusalView({ code: 'impossible-result-value-pointer', file: 'test/runtime/H01-story.json' }, []);
  assert.match(view.hint ?? '', /result_value_pointer/);
  assert.match(view.hint ?? '', /result_schema/);
  const rendered = renderText({ batch: 'b1', exitCode: 2, rows: [{ story: 'H01', title: 'Pairing', test: 'test/runtime/H01-story.json', state: 'refused', unsent: true, refusals: [{ code: 'impossible-result-value-pointer', message: 'Port schema excluded pointer.' }] }] });
  assert.match(rendered, /result_value_pointer to ""/);
});

test('pdd#3488 (5): Linux deleted-cwd symlink fallback strips trailing " (deleted)" when realpathSync fails', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-3488-cwd-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const target = join(dir, 'gone-worktree (deleted)');
  const link = join(dir, 'fake-proc-cwd');
  symlinkSync(target, link);
  let resolved = null;
  try {
    execFileSync(process.execPath, ['-e', `import('node:fs').then(fs => fs.realpathSync(${JSON.stringify(link)}))`], { stdio: 'ignore' });
  } catch {
    const raw = execFileSync(process.execPath, ['-e', `import('node:fs').then(fs => process.stdout.write(fs.readlinkSync(${JSON.stringify(link)}).replace(/ \\(deleted\\)$/, '')))`], { encoding: 'utf8' });
    resolved = raw;
  }
  assert.equal(resolved, join(dir, 'gone-worktree'));
  unlinkSync(link);
});
