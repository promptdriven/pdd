import './helpers/test-home.mjs';
import { test, after } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { proseSha256 } from '../src/runtime-seam.mjs';
import { compareTargets, runTargetBoth } from '../src/core/target-both.mjs';

const bin = join(process.cwd(), 'bin/pdd.mjs');
const roots = [];
after(() => { for (const root of roots) rmSync(root, { recursive: true, force: true }); });
const capture = () => ({ text: '', write(value) { this.text += value; return true; } });

// A CLI that upper-cases its argument; the scenario has two steps on one Story.
function project({ app = "process.stdout.write(process.argv[2].toUpperCase()+'\\n');\n", resources = [] } = {}) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-target-both-')); roots.push(root);
  spawnSync('git', ['init', '-q', root]);
  for (const d of ['prompts', 'tests', 'user_stories']) mkdirSync(join(root, d));
  writeFileSync(join(root, 'app.mjs'), app);
  const iface = { status: 'draft', prose_sha256: 'HASH', entries: [{ operation: 'main', implementation: { kind: 'cli', command: 'node app.mjs' },
    input_schema: { type: 'object', properties: { argv: { type: 'array', items: { type: 'string' } }, stdin: { type: 'string' } }, required: ['argv'], additionalProperties: false },
    result_schema: { type: 'object', properties: { stdout: { type: 'string' }, stderr: { type: 'string' }, exit_code: { type: 'integer' } }, required: ['stdout', 'stderr', 'exit_code'], additionalProperties: false },
    errors: [] }], resources, conventions: [{ path: '/entries/0/input_schema', convention: 'cli' }, { path: '/entries/0/result_schema', convention: 'cli' }], calls: [], limits: { max_steps: 4, max_model_calls: 2 } };
  const prompt = '# app\n\nPrint the argument in upper case.\n\n<details><summary>Runtime interface</summary>\n\n```json\n' + JSON.stringify(iface) + '\n```\n</details>\n';
  writeFileSync(join(root, 'prompts/app.prompt.md'), prompt.replace('HASH', proseSha256(prompt)));
  writeFileSync(join(root, 'user_stories/demo.md'), '# Demo\n\n## Acceptance criteria\n\n1. Upper-cases a word.\n2. Keeps digits.\n');
  const step = (id, criterion, arg, out) => ({ step_id: id, entry_path: 'prompts/app.prompt.md', operation: 'main', input: { argv: [arg] },
    checks: [{ criterion_id: criterion, target: 'result', path: '/stdout', op: 'equals', value: out }, { criterion_id: criterion, target: 'result', path: '/exit_code', op: 'equals', value: 0 }] });
  writeFileSync(join(root, 'tests/demo.json'), JSON.stringify({ schema_version: 'prompt-runtime.program-scenario.v1', story_path: 'user_stories/demo.md',
    criteria: [{ id: 'AC1', text: 'Upper-cases a word.' }, { id: 'AC2', text: 'Keeps digits.' }], initial_world: {}, simulation: {}, context: [],
    steps: [step('word', 'AC1', 'abc', 'ABC\n'), step('digits', 'AC2', 'a1', 'A1\n')] }));
  spawnSync('git', ['add', '.'], { cwd: root });
  spawnSync('git', ['-c', 'user.name=test', '-c', 'user.email=test@example.com', 'commit', '-qm', 'fixture'], { cwd: root });
  return root;
}

// Stands in for `pdd test --json`: one row per scenario, failed checks carry the interpreter's actual value.
function fakeInterpreter(rows, exit = rows.some(row => row.state !== 'passed') ? 1 : 0) {
  const calls = [];
  const check = async (input, { stdout }) => {
    calls.push(input);
    if (rows !== null) stdout.write(JSON.stringify({ batch: 'b1', exit_code: exit, rows }) + '\n');
    return exit;
  };
  return { check, calls };
}
const row = (state, failed_checks = [], extra = {}) => ({ story: 'demo', test: 'tests/demo.json', state, failed_checks, calls: 2, ...extra });

async function both(root, interpreter, { words = ['demo'], options = {}, json = true } = {}) {
  const stdout = capture(), stderr = capture();
  const code = await runTargetBoth({ root, words, options, json }, { stdout, stderr, env: {}, check: interpreter.check });
  return { code, out: stdout.text, err: stderr.text, report: json && stdout.text ? JSON.parse(stdout.text) : null };
}

test('3296: both targets pass the same checks, so the Story agrees and the command passes', async () => {
  const interpreter = fakeInterpreter([row('passed')]);
  const { code, report, err } = await both(project(), interpreter, { options: { '--fresh': true, '--max-calls': 20, '--lf': true } });
  assert.equal(code, 0, err);
  assert.equal(report.target, 'both');
  assert.deepEqual(report.summary, { compared: 4, agree: 4, disagree: 0, not_compared: 0 });
  assert.equal(report.stories[0].status, 'agree');
  assert.equal(report.interpreter.calls, 2);
  // Only interpreter options pdd test understands are passed on, with --json for the comparison.
  assert.deepEqual(interpreter.calls[0].options, { '--fresh': true, '--max-calls': 20, '--json': true });
  assert.deepEqual(interpreter.calls[0].words, ['demo']);
});

test('3296: a step where the interpreter fails and the code passes is reported with both values', async () => {
  const interpreter = fakeInterpreter([row('failed', [{ criterion_id: 'AC2', step_id: 'digits', target: 'result', path: '/stdout', expected: 'A1\n', actual: 'A\n' }])]);
  const { code, report } = await both(project(), interpreter);
  assert.equal(code, 1);
  const story = report.stories[0];
  assert.equal(story.status, 'disagree');
  assert.deepEqual(story.differing_steps, ['tests/demo.json · digits']);
  assert.deepEqual(story.differing_criteria, ['AC2']);
  const diff = story.checks.filter(check => check.group === 'disagree');
  assert.deepEqual(diff.map(check => [check.step_id, check.path, check.interpreter, check.code]), [['digits', '/stdout', { status: 'failed', actual: 'A\n' }, { status: 'passed', actual: 'A1\n' }]]);
  assert.deepEqual(report.summary, { compared: 4, agree: 3, disagree: 1, not_compared: 0 });
});

test('3296: code that fails where the interpreter passes is a disagreement, and the text report names it', async () => {
  const root = project({ app: "process.stdout.write(process.argv[2].replace(/[0-9]/g,'').toUpperCase()+'\\n');\n" });
  const { code, out } = await both(root, fakeInterpreter([row('passed')]), { json: false });
  assert.equal(code, 1);
  assert.match(out, /^Target both: 4 check\(s\) compared · 1 disagree · 3 agree · 0 not compared · 2 interpreter call\(s\)$/m);
  assert.match(out, /^DISAGREE +user_stories\/demo\.md +\(interpreter passed, code failed\)$/m);
  assert.match(out, /tests\/demo\.json · step digits · AC2 \/stdout: expected "A1\\n", interpreter as expected, code "A\\n"/);
});

test('3296: both failing the same check with different values still disagree; with the same value they agree', () => {
  const codeReport = { stories: [{ story: 'user_stories/demo.md', status: 'failed', steps: [{ step_id: 'word', scenario: 'tests/demo.json', status: 'failed',
    checks: [{ criterion_id: 'AC1', path: '/stdout', status: 'failed', expected: 'ABC\n', actual: 'abc\n' }] }] }] };
  const interp = actual => ({ rows: [row('failed', [{ criterion_id: 'AC1', step_id: 'word', target: 'result', path: '/stdout', expected: 'ABC\n', actual }])] });
  assert.equal(compareTargets(codeReport, interp('Abc\n')).stories[0].status, 'disagree');
  const agreeing = compareTargets(codeReport, interp('abc\n'));
  assert.equal(agreeing.stories[0].status, 'agree');
  assert.deepEqual(agreeing.summary, { compared: 1, agree: 1, disagree: 0, not_compared: 0 });
});

test('3296: steps either side did not run are listed as not compared, never as agreeing', async () => {
  const unrunCode = await both(project({ resources: [{ name: 'db', kind: 'port' }] }), fakeInterpreter([row('passed')]));
  assert.equal(unrunCode.code, 1);
  assert.equal(unrunCode.report.stories[0].status, 'not compared');
  assert.equal(unrunCode.report.summary.compared, 0);
  assert.ok(unrunCode.report.stories[0].not_compared.every(item => item.side === 'code' && /resources or calls/.test(item.reason)), JSON.stringify(unrunCode.report.stories[0].not_compared));

  const refused = await both(project(), fakeInterpreter([row('refused', [], { why: 'The scenario names an unknown operation.' })]));
  assert.equal(refused.code, 1);
  assert.equal(refused.report.stories[0].status, 'not compared');
  assert.equal(refused.report.summary.not_compared, 4);
  assert.match(refused.report.stories[0].not_compared[0].reason, /^The interpreter reported refused: The scenario names an unknown operation\.$/);
});

test('3296: when the interpreter reports nothing, its exit code is returned after the code results are shown', async () => {
  const { code, report } = await both(project(), fakeInterpreter(null, 4));
  assert.equal(code, 4);
  assert.equal(report.interpreter.rows, null);
  assert.equal(report.summary.not_compared, 4);
});

test('3296: a selection error stops before the interpreter is called', async () => {
  const interpreter = fakeInterpreter([row('passed')]);
  const { code, err } = await both(project(), interpreter, { words: ['no-such-story'] });
  assert.equal(code, 2);
  assert.match(err, /No selected Story tests/);
  assert.equal(interpreter.calls.length, 0);
});

test('3296: the CLI accepts --target both and rejects options the comparison cannot honour', () => {
  const root = project();
  const env = { ...process.env, GH_TOKEN: '', GITHUB_TOKEN: '', PDD_RUNTIME_URL: 'http://127.0.0.1:1' };
  const bad = spawnSync(process.execPath, [bin, 'test', '--target', 'both', '--lf', 'demo'], { cwd: root, encoding: 'utf8', env });
  assert.equal(bad.status, 2, bad.stderr);
  assert.match(bad.stderr, /--target both accepts only --fresh, --max-calls, --timeout, --json/);
  const help = spawnSync(process.execPath, [bin, 'test', '--help'], { cwd: root, encoding: 'utf8', env });
  assert.match(help.stdout + help.stderr, /--target both \[STORY\.\.\.\]/);
});

