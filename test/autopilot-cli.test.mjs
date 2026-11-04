import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { runPdd } from '../src/pdd-cli.mjs';
import { renderCompletion } from '../src/completion.mjs';

const capture = () => ({ text: '', write(value) { this.text += value; } });
function repo(t) {
  const cwd = mkdtempSync(join(tmpdir(), 'pdd-autopilot-'));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', cwd]);
  return cwd;
}
async function invoke(cwd, argv, extra = {}) {
  const stdout = capture(), stderr = capture();
  const exitCode = await runPdd(argv, { cwd, stdout, stderr, ...extra });
  return { exitCode, stdout: stdout.text, stderr: stderr.text };
}

for (const mode of ['off', 'observe', 'auto']) test(`autopilot-mode: CLI saves ${mode} without starting work`, async t => {
  const cwd = repo(t);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ strict_approvals: true, keep: 7, autopilot: { mode: 'off', trust: ['Dana'], keep: 'inside' } }));
  const result = await invoke(cwd, ['autopilot', mode], {
    workflowRunner: new Proxy({}, { get() { assert.fail('No workflow may start'); } }),
    autopilotPorts: { github: { lookup() { assert.fail('Mode needs no GitHub lookup'); } } },
  });
  assert.equal(result.exitCode, 0, result.stderr);
  assert.equal(result.stderr, '');
  assert.deepEqual(JSON.parse(readFileSync(join(cwd, 'pdd.json'))), {
    strict_approvals: true, keep: 7, autopilot: { mode, trust: ['Dana'], keep: 'inside' },
  });
});

test('autopilot-trust: CLI adds several names, deduplicates and removes ignoring case', async t => {
  const cwd = repo(t);
  assert.equal((await invoke(cwd, ['autopilot', 'trust', 'Dana', 'dana', 'BO'])).exitCode, 0);
  assert.deepEqual(JSON.parse(readFileSync(join(cwd, 'pdd.json'))).autopilot, { mode: 'off', trust: ['Dana', 'BO'] });
  assert.equal((await invoke(cwd, ['autopilot', 'untrust', 'DANA'])).exitCode, 0);
  assert.deepEqual(JSON.parse(readFileSync(join(cwd, 'pdd.json'))).autopilot.trust, ['BO']);
});

test('autopilot-mode/trust: help and completion advertise the five commands', async t => {
  const result = await invoke(repo(t), ['autopilot', '--help']);
  assert.equal(result.exitCode, 0);
  for (const word of ['off', 'observe', 'auto', 'trust', 'untrust']) {
    assert.ok(result.stdout.includes(`pdd autopilot ${word}`), word);
    for (const shell of ['bash', 'zsh']) assert.ok(renderCompletion(shell).includes(word), `${shell} ${word}`);
  }
});

test('autopilot-mode/trust: bad CLI arguments exit 2 before effects', async t => {
  const cwd = repo(t);
  const file = join(cwd, 'pdd.json'), before = '{"strict_approvals":true}\n';
  writeFileSync(file, before);
  for (const argv of [[], ['on'], ['turbo'], ['auto', 'extra'], ['auto', '--json'], ['trust'],
    ['trust', ''], ['trust', '  '], ['untrust'], ['untrust', 'Dana', 'Bo'], ['untrust', '']]) {
    const result = await invoke(cwd, ['autopilot', ...argv]);
    assert.equal(result.exitCode, 2, JSON.stringify(argv));
    assert.equal(result.stdout, ''); assert.ok(result.stderr.trim());
    assert.equal(readFileSync(file, 'utf8'), before);
  }
});

function setupOptions(extra = {}) {
  return { stdin: { isTTY: true }, pathDiagnostic: () => [], setupSkills: () => [],
    setupProject: () => ({ file: 'AGENTS.md', changed: false }), setupAgentMcp: async () => 0,
    workflowAgents: { checkWorkflowAgents: async () => ({ ok: true, agent: 'codex', message: '' }) }, ...extra };
}
for (const mode of ['', 'observe', 'auto']) test(`autopilot-setup${mode ? `-${mode}` : ''}: CLI saves first answer and uses additional trust names`, async t => {
  const cwd = repo(t); let questions = 0;
  const options = setupOptions({ autopilotPorts: {
    terminal: { mode: async () => { questions++; return { answer: mode }; }, names: async info => {
      assert.deepEqual(info, { owner: 'Ada', writers: ['Bo', 'Cy'], complete: true }); return { names: ['Dana'] };
    } }, github: { lookup: async () => ({ owner: 'Ada', writers: ['Bo', 'Cy'], complete: true }) },
  } });
  const result = await invoke(cwd, ['setup'], options);
  assert.equal(result.exitCode, 0, result.stderr);
  assert.ok(existsSync(join(cwd, 'pdd.json')), 'Setup must save Autopilot settings');
  assert.deepEqual(JSON.parse(readFileSync(join(cwd, 'pdd.json'))).autopilot, { mode: mode || 'off', trust: ['Dana'] });
  assert.match(result.stdout, /owner.*Ada/); assert.match(result.stdout, /write.*Bo.*Cy/);
  assert.equal((await invoke(cwd, ['setup'], options)).exitCode, 0);
  assert.equal(questions, 1, 'Repeat setup must not ask the mode again');
});

test('autopilot-setup: CLI does not ask or save without a terminal or outside Git', async t => {
  const cwd = repo(t), outside = join(cwd, 'outside'); mkdirSync(outside);
  const noQuestions = { terminal: new Proxy({}, { get() { assert.fail('No questions'); } }), github: { lookup() { assert.fail('No lookup'); } } };
  assert.equal((await invoke(cwd, ['setup'], setupOptions({ stdin: { isTTY: false }, autopilotPorts: noQuestions }))).exitCode, 0);
  assert.throws(() => readFileSync(join(cwd, 'pdd.json')), { code: 'ENOENT' });
  const context = async () => null;
  assert.equal((await invoke(outside, ['setup'], setupOptions({ gitContext: context, autopilotPorts: noQuestions }))).exitCode, 0);
  assert.throws(() => readFileSync(join(outside, 'pdd.json')), { code: 'ENOENT' });
});
