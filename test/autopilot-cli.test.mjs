import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { PassThrough } from 'node:stream';
import { runAutopilot } from '../src/autopilot.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { renderCompletion } from '../src/completion.mjs';

const capture = () => ({ text: '', write(value) { this.text += value; } });
function repo(t) {
  const cwd = mkdtempSync(join(tmpdir(), 'pdd-autopilot-'));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', cwd]);
  return cwd;
}
// The mode, trust and untrust commands also update pdd.json on GitHub; this stub stands in for GitHub, so no test can reach the real gh.
const noGithub = { github: { repository: async () => { throw Error('Tests never call GitHub'); }, request: async () => { throw Error('Tests never call GitHub'); } } };
async function invoke(cwd, argv, extra = {}) {
  const stdout = { ...capture(), isTTY: true }, stderr = capture();
  const exitCode = await runPdd(argv, { cwd, stdout, stderr, autopilotGithubPorts: noGithub, ...extra });
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
  const result = await invoke(outside, ['setup'], setupOptions({ gitContext: context, autopilotPorts: noQuestions }));
  assert.equal(result.exitCode, 0);
  assert.equal(result.stdout, 'AGENTS.md already has this PDD block. No change.\n');
  assert.equal(result.stderr, '');
  assert.throws(() => readFileSync(join(outside, 'pdd.json')), { code: 'ENOENT' });
});


test('autopilot-trust: trust and untrust preserve a saved non-object value until a mode command replaces it', async t => {
  const cwd = repo(t), file = join(cwd, 'pdd.json');
  for (const value of ['auto', false, null, ['auto'], 7]) {
    const before = JSON.stringify({ strict_approvals: true, autopilot: value }) + '\n';
    writeFileSync(file, before);
    for (const action of ['trust', 'untrust']) {
      const result = await invoke(cwd, ['autopilot', action, 'Dana']);
      assert.equal(result.exitCode, 0, result.stderr);
      assert.match(result.stdout, /saved value.*unchanged/i);
      assert.equal(readFileSync(file, 'utf8'), before, `${action} ${JSON.stringify(value)}`);
    }
    assert.equal((await invoke(cwd, ['autopilot', 'auto'])).exitCode, 0);
    assert.deepEqual(JSON.parse(readFileSync(file)), { strict_approvals: true, autopilot: { mode: 'auto', trust: [] } });
  }
});

test('autopilot-setup: default terminal consumes piped mode and names answers in order', t => {
  // Explicit interactive context tests the actual terminal adapter with real stdin;
  // CLI non-terminal admission remains covered separately and asks nothing.
  for (const mode of ['', 'auto', 'observe']) {
    const cwd = repo(t);
    const script = `
      import { runAutopilot } from ${JSON.stringify(new URL('../src/autopilot.mjs', import.meta.url).href)};
      const result = await runAutopilot({ action: 'setup', interactive: true, inRepo: true }, {
        github: { lookup: async () => ({ owner: 'Ada', writers: ['Bo'], complete: true }) },
      });
      console.log('\\nSETUP_RESULT ' + JSON.stringify(result));
      process.exitCode = result.exitCode;
    `;
    const child = spawnSync(process.execPath, ['--input-type=module', '-e', script], {
      cwd, input: `${mode}\nDana Eli\n`, encoding: 'utf8', timeout: 5000,
    });
    assert.equal(child.status, 0, `${mode || 'blank'}: ${child.stderr} ${child.stdout}`);
    assert.match(child.stdout, /Autopilot for this repo/);
    assert.match(child.stdout, /Add anyone else/);
    assert.deepEqual(JSON.parse(readFileSync(join(cwd, 'pdd.json'))).autopilot, { mode: mode || 'off', trust: ['Dana', 'Eli'] });
  }
});


test('autopilot-setup: default terminal redraws each question after backspace and preserves answers', async t => {
  const modeQuestion = 'Autopilot for this repo (off/observe/auto) [off]: ';
  const namesQuestion = 'Add anyone else? GitHub names, separated by spaces (optional): ';
  const flush = () => new Promise(resolve => setImmediate(resolve));
  for (const mode of ['', 'auto']) {
    // readline infers terminal:true from output.isTTY; its actual line editor
    // handles the key presses and emits the redraw, without a terminal-port fake.
    const stdin = new PassThrough(), stdout = new PassThrough();
    stdin.isTTY = true; stdin.setRawMode = () => {};
    stdout.isTTY = true; stdout.columns = 120;
    t.after(() => { stdin.destroy(); stdout.destroy(); });
    let output = '', raw = null;
    stdout.on('data', chunk => { output += chunk; });
    const result = runAutopilot({ action: 'setup', interactive: true, inRepo: true }, {
      stdin, stdout,
      config: { read: async () => ({ raw }), save: async args => { raw = args.raw; return args; } },
      github: { lookup: async () => ({ owner: 'Ada', writers: ['Bo'], complete: true }) },
    });
    await flush();
    assert.ok(output.includes(modeQuestion));
    stdin.write(`${mode}x`);
    const modeRedraw = output.length;
    stdin.write('\x7f');
    await flush();
    assert.ok(output.slice(modeRedraw).includes(modeQuestion), 'Backspace must redraw the mode question');
    stdin.write('\r');
    await flush();
    assert.ok(output.includes(namesQuestion));
    stdin.write('Danx');
    const namesRedraw = output.length;
    stdin.write('\x7f');
    await flush();
    assert.ok(output.slice(namesRedraw).includes(namesQuestion), 'Backspace must redraw the additional names question');
    stdin.write('a Eli\r');
    assert.equal((await result).exitCode, 0);
    assert.deepEqual(JSON.parse(raw), { mode: mode || 'off', trust: ['Dana', 'Eli'] });
  }
});
