import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parseArgv } from '../src/argument-parser.mjs';
import { NAMES } from '../src/command-catalog.mjs';
import { renderCompletion } from '../src/completion.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { fakeRuntime, harbor, root, sink } from './runtime-fake.mjs';

// Rules of user_stories/new-command-names.md that the runPdd vectors cannot see: a removed name runs
// nothing, quiet forms give the same result with no extra line, completion, and the words of printed lines.
const { test: TEST, lint: LINT, simulate: SIMULATE, run: RUN } = NAMES;
const names = (line, before, after) => line.includes(`pdd ${before}`) && line.includes(`pdd ${after}`);
const effect = plan => ({ local: plan.local, operands: plan.operands, options: plan.options, helpPrefix: plan.helpPrefix });
const forbidden = new Proxy({}, { get(_, name) { return typeof name === 'string' ? () => assert.fail(`A removed name must not run ${name}`) : undefined; } });

// [removed words, the new command that the line names, argument tails]
const REMOVED = [
  [['check'], TEST, [[], ['place-order'], ['place-order', '--json', '--details', '--timeout', '4', '--max-calls', '20'], ['--read', 'b1', '--json'],
    ['--retry', 'b1'], ['--fill-hash'], ['--files', 'place-order'], ['--screen', 'http://127.0.0.1:1/', '--drawing', 'a.ui.svg'],
    ['--help'], ['-h'], ['-help'], ['--bogus'], ['--max-calls', '0'], ['a', '--help', 'b']]],
  [['check'], LINT, [['--lint'], ['--lint', '--help'], ['place-order', '--lint'], ['--json', '--lint', '--local'], ['--lint', '--bogus'], ['--', '--lint']]],
  [['try'], SIMULATE, [[], ['place-order'], ['place-order', '--new', '--no-open', '--no-wait'], ['--cli', '--shell'], ['--serve', '8123'],
    ['--save-last'], ['--stop', 'place-order'], ['--help'], ['-h'], ['--bogus'], ['--tab', 'phone']]],
  [['help', 'check'], TEST, [[], ['x'], ['--json']]],
  [['help', 'check'], LINT, [['--lint']]],
  [['help', 'try'], SIMULATE, [[], ['--help']]],
];

test('a removed name exits 2 with one line that names the new command, and runs nothing', async t => {
  const setup = harbor(t), bin = join(setup.sandbox, 'bin'), marker = join(setup.sandbox, 'gh-called'); mkdirSync(bin);
  writeFileSync(join(bin, 'gh'), `#!/bin/sh\ntouch '${marker}'\necho fake-test-token\n`, { mode: 0o755 });
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  let fetches = 0; const realFetch = globalThis.fetch;
  globalThis.fetch = async (...args) => { fetches++; return realFetch(...args); };
  t.after(() => { globalThis.fetch = realFetch; });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, PATH: `${bin}:/usr/bin:/bin` };
  const ports = { cwd: setup.repo, env, packageRoot: root, workflowRunner: forbidden, workflowAreas: forbidden, mcpServer: forbidden,
    runtimeSlots: forbidden, contracts: forbidden, product: forbidden, workflowProve: forbidden, gitContext: forbidden };
  let runs = 0;
  for (const [words, after, tails] of REMOVED) for (const tail of tails) {
    const argv = [...words, ...tail], stdout = sink(), stderr = sink(), label = argv.join(' ');
    assert.equal(await runPdd(argv, { ...ports, stdout, stderr }), 2, label);
    assert.equal(stdout.text, '', label);
    const lines = stderr.text.split('\n');
    assert.equal(lines.length, 2, `${label}: one line: ${stderr.text}`); assert.equal(lines[1], '');
    const before = after === LINT ? 'check --lint' : words.at(-1);
    assert.ok(names(lines[0], before, after), `${label}: ${lines[0]}`);
    // The line repeats no other word of the input and is no usage error about another option.
    const said = lines[0].split(' ').map(word => word.replace(/\.$/, ''));
    for (const word of tail.filter(word => word !== '--lint')) assert.ok(!said.includes(word), `${label}: ${lines[0]}`);
    assert.doesNotMatch(lines[0], /Unknown command|Unsupported|is now/, label);
    runs++;
  }
  assert.equal(fetches, 0, 'no interpreter call'); assert.equal(fake.posts.length, 0, 'no job');
  assert.equal(existsSync(marker), false, 'no gh sign-in');
  assert.equal(existsSync(setup.state), false, 'no saved state');
  t.diagnostic(`${runs} removed argv`);
});

test('a removed name is refused by the parser before any other rule', () => {
  for (const argv of [['check', 'a\0b'], ['try', '--serve', '70000'], ['check', '--request', 'nope'], ['help', 'try', 'x', 'y']]) {
    assert.throws(() => parseArgv(argv), error => error.exitCode === 2 && / was removed\. Use pdd /.test(error.message), argv.join(' '));
  }
  // `check`, `try` and `sim` as Story words are Story words, not command words.
  assert.deepEqual(parseArgv([SIMULATE, 'try']).operands, ['try']);
  assert.deepEqual(parseArgv([TEST, 'check', 'sim']).operands, ['check', 'sim']);
});

test('quiet forms give the plan, help and usage error of the main name, and no plan has a notice', async () => {
  const outcome = async argv => {
    let plan; try { plan = parseArgv(argv); } catch (error) { plan = { error: error.message }; }
    // Help and usage errors stay local, so run them; any other plan would open a simulation or a chat, so compare only the plan.
    const stdout = sink(), stderr = sink(), code = plan.error || plan.local === 'help' ? await runPdd(argv, { stdout, stderr, workflowRunner: forbidden }) : null;
    assert.equal(Object.hasOwn(plan, 'notice'), false, argv.join(' '));
    return { plan: plan.error ? plan : effect(plan), code, stdout: stdout.text, stderr: stderr.text };
  };
  const pairs = [[['sim'], [SIMULATE], [[], ['place-order', '--max-calls', '5', '--tab', 'world', '--new', '--no-open', '--no-wait', '--agent', 'Codex (work5)'],
      ['place-order', '--cli', '--shell'], ['--serve', '8123'], ['--save-last'], ['--stop', 'place-order'], ['--help'], ['-h'], ['--tab', 'phone'], ['a', 'b'], ['--serve', '70000']]],
    [['workflow', 'start'], ['workflow', RUN], [['feature', 'owner/repo#42', '--agent', 'claude', '--base', 'main'], ['bug', '7'], ['--help'], ['-h'], [], ['81'],
      ['feature', '0'], ['feature', '42', '--agent', 'other']]]];
  for (const [quiet, main, tails] of pairs) for (const tail of tails) {
    for (const head of [[], ['help']]) {
      if (head.length && tail.length) continue;
      const result = await outcome([...head, ...quiet, ...tail]);
      assert.deepEqual(result, await outcome([...head, ...main, ...tail]), [...head, ...quiet, ...tail].join(' '));
      assert.ok(!(result.stdout + result.stderr).includes('workflow start'), [...head, ...quiet, ...tail].join(' '));
    }
  }
  // `pdd test --lint` works like `pdd lint`: no new refusal.
  for (const tail of [[], ['place-order', '--json', '--timeout', '4'], ['--local', '--json'], ['--help']]) {
    assert.deepEqual(effect(parseArgv([TEST, '--lint', ...tail])), effect(parseArgv([LINT, ...tail])), tail.join(' '));
  }
});

// The quiet form adds nothing: the same stdout, stderr, exit code and runner call as the main name.
async function sameRun(argvs, options) {
  const runs = [];
  for (const argv of argvs) {
    const stdout = sink(), stderr = sink();
    runs.push({ code: await runPdd(argv, { stdout, stderr, ...options() }), stdout: stdout.text, stderr: stderr.text });
  }
  return runs;
}

test('workflow start reaches the same runner export as workflow run, with no extra line', async () => {
  const calls = [];
  const runs = await sameRun([['workflow', RUN, 'feature', 'o/r#42', '--agent', 'claude'], ['workflow', 'start', 'feature', 'o/r#42', '--agent', 'claude']], () => ({
    cwd: '/chosen', packageRoot: '/bundle', workflowRunner: { startRun: async input => { calls.push(input); return { exitCode: 0, message: 'started' }; } } }));
  assert.equal(calls.length, 2); assert.deepEqual(calls[0], calls[1]);
  assert.deepEqual(runs[0], runs[1]); assert.equal(runs[0].stdout, 'started\n');
});

test('sim runs like simulate and test --lint like lint, in local modes', async t => {
  const setup = harbor(t);
  const options = () => ({ cwd: setup.repo, env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: 'http://127.0.0.1:9', PATH: '/usr/bin:/bin' } });
  const lint = await sameRun([[LINT, '--local', '--json'], [TEST, '--lint', '--local', '--json']], options);
  assert.equal(lint[0].code, 0, lint[0].stderr); JSON.parse(lint[0].stdout); assert.deepEqual(lint[0], lint[1]);
  const story = await sameRun([[SIMULATE, 'no-such-story'], ['sim', 'no-such-story']], options);
  assert.equal(story[0].code, 2); assert.deepEqual(story[0], story[1]);
});

test('pdd mcp stdout carries only MCP messages', t => {
  const setup = harbor(t);
  const input = [{ jsonrpc: '2.0', id: 1, method: 'initialize', params: { protocolVersion: '2025-06-18', capabilities: {}, clientInfo: { name: 'test', version: '1' } } },
    { jsonrpc: '2.0', id: 2, method: 'tools/list' }].map(message => JSON.stringify(message)).join('\n') + '\n';
  const result = spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), 'mcp'], { cwd: setup.repo, input, encoding: 'utf8', timeout: 20000,
    env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: '/usr/bin:/bin' } });
  assert.equal(result.status, 0, result.stderr);
  const rows = result.stdout.trim().split('\n').map(line => JSON.parse(line));
  assert.deepEqual(rows.map(row => [row.jsonrpc, row.id]), [['2.0', 1], ['2.0', 2]]);
  for (const tool of rows[1].result.tools) assert.match(tool.name, /^simulate_/);
});

test('shell completion offers only the main names', t => {
  const cwd = join(harbor(t).sandbox, 'completion');
  mkdirSync(cwd);
  const choices = (shell, words) => {
    const file = join(cwd, `completion.${shell}`); writeFileSync(file, renderCompletion(shell));
    const list = words.map(word => JSON.stringify(word)).join(' ');
    const result = shell === 'bash'
      ? spawnSync('bash', ['--noprofile', '--norc', '-c', `source "$1"; COMP_WORDS=(pdd ${list} ""); COMP_CWORD=${words.length + 1}; _pdd_complete; printf "%s\\n" "\${COMPREPLY[@]}"`, 'test', file], { encoding: 'utf8' })
      : spawnSync('zsh', ['-f', '-c', `autoload -Uz compinit; compinit -D -i || exit 1; source "$1"; _describe() { print -rl -- "\${choices[@]}"; }; words=(pdd ${list} ""); CURRENT=${words.length + 2}; _pdd`, 'test', file], { encoding: 'utf8' });
    assert.equal(result.status, 0, result.stderr);
    return result.stdout.split('\n').filter(Boolean);
  };
  for (const shell of ['bash', 'zsh']) {
    for (const words of [[], ['help']]) {
      const first = choices(shell, words);
      for (const word of [TEST, LINT, SIMULATE, 'workflow']) assert.ok(first.includes(word), `${shell} ${words} ${word}`);
      for (const word of ['check', 'try', 'sim']) assert.ok(!first.includes(word), `${shell} ${words} ${word}`);
    }
    const workflow = choices(shell, ['workflow']);
    assert.ok(workflow.includes(RUN)); assert.ok(!workflow.includes('start'));
    const testOptions = choices(shell, [TEST]);
    assert.ok(testOptions.includes('--read') && testOptions.includes('--fill-hash'));
    for (const hidden of ['--lint', '--local', '--request']) assert.ok(!testOptions.includes(hidden), `${shell} ${TEST} ${hidden}`);
    assert.ok(choices(shell, [LINT]).includes('--local'));
    assert.ok(choices(shell, [SIMULATE]).includes('--stop'));
    assert.deepEqual(choices(shell, [SIMULATE, '--tab']).sort(), ['call', 'screen', 'terminal', 'world']);
    assert.deepEqual(choices(shell, ['workflow', RUN, 'bug', '7', '--agent']).sort(), ['claude', 'codex']);
  }
});

// The lines that pdd writes name only the new commands. The removal line is built from the catalog words, so
// no source file needs the text `pdd check` or `pdd try`. A server text passes through as data, never as source.
test('no source line names pdd check or pdd try, or calls the simulation the Try', () => {
  const dir = join(root, 'src'), found = [];
  for (const name of readdirSync(dir).filter(file => file.endsWith('.mjs'))) {
    readFileSync(join(dir, name), 'utf8').split('\n').forEach((text, index) => {
      // A whole-line comment is never printed.
      if (!text.trim().startsWith('//') && /\bpdd (?:check|try)\b|\bTry (?:ready|link|page|budget|AI usage|is ready|is serving|tools)\b|PDD Try tools|['"`]pdd try:|\btry_(?:open|state|run|check|save_case)\b/.test(text)) found.push(`${name}:${index + 1}: ${text.trim().slice(0, 120)}`);
    });
  }
  assert.deepEqual(found, []);
});
