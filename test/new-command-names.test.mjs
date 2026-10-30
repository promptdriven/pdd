import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parseArgv } from '../src/argument-parser.mjs';
import { NAMES } from '../src/command-catalog.mjs';
import { renderCompletion } from '../src/completion.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { fakeRuntime, harbor, root, sink } from './runtime-fake.mjs';

// Rules of user_stories/new-command-names.md that the runPdd vectors cannot see: the same code,
// the notice on stderr only and once, clean --json and mcp stdout, and completion.
const { test: TEST, lint: LINT, simulate: SIMULATE, start: START } = NAMES;
const names = (line, before, after) => line.includes(`pdd ${before}`) && line.includes(`pdd ${after}`);
const effect = plan => ({ local: plan.local, operands: plan.operands, options: plan.options, helpPrefix: plan.helpPrefix });
const noRunner = new Proxy({}, { get() { assert.fail('A usage error must not dispatch'); } });

// [former words, new words, argument tails]; each tail keeps the options that the former name had.
const PAIRS = [
  [['check'], [TEST], [[], ['place-order', '--json', '--details', '--timeout', '4', '--max-calls', '20'], ['--read', 'b1', '--json', '--timeout', '3'],
    ['--retry', 'b1', '--json'], ['--fill-hash'], ['--files', 'place-order', '--app-map', 'map.json'],
    ['--screen', 'http://127.0.0.1:1/', '--drawing', 'a.ui.svg', '--json'], ['--', '--lint'], ['--help'], ['-h']]],
  [['check', '--lint'], [LINT], [[], ['place-order', 'unknown-item', '--json', '--timeout', '4'], ['--local', '--json'], ['--help']]],
  [['try'], [SIMULATE], [[], ['place-order', '--max-calls', '5', '--tab', 'world', '--new', '--no-open', '--no-wait', '--agent', 'Codex (work5)'],
    ['place-order', '--cli', '--shell'], ['--serve', '8123'], ['--save-last'], ['--stop', 'place-order'], ['--help']]],
  [['workflow', 'run'], ['workflow', START], [['feature', 'owner/repo#42', '--agent', 'claude', '--base', 'main'], ['bug', '7'], ['--help']]],
];

test('an old name gives the same plan as its new name, and only the old name carries a notice', () => {
  for (const [before, after, tails] of PAIRS) for (const tail of tails) {
    const old = parseArgv([...before, ...tail]), plan = parseArgv([...after, ...tail]);
    assert.deepEqual(effect(old), effect(plan), [...before, ...tail].join(' '));
    assert.equal(plan.notice, undefined, [...after, ...tail].join(' '));
    // `check -- --lint` has the story "--lint", not the flag, so its notice names `pdd test`, not `pdd lint`.
    assert.ok(names(old.notice, before.join(' '), after.join(' ')), old.notice);
  }
  // `pdd test --lint` works like `pdd lint`, with no notice and no new refusal.
  for (const tail of [[], ['place-order', '--json', '--timeout', '4'], ['--local', '--json'], ['--help']]) {
    const plan = parseArgv([TEST, '--lint', ...tail]);
    assert.deepEqual(effect(plan), effect(parseArgv([LINT, ...tail]))); assert.equal(plan.notice, undefined);
  }
  assert.ok(names(parseArgv(['check', '--json', '--lint']).notice, 'check --lint', LINT), 'the flag may stand anywhere');
  assert.ok(names(parseArgv(['help', 'try']).notice, 'try', SIMULATE));
  assert.ok(names(parseArgv(['help', 'workflow', 'run']).notice, 'workflow run', `workflow ${START}`));
});

test('sim is the short form of simulate: the same plan, help and usage error, and never a notice', async () => {
  const outcome = async argv => {
    let plan; try { plan = parseArgv(argv); } catch (error) { plan = { error: error.message }; }
    // Help and usage errors stay local, so run them; any other plan would open a simulation, so compare only the plan.
    const stdout = sink(), stderr = sink(), code = plan.error || plan.local === 'help' ? await runPdd(argv, { stdout, stderr }) : null;
    return { plan: plan.error ? plan : effect(plan), notice: plan.notice, code, stdout: stdout.text, stderr: stderr.text };
  };
  const [, , tails] = PAIRS.find(([before]) => before[0] === 'try');
  for (const tail of [...tails, ['-h'], ['--tab', 'phone'], ['a', 'b'], ['--serve', '70000']]) {
    const short = await outcome(['sim', ...tail]);
    assert.deepEqual(short, await outcome([SIMULATE, ...tail]), ['sim', ...tail].join(' '));
    assert.equal(short.notice, undefined); assert.ok(!/ is now /.test(short.stderr), short.stderr);
  }
  assert.deepEqual(parseArgv(['help', 'sim']).helpPrefix, [SIMULATE]); assert.equal(parseArgv(['help', 'sim']).notice, undefined);
  // Only the first command word is the short form; `sim` as a Story name stays a Story name.
  assert.deepEqual(parseArgv([SIMULATE, 'sim']).operands, ['sim']);
  assert.deepEqual(parseArgv([TEST, 'sim']).operands, ['sim']);
});

test('a usage error of an old name prints the same message as the new name, with no notice', async () => {
  const bad = [[['check'], [TEST], [['--bogus'], ['--max-calls', '0'], ['--timeout', 'x'], ['--lint', '--lint'], ['--request', 'nope']]],
    [['try'], [SIMULATE], [['--tab', 'phone'], ['a', 'b'], ['--serve', '70000']]],
    [['workflow', 'run'], ['workflow', START], [[], ['feature', '0'], ['feature', '42', '--agent', 'other'], ['../bad', '1']]]];
  for (const [before, after, tails] of bad) for (const tail of tails) {
    const results = [];
    for (const argv of [[...before, ...tail], [...after, ...tail]]) {
      const stdout = sink(), stderr = sink();
      results.push({ code: await runPdd(argv, { stdout, stderr, workflowRunner: noRunner }), stdout: stdout.text, stderr: stderr.text });
    }
    assert.equal(results[0].code, 2, [...before, ...tail].join(' ')); assert.deepEqual(results[0], results[1], [...before, ...tail].join(' '));
    assert.equal(results[0].stderr.split('\n').filter(Boolean).length, 1, results[0].stderr);
    assert.ok(!names(results[0].stderr, before.join(' '), after.join(' ')), results[0].stderr);
  }
});

// The old name adds exactly one notice line in front of the new name's stderr; stdout and the exit code stay the same.
async function sameRun(argvs, options) {
  const runs = [];
  for (const argv of argvs) {
    const stdout = sink(), stderr = sink();
    const code = await runPdd(argv, { stdout, stderr, ...options(argv) });
    runs.push({ argv, code, stdout: stdout.text, stderr: stderr.text });
  }
  return runs;
}
function assertNotice([old, ...current], before, after, normalize = text => text) {
  for (const run of current) {
    assert.equal(run.code, old.code, run.argv.join(' '));
    assert.equal(normalize(run.stdout), normalize(old.stdout), run.argv.join(' '));
    assert.ok(!/ is now /.test(run.stdout + run.stderr), run.argv.join(' '));
  }
  const [notice, ...rest] = old.stderr.split('\n');
  assert.ok(names(notice, before, after), old.stderr);
  assert.equal(normalize(rest.join('\n')), normalize(current[0].stderr), 'the notice is the only extra stderr line');
  assert.ok(!old.stdout.includes(' is now '), 'never on stdout');
}

test('workflow run reaches the same runner export as workflow start, with the notice once on stderr', async () => {
  const calls = [];
  const runs = await sameRun([['workflow', 'run', 'feature', 'o/r#42', '--agent', 'claude'], ['workflow', START, 'feature', 'o/r#42', '--agent', 'claude']], () => ({
    cwd: '/chosen', packageRoot: '/bundle', workflowRunner: { startRun: async input => { calls.push(input); return { exitCode: 0, message: 'started' }; } } }));
  assert.equal(calls.length, 2); assert.deepEqual(calls[0], calls[1]);
  assertNotice(runs, 'workflow run', `workflow ${START}`);
});

test('local check, lint and Try modes of an old name keep stdout, --json and the exit code', async t => {
  const setup = harbor(t);
  const options = () => ({ cwd: setup.repo, env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: 'http://127.0.0.1:9', PATH: '/usr/bin:/bin' } });
  const files = await sameRun([['check', '--files', 'place-order'], [TEST, '--files', 'place-order']], options);
  assert.equal(files[0].code, 0, files[0].stderr); assertNotice(files, 'check', TEST);
  const lint = await sameRun([['check', '--lint', '--local', '--json'], [LINT, '--local', '--json'], [TEST, '--lint', '--local', '--json']], options);
  assert.equal(lint[0].code, 0, lint[0].stderr); JSON.parse(lint[0].stdout); assertNotice(lint, 'check --lint', LINT);
  const story = await sameRun([['try', 'no-such-story'], [SIMULATE, 'no-such-story'], ['sim', 'no-such-story']], options);
  assert.equal(story[0].code, 2); assertNotice(story, 'try', SIMULATE);
  assert.equal(story[2].stderr, story[1].stderr, 'sim runs like simulate');
});

test('an old name sends the same interpreter jobs and prints the same --json result', async t => {
  const setup = harbor(t), bin = join(setup.sandbox, 'bin'); mkdirSync(bin);
  writeFileSync(join(bin, 'gh'), '#!/bin/sh\nif [ "$1" = auth ]; then echo fake-test-token; else echo "octo 4242"; fi\n', { mode: 0o755 });
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  let state = 0;
  const options = () => ({ cwd: setup.repo, env: { HOME: setup.home, PDD_STATE_DIR: join(setup.sandbox, `state-${state++}`), PDD_RUNTIME_URL: fake.origin, PATH: `${bin}:/usr/bin:/bin` } });
  // Request IDs, batch names, report links and run times are new for every run.
  const normalize = text => text.replace(/[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}/g, 'ID').replace(/\/r\/[0-9a-f]{32}/g, '/r/R')
    .replace(/"batch":"[^"]+"/g, '"batch":"B"').replace(/--read \S+/g, '--read B').replace(/\d{4}-\d\d-\d\dT[\d:.]+Z/g, 'TIME').replace(/\b\d\d:\d\d(?::\d\d)?\b/g, 'HH:MM').replace(/ · \d+ s/g, '').replace(/"seconds":[\d.]+/g, '"seconds":S');
  for (const [argvs, before, after, commands] of [
    [[['check', 'place-order', '--json'], [TEST, 'place-order', '--json']], 'check', TEST, ['lint', 'check']],
    [[['check', '--lint', 'place-order', '--json'], [LINT, 'place-order', '--json']], 'check --lint', LINT, ['lint']]]) {
    const start = fake.posts.length, runs = await sameRun(argvs, options);
    assert.equal(runs[0].code, 0, runs[0].stdout + runs[0].stderr); JSON.parse(runs[0].stdout);
    assertNotice(runs, before, after, normalize);
    const sent = fake.posts.slice(start).map(entry => entry.command);
    assert.deepEqual(sent, [...commands, ...commands], 'each name sends the same jobs');
  }
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
  assert.ok(!/ is now /.test(result.stdout + result.stderr));
});

test('shell completion offers only the new names', t => {
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
    assert.ok(workflow.includes(START)); assert.ok(!workflow.includes('run'));
    const testOptions = choices(shell, [TEST]);
    assert.ok(testOptions.includes('--read') && testOptions.includes('--fill-hash'));
    for (const hidden of ['--lint', '--local', '--request']) assert.ok(!testOptions.includes(hidden), `${shell} ${TEST} ${hidden}`);
    assert.ok(choices(shell, [LINT]).includes('--local'));
    assert.ok(choices(shell, [SIMULATE]).includes('--stop'));
    assert.deepEqual(choices(shell, [SIMULATE, '--tab']).sort(), ['call', 'screen', 'terminal', 'world']);
    assert.deepEqual(choices(shell, ['workflow', START, 'bug', '7', '--agent']).sort(), ['claude', 'codex']);
  }
});
