import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { CommandInputError, parseArgv } from '../src/argument-parser.mjs';
import { PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { renderCompletion } from '../src/completion.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { harbor, root, sink, temp } from './runtime-fake.mjs';

// Bounded check of user_stories/new-command-names.md, Rules to check (RUNBOOK §17).
// Oracle from the Story: `check` names `pdd test`, or `pdd lint` when `--lint` is one of its words; `try` names
// `pdd simulate`. `sim` and `workflow start` are quiet forms of `simulate` and `workflow run`.
const words = list => list.join(' ');
// The one line names the old and the new command; the test does not pin the rest of the sentence.
const names = (line, before, after) => line.includes(`pdd ${before}`) && line.includes(`pdd ${after}`);
const label = argv => JSON.stringify(argv);
const effect = plan => ({ local: plan.local, operands: plan.operands, options: plan.options, helpPrefix: plan.helpPrefix });
const parse = argv => { try { return { plan: parseArgv(argv) }; } catch (error) { return { error: String(error?.message), input: error instanceof CommandInputError }; } };
const oracle = (command, tail) => command === 'try' ? ['try', 'simulate'] : tail.includes('--lint') ? ['check --lint', 'lint'] : ['check', 'test'];
const QUIET = [{ quiet: ['sim'], main: ['simulate'] }, { quiet: ['workflow', 'start'], main: ['workflow', 'run'] }];
const HEADS = { simulate: [[], ['place-order'], ['place-order', 'unknown-item']], 'workflow run': [[], ['feature', '42'], ['bug', 'owner/repo#7'], ['81'], ['feature', '0']] };

// The input range: every option of the test, lint, simulate and workflow run routes, each without a value, with a good value and with bad values.
function optionSamples() {
  const samples = new Map();
  const add = sample => samples.set(label(sample), sample);
  for (const prefix of [['test'], ['lint'], ['simulate'], ['workflow', 'run']]) {
    const route = PUBLIC_COMMAND_ROUTES.find(item => words(item.prefix) === words(prefix));
    assert.ok(route, `route ${words(prefix)}`);
    for (const option of route.options) {
      const values = { flag: [], text: ['place-order', '--json'], uuid: ['0b5a1f2e-1c2d-4e5f-8a9b-0c1d2e3f4a5b', 'nope'],
        integer: [String(option.min), String(option.max), '0', String(option.max + 1), 'x'], 'optional-integer': ['8123', '0', '70000'],
        value: [...(option.choices ?? []), 'other'] }[option.kind];
      assert.ok(values, `kind ${option.kind}`);
      add([option.name]); for (const value of values) add([option.name, value]);
    }
  }
  for (const extra of [['--bogus'], ['--lint'], ['--local'], ['--', '--lint'], ['--', 'x'], ['-x'], ['place-order'], ['a\u0007b']]) add(extra);
  return [...samples.values()];
}
const SAMPLES = optionSamples();
const HELP = [[], ['--help'], ['-h'], ['-help']];
function tails(heads, pairs = true) {
  const list = [];
  for (const head of heads) for (const help of HELP) {
    list.push([...head, ...help]);
    for (const one of SAMPLES) {
      list.push([...head, ...one, ...help]);
      if (pairs) for (const two of SAMPLES) if (two[0] !== one[0]) list.push([...head, ...one, ...two, ...help]);
    }
  }
  return list;
}

test('removed: every check or try argv, also after help, is one exit-2 line that names the old and the new command', t => {
  let count = 0;
  for (const command of ['check', 'try']) for (const head of [[], ['help']]) for (const tail of tails([[], ['place-order']])) {
    const argv = [...head, command, ...tail], result = parse(argv), [before, after] = oracle(command, tail);
    assert.ok(result.input, `${label(argv)}: a CommandInputError`);
    assert.ok(!result.error.includes('\n') && names(result.error, before, after), `${label(argv)}: ${result.error}`);
    count++;
  }
  // The oracle line itself: one line, the old and the new command, no other word of the input.
  for (const [before, after] of [oracle('check', []), oracle('check', ['--lint']), oracle('try', [])]) {
    const line = parse(before === 'try' ? ['try'] : before.split(' ')).error;
    assert.ok(!line.includes('\n') && line.includes(`pdd ${before}`) && line.includes(`pdd ${after}`), line);
  }
  assert.ok(count > 10000, 'the range reaches every option pair');
  t.diagnostic(`bounds: ${SAMPLES.length} option samples; ${count} removed argv (check, try, help check, help try with 0 to 2 options and a help flag)`);
});

test('quiet: every sim and workflow start argv parses like its main name, with the same plan or usage error and no notice', t => {
  let good = 0, bad = 0, lintSame = 0;
  for (const { quiet, main } of QUIET) for (const tail of tails(HEADS[words(main)])) {
    const short = parse([...quiet, ...tail]), current = parse([...main, ...tail]), argv = label([...quiet, ...tail]);
    assert.equal(!!short.plan, !!current.plan, `${argv}: the quiet and the main name accept the same input`);
    if (current.plan) {
      good++;
      assert.deepEqual(effect(short.plan), effect(current.plan), `${argv}: same plan`);
      for (const plan of [short.plan, current.plan]) assert.equal(Object.hasOwn(plan, 'notice'), false, `${argv}: no notice`);
    } else {
      bad++;
      assert.equal(short.error, current.error, `${argv}: same usage error`);
      assert.doesNotMatch(short.error, /was removed|workflow start|Unknown command/, argv);
    }
  }
  // `pdd test --lint` works like `pdd lint`: no new refusal.
  for (const tail of tails([[], ['place-order']], false)) {
    const lint = parse(['lint', ...tail]);
    if (!lint.plan) continue;
    const same = parse(['test', '--lint', ...tail]);
    assert.ok(same.plan, `test --lint ${tail.join(' ')}: ${same.error}`);
    assert.deepEqual(effect(same.plan), effect(lint.plan), `test --lint ${tail.join(' ')}`);
    lintSame++;
  }
  assert.ok(good > 1000 && bad > 1000 && lintSame > 10, 'the range reaches good and bad parses');
  t.diagnostic(`bounds: ${good + bad} quiet/main argv pairs (${good} good parses, ${bad} usage errors); ${lintSame} test --lint = lint argv`);
});

// Run the public entry for each removed argv: no stdout, one stderr line, no runner call, no fetch, no gh, no saved state.
test('removed names run nothing on runPdd', async t => {
  const setup = harbor(t), bin = join(setup.sandbox, 'bin'), marker = join(setup.sandbox, 'gh-called'); mkdirSync(bin);
  writeFileSync(join(bin, 'gh'), `#!/bin/sh\ntouch '${marker}'\necho fake-test-token\n`, { mode: 0o755 });
  let fetches = 0; const realFetch = globalThis.fetch;
  globalThis.fetch = async () => { fetches++; throw new Error('No network in the formal check.'); };
  t.after(() => { globalThis.fetch = realFetch; });
  const calls = [], state = join(setup.sandbox, 'state');
  const spy = new Proxy({}, { get: (_, name) => typeof name !== 'string' ? undefined : (...input) => { calls.push(name); return { exitCode: 0, message: '' }; } });
  let count = 0;
  for (const command of ['check', 'try']) for (const head of [[], ['help']]) for (const tail of tails([[], ['place-order']], false)) {
    const argv = [...head, command, ...tail], stdout = sink(), stderr = sink(), [before, after] = oracle(command, tail);
    const env = { HOME: setup.home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'http://127.0.0.1:9', PATH: `${bin}:/usr/bin:/bin` };
    const code = await runPdd(argv, { stdout, stderr, cwd: setup.repo, env, packageRoot: root, workflowRunner: spy, workflowAreas: spy,
      mcpServer: spy, runtimeSlots: spy, contracts: spy, product: spy, workflowProve: spy, gitContext: spy });
    assert.equal(code, 2, label(argv)); assert.equal(stdout.text, '', label(argv));
    const lines = stderr.text.split('\n');
    assert.equal(lines.length, 2, `${label(argv)}: one line: ${stderr.text}`); assert.equal(lines[1], '', label(argv));
    assert.ok(names(lines[0], before, after), `${label(argv)}: ${lines[0]}`);
    count++;
  }
  assert.deepEqual(calls, []); assert.equal(fetches, 0, 'no interpreter call');
  assert.equal(existsSync(marker), false, 'no gh call'); assert.equal(existsSync(state), false, 'no saved state');
  t.diagnostic(`bounds: ${count} removed argv on runPdd; 0 runner calls, 0 fetches, 0 gh calls`);
});

// Every help argv: the root, every catalog prefix, the quiet forms. The output must name no old or quiet command.
const OLD_IN_HELP = [/\bpdd check\b/, /\bpdd try\b/, /\bworkflow start\b/];
function helpArgvs() {
  const prefixes = new Map();
  for (const route of PUBLIC_COMMAND_ROUTES) for (let length = 1; length <= route.prefix.length; length++) {
    const prefix = route.prefix.slice(0, length);
    if (!['help', '--version'].includes(prefix[0])) prefixes.set(words(prefix), prefix);
  }
  const list = [[], ['--help'], ['-h'], ['help']];
  for (const prefix of [...prefixes.values(), ...QUIET.map(item => item.quiet)]) {
    list.push(['help', ...prefix], [...prefix, '--help'], [...prefix, '-h']);
  }
  return list;
}

test('help shows only the main names, for every help argv', async t => {
  const list = helpArgvs();
  for (const argv of list) {
    const stdout = sink(), stderr = sink();
    assert.equal(await runPdd(argv, { stdout, stderr }), 0, label(argv)); assert.equal(stderr.text, '', label(argv));
    assert.ok(stdout.text.includes('  pdd '), `${label(argv)}: help has forms`);
    for (const pattern of OLD_IN_HELP) assert.doesNotMatch(stdout.text, pattern, label(argv));
  }
  t.diagnostic(`bounds: ${list.length} help argv`);
});

// Ask each shell for its choices in every context built from the catalog prefixes, the old and quiet names and option values.
function completionChoices(t, script, shell, contexts) {
  const dir = temp(t), file = join(dir, `pdd.${shell}`);
  writeFileSync(file, script);
  const input = contexts.map(words).join('\n') + '\n';
  const body = shell === 'bash'
    ? 'source "$1"; while IFS= read -r ctx; do eval "COMP_WORDS=(pdd $ctx \\"\\")"; COMP_CWORD=$(( ${#COMP_WORDS[@]} - 1 )); COMPREPLY=(); _pdd_complete; printf "%s\\n" "${COMPREPLY[@]}" "---"; done'
    : 'autoload -Uz compinit; compinit -D -i || exit 1; source "$1"; _describe() { print -rl -- "${choices[@]}"; }; while IFS= read -r ctx; do words=(pdd ${=ctx} ""); CURRENT=${#words}; choices=(); _pdd; print -- "---"; done';
  const args = shell === 'bash' ? ['--noprofile', '--norc', '-c', body, 'pdd', file] : ['-f', '-c', body, 'pdd', file];
  const result = spawnSync(shell, args, { input, encoding: 'utf8', env: { PATH: '/usr/bin:/bin', HOME: dir } });
  assert.equal(result.status, 0, result.stderr);
  const blocks = result.stdout.split('---\n'); blocks.pop();
  assert.equal(blocks.length, contexts.length, result.stdout);
  return blocks.map(block => block.split('\n').filter(Boolean));
}
const SHELLS = ['bash', ...(spawnSync('zsh', ['-fc', 'true']).status === 0 ? ['zsh'] : [])];
const NOT_OFFERED = [['check'], ['try'], ['sim'], ['workflow', 'start']];
function completionContexts() {
  const contexts = new Map(), add = context => contexts.set(words(context), context);
  add([]); add(['help']);
  for (const route of [...PUBLIC_COMMAND_ROUTES, ...NOT_OFFERED.map(prefix => ({ prefix, options: [] }))]) {
    if (route.prefix[0] === '--version') continue;
    for (let length = 1; length <= route.prefix.length; length++) { add(route.prefix.slice(0, length)); add(['help', ...route.prefix.slice(0, length)]); }
    for (const option of route.options) if (option.choices) add([...route.prefix, option.name]);
  }
  contexts.delete('workflow run'); // that context asks the installed pdd for workflow names
  return [...contexts.values()];
}

test('shell completion offers no removed or quiet name in any context', t => {
  const contexts = completionContexts();
  for (const shell of SHELLS) {
    const all = completionChoices(t, renderCompletion(shell), shell, contexts);
    contexts.forEach((context, index) => {
      for (const choice of all[index]) {
        const typed = [...context, choice].filter((word, at) => !(at === 0 && word === 'help'));
        assert.ok(!NOT_OFFERED.some(prefix => words(typed) === words(prefix)), `${shell} "${words(context)}" offers ${choice}`);
      }
    });
    const at = context => all[contexts.findIndex(item => words(item) === context)];
    for (const name of ['test', 'lint', 'simulate', 'workflow']) assert.ok(at('').includes(name), `${shell}: root offers ${name}`);
    assert.ok(at('workflow').includes('run'), `${shell}: workflow offers run`);
  }
  t.diagnostic(`bounds: ${contexts.length} contexts x ${SHELLS.join(', ')}`);
});

// A later rename is one edit: change only NAMES in a copy of src; help, parse, removal lines and completion follow it.
test('the new words are data in one place', async t => {
  const copy = join(temp(t), 'src'); cpSync(join(root, 'src'), copy, { recursive: true });
  const file = join(copy, 'command-catalog.mjs'), source = readFileSync(file, 'utf8');
  const RENAMED = { test: 'exam', lint: 'sweep', simulate: 'sandbox', run: 'begin' };
  const edited = source.replace(/(export const NAMES = Object\.freeze\()\{[^}]*\}/, (_, head) => `${head}${JSON.stringify(RENAMED)}`);
  assert.notEqual(edited, source, 'NAMES holds the words');
  assert.equal(edited.split('\n').filter((line, index) => line !== source.split('\n')[index]).length, 1, 'one line changes');
  writeFileSync(file, edited);
  const cli = await import(pathToFileURL(join(copy, 'pdd-cli.mjs')));
  const parser = await import(pathToFileURL(join(copy, 'argument-parser.mjs')));
  const completion = await import(pathToFileURL(join(copy, 'completion.mjs')));
  const help = cli.renderHelp();
  for (const word of ['exam', 'sweep', 'sandbox']) assert.match(help, new RegExp(`\\n  pdd ${word}\\b`), word);
  assert.match(help, /\n {2}pdd workflow begin\b/); assert.match(help, /\bworkflow begin\b.*Herdr/);
  for (const word of ['test', 'lint', 'simulate']) assert.doesNotMatch(help, new RegExp(`\\bpdd ${word}\\b`), word);
  assert.doesNotMatch(help, /\bworkflow (?:start|run)\b/);
  for (const [before, after] of [[['check'], 'exam'], [['check', '--lint'], 'sweep'], [['try'], 'sandbox']]) {
    assert.throws(() => parser.parseArgv([...before, '--help']), error => error.message.includes(`pdd ${words(before)}`) && error.message.includes(`pdd ${after}`));
  }
  assert.deepEqual(effect(parser.parseArgv(['exam', '--lint', '--local'])), effect(parser.parseArgv(['sweep', '--local'])));
  assert.deepEqual(parser.parseArgv(['sim', '--help']), parser.parseArgv(['sandbox', '--help']), 'the quiet form follows the route');
  assert.deepEqual(parser.parseArgv(['workflow', 'start', '--help']), parser.parseArgv(['workflow', 'begin', '--help']));
  for (const shell of SHELLS) {
    const [rootChoices, workflowChoices] = completionChoices(t, completion.renderCompletion(shell), shell, [[], ['workflow']]);
    for (const word of ['exam', 'sweep', 'sandbox']) assert.ok(rootChoices.includes(word), `${shell} ${word}`);
    for (const word of ['test', 'lint', 'simulate', 'check', 'try']) assert.ok(!rootChoices.includes(word), `${shell} ${word}`);
    assert.ok(workflowChoices.includes('begin') && !workflowChoices.includes('start') && !workflowChoices.includes('run'), shell);
  }
});
