import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { parseArgv } from '../src/argument-parser.mjs';
import { PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { renderCompletion } from '../src/completion.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { harbor, root, sink, temp } from './runtime-fake.mjs';

// Bounded check of user_stories/new-command-names.md, Rules to check (RUNBOOK §17).
// Oracle from the Story: each former name and its new name. `check --lint` is `check` with the flag --lint.
const RENAMES = [
  { before: ['check'], after: ['test'] },
  { before: ['check', '--lint'], after: ['lint'] },
  { before: ['try'], after: ['simulate'] },
  { before: ['workflow', 'run'], after: ['workflow', 'start'] },
];
// The typed pairs: an old argv and the new argv with the same tail. `check --lint T` pairs with `test --lint T`.
const PAIRS = [
  { before: ['check'], after: ['test'], operands: [[], ['place-order'], ['place-order', 'unknown-item']] },
  { before: ['try'], after: ['simulate'], operands: [[], ['place-order'], ['place-order', 'unknown-item']] },
  { before: ['workflow', 'run'], after: ['workflow', 'start'], operands: [[], ['feature', '42'], ['bug', 'owner/repo#7'], ['81'], ['feature', '0']] },
];
const words = list => list.join(' ');
const isNotice = line => / is now /.test(line) || RENAMES.some(({ before, after }) => line.includes(`pdd ${words(before)}`) && line.includes(`pdd ${words(after)}`));
const notices = text => text.split('\n').filter(isNotice);
const effect = plan => ({ local: plan.local, operands: plan.operands, options: plan.options, helpPrefix: plan.helpPrefix });
const parse = argv => { try { return { plan: parseArgv(argv) }; } catch (error) { return { error: String(error?.message) }; } };
const label = argv => JSON.stringify(argv);

// The input range: every option of the four new routes, each without a value, with a good value and with bad values.
function optionSamples() {
  const samples = new Map();
  const add = sample => samples.set(label(sample), sample);
  for (const after of [['test'], ['lint'], ['simulate'], ['workflow', 'start']]) {
    const route = PUBLIC_COMMAND_ROUTES.find(item => words(item.prefix) === words(after));
    assert.ok(route, `route ${words(after)}`);
    for (const option of route.options) {
      const values = { flag: [], text: ['place-order', '--json'], uuid: ['0b5a1f2e-1c2d-4e5f-8a9b-0c1d2e3f4a5b', 'nope'],
        integer: [String(option.min), String(option.max), '0', String(option.max + 1), 'x'], 'optional-integer': ['8123', '0', '70000'],
        value: [...(option.choices ?? []), 'other'] }[option.kind];
      assert.ok(values, `kind ${option.kind}`);
      add([option.name]); for (const value of values) add([option.name, value]);
    }
  }
  for (const extra of [['--bogus'], ['--lint'], ['--local'], ['--', '--lint'], ['--', 'x'], ['-x']]) add(extra);
  return [...samples.values()];
}
const SAMPLES = optionSamples();
const HELP = [[], ['--help'], ['-h']];

test('same code: every old argv parses like its new argv, and only the old name has a notice', t => {
  let accepted = 0, refused = 0, lintSame = 0, shortSame = 0;
  for (const { before, after, operands } of PAIRS) {
    const tails = [];
    for (const head of operands) for (const help of HELP) {
      tails.push([...head, ...help]);
      for (const one of SAMPLES) {
        tails.push([...head, ...one, ...help]);
        for (const two of SAMPLES) if (two[0] !== one[0]) tails.push([...head, ...one, ...two, ...help]);
      }
    }
    for (const tail of tails) {
      const old = parse([...before, ...tail]), current = parse([...after, ...tail]), argv = label([...before, ...tail]);
      assert.equal(!!old.plan, !!current.plan, `${argv}: the old and the new name accept the same input`);
      if (current.plan) {
        accepted++;
        assert.deepEqual(effect(old.plan), effect(current.plan), `${argv}: same plan`);
        assert.equal(current.plan.notice, undefined, `${label([...after, ...tail])}: no notice for a new name`);
        const lint = current.plan.options?.['--lint'] === true || words(current.plan.helpPrefix ?? []) === 'lint';
        const rename = RENAMES.find(item => words(item.before) === (lint ? 'check --lint' : words(before)));
        assert.ok(old.plan.notice.includes(`pdd ${words(rename.before)}`) && old.plan.notice.includes(`pdd ${words(rename.after)}`), `${argv}: ${old.plan.notice}`);
        if (!lint) assert.ok(!old.plan.notice.includes('lint'), `${argv}: ${old.plan.notice}`);
      } else {
        refused++;
        assert.equal(old.error.split(`pdd ${words(before)} `).join(`pdd ${words(after)} `), current.error, `${argv}: same usage error`);
      }
      // `pdd sim` is the short form of `pdd simulate`: the same plan or the same usage error, and no notice.
      if (words(after) === 'simulate') {
        const short = parse(['sim', ...tail]);
        assert.deepEqual(short.plan ? effect(short.plan) : short, current.plan ? effect(current.plan) : current, label(['sim', ...tail]));
        assert.equal(short.plan?.notice, undefined, label(['sim', ...tail]));
        shortSame++;
      }
      // `pdd test --lint` works like `pdd lint`: no new refusal and no notice.
      if (words(after) === 'test') {
        const lint = parse(['lint', ...tail]);
        if (lint.plan) {
          const same = parse(['test', '--lint', ...tail]);
          assert.ok(same.plan, `test --lint ${tail.join(' ')}: ${same.error}`);
          assert.deepEqual(effect(same.plan), effect(lint.plan), `test --lint ${tail.join(' ')}`);
          assert.equal(same.plan.notice, undefined); assert.equal(lint.plan.notice, undefined);
          lintSame++;
        }
      }
    }
  }
  // Every catalog route, typed with its own words, has no notice; an old word as an operand is not an old name.
  for (const route of PUBLIC_COMMAND_ROUTES) for (const tail of route.id === 'help' ? [[], ['test'], ['workflow', 'start']] : [[], ['--help'], ['check'], ['try'], ['run']]) {
    const result = parse([...route.prefix, ...tail]);
    assert.equal(result.plan?.notice, undefined, label([...route.prefix, ...tail]));
  }
  assert.ok(accepted > 1000 && refused > 1000 && lintSame > 100 && shortSame > 1000, 'the range reaches both good and bad parses');
  t.diagnostic(`bounds: ${SAMPLES.length} option samples; ${accepted + refused} old/new argv pairs (${accepted} good parses, ${refused} usage errors); ${lintSame} test --lint = lint pairs; ${shortSame} sim = simulate argv`);
});

// Run the public entry for each old and new argv: help, usage errors, the workflow runner (a fake) and the interpreter
// routes (a fake gh that is not logged in, and a fetch that fails the test), so nothing leaves this machine.
test('notice: once, on stderr, first, only after a good parse; same exit code and stdout as the new name', async t => {
  const setup = harbor(t), bin = join(setup.sandbox, 'bin'); mkdirSync(bin);
  writeFileSync(join(bin, 'gh'), '#!/bin/sh\necho "not logged in" >&2\nexit 1\n', { mode: 0o755 });
  let fetches = 0; const realFetch = globalThis.fetch;
  globalThis.fetch = async () => { fetches++; throw new Error('No network in the formal check.'); };
  t.after(() => { globalThis.fetch = realFetch; });
  async function run(argv) {
    const stdout = sink(), stderr = sink(), calls = [];
    const workflowRunner = new Proxy({}, { get: (_, name) => typeof name !== 'string' ? undefined
      : async input => { calls.push([name, input]); return { exitCode: 0, message: `runner ${name}` }; } });
    const env = { HOME: setup.home, PDD_STATE_DIR: mkdtempSync(join(setup.sandbox, 'state-')), PDD_RUNTIME_URL: 'http://127.0.0.1:9', PATH: `${bin}:/usr/bin:/bin` };
    const code = await runPdd(argv, { stdout, stderr, cwd: setup.repo, env, workflowRunner, packageRoot: root });
    return { code, stdout: stdout.text, stderr: stderr.text, calls };
  }
  const argvs = [];
  for (const { before, after, operands } of PAIRS) {
    for (const head of operands) for (const help of HELP) {
      argvs.push([before, after, [...head, ...help]]);
      if (!help.length || help[0] === '--help') for (const one of SAMPLES) argvs.push([before, after, [...head, ...one, ...help]]);
    }
    for (const tail of [[], ['x'], ['--json']]) argvs.push([['help', ...before], ['help', ...after], tail]);
  }
  argvs.push([['check', '--lint'], ['test', '--lint'], ['--local', '--json']], [['check', '--lint'], ['lint'], ['--local', '--json']]);
  let good = 0, bad = 0, runtimeRuns = 0, runnerRuns = 0, shortRuns = 0;
  for (const [before, after, tail] of argvs) {
    const oldArgv = [...before, ...tail], newArgv = [...after, ...tail], name = label(oldArgv);
    const old = await run(oldArgv), current = await run(newArgv);
    assert.equal(notices(current.stderr).length, 0, `${label(newArgv)}: no notice for a new name`);
    assert.equal(notices(old.stdout).length + notices(current.stdout).length, 0, `${name}: never a notice on stdout`);
    assert.equal(old.code, current.code, `${name}: same exit code`);
    assert.equal(old.stdout, current.stdout, `${name}: same stdout`);
    assert.deepEqual(old.calls, current.calls, `${name}: same runner call`);
    if (words(after).endsWith('simulate')) {
      const shortArgv = [...after.slice(0, -1), 'sim', ...tail], short = await run(shortArgv);
      assert.deepEqual(short, current, `${label(shortArgv)}: same result as simulate, no notice`);
      shortRuns++;
    }
    if (parse(newArgv).plan) {
      good++;
      const [first, ...rest] = old.stderr.split('\n');
      assert.equal(notices(old.stderr).length, 1, `${name}: one notice: ${old.stderr}`);
      assert.ok(isNotice(first), `${name}: the notice comes first: ${old.stderr}`);
      assert.equal(rest.join('\n'), current.stderr, `${name}: the notice is the only extra stderr line`);
      if (parse(newArgv).plan.local === 'runtime-check' || parse(newArgv).plan.local === 'runtime-try') runtimeRuns++;
      if (old.calls.length) runnerRuns++;
    } else {
      bad++;
      assert.equal(old.code, 2, `${name}: usage error`);
      assert.equal(notices(old.stderr).length, 0, `${name}: no notice on a usage error: ${old.stderr}`);
      assert.ok(!old.stderr.includes('Unknown command'), `${name}: ${old.stderr}`);
      assert.equal(old.stderr.split(`pdd ${words(before)} `).join(`pdd ${words(after)} `), current.stderr, `${name}: same usage error`);
    }
  }
  assert.equal(fetches, 0, 'no interpreter call');
  assert.ok(good > 100 && bad > 100 && runtimeRuns > 50 && runnerRuns > 0 && shortRuns > 50, 'the range reaches each kind of run');
  t.diagnostic(`bounds: ${argvs.length} old/new argv pairs on runPdd (${good} good parses: ${runtimeRuns} interpreter routes, ${runnerRuns} runner calls; ${bad} usage errors); ${shortRuns} sim runs; 0 fetches`);
});

// Every help argv: the root, every catalog prefix, the old names. The output must not name an old command.
const OLD_IN_HELP = [/\bpdd check\b/, /\bpdd try\b/, /\bworkflow run\b/];
function helpArgvs() {
  const prefixes = new Map();
  for (const route of PUBLIC_COMMAND_ROUTES) for (let length = 1; length <= route.prefix.length; length++) {
    const prefix = route.prefix.slice(0, length);
    if (!['help', '--version'].includes(prefix[0])) prefixes.set(words(prefix), prefix);
  }
  const list = [[], ['--help'], ['-h'], ['help']];
  // `pdd help` takes command words only, so `check --lint` has its help as `pdd check --lint --help` (Story AC5).
  for (const prefix of [...prefixes.values(), ...RENAMES.map(item => item.before), ['sim']]) {
    if (!prefix.some(word => word.startsWith('-'))) list.push(['help', ...prefix]);
    list.push([...prefix, '--help'], [...prefix, '-h']);
  }
  return list;
}

test('help shows only the new names, for every help argv', async t => {
  const list = helpArgvs();
  for (const argv of list) {
    const stdout = sink(), stderr = sink();
    assert.equal(await runPdd(argv, { stdout, stderr }), 0, label(argv));
    assert.ok(stdout.text.includes('  pdd '), `${label(argv)}: help has forms`);
    for (const pattern of OLD_IN_HELP) assert.doesNotMatch(stdout.text, pattern, label(argv));
  }
  t.diagnostic(`bounds: ${list.length} help argv`);
});

// Ask each shell for its choices in every context built from the catalog prefixes, the old names and option values.
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
function completionContexts() {
  const contexts = new Map(), add = context => contexts.set(words(context), context);
  add([]); add(['help']);
  for (const route of [...PUBLIC_COMMAND_ROUTES, ...RENAMES.map(item => ({ prefix: item.before, options: [] }))]) {
    if (route.prefix[0] === '--version') continue;
    for (let length = 1; length <= route.prefix.length; length++) { add(route.prefix.slice(0, length)); add(['help', ...route.prefix.slice(0, length)]); }
    for (const option of route.options) if (option.choices) add([...route.prefix, option.name]);
  }
  contexts.delete('workflow start'); // that context asks the installed pdd for workflow names
  return [...contexts.values()];
}

test('shell completion offers no old name in any context', t => {
  const contexts = completionContexts();
  for (const shell of SHELLS) {
    const all = completionChoices(t, renderCompletion(shell), shell, contexts);
    contexts.forEach((context, index) => {
      for (const choice of all[index]) {
        const typed = [...context, choice].filter((word, at) => !(at === 0 && word === 'help'));
        assert.ok(!RENAMES.some(({ before }) => words(typed) === words(before)), `${shell} "${words(context)}" offers ${choice}`);
        assert.ok(!(typed.length === 1 && typed[0] === 'sim'), `${shell} "${words(context)}" offers the short form ${choice}`);
      }
    });
    const at = context => all[contexts.findIndex(item => words(item) === context)];
    for (const name of ['test', 'lint', 'simulate', 'workflow']) assert.ok(at('').includes(name), `${shell}: root offers ${name}`);
    assert.ok(at('workflow').includes('start'), `${shell}: workflow offers start`);
  }
  t.diagnostic(`bounds: ${contexts.length} contexts x ${SHELLS.join(', ')}`);
});

// A later rename is one edit: change only NAMES in a copy of src; help, parse, notices and completion follow it.
test('the new words are data in one place', async t => {
  const copy = join(temp(t), 'src'); cpSync(join(root, 'src'), copy, { recursive: true });
  const file = join(copy, 'command-catalog.mjs'), source = readFileSync(file, 'utf8');
  const RENAMED = { test: 'exam', lint: 'sweep', simulate: 'sandbox', start: 'begin' };
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
  assert.doesNotMatch(help, /\bworkflow start\b/);
  for (const pattern of OLD_IN_HELP) assert.doesNotMatch(help, pattern);
  for (const [before, after] of [[['check'], ['exam']], [['check', '--lint'], ['sweep']], [['try'], ['sandbox']], [['workflow', 'run'], ['workflow', 'begin']]]) {
    const plan = parser.parseArgv([...before, '--help']);
    assert.deepEqual(plan.helpPrefix, after); assert.ok(plan.notice.includes(`pdd ${words(before)}`) && plan.notice.includes(`pdd ${words(after)}`), plan.notice);
    assert.equal(parser.parseArgv([...after, '--help']).notice, undefined);
  }
  assert.deepEqual(effect(parser.parseArgv(['exam', '--lint', '--local'])), effect(parser.parseArgv(['sweep', '--local'])));
  assert.deepEqual(parser.parseArgv(['sim', '--help']), parser.parseArgv(['sandbox', '--help']), 'the short form follows the route');
  for (const shell of SHELLS) {
    const [rootChoices, workflowChoices] = completionChoices(t, completion.renderCompletion(shell), shell, [[], ['workflow']]);
    for (const word of ['exam', 'sweep', 'sandbox']) assert.ok(rootChoices.includes(word), `${shell} ${word}`);
    for (const word of ['test', 'lint', 'simulate', 'check', 'try']) assert.ok(!rootChoices.includes(word), `${shell} ${word}`);
    assert.ok(workflowChoices.includes('begin') && !workflowChoices.includes('start') && !workflowChoices.includes('run'), shell);
  }
});
