import test from 'node:test';
import assert from 'node:assert/strict';
import { runPdd } from '../src/pdd-cli.mjs';

const helpWords = ['--help', '-h', '-help'];
const capture = () => ({ text: '', write(value) { this.text += value; } });
async function invoke(argv) {
  const stdout = capture(), stderr = capture(), calls = [], input = [...argv];
  const exit = await runPdd(input, {
    cwd: '/chosen', stdout, stderr,
    workflowProve: { proveRun: async value => { calls.push(value); return { exitCode: 0, message: 'accepted' }; } }
  });
  assert.deepEqual(input, argv, 'Parsing must preserve the caller argv');
  return { exit, calls, stdout: stdout.text, stderr: stderr.text };
}
async function accepted(argv, test, expect) {
  assert.deepEqual(await invoke(argv), {
    exit: 0, calls: [{ ref: '2594', test, expect, cwd: '/chosen' }], stdout: 'accepted\n', stderr: ''
  }, JSON.stringify(argv));
}

test('PROVE-CLI-LITERALS: help-looking text values are unchanged in either option order', async () => {
  for (const word of helpWords) {
    for (const option of ['--test', '--expect']) {
      const other = option === '--test' ? '--expect' : '--test';
      const test = option === '--test' ? word : 'true', expect = option === '--expect' ? word : 'defect';
      const otherValue = option === '--test' ? expect : test;
      for (const options of [[option, word, other, otherValue], [other, otherValue, option, word]]) {
        await accepted(['workflow', 'prove', '2594', ...options], test, expect);
      }
    }
  }
});

test('PROVE-CLI-CONTROLS: other nonblank option-looking literals and existing text callers retain their values', async () => {
  for (const word of ['--', '--expect', '--test', '-unknown', ' --help ', '-help\n']) {
    await accepted(['workflow', 'prove', '2594', '--test', 'true', '--expect', word], 'true', word);
    await accepted(['workflow', 'prove', '2594', '--expect', 'defect', '--test', word], word, 'defect');
  }
  for (const word of helpWords) {
    const calls = [], stdout = capture(), stderr = capture();
    const exit = await runPdd(['workflow', 'done', 'build', '--summary', word], {
      cwd: '/chosen', packageRoot: '/bundle', stdout, stderr,
      workflowRunner: { stepDone: async value => { calls.push(value); return { exitCode: 0, message: 'saved' }; } }
    });
    assert.equal(exit, 0);
    assert.deepEqual(calls, [{ step: 'build', summary: word, cwd: '/chosen', packageRoot: '/bundle' }]);
    assert.equal(stdout.text, 'saved\n');
    assert.equal(stderr.text, '');
  }
});

test('PROVE-CLI-HELP: genuine trailing help stays local and cannot conceal invalid syntax', async () => {
  await accepted(['workflow', 'prove', '2594', '--test', '--help', '--expect', '--help'], '--help', '--help');
  for (const word of helpWords) {
    for (const argv of [
      ['workflow', 'prove', word],
      ['workflow', 'prove', '2594', '--test', 'true', '--expect', 'defect', word],
      ['workflow', 'prove', '2594', '--test', 'true', '--expect', word, word],
      ['workflow', 'prove', '2594', '--test', 'true', word],
      ['workflow', 'prove', '2594', '--expect', 'defect', word]
    ]) {
      const result = await invoke(argv);
      assert.equal(result.exit, 0, JSON.stringify(argv));
      assert.deepEqual(result.calls, []);
      assert.match(result.stdout, /pdd workflow prove ISSUE --test COMMAND --expect TEXT/);
      assert.equal(result.stderr, '');
    }
    for (const argv of [
      ['workflow', 'prove', '2594', 'extra', '--test', 'true', '--expect', 'defect', word],
      ['workflow', 'prove', '2594', '--test', 'true', '--test', 'again', '--expect', 'defect', word],
      ['workflow', 'prove', '2594', '--bogus', 'value', '--test', 'true', '--expect', 'defect', word],
      ['workflow', 'prove', '0', '--test', 'true', '--expect', 'defect', word],
      ['workflow', 'prove', '2594', '--test', '', '--expect', 'defect', word],
      ['workflow', 'prove', '2594', '--test', 'true', '--expect', ' ', word],
      ['workflow', 'prove', '2594', '--test', 'true', '--expect', 'defect', word, 'extra'],
      ['unknown', word]
    ]) {
      const result = await invoke(argv);
      assert.equal(result.exit, 2, JSON.stringify(argv));
      assert.deepEqual(result.calls, []);
      assert.equal(result.stdout, '');
      assert.ok(result.stderr.endsWith('\n'));
    }
  }
});
