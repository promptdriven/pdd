import test from 'node:test';
import assert from 'node:assert/strict';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';

const capture = () => ({ text: '', write(value) { this.text += value; } });
const uuid = 'a1234567-1234-4123-8123-123456789abc';
const cases = [
  [['phone', '--name', 'Test machine'], 'runPhoneCommand', ['--name', 'Test machine']],
  [['link', 'status', '--json'], 'runLinkCommand', ['status', '--json']],
  [['fleet', 'status'], 'runFleetCommand', ['status']],
  [['agents', '--search', 'two words'], 'runAgentCommand', ['agents', '--search', 'two words']],
  [['agent', 'send', 'test-agent', 'hello', '--id', uuid], 'runAgentCommand', ['agent', 'send', 'test-agent', 'hello', '--id', uuid]],
  [['open', 'test-agent'], 'runAgentCommand', ['open', 'test-agent']],
  [['accounts', 'mode', 'codex', 'auto'], 'runAccountsCommand', ['mode', 'codex', 'auto']],
  [['setup', '--no-phone'], 'runSetupCommand', ['--no-phone']],
  [['join'], 'runJoinCommand', []],
];

test('optional families explain absence and forward validated argv exactly once to their registered binding', async () => {
  for (const [argv, binding, expected] of cases) {
    const stdout = capture(), stderr = capture(), original = [...argv];
    assert.equal(await runPdd(argv, { stdout, stderr }), 1);
    assert.equal(stdout.text, '');
    assert.equal(stderr.text, 'This command needs the optional client.\n');
    stderr.text = '';
    let calls = 0;
    const token = {};
    const adapter = { async [binding](args, ports) {
      calls++;
      assert.equal(this, adapter);
      assert.deepEqual(args, expected);
      assert.equal(ports.stdout, stdout); assert.equal(ports.stderr, stderr);
      assert.equal(ports.cwd, '/chosen project'); assert.equal(ports.packageRoot, '/bundle');
      assert.equal(ports.token, token);
      ports.stdout.write('adapter reached\n');
      return 17;
    } };
    assert.equal(await runPdd(argv, { stdout, stderr, clientAdapter: adapter,
      cwd: '/chosen project', packageRoot: '/bundle', ports: { token } }), 17);
    assert.equal(calls, 1); assert.equal(stdout.text, 'adapter reached\n'); assert.equal(stderr.text, '');
    assert.deepEqual(argv, original);
  }
});

test('optional help and invalid syntax never inspect or invoke an adapter', async () => {
  const clientAdapter = new Proxy({}, { get() { assert.fail('Adapter lookup before dispatch'); } });
  for (const argv of [[], ['link', '--help'], ['link', 'status', '--help'], ['help', 'fleet'], ['accounts', '--help'], ['completion', 'bash']]) {
    const stdout = capture(), stderr = capture();
    assert.equal(await runPdd(argv, { stdout, stderr, clientAdapter }), 0);
    assert.equal(stderr.text, '');
  }
  for (const argv of [
    ['link', 'unknown'], ['link', 'status', '--bad'], ['link', 'status', 'extra'],
    ['phone', '--name'], ['phone', '--name', ''], ['phone', '--name', '--no-integrations'],
    ['phone', '--name', 'one', '--name', 'two'], ['fleet', 'status', '--help', 'extra'],
    ['agent', 'send', 'a', 'text'], ['agent', 'send', 'a', 'text', '--id', 'bad'],
    ['agent', 'stop', 'a', '--id', uuid], ['agent', 'stop', 'a', '--id', uuid, '--how', 'all'],
    ['accounts', 'quota-decide', uuid, '--decision', 'continue', '--rev', '0'],
    ['accounts', 'quota-decide', uuid, '--decision', 'continue'],
    ['accounts', 'add', 'claude', 'a', '--from-pool'], ['accounts', 'add', 'codex', 'a', '--replace'],
    ['accounts', 'allow', 'a', 'on'], ['accounts', 'policy', 'codex', '--pinned', 'a'],
    ['setup', '--native'], ['join', 'extra'], ['runtime', '--help'],
  ]) {
    const stdout = capture(), stderr = capture();
    assert.equal(await runPdd(argv, { stdout, stderr, clientAdapter }), 2, JSON.stringify(argv));
    assert.equal(stdout.text, ''); assert.ok(stderr.text);
  }
});

test('adapter failures are finite, redact thrown details, and never retry', async () => {
  for (const result of [undefined, -1, 256, 1.5, NaN, '0', { exitCode: 0 }, new Error('sensitive detail')]) {
    let calls = 0;
    const stdout = capture(), stderr = capture();
    const clientAdapter = { runLinkCommand() { calls++; if (result instanceof Error) throw result; return result; } };
    assert.equal(await runPdd(['link', 'status'], { stdout, stderr, clientAdapter }), 1);
    assert.equal(calls, 1); assert.equal(stdout.text, '');
    assert.equal(stderr.text, 'Optional client command unconfirmed. Inspect local state before retrying.\n');
  }
  for (const clientAdapter of [null, {}, { runLinkCommand: true }]) {
    const stderr = capture();
    assert.equal(await runPdd(['link', 'status'], { stdout: capture(), stderr, clientAdapter }), 1);
    assert.equal(stderr.text, 'This command needs the optional client.\n');
  }
});

test('legacy phoneCli registration works; explicit clientAdapter takes precedence', async () => {
  const deps = { stdout: capture(), stderr: capture(), phoneCli: { runLinkCommand: () => 9 } };
  assert.equal(await runPdd(['link', 'status'], deps), 9);
  assert.equal(await runPdd(['link', 'status'], { ...deps, clientAdapter: { runLinkCommand: () => 23 } }), 23);
  assert.equal(parseArgv(['link', 'status']).commandId, 'link.status');
});

test('shell option choices belong to their command, even when optional and local flags share a name', async () => {
  const { renderCompletion } = await import('../src/completion.mjs');
  const { spawnSync } = await import('node:child_process');
  for (const shell of ['bash', 'zsh']) {
    for (const [words, expected] of [
      [['pdd', 'workflow', 'resume', uuid, '--decision', ''], ['approve', 'skip']],
      [['pdd', 'accounts', 'quota-decide', uuid, '--decision', ''], ['continue', 'wait']],
      [['pdd', 'agent', 'stop', 'a', '--id', uuid, '--how', ''], ['close', 'exit', 'interrupt']],
    ]) {
      const array = words.map(word => `'${word}'`).join(' ');
      const setup = shell === 'bash' ? '' : 'autoload -Uz compinit; compinit -D -i;\n';
      const invoke = shell === 'bash'
        ? `COMP_WORDS=(${array}); COMP_CWORD=${words.length - 1}; _pdd_complete; printf '%s\\n' "\${COMPREPLY[@]}"`
        : `_describe() { print -rl -- "\${choices[@]}"; }; words=(${array}); CURRENT=${words.length}; _pdd`;
      const result = spawnSync(shell, ['-f', '-c', setup + renderCompletion(shell) + '\n' + invoke], { encoding: 'utf8' });
      assert.equal(result.status, 0, result.stderr);
      assert.deepEqual(result.stdout.trim().split('\n').sort(), expected, `${shell}: ${words.join(' ')}`);
    }
  }
});
