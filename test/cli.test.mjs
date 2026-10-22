import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import { parseArgv, CommandInputError } from '../src/argument-parser.mjs';
import { PUBLIC_COMMAND_IDS, PUBLIC_COMMAND_MANIFEST, PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { renderCompletion } from '../src/completion.mjs';
import { installedHostPath, loadInstalledHost } from '../src/host-adapter.mjs';
import { renderHelp, runPdd } from '../src/pdd-cli.mjs';
import { formatLocalWorkflows, listLocalWorkflows } from '../src/workflow-list.mjs';

function capture() {
  return {
    text: '',
    write(value) { this.text += String(value); return true; },
  };
}

function temporary(t) {
  const directory = mkdtempSync(join(tmpdir(), 'pdd-public-cli-'));
  t.after(() => rmSync(directory, { recursive: true, force: true }));
  return directory;
}

test('catalog IDs and manifest forms are unique, described, and shown in help', () => {
  assert.equal(new Set(PUBLIC_COMMAND_IDS).size, PUBLIC_COMMAND_IDS.length);
  assert.equal(new Set(PUBLIC_COMMAND_MANIFEST.map((entry) => entry.form)).size, PUBLIC_COMMAND_MANIFEST.length);
  for (const entry of PUBLIC_COMMAND_MANIFEST) {
    assert.match(entry.description, /\S/);
    assert.doesNotMatch(entry.description, /\r|\n/);
    assert.ok(renderHelp().includes(entry.form));
    assert.ok(renderHelp().includes(entry.description));
  }
  assert.ok(PUBLIC_COMMAND_ROUTES.every((route) => PUBLIC_COMMAND_IDS.includes(route.id)));
  assert.doesNotMatch(renderHelp(), /Coordinator|Discord|Workbench|Herdr|account pool/i);
});

test('help, version, skill, completion, and local workflow listing work without Host', async (t) => {
  const packageRoot = temporary(t);
  mkdirSync(join(packageRoot, 'skills', 'pdd'), { recursive: true });
  writeFileSync(join(packageRoot, 'package.json'), JSON.stringify({ version: '9.8.7' }));
  writeFileSync(join(packageRoot, 'skills', 'pdd', 'SKILL.md'), '# PDD skill\n');
  const project = temporary(t);
  mkdirSync(join(project, '.pdd', 'workflows', 'feature'), { recursive: true });
  writeFileSync(join(project, '.pdd', 'workflows', 'feature', 'WORKFLOW.md'), '# Feature\n');
  const output = capture();
  const error = capture();
  const noHost = async () => { throw new Error('Host must not load for a local command'); };

  assert.equal(await runPdd(['--help'], { stdout: output, stderr: error, packageRoot, cwd: project, loadHost: noHost }), 0);
  assert.equal(await runPdd(['--version'], { stdout: output, stderr: error, packageRoot, cwd: project, loadHost: noHost }), 0);
  assert.match(output.text, /pdd 9\.8\.7/);
  assert.equal(await runPdd(['--skill'], { stdout: output, stderr: error, packageRoot, cwd: project, loadHost: noHost }), 0);
  assert.match(output.text, /# PDD skill/);
  assert.equal(await runPdd(['workflow', 'list'], { stdout: output, stderr: error, packageRoot, cwd: project, loadHost: noHost }), 0);
  assert.match(output.text, /feature  \.pdd\/workflows\/feature\/WORKFLOW\.md/);
  assert.match(output.text, /commit and push/);
  assert.equal(await runPdd(['completion', 'bash'], { stdout: output, stderr: error, packageRoot, cwd: project, loadHost: noHost }), 0);
  assert.match(output.text, /complete -F _pdd_complete pdd/);
  assert.equal(error.text, '');
});

test('local workflow listing ignores symlinked workflow folders and reports empty catalogs', (t) => {
  const project = temporary(t);
  const outside = temporary(t);
  mkdirSync(join(project, '.pdd', 'workflows', 'small-change'), { recursive: true });
  writeFileSync(join(project, '.pdd', 'workflows', 'small-change', 'WORKFLOW.md'), '# Change\n');
  writeFileSync(join(outside, 'outside.md'), '# Outside\n');
  mkdirSync(join(project, '.pdd', 'workflows', 'symlinked-file'));
  symlinkSync(join(outside, 'outside.md'), join(project, '.pdd', 'workflows', 'symlinked-file', 'WORKFLOW.md'));
  mkdirSync(join(outside, 'WORKFLOW.md'));
  symlinkSync(outside, join(project, '.pdd', 'workflows', 'outside'));

  const catalog = listLocalWorkflows({ cwd: project });
  assert.deepEqual(catalog, {
    workflows: [{ name: 'small-change', file: '.pdd/workflows/small-change/WORKFLOW.md' }],
    default: null,
  });
  assert.match(formatLocalWorkflows(catalog), /Review, commit and push/);
  assert.deepEqual(listLocalWorkflows({ cwd: outside }), { workflows: [], default: null });
  assert.deepEqual(JSON.parse(formatLocalWorkflows(catalog, { json: true })), catalog);

  const linkedProject = temporary(t);
  mkdirSync(join(linkedProject, '.pdd'));
  symlinkSync(join(outside, 'WORKFLOW.md'), join(linkedProject, '.pdd', 'workflows'));
  assert.deepEqual(listLocalWorkflows({ cwd: linkedProject }), { workflows: [], default: null });
});

test('the parser rejects unsupported/private surfaces and arbitrary runtime arguments', () => {
  for (const argv of [
    ['coordinator'], ['host', 'doctor'], ['accounts'], ['workbench'], ['discord', 'link'],
    ['phone', 'pair'], ['machine', 'accounts', 'switch'], ['runtime', 'unknown'],
    ['runtime', 'discover', '--', 'arbitrary'], ['run', 'list', '--shell'],
  ]) {
    assert.throws(() => parseArgv(argv), CommandInputError, JSON.stringify(argv));
  }
  assert.equal(parseArgv(['runtime', 'discover']).commandId, 'runtime');
  assert.deepEqual(parseArgv(['runtime', '--request', 'operation-123']).hostArgv, ['runtime', '--request', 'operation-123']);
  assert.deepEqual(parseArgv(['try', '--request', 'try-123']).hostArgv, ['try', '--request', 'try-123']);
  assert.throws(() => parseArgv(['runtime']), CommandInputError);
  assert.throws(() => parseArgv(['runtime', 'discover', '--request', 'operation-123']), CommandInputError);
  assert.throws(() => parseArgv(['replay']), CommandInputError);
  assert.deepEqual(parseArgv(['agents', 'start', '--list-models', '--host', 'work-laptop', '--json']).hostArgv,
    ['agents', 'start', '--list-models', '--host', 'work-laptop', '--json']);
  assert.deepEqual(parseArgv(['agents', 'open', 'Ada Lovelace']).hostArgv, ['agents', 'open', 'Ada Lovelace']);
  assert.throws(() => parseArgv(['agents', 'start', 'hello', '--list-models']), CommandInputError);
  assert.throws(() => parseArgv(['run', 'message', '44']), /Use: pdd run message/);
  assert.throws(() => parseArgv(['workflow', 'new', 'bad name']), CommandInputError);
});

test('validated operands are reconstructed as a fresh typed argument vector', () => {
  const input = ['repo', 'add', '../project folder', '--preparation', 'on-demand', '--json'];
  const project = parseArgv(input);
  assert.equal(project.commandId, 'repo.add');
  assert.deepEqual(project.hostArgv, ['repo', 'add', '../project folder', '--preparation', 'on-demand', '--json']);
  assert.notEqual(project.hostArgv, input);

  const message = parseArgv(['run', 'message', 'owner/repo#12', 'first line\nsecond line']);
  assert.equal(message.commandId, 'run.message');
  assert.deepEqual(message.hostArgv, ['run', 'message', 'owner/repo#12', 'first line\nsecond line']);

  const search = parseArgv(['repo', 'list', '--query', 'project search', '--page', '2']);
  assert.deepEqual(search.hostArgv, ['repo', 'list', '--query', 'project search', '--page', '2']);
  assert.deepEqual(parseArgv(['agents', 'message', 'ses-one', 'hello', '--file', './one', '--file', './two']).hostArgv,
    ['agents', 'message', 'ses-one', 'hello', '--file', './one', '--file', './two']);
  assert.throws(() => parseArgv(['repo', 'list', '--query', '--page']), CommandInputError);
});

test('invalid commands never load or dispatch to Host and raw arguments are not echoed', async () => {
  const error = capture();
  let loads = 0;
  const result = await runPdd(['not-a-command', 'secret-value'], {
    stderr: error,
    loadHost: async () => { loads += 1; return async () => 0; },
  });
  assert.equal(result, 2);
  assert.equal(loads, 0);
  assert.doesNotMatch(error.text, /secret-value/);

  const optionResult = await runPdd(['repo', 'list', '--unknown'], {
    stderr: error,
    loadHost: async () => { loads += 1; return async () => 0; },
  });
  assert.equal(optionResult, 2);
  assert.equal(loads, 0);
});

test('valid Host commands report unavailable clearly when the installed export is missing', async () => {
  const output = capture();
  const error = capture();
  const result = await runPdd(['run', 'status', '44'], {
    stdout: output,
    stderr: error,
    loadHost: async () => null,
  });
  assert.equal(result, 69);
  assert.match(error.text, /installed PDD Host/);
  assert.match(error.text, /coming soon/);
  assert.equal(output.text, '');
});

test('Host receives only the reconstructed allowlisted argv and its exit code is preserved', async () => {
  const error = capture();
  const output = capture();
  const input = capture();
  const env = { PDD_TEST: 'yes' };
  let received;
  const result = await runPdd(['run', 'status', '44', '--json'], {
    stdout: output,
    stderr: error,
    stdin: input,
    env,
    loadHost: async () => async (argv, streams) => {
      received = argv;
      assert.equal(streams.stdout, output);
      assert.equal(streams.stderr, error);
      assert.equal(streams.stdin, input);
      assert.equal(streams.env, env);
      return 3;
    },
  });
  assert.equal(result, 3);
  assert.deepEqual(received, ['run', 'status', '44', '--json']);
  assert.equal(error.text, '');

  for (const request of [['runtime', '--request', 'operation-123'], ['try', '--request', 'try-123']]) {
    let recoveryArgv;
    const recoveryStatus = await runPdd(request, {
      stderr: error,
      loadHost: async () => async (argv) => { recoveryArgv = argv; return 0; },
    });
    assert.equal(recoveryStatus, 0);
    assert.deepEqual(recoveryArgv, request);
  }

  const invalidStatus = await runPdd(['run', 'status', '44'], {
    stderr: error,
    loadHost: async () => async () => undefined,
  });
  assert.equal(invalidStatus, 1);
  assert.match(error.text, /invalid command status/);

  for (const exitCode of [0, -1, 256]) {
    const invalidThrownStatus = await runPdd(['run', 'status', '44'], {
      stderr: error,
      loadHost: async () => async () => { throw Object.assign(new Error('native failure'), { exitCode }); },
    });
    assert.equal(invalidThrownStatus, 1);
  }
});

test('completion choices come from every route and option in the catalog', () => {
  const bash = renderCompletion('bash');
  const zsh = renderCompletion('zsh');
  for (const route of PUBLIC_COMMAND_ROUTES) {
    for (const token of route.prefix) {
      assert.ok(bash.includes(token), `Bash completion omits ${token}`);
      assert.ok(zsh.includes(token), `Zsh completion omits ${token}`);
    }
    for (const option of route.options) {
      assert.ok(bash.includes(option.name), `Bash completion omits ${option.name}`);
      assert.ok(zsh.includes(option.name), `Zsh completion omits ${option.name}`);
    }
  }
  assert.throws(() => renderCompletion('fish'), TypeError);
});

test('installed Host loader exposes only the existing runCli export and never invokes it', async () => {
  assert.equal(installedHostPath('/tmp/person'), '/tmp/person/pocket/app/src/cli/pocket.mjs');
  let importedUrl;
  let invoked = false;
  const runCli = async () => { invoked = true; };
  const loaded = await loadInstalledHost({
    home: '/tmp/person',
    importer: async (url) => { importedUrl = url; return { runCli }; },
  });
  assert.equal(typeof loaded, 'function');
  assert.match(importedUrl, /\/tmp\/person\/pocket\/app\/src\/cli\/pocket\.mjs$/);
  assert.equal(invoked, false);
  assert.equal(await loadInstalledHost({ home: '/tmp/person', importer: async () => ({}) }), null);
  assert.equal(await loadInstalledHost({ home: '/tmp/person', importer: async () => { throw new Error('missing'); } }), null);
});
