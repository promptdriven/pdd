import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, portsFor } from './runtime-fake.mjs';
import { cliInterfaceFindings, interfaceFindings, missingInterfaces, runInterfaceDraft } from '../src/interface-draft.mjs';

const declaration = kind => '<details><summary>Runtime interface</summary>\n\n```json\n'
  + JSON.stringify({ kind, status: 'draft', prose_sha256: '', ...(kind === 'native-only'
    ? { reason: 'Physical Git worktree identity requires native tests.' }
    : { entries: [], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 1 } }) })
  + '\n```\n</details>\n';

for (const relative of ['new.prompt.md', 'nested/new.prompt.md']) for (const words of [[], ['place-order']]) for (const local of [false, true]) test(`lint refuses an undeclared CLI prompt before auth (path=${relative}, words=${words.length}, local=${local})`, async t => {
  const f = harbor(t, repo => {
    mkdirSync(join(repo, 'prompts/cli/nested'), { recursive: true });
    writeFileSync(join(repo, 'prompts/cli', relative), '# New command\n');
  });
  const { ports } = portsFor({ HOME: f.home, PDD_STATE_DIR: f.state }, {
    gh: () => assert.fail('declaration preparation must precede auth'),
    fetch: () => assert.fail('declaration preparation must precede upload'),
  });
  assert.equal(await runCheck({ cwd: f.repo, words, options: {
    '--lint': true, '--json': true, ...(local ? { '--local': true } : {}),
  } }, ports), 4);
  const report = JSON.parse(ports.stdout.text);
  assert.ok(report.problems.some(p => p.path === 'prompts/cli/' + relative && p.code === 'interface-missing'));
});

for (const kind of ['full', 'partial', 'native-only']) test(`CLI declaration gate accepts ${kind} without widening named hash checks`, async t => {
  const f = harbor(t, repo => {
    mkdirSync(join(repo, 'prompts/cli'), { recursive: true });
    writeFileSync(join(repo, 'prompts/cli/new.prompt.md'), '# Unselected\n\n' + declaration(kind));
  });
  assert.deepEqual(cliInterfaceFindings({ root: f.repo }), []);
  const { ports } = portsFor({ HOME: f.home, PDD_STATE_DIR: f.state });
  assert.equal(await runCheck({ cwd: f.repo, words: ['place-order'], options: {
    '--lint': true, '--local': true, '--json': true,
  } }, ports), 0, ports.stdout.text + ports.stderr.text);
});

test('CLI declaration gate rejects malformed and unsupported declarations', t => {
  const f = harbor(t, repo => {
    mkdirSync(join(repo, 'prompts/cli'), { recursive: true });
    writeFileSync(join(repo, 'prompts/cli/bad.prompt.md'), declaration('unknown'));
    writeFileSync(join(repo, 'prompts/cli/json.prompt.md'), '<details><summary>Runtime interface</summary>\n\n```json\n{\n```\n</details>');
  });
  assert.deepEqual(cliInterfaceFindings({ root: f.repo }).map(p => p.code).sort(), ['interface-kind-invalid', 'invalid-json']);
});

test('the package declares every callable CLI prompt, including newly added files', () => {
  assert.deepEqual(cliInterfaceFindings({ root: new URL('..', import.meta.url).pathname }), []);
});

test('only the non-callable policy context is omitted from missing-interface inventories and --all', async t => {
  const f = harbor(t, repo => {
    mkdirSync(join(repo, 'prompts/cli'), { recursive: true });
    writeFileSync(join(repo, 'prompts/cli/public-boundary.prompt.md'), '# Shared public policy context\nNo callable operation exists.\n');
    writeFileSync(join(repo, 'prompts/cli/module.prompt.md'), '# Callable module\n');
  });
  assert.deepEqual(missingInterfaces(f.repo), ['prompts/cli/module.prompt.md']);
  assert.deepEqual(cliInterfaceFindings({ root: f.repo }).map(({ path, code }) => ({ path, code })), [
    { path: 'prompts/cli/module.prompt.md', code: 'interface-missing' },
  ]);
  assert.equal(interfaceFindings({ root: f.repo, paths: ['prompts/cli/public-boundary.prompt.md'] })[0]?.code, 'interface-missing');

  const policy = harbor(t, repo => {
    mkdirSync(join(repo, 'prompts/cli'), { recursive: true });
    writeFileSync(join(repo, 'prompts/cli/public-boundary.prompt.md'), '# Shared public policy context\nNo callable operation exists.\n');
  });
  let stdout = '', stderr = '';
  assert.equal(await runInterfaceDraft({ all: true, json: true, cwd: policy.repo }, {
    stdout: { write: text => { stdout += text; } },
    stderr: { write: text => { stderr += text; } },
  }), 0, stderr);
  assert.equal(JSON.parse(stdout).rows.some(row => row.path === 'prompts/cli/public-boundary.prompt.md'), false);
  assert.equal(interfaceFindings({ root: policy.repo, paths: ['prompts/cli/public-boundary.prompt.md'] })[0]?.code, 'interface-missing');
});

for (const local of [false, true]) test(`default lint refuses malformed CLI JSON before auth (local=${local})`, async t => {
  const f = harbor(t, repo => {
    mkdirSync(join(repo, 'prompts/cli'), { recursive: true });
    writeFileSync(join(repo, 'prompts/cli/bad.prompt.md'), '<details><summary>Runtime interface</summary>\n\n```json\n{\n```\n</details>');
  });
  const { ports } = portsFor({ HOME: f.home, PDD_STATE_DIR: f.state }, {
    gh: () => assert.fail('malformed declarations must precede auth'),
    fetch: () => assert.fail('malformed declarations must precede upload'),
  });
  assert.equal(await runCheck({ cwd: f.repo, options: {
    '--lint': true, '--json': true, ...(local ? { '--local': true } : {}),
  } }, ports), 4);
  assert.ok(JSON.parse(ports.stdout.text).problems.some(p => p.code === 'invalid-json'));
});
