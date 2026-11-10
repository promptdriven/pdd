import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { PLACE, fakeRuntime, harbor, portsFor, storyTest } from './runtime-fake.mjs';
import { cliInterfaceFindings } from '../src/interface-draft.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { readRunResults } from '../src/workflow-results.mjs';

const declaration = kind => '<details><summary>Runtime interface</summary>\n\n```json\n'
  + JSON.stringify({ kind, status: 'draft', prose_sha256: '', ...(kind === 'native-only'
    ? { reason: 'Physical Git worktree identity requires native tests.' }
    : { entries: [], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 1 } }) })
  + '\n```\n</details>\n';

for (const relative of ['new.prompt.md', 'nested/new.prompt.md']) for (const words of [[], ['place-order']]) for (const local of [false, true]) test(`lint refuses a changed or untracked undeclared CLI prompt before auth (path=${relative}, words=${words.length}, local=${local})`, async t => {
  const f = harbor(t);
  mkdirSync(join(f.repo, 'prompts/cli/nested'), { recursive: true });
  writeFileSync(join(f.repo, 'prompts/cli', relative), '# New command\n');
  const { ports } = portsFor({ HOME: f.home, PDD_STATE_DIR: f.state }, {
    gh: () => assert.fail('declaration preparation must precede auth'),
    fetch: () => assert.fail('declaration preparation must precede upload'),
  });
  assert.equal(await runCheck({ cwd: f.repo, words, options: {
    '--lint': true, '--json': true, ...(local ? { '--local': true } : {}),
  } }, ports), 4);
  const report = JSON.parse(ports.stdout.text);
  assert.ok(report.problems.some(p => p.path === 'prompts/cli/' + relative && p.code === 'interface-missing'));
  if (!local && words.length) assert.equal(report.rows.length, 1);
});

for (const local of [false, true]) test(`old checkout with undeclared CLI prompts outside Story closure passes named lint while no-argument lint checks all (local=${local})`, async t => {
  const f = harbor(t, repo => {
    mkdirSync(join(repo, 'prompts/cli/nested'), { recursive: true });
    writeFileSync(join(repo, 'prompts/cli/legacy.prompt.md'), '# Legacy CLI prompt\n');
    writeFileSync(join(repo, 'prompts/cli/nested/legacy.prompt.md'), '# Nested legacy CLI prompt\n');
  });
  const fake = local ? null : await fakeRuntime(t, (entry, server) => server.normal(entry));
  const { ports: namedPorts } = portsFor({
    HOME: f.home, PDD_STATE_DIR: f.state, ...(fake ? { PDD_RUNTIME_URL: fake.origin } : {}),
  });
  assert.equal(await runCheck({ cwd: f.repo, words: ['place-order'], options: {
    '--lint': true, '--json': true, ...(local ? { '--local': true } : {}),
  } }, namedPorts), 0, namedPorts.stdout.text + namedPorts.stderr.text);

  const { ports: unknownPorts } = portsFor({ HOME: f.home, PDD_STATE_DIR: f.state });
  assert.equal(await runCheck({ cwd: f.repo, words: ['missing-story'], options: {
    '--lint': true, ...(local ? { '--local': true } : {}),
  } }, unknownPorts), 2);
  assert.match(unknownPorts.stderr.text, /Unknown story "missing-story"/);

  const { ports: allPorts } = portsFor({ HOME: f.home, PDD_STATE_DIR: f.state }, {
    gh: () => assert.fail('no-argument declaration check must precede auth'),
    fetch: () => assert.fail('no-argument declaration check must precede upload'),
  });
  assert.equal(await runCheck({ cwd: f.repo, options: {
    '--lint': true, '--json': true, ...(local ? { '--local': true } : {}),
  } }, allPorts), 4);
  const allReport = JSON.parse(allPorts.stdout.text);
  assert.deepEqual(
    allReport.problems.filter(p => p.code === 'interface-missing').map(p => p.path).sort(),
    ['prompts/cli/legacy.prompt.md', 'prompts/cli/nested/legacy.prompt.md'],
  );

  // Modifying a committed undeclared CLI prompt in the checkout causes named lint to refuse it.
  writeFileSync(join(f.repo, 'prompts/cli/legacy.prompt.md'), '# Legacy CLI prompt (edited)\n');
  const { ports: editedPorts } = portsFor({ HOME: f.home, PDD_STATE_DIR: f.state }, {
    gh: () => assert.fail('changed declaration check must precede auth'),
    fetch: () => assert.fail('changed declaration check must precede upload'),
  });
  assert.equal(await runCheck({ cwd: f.repo, words: ['place-order'], options: {
    '--lint': true, '--json': true, ...(local ? { '--local': true } : {}),
  } }, editedPorts), 4);
  assert.ok(JSON.parse(editedPorts.stdout.text).problems.some(p => p.path === 'prompts/cli/legacy.prompt.md' && p.code === 'interface-missing'));
});

for (const local of [false, true]) test(`named lint refuses an undeclared CLI prompt inside the selected Story closure (local=${local})`, async t => {
  const f = harbor(t, repo => {
    mkdirSync(join(repo, 'prompts/cli'), { recursive: true });
    writeFileSync(join(repo, 'prompts/cli/called.prompt.md'), '# Called CLI prompt without interface\n');
    const placePath = join(repo, PLACE);
    let text = '# Place an order\n\n<details><summary>Runtime interface</summary>\n\n```json\n' + JSON.stringify({
      status: 'approved',
      prose_sha256: '',
      entries: [{
        operation: 'placeOrder',
        input_schema: { type: 'object', properties: { sku: { type: 'string' }, qty: { type: 'integer', minimum: 1 } }, required: ['sku', 'qty'], additionalProperties: false },
        result_schema: { type: 'object', properties: { totalCents: { type: 'integer' } }, required: ['totalCents'], additionalProperties: false },
      }],
      calls: [{ operation: 'cliCall', target: 'prompts/cli/called.prompt.md', target_operation: 'run', max_calls: 1 }],
      resources: [],
      limits: { max_steps: 4, max_model_calls: 2 },
    }) + '\n```\n</details>\n';
    text = text.replace('"prose_sha256":""', `"prose_sha256":"${proseSha256(text)}"`);
    writeFileSync(placePath, text);
  });
  const { ports } = portsFor({ HOME: f.home, PDD_STATE_DIR: f.state }, {
    gh: () => assert.fail('closure declaration check must precede auth'),
    fetch: () => assert.fail('closure declaration check must precede upload'),
  });
  assert.equal(await runCheck({ cwd: f.repo, words: ['place-order'], options: {
    '--lint': true, '--json': true, ...(local ? { '--local': true } : {}),
  } }, ports), 4);
  const report = JSON.parse(ports.stdout.text);
  assert.ok(report.problems.some(p => p.path === 'prompts/cli/called.prompt.md' && p.code === 'interface-missing'));
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

test('the package declares every CLI prompt, including newly added files', () => {
  assert.deepEqual(cliInterfaceFindings({ root: new URL('..', import.meta.url).pathname }), []);
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

test('named lint with a changed undeclared CLI prompt retains native-only row and batch evidence', async t => {
  const reason = 'cross-process filesystem locks';
  const f = harbor(t, repo => {
    storyTest(repo, 'kernel');
    let text = '# Kernel\n\n<details><summary>Runtime interface</summary>\n\n```json\n'
      + JSON.stringify({ kind: 'native-only', reason, status: 'draft', prose_sha256: '' }) + '\n```\n</details>\n';
    text = text.replace('"prose_sha256":""', `"prose_sha256":"${proseSha256(text)}"`);
    writeFileSync(join(repo, 'prompts/kernel.prompt.md'), text);
    const testPath = join(repo, 'tests/kernel.json'), doc = JSON.parse(readFileSync(testPath, 'utf8'));
    doc.steps[0].entry_path = 'prompts/kernel.prompt.md';
    writeFileSync(testPath, JSON.stringify(doc));
  });
  mkdirSync(join(f.repo, 'prompts/cli'), { recursive: true });
  writeFileSync(join(f.repo, 'prompts/cli/new.prompt.md'), '# New CLI prompt\n');
  const env = { HOME: f.home, XDG_CONFIG_HOME: join(f.home, '.config'), PDD_STATE_DIR: f.state };
  const { ports } = portsFor(env, {
    gh: () => assert.fail('declaration refusal must precede auth'),
    fetch: () => assert.fail('declaration refusal must precede upload'),
  });
  assert.equal(await runCheck({ cwd: f.repo, words: ['kernel'], options: { '--lint': true, '--json': true } }, ports), 4);
  const report = JSON.parse(ports.stdout.text);
  assert.ok(report.batch);
  assert.ok(report.problems.some(p => p.path === 'prompts/cli/new.prompt.md' && p.code === 'interface-missing'));
  assert.deepEqual(report.rows.find(r => r.test === 'tests/kernel.json')?.native_only, [{ path: 'prompts/kernel.prompt.md', reason }]);
  const saved = readRunResults({ root: f.repo }, { env }).find(row => row.kind === 'pdd lint');
  assert.ok(saved);
});
