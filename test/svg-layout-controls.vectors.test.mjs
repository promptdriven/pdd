import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { dirname, join } from 'node:path';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { lintSvgLayouts } from '../src/svg-layout.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { portsFor, temp } from './helpers/runtime-fake.mjs';

const manifestPath = new URL('./runtime/svg-layout-controls-cases.json', import.meta.url);
const manifestBytes = readFileSync(manifestPath);
const parseExactJson = text => JSON.parse(text, (_key, value, context) =>
  typeof value === 'number' && /^-?(?:0|[1-9][0-9]*)$/.test(context?.source ?? '') && !Number.isSafeInteger(value) ? BigInt(context.source) : value);
const inventory = parseExactJson(manifestBytes.toString('utf8'));

function git(cwd, ...args) {
  const result = spawnSync('git', args, { cwd, encoding: 'utf8' });
  assert.equal(result.status, 0, result.stderr);
}

function guardedPorts(env) {
  const calls = { authentication: 0, network: 0, model: 0 };
  const deny = kind => () => { calls[kind]++; assert.fail(`Unexpected ${kind} call during local SVG layout lint`); };
  const { ports } = portsFor(env, { gh: deny('authentication'), fetch: deny('network'), modelMetadata: deny('model') });
  return { ports, calls };
}

const nativeOnlyBlock = `\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify({
  kind: 'native-only',
  status: 'draft',
  prose_sha256: '',
  reason: 'Screen layout lint vector fixture uses local static SVG advice without interpreter operations.'
})}\n\`\`\`\n</details>\n`;

test('svg-layout-controls manifest stays aligned with Story criteria', () => {
  assert.equal(inventory.kind, 'native-draft-cases');
  assert.equal(inventory.story_path, 'user_stories/svg-layout-controls.md');
  assert.equal(inventory.cases.length, 6);
  assert.deepEqual(readFileSync(manifestPath), manifestBytes);
});

for (const vector of inventory.cases) {
  test(`2733 vector: ${vector.id} (${vector.criterion_ids.join(', ')})`, async t => {
    const sandbox = temp(t), repo = join(sandbox, 'repo'), home = join(sandbox, 'home'), state = join(sandbox, 'state');
    mkdirSync(repo, { recursive: true });
    mkdirSync(home, { recursive: true });
    const promptFile = join(repo, vector.prompt_path), drawingFile = join(repo, vector.drawing_path);
    mkdirSync(dirname(promptFile), { recursive: true });
    mkdirSync(dirname(drawingFile), { recursive: true });
    writeFileSync(promptFile, vector.prompt_markdown);
    writeFileSync(drawingFile, vector.drawing_svg);

    const files = [vector.prompt_path, vector.drawing_path];
    const directWarnings = lintSvgLayouts({ root: repo, files });
    assert.deepEqual(directWarnings, vector.expected.warnings, `${vector.id}: direct lintSvgLayouts warnings`);

    writeFileSync(promptFile, `${vector.prompt_markdown}${nativeOnlyBlock}`);
    git(repo, 'init', '-q');
    git(repo, 'add', '-A');
    const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' };
    const fill = guardedPorts(env);
    assert.equal(await runPdd(['test', '--fill-hash'], { cwd: repo, ...fill.ports }), 0, fill.ports.stderr.text);
    git(repo, 'add', '-A');

    const cliRun = guardedPorts(env);
    const exitCode = await runPdd(['lint', '--local', '--json'], { cwd: repo, ...cliRun.ports });
    const json = parseExactJson(cliRun.ports.stdout.text);

    assert.equal(exitCode, inventory.local_invariants.cli_exit_code, cliRun.ports.stderr.text);
    assert.equal(json.exit_code, inventory.local_invariants.cli_exit_code);
    assert.deepEqual(json.problems, []);
    assert.deepEqual(json.warnings, vector.expected.warnings, `${vector.id}: CLI pdd lint --local --json warnings`);

    for (const forbidden of vector.expected.forbidden_control_values ?? []) {
      const token = `control "${forbidden}": prompt control absent from drawing.`;
      assert.ok(!directWarnings.some(warning => warning.includes(token)), `${vector.id}: forbidden direct control warning ${forbidden}`);
      assert.ok(!json.warnings.some(warning => warning.includes(token)), `${vector.id}: forbidden CLI control warning ${forbidden}`);
    }

    if (vector.expected.apply_local_invariants) {
      assert.equal(fill.calls.authentication + cliRun.calls.authentication, inventory.local_invariants.authentication_calls);
      assert.equal(fill.calls.network + cliRun.calls.network, inventory.local_invariants.network_calls);
      assert.equal(fill.calls.model + cliRun.calls.model, inventory.local_invariants.model_calls);
    }

    assert.deepEqual(readFileSync(manifestPath), manifestBytes, 'approved draft cases file must remain unchanged');
  });
}
