import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { lintSvgLayouts } from '../src/svg-layout.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { portsFor, temp } from './helpers/runtime-fake.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/svg-layout-view-controls.json', import.meta.url), 'utf8'));
const nativeBlock = '\n<details><summary>Runtime interface</summary>\n\n```json\n' + JSON.stringify({
  kind: 'native-only', status: 'draft', prose_sha256: '', reason: 'Local filesystem layout fixture.'
}) + '\n```\n</details>\n';

for (const step of scenario.steps) {
  test(`3394 view controls: ${step.step_id}`, async t => {
    const sandbox = temp(t);
    for (const [path, content] of Object.entries(scenario.initial_world.files)) {
      const full = join(sandbox, path);
      mkdirSync(dirname(full), { recursive: true });
      writeFileSync(full, content);
    }
    const root = join(sandbox, step.input.root);
    const warnings = lintSvgLayouts({ ...step.input, root });
    for (const check of step.checks) {
      assert.equal(check.target, 'result');
      assert.equal(check.path, '');
      assert.equal(check.op, 'equals');
      assert.deepEqual(warnings, check.value, `${step.step_id}: public lintSvgLayouts warnings`);
    }

    // Exercise the same files through the public CLI; deny every remote/auth path.
    writeFileSync(join(root, 'screen.prompt.md'), readFileSync(join(root, 'screen.prompt.md'), 'utf8') + nativeBlock);
    const git = (...args) => {
      const result = spawnSync('git', args, { cwd: root, encoding: 'utf8' });
      assert.equal(result.status, 0, result.stderr);
    };
    git('init', '-q'); git('add', '-A');
    const forbidden = () => assert.fail('Local lint must not call authentication, network or models');
    const env = { HOME: join(sandbox, 'home'), PDD_STATE_DIR: join(sandbox, 'state'), PDD_RUNTIME_URL: 'invalid' };
    const ports = () => portsFor(env, { gh: forbidden, fetch: forbidden, modelMetadata: forbidden }).ports;
    const fill = ports();
    assert.equal(await runPdd(['test', '--fill-hash'], { cwd: root, ...fill }), 0, fill.stderr.text);
    git('add', '-A');
    const cli = ports();
    assert.equal(await runPdd(['lint', '--local', '--json'], { cwd: root, ...cli }), 0, cli.stderr.text);
    const report = JSON.parse(cli.stdout.text);
    assert.deepEqual(report.problems, []);
    assert.deepEqual(report.warnings, warnings, `${step.step_id}: public local-lint CLI warnings`);
  });
}


test('labeled view blocks retain child list controls in API and CLI', async t => {
  const sandbox = temp(t);
  const root = join(sandbox, 'repo');
  mkdirSync(join(root, 'views'), { recursive: true });
  const paths = ['views/now__stacked.ui.svg', 'views/agents__stacked.ui.svg'];
  writeFileSync(join(root, 'screen.prompt.md'), `# Screen
Button "Help".
## Appearance
**Now:**
![Now](${paths[0]})
- Button "Approve".
**Agents:**
![Agents](${paths[1]})
- Button "Connect".
${nativeBlock}`);
  writeFileSync(join(root, paths[0]), '<svg><text>Help</text><text>Approve</text></svg>');
  writeFileSync(join(root, paths[1]), '<svg><text>Help</text><text>Connect</text></svg>');
  const warnings = lintSvgLayouts({ root, files: ['screen.prompt.md', ...paths] });
  assert.deepEqual(warnings, []);
  for (const args of [['init', '-q'], ['add', '-A']]) {
    const result = spawnSync('git', args, { cwd: root, encoding: 'utf8' });
    assert.equal(result.status, 0, result.stderr);
  }
  const forbidden = () => assert.fail('Local lint must not call authentication, network or models');
  const env = { HOME: join(sandbox, 'home'), PDD_STATE_DIR: join(sandbox, 'state'), PDD_RUNTIME_URL: 'invalid' };
  const ports = () => portsFor(env, { gh: forbidden, fetch: forbidden, modelMetadata: forbidden }).ports;
  const fill = ports();
  assert.equal(await runPdd(['test', '--fill-hash'], { cwd: root, ...fill }), 0, fill.stderr.text);
  const add = spawnSync('git', ['add', '-A'], { cwd: root, encoding: 'utf8' });
  assert.equal(add.status, 0, add.stderr);
  const cli = ports();
  assert.equal(await runPdd(['lint', '--local', '--json'], { cwd: root, ...cli }), 0, cli.stderr.text);
  const report = JSON.parse(cli.stdout.text);
  assert.deepEqual(report.problems, []);
  assert.deepEqual(report.warnings, []);
});
