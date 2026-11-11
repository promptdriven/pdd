import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { harbor, PLACE, storyTest, portsFor } from './runtime-fake.mjs';
import { runCheck } from '../src/runtime-seam.mjs';
import { interfaceBlocks, proseSha256 } from '../src/runtime/runtime-preflight.mjs';
import { readRunResults } from '../src/workflow-results.mjs';

const nativePath = 'prompts/kernel.prompt.md', nativeTest = 'tests/kernel.json';
const reason = 'cross-process filesystem locks';
const globalPath = 'prompts/unselected.prompt.md';
function mixed(repo, mode) {
  storyTest(repo, 'kernel');
  let text = '# Kernel\n\n<details><summary>Runtime interface</summary>\n\n```json\n'
    + JSON.stringify({ kind: 'native-only', reason, status: 'draft', prose_sha256: '' }) + '\n```\n</details>\n';
  text = text.replace('"prose_sha256":""', `"prose_sha256":"${proseSha256(text)}"`);
  writeFileSync(join(repo, nativePath), text);
  for (const name of mode === 'all-native' ? ['kernel', 'place-order', 'unknown-item'] : ['kernel']) {
    const path = join(repo, `tests/${name}.json`), doc = JSON.parse(readFileSync(path));
    doc.steps[0].entry_path = nativePath;
    writeFileSync(path, JSON.stringify(doc));
  }
  if (mode === 'selected' || mode === 'all-native') {
    const path = join(repo, PLACE), text = readFileSync(path, 'utf8');
    writeFileSync(path, text.replace(interfaceBlocks(text)[0][0], ''));
  }
  if (mode !== 'selected') writeFileSync(join(repo, globalPath), '# Unselected behavior\n');
}
const offline = setup => portsFor({ HOME: setup.home, XDG_CONFIG_HOME: join(setup.home, '.config'), PDD_STATE_DIR: setup.state }, {
  gh: () => assert.fail('local lint must not authenticate'),
  fetch: () => assert.fail('local lint must not contact Runtime'),
}).ports;
function evidence(result, mode) {
  assert.deepEqual(result.rows.find(row => row.test === nativeTest)?.native_only, [{ path: nativePath, reason }], 'native omission must survive global interface diagnostics');
  assert.equal(result.rows.find(row => row.test === nativeTest).state, 'not run');
  assert.deepEqual(result.coverage.runtime, { total: mode === 'selected' ? 2 : 3, checkable: mode === 'selected' || mode === 'all-native' ? 0 : 1, native_only: 1 });
  assert.ok(result.batch, 'save local lint evidence');
  assert.ok(result.problems.some(item => item.code === 'interface-missing' && item.path === (mode === 'selected' ? PLACE : globalPath)));
  if (mode === 'selected') for (const path of ['tests/place-order.json', 'tests/unknown-item.json']) {
    const row = result.rows.find(row => row.test === path);
    assert.equal(row.reason.code, 'broken-test');
    assert.ok(row.refusals.some(item => item.code === 'interface-missing' && item.path === PLACE));
  }
  assert.ok(result.rows.every(row => row.state === 'not run'));
}
for (const mode of ['selected', 'unselected', 'all-native']) for (const json of [false, true]) {
  test(`default lint retains local evidence (${mode} missing interface, ${json ? 'JSON' : 'text'})`, async t => {
    const setup = harbor(t, repo => mixed(repo, mode)), ports = offline(setup);
    assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, ...(json ? { '--json': true } : {}) } }, ports), 4);
    assert.ok(ports.stdout.text.includes(reason), 'native reason must survive global interface diagnostics');
    assert.ok(ports.stdout.text.includes(nativePath));
    if (json) evidence(JSON.parse(ports.stdout.text), mode);
    else assert.match(ports.stdout.text, /Runtime coverage:/);
    const saved = readRunResults({ root: setup.repo }, { env: { HOME: setup.home, PDD_STATE_DIR: setup.state } }).find(row => row.kind === 'pdd lint');
    assert.ok(saved, 'save local lint for PR/status evidence');
    assert.deepEqual(saved.nativeOnly.find(row => row.test === nativeTest)?.prompts, [{ path: nativePath, reason }]);
    for (const readJson of [false, true]) {
      const next = offline(setup);
      assert.equal(await runCheck({ cwd: setup.repo, options: { '--read': saved.batch, ...(readJson ? { '--json': true } : {}) } }, next), 4);
      if (readJson) evidence(JSON.parse(next.stdout.text), mode);
      else {
        assert.ok(next.stdout.text.includes(reason));
        assert.ok(next.stdout.text.includes(mode === 'selected' ? PLACE : globalPath));
        assert.match(next.stdout.text, /Runtime coverage:/);
      }
    }
  });
}

for (const json of [false, true]) test(`default lint keeps global diagnostics without Stories (${json ? 'JSON' : 'text'})`, async t => {
  const setup = harbor(t, repo => {
    rmSync(join(repo, 'user_stories'), { recursive: true });
    rmSync(join(repo, 'tests'), { recursive: true });
    writeFileSync(join(repo, globalPath), '# Unselected behavior\n');
  }), ports = offline(setup);
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, ...(json ? { '--json': true } : {}) } }, ports), 4);
  if (json) {
    const result = JSON.parse(ports.stdout.text);
    assert.deepEqual(result.rows, []);
    assert.ok(result.problems.some(item => item.code === 'interface-missing' && item.path === globalPath));
  } else assert.ok(ports.stdout.text.includes(globalPath));
});

for (const json of [false, true]) test(`CLI default lint saves native evidence (${json ? 'JSON' : 'text'})`, t => {
  const setup = harbor(t, repo => mixed(repo, 'selected'));
  const env = { ...process.env, HOME: setup.home, XDG_CONFIG_HOME: join(setup.home, '.config'), PDD_STATE_DIR: setup.state,
    PDD_RUNTIME_URL: 'http://127.0.0.1:1', PDD_SUITE_QUEUE: join(setup.sandbox, 'suite') };
  for (const key of ['GH_TOKEN', 'GITHUB_TOKEN', 'GH_CONFIG_DIR', 'CODEX_HOME', 'CLAUDE_CONFIG_DIR', 'PDD_VM_SUITE_LOCK']) delete env[key];
  const args = [new URL('../bin/pdd.mjs', import.meta.url).pathname, 'lint', ...(json ? ['--json'] : [])];
  const result = spawnSync(process.execPath, args, { cwd: setup.repo, env, encoding: 'utf8', timeout: 15_000 });
  assert.equal(result.signal, null);
  assert.equal(result.status, 4, result.stderr);
  assert.ok(result.stdout.includes(reason), 'CLI must retain native omission beside local refusal');
  if (json) evidence(JSON.parse(result.stdout), 'selected');
  const saved = readRunResults({ root: setup.repo }, { env }).find(row => row.kind === 'pdd lint');
  assert.ok(saved?.batch, 'CLI must save local lint evidence');
});
