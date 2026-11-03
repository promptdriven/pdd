import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { captureSource, findTests, proseSha256 } from '../src/runtime-preflight.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { PLACE, harbor, portsFor, root, temp } from './runtime-fake.mjs';

// Replay the frozen approved observations through the real public source boundary.
const fixture = JSON.parse(readFileSync(join(root, 'test/source-capture/markdown-code-examples.json'), 'utf8'));
const ORDER = 'tests/place-order.json', STORY = 'user_stories/place-order.md';
const write = (repo, path, bytes) => {
  mkdirSync(join(repo, path, '..'), { recursive: true });
  writeFileSync(join(repo, path), bytes);
};
const archived = (capture, path) => {
  const result = spawnSync('tar', ['-xOf', '-', path], { input: capture.tar });
  assert.equal(result.status, 0, result.stderr.toString());
  return result.stdout;
};
function captureExpected(repo, options) {
  let capture, failure;
  try { capture = captureSource(repo, options); } catch (error) {
    failure = { exitCode: error.exitCode, message: error.message };
  }
  assert.equal(failure, undefined, `source capture must succeed: ${JSON.stringify(failure)}`);
  return capture;
}
function setPrompt(repo, markdown) {
  const original = readFileSync(join(repo, PLACE), 'utf8');
  const iface = JSON.parse(original.slice(original.indexOf('<details>')).match(/```json\s*([\s\S]*?)```/)[1]);
  iface.status = 'draft'; iface.calls = [];
  const text = `# Entry\n${markdown}\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
  iface.prose_sha256 = proseSha256(text);
  write(repo, PLACE, text.replace(/"prose_sha256":"[^"]*"/, `"prose_sha256":"${iface.prose_sha256}"`));
}
function repositoryTests(row) {
  assert.equal(row.selected_tests, 'all discovered repository PDD scenarios outside test/fixtures/');
  const selected = findTests({ root }).tests.filter(test => !test.path.startsWith('test/fixtures/')).map(test => test.path);
  assert.ok(selected.length > 0, 'exercise the real repository source selection');
  return selected;
}
function offline(home) {
  const calls = { gh: 0, fetch: 0 };
  const { ports } = portsFor({ HOME: home, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, {
    gh: () => { calls.gh++; assert.fail('local capture must not sign in'); },
    fetch: () => { calls.fetch++; assert.fail('local capture must not contact a server'); },
  });
  return { ports, calls };
}

for (const row of fixture.cases) test(`SOURCE-MARKDOWN: ${row.id}`, async t => {
  const setup = harbor(t), { repo } = setup;
  setPrompt(repo, row.markdown);
  for (const [path, bytes] of Object.entries(row.files)) write(repo, path, bytes);
  if (row.symlink) symlinkSync(row.symlink.target, join(repo, row.symlink.path));
  const before = readFileSync(join(repo, PLACE));
  const { ports, calls } = offline(setup.home);
  if (row.expected_refusal) {
    assert.throws(() => captureSource(repo, { tests: [ORDER] }), error =>
      error.exitCode === 4 && error.message.includes(row.expected_refusal.path) && error.message.includes(row.expected_refusal.message));
    assert.equal(await runCheck({ cwd: repo, words: [ORDER], options: { '--files': true } }, ports), 4, ports.stderr.text);
    assert.ok(ports.stderr.text.includes(row.expected_refusal.path), ports.stderr.text);
    assert.ok(ports.stderr.text.includes(row.expected_refusal.message), ports.stderr.text);
  } else {
    const capture = captureExpected(repo, { tests: [ORDER] });
    assert.deepEqual(capture.files.map(file => file.path), [PLACE, ORDER, STORY, ...row.expected_files].sort());
    assert.deepEqual(archived(capture, PLACE), before, 'capture preserves authored code examples');
    assert.equal(await runCheck({ cwd: repo, words: [ORDER], options: { '--files': true } }, ports), 0, ports.stderr.text);
  }
  assert.deepEqual(readFileSync(join(repo, PLACE)), before, 'discovery must not edit the prompt');
  assert.deepEqual(calls, { gh: 0, fetch: 0 });
});

test('SOURCE-MARKDOWN: actual repository source captures the real guides without editing their bytes', () => {
  const row = fixture.repository_cases.find(row => row.id === 'actual-repository-capture');
  const originals = new Map(row.required_files.map(path => [path, readFileSync(join(root, path))]));
  const tests = repositoryTests(row);
  const ordinary = captureExpected(root, { tests });
  assert.ok(ordinary.files.some(file => file.path === 'docs/prompting-guide.md'), 'ordinary actual source reaches the real guide');
  // Explicit include metadata reaches both real guide files without editing the repository.
  const capture = captureExpected(root, { tests, prepareSource: () => [{ path: 'pdd-source.json', bytes: JSON.stringify({ include: row.required_files }) }] });
  const selected = new Set(capture.files.map(file => file.path));
  for (const [path, bytes] of originals) {
    assert.ok(selected.has(path), `actual source must reach ${path}`);
    assert.deepEqual(archived(capture, path), bytes, path);
    assert.deepEqual(readFileSync(join(root, path)), bytes, path);
  }
  for (const path of row.excluded_files) assert.ok(!selected.has(path), path);
});

test('SOURCE-MARKDOWN: pdd lint --local on actual repository selected source makes no network calls', async t => {
  const row = fixture.repository_cases.find(row => row.id === 'actual-repository-local-lint');
  const selected = repositoryTests(row);
  const { ports, calls } = offline(temp(t));
  assert.equal(await runCheck({ cwd: root, words: selected, options: row.options }, ports), row.expected_exit_code, ports.stderr.text);
  assert.deepEqual(calls, { gh: row.expected_auth_calls, fetch: row.expected_network_calls });
});
