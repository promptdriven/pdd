import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { captureSource } from '../../src/runtime-seam.mjs';
import { runCheck, runTry } from '../../src/runtime-seam.mjs';
import { PLACE, fakeRuntime, harbor, portsFor, root, temp } from './runtime-fake.mjs';

const ORDER = 'tests/place-order.json';
const headOf = repo => spawnSync('git', ['rev-parse', 'HEAD'], { cwd: repo, encoding: 'utf8' }).stdout.trim();

test('PROVENANCE1: captureSource reports clean HEAD commit, edited dirty files, untracked dependencies and unborn HEAD', t => {
  const setup = harbor(t);
  const head = headOf(setup.repo);

  // Unrelated untracked file outside the selected test's upload does not mark the uploaded source dirty.
  writeFileSync(join(setup.repo, 'scratch.tmp.txt'), 'untracked outside upload\n');

  const clean = captureSource(setup.repo, { tests: [ORDER] });
  assert.equal(clean.source_commit, head);
  assert.equal(clean.source_dirty, false);
  assert.deepEqual(clean.dirty_files, []);

  // Editing the prompt marks source_dirty: true and lists prompts/place_order.prompt.md.
  const originalPrompt = readFileSync(join(setup.repo, PLACE), 'utf8');
  writeFileSync(join(setup.repo, PLACE), `${originalPrompt}\n<!-- local edit -->\n`);
  const edited = captureSource(setup.repo, { tests: [ORDER] });
  assert.equal(edited.source_commit, head);
  assert.equal(edited.source_dirty, true);
  assert.deepEqual(edited.dirty_files, [PLACE]);

  // Adding an untracked dependency referenced by the prompt also lists that untracked file.
  mkdirSync(join(setup.repo, 'docs'), { recursive: true });
  writeFileSync(join(setup.repo, 'docs/extra.md'), '# Extra rule\n');
  writeFileSync(join(setup.repo, PLACE), originalPrompt.replace('# ', '## Dependencies\n- [Extra](../docs/extra.md)\n\n# '));
  const withUntracked = captureSource(setup.repo, { tests: [ORDER] });
  assert.equal(withUntracked.source_commit, head);
  assert.equal(withUntracked.source_dirty, true);
  assert.deepEqual(withUntracked.dirty_files, ['docs/extra.md', PLACE]);

  // Repository with unborn HEAD (git init, no commit yet) reports source_commit: null.
  const sandbox = temp(t), unbornRepo = join(sandbox, 'unborn');
  cpSync(join(root, 'test/fixtures/harbor'), unbornRepo, { recursive: true });
  assert.equal(spawnSync('git', ['init', '-q'], { cwd: unbornRepo }).status, 0);
  const unborn = captureSource(unbornRepo, { tests: [ORDER] });
  assert.equal(unborn.source_commit, null);
  assert.equal(unborn.source_dirty, null);
  assert.deepEqual(unborn.dirty_files, []);
});

test('PROVENANCE2: runCheck and runTry send source provenance only when /v1/capacity advertises source-provenance', async t => {
  const setup = harbor(t);
  const head = headOf(setup.repo);

  // 1. Server advertising source-provenance receives clean commit on /v1/lint, /v1/check, and /v1/try
  const modern = await fakeRuntime(t, entry => {
    if (entry.method === 'POST' && entry.command === 'try') return { status: 200, json: modern.tryJob(entry.request.requestId) };
    return modern.normal(entry);
  });
  modern.capacity = async () => ({
    status: 200,
    json: {
      maintenance: null,
      features: ['lint-tests', 'lint-call-preflight', 'source-provenance'],
      slots: { check: { running: 0, limit: 4, waiting: 0 }, lint: { running: 0, limit: 4, waiting: 0 } },
      tries: { open: 0, limit: 4, yours: 0, per_account: null },
    },
  });

  const envModern = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: modern.origin };
  let { ports } = portsFor(envModern);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--cache-clear': true } }, ports), 0, ports.stderr.text);

  const lintPost = modern.posts.find(p => p.command === 'lint');
  const checkPost = modern.posts.find(p => p.command === 'check');
  assert.equal(lintPost.request.source_commit, head);
  assert.equal(lintPost.request.source_dirty, false);
  assert.deepEqual(lintPost.request.dirty_files, []);
  assert.equal(checkPost.request.source_commit, head);
  assert.equal(checkPost.request.source_dirty, false);
  assert.deepEqual(checkPost.request.dirty_files, []);

  // Edit prompt and start a Try: dirty provenance sent on /v1/try
  const originalPrompt = readFileSync(join(setup.repo, PLACE), 'utf8');
  writeFileSync(join(setup.repo, PLACE), originalPrompt.replace('"approved"', '"draft"'));
  ({ ports } = portsFor(envModern));
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: {} }, ports), 0, ports.stderr.text);
  const tryPost = modern.posts.find(p => p.command === 'try');
  assert.equal(tryPost.request.source_commit, head);
  assert.equal(tryPost.request.source_dirty, true);
  assert.deepEqual(tryPost.request.dirty_files, [PLACE]);

  // 2. Legacy server without source-provenance does not receive provenance keys
  const legacy = await fakeRuntime(t, entry => legacy.normal(entry));
  const envLegacy = { HOME: setup.home, PDD_STATE_DIR: join(setup.sandbox, 'legacy-state'), PDD_RUNTIME_URL: legacy.origin };
  ({ ports } = portsFor(envLegacy));
  writeFileSync(join(setup.repo, PLACE), originalPrompt);
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--cache-clear': true } }, ports), 0, ports.stderr.text);
  for (const post of legacy.posts) {
    assert.equal('source_commit' in post.request, false);
    assert.equal('source_dirty' in post.request, false);
    assert.equal('dirty_files' in post.request, false);
  }
});
