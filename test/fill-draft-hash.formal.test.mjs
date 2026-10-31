import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fillHashes } from '../src/runtime-preflight.mjs';

// Story: user_stories/fill-draft-hash.md, Rules to check. Exhaust the Cartesian
// product below, each beside a fresh fillable draft and a skipped fixture.
// Hash oracle uses the known prose outside our block, not production hashing.
const prefix = '# Bounded hash safety\n\nRetain this prose.\n\n';
const suffix = '\n';
const current = createHash('sha256').update(prefix + suffix).digest('hex');
const block = value => `${prefix}<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(value)}\n\`\`\`\n</details>${suffix}`;
const statuses = [undefined, 'draft', 'approved', null, '', 'pending'];
const hashes = [undefined, '', current, 'stale'];
const directories = ['test/fixtures', 'examples', 'prompts'];
const fixture = readFileSync(new URL('./fixtures/svg-layout/game.prompt.md', import.meta.url), 'utf8');
const actionable = message => {
  for (const text of ['"status": "draft"', 'pdd test --fill-hash']) assert.ok(message.includes(text), message);
};
const buckets = ['filled', 'current', 'refused', 'stale', 'warnings'];

// One test includes the genuine statusless regression before the safety controls;
// on old alpha it must fail by assertion rather than an absent-array TypeError.
test('bounded status x hash x directory classification preserves approval and skipped bytes', t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-fill-formal-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const write = (path, text) => {
    mkdirSync(dirname(join(root, path)), { recursive: true });
    writeFileSync(join(root, path), text);
  };
  const probe = 'test/fixtures/probe.prompt.md';
  write(probe, fixture);
  const first = fillHashes({ root, files: [probe] });
  assert.equal(first.refused.length, 0, 'absent status is skipped, never refused');
  assert.ok(Array.isArray(first.warnings), 'skipped fixtures have a warning array');
  assert.equal(first.warnings.length, 1);
  assert.equal(readFileSync(join(root, probe), 'utf8'), fixture);

  let checked = 0;
  for (const status of statuses) for (const hash of hashes) for (const directory of directories) {
    const label = JSON.stringify({ status: status === undefined ? '<absent>' : status, hash: hash === undefined ? '<absent>' : hash, directory });
    const value = {};
    if (status !== undefined) value.status = status;
    if (hash !== undefined) value.prose_sha256 = hash;
    const path = `${directory}/subject.prompt.md`;
    const draft = 'anchor/draft.prompt.md', skipped = 'anchor/skipped.prompt.md';
    const before = block(value), draftBefore = block({ status: 'draft', prose_sha256: '' });
    write(path, before); write(draft, draftBefore); write(skipped, fixture);
    // Independent Story oracle: absence of both keys warns; a hash without status refuses.
    // Approved never mutates;
    // invalid explicit statuses and missing draft hash refuse.
    const outcome = status === undefined ? (hash === undefined ? 'warnings' : 'refused')
      : status === 'approved' ? (hash === current ? 'current' : 'stale')
      : status !== 'draft' || hash === undefined ? 'refused'
      : hash === current ? 'current' : 'filled';
    const expected = Object.fromEntries(buckets.map(key => [key, []]));
    expected.filled.push(draft); expected.warnings.push(skipped); expected[outcome].push(path);
    const actual = fillHashes({ root, files: [path, draft, skipped] });
    for (const key of buckets) {
      assert.ok(Array.isArray(actual[key]), `${label}: ${key} array`);
      assert.deepEqual(actual[key].map(row => row.path).sort(), expected[key].sort(), `${label}: ${key}`);
    }
    for (const row of actual.warnings) {
      assert.match(row.message, /no status.*no prose_sha256.*skipped/, label); actionable(row.message);
    }
    if (status === undefined && hash !== undefined) actionable(actual.refused.find(row => row.path === path).message);
    const expectedBytes = outcome === 'filled' ? block({ ...value, prose_sha256: current }) : before;
    assert.equal(readFileSync(join(root, path), 'utf8'), expectedBytes, label);
    assert.equal(readFileSync(join(root, skipped), 'utf8'), fixture, label);
    assert.equal(readFileSync(join(root, draft), 'utf8'), block({ status: 'draft', prose_sha256: current }), label);
    checked++;
  }
  assert.equal(checked, 72, 'all 6 x 4 x 3 inputs exercised');
});
