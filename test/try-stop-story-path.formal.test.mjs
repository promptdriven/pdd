import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { harbor, portsFor } from './runtime-fake.mjs';

const SAVED_FIELDS = {
  seed_scenario: { schema_version: 'prompt-runtime.program-scenario.v1', steps: [] },
  story_sha256: 'a'.repeat(64),
  prompt_hashes: { 'prompts/place_order.prompt.md': 'b'.repeat(64) },
  effective_prompt_hashes: { 'prompts/place_order.prompt.md': 'c'.repeat(64) },
  contract_references: [],
};

const RECORD_TESTER = {
  id: 'try-tester-1',
  request_ids: ['try-tester-1'],
  reservation: null,
  story: 'tester-panel',
  storyPath: 'user_stories/fakes/tester-panel.md',
  title: 'I can control test events while I try Pocket',
  origin: 'https://runtime.promptdriven.ai',
  login: 'octo',
  ...SAVED_FIELDS,
};

const RECORD_PLACE = {
  id: 'try-place-1',
  request_ids: ['try-place-1'],
  reservation: null,
  story: 'place-order',
  storyPath: 'user_stories/place-order.md',
  title: 'Place a coffee order',
  origin: 'https://runtime.promptdriven.ai',
  login: 'octo',
  ...SAVED_FIELDS,
};

const RECORD_LEGACY_PLACE = (() => {
  const copy = structuredClone(RECORD_PLACE);
  delete copy.storyPath;
  return copy;
})();

const RECORD_LEGACY_TESTER = (() => {
  const copy = structuredClone(RECORD_TESTER);
  delete copy.storyPath;
  return copy;
})();

// Story-derived oracle from user_stories/try-stop-story-path.md ## Rules to check (rules 1..5).
function oracleMatch(testPath, record, canonicalPath, strippedWord) {
  const fileBase = testPath.split('/').at(-1).replace(/\.json$/, '');
  if (strippedWord === record.story || strippedWord === testPath || strippedWord === fileBase) return true;
  if (canonicalPath === testPath) return true;
  if (record.storyPath) return canonicalPath === record.storyPath;
  return canonicalPath === `user_stories/${record.story}.md` || canonicalPath === `user_stories/fakes/${record.story}.md`;
}

function oracleStop(initialTries, selector) {
  const entries = Object.entries(initialTries);
  const names = entries.map(([p, r]) => r.story ?? p.split('/').at(-1).replace(/\.json$/, '')).join(', ') || 'none';
  const hits = selector.word === undefined
    ? entries
    : entries.filter(([p, r]) => oracleMatch(p, r, selector.canonical, selector.word.replace(/^\.\//, '')));
  if (hits.length !== 1) {
    const stripped = selector.word?.replace(/^\.\//, '');
    const err = stripped !== undefined
      ? `No open Try for "${stripped}". Open Try links: ${names}.\n`
      : entries.length
        ? `Name the Try to stop. Open Try links: ${names}.\n`
        : 'No open Try in this repository.\n';
    return {
      exit_code: 2,
      stdout: '',
      stderr: err,
      stoppedId: null,
      savedTries: structuredClone(initialTries),
    };
  }
  const [matchedPath, matchedRecord] = hits[0];
  const nextTries = structuredClone(initialTries);
  delete nextTries[matchedPath];
  return {
    exit_code: 0,
    stdout: `The Try link for "${matchedRecord.title}" is stopped.\n`,
    stderr: `Stopping the Try for "${matchedRecord.title}"…\n`,
    stoppedId: matchedRecord.id,
    savedTries: nextTries,
  };
}

test('try-stop-story-path formal check: bounded exhaustive check of Rules 1..5 against Story oracle + control', async t => {
  const setup = harbor(t, repo => {
    mkdirSync(join(repo, 'user_stories/fakes'), { recursive: true });
  });
  const realRoot = realpathSync(setup.repo);
  const repoKey = createHash('sha256').update(realRoot).digest('hex').slice(0, 16);
  const reposDir = join(setup.state, 'repos');
  mkdirSync(reposDir, { recursive: true, mode: 0o700 });
  const repoStatePath = join(reposDir, `${repoKey}.json`);

  const states = [
    { name: 'empty', tries: {} },
    { name: 'single-subfolder', tries: { 'tests/tester-panel.json': RECORD_TESTER } },
    { name: 'single-legacy-root', tries: { 'tests/place-order.json': RECORD_LEGACY_PLACE } },
    { name: 'single-legacy-subfolder', tries: { 'tests/tester-panel.json': RECORD_LEGACY_TESTER } },
    {
      name: 'two-open-tries',
      tries: {
        'tests/place-order.json': RECORD_PLACE,
        'tests/tester-panel.json': RECORD_TESTER,
      },
    },
  ];

  const selectors = [
    { word: undefined, canonical: '', subCwd: '' },
    { word: 'tester-panel', canonical: 'tester-panel', subCwd: '' },
    { word: 'place-order', canonical: 'place-order', subCwd: '' },
    { word: 'user_stories/fakes/tester-panel.md', canonical: 'user_stories/fakes/tester-panel.md', subCwd: '' },
    { word: './user_stories/fakes/tester-panel.md', canonical: 'user_stories/fakes/tester-panel.md', subCwd: '' },
    { word: 'user_stories/fakes/../fakes/tester-panel.md', canonical: 'user_stories/fakes/tester-panel.md', subCwd: '' },
    { word: 'fakes/tester-panel.md', canonical: 'user_stories/fakes/tester-panel.md', subCwd: 'user_stories' },
    { word: 'user_stories/place-order.md', canonical: 'user_stories/place-order.md', subCwd: '' },
    { word: './user_stories/place-order.md', canonical: 'user_stories/place-order.md', subCwd: '' },
    { word: 'tests/tester-panel.json', canonical: 'tests/tester-panel.json', subCwd: '' },
    { word: './tests/tester-panel.json', canonical: 'tests/tester-panel.json', subCwd: '' },
    { word: 'tests/place-order.json', canonical: 'tests/place-order.json', subCwd: '' },
    { word: 'user_stories/fakes/other.md', canonical: 'user_stories/fakes/other.md', subCwd: '' },
    { word: './user_stories/fakes/other.md', canonical: 'user_stories/fakes/other.md', subCwd: '' },
  ];

  let checked = 0;
  for (const state of states) {
    for (const selector of selectors) {
      checked += 1;
      const initialTries = structuredClone(state.tries);
      writeFileSync(repoStatePath, `${JSON.stringify({ root: realRoot, last_batch: null, tries: initialTries }, null, 2)}\n`, { mode: 0o600 });
      const deleted = [];
      const { ports } = portsFor(
        { HOME: setup.home, PDD_STATE_DIR: setup.state },
        {
          fetch: async (url, init = {}) => {
            const parsed = new URL(String(url));
            if (init.method === 'DELETE' && parsed.pathname.startsWith('/v1/try/')) {
              const tryId = parsed.pathname.split('/').at(-1);
              const requestId = init.headers?.['X-Request-Id'] ?? init.headers?.['x-request-id'];
              assert.match(String(requestId), /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i);
              deleted.push(tryId);
              const body = JSON.stringify({
                requestId,
                id: requestId,
                command: 'stop',
                state: 'passed',
                engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15',
                result: { exitCode: 0, refusals: [], output: 'Try stopped.', session: { id: tryId, state: 'stopped' } },
              });
              return { status: 200, headers: new Headers({ 'content-type': 'application/json' }), text: async () => body };
            }
            assert.fail(`Unexpected fetch: ${init.method} ${url}`);
          },
        },
      );
      const cwd = selector.subCwd ? join(setup.repo, selector.subCwd) : setup.repo;
      const words = selector.word === undefined ? [] : [selector.word];
      const exit_code = await runTry({ words, options: { '--stop': true }, cwd }, ports);
      const saved = JSON.parse(readFileSync(repoStatePath, 'utf8'));
      const expected = oracleStop(initialTries, selector);
      const label = `${state.name} / word=${String(selector.word)} / subCwd=${selector.subCwd}`;
      assert.equal(exit_code, expected.exit_code, `${label} exit_code`);
      assert.equal(ports.stdout.text, expected.stdout, `${label} stdout`);
      assert.equal(ports.stderr.text, expected.stderr, `${label} stderr`);
      assert.deepEqual(deleted, expected.stoppedId ? [expected.stoppedId] : [], `${label} DELETE calls`);
      assert.deepEqual(saved.tries, expected.savedTries, `${label} saved tries`);
    }
  }
  assert.equal(checked, 70);

  // Control: pre-fix matcher fails by assertion on Story-path selectors.
  const preFixMatch = (testPath, record, rawWord) => {
    const word = rawWord.replace(/^\.\//, '');
    return [record.story, testPath, testPath.split('/').at(-1).replace(/\.json$/, '')].includes(word);
  };
  assert.throws(() => {
    const matched = preFixMatch('tests/tester-panel.json', RECORD_TESTER, 'user_stories/fakes/tester-panel.md');
    const oracleMatched = oracleMatch('tests/tester-panel.json', RECORD_TESTER, 'user_stories/fakes/tester-panel.md', 'user_stories/fakes/tester-panel.md');
    assert.equal(matched, oracleMatched);
  }, { code: 'ERR_ASSERTION' });
});
