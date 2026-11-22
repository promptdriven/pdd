import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {readRunResults} from '../src/workflow-results.mjs';

// Native local replay. Expectations come from the approved frozen cases, not
// from the reader.
const vectorPath = new URL('./fixtures/retained-binding-evidence-cases.json', import.meta.url);
const vectorBytes = readFileSync(vectorPath);
const vectors = JSON.parse(vectorBytes);
const batch = '20261101-120000-abcd';

function writeBatch({home, root, intent, rows, at}) {
  const folder = join(home, '.pdd/runtime/batches', batch);
  mkdirSync(folder, {recursive: true});
  writeFileSync(join(folder, 'batch.json'), JSON.stringify({version: 1, batch,
    root, intent, created_at: new Date(at).toISOString(), rows}));
  // A saved summary must not become the source of detailed row evidence.
  writeFileSync(join(folder, 'summary.json'), JSON.stringify({batch, rows: [], summary_line: 'No admission verdict.'}));
  return folder;
}

function filesUnder(folder) {
  return Object.fromEntries(readdirSync(folder, {withFileTypes: true}).sort((a, b) => a.name.localeCompare(b.name))
    .flatMap(entry => entry.isDirectory()
      ? Object.entries(filesUnder(join(folder, entry.name))).map(([name, bytes]) => [join(entry.name, name), bytes])
      : [[entry.name, readFileSync(join(folder, entry.name))]]));
}

for (const intent of vectors.reader_intents) for (const row of vectors.reader_cases) {
  test(`3135 reader ${intent}: ${row.id} (${row.criteria.join(',')})`, t => {
    const base = mkdtempSync(join(tmpdir(), 'pdd-retained-evidence-'));
    t.after(() => rmSync(base, {recursive: true, force: true}));
    const root = join(base, 'project'), home = join(base, 'home');
    mkdirSync(root); mkdirSync(home);
    writeBatch({root, home, intent, rows: row.rows, at: Date.parse('2026-11-01T12:00:00Z')});
    const before = filesUnder(base);
    const requests = [];
    t.mock.method(globalThis, 'fetch', async (...args) => {
      requests.push(args); assert.fail('Saved-result reader must not request a service');
    });
    const results = readRunResults({root}, {env: {HOME: home},
      capture: () => assert.fail('Legacy evidence must not start source capture'),
      git: () => assert.fail('Saved-result reader must not start Git')});
    assert.equal(results.length, 1);
    assert.equal(results[0].kind, intent === 'check' ? 'pdd test' : 'pdd lint');
    assert.deepEqual(results[0].states, row.expected_states, '3135_READER_EVIDENCE_DROPPED');
    assert.deepEqual(filesUnder(base), before, 'AC4: reader changed saved files');
    assert.deepEqual(requests, [], 'AC4: reader requested a service');
    assert.deepEqual(readFileSync(vectorPath), vectorBytes, 'Frozen cases changed');
  });
}
