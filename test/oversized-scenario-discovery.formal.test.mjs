import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { findTests, selectTests } from '../src/runtime-preflight.mjs';

// Independent oracle: Story Rules to check, not implementation constants or vectors.
// Exhaust exactly 5 byte sizes x 6 document layouts x 7 selections = 210 cases.
// This proves only these finite materialized documents and stable local snapshots.
const cap = 1_048_576, inspection = 10_485_760;
const sizes = [cap - 1, cap, cap + 1, inspection, inspection + 1];
const layouts = ['early', 'late', 'duplicate-scenario', 'duplicate-data', 'decoy', 'array'];
const selections = [[], ['tests/different-basename.json'], ['different-basename'], ['user_stories/actual-story.md'], ['actual-story'], ['normal'], ['never-authored']];
const schema = 'prompt-runtime.program-scenario.v1';
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
function document(layout, size) {
  const fields = '"criteria":[{"id":"AC1","text":"Echo text."}],"initial_world":{},"steps":[{"step_id":"echo","entry_path":"prompts/echo.prompt.md","operation":"echo","input":{"text":"PAD"},"checks":[{"criterion_id":"AC1","target":"result","path":"/text","op":"equals","value":""}]}]';
  const identity = `"schema_version":"${schema}","story_path":"user_stories/actual-story.md"`;
  const templates = {
    early: `{${identity},${fields}}`,
    late: `{${fields},${identity}}`,
    'duplicate-scenario': `{"schema_version":"data","story_path":"user_stories/obsolete.md",${fields},${identity}}`,
    'duplicate-data': `{${identity},${fields},"schema_version":"data","story_path":"user_stories/obsolete.md"}`,
    decoy: JSON.stringify({ text: 'PAD', nested: { schema_version: schema }, marker: `{"schema_version":"${schema}"}` }),
    array: '["PAD"]',
  };
  const template = templates[layout];
  const text = template.replace('PAD', Buffer.alloc(size - Buffer.byteLength(template) + 3, 65).toString('ascii'));
  assert.equal(Buffer.byteLength(text, 'utf8'), size);
  JSON.parse(text);
  return Buffer.from(text);
}
// No discovery/selection helper participates in expected-result computation.
function oracle(layout, size, selection) {
  const scenario = ['early', 'late', 'duplicate-scenario'].includes(layout);
  const uncertain = size > inspection && layout !== 'array';
  const chosen = selection.length === 0 || !['normal', 'never-authored'].includes(selection[0]);
  if ((uncertain && selection[0] !== 'normal') || (scenario && size > cap && chosen)) return 'refuse';
  if (!selection.length) return scenario ? 'normal+candidate' : 'normal';
  if (selection[0] === 'normal') return 'normal';
  if (scenario && selection[0] !== 'never-authored') return 'candidate';
  return 'unknown';
}
for (const size of sizes) for (const layout of layouts) {
  test(`bounded discovery: ${layout}, ${size} UTF-8 bytes, all seven selections`, t => {
    const root = fs.mkdtempSync(join(tmpdir(), 'pdd-formal-2580-'));
    t.after(() => fs.rmSync(root, { recursive: true, force: true }));
    assert.equal(spawnSync('git', ['init', '-q'], { cwd: root }).status, 0);
    for (const dir of ['tests', 'user_stories', 'prompts']) fs.mkdirSync(join(root, dir));
    fs.writeFileSync(join(root, 'user_stories/actual-story.md'), '# Actual\n\n## Acceptance criteria\n\n1. Echo text.\n');
    fs.writeFileSync(join(root, 'user_stories/normal.md'), '# Normal\n\n## Acceptance criteria\n\n1. Echo text.\n');
    const inputSchema = { type: 'object', properties: { text: { type: 'string' } }, required: ['text'], additionalProperties: false };
    const prose = '# Echo\nReturn the supplied text.\n\n';
    const iface = { status: 'draft', prose_sha256: hash(Buffer.from(prose + '\n')), entries: [{ operation: 'echo', input_schema: inputSchema, result_schema: inputSchema, errors: [] }], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 1 }, conventions: [] };
    fs.writeFileSync(join(root, 'prompts/echo.prompt.md'), prose + '<details><summary>Runtime interface</summary>\n\n```json\n' + JSON.stringify(iface) + '\n```\n</details>\n');
    fs.writeFileSync(join(root, 'tests/normal.json'), document('early', 700).toString().replace('user_stories/actual-story.md', 'user_stories/normal.md'));
    const path = 'tests/different-basename.json', bytes = document(layout, size);
    fs.writeFileSync(join(root, path), bytes);
    assert.equal(fs.statSync(join(root, path)).size, size);
    assert.equal(hash(fs.readFileSync(join(root, path))), hash(bytes));
    const found = findTests({ root });
    for (const selection of selections) {
      const expected = oracle(layout, size, selection);
      const label = JSON.stringify({ layout, size, selection, expected });
      if (expected === 'refuse') {
        assert.throws(() => selectTests(found, selection), error => {
          assert.equal(error.exitCode, 4, label);
          for (const text of [path, String(size), String(cap), ...(size > inspection ? [String(inspection)] : [])]) assert.ok(error.message.includes(text), label + error.message);
          return true;
        }, label);
      } else {
        const actual = selectTests(found, selection);
        const wanted = expected === 'normal+candidate' ? [path, 'tests/normal.json'] : expected === 'candidate' ? [path] : expected === 'normal' ? ['tests/normal.json'] : [];
        assert.deepEqual(actual.selected.map(row => row.path).sort(), wanted.sort(), label);
        assert.deepEqual(actual.unknown, expected === 'unknown' ? selection : [], label);
      }
    }
  });
}
