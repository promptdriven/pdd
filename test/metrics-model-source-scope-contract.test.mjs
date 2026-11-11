import './helpers/test-home.mjs';
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { checkInput, interfaceBlocks, interfaceSchemaProblems, proseSha256 } from '../src/runtime/runtime-preflight.mjs';
import { calculateMetrics } from '../src/metrics-model.mjs';

const prompt = readFileSync(new URL('../prompts/cli/metrics-model.prompt.md', import.meta.url), 'utf8');
const contract = JSON.parse(interfaceBlocks(prompt)[0][1]);
const entry = contract.entries.find(({ operation }) => operation === 'calculateMetrics');
const fixture = JSON.parse(readFileSync(new URL('./runtime/metrics-shared-report.json', import.meta.url))).steps[0].input;
// Output and input schemas use the same native JSON Schema validation path.
const checkOutput = (output, schema) => checkInput(output, schema, 0);

test('model source scope composes with the frozen scenario and actual calculator', () => {
  assert.ok(entry, 'calculateMetrics contract entry exists');
  assert.ok(entry.input_schema && typeof entry.input_schema === 'object', 'input schema exists');
  assert.ok(entry.result_schema && typeof entry.result_schema === 'object', 'result schema exists');
  assert.deepEqual(interfaceSchemaProblems(contract), []);
  assert.equal(contract.prose_sha256, proseSha256(prompt));
  assert.deepEqual(checkInput(fixture, entry.input_schema, 0).refusals, []);
  assert.deepEqual(checkOutput(calculateMetrics(fixture), entry.result_schema).refusals, []);
  for (const source of [
    { source: 'machine-a' },
    { source: 'machine-a', scope: 'all-retained-repo-events' },
    { source: 'machine-a', scope: 'unknown' },
  ]) {
    const input = { ...fixture, sources: [source] };
    assert.deepEqual(checkInput(input, entry.input_schema, 0).refusals, []);
    const output = calculateMetrics(input);
    assert.deepEqual(output.sources, [source]);
    assert.deepEqual(checkOutput(output, entry.result_schema).refusals, []);
  }
  const invalid = { ...fixture, sources: [{ source: 'machine-a', scope: 'invalid' }] };
  assert.ok(checkInput(invalid, entry.input_schema, 0).refusals.length);
  const output = calculateMetrics(fixture);
  for (const source of [
    { source: 'machine-a', scope: 'invalid' },
    { source: 'machine-a', unexpected: true },
  ]) {
    assert.ok(checkOutput({ ...output, sources: [source] }, entry.result_schema).refusals.length);
  }
});
