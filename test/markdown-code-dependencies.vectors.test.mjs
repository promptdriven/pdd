import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { markdownDefinitions, markdownLinks, markdownSectionText } from '../src/runtime/runtime-markdown.mjs';

const pointer = (value, path) => path === '' ? value : path.slice(1).split('/').reduce(
  (current, key) => current[key.replace(/~1/g, '/').replace(/~0/g, '~')], value);

test('MARKDOWN-VECTORS: replay every approved Markdown result check', async t => {
  const scenario = JSON.parse(readFileSync(new URL('./runtime/markdown-code-dependencies.json', import.meta.url), 'utf8'),
    (key, value, context) => typeof value === 'number' && /^-?(?:0|[1-9][0-9]*)$/.test(context.source)
      && !Number.isSafeInteger(value) ? BigInt(context.source) : value);
  const results = new Map();
  const resolve = value => {
    if (Array.isArray(value)) return value.map(resolve);
    if (!value || typeof value !== 'object') return value;
    if (Object.hasOwn(value, '$step_result')) {
      const ref = value.$step_result;
      assert.ok(results.has(ref.step_id), `Not replayed: unavailable prior result ${ref.step_id}`);
      return pointer(results.get(ref.step_id), ref.path);
    }
    return Object.fromEntries(Object.entries(value).map(([key, child]) => [key, resolve(child)]));
  };
  // These projections express the approved JSON transport only. Each operation
  // calls the existing native export; no product wrapper or implicit mask exists.
  const operations = {
    markdownSectionText: input => ({ text: markdownSectionText(input.text) }),
    markdownDefinitions: input => ({ definitions: [...markdownDefinitions(input.text)]
      .map(([label, destination]) => ({ label, destination })) }),
    markdownLinks: input => ({ destinations: markdownLinks(input.text,
      new Map(input.definitions.map(({ label, destination }) => [label, destination])), input.imagesOnly) }),
  };
  let executed = 0;
  const expected = scenario.steps.reduce((count, step) => count + step.checks.length, 0);
  for (const step of scenario.steps) {
    assert.ok(Object.hasOwn(operations, step.operation), `Not replayed: operation ${step.operation}`);
    const result = operations[step.operation](resolve(step.input));
    results.set(step.step_id, result);
    for (const check of step.checks) {
      await t.test(`${step.step_id}: ${check.criterion_id} ${check.path}`, () => {
        assert.equal(check.target, 'result', `Not replayed: target ${check.target}`);
        assert.equal(check.op, 'equals', `Not replayed: comparison ${check.op}`);
        executed++;
        assert.deepEqual(pointer(result, check.path), check.value);
      });
    }
  }
  assert.equal(executed, expected, 'Every frozen check must execute');
  t.diagnostic(`Replayed ${scenario.steps.length} public operations and ${executed}/${expected} frozen result checks.`);
});
