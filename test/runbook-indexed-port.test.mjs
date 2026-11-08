import './helpers/test-home.mjs';
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

// Validate the documented files, not a second fixture that can drift from them.
test('RUNBOOK indexed port example has complete, schema-compatible cases', () => {
  const text = readFileSync(new URL('../RUNBOOK.md', import.meta.url), 'utf8');
  const section = text.split('### Return a different port reply on each call\n')[1]?.split('\n### ')[0];
  assert.ok(section);
  const extract = (path, fence, language) => {
    const marker = `\`${path}\`:\n\n${fence}${language}\n`;
    const block = section.split(marker)[1];
    assert.ok(block, `missing ${path}`);
    const end = block.indexOf(`\n${fence}`);
    assert.notEqual(end, -1);
    return block.slice(0, end);
  };
  const prompt = extract('prompts/varying-port.prompt.md', '````', 'markdown');
  const story = extract('user_stories/varying-port.md', '```', 'markdown');
  const scenario = JSON.parse(extract('test/runtime/varying-port.json', '```', 'json'));
  const iface = JSON.parse(prompt.match(/```json\n([\s\S]*?)\n```/)[1]);
  const entry = iface.entries[0];
  const resource = iface.resources.find(item => item.name === 'service');
  const operation = resource.operations.find(item => item.name === 'lookup');
  const binding = scenario.simulation['service.lookup'];
  assert.equal(resource.kind, 'port');
  assert.equal(resource.access, 'write');
  assert.equal(operation.access, 'write');
  assert.equal(binding.action, 'fixture.lookup');
  const pointer = (root, path) => path === '' ? root : path.slice(1).split('/').reduce((value, key) => value[key.replaceAll('~1', '/').replaceAll('~0', '~')], root);
  assert.equal(pointer(scenario.initial_world, binding.world_pointer), 0);
  assert.equal(binding.result_value_pointer, '');
  assert.equal(binding.result_template, null);

  function matches(schema, value) {
    if (schema.type === 'string') return typeof value === 'string';
    if (schema.type !== 'object' || value === null || typeof value !== 'object' || Array.isArray(value)) return false;
    return schema.required.every(key => Object.hasOwn(value, key)) &&
      Object.entries(value).every(([key, child]) => schema.properties[key] ? matches(schema.properties[key], child) : schema.additionalProperties !== false);
  }
  // The pointer selects a location in the declared result schema as well as the template.
  const schemaAt = (schema, path) => path === '' ? schema : path.slice(1).split('/').reduce(
    (current, key) => current?.properties?.[key.replaceAll('~1', '/').replaceAll('~0', '~')], schema);
  assert.ok(schemaAt(operation.result_schema, binding.result_value_pointer));
  assert.equal(schemaAt(operation.result_schema, '/value'), undefined);
  const validCases = cases => {
    const indices = new Set();
    return cases.every(item => {
      if (Object.keys(item).sort().join(',') !== 'args,call_index,result' ||
          !Number.isInteger(item.call_index) || item.call_index < 1 || indices.has(item.call_index) ||
          !matches(operation.arguments_schema, item.args) || !matches(operation.result_schema, item.result)) return false;
      indices.add(item.call_index);
      return true;
    });
  };
  assert.ok(validCases(binding.cases));
  assert.equal(validCases([{ ...binding.cases[0], world_result_bindings: {} }]), false);
  assert.equal(scenario.story_path, 'user_stories/varying-port.md');
  assert.match(story, /Acceptance criteria/);
  assert.equal(scenario.steps.length, 2);
  for (const [index, step] of scenario.steps.entries()) {
    const item = binding.cases[index];
    assert.equal(item.call_index, index + 1);
    assert.equal(step.entry_path, 'prompts/varying-port.prompt.md');
    assert.equal(step.operation, entry.operation);
    assert.ok(matches(entry.input_schema, step.input));
    assert.deepEqual(step.input, item.args);
    assert.ok(matches(entry.result_schema, item.result));
    assert.equal(step.checks[0].criterion_id, scenario.criteria[0].id);
    assert.equal(pointer(item.result, step.checks[0].path), step.checks[0].value);
  }
  assert.notDeepEqual(binding.cases[0].result, binding.cases[1].result);
});
