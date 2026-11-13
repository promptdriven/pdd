import './helpers/test-home.mjs';
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

// Validate the documented after + bind app-map.json directly from RUNBOOK.md so prose and schema cannot drift.
test('RUNBOOK app-map after + bind example is complete, synced and schema-valid', () => {
  const runbook = readFileSync(new URL('../RUNBOOK.md', import.meta.url), 'utf8');
  const skillRunbook = readFileSync(new URL('../skills/pdd-prompting/RUNBOOK.md', import.meta.url), 'utf8');
  assert.equal(runbook, skillRunbook);

  const section = runbook.split('### App map\n')[1]?.split('\n### ')[0];
  assert.ok(section, 'missing ### App map section');
  assert.match(section, /Ordinary `pdd lint <story>` checks the Story's prompts and scenario \(unless the scenario declares `"app_maps": \["app-map\.json"\]`\); `pdd simulate <story> --new` checks `app-map\.json` before starting Try\./);

  const marker = 'An app map with a follow-up `after` step (`app-map.json`):\n```json\n';
  const block = section.split(marker)[1];
  assert.ok(block, 'missing after + bind app-map.json example');
  const end = block.indexOf('\n```');
  assert.notEqual(end, -1);
  const map = JSON.parse(block.slice(0, end));

  assert.deepEqual(
    Object.keys(map).sort(),
    ['handlers', 'initial_route', 'initial_screen', 'initial_state', 'name', 'router', 'routes', 'schema_version', 'screens', 'state_schema', 'stylesheets', 'synthetic'],
  );
  assert.equal(map.schema_version, 'prompt-runtime.app-map.v1');
  assert.equal(typeof map.name, 'string');
  assert.ok(map.name.length > 0);
  assert.equal(map.screens.length, 1);
  assert.equal(map.initial_screen, map.screens[0].id);

  function validSchemaAndValue(schema, value) {
    if (schema.type === 'string') return typeof value === 'string';
    if (schema.type === 'integer') return Number.isSafeInteger(value);
    if (schema.type === 'boolean') return typeof value === 'boolean';
    if (schema.type !== 'object' || value === null || typeof value !== 'object' || Array.isArray(value)) return false;
    if (schema.additionalProperties !== false || !Array.isArray(schema.required) || !schema.properties) return false;
    const keys = Object.keys(schema.properties).sort();
    if (JSON.stringify([...schema.required].sort()) !== JSON.stringify(keys)) return false;
    return keys.every(key => Object.hasOwn(value, key) && validSchemaAndValue(schema.properties[key], value[key]))
      && Object.keys(value).every(key => Object.hasOwn(schema.properties, key));
  }
  assert.ok(validSchemaAndValue(map.state_schema, map.initial_state));

  const handler = map.handlers[0];
  assert.ok(handler && Array.isArray(handler.after) && handler.after.length === 1);
  const step = handler.after[0];
  assert.deepEqual(Object.keys(step).sort(), ['bind', 'handler', 'input']);
  assert.equal(Object.hasOwn(step, 'prompt_path'), false);
  assert.equal(Object.hasOwn(step, 'operation'), false);
  assert.deepEqual(Object.keys(step.handler).sort(), ['operation', 'prompt_path']);
  assert.match(step.handler.prompt_path, /\.prompt\.md$/);
  assert.ok(step.handler.operation.length > 0);

  // bind must be a non-root state pointer whose parent objects exist in initial_state and are required in state_schema.
  assert.ok(step.bind.startsWith('/') && step.bind.length > 1);
  const segments = step.bind.slice(1).split('/').map(part => part.replaceAll('~1', '/').replaceAll('~0', '~'));
  assert.ok(segments.length >= 2, 'example should demonstrate a required parent object on bind');
  let currentSchema = map.state_schema;
  let currentValue = map.initial_state;
  for (let i = 0; i < segments.length - 1; i++) {
    const key = segments[i];
    assert.ok(currentSchema.required.includes(key), `parent "${key}" must be required in state_schema`);
    currentSchema = currentSchema.properties[key];
    currentValue = currentValue[key];
    assert.equal(currentSchema?.type, 'object');
    assert.ok(currentValue && typeof currentValue === 'object' && !Array.isArray(currentValue));
  }
  const leaf = segments.at(-1);
  assert.ok(currentSchema.required.includes(leaf));
  assert.ok(currentSchema.properties[leaf]);

  // Collect all $ref values inside after[0].input and verify only /state and /result roots are used.
  const refs = [];
  function collectRefs(node) {
    if (!node || typeof node !== 'object') return;
    if (!Array.isArray(node) && Object.keys(node).length === 1 && typeof node.$ref === 'string') {
      refs.push(node.$ref);
      return;
    }
    for (const child of Object.values(node)) collectRefs(child);
  }
  collectRefs(step.input);
  assert.ok(refs.length >= 2);
  for (const ref of refs) {
    assert.match(ref, /^\/(?:state|result)(?:\/|$)/, `disallowed $ref root in after input: ${ref}`);
    if (ref.startsWith('/state/')) {
      const targetSchema = ref.slice('/state/'.length).split('/').reduce(
        (cur, key) => cur?.properties?.[key.replaceAll('~1', '/').replaceAll('~0', '~')],
        map.state_schema,
      );
      assert.ok(targetSchema, `missing state_schema field for ${ref}`);
    }
  }
});
