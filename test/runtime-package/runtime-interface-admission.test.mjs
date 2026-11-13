import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { buildBindingPlan } from '../../src/runtime/runtime-binding-plan.mjs';

function fixture() {
  const iface = { entries: [
    { operation: 'inspect', resource_operations: [] },
    { operation: 'launch', resource_operations: ['process.run'] },
  ], calls: [], resources: [{ name: 'process', kind: 'port', operations: [{ name: 'run' }] }] };
  const context = { calls: [], resources: [{ name: 'source', kind: 'port', operations: [{ name: 'read' }] }] };
  return { iface, input: {
    test: { path: 'tests/inspect.json', storyPath: 'user_stories/inspect.md', doc: { simulation: {}, steps: [
      { step_id: 'inspect', entry_path: 'main.prompt.md', operation: 'inspect' },
      { step_id: 'launch', entry_path: 'main.prompt.md', operation: 'launch' },
    ] } }, storyText: '', prompts: new Map([['main.prompt.md', iface], ['context.prompt.md', context]]),
    dependencyPaths: ['main.prompt.md', 'context.prompt.md'],
  } };
}

test('817: selected entry scope removes unrelated binding advice and keeps context requirements', () => {
  const { input } = fixture();
  const plan = buildBindingPlan(input);
  assert.deepEqual(plan.steps.map(step => step.closure), [
    ['context.prompt.md', 'main.prompt.md'], ['context.prompt.md', 'main.prompt.md'],
  ]);
  assert.deepEqual(plan.edges.map(edge => [edge.step_id, edge.key, edge.state]), [
    ['inspect', 'source.read', 'missing'], ['launch', 'source.read', 'missing'], ['launch', 'process.run', 'missing'],
  ]);
  assert.deepEqual(input.prompts.get('main.prompt.md').entries[0].resource_operations, []);
});

for (const invalid of ['absent', 'partial', 'unknown', 'duplicate', 'uncovered', 'wrong-type', 'ambiguous-entry', 'duplicate-other-entry']) {
  test(`817: ${invalid} scope retains conservative binding advice`, () => {
    const { iface, input } = fixture();
    if (invalid === 'absent') iface.entries.forEach(entry => delete entry.resource_operations);
    if (invalid === 'partial') delete iface.entries[1].resource_operations;
    if (invalid === 'unknown') iface.entries[0].resource_operations = ['ghost.read'];
    if (invalid === 'duplicate') iface.entries[1].resource_operations.push('process.run');
    if (invalid === 'uncovered') iface.entries[1].resource_operations = [];
    if (invalid === 'wrong-type') iface.entries[0].resource_operations = 'process.run';
    if (invalid === 'ambiguous-entry') iface.entries.push({ ...iface.entries[0] });
    if (invalid === 'duplicate-other-entry') iface.entries.push({ ...iface.entries[1] });
    assert.ok(buildBindingPlan(input).edges.some(edge => edge.step_id === 'inspect' && edge.key === 'process.run'));
  });
}

test('817: another operation reached in the same module keeps its resource advice', () => {
  const { iface, input } = fixture();
  iface.calls = [{ operation: 'start', target: 'main.prompt.md', target_operation: 'launch' }];
  assert.ok(buildBindingPlan(input).edges.some(edge => edge.step_id === 'inspect' && edge.key === 'process.run'));
});

test('817: selected entry fixture keeps its bound verdict', () => {
  const { input } = fixture();
  input.test.doc.simulation['process.run'] = { action: 'port.write' };
  const plan = buildBindingPlan(input);
  assert.deepEqual(plan.edges.filter(edge => edge.key === 'process.run').map(edge => [edge.step_id, edge.state]), [['launch', 'bound']]);
});
