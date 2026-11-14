import test from 'node:test';
import assert from 'node:assert/strict';
import { expandSource } from '../../src/runtime/contract-refs.mjs';

const scenarioPath = 'tests/runtime/story.json';
function expand(scenario, sources) {
  const files = {
    stat: ({ path }) => ({ exists: Object.hasOwn(sources, path), is_symlink: false, size: Buffer.byteLength(sources[path] ?? '') }),
    read: ({ path }) => ({ content: sources[path] })
  };
  return JSON.parse(expandSource({ path: scenarioPath, text: JSON.stringify(scenario), format: 'scenario' }, files).text);
}

test('bounded shared binding replacement preserves other bindings and step overrides', () => {
  // Exhaust all presence combinations for two identifiers across shared and local maps.
  for (let sharedMask = 0; sharedMask < 4; sharedMask++) for (let localMask = 0; localMask < 4; localMask++) {
    const shared = {}, local = {}, expected = {};
    for (let i = 0; i < 2; i++) {
      const key = `port${i}`;
      if (sharedMask & (1 << i)) shared[key] = { kind: 'read_world', sharedOnly: i, value_template: { $ref: `/world/${i}` } };
      if (localMask & (1 << i)) local[key] = { kind: 'write_world', localOnly: i, value_template: { $ref: `/input/${i}` } };
      if (localMask & (1 << i)) expected[key] = local[key];
      else if (sharedMask & (1 << i)) expected[key] = shared[key];
    }
    const steps = [{ simulation_overrides: { port0: { kind: 'error', message: 'step' } } }];
    const sources = { 'shared.json': JSON.stringify(shared) };
    const result = expand({ $simulation: 'shared.json', simulation: local, steps }, sources);
    assert.deepEqual(result.simulation, expected, `shared=${sharedMask}, local=${localMask}`);
    assert.deepEqual(result.steps, steps);
    assert.equal(sources['shared.json'], JSON.stringify(shared));
  }
});

test('bounded invalid references report scenario and reference location', () => {
  const cases = [
    [{ $simulation: 'missing.json' }, {}],
    [{ $simulation: '../outside.json' }, {}],
    [{ $simulation: 7 }, {}],
    [{ $simulation: 'loop.json' }, { 'loop.json': JSON.stringify({ $simulation: 'loop.json' }) }],
    [{ $simulation: 'bad.json' }, { 'bad.json': '[]' }]
  ];
  for (const [scenario, sources] of cases) assert.throws(() => expand(scenario, sources), error => {
    assert.match(error.message, /tests\/runtime\/story\.json/);
    assert.match(error.message, /\/\$simulation/);
    return true;
  });
});

test('binding contents remain literal', () => {
  const binding = { kind: 'read_world', value_template: { $seed: 'missing.json', $contract: 'missing.json', $simulation: 'missing.json' } };
  const sources = { 'shared.json': JSON.stringify({ port: binding }) };
  assert.deepEqual(expand({ $simulation: 'shared.json' }, sources).simulation.port, binding);
});
