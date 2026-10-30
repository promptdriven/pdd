import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { composeProductTry } from '../src/product-composition.mjs';
import { productStatus } from '../src/product.mjs';

const pointer = (value, path) => path === '' ? value : path.slice(1).split('/').reduce((item, token) => item?.[token.replace(/~1/g, '/').replace(/~0/g, '~')], value);

for (const name of ['product-compose-try', 'product-journey-seed', 'product-server-without-screen', 'product-map-field-diagnostics']) test(`${name}: unchanged prompt-space cases execute actual public module functions`, async () => {
  const scenario = JSON.parse(readFileSync(new URL(`./runtime/${name}.json`, import.meta.url)));
  const world = structuredClone(scenario.initial_world);
  const invoke = (resource, args) => {
    const binding = scenario.simulation[resource];
    assert.ok(binding, `Not replayed resource ${resource}`);
    if (binding.action === 'port.write') pointer(world, binding.world_pointer).push(structuredClone(args));
    return structuredClone(binding.result_template);
  };
  const readFile = path => {
    const file = world.files[path];
    if (!file) throw Object.assign(Error(`${path} missing`), { code: 'ENOENT' });
    return file.content;
  };
  const ports = {
    readProductState: async args => invoke('productState.read', args),
    writeProductState: async args => invoke('productState.write', args),
    lockProductState: async args => invoke('productState.lock', args),
    unlockProductState: async args => invoke('productState.unlock', args),
    now: async () => invoke('clock.now', {}),
    ...Object.fromEntries(['issuePage','issueByNumber','timelinePage','pullRequest','currentActor'].filter(name => scenario.simulation['github.' + name]).map(name => [name, async args => { const value = invoke('github.' + name, args); return value.json ? JSON.parse(value.json) : value; }])),
    readFile, statFile(path) { const file = world.files[path]; return { exists: !!file, is_symlink: file?.is_symlink ?? false, size: file ? Buffer.byteLength(file.content) : 0 }; },
    listRuns: args => JSON.parse(invoke('runs.list', args).json),
    storyEvidence: run => JSON.parse(invoke('runs.evidence', { run_json: JSON.stringify(run) }).json),
    resolveRepository: args => invoke('github.repository', args),
    planOnBase: args => invoke('repository.planOnBase', args).present,
    execFile: (file, args, { cwd }) => { assert.equal(file, 'gh'); return invoke('github.run', { args, cwd }); },
  };
  for (const step of scenario.steps) {
    let result, error;
    try {
      if (step.operation === 'composeProductTry') result = composeProductTry(step.input, ports);
      else if (step.operation === 'productStatus') result = await productStatus(step.input, ports);
      else assert.fail(`Not replayed operation ${step.operation}`);
    } catch (caught) { error = caught; }
    if (!step.expected_error) assert.equal(error, undefined, `${step.step_id}: ${error?.stack}`);
    for (const check of step.checks) {
      const target = check.target === 'result' ? result : check.target === 'world' ? world : check.target === 'error' ? error : null;
      assert.notEqual(target, null, `Not replayed target ${check.target}`);
      const actual = pointer(target, check.path), label = `${name}/${step.step_id}/${check.criterion_id}${check.path}`;
      if (check.op === 'equals') assert.deepEqual(actual, check.value, label);
      else if (check.op === 'contains') { assert.equal(typeof actual, 'string', label); assert.ok(actual.includes(check.value), label); }
      else if (check.op === 'count') assert.equal(actual?.length, check.value, label);
      else assert.fail(`Not replayed check ${check.op}`);
    }
  }
});
