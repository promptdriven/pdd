import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import * as product from '../src/product.mjs';

const pointer = (value, path) => path === '' ? value : path.split('/').slice(1).reduce((item, token) => item?.[token.replace(/~1/g, '/').replace(/~0/g, '~')], value);
for (const name of ['map', 'status', 'next', 'start', 'issue-binding', 'search-cache', 'unavailable-actor', 'repair-link', 'unresolved-link', 'worktree-links', 'state-updates']) {
  test(`product-${name}: original prompt-space vectors at public module boundaries`, async () => {
    const scenario = JSON.parse(readFileSync(new URL(`./runtime/product-${name}.json`, import.meta.url)));
    const world = structuredClone(scenario.initial_world), calls = {};
    const invoke = (resource, args) => {
      const key = `product-${resource.replace('.', '-')}`;
      calls[key] = (calls[key] ?? 0) + 1;
      const binding = scenario.simulation[resource];
      assert.ok(binding, `Unmapped resource ${resource}`);
      if (binding.action === 'key-value.get') return { json: pointer(world, binding.world_pointer)[pointer(args, binding.key_argument_pointer)] ?? null };
      if (binding.action === 'key-value.put') { pointer(world, binding.world_pointer)[pointer(args, binding.key_argument_pointer)] = pointer(args, binding.value_argument_pointer); return {}; }
      if (binding.action === 'port.write') pointer(world, binding.world_pointer).push(structuredClone(args));
      return structuredClone(binding.result_template);
    };
    let fallbackState = null;
    const ports = {
      lockProductState: async args => invoke('productState.lock', args),
      unlockProductState: async args => invoke('productState.unlock', args),
      readProductState: async args => scenario.simulation['productState.read'] ? invoke('productState.read', args) : ({ json: fallbackState }),
      writeProductState: async args => { if (scenario.simulation['productState.write']) return invoke('productState.write', args); fallbackState = args.json; return {}; },
      now: async () => scenario.simulation['clock.now'] ? invoke('clock.now', {}) : ({ milliseconds: 0 }),
      ...Object.fromEntries(['issuePage','issueByNumber','timelinePage','pullRequest','currentActor'].filter(name=>scenario.simulation['github.'+name]).map(name=>[name,async args=>{const value=invoke('github.'+name,args);return value.json?JSON.parse(value.json):value;}])),
      readFile: async path => {
        const file = world.files[path]; if (!file) throw Object.assign(Error('missing'), { code: 'ENOENT' }); return file.content;
      },
      listRuns: async args => JSON.parse(invoke('runs.list', args).json),
      storyEvidence: async run => JSON.parse(invoke('runs.evidence', { run_json: JSON.stringify(run) }).json),
      resolveRepository: async args => invoke('github.repository', args),
      planOnBase: async args => invoke('repository.planOnBase', args).present,
      createIssue: async args => invoke('github.createIssue', args),
      execFile: async (file, args, { cwd }) => { assert.equal(file, 'gh'); return invoke('github.run', { args, cwd }); },
      startRun: async args => invoke('workflow.start', args),
    };
    for (const step of scenario.steps) {
      for (const key of Object.keys(calls)) delete calls[key];
      let result, error;
      try { result = await product[step.operation](step.input, ports); } catch (caught) { error = caught; }
      if (!step.expected_error) assert.equal(error, undefined, `${step.step_id}: ${error?.stack}`);
      for (const check of step.checks) {
        const source = check.target === 'result' ? result : check.target === 'world' ? world : check.target === 'error' ? error : check.target === 'calls' ? { resources: new Proxy(calls, { get: (object, key) => object[key] ?? 0 }) } : null;
        assert.notEqual(source, null, `Not replayed target ${check.target}`);
        const actual = pointer(source, check.path), label = `${name}/${step.step_id}/${check.criterion_id}${check.path}`;
        if (check.op === 'equals') assert.deepEqual(actual, check.value, label);
        else if (check.op === 'not_equals') assert.notDeepEqual(actual, check.value, label);
        else if (check.op === 'count') assert.equal(actual?.length, check.value, label);
        else if (check.op === 'contains') { assert.equal(typeof actual, 'string', label); assert.ok(actual.includes(check.value), label); }
        else assert.fail(`Not replayed operation ${check.op}`);
      }
    }
  });
}
