import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { runPdd } from '../../src/pdd-cli.mjs';

const pointer = (value, path) => path === '' ? value : path.slice(1).split('/').reduce((v, k) => v?.[k.replace(/~1/g, '/').replace(/~0/g, '~')], value);
const clone = value => structuredClone(value);
const set = (value, path, item) => { const keys = path.slice(1).split('/'); const last = keys.pop(); let at = value; for (const key of keys) at = at[key] ??= {}; at[last] = item; };
export async function replayScenario(name, { output } = {}) {
  const vector = `test/runtime/${name}.json`, bytes = readFileSync(vector), scenario = JSON.parse(bytes);
  const world = clone(scenario.initial_world), checks = [], operations = [], effects = [];
  let prove, evidence;
  try { prove = await import('../../src/workflow-prove.mjs'); } catch (e) { if (e.code !== 'ERR_MODULE_NOT_FOUND') throw e; }
  try { evidence = await import('../../src/workflow-pr-evidence.mjs'); } catch (e) { if (e.code !== 'ERR_MODULE_NOT_FOUND') throw e; }
  assert.equal(typeof (name === 'workflow-prove' ? prove?.proveRun : evidence?.preparePrEvidence), 'function', `#2594 missing API: ${name}`);
  for (const step of scenario.steps) {
    const calls = { resources: {} }, ports = {};
    for (const [binding, rule] of Object.entries(scenario.simulation)) {
      const [resource, method] = binding.split('.');
      ports[method] = async input => {
        const id = resource === 'host' ? `workflow-prove-host-${method}` : resource === 'publication' ? `workflow-pr-evidence-publication-${method}` : 'pdd-cli-dispatch-prove';
        calls.resources[id] = (calls.resources[id] ?? 0) + 1;
        let reply;
        if (rule.action === 'collection.get') {
          const row = pointer(world, rule.world_pointer).find(row => JSON.stringify(pointer(row, rule.item_key_pointer)) === JSON.stringify(pointer(input, rule.key_argument_pointer)));
          assert.ok(row, `${name}/${step.step_id}: no callback fixture for ${binding} ${JSON.stringify(input)}`);
          reply = clone(pointer(row, rule.item_value_pointer));
        } else if (rule.action === 'fixture.lookup') {
          const index = (pointer(world, rule.world_pointer) ?? 0) + 1; set(world, rule.world_pointer, index);
          const row = rule.cases.find(row => row.call_index === index);
          assert.ok(row, `${binding} call ${index} not declared`); assert.deepEqual(input, row.args, `${binding} exact forwarding`); reply = clone(row.result);
        } else if (rule.action === 'port.write') {
          pointer(world, rule.world_pointer).push(clone(input)); reply = clone(rule.result_template);
        } else assert.fail(`Unsupported simulation action ${rule.action}`);
        effects.push({ step_id: step.step_id, binding, input: clone(input), reply: clone(reply) }); return reply;
      };
    }
    let result;
    if (step.operation === 'proveRun') result = await prove.proveRun(step.input, ports);
    else if (step.operation === 'preparePrEvidence') result = await evidence.preparePrEvidence(step.input, ports);
    else if (step.operation === 'runPdd') {
      let stdout = '', stderr = '';
      const exit_code = await runPdd(step.input.argv, { cwd: step.input.cwd ?? '.', stdout: { write: s => { stdout += s; } }, stderr: { write: s => { stderr += s; } }, workflowProve: { proveRun: ports.prove } });
      result = { exit_code, stdout, stderr };
    } else assert.fail(`Unmapped public operation ${step.operation}`);
    operations.push({ vector, step_id: step.step_id, entry_path: step.entry_path, operation: step.operation, executed: true, outcome: 'returned', boundary: { kind: 'function', name: step.operation }, observed_result: clone(result), command: `node --test test/${name}.vectors.test.mjs`, exit_code: 0 });
    for (let i = 0; i < step.checks.length; i++) {
      const check = step.checks[i], actual = pointer(({ result, world, calls, error: null })[check.target], check.path);
      // An uncalled resource is the observed count zero, not a missing observation.
      const got = check.target === 'calls' && actual === undefined ? 0 : actual;
      const identity = { vector, step_id: step.step_id, check_index: i, entry_path: step.entry_path, operation: step.operation, ...Object.fromEntries(['criterion_id', 'target', 'path', 'op'].map(k => [k, check[k]])) };
      let failure;
      try { if (check.op === 'equals') assert.deepEqual(got, check.value); else if (check.op === 'not_equals') assert.notDeepEqual(got, check.value); else if (check.op === 'contains') assert.ok(typeof got === 'string' ? got.includes(check.value) : got.some(x => JSON.stringify(x) === JSON.stringify(check.value))); else assert.fail(`Unmapped check op ${check.op}`); } catch (error) { failure = error; }
      checks.push({ ...identity, expected: clone(check.value), got: clone(got), outcome: failure ? 'fail' : 'pass' });
    }
  }
  const report = { vector, sha256: createHash('sha256').update(bytes).digest('hex'), checks, operations, effects, finalWorld: world };
  if (output) writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  return report;
}
export function assertReplay(report) {
  const failures = report.checks.filter(row => row.outcome !== 'pass');
  assert.deepEqual(failures, [], `${report.vector}: ${failures.length} exact checks failed`);
}
