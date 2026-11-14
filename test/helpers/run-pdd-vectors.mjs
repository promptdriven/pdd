import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { runPdd } from '../../src/pdd-cli.mjs';

// Replay the approved runPdd steps of a Story's test file on the real CLI entry (RUNBOOK §17).
// Steps are help and usage errors: no step may reach workflow or Autopilot execution.
const pointer = (value, path) => path === '' ? value : path.slice(1).split('/').reduce(
  (current, key) => current?.[key.replace(/~1/g, '/').replace(/~0/g, '~')], value);
const capture = () => ({ text: '', write(value) { this.text += value; } });
const compare = {
  equals: (actual, value) => assert.deepEqual(actual, value),
  not_equals: (actual, value) => assert.notDeepEqual(actual, value),
  contains: (actual, value) => { assert.equal(typeof actual, 'string'); assert.ok(actual.includes(value), JSON.stringify(actual)); },
  not_contains: (actual, value) => { assert.equal(typeof actual, 'string'); assert.ok(!actual.includes(value), JSON.stringify(actual)); },
};

export async function replayRunPddVectors(t, file) {
  const scenario = JSON.parse(readFileSync(new URL(`../runtime/${file}`, import.meta.url), 'utf8'));
  assert.ok(scenario.steps.length > 0);
  const world = structuredClone(scenario.initial_world ?? {});
  const noDispatch = new Proxy({}, { get() { assert.fail('A help or usage-error step must not dispatch'); } });
  for (const step of scenario.steps) {
    await t.test(step.step_id, async st => {
      assert.equal(step.operation, 'runPdd', `Not replayed: unmapped operation ${step.operation}`);
      const stdout = capture(), stderr = capture(), calls = { resources: {} }, mapped = new Set();
      const spy = binding => {
        if (!scenario.simulation?.[binding]) return undefined;
        mapped.add(binding);
        const [resource, method] = binding.split('.');
        const owner = ['origin', 'credentials', 'metadata'].includes(resource) ? 'interpreter-version' : 'pdd-cli';
        const id = `${owner}-${resource}-${method}`;
        calls.resources[id] = 0;
        return () => { calls.resources[id]++; assert.fail(`Unexpected ${binding} call`); };
      };
      const get = name => spy(name);
      const runAutopilotLauncher = get('autopilotLauncher.runAutopilotLauncher');
      const deps = {
        readPackageVersion: get('package.readVersion'), findSkills: get('skills.findSkills'),
        pathDiagnostic: get('diagnostics.pathDiagnostic'),
        interpreterVersionPorts: { resolveOrigin: get('origin.resolve'), readToken: get('credentials.readToken'), getMetadata: get('metadata.get') },
        workflowProve: { proveRun: get('dispatch.prove') },
        workflowRunner: { acknowledgeRequest: get('dispatch.requestUptake'), startRun: get('dispatch.startRun') },
        workflowAgents: { checkWorkflowAgents: get('agents.checkWorkflowAgents') },
        setupSkills: get('setup.setupSkills'), setupProject: get('setup.setupProject'), setupAgentMcp: get('setup.setupAgentMcp'),
        autopilotLauncher: runAutopilotLauncher ? { runAutopilotLauncher } : noDispatch,
      };
      for (const key of Object.keys(scenario.simulation ?? {})) assert.ok(mapped.has(key), `Not replayed: unmapped simulation ${key}`);
      const exit_code = await runPdd(step.input.argv, { stdout, stderr, ...deps });
      const result = { exit_code, stdout: stdout.text, stderr: stderr.text };
      for (const check of step.checks) {
        assert.ok(check.target === 'result' || check.target === 'calls', `Not replayed: unmapped target ${check.target}`);
        assert.ok(compare[check.op], `Not replayed: unmapped comparison ${check.op}`);
        await st.test(`${check.criterion_id} ${check.path} ${check.op} ${JSON.stringify(check.value)}`, () => {
          const actual = pointer(check.target === 'calls' ? calls : result, check.path);
          if (check.target === 'calls') assert.notEqual(actual, undefined, `Not replayed: unmapped call count ${check.path}`);
          compare[check.op](actual, check.value);
        });
      }
    });
  }
}
