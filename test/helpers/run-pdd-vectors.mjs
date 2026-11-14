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
      const stdout = capture(), stderr = capture(), calls = { resources: {} }, mapped = new Set(), fixtureErrors = [];
      const spy = (binding, owner = 'pdd-cli') => {
        const rule = scenario.simulation?.[binding];
        if (!rule) return undefined;
        mapped.add(binding);
        const [resource, method] = binding.split('.');
        const id = `${owner}-${resource}-${method}`;
        calls.resources[id] = 0;
        return input => {
          calls.resources[id]++;
          try {
            if (rule.action === 'port.write') {
              pointer(world, rule.world_pointer).push(structuredClone(input));
              return structuredClone(rule.result_template);
            }
            assert.equal(rule.action, 'fixture.lookup', `Not replayed: unmapped action ${rule.action}`);
            const parts = rule.world_pointer.slice(1).split('/');
            const key = parts.pop().replace(/~1/g, '/').replace(/~0/g, '~');
            const parent = pointer(world, '/' + parts.join('/'));
            assert.equal(typeof parent?.[key], 'number', `${binding} fixture counter`);
            const index = ++parent[key];
            const row = rule.cases.find(candidate => candidate.call_index === index);
            assert.ok(row, `${binding} fixture ${index}`);
            assert.deepEqual(JSON.parse(JSON.stringify(input)), row.args, `${binding} arguments`);
            return structuredClone(row.result);
          } catch (error) {
            fixtureErrors.push(error);
            throw error;
          }
        };
      };
      const runAutopilotLauncher = spy('autopilotLauncher.runAutopilotLauncher');
      const prove = spy('dispatch.prove'), requestUptake = spy('dispatch.requestUptake');
      const startRun = spy('dispatch.startRun'), checkWorkflowAgents = spy('agents.checkWorkflowAgents');
      const pathDiagnostic = spy('diagnostics.pathDiagnostic'), findSkills = spy('skills.findSkills');
      const readPackageVersion = spy('package.readVersion');
      const setupSkills = spy('setup.setupSkills'), setupProject = spy('setup.setupProject');
      const setupAgentMcp = spy('setup.setupAgentMcp');
      const resolveOrigin = spy('origin.resolve', 'interpreter-version');
      const readToken = spy('credentials.readToken', 'interpreter-version');
      const getMetadata = spy('metadata.get', 'interpreter-version');
      for (const key of Object.keys(scenario.simulation ?? {})) assert.ok(mapped.has(key), `Not replayed: unmapped simulation ${key}`);
      const options = { stdout, stderr,
        workflowRunner: new Proxy({ ...(requestUptake && { acknowledgeRequest: requestUptake }),
          ...(startRun && { startRun }) }, { get(target, key) { return key in target ? target[key] : noDispatch[key]; } }),
        autopilotLauncher: runAutopilotLauncher ? { runAutopilotLauncher } : noDispatch,
        ...(prove && { workflowProve: { proveRun: prove } }),
        ...(checkWorkflowAgents && { workflowAgents: { checkWorkflowAgents } }),
        ...(pathDiagnostic && { pathDiagnostic: args => pathDiagnostic(args).lines }),
        ...(findSkills && { findSkills: args => findSkills(args).results }),
        ...(readPackageVersion && { readPackageVersion }),
        ...(setupSkills && { setupSkills }), ...(setupProject && { setupProject }),
        ...(setupAgentMcp && { setupAgentMcp }),
        interpreterVersionPorts: { ...(resolveOrigin && { resolveOrigin }), ...(readToken && { readToken }),
          ...(getMetadata && { getMetadata }) },
      };
      let exit_code, runError;
      try { exit_code = await runPdd(step.input.argv, options); } catch (error) { runError = error; }
      assert.deepEqual(fixtureErrors, [], 'all fixture arguments matched the approved scenario');
      if (runError) throw runError;
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
