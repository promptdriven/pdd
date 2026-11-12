import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { runPdd } from '../src/pdd-cli.mjs';
import { runDetailedVersion } from '../src/interpreter-version.mjs';

const pointer = (value, path) => path.slice(1).split('/').reduce((row, key) => row?.[key.replaceAll('~1', '/').replaceAll('~0', '~')], value);
const capture = () => ({ text: '', write(value) { this.text += value; } });

test('replay every approved interpreter-build check through the CLI and helper', async t => {
  const scenario = JSON.parse(readFileSync(new URL('./runtime/interpreter-build.json', import.meta.url), 'utf8'));
  const world = structuredClone(scenario.initial_world);
  let calls, fixtureErrors;
  const port = (name, id) => args => {
    calls.resources[id]++;
    const fixture = scenario.simulation[name], counter = fixture.world_pointer.split('/').at(-1);
    const index = ++world.counters[counter];
    const row = fixture.cases.find(row => row.call_index === index);
    try { assert.ok(row, `${name} fixture ${index}`); assert.deepEqual(JSON.parse(JSON.stringify(args)), row.args, `${name} arguments`); }
    catch (error) { fixtureErrors.push(error); throw error; }
    return structuredClone(row.result);
  };
  const readVersion = port('package.readVersion', 'pdd-cli-package-readVersion');
  const skills = port('skills.findSkills', 'pdd-cli-skills-findSkills');
  const diagnostic = port('diagnostics.pathDiagnostic', 'pdd-cli-diagnostics-pathDiagnostic');
  const helperPorts = { resolveOrigin: port('origin.resolve', 'interpreter-version-origin-resolve'),
    readToken: port('credentials.readToken', 'interpreter-version-credentials-readToken'),
    getMetadata: port('metadata.get', 'interpreter-version-metadata-get') };
  const dependencies = {
    readPackageVersion: readVersion, findSkills: args => skills(args).results,
    pathDiagnostic: args => diagnostic(args).lines,
    interpreterVersion: { runDetailedVersion(input, ports) { calls.internal['interpreter-version']++; return runDetailedVersion(input, ports); } },
    interpreterVersionPorts: helperPorts,
    workflowProve: { proveRun: port('dispatch.prove', 'pdd-cli-dispatch-prove') },
    workflowRunner: { acknowledgeRequest: port('dispatch.requestUptake', 'pdd-cli-dispatch-requestUptake'),
      startRun: port('dispatch.startRun', 'pdd-cli-dispatch-startRun') },
    workflowAgents: { checkWorkflowAgents: port('agents.checkWorkflowAgents', 'pdd-cli-agents-checkWorkflowAgents') },
    setupSkills: port('setup.setupSkills', 'pdd-cli-setup-setupSkills'),
    setupProject: port('setup.setupProject', 'pdd-cli-setup-setupProject'),
    setupAgentMcp: port('setup.setupAgentMcp', 'pdd-cli-setup-setupAgentMcp'),
  };
  for (const step of scenario.steps) await t.test(step.step_id, async st => {
    assert.equal(step.operation, 'runPdd');
    assert.equal(step.entry_path, 'prompts/cli/pdd-cli.prompt.md');
    calls = { internal: { 'interpreter-version': 0 }, resources: {} }; fixtureErrors = [];
    for (const check of step.checks) if (check.target === 'calls' && check.path.startsWith('/resources/')) calls.resources[check.path.split('/').at(-1)] = 0;
    const stdout = capture(), stderr = capture();
    const { argv, ...input } = step.input;
    const exit_code = await runPdd(argv, { cwd: '.', packageRoot: '.', ...input, ...dependencies, stdout, stderr });
    assert.deepEqual(fixtureErrors, [], 'all fixture arguments matched the approved scenario');
    const result = { exit_code, stdout: stdout.text, stderr: stderr.text };
    for (const check of step.checks) await st.test(`${check.criterion_id} ${check.target} ${check.path}`, () => {
      assert.equal(check.op, 'equals', 'all approved operators mapped');
      assert.ok(['result', 'calls', 'world'].includes(check.target), 'all approved targets mapped');
      assert.deepEqual(pointer({ result, calls, world }[check.target], check.path), check.value);
    });
  });
});
