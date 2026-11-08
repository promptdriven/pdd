import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { runPdd } from '../src/pdd-cli.mjs';
import { chooseWorkflowAgent } from '../src/workflow-agents.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/use-a-signed-in-workflow-agent.json', import.meta.url)));
const pointer = (obj, path) => path === '' ? obj : path.slice(1).split('/').reduce((o, k) => o?.[k.replaceAll('~1', '/').replaceAll('~0', '~')], obj);

test('replay signed-in workflow agent scenario through public functions', async t => {
  const world = structuredClone(scenario.initial_world);
  let readiness = 0;
  for (const step of scenario.steps) {
    // Reserve the scripted response for this step even if a defective implementation skips the probe.
    const readinessRow = step.operation === 'runPdd' && !step.input.argv.includes('--help')
      ? scenario.simulation['agents.checkWorkflowAgents'].cases[readiness++] : undefined;
    await t.test(step.step_id, async () => {
    const calls = {};
    const call = (name, args) => {
      const key = `pdd-cli-${name.replace('.', '-')}`;
      calls[key] = (calls[key] ?? 0) + 1;
      const spec = scenario.simulation[name];
      if (name === 'agents.checkWorkflowAgents') {
        const row = readinessRow;
        assert.deepEqual(args, row.args, step.step_id);
        return structuredClone(row.result);
      }
      if (spec.world_pointer) pointer(world, spec.world_pointer).push(structuredClone(args));
      return structuredClone(spec.result_template);
    };
    let result;
    if (step.operation === 'chooseWorkflowAgent') result = chooseWorkflowAgent(step.input);
    else {
      const stdout = { text: '', write(s) { this.text += s; } };
      const stderr = { text: '', write(s) { this.text += s; } };
      const exit_code = await runPdd(step.input.argv, { ...step.input, stdout, stderr,
        workflowAgents: { checkWorkflowAgents: async args => call('agents.checkWorkflowAgents', args) },
        pathDiagnostic: args => call('diagnostics.pathDiagnostic', args).lines,
        setupSkills: args => call('setup.setupSkills', args).results,
        setupProject: args => call('setup.setupProject', args),
        setupAgentMcp: async args => call('setup.setupAgentMcp', args).exitCode,
        workflowRunner: { startRun: async (input, ports) => call('dispatch.startRun', { input, env: ports.env }) },
      });
      result = { exit_code, stdout: stdout.text, stderr: stderr.text };
    }
    for (const [index, check] of step.checks.entries()) {
      const actual = check.target === 'result' ? pointer(result, check.path)
        : check.target === 'world' ? pointer(world, check.path)
        : (pointer({ resources: calls }, check.path) ?? 0);
      assert.deepEqual(actual, check.value, `${step.step_id} check ${index}`);
    }
    });
  }
});

test('workflow and setup admit a ready Claude using status probes before effects', async () => {
  const env = { HOME: '/home/example', PATH: '/bin/example', CLAUDE_CONFIG_DIR: '/custom/claude' };
  const probes = [], starts = [], effects = [];
  const run = async (agent, args, options) => {
    probes.push({ agent, args, options });
    if (agent === 'codex') return { code: 1, stdout: '', stderr: 'Not logged in' };
    return { code: 0, stdout: '{"loggedIn":true}', stderr: '' };
  };
  const sink = () => ({ text: '', write(s) { this.text += s; } });
  const common = { cwd: '/project', env, stdout: sink(), stderr: sink(), pathDiagnostic: () => [], workflowAgentPorts: { run },
    setupSkills: () => { effects.push('skills'); return []; }, setupProject: () => { effects.push('project'); return { file: '/project/AGENTS.md', changed: true }; },
    setupAgentMcp: async () => { effects.push('mcp'); return 0; }, workflowRunner: { startRun: async (input, ports) => { starts.push({ input, env: ports.env }); return { exitCode: 0, message: 'Started' }; } } };
  assert.equal(await runPdd(['setup'], common), 0);
  assert.deepEqual(effects, ['skills', 'project', 'mcp']);
  assert.equal(await runPdd(['workflow', 'run', 'bug', '42'], common), 0);
  assert.equal(starts[0].input.agent, 'claude');
  assert.equal(starts[0].env, env);
  assert.equal(probes.length, 8);
  for (const probe of probes) {
    assert.deepEqual(probe.args, probe.agent === 'codex' ? ['login', 'status'] : probe.agent === 'gemini' ? ['--version'] : probe.agent === 'agy' ? ['models'] : ['auth', 'status']);
    assert.equal(probe.options.env, env);
  }
});
