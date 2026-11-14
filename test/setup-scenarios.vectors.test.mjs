import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { runPdd } from '../src/pdd-cli.mjs';
const pointer = (o, p) => p.split('/').slice(1).reduce((v, k) => v?.[k.replace(/~1/g, '/').replace(/~0/g, '~')], o);
for (const name of ['setup-readiness', 'setup-unattended', 'setup-phone-pairing']) test(`replay ${name}`, async () => {
 const scenario = JSON.parse(readFileSync(new URL(`./runtime/${name}.json`, import.meta.url))), world = structuredClone(scenario.initial_world), indexes = {};
 for (const step of scenario.steps) {
  const calls = {};
  const call = (key, args) => {
   const id = `pdd-cli-${key.replace('.', '-')}`; calls[id] = (calls[id] ?? 0) + 1;
   const binding = scenario.simulation[key]; if (!binding) throw Error(`Missing binding ${key}`);
   if (binding.action === 'fixture.lookup') { const index = indexes[key] = (indexes[key] ?? 0) + 1; const row = binding.cases.find(x => x.call_index === index); assert.deepEqual(args, row.args); world[binding.world_pointer.slice(1)] = index; return row.result; }
   pointer(world, binding.world_pointer).push(args); return binding.result_template;
  };
  const input = step.input, stdout = { isTTY: !!input.stdoutIsTTY, text: '', write(x) { this.text += x; } }, stderr = { text: '', write(x) { this.text += x; } }, stdin = { isTTY: !!input.stdinIsTTY };
  const dependencies = { cwd: input.cwd, env: input.env, packageRoot: input.packageRoot, stdout, stderr, stdin,
   checkProjectReady: a => call('setup.checkProjectReady', a).ready,
   pathDiagnostic: a => call('diagnostics.pathDiagnostic', a).lines,
   workflowAgents: { checkWorkflowAgents: a => call('agents.checkWorkflowAgents', a) },
   setupSkills: a => call('setup.setupSkills', a).results,
   setupProject: a => call('setup.setupProject', a),
   setupAgentMcp: a => call('setup.setupAgentMcp', a).exitCode,
   pairing: { runSetupPairing: a => call('pairing.runSetupPairing', a), pairStatus: a => call('pairing.pairStatus', a), pairOffer: a => call('pairing.pairOffer', a) },
   gitContext: () => null, autopilot: { runAutopilot: () => ({ exitCode: 0, message: '' }) }
  };
  const exit_code = await runPdd(input.argv, dependencies), result = { exit_code, stdout: stdout.text, stderr: stderr.text };
  for (const check of step.checks) {
   const got = check.target === 'result' ? pointer(result, check.path) : check.target === 'world' ? pointer(world, check.path) : calls[check.path.split('/').at(-1)] ?? 0;
   assert.equal(check.op, 'equals'); assert.deepEqual(got, check.value, `${name} ${step.step_id} ${check.target}${check.path}`);
  }
 }
});
