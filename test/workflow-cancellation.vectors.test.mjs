import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import * as runner from '../src/workflow-runner.mjs';

const pointer = (value, path) => path.split('/').slice(1).reduce((item, key) => item?.[key.replace(/~1/g, '/').replace(/~0/g, '~')], value);

// These adapters bind the documented production dependencies. records.save is
// deliberately the writeRun INPUT ledger, not a simulated persisted status file.
for (const story of ['cancel-or-replace-run', 'keep-run-when-stop-is-uncertain']) {
  test(`approved runtime vectors: ${story}`, async t => {
    const scenario = JSON.parse(readFileSync(new URL(`../tests/runtime/${story}.json`, import.meta.url)));
    const world = structuredClone(scenario.initial_world);
    let counts;
    function resource(name, args) {
      const simulation = scenario.simulation[name];
      counts[name] = (counts[name] ?? 0) + 1;
      const result = structuredClone(simulation.result_template);
      const store = pointer(world, simulation.world_pointer);
      if (simulation.action === 'port.write') store.push(structuredClone(args));
      else if (simulation.action === 'key-value.get') {
        const key = pointer(args, simulation.key_argument_pointer);
        const field = simulation.result_value_pointer.slice(1);
        result[field] = store[key] ?? null;
      } else if (simulation.action === 'key-value.put') {
        store[pointer(args, simulation.key_argument_pointer)] = pointer(args, simulation.value_argument_pointer);
      } else assert.fail(`Not replayed: ${name} uses ${simulation.action}`);
      return result;
    }
    const load = (key, cwd = '/project') => {
      const value = resource('records.load', { key, cwd }).value;
      return value ? JSON.parse(value) : null;
    };
    const p = {
      env: { HOME: '/home' }, isTTY: true,
      gitContext: async () => ({ toplevel: '/project', commonDir: '/project/.git' }),
      withIssueCustody: async (_run, action) => action(),
      execFile: async () => ({ stdout: '' }),
      readWorkflowAreas: input => JSON.parse(resource('workflows.read', input).workflow),
      resolveWorkflowIssue: async input => JSON.parse(resource('github.resolve', input).binding),
      readRun: dir => load(dir.split('/').at(-1)),
      resolveRun: async (ref, { cwd }) => { const run = load(ref, cwd); return run ? { run } : { error: 'Run not found' }; },
      runForWorktree: async cwd => load(cwd, cwd),
      writeRun: run => resource('records.save', { key: run.runId, value: JSON.stringify(run) }),
      now: () => resource('clock.now', {}).now,
      confirm: async question => resource('person.confirm', { question }).answer,
      stopChats: async run => resource('chats.stop', { run: JSON.stringify(run) }),
      releaseIssueClaim: async input => resource('claims.release', input),
      uuid: () => resource('identity.uuid', {}).runId,
      allocateIssueWorktree: async input => { const result = resource('worktrees.allocate', input); return { ...result, assignment: JSON.parse(result.assignment) }; },
      archiveRun: (from, to) => resource('archives.rename', { from, to }),
      startChat: async ({ run, area, message }) => JSON.parse(resource('chats.start', { run: JSON.stringify(run), area, message }).chat),
    };
    let checked = 0;
    for (const step of scenario.steps) {
      await t.test(step.step_id, async () => {
        counts = {};
        let result, error;
        try { result = await runner[step.operation](step.input, p); }
        catch (caught) { error = { code: caught.code ?? caught.message }; }
        for (const check of step.checks) {
          const source = check.target === 'result' ? result : check.target === 'world' ? world : check.target === 'error' ? error : undefined;
          const got = check.target === 'calls' ? counts[check.path.replace('/resources/workflow-runner-', '').replace('-', '.')] ?? 0 : pointer(source, check.path);
          const label = `${step.step_id} ${check.criterion_id} ${check.target} ${check.path}`;
          if (check.op === 'equals') assert.deepEqual(got, check.value, label);
          else if (check.op === 'contains') assert.ok(got?.includes(check.value), `${label}: expected ${JSON.stringify(check.value)} in ${JSON.stringify(got)}`);
          else if (check.op === 'not_contains') assert.ok(!got?.includes(check.value), label);
          else assert.fail(`Not replayed: ${label} uses ${check.op}`);
          checked++;
        }
      });
    }
    assert.equal(checked, scenario.steps.reduce((sum, step) => sum + step.checks.length, 0));
  });
}
