import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { runCliUpgrade } from '../src/autopilot-update.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/migrate-global-pdd.json', import.meta.url), 'utf8'));

for (const step of scenario.steps) {
  test(step.step_id, async () => {
    const world = structuredClone(scenario.initial_world);
    const reply = (operation, path) => {
      const binding = scenario.simulation[operation];
      const counter = binding.world_pointer.slice(1);
      const callIndex = ++world[counter];
      const fixture = binding.cases.find(row => row.call_index === callIndex && row.args.path === path);
      assert.ok(fixture, `${operation}(${path}) has no fixture`);
      return fixture.result;
    };
    const fs = {
      realpathSync: path => reply('fs.realpathSync', path),
      statSync: path => {
        const info = reply('fs.statSync', path);
        return { uid: info.uid, isDirectory: () => info.isDirectory };
      },
      existsSync: path => reply('fs.existsSync', path),
      readFileSync: () => '{"name":"pdd","version":"0.1.31"}',
    };
    const calls = { resources: { 'autopilot-update-process-spawnSync': 0 } };
    assert.equal(step.operation, 'runCliUpgrade');
    const result = await runCliUpgrade({
      ...step.input,
      stderr: { write: text => world.stderr.push({ text }) },
      stdout: { write: text => assert.fail(`Unexpected upgrade output: ${text}`) },
      fetchImpl: async () => ({ ok: true, json: async () => [{ tag_name: 'alpha-v0.1.34' }] }),
      spawnSyncImpl: () => {
        calls.resources['autopilot-update-process-spawnSync']++;
        return { status: 1, stderr: 'npm error code EEXIST' };
      },
    }, { fs, uid: null });
    const observed = { result, world, calls };
    for (const check of step.checks) {
      assert.equal(check.op, 'equals');
      const actual = check.path.slice(1).split('/').reduce((value, key) => value?.[key], observed[check.target]);
      assert.deepEqual(actual, check.value, `${step.step_id}: ${check.target}${check.path}`);
    }
  });
}
