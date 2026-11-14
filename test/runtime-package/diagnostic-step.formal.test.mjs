import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { harbor, portsFor } from './runtime-fake.mjs';
import { runCheck } from '../../src/runtime-seam.mjs';

// Exhaust all nonempty subsets of three authored IDs, with and without an unknown ID.
// A stateful world requires every earlier step when a later step is selected.
test('bounded selector refusal and predecessor rule', async t => {
  const setup = harbor(t), file = join(setup.repo, 'tests/place-order.json');
  const doc = JSON.parse(readFileSync(file));
  const ids = ['first', 'second', 'third'];
  doc.steps = ids.map(step_id => ({...structuredClone(doc.steps[0]), step_id}));
  doc.initial_world = { marker: true };
  writeFileSync(file, JSON.stringify(doc));
  for (let mask = 1; mask < 8; mask++) {
    for (const unknown of [false, true]) {
      const selection = ids.filter((_, i) => mask & (1 << i));
      if (unknown) selection.push('absent');
      // Only refusal cases are exercised: no network calls are allowed.
      const prefix = mask === 1 || mask === 3 || mask === 7;
      if (!unknown && prefix) continue;
      const ports = portsFor({HOME: setup.home, PDD_STATE_DIR: setup.state}, {fetch: () => assert.fail('upload before refusal')}).ports;
      const code = await runCheck({cwd: setup.repo, words: ['place-order'], options: {'--step': selection, '--json': true}}, ports);
      assert.equal(code, 4, `mask=${mask} unknown=${unknown}`);
      const refusal = JSON.parse(ports.stdout.text).rows[0].refusals[0];
      assert.equal(refusal.code, unknown ? 'unknown-step' : 'step-prerequisite');
      if (unknown) for (const id of ids) assert.ok(refusal.message.includes(id), refusal.message);
    }
  }
});
