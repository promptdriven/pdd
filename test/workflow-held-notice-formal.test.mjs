import test from 'node:test';
import assert from 'node:assert/strict';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';
import { runStatus } from '../src/workflow-runner.mjs';

test('bounded held-notice status distinguishes definite non-delivery', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  const current = run.areas[run.area].name;
  for (const state of ['pending', 'uncertain', 'in-flight']) {
    for (const departed of [false, true]) {
      const text = 'Saved first line\nSaved second line';
      const row = { id: 'formal-notice', kind: 'notice', text, area: departed ? 'departed-area' : current,
        paneId: 'original-pane', state: state === 'uncertain' ? 'uncertain' : 'pending', at: 1,
        reason: 'screen unavailable', ...(state === 'in-flight' ? { inFlight: true } : {}) };
      const bytes = JSON.stringify({ requests: [row] });
      const ports = { ...f.ports, deliveryFiles: { readFileSync: () => bytes, writeFileSync: () => assert.fail('status must not write the journal') } };
      const result = await runStatus({ ref: '17', cwd: f.source }, ports);
      assert.equal(result.exitCode, 0);
      const final = result.message.includes('was not sent and later changes will not send it');
      assert.equal(final, state === 'pending' && departed, `final-unsent classification: ${state}, departed=${departed}`);
      if (state === 'pending' && departed) {
        assert.ok(result.message.includes(text), 'final notice retains full text');
        assert.ok(result.message.includes(row.reason), 'final notice retains reason');
      }
      assert.equal(bytes, JSON.stringify({ requests: [row] }), 'status preserves journal bytes');
    }
  }
});
