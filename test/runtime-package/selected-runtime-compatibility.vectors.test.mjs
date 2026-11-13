import test from 'node:test';
import assert from 'node:assert/strict';
import { cases, viewCases } from './runtime-compatibility/replay.mjs';
const approved = cases('selected-runtime-compatibility');
for (const record of approved.cases) test(`COMPAT selected native replay ${record.id} (${record.criterion_ids.join(',')})`, async t => {
  assert.equal(typeof viewCases[record.id], 'function', `Not replayed: ${record.id}`);
  await viewCases[record.id](t);
});
