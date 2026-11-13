import test from 'node:test';
import assert from 'node:assert/strict';
import { cases, paidCases } from './runtime-compatibility/replay.mjs';
const approved = cases('runtime-compatibility-before-paid-work');
for (const record of approved.cases) test(`COMPAT paid native replay ${record.id} (${record.criterion_ids.join(',')})`, async t => {
  assert.equal(typeof paidCases[record.id], 'function', `Not replayed: ${record.id}`);
  await paidCases[record.id](t);
});
