import test from 'node:test';
import { replay } from './workflow-inventory-replay-helper.mjs';
test('workflow-assertion-changes: replay every approved scenario check through the public boundary', async () => {
  await replay('workflow-assertion-changes');
});
