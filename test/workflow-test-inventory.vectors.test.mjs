import test from 'node:test';
import { replay } from './workflow-inventory-replay-helper.mjs';
test('workflow-test-inventory: replay every approved scenario check through the public boundary', async () => {
  await replay('workflow-test-inventory');
});
