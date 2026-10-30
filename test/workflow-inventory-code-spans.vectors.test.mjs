import test from 'node:test';
import { replay } from './workflow-inventory-replay-helper.mjs';

test('workflow-inventory-code-spans: replay every approved scenario check through the public boundary', async () => {
  await replay('workflow-inventory-code-spans');
});
