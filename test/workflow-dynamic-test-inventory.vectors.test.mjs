import test from 'node:test';
import { replay } from './workflow-inventory-replay-helper.mjs';
for (const story of ['workflow-dynamic-test-inventory', 'workflow-assertion-changes', 'workflow-inventory-code-spans', 'workflow-new-skips', 'workflow-test-inventory']) {
  test(`${story}: replay approved checks through the public boundary`, async () => replay(story));
}
