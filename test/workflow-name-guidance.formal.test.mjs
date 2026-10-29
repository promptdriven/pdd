import test from 'node:test';
import assert from 'node:assert/strict';
import { runPdd } from '../src/pdd-cli.mjs';

// Oracle: approved user_stories/workflow-name-guidance.md, Rules to check
// and AC1/AC2. Exhaust the canonical decimal issue strings from 1 through 999.
test('bounded missing-workflow rule: every decimal issue from 1 through 999', async () => {
  let dispatches = 0;
  const workflowRunner = new Proxy({}, { get() { dispatches++; assert.fail('Workflow dispatch is forbidden'); } });
  for (let issue = 1; issue <= 999; issue++) {
    const number = String(issue);
    const stdout = { text: '', write(text) { this.text += text; } };
    const stderr = { text: '', write(text) { this.text += text; } };
    const exit = await runPdd(['workflow', 'run', number], { stdout, stderr, workflowRunner });
    assert.equal(exit, 2, `issue ${number}: usage error`);
    assert.equal(stdout.text, '', `issue ${number}: empty stdout`);
    assert.equal(stderr.text, `Name the workflow: pdd workflow run small-change ${number} (or bug, feature). See pdd workflow list.\n`, `issue ${number}: repeat the issue in guidance`);
    assert.equal(dispatches, 0, `issue ${number}: no workflow dispatch`);
  }
});
