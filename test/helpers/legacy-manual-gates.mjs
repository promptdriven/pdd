import { writeRun } from '../../src/workflow-runs.mjs';

// These synthetic cases cover persisted pre-card workflows. Retain the real
// decisions and approval journal, but omit the additive Story-card record that
// an older saved run did not have. Normal card publication has its own tests.
export function legacyManualGates(f) {
  const run = f.record();
  delete run.storyApproval;
  writeRun(run, f.ports);
}
