// Child-only preload. Simulate hosts with absent or inaccessible synthetic PIDs.
import assert from 'node:assert/strict';

const code = process.env.PDD_TEST_OWNER_PROBE;
assert.ok(['ESRCH', 'EPERM'].includes(code));
let probes = 0;
process.kill = (pid, signal) => {
  assert.equal(signal, 0);
  probes++;
  throw Object.assign(Error(code), { code });
};
process.on('exit', () => assert.equal(probes, 0, 'synthetic queue ownership must use its injected observation'));
