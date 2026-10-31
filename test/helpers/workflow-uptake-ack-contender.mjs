import { parentPort, workerData } from 'node:worker_threads';
import * as runner from '../../src/workflow-runner.mjs';
const { root, stateDir, env, barrier } = workerData;
try {
 const result = await runner.acknowledgeRequest({ requestId: 'r1', summary: 'First', cwd: root }, {
  stateDir, env, now: () => {
   parentPort.postMessage({ held: true });
   if (Atomics.wait(new Int32Array(barrier), 0, 0, 15000) === 'timed-out') throw Error('ACK contender timed out');
   return 2000;
  },
 });
 parentPort.postMessage({ result });
} catch (error) { parentPort.postMessage({ error: error.stack }); }
