import { parentPort, workerData } from 'node:worker_threads';
import * as runner from '../../src/workflow-runner.mjs';
const { operation, root, source, stateDir, env, barrier } = workerData;
let held = false;
const ports = { stateDir, env, now: () => {
 if (!held) { held = true; parentPort.postMessage({held:true}); if (Atomics.wait(new Int32Array(barrier),0,0,15000)==='timed-out') throw Error('stale-writer barrier timed out'); }
 return 3000;
}, readPrStatus: async () => ({state:'open',ci:'success'}), herdr:async()=>({result:{agent:{agent_status:'idle'}}}) };
try {
 const result = operation === 'runStatus' ? await runner.runStatus({ref:'17',cwd:source},ports)
  : operation === 'stepDone' ? await runner.stepDone({step:'reproduce',summary:'Stale writer',cwd:root},ports)
  : await runner.askPerson({text:'Stale question?',cwd:root},ports);
 parentPort.postMessage({result});
} catch (error) { parentPort.postMessage({error:error.stack}); }
