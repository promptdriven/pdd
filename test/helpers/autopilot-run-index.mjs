// Fixture access to the machine index. Selection assertions use the public CLI.
import { join } from 'node:path';
import { withAutopilotStore } from '../../src/autopilot-store.mjs';
export const readIndex = stateDir => withAutopilotStore(join(stateDir,'autopilot'),{},tx => ({ runs: tx.list('runs').sort((a,b)=>a.value.order-b.value.order).map(row=>row.value.entry) }));
export const writeIndex = (stateDir,index) => withAutopilotStore(join(stateDir,'autopilot'),{},tx => {
  for(const row of tx.list('runs'))tx.remove('runs',row.key);
  for(const [order,entry] of index.runs.entries())tx.put('runs',entry.runDir ?? `fixture:${order}`,{order,entry});
});
