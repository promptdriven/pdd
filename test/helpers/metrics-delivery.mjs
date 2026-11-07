import {appendEvents} from '../../src/metrics-store.mjs';
// Worker reply means its real optional ledger writes have settled, so teardown
// cannot race writes from another isolate. This changes no workflow oracle.
export function metricsDelivery() {
 const pending=new Set();
 return {
  metricsAppendEvents(input) {
   const task=appendEvents(input);pending.add(task);
   task.then(()=>pending.delete(task),()=>pending.delete(task));return task;
  },
  async settle() {
   do { await new Promise(resolve=>setImmediate(resolve));await Promise.allSettled([...pending]); } while(pending.size);
   await new Promise(resolve=>setImmediate(resolve));
  }
 };
}
