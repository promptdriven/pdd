// Generated from prompts/cli/metrics-hooks.prompt.md.
import { captureObservation } from './metrics-capture.mjs';

const time = value => typeof value === 'number' && Number.isFinite(value) ? new Date(value).toISOString() : value;
const areaFor = (run, step) => run.areas?.find(area => area.steps?.includes(step))?.name;
const completionKey = event => JSON.stringify([event.data.step,event.data.status,event.at,event.data.area ?? null]);

export function journalRunMutation({before, after, source, observedAt, transitionId, observations = []}) {
  if (!after || !transitionId || !Array.isArray(observations)) throw new TypeError('Invalid metrics journal input');
  const prior = after.metrics?.events ?? [];
  if (!Array.isArray(prior)) throw new TypeError('Invalid metrics journal');
  const events = [...prior];
  const known = new Set(events.filter(event => event.type === 'step' && ['done','skipped'].includes(event.data?.status)).map(completionKey));
  const base = {repo:after.repo, issue:after.number, attempt:after.runId, source, observedAt};
  let sequence = 0;
  const add = fact => events.push(captureObservation({...base, ...fact, id:`${transitionId}:${sequence++}`}));
  for (const run of [before, after]) {
    for (const [step, record] of Object.entries(run?.done ?? {})) {
      if (!record?.at) continue;
      const at = time(record.at), data = {step,status:record.skipped ? 'skipped' : 'done'};
      const area = areaFor(run,step); if (area) data.area = area;
      const key = completionKey({at,data});
      if (!known.has(key)) { add({type:'step',at,data}); known.add(key); }
    }
  }
  if (after.state === 'cancelled' && after.cancelled?.state === 'cancelled' && Number.isFinite(after.cancelled.at) && !events.some(e=>e.type==='step' && e.data?.step==='cancel' && e.data?.status==='done')) add({type:'step',at:time(after.cancelled.at),data:{step:'cancel',status:'done'}});
  const oldOutcome=before?.metricsOrigin?.requiredOutcome, newOutcome=after.metricsOrigin?.requiredOutcome;
  if (['code','prompt-only'].includes(newOutcome) && oldOutcome!==newOutcome) add({type:'outcome',at:observedAt,data:{requiredOutcome:newOutcome}});
  const waiting=run=>run?.state==='waiting';
  if (waiting(after) && !waiting(before)) {
    const reason=after.chatFailure ? 'chat-unconfirmed' : after.question ? 'question' : ['ask-code','approve-pr','approve'].includes(after.gate?.kind) ? after.gate.kind : 'unknown';
    add({type:'milestone',at:observedAt,data:{stage:'wait',reason}});
  } else if (waiting(before) && !waiting(after)) add({type:'milestone',at:observedAt,data:{stage:'resume'}});
  for (const observation of observations) add(observation);
  return {...after, metrics:{...(after.metrics ?? {}),events}};
}

export async function drainRunJournal({run, root, store}) {
  const events = run?.metrics?.events ?? [];
  try {
    if (!Array.isArray(events)) throw new TypeError('Invalid metrics journal');
    if (events.length) await store.appendEvents({root,events});
    return {ok:true,count:events.length};
  } catch (error) { return {ok:false,error:String(error?.message ?? error)}; }
}
