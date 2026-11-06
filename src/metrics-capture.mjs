// Generated from prompts/cli/metrics-capture.prompt.md.
const choices = {
  launch: { origin: ['autopilot', 'manual', 'unknown'], status: ['attempted', 'confirmed', 'uncertain', 'failed'] },
  start: { origin: ['autopilot', 'manual', 'unknown'], requiredOutcome: ['code', 'prompt-only', 'unknown'] },
  outcome: { requiredOutcome: ['code', 'prompt-only', 'unknown'] },
  milestone: { stage: ['prompt-pr', 'code-start', 'implementation-ready', 'wait', 'resume'] },
  check: { verdict: ['PASS', 'FAIL', 'NOT SURE'] },
  assistance: { classification: ['recovery', 'decision', 'unknown'] },
  step: { status: ['started', 'done', 'skipped', 'failed', 'waiting', 'resumed'] }
};
const fields = {
  launch: ['origin', 'decisionId', 'status'], start: ['origin', 'decisionId', 'cliVersion', 'skillVersion', 'candidateVersion', 'requiredOutcome'],
  outcome: ['requiredOutcome'], milestone: ['stage', 'reason', 'pr', 'head'],
  check: ['pr', 'head', 'verdict', 'reviewer', 'evidence', 'acceptance'],
  assistance: ['classification', 'evidence'], coverage: ['complete', 'since', 'until'], step: ['step', 'status', 'area']
};
const required = {launch:['origin','status'], start:['origin'], outcome:['requiredOutcome'], milestone:['stage'], check:['verdict'], assistance:['classification'], coverage:['complete'], step:['step','status']};
const safe = value => typeof value === 'string' && value.length > 0 && value.length <= 256 && !/[\r\n]/.test(value);
const iso = value => typeof value === 'string' && /^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(?:\.\d{1,3})?Z$/.test(value) && Number.isFinite(Date.parse(value));
const time = value => typeof value === 'number' && Number.isFinite(value) ? new Date(value).toISOString() : iso(value) ? value : null;

export function captureObservation(input) {
  if (!input || !safe(input.id) || !safe(input.source) || typeof input.repo !== 'string' || !/^[\w.-]+\/[\w.-]+$/.test(input.repo) || !Number.isSafeInteger(input.issue) || input.issue < 1 || !iso(input.at) || !iso(input.observedAt) || !fields[input.type] || !input.data || typeof input.data !== 'object' || Array.isArray(input.data) || (input.attempt !== undefined && !safe(input.attempt))) throw new TypeError('Invalid metrics observation');
  const data = {};
  for (const key of fields[input.type]) {
    const value = input.data[key];
    if (value === undefined || value === null) continue;
    const valid = choices[input.type]?.[key] ? choices[input.type][key].includes(value)
      : key === 'complete' ? typeof value === 'boolean'
      : key === 'pr' ? Number.isSafeInteger(value) && value > 0
      : key === 'since' || key === 'until' ? iso(value)
      : safe(value);
    if (!valid) throw new TypeError(`Invalid metrics ${key}`);
    data[key] = value;
  }
  if (required[input.type].some(key => data[key] === undefined)) throw new TypeError('Missing metrics fact');
  return { schema:'pdd.metrics.event.v1', id:input.id, repo:input.repo.toLowerCase(), issue:input.issue, type:input.type, at:input.at, observedAt:input.observedAt, source:input.source, ...(input.attempt ? {attempt:input.attempt} : {}), data };
}

export function backfillRun({run, source, observedAt, idPrefix}) {
  if (!run || !safe(run.runId) || !safe(idPrefix)) throw new TypeError('Invalid saved run');
  const base = {repo:run.repo, issue:run.number, source, observedAt, attempt:run.runId};
  const events = [];
  for (const [step, record] of Object.entries(run.done ?? {})) {
    const at = time(record?.at);
    if (at && safe(step)) events.push(captureObservation({...base, id:`${idPrefix}:step:${step}:${at}`, type:'step', at, data:{step,status:record.skipped ? 'skipped' : 'done'}}));
  }
  return events;
}

export async function recordObservation({root, observation, store}) {
  try {
    const event = captureObservation(observation);
    await store.appendEvents({root, events:[event]});
    return {ok:true, count:1};
  } catch (error) { return {ok:false, error:String(error?.message ?? error)}; }
}
