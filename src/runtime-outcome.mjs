// Generated from prompts/cli/runtime-outcome.prompt.md (sha256: 15c59ba9b948b59ef7bc066297fc42336a3f5e84838537bb099ac35af1715eeb).
// What happened to one selected test: the one place that turns a server answer into an outcome.
const objects = value => Array.isArray(value) ? value.filter(item => item && typeof item === 'object' && !Array.isArray(item)) : [];
const count = value => Number.isSafeInteger(value) && value >= 0;
const TERMINAL = new Set(['passed', 'failed', 'refused', 'not_run']);
// Exit precedence: the first state present decides. Any state that is not a known end counts as unknown.
const DECIDES = [['unknown', 3], ['not_run', 5], ['refused', 4], ['failed', 1], ['passed', 0]];

const refused = (refusals, extra = {}) => {
  const first = refusals[0] ?? {};
  return { state: 'refused', code: first.code ?? null, field: first.field ?? first.at ?? first.section ?? null, fix: first.fix ?? null,
    message: first.reason ?? first.message ?? first.code ?? null, refusals, ...extra };
};

// Module function: one outcome for one selected test from one server answer.
export function outcomeFor(answer, { test, steps = [], kind = answer?.command, timeLimit = false } = {}) {
  const result = answer?.result, report = result?.report;
  if (timeLimit) return { state: 'unknown', reason: 'The step was stopped at its time limit.' };
  if (answer?.state === 'queued') return { state: 'queued', ...(count(answer.queue?.ahead) ? { ahead: answer.queue.ahead } : {}) };
  if (answer?.state === 'running') {
    const progress = progressFrom(answer.progress);
    return { state: 'running', ...(Object.keys(progress).length ? { progress } : {}) };
  }
  // The public refusal list; the report's own refusal stands in only when that list is empty.
  const refusals = objects(result?.refusals);
  if (!refusals.length && report?.refusal && typeof report.refusal === 'object' && !Array.isArray(report.refusal)) refusals.push(report.refusal);
  // A retryable pool refusal before dispatch is a check that did not run, never a refused test.
  const pool = refusals.find(item => item.code === 'pool-copy-unavailable' && (item.retryable === true || item.details?.retryable === true));
  if (pool && (report?.dispatch ?? answer?.dispatch) === 'not_started')
    return { state: 'not_run', code: pool.code, retryable: true, message: pool.reason ?? pool.message ?? pool.code };
  if (kind === 'lint') return lintOutcome(answer, refusals, test, steps);
  if (answer?.state === 'unknown') return { state: 'unknown', reason: result?.why ?? 'No verdict was returned.' };
  if (answer?.state === 'refused' || report?.verdict === 'refused') return refused(refusals);
  if (answer?.state === 'failed') return { state: 'failed', criteria: objects(report?.criterion_results) };
  if (answer?.state === 'passed' && result && typeof result === 'object') return { state: 'passed' };
  return { state: 'unknown', reason: result?.why ?? 'No verdict was returned.' };
}

// Lint passes a selected test only on positive evidence: complete lint and a passing verdict for that test.
function lintOutcome(answer, refusals, test, steps) {
  const result = answer?.result, report = result?.report, program = report?.program;
  if (!['passed', 'failed', 'refused'].includes(answer?.state)) return { state: 'unknown', reason: 'no lint verdict' };
  const complete = report?.lint && typeof report.lint === 'object' ? report.lint.complete === true : result?.problems_complete === true;
  const listed = objects(Array.isArray(result?.tests) ? result.tests : report?.lint?.tests).filter(item => item.path === test);
  const verdict = listed.length && listed.every(item => item.verdict === listed[0].verdict) ? listed[0].verdict : null;
  const own = [...refusals, ...objects(result?.problems ?? report?.problems)]
    .filter(item => (item.file ?? item.path) === test && item.severity !== 'warning');
  if (own.some(item => refusals.includes(item))) return refused(own);
  // The prompts the test reaches: each step's entry prompt and its declared call targets.
  // An explicit refusal of any reached prompt wins over a prompt that incomplete lint did not list.
  let draft = false, unlisted = false, reachedProblem = null;
  if (Array.isArray(program?.prompts) || Array.isArray(program?.refused_prompts)) {
    const byPath = new Map(objects(program.prompts).map(prompt => [prompt.path, prompt]));
    const refusedPrompts = new Map(objects(program.refused_prompts).map(item => [item.path, item]));
    const reached = new Set(), queue = objects(steps).map(step => step.entry_path);
    while (queue.length && !reachedProblem) {
      const path = queue.shift();
      if (reached.has(path)) continue;
      reached.add(path);
      const prompt = byPath.get(path), state = prompt?.admission_state ?? prompt?.state, item = refusedPrompts.get(path);
      if (item) reachedProblem = { ...item, code: item.code || 'lint-refused', path, section: 'lint', message: `${path}: ${item.message || item.code}` };
      else if (!Array.isArray(program.prompts)) continue;
      else if (!prompt && !complete) unlisted = true;
      else if (!prompt) reachedProblem = { code: 'unknown-target', path, section: 'lint', message: `${path} is not in the lint report.` };
      else if (state === 'stale') reachedProblem = { code: 'interface-stale', path, section: 'lint', message: `${path} changed after its hash was filled or approved.` };
      else if (state !== 'approved' && state !== 'draft') reachedProblem = { code: `interface-${typeof state === 'string' && state ? state : 'unapproved'}`, path,
        section: 'lint', message: `${path} has no usable Runtime interface.` };
      else {
        draft ||= state === 'draft';
        for (const call of objects(prompt.interface?.calls)) if (typeof call.target === 'string') queue.push(call.target);
      }
    }
  }
  if (reachedProblem) return refused([reachedProblem], { draft });
  if (unlisted) return { state: 'unknown', reason: 'lint did not finish', draft };
  if (verdict === 'refused') return refused(own.length ? own : [{ code: 'lint-refused', message: `${test} was refused by complete lint.` }], { draft });
  if (verdict === 'passed' && complete) return { state: 'passed', draft };
  // A job refusal refuses a selected test that has no verdict of its own.
  if (!listed.length && (answer.state === 'refused' || report?.verdict === 'refused' || refusals.length))
    return refused(refusals.length ? refusals : [{ code: 'lint-refused', message: 'The interpreter refused lint.' }], { draft });
  return { state: 'unknown', reason: complete ? 'lint gave no verdict for this test' : 'lint did not finish', draft };
}

function progressFrom(value) {
  const progress = {};
  for (const key of ['steps_done', 'steps_total', 'calls_settled', 'calls_open']) if (count(value?.[key])) progress[key] = value[key];
  if (count(value?.step) || typeof value?.step === 'string' && value.step.trim()) progress.step = value.step;
  return progress;
}

// Module function: the words for an outcome, or for a saved row that carries its outcome fields.
export function outcomeText(outcome) {
  if (outcome.state === 'queued') return `queued${count(outcome.ahead) ? ` · ${outcome.ahead} ahead` : ''}`;
  if (outcome.state === 'not_run') return 'not run';
  if (outcome.state !== 'running') return outcome.state;
  const p = outcome.progress ?? {};
  const step = p.step ?? (count(p.steps_done) && count(p.steps_total) && p.steps_done < p.steps_total ? p.steps_done + 1 : undefined);
  return ['running', ...(typeof step === 'number' ? [`step ${step}${count(p.steps_total) ? ` of ${p.steps_total}` : ''}`] : step ? [step] : []),
    ...(count(p.calls_settled) ? [`${p.calls_settled} AI call${p.calls_settled === 1 ? '' : 's'} so far`] : []),
    ...(p.calls_open > 0 ? [`${p.calls_open} in flight`] : [])].join(' · ');
}

export const hasProgress = outcome => outcome.state === 'running' && Object.keys(outcome.progress ?? {}).length > 0;
export const outcomeDone = outcome => TERMINAL.has(outcome.state);

// Module function: the state that decides a group's result, with the exit code's precedence.
export function outcomeOverall(outcomes, { interrupted = false, lintUnknown = false } = {}) {
  if (interrupted || lintUnknown || !outcomes.length) return 'unknown';
  const present = new Set(outcomes.map(outcome => outcomeDone(outcome) ? outcome.state : 'unknown'));
  return DECIDES.find(([state]) => present.has(state))[0];
}
export const outcomeExitCode = (outcomes, options) => new Map(DECIDES).get(outcomeOverall(outcomes, options));
