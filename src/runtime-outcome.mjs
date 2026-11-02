// Generated from prompts/cli/runtime-outcome.prompt.md (sha256: 1191f789e2f90581ae521758f335315804768b5f4deb6e693634c0a01969be55).
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
  if (answer?.state === 'failed') return { state: 'failed', criteria: objects(report?.criterion_results) };
  if (answer?.state === 'refused' || report?.verdict === 'refused') return refused(refusals);
  if (answer?.state === 'passed' && result && typeof result === 'object') return { state: 'passed' };
  return { state: 'unknown', reason: result?.why ?? 'No verdict was returned.' };
}

// A selected test passes lint on its own evidence: a passing per-test verdict. An ended lint that
// gives a test no verdict leaves it not run; only a lint that has not ended is unknown.
function lintOutcome(answer, refusals, test, steps) {
  const result = answer?.result, report = result?.report, program = report?.program;
  if (!['passed', 'failed', 'refused'].includes(answer?.state)) return { state: 'unknown', reason: 'no lint verdict' };
  const complete = report?.lint && typeof report.lint === 'object' ? report.lint.complete === true : result?.problems_complete === true;
  const entries = list => objects(list).filter(item => item.path === test);
  const listed = entries(result?.tests).length ? entries(result.tests) : entries(report?.lint?.tests);
  const verdict = listed.length && listed.every(item => item.verdict === listed[0].verdict) ? listed[0].verdict : null;
  const own = [...refusals, ...objects(result?.problems ?? report?.problems)]
    .filter(item => (item.file ?? item.path) === test && item.severity !== 'warning');
  // The prompts the test reaches: each step's entry prompt and its declared call targets.
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
      const problem = (code, message) => ({ code, path, section: 'lint', message, reached: true });
      if (item) reachedProblem = { ...item, ...problem(item.code || 'lint-refused', `${path}: ${item.message || item.code}`) };
      else if (!Array.isArray(program.prompts)) continue;
      else if (!prompt && !complete) unlisted = true;
      else if (!prompt) reachedProblem = problem('unknown-target', `${path} is not in the lint report.`);
      else if (state === 'stale') reachedProblem = problem('interface-stale', `${path} changed after its hash was filled or approved.`);
      else if (state !== 'approved' && state !== 'draft') reachedProblem = problem(`interface-${typeof state === 'string' && state ? state : 'unapproved'}`,
        `${path} has no usable Runtime interface.`);
      else {
        draft ||= state === 'draft';
        for (const call of objects(prompt.interface?.calls)) if (typeof call.target === 'string') queue.push(call.target);
      }
    }
  }
  const notRun = reason => ({ state: 'not_run', code: null, retryable: false, reason, draft });
  if (own.some(item => refusals.includes(item))) return refused(own, { draft });
  if (reachedProblem) return refused([reachedProblem], { draft });
  if (verdict === 'refused') return refused(own.length ? own : [{ code: 'lint-refused', message: `${test} was refused by complete lint.` }], { draft });
  if (verdict === 'passed') return { state: 'passed', draft };
  // A job refusal refuses a selected test that has no verdict of its own.
  if (!listed.length && (answer.state === 'refused' || report?.verdict === 'refused' || refusals.length))
    return refused(refusals.length ? refusals : [{ code: 'lint-refused', message: 'The interpreter refused lint.' }], { draft });
  return notRun(complete && !unlisted && verdict !== 'not-checked' ? 'lint gave no verdict for this test' : 'lint did not finish');
}

function progressFrom(value) {
  const progress = {};
  for (const key of ['steps_done', 'steps_total', 'calls_settled', 'calls_open']) if (count(value?.[key])) progress[key] = value[key];
  if (Number.isSafeInteger(value?.step) && value.step >= 1 || typeof value?.step === 'string' && value.step.trim()) progress.step = value.step;
  return progress;
}

const callWords = (settled, open) => [...(count(settled) ? [`${settled} AI call${settled === 1 ? '' : 's'} so far`] : []), ...(open > 0 ? [`${open} in flight`] : [])];

// Module function: the words for an outcome, or for a saved row that carries its outcome fields.
export function outcomeText(outcome) {
  if (outcome.state === 'queued') return `queued${count(outcome.ahead) ? ` · ${outcome.ahead} ahead` : ''}`;
  if (outcome.state === 'not_run') return 'not run';
  if (outcome.state !== 'running') return outcome.state;
  const p = outcome.progress ?? {};
  const step = p.step ?? (count(p.steps_done) && count(p.steps_total) && p.steps_done < p.steps_total ? p.steps_done + 1 : undefined);
  return ['running', ...(typeof step === 'number' ? [`step ${step}${count(p.steps_total) ? ` of ${p.steps_total}` : ''}`] : step ? [step] : []),
    ...callWords(p.calls_settled, p.calls_open)].join(' · ');
}

export const hasProgress = outcome => outcome.state === 'running' && Object.keys(outcome.progress ?? {}).length > 0;

// Module function: one progress fragment for a group of rows; null when no row has server progress.
// One row keeps its step; several rows add up the counts they report.
export function progressText(outcomes) {
  const moving = outcomes.filter(hasProgress);
  if (moving.length < 2) return moving.length ? outcomeText(moving[0]) : null;
  const reported = key => moving.filter(outcome => count(outcome.progress[key]));
  const sum = key => reported(key).reduce((total, outcome) => total + outcome.progress[key], 0);
  return ['running', ...callWords(reported('calls_settled').length ? sum('calls_settled') : undefined, sum('calls_open'))].join(' · ');
}

export const outcomeDone = outcome => TERMINAL.has(outcome.state);

// Module function: the state that decides a group's result, with the exit code's precedence.
export function outcomeOverall(outcomes, { interrupted = false, lintUnknown = false } = {}) {
  if (interrupted || lintUnknown || !outcomes.length) return 'unknown';
  const present = new Set(outcomes.map(outcome => outcomeDone(outcome) ? outcome.state : 'unknown'));
  return DECIDES.find(([state]) => present.has(state))[0];
}
export const outcomeExitCode = (outcomes, options) => new Map(DECIDES).get(outcomeOverall(outcomes, options));
