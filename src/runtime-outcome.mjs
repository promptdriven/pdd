// Selected-test evidence shared by lint admission, results, progress and exits.
const objects = value => Array.isArray(value) ? value.filter(item => item && typeof item === 'object') : [];
const count = value => Number.isSafeInteger(value) && value >= 0;
const terminal = new Set(['passed', 'failed', 'refused', 'not_run']);
const states = new Set([...terminal, 'queued', 'running', 'unknown']);
const refusalOutcome = (refusals, fallback = 'lint-refused') => {
  const first = refusals[0] ?? { code: fallback };
  return { state: 'refused', code: first.code ?? fallback, field: first.field ?? first.at ?? first.section ?? null,
    fix: first.fix ?? null, message: first.reason ?? first.message ?? first.code ?? fallback, refusals };
};

export function outcomeFor(answer, { test, steps = [], kind = answer?.command, timeLimit = false } = {}) {
  const result = answer?.result, report = result?.report;
  if (timeLimit) return { state: 'unknown', reason: 'The step was stopped at its time limit.' };
  // Persisted rows are evidence already projected by the client, not fresh job answers.
  if (!kind && !Object.hasOwn(answer ?? {}, 'result')) {
    const state = states.has(answer?.state) ? answer.state : 'unknown';
    return { state, ...(count(answer?.ahead) ? { ahead: answer.ahead } : {}), ...(answer?.progress ? { progress: progressFor(answer.progress) } : {}),
      ...(state === 'unknown' ? { reason: answer?.why ?? answer?.note?.message ?? 'No verdict was returned.' } : {}) };
  }
  if (answer?.state === 'queued') return { state: 'queued', ...(count(answer.queue?.ahead) ? { ahead: answer.queue.ahead } : {}) };
  if (answer?.state === 'running') return { state: 'running', progress: progressFor(answer.progress) };
  const refusals = objects(result?.refusals);
  if (report?.refusal && !refusals.some(item => item.code === report.refusal.code && (item.message ?? item.reason) === (report.refusal.message ?? report.refusal.reason))) refusals.push(report.refusal);
  const pool = refusals.find(item => item.code === 'pool-copy-unavailable' && (item.retryable === true || item.details?.retryable === true));
  if (pool && (report?.dispatch ?? answer?.dispatch) === 'not_started') return {
    state: 'not_run', code: pool.code, retryable: true, message: pool.reason ?? pool.message ?? pool.code, refusals };
  if (kind === 'lint') {
    const tests = Array.isArray(result?.tests) ? result.tests : report?.lint?.tests;
    const selected = objects(tests).filter(item => item.path === test);
    const verdict = selected.length && selected.every(item => item.verdict === selected[0].verdict) ? selected[0].verdict : null;
    const complete = report?.lint ? report.lint.complete === true : result?.problems_complete === true;
    const diagnostics = [...objects(result?.problems ?? report?.problems), ...refusals, ...objects(report?.program?.refused_prompts)];
    const own = diagnostics.filter(item => (item.file ?? item.path) === test && item.severity !== 'warning');
    if (own.length) return { ...refusalOutcome(own.length ? own : [{ code: 'lint-refused', message: `${test} was refused by complete lint.` }]), diagnostics };
    const program = report?.program, prompts = objects(program?.prompts);
    const byPath = new Map(prompts.map(prompt => [prompt.path, prompt]));
    const promptRefusals = new Map(objects(program?.refused_prompts).map(item => [item.path, item]));
    let draft = false;
    {
      const reached = new Set(), queue = steps.map(step => step.entry_path);
      while (queue.length) {
        const path = queue.shift();
        if (reached.has(path)) continue;
        reached.add(path);
        const prompt = byPath.get(path), state = prompt?.admission_state ?? prompt?.state;
        const explicit = promptRefusals.get(path);
        let problem = explicit;
        if (!problem && !prompt && !Array.isArray(program?.prompts)) continue;
        if (!problem && !prompt && !complete) return { state: 'unknown', reason: 'lint did not finish', diagnostics };
        if (!problem && !prompt) problem = { code: 'unknown-target', path, message: `${path} is not in the lint report.` };
        if (!problem && !['approved', 'draft'].includes(state)) problem = { code: `interface-${state || 'unapproved'}`, path,
          section: 'lint', message: `${path} has no usable Runtime interface.` };
        if (problem) return { ...refusalOutcome([problem]), diagnostics, draft };
        draft ||= state === 'draft';
        for (const call of objects(prompt.interface?.calls)) if (typeof call.target === 'string') queue.push(call.target);
      }
    }
    if (verdict === 'refused') return { ...refusalOutcome([{ code: 'lint-refused', message: `${test} was refused by complete lint.` }]), diagnostics, draft };
    if (verdict === 'passed' && complete) return { state: 'passed', diagnostics, draft };
    if (!selected.length && (answer?.state === 'refused' || report?.verdict === 'refused' || refusals.length))
      return { ...refusalOutcome(refusals.length ? refusals : [{ code: 'lint-refused', message: 'The interpreter refused lint.' }]), diagnostics, draft };
    return { state: 'unknown', reason: !complete ? 'lint did not finish' : 'Lint returned no verdict for the selected test.', diagnostics, draft };
  }
  if (answer?.state === 'refused' || report?.verdict === 'refused') return refusalOutcome(refusals, 'refused');
  if (answer?.state === 'not_run') return { state: 'not_run', code: answer.code, retryable: answer.retryable === true, message: answer.message };
  if (answer?.state === 'failed') return { state: 'failed', criteria: objects(report?.criterion_results) };
  if (answer?.state === 'passed' && result && typeof result === 'object') return { state: 'passed' };
  return { state: 'unknown', reason: result?.why ?? 'No verdict was returned.' };
}

function progressFor(value) {
  const progress = {};
  for (const key of ['steps_done', 'steps_total', 'calls_settled', 'calls_open']) if (count(value?.[key])) progress[key] = value[key];
  if (count(value?.step) || typeof value?.step === 'string' && value.step.trim()) progress.step = value.step;
  return progress;
}

export function outcomeText(outcome) {
  if (outcome.state === 'queued') return `queued${count(outcome.ahead) ? ` · ${outcome.ahead} ahead` : ''}`;
  if (outcome.state !== 'running') return outcome.state === 'not_run' ? 'not run' : outcome.state;
  const p = outcome.progress ?? {}, step = p.step ?? (count(p.steps_done) && count(p.steps_total) && p.steps_done < p.steps_total ? p.steps_done + 1 : undefined);
  return ['running', ...(typeof step === 'number' ? [`step ${step}${count(p.steps_total) ? ` of ${p.steps_total}` : ''}`] : step ? [step] : []),
    ...(count(p.calls_settled) ? [`${p.calls_settled} AI call${p.calls_settled === 1 ? '' : 's'} so far`] : []),
    ...(p.calls_open > 0 ? [`${p.calls_open} in flight`] : [])].join(' · ');
}

export const outcomeDone = outcome => terminal.has(outcome.state);
export function outcomeExitCode(outcomes, { interrupted = false, lintUnknown = false } = {}) {
  if (interrupted || lintUnknown || !outcomes.length || outcomes.some(outcome => !outcomeDone(outcome))) return 3;
  if (outcomes.some(outcome => outcome.state === 'not_run')) return 5;
  if (outcomes.some(outcome => outcome.state === 'refused')) return 4;
  if (outcomes.some(outcome => outcome.state === 'failed')) return 1;
  return 0;
}
