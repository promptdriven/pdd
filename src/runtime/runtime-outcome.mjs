// Generated from prompts/cli/runtime-outcome.prompt.md (sha256: 743f92ec9409b8049bba6de22cbcf62411a91651a0196a9e9a0990c0b9e71b36).
// What happened to one selected test: the one place that turns a server answer into an outcome.
export const PROVIDER_TEXT = 'the AI provider failed during the run. It is not a failed check. Do not send it again yet.';
export const CHECK_STATES = Object.freeze(['waiting', 'sent', 'passed', 'failed', 'refused', 'partial', 'not run']);

// The public result is independent of the transport state needed to resume a job.
export function resultOutcome(row = {}) {
  const supplied = row.note ?? (row.reason && typeof row.reason === 'object' ? row.reason : null);
  const originalCode = supplied?.code || row.code || (row.time_limit ? 'deadline' : null) || row.provider?.code || (row.state === 'sending' ? 'dispatch-uncertain' : null) || row.refusals?.[0]?.code;
  let code = ['check-busy', 'lint-busy'].includes(originalCode) ? 'server-busy' : originalCode === 'lint-pending' ? 'deadline' : originalCode;
  const states = { ready: 'waiting', queued: 'sent', running: 'sent', sending: 'partial', not_run: 'not run', unknown: 'partial' };
  let state = Object.hasOwn(states, row.state) ? states[row.state] : CHECK_STATES.includes(row.state) ? row.state : 'partial';
  if (row.unsent && row.refusals?.length) { code='broken-test'; state='not run'; }
  if (code === 'broken-test') state = 'not run';
  if (state === 'not run' && (row.retryable === true || row.busy_display) && !['timeout-flag', 'deadline', 'interrupted'].includes(code)) code = 'server-busy';
  if (state === 'passed') return { state, reason: null };
  const defaults = { waiting: ['awaiting-admission', 'Waiting for admission.'], sent: ['awaiting-server-verdict', 'Sent; waiting for a server verdict.'],
    failed: ['check-failed', 'A check failed.'], refused: ['admission-refused', 'Admission was refused.'],
    partial: ['no-server-verdict', 'No complete server verdict.'], 'not run': ['no-server-verdict', 'No server verdict for this test.'] };
  const [fallbackCode, fallbackMessage] = defaults[state];
  const message = supplied?.message || (row.time_limit ? [row.time_limit.message, row.time_limit.fix].filter(Boolean).join(' ') : null) || (row.provider ? PROVIDER_TEXT : null) || row.message || (typeof row.reason === 'string' ? row.reason : null) || row.why || row.refusals?.[0]?.message || fallbackMessage;
  return { state, reason: { code: code || fallbackCode, message } };
}

const objects = value => Array.isArray(value) ? value.filter(item => item && typeof item === 'object' && !Array.isArray(item)) : [];
const count = value => Number.isSafeInteger(value) && value >= 0;
const TERMINAL = new Set(['passed', 'failed', 'refused', 'not_run']);
// Group precedence: the first state present decides. Any state that is not a known end counts as unknown.
const DECIDES = ['unknown', 'not_run', 'refused', 'failed', 'passed'];

const nonEmpty = (...values) => values.find(value => typeof value === 'string' && value.length > 0) ?? null;

const refused = (refusals, extra = {}) => {
  const first = refusals[0] ?? {};
  return { state: 'refused', code: first.code ?? null, field: first.field ?? first.at ?? first.section ?? null, fix: first.fix ?? null,
    message: first.reason ?? first.message ?? first.code ?? null, refusals, ...extra };
};

const appMapRefused = (refusals, extra = {}) => {
  const first = refusals[0] ?? {};
  return { state: 'refused', code: nonEmpty(first.code),
    field: nonEmpty(first.field, first.at, first.pointer, first.section, first.file, first.path),
    fix: nonEmpty(first.fix), message: nonEmpty(first.reason, first.message, first.code), refusals, ...extra };
};

// Module function: one outcome for one selected test from one server answer.
export function outcomeFor(answer, { test, steps = [], appMaps, kind = answer?.command, timeLimit = false, sourceFiles, capacityUncertain = false } = {}) {
  const outcome = answerOutcome(answer, { test, steps, appMaps, kind, timeLimit, sourceFiles, capacityUncertain });
  if (outcome.state !== 'passed' && !outcome.code) outcome.code = timeLimit ? 'deadline' : resultOutcome(outcome).reason.code;
  return kind === 'lint' ? { ...outcome, compatibility: selectedCompatibility(answer, test, sourceFiles) } : outcome;
}

function answerOutcome(answer, { test, steps, appMaps, kind, timeLimit, sourceFiles, capacityUncertain }) {
  const result = answer?.result, report = result?.report;
  if (timeLimit) return { state: 'unknown', reason: 'The step was stopped at its time limit.' };
  if (capacityUncertain && kind === 'check') return { state: 'unknown', reason: 'Check capacity accounting is incomplete or conflicting.' };
  if (answer?.state === 'queued') return { state: 'queued', ...(count(answer.queue?.ahead) ? { ahead: answer.queue.ahead } : {}) };
  if (answer?.state === 'running') {
    const progress = progressFrom(answer.progress);
    return { state: 'running', ...(Object.keys(progress).length ? { progress } : {}) };
  }
  // The public refusal list; the report's own refusal stands in only when that list is empty.
  const refusals = objects(result?.refusals);
  if (!refusals.length && report?.refusal && typeof report.refusal === 'object' && !Array.isArray(report.refusal)) refusals.push(report.refusal);
  // A refusal the server declares retryable, before dispatch, is a check that did not run, whatever its code.
  const retry = refusals.find(item => item.retryable === true || item.details?.retryable === true);
  if (retry && (report?.dispatch ?? answer?.dispatch) === 'not_started')
    return { state: 'not_run', code: retry.code ?? 'server-busy', retryable: true, message: retry.reason ?? retry.message ?? retry.code ?? null };
  if (kind === 'lint') return lintOutcome(answer, refusals, test, steps, appMaps, sourceFiles);
  if (answer?.state === 'unknown') return { state: 'unknown', reason: result?.why ?? 'No verdict was returned.' };
  if (answer?.state === 'failed') return { state: 'failed', criteria: objects(report?.criterion_results) };
  if (answer?.state === 'refused' || report?.verdict === 'refused') return refused(refusals);
  if (answer?.state === 'passed' && result && typeof result === 'object') return { state: 'passed' };
  return { state: 'unknown', reason: result?.why ?? 'No verdict was returned.' };
}

function normalizeMapProblem(item, mapPath) {
  const { detail, ...rest } = item;
  const message = nonEmpty(
    item.message,
    [item.reason, item.fix].filter(Boolean).join(' '),
    detail,
    item.engine_message,
    item.code,
  );
  return {
    ...rest,
    code: nonEmpty(item.code) ?? 'lint-refused',
    file: item.file ?? mapPath,
    path: item.path ?? item.file ?? mapPath,
    ...(message ? { message } : {}),
  };
}

// A selected test passes lint on its own evidence: a passing per-test verdict and passing applicable app maps.
// An ended lint that gives a test or applicable app map no verdict leaves it not run; only a lint that has not ended is unknown.
function lintOutcome(answer, refusals, test, steps, appMaps, sourceFiles) {
  const result = answer?.result, report = result?.report, program = report?.program;
  if (!['passed', 'failed', 'refused'].includes(answer?.state)) return { state: 'unknown', reason: 'no lint verdict' };
  const complete = report?.lint && typeof report.lint === 'object' ? report.lint.complete === true : result?.problems_complete === true;
  const entries = list => objects(list).filter(item => item.path === test);
  const listed = entries(result?.tests).length ? entries(result.tests) : entries(report?.lint?.tests);
  const verdict = listed.length && listed.every(item => item.verdict === listed[0].verdict) ? listed[0].verdict : null;
  const problems = objects(result?.problems).length ? objects(result.problems) : objects(report?.problems);
  const targetOf = item => nonEmpty(item.file, item.path);
  const own = [...refusals, ...problems].filter(item => targetOf(item) === test && item.severity !== 'warning');
  const hasAppMaps = Array.isArray(result?.app_maps) || Array.isArray(report?.lint?.app_maps);
  const reportAppMaps = objects(report?.lint?.app_maps);
  const rawAppMaps = objects(result?.app_maps).length ? objects(result.app_maps) : reportAppMaps;
  const applicableMaps = Array.isArray(appMaps)
    ? [...new Set(appMaps.filter(path => typeof path === 'string' && path.length > 0))]
    : [...new Set(rawAppMaps.map(item => item.path).filter(path => typeof path === 'string' && path.length > 0))];
  const applicableSet = new Set(applicableMaps);
  const appMapProblems = problems.filter(item => applicableSet.has(targetOf(item)) && item.severity !== 'warning');
  const matchingAppMapRefusals = refusals.filter(item => applicableSet.has(targetOf(item)) && item.severity !== 'warning');
  const reportMapErrors = reportAppMaps
    .filter(entry => applicableSet.has(entry.path))
    .flatMap(entry => objects(entry.errors).filter(item => item.severity !== 'warning').map(item => normalizeMapProblem(item, entry.path)));
  const entryErrors = applicableMaps.flatMap(mapPath => {
    const entry = [...rawAppMaps, ...reportAppMaps].find(item => item.path === mapPath && nonEmpty(item.error));
    return entry ? [normalizeMapProblem({ code: entry.error, ...(nonEmpty(entry.reason) ? { reason: entry.reason } : {}) }, mapPath)] : [];
  });
  const candidateItems = [
    ...appMapProblems.map(item => normalizeMapProblem(item, targetOf(item))),
    ...matchingAppMapRefusals.map(item => normalizeMapProblem(item, targetOf(item))),
    ...reportMapErrors,
  ];
  const specificMaps = new Set(
    candidateItems
      .filter(item => nonEmpty(item.code) && item.code !== 'lint-refused')
      .map(targetOf),
  );
  for (const fallback of entryErrors) {
    const mapPath = targetOf(fallback);
    if (!specificMaps.has(mapPath)) {
      candidateItems.push(fallback);
      specificMaps.add(mapPath);
    }
  }
  const appMapRefusals = [];
  const seenAppMapRefusals = new Map();
  for (const item of candidateItems) {
    const mapPath = targetOf(item);
    if (item.code === 'lint-refused' && specificMaps.has(mapPath)) continue;
    const key = JSON.stringify([
      mapPath,
      nonEmpty(item.code),
      nonEmpty(item.field, item.at, item.pointer, item.section, item.file, item.path),
      nonEmpty(item.reason, item.message, item.code),
    ]);
    const existingIndex = seenAppMapRefusals.get(key);
    if (existingIndex === undefined) {
      seenAppMapRefusals.set(key, appMapRefusals.length);
      appMapRefusals.push(item);
    } else {
      const kept = appMapRefusals[existingIndex];
      const patch = {};
      if (!nonEmpty(kept.fix) && nonEmpty(item.fix)) patch.fix = item.fix;
      if (!nonEmpty(kept.reason) && nonEmpty(item.reason)) patch.reason = item.reason;
      if (Object.keys(patch).length) appMapRefusals[existingIndex] = { ...kept, ...patch };
    }
  }
  const coveredAppMaps = new Set(appMapRefusals.map(targetOf));
  for (const mapPath of applicableMaps) {
    if (!coveredAppMaps.has(mapPath) && [...rawAppMaps, ...reportAppMaps].some(item => item.path === mapPath && item.verdict === 'refused')) {
      appMapRefusals.push({ code: 'lint-refused', field: mapPath, path: mapPath, message: `${mapPath} was refused by complete lint.` });
    }
  }
  const mapEntries = mapPath => rawAppMaps.filter(item => item.path === mapPath);
  const appMapsPassed = !hasAppMaps || applicableMaps.every(mapPath => {
    const mapListed = mapEntries(mapPath);
    return mapListed.length === 1 && mapListed[0].verdict === 'passed';
  });
  const appMapNotChecked = hasAppMaps && applicableMaps.some(mapPath => mapEntries(mapPath).some(item => item.verdict === 'not-checked'));
  const notChecked = verdict === 'not-checked' || appMapNotChecked;
  // The prompts the test reaches: each step's entry prompt and its declared call targets.
  let draft = false, lazyPending = false, unlisted = false, reachedProblem = null;
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
      else if (state === 'missing' && prompt.lazy_interface_pending === true) {
        lazyPending = true;
        for (const dep of Array.isArray(prompt.dependencies) ? prompt.dependencies : []) {
          if (typeof dep === 'string' && (byPath.has(dep) || refusedPrompts.has(dep))) queue.push(dep);
        }
      }
      else if (state !== 'approved' && state !== 'draft') reachedProblem = problem(`interface-${typeof state === 'string' && state ? state : 'unapproved'}`,
        `${path} has no usable Runtime interface.`);
      else {
        draft ||= state === 'draft' && prompt.lazy_interface !== true;
        for (const call of objects(prompt.interface?.calls)) if (typeof call.target === 'string') queue.push(call.target);
        if (prompt.lazy_interface === true) {
          for (const dep of Array.isArray(prompt.dependencies) ? prompt.dependencies : []) {
            if (typeof dep === 'string' && (byPath.has(dep) || refusedPrompts.has(dep))) queue.push(dep);
          }
        }
      }
    }
  }
  const notRun = (reason, code = !complete || notChecked ? 'deadline' : 'no-server-verdict') => ({ state: 'not_run', code, retryable: false, reason, draft });
  if (own.some(item => refusals.includes(item))) return refused(own, { draft });
  if (reachedProblem) return refused([reachedProblem], { draft });
  if (appMapRefusals.length) return appMapRefused(appMapRefusals, { draft });
  if (verdict === 'refused') return refused(own.length ? own : [{ code: 'lint-refused', message: `${test} was refused by complete lint.` }], { draft });
  if (verdict === 'passed') {
    if (!appMapsPassed) return notRun(!complete || unlisted || notChecked ? 'lint did not finish' : 'lint gave no verdict for this app map');
    const compatibility = selectedCompatibility(answer, test, sourceFiles);
    if (compatibility.association === 'matched') {
      if (['invalid-source', 'unsupported-capability', 'missing-binding'].includes(compatibility.state)) {
        const rows = [...compatibility.reported.operations, ...compatibility.reported.edges].filter(row => row.verdict === compatibility.state);
        return refused(rows.length ? rows.map(row => ({ code: row.reason_code, path: row.selection.prompt_path,
          section: row.selection.step_id, message: `${row.verdict}: ${row.reason_code}` }))
          : [{ code: compatibility.state, message: compatibility.state }], { draft });
      }
      if (compatibility.state === 'supported' && compatibility.reported.complete) return { state: 'passed', draft };
      if (lazyPending && complete && !own.length && compatibility.state === 'unknown' && compatibility.reported?.complete === false) {
        return { state: 'passed', draft };
      }
    }
    return notRun(compatibility.issue ?? 'selected compatibility is unknown or incomplete', compatibility.issue ?? 'no-server-verdict');
  }
  // A job refusal refuses a selected test that has no verdict of its own.
  if (!listed.length && (answer.state === 'refused' || report?.verdict === 'refused' || refusals.length))
    return refused(refusals.length ? refusals : [{ code: 'lint-refused', message: 'The interpreter refused lint.' }], { draft });
  return notRun(!complete || unlisted || notChecked ? 'lint did not finish' : !appMapsPassed ? 'lint gave no verdict for this app map' : 'lint gave no verdict for this test');
}

const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const fields = (value, names) => object(value) && Object.keys(value).length === names.length && names.every(name => Object.hasOwn(value, name));
const text = value => typeof value === 'string' && value.length <= 4096;
const hex = (value, length) => typeof value === 'string' && new RegExp(`^[0-9a-f]{${length}}$`).test(value);
const verdicts = ['invalid-source', 'unsupported-capability', 'missing-binding', 'unknown', 'supported'];
const reasons = { supported: 'supported', 'engine-build-unknown': 'unknown', 'source-mismatch': 'invalid-source',
  'source-admission-refused': 'invalid-source', 'retained-attachment-unsupported': 'unsupported-capability',
  'retained-mutation-unsupported': 'unsupported-capability', 'runtime-mode-unsupported': 'unsupported-capability',
  'binding-missing': 'missing-binding', 'analysis-unavailable': 'unknown', 'requirement-uninspectable': 'unknown' };
const canonical = value => Array.isArray(value) ? `[${value.map(canonical).join(',')}]` : object(value)
  ? `{${Object.keys(value).sort().map(key => `${JSON.stringify(key)}:${canonical(value[key])}`).join(',')}}` : JSON.stringify(value);
const diagnostic = value => fields(value, ['code', 'path', 'section']) && text(value.code) && text(value.section) && (value.path === null || text(value.path));
const sourceShape = value => fields(value, ['scenario_sha256', 'closure_sha256', 'files']) && hex(value.scenario_sha256, 64)
  && hex(value.closure_sha256, 64) && Array.isArray(value.files) && value.files.length <= 10000
  && value.files.every((file, index, files) => fields(file, ['path', 'sha256']) && text(file.path) && hex(file.sha256, 64)
    && (!index || files[index - 1].path < file.path));

function capabilityRow(row, edge) {
  if (!fields(row, ['selection', 'feature', 'binding_kind', 'resource_mode', 'evaluator_mode', 'execution_mode', 'verdict', 'reason_code'])
    || !fields(row.selection, ['step_id', 'node_id', 'prompt_path', 'operation', ...(edge ? ['edge'] : [])])
    || !['step_id', 'node_id', 'prompt_path', 'operation'].every(key => text(row.selection[key]) && row.selection[key].length)
    || !['ordinary', 'constructor-retained-read', 'method-attachment', 'retained-mutation', 'uninspectable'].includes(row.feature)
    || !['none', 'internal', 'fixture', 'prompt', 'live', 'missing'].includes(row.binding_kind)
    || !['simulated', 'live'].includes(row.resource_mode) || !text(row.evaluator_mode)
    || !['ordinary', 'checkpoint', 'resume'].includes(row.execution_mode)
    || !text(row.reason_code) || !Object.hasOwn(reasons, row.reason_code) || reasons[row.reason_code] !== row.verdict) return false;
  if (!edge) return row.binding_kind === 'none';
  const e = row.selection.edge;
  if (!fields(e, ['edge_id', 'kind', 'call_operation', 'target_node_id', 'target_path', 'target_operation', 'resource_operation'])
    || !Object.values(e).every(text) || !e.edge_id || !e.call_operation || !['internal', 'resource'].includes(e.kind)
    || row.binding_kind === 'none') return false;
  const targets = [e.target_node_id, e.target_path, e.target_operation];
  return (targets.every(Boolean) || targets.every(value => value === '')) && (e.kind === 'internal'
    ? targets.every(Boolean) && e.resource_operation === '' && row.binding_kind === 'internal'
    : !!e.resource_operation && row.binding_kind !== 'internal');
}

function reportShape(report) {
  if (!fields(report, ['schema_version', 'capability_version', 'engine_build', 'source', 'complete', 'verdict', 'operations', 'edges', 'diagnostics', 'provider_calls', 'resource_calls'])
    || report.schema_version !== 'prompt-runtime.program-capabilities.v1' || !text(report.capability_version) || !text(report.engine_build)
    || typeof report.complete !== 'boolean' || !verdicts.includes(report.verdict) || report.provider_calls !== 0 || report.resource_calls !== 0
    || report.source !== null && !sourceShape(report.source)
    || !Array.isArray(report.operations) || !Array.isArray(report.edges) || report.operations.length + report.edges.length > 10000
    || !Array.isArray(report.diagnostics) || report.diagnostics.length > 10002 || !report.diagnostics.every(diagnostic)
    || !report.operations.every(row => capabilityRow(row, false)) || !report.edges.every(row => capabilityRow(row, true))
    || report.complete && (!report.source || !report.operations.length)) return false;
  return true;
}

function reportConsistent(report) {
  const nodes = new Map(report.operations.map(row => [canonical([row.selection.step_id, row.selection.node_id]), row.selection]));
  for (const row of report.edges) {
    const s = row.selection, e = s.edge;
    for (const [node, path, operation] of [[s.node_id, s.prompt_path, s.operation], [e.target_node_id, e.target_path, e.target_operation]]) {
      const target = nodes.get(canonical([s.step_id, node]));
      if (node && !target && report.complete || target && (target.prompt_path !== path || target.operation !== operation)) return false;
    }
  }
  // Validate reported aggregate consistency, without discovering features or applying the engine's mode policy.
  const classes = new Set([...report.operations, ...report.edges].map(row => row.verdict));
  if (!report.complete) classes.add('unknown');
  if (report.diagnostics.some(item => item.code === 'source-mismatch')) classes.add('invalid-source');
  if (report.engine_build === 'unknown') return report.capability_version === 'unknown' && report.verdict === 'unknown'
    && [...report.operations, ...report.edges].every(row => row.verdict === 'unknown' && row.reason_code === 'engine-build-unknown');
  return report.verdict === (verdicts.find(verdict => classes.has(verdict)) ?? 'unknown');
}

function selectedCompatibility(answer, test, sourceFiles) {
  const result = answer?.result, top = objects(result?.capabilities).filter(item => item.path === test).map(item => item.report);
  const legacy = objects(result?.report?.lint?.tests).filter(item => item.path === test && Object.hasOwn(item, 'capabilities')).map(item => item.capabilities);
  const reports = [...top, ...legacy], report = reports[0];
  const unknown = (issue, reported = null, association = 'unknown') => ({ reported, state: 'unknown', association, issue });
  const unavailable = value => {
    const metadata = object(value) ? Object.fromEntries(['schema_version', 'engine_build', 'capability_version'].filter(key => text(value[key])).map(key => [key, value[key]])) : {};
    if (typeof value?.complete === 'boolean') metadata.complete = value.complete;
    if (sourceShape(value?.source)) metadata.source = structuredClone(value.source);
    if (Array.isArray(value?.diagnostics)) metadata.diagnostics = structuredClone(value.diagnostics.filter(diagnostic).slice(0, 10002));
    return unknown('capability-report-unavailable', Object.keys(metadata).length ? metadata : null);
  };
  if (!reports.length) return unavailable(null);
  // Validate the closed, fixed-depth wire shape before cloning or comparing it.
  // Unexpected fields and malformed identities can contain arbitrarily nested JSON.
  const malformed = reports.findIndex(value => !reportShape(value));
  if (malformed !== -1) return unavailable(reports[malformed]);
  if (reports.some(value => canonical(value) !== canonical(report))) return unknown('capability-report-conflict');
  for (const [name, key] of [['operations', row => [row.selection.step_id, row.selection.node_id]], ['edges', row => [row.selection.step_id, row.selection.edge.edge_id]]]) {
    if (new Set(report[name].map(row => canonical(key(row)))).size !== report[name].length)
      return unknown('capability-report-conflict');
  }
  if (!reportConsistent(report)) return unavailable(report);
  const reported = structuredClone(report);
  const knownBuild = hex(report.engine_build, 40), knownJob = hex(answer?.engine_sha, 40);
  let mismatch = knownBuild && knownJob && report.engine_build !== answer.engine_sha;
  mismatch ||= knownBuild && report.capability_version !== `program-capabilities.v1@${report.engine_build}`;
  const filesValid = Array.isArray(sourceFiles) && sourceFiles.every(file => object(file) && text(file.path) && hex(file.sha256, 64))
    && new Set(sourceFiles.map(file => file.path)).size === sourceFiles.length;
  const files = new Map(filesValid ? sourceFiles.map(file => [file.path, file.sha256]) : []);
  if (filesValid && report.source) {
    mismatch ||= files.has(test) && report.source.scenario_sha256 !== files.get(test);
    mismatch ||= report.source.files.some(file => !files.has(file.path) || files.get(file.path) !== file.sha256);
  }
  if (mismatch) return unknown('capability-association-mismatch', reported, 'mismatch');
  if (!knownBuild || !knownJob || !filesValid || !files.has(test) || !report.source)
    return unknown('capability-association-unavailable', reported);
  return { reported, state: report.verdict, association: 'matched', issue: null };
}

function progressFrom(value) {
  const progress = {};
  for (const key of ['steps_done', 'steps_total', 'calls_settled', 'calls_open']) if (count(value?.[key])) progress[key] = value[key];
  if (Number.isSafeInteger(value?.step) && value.step >= 1 || typeof value?.step === 'string' && value.step.trim()) progress.step = value.step;
  return progress;
}

// An open call has no settled result yet; it can stay open until the check ends, so it is never shown as live traffic.
const callWords = (settled, open) => [...(count(settled) ? [`${settled} AI call${settled === 1 ? '' : 's'} so far`] : []), ...(open > 0 ? [`${open} not yet settled`] : [])];

// Module function: the words for an outcome, or for a saved row that carries its outcome fields.
export function outcomeText(outcome) {
  const { state, reason } = resultOutcome(outcome);
  const p = outcome.progress ?? {};
  const number = typeof p.step === 'number' ? p.step : count(p.steps_done) && count(p.steps_total) && p.steps_done < p.steps_total ? p.steps_done + 1 : null;
  const step = number ? `step ${number}${count(p.steps_total) ? ` of ${p.steps_total}` : ''}` : typeof p.step === 'string' ? p.step : null;
  return [state + (reason ? ` (${reason.code})` : ''), ...(count(outcome.ahead) ? [`${outcome.ahead} ahead`] : []),
    ...(step ? [step + (number && typeof p.step === 'string' ? ` (${p.step})` : '')] : []), ...callWords(p.calls_settled, p.calls_open)].join(' · ');
}

export const hasProgress = outcome => ['running', 'sent'].includes(outcome.state) && Object.keys(outcome.progress ?? {}).length > 0;

// Module function: one progress fragment for a group of rows; null when no row has server progress.
// One row keeps its step; several rows add up the counts they report.
export function progressText(outcomes) {
  const moving = outcomes.filter(hasProgress);
  if (moving.length < 2) return moving.length ? outcomeText(moving[0]) : null;
  const reported = key => moving.filter(outcome => count(outcome.progress[key]));
  const sum = key => reported(key).reduce((total, outcome) => total + outcome.progress[key], 0);
  return ['sent (awaiting-server-verdict)', ...callWords(reported('calls_settled').length ? sum('calls_settled') : undefined, sum('calls_open'))].join(' · ');
}

export const outcomeDone = outcome => TERMINAL.has(outcome.state) || outcome.state === 'not run';

// Module function: the state that decides a group's result.
export function outcomeOverall(outcomes, { interrupted = false, lintUnknown = false } = {}) {
  if (interrupted || lintUnknown || !outcomes.length || outcomes.some(outcome => outcome.state === 'partial')) return 'unknown';
  const present = new Set(outcomes.map(outcome => outcomeDone(outcome) ? outcome.state === 'not run' ? 'not_run' : outcome.state : 'unknown'));
  return DECIDES.find(state => present.has(state));
}

// Public aggregate keeps the deciding row's explanation, not a raw job's label.
export function resultOverall(outcomes, options) {
  const state = outcomeOverall(outcomes, options);
  const row = outcomes.find(row => (outcomeDone(row) ? row.state === 'not run' ? 'not_run' : row.state : 'unknown') === state);
  return resultOutcome(row ?? { state });
}
