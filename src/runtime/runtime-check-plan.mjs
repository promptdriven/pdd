// Generated from prompts/cli/runtime-check-plan.prompt.md (sha256: 93de87a46fe0fbd788029c90585e8fa15df6ceb4e4834438ee93238f90c123f8).
import { spawnSync } from 'node:child_process';
import { isAbsolute, posix } from 'node:path';
import { captureSource, readPrompt, sourceFilePort, promptMarkdownTargets } from './runtime-preflight.mjs';
import { resultOutcome } from './runtime-outcome.mjs';
import { allowsRuntimePath, loadRuntimeWorkspace } from './runtime-workspace.mjs';

const HEAD = 4096, LINE = 1100;
const HEADER = /^\s*(?:\/\/+|#+|--|;+|\/\*+|\*+|<!--|"""|''')?\s*Generated from (\S+\.prompt\.md)(?: \(sha256: ([a-f0-9]{64})\))?\.?\s*(?:\*\/|-->|"""|''')?\s*$/;
const bytesOf = content => typeof content === 'string' ? Buffer.from(content, 'utf8') : content;
const decode = (content, limit) => content ? new TextDecoder().decode(bytesOf(content).subarray(0, limit)) : '';
const canonicalHeaderPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');
export function defaultHeaderPrompts(content) {
  if (!content) return [];
  const bytes = bytesOf(content), lines = decode(bytes, HEAD).split(/\r?\n/), seen = new Set();
  if (bytes.length > HEAD) lines.pop();
  for (const line of lines.filter(line => line.length <= LINE)) {
    const match = HEADER.exec(line);
    if (match && canonicalHeaderPath(match[1])) seen.add(match[1]);
  }
  return [...seen];
}

const sorted = values => [...new Set(values)].sort();
const unique = values => [...new Set(values)];
const gitRead = (root, args) => {
  const reply = spawnSync('git', args, { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (reply.status !== 0) throw Error('change scope unavailable');
  return reply.stdout;
};

export function buildCheckPlan({ root, found, selected, rows = [], full, base = 'HEAD', affected = false, allowMissingInterfaces = false, maxCalls = null, maxTotalCalls = null, singleAttempt = false, unresolvedReservations = null }, ports = {}) {
  const git = args => (ports.git ?? gitRead)(root, args);
  const readHeaders = ports.headerPrompts ?? defaultHeaderPrompts;
  let changed = null;
  try {
    changed = sorted([...git(['diff', '--name-only', '-z', '--no-renames', base, '--']).split('\0'),
      ...git(['ls-files', '--others', '--exclude-standard', '-z']).split('\0')].filter(Boolean));
  } catch { /* Unknown changes require conservative target coverage. */ }
  const workspace = found.workspace ?? loadRuntimeWorkspace({root});
  const source = sourceFilePort(root, found.visible, workspace);
  const permitted = path => allowsRuntimePath(workspace,path) && !(full && (found.excludedFixtureProjects ?? []).some(prefix=>path === prefix || path.startsWith(`${prefix}/`)));
  const owners = new Map(), unknownOwners = new Set();
  let deleted = new Set(), deletionsUnavailable = false;
  if (changed?.some(permitted)) {
    try { deleted = new Set(git(['diff', '--name-only', '-z', '--no-renames', '--diff-filter=D', base, '--']).split('\0').filter(Boolean)); }
    catch { deletionsUnavailable = true; }
  }
  const own = (prompt, path) => {
    if (!found.visible.has(prompt)) return;
    owners.set(prompt, [...(owners.get(prompt) ?? []), path]);
    unknownOwners.delete(path);
  };
  for (const path of changed ?? []) {
    if (!permitted(path)) continue;
    if (deleted.has(path)) unknownOwners.add(path);
    else if (!found.visible.has(path)) continue;
    try {
      // Validate the permitted source path even when its working file is absent.
      if (deleted.has(path)) source.stat({path});
      const content = deleted.has(path) ? git(['show', `${base}:${path}`]) : source.read({path}).content;
      for (const prompt of readHeaders(content)) own(prompt, path);
    } catch { /* Unproved deleted ownership keeps target coverage conservative. */ }
  }
  if (changed?.length && found.visible.has('pdd-bindings.json')) {
    try {
      const inventory = JSON.parse(source.read({path:'pdd-bindings.json'}).content);
      for (const item of inventory.modules ?? []) if (changed.includes(item.module) && permitted(item.module) && typeof item.prompt === 'string') own(item.prompt, item.module);
    } catch { /* The binding owner retains inventory validation. */ }
  }
  const prerequisites = [], seenProblems = new Set(), prompts = new Map();
  const problem = (code, path, field) => {
    const key = `${code}\0${path}\0${field}`;
    if (!seenProblems.has(key)) { seenProblems.add(key); prerequisites.push({code,path,field}); }
  };
  const cost = (path, stack = new Set(), proseOnly = false) => {
    if (stack.has(path)) { if (!proseOnly) problem('recursive-call-bound', path, '/calls'); return 0; }
    let prompt = prompts.get(path);
    if (!prompt) {
      try { prompt = readPrompt(root, found.visible, path, found.workspace); }
      catch { prompt = {error:'interface-unavailable'}; }
      prompts.set(path, prompt);
    }
    const iface = prompt.interface;
    if (!iface) {
      if (allowMissingInterfaces && prompt.error === 'interface-missing') {
        const next = new Set([...stack, path]);
        let count = 1;
        for (const target of promptMarkdownTargets(prompt.text, path, found.visible)) count += cost(target, next, true);
        return count;
      }
      problem(prompt.error ?? 'interface-missing', path, '/interface');
      return 0;
    }
    if (iface.kind === 'native-only') return 0;
    if (!Number.isSafeInteger(iface.limits?.max_model_calls) || iface.limits.max_model_calls < 1)
      problem('undefined-call-bound', path, '/limits/max_model_calls');
    const next = new Set([...stack, path]);
    let count = 1 + (Array.isArray(iface.resources) ? iface.resources : []).reduce((sum, resource) => sum + (Array.isArray(resource.operations) ? resource.operations.length : 0), 0);
    for (const [index, call] of (Array.isArray(iface.calls) ? iface.calls : []).entries()) {
      if (!Number.isSafeInteger(call?.max_calls) || call.max_calls < 1) problem('undefined-call-bound', path, `/calls/${index}/max_calls`);
      const nested = cost(call?.target, next);
      if (Number.isSafeInteger(call?.max_calls)) count += call.max_calls * nested;
    }
    return count;
  };
  const groups = new Map();
  for (const test of selected) {
    const key = test.storyPath ?? test.path;
    if (!groups.has(key)) groups.set(key, []);
    groups.get(key).push(test);
  }
  const capture = ports.capture ?? ((r, opts) => captureSource(r, opts, ports));
  let footprints = new Map();
  const targets = new Map();
  const rememberTargets = captured => {
    for (const file of captured.files ?? []) if (file.target) targets.set(file.path,file.target);
    return captured;
  };
  const captureExtra = allowMissingInterfaces ? { allowMissingInterfaces: true } : {};
  try {
    const captured = rememberTargets(capture(root,{tests:selected.map(test=>test.path),appMap:null,excludeFixtureProjects:full,...captureExtra}));
    footprints = new Map((captured.stories ?? []).map(story=>[story.story_path,story]));
  } catch (error) { if (error?.unboundPort) throw error; /* Keep a broken Story from hiding other Stories' closures. */ }
  const classified = [...groups].map(([story_path, tests]) => {
    let closure = [], unavailable = false;
    const footprint = footprints.get(story_path);
    try {
      if (footprint?.unavailable) unavailable = true;
      else closure = sorted((footprint?.files ?? rememberTargets(capture(root, {tests:tests.map(test=>test.path),appMap:null,excludeFixtureProjects:full,...captureExtra})).files).map(file=>file.path));
    }
    catch (error) { if (error?.unboundPort) throw error; unavailable = true; }
    return {story_path,tests,closure,unavailable};
  });
  let conservative = '';
  if (affected && changed?.length) {
    if (changed.some(path=>['pdd-source.json','pdd-workspace.json','pdd-bindings.json'].includes(path)))
      conservative = 'global source, workspace or binding inventory changed; conservative selection';
    if (classified.some(story=>story.unavailable)) conservative ||= 'dependency closure unavailable; conservative selection';

    // Query only permitted names. The tree establishes whether a working path is
    // new, and identifies old link aliases without following their targets.
    const paths = sorted([...changed.filter(permitted), ...classified.flatMap(story=>story.closure).filter(permitted)]);
    const old = new Map();
    try {
      if (paths.length) for (const record of git(['ls-tree','-z',base,'--',...paths]).split('\0').filter(Boolean)) {
        const match = /^(\d+) (?:blob|tree|commit) [a-f0-9]+\t([\s\S]+)$/.exec(record);
        if (!match) throw Error('invalid tree metadata');
        if (permitted(match[2])) old.set(match[2],match[1]);
      }
    } catch { conservative ||= 'old ownership or safe-link metadata unavailable; conservative selection'; }
    const implementation = path => /(?:^|\/)(?:src|lib|bin|app)\//.test(path)
      || !/\.(?:md|txt|rst|csv|svg|png|jpe?g|gif|webp|ico|woff2?|ttf|json)$/i.test(path)
      || [...owners.values()].some(paths=>paths.includes(path));
    let bindings = [];
    if (found.visible.has('pdd-bindings.json')) {
      try {
        const inventory = JSON.parse(source.read({path:'pdd-bindings.json'}).content);
        if (inventory.schema_version !== 'pdd.bindings.v1' || !Array.isArray(inventory.modules)) throw Error('invalid binding inventory');
        bindings = inventory.modules;
      } catch { conservative ||= 'binding ownership unavailable; conservative selection'; }
    }
    for (const path of changed.filter(permitted)) {
      const bound = bindings.filter(item=>item?.module === path && typeof item.prompt === 'string').map(item=>item.prompt);
      const inspectOwners = content => {
        const named = unique([...bound,...readHeaders(content)]);
        if (!named.length || named.some(prompt=>!permitted(prompt) || !found.visible.has(prompt)))
          conservative ||= `${deleted.has(path)?'deleted':'implementation'} ownership unavailable: ${path}; conservative selection`;
        for (const prompt of named) if (permitted(prompt)) own(prompt,path);
      };
      try {
        // Headers in either revision establish ownership, including assets whose
        // current header was removed. Apply permission before either read.
        const current = deleted.has(path) ? null : source.read({path}).content;
        const previous = old.has(path) ? git(['show',`${base}:${path}`]) : null;
        if (!implementation(path) && !bound.length && !readHeaders(previous).length && !readHeaders(current).length) continue;
        if (current !== null) inspectOwners(current);
        if (previous !== null) inspectOwners(previous);
        else if (deleted.has(path)) conservative ||= `deleted ownership unavailable: ${path}; conservative selection`;
      } catch { conservative ||= `${deleted.has(path)?'deleted':'old/new implementation'} ownership unavailable: ${path}; conservative selection`; }
    }
    // Capture records the final safe target while retaining the authored alias.
    // Old aliases must also be known: a changed target may otherwise disappear
    // from the current closure after a link is redirected or removed.
    for (const [path,mode] of old) if (mode === '120000') {
      try {
        const raw = git(['show',`${base}:${path}`]);
        const target = raw.startsWith('/') ? null : posix.normalize(posix.join(posix.dirname(path),raw));
        if (!target || target.startsWith('../') || target.includes('\\') || !permitted(target)) throw Error('unavailable target');
        if (!targets.has(path) || targets.get(path) !== target) throw Error('unproved old/new relationship');
      } catch { conservative ||= 'old/new safe-link target relationship unavailable; conservative selection'; }
    }
    for (const [path,target] of targets) if (!permitted(path) || !permitted(target) || !old.has(path)
      || changed.some(change=>path.startsWith(`${change}/`)))
      conservative ||= 'safe-link target relationship unavailable; conservative selection';
  }
  const stories = classified.map(({story_path,tests,closure,unavailable}) => {
    const affectedPaths = sorted((changed ?? []).filter(path => allowsRuntimePath(workspace,path) && (closure.includes(path) || tests.some(test=>test.path === path || test.storyPath === path)
      || (affected && closure.some(alias=>targets.get(alias) === path))))
      .concat(closure.flatMap(path=>owners.get(path) ?? [])));
    const uncertainOwner = deletionsUnavailable || unknownOwners.size > 0;
    const target = !full || changed === null || !changed.length || unavailable || uncertainOwner || !!conservative || affectedPaths.length > 0 || changed.includes('pdd-bindings.json');
    return {story_path,tests:tests.map(test=>test.path),role:target?'target':'baseline',
      reason:!full?'explicit selection':unavailable?'dependency closure unavailable; conservative selection':changed === null?'change scope unavailable; conservative selection':!changed.length?'no changed paths; conservative selection':uncertainOwner?'deleted ownership unavailable; conservative selection':conservative || (affectedPaths.length?`changed paths: ${affectedPaths.join(', ')}`:target?'binding inventory changed':'unrelated to known changes; required by full batch; pre-change result unknown'),
      affected_paths:affectedPaths,dependency_closure:closure};
  });
  if (!stories.some(story=>story.role === 'target')) for (const story of stories) {
    story.role = 'target'; story.reason = 'no affected Story established; conservative selection';
  }
  let estimated = 0;
  const dispatched = new Set(selectCheckTests({stories},{affected}).tests), budgetRows = [];
  for (const row of rows.filter(row=>!affected || dispatched.has(row.test))) {
    // Inspect interfaces even when a different local rule won preflight precedence.
    const count = (row.steps ?? []).reduce((sum, step) => sum + cost(step?.entry_path), 0);
    if (row.state !== 'ready') continue;
    const validBound = Number.isSafeInteger(row.max_calls) && row.max_calls >= 1;
    if (!validBound) problem('undefined-call-bound',row.test,'/max_calls');
    else estimated += Math.min(row.max_calls, count);
    budgetRows.push({ test: row.test, max_calls: validBound ? row.max_calls : 0, restart_used: false, attempts: [] });
  }
  const prior = {
    count: Number.isSafeInteger(unresolvedReservations?.count) && unresolvedReservations.count >= 0 ? unresolvedReservations.count : 0,
    reserved_calls: Number.isSafeInteger(unresolvedReservations?.reserved_calls) && unresolvedReservations.reserved_calls >= 0 ? unresolvedReservations.reserved_calls : 0,
    batches: Array.isArray(unresolvedReservations?.batches) ? [...unresolvedReservations.batches] : []
  };
  const evaluated = evaluateCheckBudget({ max_total_calls: maxTotalCalls, single_attempt: singleAttempt,
    unresolved_prior_reservations: { count: prior.count, reserved_calls: prior.reserved_calls }, rows: budgetRows, candidate: null });
  const call_policy = {
    max_calls_override: maxCalls ?? null,
    per_request_max_calls: evaluated.plan.per_request_caps,
    max_total_calls: maxTotalCalls ?? null,
    restart_replacement: evaluated.plan.restart_replacement,
    unbounded_maximum: prerequisites.length ? null : evaluated.plan.unbounded_maximum,
    planned_maximum: prerequisites.length ? null : evaluated.plan.planned_maximum,
    unresolved_reservations: prior,
    accounting_scope: evaluated.plan.accounting_scope
  };
  return {schema_version:'pdd.check-plan.v1',full,base,changed_paths:changed,stories,
    calls:{estimated:prerequisites.length?null:estimated,maximum:prerequisites.length?null:evaluated.plan.planned_maximum,check_requests:evaluated.plan.planned_check_requests,lint_model_calls:0},
    call_policy,prerequisites};
}

export function evaluateCheckBudget({ max_total_calls = null, single_attempt = false, unresolved_prior_reservations = { count: 0, reserved_calls: 0 }, rows = [], candidate = null } = {}) {
  const multiplier = single_attempt ? 1 : 2;
  const per_request_caps = [...new Set(rows.map(row => row.max_calls).filter(value => Number.isSafeInteger(value) && value >= 1))].sort((a, b) => a - b);
  const unbounded_maximum = rows.reduce((sum, row) => sum + (Number.isSafeInteger(row.max_calls) && row.max_calls >= 1 ? row.max_calls * multiplier : 0), 0);
  const planned_maximum = max_total_calls === null ? unbounded_maximum : Math.min(unbounded_maximum, max_total_calls);
  const plan = {
    per_request_caps,
    max_total_calls,
    restart_replacement: single_attempt ? 'disabled' : 'at-most-one',
    unbounded_maximum,
    planned_maximum,
    planned_check_requests: rows.length * multiplier,
    unresolved_prior_reservations: {
      count: unresolved_prior_reservations?.count ?? 0,
      reserved_calls: unresolved_prior_reservations?.reserved_calls ?? 0
    },
    accounting_scope: 'logical-interpreter-calls'
  };
  let consumed_known = 0, unresolved_reserved = 0, in_flight_reserved = 0;
  for (const row of rows) {
    for (const attempt of row.attempts ?? []) {
      const floor = Math.max(attempt.requested_max_calls, (attempt.known_calls ?? 0) + (attempt.unknown_calls ?? 0));
      if (attempt.status === 'capacity_refused_zero') continue;
      if (attempt.status === 'settled') consumed_known += attempt.known_calls;
      else if (attempt.status === 'in_flight') in_flight_reserved += floor;
      else unresolved_reserved += floor;
    }
  }
  const committed_calls = consumed_known + unresolved_reserved + in_flight_reserved;
  const remaining_calls = max_total_calls === null ? null : Math.max(0, max_total_calls - committed_calls);
  const accounting = { consumed_known, unresolved_reserved, in_flight_reserved, committed_calls, remaining_calls };
  let decision = null;
  if (candidate !== null && candidate !== undefined) {
    if (candidate.kind === 'restart-replacement' && candidate.prior_reason_code !== 'service-restarted') {
      decision = { action: 'refuse-replacement', reason_code: 'not-service-restarted', effective_max_calls: 0, retain_prior_uncertainty: true };
    } else if (candidate.kind === 'restart-replacement' && candidate.restart_used) {
      decision = { action: 'refuse-replacement', reason_code: 'restart-limit-reached', effective_max_calls: 0, retain_prior_uncertainty: true };
    } else if (candidate.kind === 'restart-replacement' && single_attempt) {
      decision = { action: 'refuse-replacement', reason_code: 'restart-replacement-disabled', effective_max_calls: 0, retain_prior_uncertainty: true };
    } else {
      const retain_prior_uncertainty = candidate.kind === 'restart-replacement';
      if (max_total_calls === null || remaining_calls >= candidate.requested_max_calls) {
        decision = { action: 'send', reason_code: 'within-budget', effective_max_calls: candidate.requested_max_calls, retain_prior_uncertainty };
      } else if (in_flight_reserved > 0 && Math.max(0, max_total_calls - (consumed_known + unresolved_reserved)) > remaining_calls) {
        decision = { action: 'wait', reason_code: 'awaiting-in-flight-settlement', effective_max_calls: 0, retain_prior_uncertainty };
      } else if (remaining_calls >= 1) {
        decision = { action: 'send', reason_code: 'clamped-to-remaining-budget', effective_max_calls: remaining_calls, retain_prior_uncertainty };
      } else {
        decision = { action: 'block', reason_code: 'call-budget-exhausted', effective_max_calls: 0, retain_prior_uncertainty };
      }
    }
  }
  return { plan, accounting, decision };
}

export function selectCheckTests(plan, {affected = false} = {}) {
  const all = unique(plan.stories.flatMap(story=>story.tests));
  if (!affected) return {mode:'full',tests:all,baseline_tests:[]};
  const tests = unique(plan.stories.filter(story=>story.role === 'target').flatMap(story=>story.tests));
  if (!tests.length) return {mode:'affected',tests:all,baseline_tests:[]};
  return {mode:'affected',tests,baseline_tests:unique(plan.stories.filter(story=>story.role === 'baseline').flatMap(story=>story.tests))};
}

export function baselineReport({plan,observations,availability,warnings}) {
  const tests = unique(plan.stories.filter(story=>story.role === 'baseline').flatMap(story=>story.tests));
  const admitted = observations.filter(observation=>tests.includes(observation.test));
  const observed = new Set(admitted.map(observation=>observation.test));
  return {schema_version:'pdd.baseline-report.v1',availability,tests,observations:admitted,
    missing_tests:tests.filter(test=>!observed.has(test)),warnings:[...warnings]};
}

export function checkPlanResults(plan, rows) {
  if (plan?.schema_version !== 'pdd.check-plan.v1' || !Array.isArray(plan.stories)
    || plan.stories.some(story=>!story || !['target','baseline'].includes(story.role) || !Array.isArray(story.tests)
      || story.tests.some(path=>typeof path !== 'string'))) return null;
  const group = role => {
    const tests = sorted(plan.stories.filter(story=>story.role === role).flatMap(story=>story.tests));
    const state = test => {
      const matches = rows.filter(row=>row.test === test).map(row=>resultOutcome(row).state);
      return matches.length && matches.every(value=>value === 'passed') ? 'passed' : matches.includes('failed') ? 'failed' : 'not_run';
    };
    const passed = tests.filter(test=>state(test) === 'passed'), failures = tests.filter(test=>state(test) === 'failed'), unresolved = tests.filter(test=>state(test) === 'not_run');
    return {tests,passed,failures,unresolved,state:!tests.length?'none':failures.length?'failed':unresolved.length?'not_run':'passed'};
  };
  const target = group('target'), baseline = group('baseline');
  const guidance = plan.full && plan.prerequisites?.length ? `Repair local check-plan prerequisites: ${plan.prerequisites.map(item=>`${item.code}: ${item.path} ${item.field}`).join('; ')}. Repair the named interface or call bound, then run a fresh pdd test check. No checks were sent; saved reads and retries cannot repair these local prerequisites.`
    : target.failures.length ? `Repair target failures: ${target.failures.join(', ')}. Keep baseline results separate.`
    : target.unresolved.length ? 'Read the saved batch for unresolved target checks; do not resend uncertain work.'
    : baseline.failures.length || baseline.unresolved.length ? `Target checks passed. Hand off baseline obligations: ${[...baseline.failures,...baseline.unresolved].join(', ')}. Keep the failed or incomplete full batch and required full-pass gates. Do not rerun unchanged target checks or change their expectations to repair baseline work. Read the saved batch for unresolved checks; baseline age and ownership are not proved.`
    : 'Selected checks passed; required repository gates still apply.';
  return {target,baseline,guidance};
}

export function checkPlanLines(plan) {
  const policy = plan.call_policy, disabled = policy?.restart_replacement === 'disabled';
  const capNote = policy?.max_total_calls != null ? `${disabled ? ', ' : ' ('}capped by --max-total-calls ${policy.max_total_calls}${disabled ? '' : ')'}` : '';
  const callsLine = disabled
    ? `  Interpreter calls: about ${plan.calls.estimated ?? 'unknown'}; at most ${plan.calls.maximum ?? 'unknown'} (restart replacement disabled${capNote}); at most ${plan.calls.check_requests} Check requests; lint: 0 model calls.`
    : `  Interpreter calls: about ${plan.calls.estimated ?? 'unknown'}; at most ${plan.calls.maximum ?? 'unknown'} including one restart replacement per test${capNote}; at most ${plan.calls.check_requests} Check requests; lint: 0 model calls.`;
  const policyLines = policy ? [(() => {
    const caps = policy.per_request_max_calls?.length ? policy.per_request_max_calls.join(', ') : 'none';
    const ceiling = policy.max_total_calls != null ? `${policy.max_total_calls} (--max-total-calls)` : 'unbounded';
    const replacement = disabled ? 'disabled' : 'at most 1 per test on confirmed service-restarted';
    const prior = policy.unresolved_reservations;
    const priorText = prior?.count ? `${prior.count} (${prior.reserved_calls} calls reserved${prior.batches?.length ? ` in ${prior.batches.join(', ')}` : ''})` : '0';
    return `  Call policy: per-request cap ${caps}; invocation ceiling ${ceiling}; restart replacement ${replacement}; unresolved prior reservations ${priorText} (logical interpreter call limits; not dollar, token or provider-attempt guarantees).`;
  })()] : [];
  return ['Check plan:', ...plan.stories.flatMap(story=>[
    `  ${story.role}: ${story.story_path} (${story.tests.join(', ')}); ${story.reason}`,
    `    dependency closure: ${story.dependency_closure.join(', ') || 'unavailable'}`]),
    callsLine, ...policyLines,
    ...plan.prerequisites.map(item=>`  prerequisite: ${item.code}: ${item.path} ${item.field}`)];
}

export function checkPlanResultLines(result) {
  const counts = group => [`${group.passed.length} passed`,...(group.failures.length?[`${group.failures.length} failed`]:[]),
    ...(group.unresolved.length?[`${group.unresolved.length} unresolved`]:[])].join(', ');
  return result ? [`Target checks: ${result.target.state}; ${counts(result.target)}.`,
    `Baseline obligations: ${result.baseline.state}; ${counts(result.baseline)}.`, result.guidance] : [];
}
