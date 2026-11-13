// Generated from prompts/cli/runtime-check-plan.prompt.md (sha256: fd2ee080527673f163544e955f736f80f0c4bc183aee6009d9d7e8da6f0d51e4).
import { spawnSync } from 'node:child_process';
import { posix } from 'node:path';
import { captureSource, readPrompt, sourceFilePort, promptMarkdownTargets } from './runtime-preflight.mjs';
import { resultOutcome } from './runtime-outcome.mjs';
import { headerPrompts } from './file-owner.mjs';
import { allowsRuntimePath, loadRuntimeWorkspace } from './runtime-workspace.mjs';

const sorted = values => [...new Set(values)].sort();
const unique = values => [...new Set(values)];
const gitRead = (root, args) => {
  const reply = spawnSync('git', args, { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (reply.status !== 0) throw Error('change scope unavailable');
  return reply.stdout;
};

export function buildCheckPlan({ root, found, selected, rows = [], full, base = 'HEAD', affected = false, allowMissingInterfaces = false }, ports = {}) {
  const git = args => (ports.git ?? gitRead)(root, args);
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
      for (const prompt of headerPrompts(content)) own(prompt, path);
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
  const capture = ports.capture ?? captureSource;
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
  } catch { /* Keep a broken Story from hiding other Stories' closures. */ }
  const classified = [...groups].map(([story_path, tests]) => {
    let closure = [], unavailable = false;
    const footprint = footprints.get(story_path);
    try {
      if (footprint?.unavailable) unavailable = true;
      else closure = sorted((footprint?.files ?? rememberTargets(capture(root, {tests:tests.map(test=>test.path),appMap:null,excludeFixtureProjects:full,...captureExtra})).files).map(file=>file.path));
    }
    catch { unavailable = true; }
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
        const named = unique([...bound,...headerPrompts(content)]);
        if (!named.length || named.some(prompt=>!permitted(prompt) || !found.visible.has(prompt)))
          conservative ||= `${deleted.has(path)?'deleted':'implementation'} ownership unavailable: ${path}; conservative selection`;
        for (const prompt of named) if (permitted(prompt)) own(prompt,path);
      };
      try {
        // Headers in either revision establish ownership, including assets whose
        // current header was removed. Apply permission before either read.
        const current = deleted.has(path) ? null : source.read({path}).content;
        const previous = old.has(path) ? git(['show',`${base}:${path}`]) : null;
        if (!implementation(path) && !bound.length && !headerPrompts(previous).length && !headerPrompts(current).length) continue;
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
  let estimated = 0, maximum = 0, requests = 0;
  const dispatched = new Set(selectCheckTests({stories},{affected}).tests);
  for (const row of rows.filter(row=>!affected || dispatched.has(row.test))) {
    // Inspect interfaces even when a different local rule won preflight precedence.
    const count = (row.steps ?? []).reduce((sum, step) => sum + cost(step?.entry_path), 0);
    if (row.state !== 'ready') continue;
    if (!Number.isSafeInteger(row.max_calls) || row.max_calls < 1) problem('undefined-call-bound',row.test,'/max_calls');
    estimated += Math.min(row.max_calls, count);
    maximum += row.max_calls * 2; requests += 2;
  }
  return {schema_version:'pdd.check-plan.v1',full,base,changed_paths:changed,stories,
    calls:{estimated:prerequisites.length?null:estimated,maximum:prerequisites.length?null:maximum,check_requests:requests,lint_model_calls:0},prerequisites};
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
  return ['Check plan:', ...plan.stories.flatMap(story=>[
    `  ${story.role}: ${story.story_path} (${story.tests.join(', ')}); ${story.reason}`,
    `    dependency closure: ${story.dependency_closure.join(', ') || 'unavailable'}`]),
    `  Interpreter calls: about ${plan.calls.estimated ?? 'unknown'}; at most ${plan.calls.maximum ?? 'unknown'} including one restart replacement per test; at most ${plan.calls.check_requests} Check requests; lint: 0 model calls.`,
    ...plan.prerequisites.map(item=>`  prerequisite: ${item.code}: ${item.path} ${item.field}`)];
}

export function checkPlanResultLines(result) {
  const counts = group => [`${group.passed.length} passed`,...(group.failures.length?[`${group.failures.length} failed`]:[]),
    ...(group.unresolved.length?[`${group.unresolved.length} unresolved`]:[])].join(', ');
  return result ? [`Target checks: ${result.target.state}; ${counts(result.target)}.`,
    `Baseline obligations: ${result.baseline.state}; ${counts(result.baseline)}.`, result.guidance] : [];
}
