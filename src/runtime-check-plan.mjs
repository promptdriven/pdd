// Generated from prompts/cli/runtime-check-plan.prompt.md (sha256: 54b8fa31a87d406f1e42a8c3d0e7a2916a95369df65685ca0e5a406c71cf4d37).
import { spawnSync } from 'node:child_process';
import { captureSource, readPrompt, sourceFilePort } from './runtime-preflight.mjs';
import { resultOutcome } from './runtime-outcome.mjs';
import { allowsRuntimePath, loadRuntimeWorkspace } from './runtime-workspace.mjs';

const sorted = values => [...new Set(values)].sort();
const gitRead = (root, args) => {
  const reply = spawnSync('git', args, { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (reply.status !== 0) throw Error('change scope unavailable');
  return reply.stdout;
};

export function buildCheckPlan({ root, found, selected, rows, full, base = 'HEAD' }, ports = {}) {
  const git = args => (ports.git ?? gitRead)(root, args);
  let changed = null;
  try {
    changed = sorted([...git(['diff', '--name-only', '-z', '--no-renames', base, '--']).split('\0'),
      ...git(['ls-files', '--others', '--exclude-standard', '-z']).split('\0')].filter(Boolean));
  } catch { /* Unknown changes require conservative target coverage. */ }
  const workspace = found.workspace ?? loadRuntimeWorkspace({root});
  const source = sourceFilePort(root, found.visible, found.workspace);
  const owners = new Map(), unknownOwners = new Set();
  let deleted = new Set(), deletionsUnavailable = false;
  if (changed?.some(path=>allowsRuntimePath(workspace,path))) {
    try { deleted = new Set(git(['diff', '--name-only', '-z', '--no-renames', '--diff-filter=D', base, '--']).split('\0').filter(Boolean)); }
    catch { deletionsUnavailable = true; }
  }
  const own = (prompt, path) => {
    if (!found.visible.has(prompt)) return;
    owners.set(prompt, [...(owners.get(prompt) ?? []), path]);
    unknownOwners.delete(path);
  };
  for (const path of changed ?? []) {
    if (!allowsRuntimePath(workspace,path)) continue;
    if (deleted.has(path)) unknownOwners.add(path);
    else if (!found.visible.has(path)) continue;
    try {
      // Validate the permitted source path even when its working file is absent.
      if (deleted.has(path)) source.stat({path});
      const content = deleted.has(path) ? git(['show', `${base}:${path}`]) : source.read({path}).content;
      const header = content.slice(0, 4096).match(/Generated from\s+([^\s()]+\.prompt\.md)/);
      if (header) own(header[1], path);
    } catch { /* Unproved deleted ownership keeps target coverage conservative. */ }
  }
  if (changed?.length && found.visible.has('pdd-bindings.json')) {
    try {
      const inventory = JSON.parse(source.read({path:'pdd-bindings.json'}).content);
      for (const item of inventory.modules ?? []) if (changed.includes(item.module) && allowsRuntimePath(workspace,item.module) && typeof item.prompt === 'string') own(item.prompt, item.module);
    } catch { /* The binding owner retains inventory validation. */ }
  }
  const prerequisites = [], seenProblems = new Set(), prompts = new Map();
  const problem = (code, path, field) => {
    const key = `${code}\0${path}\0${field}`;
    if (!seenProblems.has(key)) { seenProblems.add(key); prerequisites.push({code,path,field}); }
  };
  const cost = (path, stack = new Set()) => {
    if (stack.has(path)) { problem('recursive-call-bound', path, '/calls'); return 0; }
    let prompt = prompts.get(path);
    if (!prompt) {
      try { prompt = readPrompt(root, found.visible, path, found.workspace); }
      catch { prompt = {error:'interface-unavailable'}; }
      prompts.set(path, prompt);
    }
    const iface = prompt.interface;
    if (!iface) { problem(prompt.error ?? 'interface-missing', path, '/interface'); return 0; }
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
  try {
    const captured = capture(root,{tests:selected.map(test=>test.path),appMap:null,excludeFixtureProjects:full});
    footprints = new Map((captured.stories ?? []).map(story=>[story.story_path,story]));
  } catch { /* Keep a broken Story from hiding other Stories' closures. */ }
  const stories = [...groups].map(([story_path, tests]) => {
    let closure = [], unavailable = false;
    const footprint = footprints.get(story_path);
    try {
      if (footprint?.unavailable) unavailable = true;
      else closure = sorted((footprint?.files ?? capture(root, {tests:tests.map(test=>test.path),appMap:null,excludeFixtureProjects:full}).files).map(file=>file.path));
    }
    catch { unavailable = true; }
    const affected = sorted((changed ?? []).filter(path => closure.includes(path) || tests.some(test=>test.path === path || test.storyPath === path))
      .concat(closure.flatMap(path=>owners.get(path) ?? [])));
    const uncertainOwner = deletionsUnavailable || unknownOwners.size > 0;
    const target = !full || changed === null || !changed.length || unavailable || uncertainOwner || affected.length > 0 || changed.includes('pdd-bindings.json');
    return {story_path,tests:tests.map(test=>test.path),role:target?'target':'baseline',
      reason:!full?'explicit selection':unavailable?'dependency closure unavailable; conservative selection':changed === null?'change scope unavailable; conservative selection':!changed.length?'no changed paths; conservative selection':uncertainOwner?'deleted ownership unavailable; conservative selection':affected.length?`changed paths: ${affected.join(', ')}`:target?'binding inventory changed':'unrelated to known changes; required by full batch; pre-change result unknown',
      affected_paths:affected,dependency_closure:closure};
  });
  if (!stories.some(story=>story.role === 'target')) for (const story of stories) {
    story.role = 'target'; story.reason = 'no affected Story established; conservative selection';
  }
  let estimated = 0, maximum = 0, requests = 0;
  for (const row of rows) {
    // Inspect interfaces even when a different local rule won preflight precedence.
    const count = row.steps.reduce((sum, step) => sum + cost(step?.entry_path), 0);
    if (row.state !== 'ready') continue;
    if (!Number.isSafeInteger(row.max_calls) || row.max_calls < 1) problem('undefined-call-bound',row.test,'/max_calls');
    estimated += Math.min(row.max_calls, count);
    maximum += row.max_calls * 2; requests += 2;
  }
  return {schema_version:'pdd.check-plan.v1',full,base,changed_paths:changed,stories,
    calls:{estimated:prerequisites.length?null:estimated,maximum:prerequisites.length?null:maximum,check_requests:requests,lint_model_calls:0},prerequisites};
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
