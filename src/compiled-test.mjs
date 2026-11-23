// Prompt: prompts/cli/compiled-test.prompt.md
import { spawnSync } from 'node:child_process';
import { mkdirSync, writeFileSync, lstatSync, statSync, realpathSync } from 'node:fs';
import { join, resolve, relative, sep } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { findTests, selectTests, readPrompt, scenarioShapeRefusal, storyCriteria, checkInput, createStrictSourceAccess, preflight, exactValue, parseScenarioJson, stringifyScenarioJson } from './runtime-seam.mjs';
import { compileScenarioText } from './scenario-compile.mjs';
import { classifyTargetedScenarioCriteria } from './core/test-ergonomics.mjs';

const commandWords = command => {
  if (typeof command !== 'string' || !command.trim() || /[\n\r;|&<>`$\\'"(){}*?\[\]]/.test(command)) return null;
  return command.trim().split(/\s+/);
};
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const unrun = (step, reason) => ({step_id:step?.step_id, status:'not run', reason});
// A plain-Markdown prompt (no Runtime interface) gets its command from pdd.json code.commands (#3641).
const missingCommand = entry => `CLI implementation command is missing or unsupported. ${entry} has no Runtime interface, so add "code": {"commands": {"${entry}": "COMMAND"}} to pdd.json (whitespace-separated argv, no shell).`;
function codeCommands(source, visible) {
  if (!visible.has('pdd.json')) return {};
  try {
    const commands = JSON.parse(source.read({path:'pdd.json'}).content.toString('utf8'))?.code?.commands;
    return object(commands) ? commands : {};
  } catch { return {}; }
}
function execute(step, doc, found, root, ports) {
  if (step.simulation_overrides !== undefined && (!object(step.simulation_overrides) || Object.keys(step.simulation_overrides).length))
    return unrun(step, 'Step simulation overrides are not supported.');
  if (!object(doc.initial_world) || Object.keys(doc.initial_world).length ||
      doc.simulation !== undefined && (!object(doc.simulation) || Object.keys(doc.simulation).length))
    return unrun(step, 'Scenario world and port simulation are not supported.');
  let prompt;
  try { prompt = readPrompt(root, found.visible, step.entry_path, found.workspace); } catch { return unrun(step, 'Entry prompt is unavailable.'); }
  if (Object.hasOwn(step, 'expected_error')) return unrun(step, 'Expected-error steps are unsupported.');
  let words;
  if (prompt.error === 'interface-missing' && prompt.interface === undefined) {
    words = commandWords(Object.hasOwn(ports.commands, step.entry_path) ? ports.commands[step.entry_path] : undefined);
    if (!words) return unrun(step, missingCommand(step.entry_path));
  } else {
  const iface = prompt.interface;
  if (!object(iface) || !Array.isArray(iface.entries) || !iface.entries.every(object) ||
      !['resources', 'calls'].every(key => iface[key] === undefined || Array.isArray(iface[key])) ||
      !Array.isArray(iface.conventions) || !iface.conventions.every(object))
    return unrun(step, 'Entry interface is malformed.');
  const index = iface.entries.findIndex(entry => entry.operation === step.operation);
  if (index < 0) return unrun(step, 'Entry is unavailable.');
  if (iface.resources?.length || iface.calls?.length) return unrun(step, 'Entry resources or calls cannot be supplied to code.');
  if (!object(iface.entries[index].input_schema) || !object(iface.entries[index].result_schema)) return unrun(step, 'Entry schemas are missing or malformed.');
  const conventions = iface.conventions;
  if (!['input_schema','result_schema'].every(key => conventions.some(c => c.path === `/entries/${index}/${key}` && c.convention === 'cli'))) return unrun(step, 'Entry is not a CLI.');
  const admission = checkInput(step.input, iface.entries[index].input_schema, 0);
  if (!iface.entries[index].input_schema || admission.refusals.length || admission.warnings.length) return unrun(step, 'CLI input schema cannot admit this input.');
  const implementation = iface.entries[index].implementation;
  words = commandWords(implementation?.command);
  if (implementation?.kind !== 'cli' || !words) return unrun(step, 'CLI implementation command is missing or unsupported.');
  }
  if (!step.input || !Array.isArray(step.input.argv) || !step.input.argv.every(x => typeof x === 'string') || (step.input.stdin !== undefined && typeof step.input.stdin !== 'string') || Object.keys(step.input).some(k => !['argv','stdin'].includes(k))) return unrun(step, 'CLI input is unsupported.');
  if (!step.checks?.length || step.checks.some(c => c.target !== 'result' || !['/stdout','/stderr','/exit_code'].includes(c.path) || c.op !== 'equals')) return unrun(step, 'A check is unsupported.');
  let result;
  try { result = ports.spawn(words[0], [...words.slice(1), ...step.input.argv], { cwd:root, input:step.input.stdin ?? '', encoding:'utf8', timeout:600000, maxBuffer:10_485_760 }); }
  catch (error) { return unrun(step, `Command did not complete: ${error.message}`); }
  if (result.error || result.status === null) return unrun(step, `Command did not complete: ${result.error?.message ?? result.signal ?? 'unknown reason'}`);
  const actual = {exit_code:result.status, stdout:result.stdout, stderr:result.stderr};
  const checks = step.checks.map(c => ({criterion_id:c.criterion_id, path:c.path, status:isDeepStrictEqual(exactValue(actual[c.path.slice(1)]),exactValue(c.value)) ? 'passed':'failed', expected:c.value, actual:actual[c.path.slice(1)]}));
  return {step_id:step.step_id,status:checks.every(c => c.status === 'passed') ? 'passed':'failed',checks};
}
export async function runCompiledTest({root, words, json}, {stdout, stderr, spawn = spawnSync} = {}) {
  const cwd = root;
  const top = spawn('git',['rev-parse','--show-toplevel'],{cwd:root,encoding:'utf8'});
  if (top.status !== 0 || !top.stdout?.trim()) { stderr.write('No Git project root is available.\n'); return 2; }
  root = top.stdout.trim();
  const found = findTests({root, excludeFixtureProjects:words.length === 0});
  const directories = new Set();
  const normalized = words.map(word => {
    const path = resolve(realpathSync(cwd), word), rel = relative(realpathSync(root), path).split(sep).join('/');
    const inside = rel !== '..' && !rel.startsWith('../');
    let directory = false;
    try { directory = inside && statSync(path).isDirectory(); } catch {}
    if (directory) directories.add(rel || '.');
    return word.includes('/') || found.visible.has(rel) || directory ? (rel || '.') : word;
  });
  const missing = (found.untested ?? []).filter(item => !words.length || [...directories].some(dir => dir === '.' || item.storyPath.startsWith(dir.replace(/\/$/, '') + '/')));
  const selection = selectTests(found, normalized);
  selection.unknown = selection.unknown.filter(word => !directories.has(word) || !missing.some(item => word === '.' || item.storyPath.startsWith(word.replace(/\/$/, '') + '/')));
  if (selection.unknown.length || selection.untested.length || (!selection.selected.length && !missing.length)) { stderr.write(`No selected Story tests: ${[...selection.unknown,...selection.untested].join(', ')}\n`); return 2; }
  const git = spawn('git',['rev-parse','HEAD'],{cwd:root,encoding:'utf8'}), commit = git.status === 0 ? git.stdout.trim() : null;
  const state = spawn('git',['status','--porcelain','--untracked-files=normal'],{cwd:root,encoding:'utf8'}), dirty = state.status === 0 ? !!state.stdout.trim() : null;
  const source = createStrictSourceAccess(root, found.workspace).sourceFilePort(found.visible);
  const commands = codeCommands(source, found.visible);
  const groups = new Map();
  for (const item of missing) groups.set(item.storyPath, [{scenario:null, step:unrun({step_id:item.storyPath}, item.line)}]);
  const explicitScenarioPaths = new Set(
    normalized
      .map(w => (typeof w === 'string' ? w.replace(/^\.\//, '') : ''))
      .filter(w => w.endsWith('.json') && selection.selected.some(t => t.path === w)),
  );
  const selectedByStory = new Map();
  for (const test of selection.selected) {
    if (test.storyPath) {
      if (!selectedByStory.has(test.storyPath)) selectedByStory.set(test.storyPath, []);
      selectedByStory.get(test.storyPath).push(test);
    }
  }
  const siblingCoveredCache = new Map();
  const checkedCriterionTextsFor = candidate => {
    try {
      if (candidate.error || scenarioShapeRefusal(candidate.doc, candidate.path)) return new Set();
      const admission = preflight({ root, found, selected: [candidate], allowMissingInterfaces: true }).rows[0];
      if (admission.refusals.length || admission.native_only?.length) return new Set();
      const raw = source.read({ path: candidate.path }).content;
      const storySource = source.read({ path: candidate.storyPath }).content;
      const compiled = compileScenarioText(raw, { path: candidate.path, storyPath: candidate.storyPath, storySource });
      if (compiled.refusal) return new Set();
      const parsedDoc = parseScenarioJson(compiled.text);
      const storyList = storyCriteria(storySource);
      if (!isDeepStrictEqual(compiled.doc, candidate.doc) || !storyList.length || !isDeepStrictEqual([...storyList].sort(), parsedDoc.criteria.map(c => c.text).sort())) return new Set();
      const notCheckedIds = new Set((admission.not_checked ?? []).map(item => item.criterion_id));
      const checkedTexts = new Set();
      for (const criterion of parsedDoc.criteria) {
        if (!notCheckedIds.has(criterion.id)) checkedTexts.add(criterion.text);
      }
      return checkedTexts;
    } catch {
      return new Set();
    }
  };
  const siblingCheckedIdsFor = (test, doc, pool) => {
    const key = `${test.path}\0${pool === found.tests ? 'all' : 'sel'}`;
    if (siblingCoveredCache.has(key)) return siblingCoveredCache.get(key);
    const idByText = new Map(doc.criteria.map(c => [c.text, c.id]));
    const coveredIds = new Set();
    for (const sib of pool) {
      if (sib.path === test.path || sib.storyPath !== test.storyPath) continue;
      for (const text of checkedCriterionTextsFor(sib)) {
        const matchedId = idByText.get(text);
        if (matchedId) coveredIds.add(matchedId);
      }
    }
    siblingCoveredCache.set(key, coveredIds);
    return coveredIds;
  };
  for (const test of selection.selected) {
    const story = test.storyPath ?? test.path, steps = groups.get(story) ?? [];
    let refusal = test.error || scenarioShapeRefusal(test.doc,test.path), doc, admission;
    try {
      admission = preflight({root,found,selected:[test],allowMissingInterfaces:true}).rows[0];
      if (admission.native_only?.length) {
        steps.push({scenario:test.path, step:unrun({step_id:test.path}, `Native-only interface: ${admission.native_only.map(item => item.reason).join('; ')}`)});
        groups.set(story,steps);
        continue;
      }
      if (admission.refusals.length) refusal = true;
      const raw = source.read({path:test.path}).content;
      const storySource = source.read({path:test.storyPath}).content;
      const compiled = compileScenarioText(raw, {path:test.path, storyPath:test.storyPath, storySource});
      if (compiled.refusal) refusal = true;
      doc = parseScenarioJson(compiled.text);
      const storyList = storyCriteria(storySource);
      if (!isDeepStrictEqual(compiled.doc, test.doc) || !storyList.length || !isDeepStrictEqual([...storyList].sort(),doc.criteria.map(c=>c.text).sort())) refusal = true;
      for (const step of doc.steps) source.read({path:step.entry_path});
    } catch { refusal = true; }
    let siblingCoverageValid = false;
    if (!refusal && admission?.not_checked?.length) {
      const notCheckedIds = new Set(admission.not_checked.map(item => item.criterion_id));
      const storyCriteriaIds = doc.criteria.map(c => c.id);
      const ownCheckedIds = storyCriteriaIds.filter(id => !notCheckedIds.has(id));
      if (explicitScenarioPaths.has(test.path)) {
        const siblingIds = siblingCheckedIdsFor(test, doc, found.tests);
        const cls = classifyTargetedScenarioCriteria({
          explicit_scenario_paths: [...explicitScenarioPaths],
          target_test_path: test.path,
          story_criteria_ids: storyCriteriaIds,
          own_checked_ids: ownCheckedIds,
          sibling_checked_ids: [...siblingIds],
        });
        siblingCoverageValid = cls.can_pass_as_targeted_slice;
      } else {
        const selectedSiblings = selectedByStory.get(test.storyPath) ?? [];
        if (selectedSiblings.length > 1) {
          const siblingIds = siblingCheckedIdsFor(test, doc, selectedSiblings);
          siblingCoverageValid = ownCheckedIds.length > 0 && storyCriteriaIds.every(id => !notCheckedIds.has(id) || siblingIds.has(id));
        }
      }
      if (!siblingCoverageValid) refusal = true;
    }
    if (refusal) steps.push({scenario:test.path, step:unrun({step_id:test.path}, 'Scenario is invalid or unavailable.')});
    else {
      const covered = new Set(doc.steps.flatMap(step => step.checks.map(check => check.criterion_id)));
      if (!siblingCoverageValid && doc.criteria.some(criterion => !covered.has(criterion.id))) steps.push({scenario:test.path, step:unrun({step_id:test.path}, 'A Story criterion has no check.')});
      steps.push(...doc.steps.map(step => ({scenario:test.path, step:execute(step,doc,found,root,{spawn,commands})})));
    }
    groups.set(story,steps);
  }
  const stories = [...groups].map(([story,entries]) => {
    const steps = entries.map(entry => entry.step);
    return {story, status:steps.some(s=>s.status==='failed')?'failed':steps.every(s=>s.status==='passed')?'passed':'not run',steps};
  });
  const report = {target:'code',commit,dirty,ai_calls:0,stories};
  for (const path of [join(root,'.pdd'),join(root,'.pdd','.gitignore'),join(root,'.pdd','code-test'),join(root,'.pdd','code-test','latest.json')]) {
    try { if (lstatSync(path).isSymbolicLink()) { stderr.write('Code test result path is a symbolic link.\n'); return 1; } }
    catch (error) { if (error.code !== 'ENOENT') throw error; }
  }
  mkdirSync(join(root,'.pdd','code-test'),{recursive:true});
  try { writeFileSync(join(root,'.pdd','.gitignore'),'*\n',{flag:'wx'}); } catch (error) { if (error.code !== 'EEXIST') throw error; }
  writeFileSync(join(root,'.pdd','code-test','latest.json'),stringifyScenarioJson(report,2)+'\n');
  if(json) stdout.write(stringifyScenarioJson(report)+'\n'); else for(const row of stories) { stdout.write(`${row.status.toUpperCase()}  ${row.story}  ${commit ?? 'commit unknown'}  ${dirty === null ? 'dirty unknown' : dirty ? 'dirty' : 'clean'}\n`); for(const {scenario, step} of groups.get(row.story) ?? []) { if(step.reason) stdout.write(`  ${step.step_id}: not run: ${step.reason}\n`); for(const check of step.checks ?? []) if(check.status === 'failed') stdout.write(`  ${scenario} · step ${step.step_id} · ${check.criterion_id} ${check.path}: expected ${stringifyScenarioJson(check.expected)}, actual ${stringifyScenarioJson(check.actual)}\n`); } }
  return commit && stories.every(row=>row.status==='passed') ? 0 : 1;
}
