// Generated from prompts/cli/compiled-test.prompt.md (sha256: 217f4e51e6117e71e51c54558158a2eab822cdb03da04ee43436b4afb213862e).
import { spawnSync } from 'node:child_process';
import { mkdirSync, writeFileSync, lstatSync, statSync, realpathSync } from 'node:fs';
import { join, resolve, relative, sep } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { findTests, selectTests, readPrompt, scenarioShapeRefusal, storyCriteria, checkInput, createStrictSourceAccess, preflight, exactValue, parseScenarioJson, stringifyScenarioJson } from './runtime-seam.mjs';

const commandWords = command => {
  if (typeof command !== 'string' || !command.trim() || /[\n\r;|&<>`$\\'"(){}*?\[\]]/.test(command)) return null;
  return command.trim().split(/\s+/);
};
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const unrun = (step, reason) => ({step_id:step?.step_id, status:'not run', reason});
function execute(step, doc, found, root, ports) {
  if (step.simulation_overrides !== undefined && (!object(step.simulation_overrides) || Object.keys(step.simulation_overrides).length))
    return unrun(step, 'Step simulation overrides are not supported.');
  if (!object(doc.initial_world) || Object.keys(doc.initial_world).length ||
      doc.simulation !== undefined && (!object(doc.simulation) || Object.keys(doc.simulation).length))
    return unrun(step, 'Scenario world and port simulation are not supported.');
  let prompt;
  try { prompt = readPrompt(root, found.visible, step.entry_path, found.workspace); } catch { return unrun(step, 'Entry prompt is unavailable.'); }
  if (Object.hasOwn(step, 'expected_error')) return unrun(step, 'Expected-error steps are unsupported.');
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
  const implementation = iface.entries[index].implementation, words = commandWords(implementation?.command);
  if (implementation?.kind !== 'cli' || !words) return unrun(step, 'CLI implementation command is missing or unsupported.');
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
  const groups = new Map();
  for (const item of missing) groups.set(item.storyPath, [{scenario:null, step:unrun({step_id:item.storyPath}, item.line)}]);
  for (const test of selection.selected) {
    const story = test.storyPath ?? test.path, steps = groups.get(story) ?? [];
    let refusal = test.error || scenarioShapeRefusal(test.doc,test.path), doc;
    try {
      const admission = preflight({root,found,selected:[test]}).rows[0];
      if (admission.native_only?.length) {
        steps.push({scenario:test.path, step:unrun({step_id:test.path}, `Native-only interface: ${admission.native_only.map(item => item.reason).join('; ')}`)});
        groups.set(story,steps);
        continue;
      }
      if (admission.refusals.length || admission.not_checked?.length) refusal = true;
      const raw = source.read({path:test.path}).content;
      doc = parseScenarioJson(raw);
      const story = storyCriteria(source.read({path:test.storyPath}).content);
      if (!isDeepStrictEqual(JSON.parse(raw), test.doc) || !story.length || !isDeepStrictEqual([...story].sort(),doc.criteria.map(c=>c.text).sort())) refusal = true;
      for (const step of doc.steps) source.read({path:step.entry_path});
    } catch { refusal = true; }
    if (refusal) steps.push({scenario:test.path, step:unrun({step_id:test.path}, 'Scenario is invalid or unavailable.')});
    else {
      const covered = new Set(doc.steps.flatMap(step => step.checks.map(check => check.criterion_id)));
      if (doc.criteria.some(criterion => !covered.has(criterion.id))) steps.push({scenario:test.path, step:unrun({step_id:test.path}, 'A Story criterion has no check.')});
      steps.push(...doc.steps.map(step => ({scenario:test.path, step:execute(step,doc,found,root,{spawn})})));
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
