// Generated from prompts/cli/compiled-test.prompt.md (sha256: e0060fec0b5881c698977df33259205a155eaeacf56600544f4e21ffdbae0968).
import { spawnSync } from 'node:child_process';
import { mkdirSync, writeFileSync, lstatSync } from 'node:fs';
import { join } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { findTests, selectTests, readPrompt, scenarioShapeRefusal, storyCriteria, checkInput, createStrictSourceAccess, preflight } from './runtime-preflight.mjs';

const commandWords = command => {
  if (typeof command !== 'string' || !command.trim() || /[\n\r;|&<>`$\\'"(){}*?\[\]]/.test(command)) return null;
  return command.trim().split(/\s+/);
};
const unrun = (step, reason) => ({step_id:step?.step_id, status:'not run', reason});
function execute(step, doc, found, root, ports) {
  if (doc.simulation && Object.keys(doc.simulation).length || doc.initial_world && Object.keys(doc.initial_world).length)
    return unrun(step, 'Scenario world and port simulation are not supported.');
  let prompt;
  try { prompt = readPrompt(root, found.visible, step.entry_path, found.workspace); } catch { return unrun(step, 'Entry prompt is unavailable.'); }
  if (Object.hasOwn(step, 'expected_error')) return unrun(step, 'Expected-error steps are unsupported.');
  const iface = prompt.interface, index = iface?.entries?.findIndex(entry => entry.operation === step.operation) ?? -1;
  if (index < 0) return unrun(step, 'Entry is unavailable.');
  if (iface.resources?.length || iface.calls?.length) return unrun(step, 'Entry resources or calls cannot be supplied to code.');
  const conventions = iface.conventions ?? [];
  if (!['input_schema','result_schema'].every(key => conventions.some(c => c.path === `/entries/${index}/${key}` && c.convention === 'cli'))) return unrun(step, 'Entry is not a CLI.');
  const admission = checkInput(step.input, iface.entries[index].input_schema, 0);
  if (!iface.entries[index].input_schema || admission.refusals.length || admission.warnings.length) return unrun(step, 'CLI input schema cannot admit this input.');
  const implementation = iface.entries[index].implementation, words = commandWords(implementation?.command);
  if (implementation?.kind !== 'cli' || !words) return unrun(step, 'CLI implementation command is missing or unsupported.');
  if (!step.input || !Array.isArray(step.input.argv) || !step.input.argv.every(x => typeof x === 'string') || (step.input.stdin !== undefined && typeof step.input.stdin !== 'string') || Object.keys(step.input).some(k => !['argv','stdin'].includes(k))) return unrun(step, 'CLI input is unsupported.');
  if (!step.checks?.length || step.checks.some(c => c.target !== 'result' || !['/stdout','/stderr','/exit_code'].includes(c.path) || c.op !== 'equals')) return unrun(step, 'A check is unsupported.');
  const result = ports.spawn(words[0], [...words.slice(1), ...step.input.argv], { cwd:root, input:step.input.stdin ?? '', encoding:'utf8', timeout:600000, maxBuffer:10_485_760 });
  if (result.error || result.status === null) return unrun(step, `Command did not complete: ${result.error?.message ?? result.signal ?? 'unknown reason'}`);
  const actual = {exit_code:result.status, stdout:result.stdout, stderr:result.stderr};
  const checks = step.checks.map(c => ({criterion_id:c.criterion_id, path:c.path, status:isDeepStrictEqual(actual[c.path.slice(1)],c.value) ? 'passed':'failed', expected:c.value, actual:actual[c.path.slice(1)]}));
  return {step_id:step.step_id,status:checks.every(c => c.status === 'passed') ? 'passed':'failed',checks};
}
export async function runCompiledTest({root, words, json}, {stdout, stderr, spawn = spawnSync} = {}) {
  const top = spawn('git',['rev-parse','--show-toplevel'],{cwd:root,encoding:'utf8'});
  if (top.status !== 0 || !top.stdout?.trim()) { stderr.write('No Git project root is available.\n'); return 2; }
  root = top.stdout.trim();
  const found = findTests({root, excludeFixtureProjects:true}), selection = selectTests(found, words);
  if (selection.unknown.length || selection.untested.length || (!selection.selected.length && (words.length || !found.untested.length))) { stderr.write(`No selected Story tests: ${[...selection.unknown,...selection.untested].join(', ')}\n`); return 2; }
  const git = spawn('git',['rev-parse','HEAD'],{cwd:root,encoding:'utf8'}), commit = git.status === 0 ? git.stdout.trim() : null;
  const state = spawn('git',['status','--porcelain','--untracked-files=normal'],{cwd:root,encoding:'utf8'}), dirty = state.status === 0 ? !!state.stdout.trim() : null;
  const source = createStrictSourceAccess(root, found.workspace).sourceFilePort(found.visible);
  const groups = new Map();
  if (!words.length) for (const item of found.untested) groups.set(item.storyPath, [unrun({step_id:item.storyPath}, item.line)]);
  for (const test of selection.selected) {
    const story = test.storyPath ?? test.path, steps = groups.get(story) ?? [];
    let refusal = test.error || scenarioShapeRefusal(test.doc,test.path);
    try {
      const admission = preflight({root,found,selected:[test]}).rows[0];
      if (admission.native_only?.length) {
        steps.push(unrun({step_id:test.path}, `Native-only interface: ${admission.native_only.map(item => item.reason).join('; ')}`));
        groups.set(story,steps);
        continue;
      }
      if (admission.refusals.length || admission.not_checked?.length) refusal = true;
      const doc = JSON.parse(source.read({path:test.path}).content);
      const story = storyCriteria(source.read({path:test.storyPath}).content);
      if (!isDeepStrictEqual(doc, test.doc) || !story.length || !isDeepStrictEqual([...story].sort(),doc.criteria.map(c=>c.text).sort())) refusal = true;
      for (const step of doc.steps) source.read({path:step.entry_path});
    } catch { refusal = true; }
    if (refusal) steps.push(unrun({step_id:test.path}, 'Scenario is invalid or unavailable.'));
    else {
      const covered = new Set(test.doc.steps.flatMap(step => step.checks.map(check => check.criterion_id)));
      if (test.doc.criteria.some(criterion => !covered.has(criterion.id))) steps.push(unrun({step_id:test.path}, 'A Story criterion has no check.'));
      steps.push(...test.doc.steps.map(step => execute(step,test.doc,found,root,{spawn})));
    }
    groups.set(story,steps);
  }
  const stories = [...groups].map(([story,steps]) => ({story, status:steps.some(s=>s.status==='failed')?'failed':steps.every(s=>s.status==='passed')?'passed':'not run',steps}));
  const report = {target:'code',commit,dirty,ai_calls:0,stories};
  for (const path of [join(root,'.pdd'),join(root,'.pdd','code-test'),join(root,'.pdd','code-test','latest.json')]) {
    try { if (lstatSync(path).isSymbolicLink()) { stderr.write('Code test result path is a symbolic link.\n'); return 1; } }
    catch (error) { if (error.code !== 'ENOENT') throw error; }
  }
  mkdirSync(join(root,'.pdd','code-test'),{recursive:true}); writeFileSync(join(root,'.pdd','code-test','latest.json'),JSON.stringify(report,null,2)+'\n');
  if(json) stdout.write(JSON.stringify(report)+'\n'); else for(const row of stories) { stdout.write(`${row.status.toUpperCase()}  ${row.story}  ${commit ?? 'commit unknown'}  ${dirty === null ? 'dirty unknown' : dirty ? 'dirty' : 'clean'}\n`); for(const step of row.steps) if(step.reason) stdout.write(`  ${step.step_id}: not run: ${step.reason}\n`); }
  return commit && stories.every(row=>row.status==='passed') ? 0 : 1;
}
