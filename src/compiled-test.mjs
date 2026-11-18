// Generated from prompts/cli/compiled-test.prompt.md (sha256: 57dd8b48eb440c9ead51ba9c95d94de66be356a563d01f5d066dca250fa6de51).
import { spawnSync } from 'node:child_process';
import { mkdirSync, writeFileSync, lstatSync, statSync, realpathSync } from 'node:fs';
import { join, resolve, relative, sep, basename } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { findTests, selectTests, readPrompt, scenarioShapeRefusal, storyCriteria, checkInput, createStrictSourceAccess, preflight, exactValue, parseScenarioJson, stringifyScenarioJson, sha256 } from './runtime-seam.mjs';

const commandWords = command => {
  if (typeof command !== 'string' || !command.trim() || /[\n\r;|&<>`$\\'"(){}*?\[\]]/.test(command)) return null;
  return command.trim().split(/\s+/);
};
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const unrun = (step, reason) => ({step_id:step?.step_id, status:'not run', reason});
function executeCli(step, doc, found, root, ports) {
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
const CALL_VERSION = 'prompt-runtime.code-call.v1';
const same = (a, b) => isDeepStrictEqual(exactValue(a), exactValue(b));
const keysExactly = (value, keys) => object(value) && same(Object.keys(value).sort(), [...keys].sort());
const safeCount = value => Number.isSafeInteger(value) && value >= 0;
const nonnegativeInteger = value => typeof value === 'bigint' ? value >= 0n : Number.isFinite(value) && Number.isInteger(value) && value >= 0;
const literal = value => typeof value === 'number' ? Number.isFinite(value) : Array.isArray(value) ? value.every(literal) : !object(value) ||
  !Object.keys(value).some(key => ['$step_result','$contract','$seed'].includes(key)) && Object.values(value).every(literal);
const pointerTokens = path => typeof path === 'string' && (path === '' || path.startsWith('/') && !/~(?![01])/.test(path))
  ? path === '' ? [] : path.slice(1).split('/').map(token => token.replace(/~1/g, '/').replace(/~0/g, '~')) : null;
const MISSING = Symbol('missing');
function atPointer(value, path) {
  if (value === undefined) return MISSING;
  const tokens = pointerTokens(path);
  if (!tokens) return MISSING;
  for (const token of tokens) {
    if ((!object(value) && !Array.isArray(value)) || Array.isArray(value) && !/^(0|[1-9][0-9]*)$/.test(token) || !Object.hasOwn(value, token)) return MISSING;
    value = value[token];
  }
  return value;
}
function validCall(implementation) {
  return keysExactly(implementation, ['kind', 'command', 'symbol']) && implementation.kind === 'call' &&
    Array.isArray(implementation.command) && implementation.command.length > 0 &&
    implementation.command.every(word => typeof word === 'string' && !word.includes('\0')) &&
    implementation.command[0].trim().length > 0 && typeof implementation.symbol === 'string' &&
    implementation.symbol.trim().length > 0 && !implementation.symbol.includes('\0');
}

function admitScenario(root, found, test, source) {
  const prompts = new Map();
  for (const step of test.doc?.steps ?? []) {
    const text = source.read({path:step.entry_path}).content;
    const prompt = readPrompt(root, found.visible, step.entry_path, found.workspace);
    if (prompt.rawText !== text) throw Error('Entry source changed during admission.');
    prompts.set(step.entry_path, prompt);
  }
  const row = preflight({root, found, selected:[test], workspace:found.workspace}).rows[0];
  const typed = [...prompts.values()].some(prompt =>
    Array.isArray(prompt.interface?.entries) && prompt.interface.entries.some(entry => entry?.implementation?.kind === 'call'));
  if (typed && !row.native_only?.length && !row.refusals.length && !row.not_checked?.length) {
    const captured = createStrictSourceAccess(root, found.workspace).captureSource({tests:[test.path]});
    for (const file of captured.sources) {
      const text = source.read({path:file.path}).content;
      if (sha256(Buffer.from(text, 'utf8')) !== captured.raw_file_hashes[file.path])
        throw Error('Required source changed during admission.');
    }
  }
  return {row, prompts};
}

function fixturePlan(iface, entryPath, doc, world) {
  if (!object(world) || !literal(world) || !object(doc.simulation ?? {}) || !literal(doc.simulation ?? {})) return 'Scenario world or simulation is malformed.';
  if ((iface.calls ?? []).length) return 'Internal prompt calls are unsupported.';
  const resources = iface.resources ?? [], bindings = new Map(), counters = [];
  for (const resource of resources) {
    if (!object(resource) || !['port','command'].includes(resource.kind) || !Array.isArray(resource.operations))
      return 'Only declared port or read-only command resources are supported.';
    if (resource.kind === 'command' && (resource.access !== 'read' || resource.operations.some(operation => operation?.access !== 'read')))
      return 'Recorded command resources and operations must be read-only.';
    for (const operation of resource.operations) {
      const name = `${resource.name}.${operation.name}`, counterName = `${basename(entryPath,'.prompt.md')}-${resource.name}-${operation.name}`;
      if (bindings.has(name)) return 'Duplicate resource operation.';
      bindings.set(name,{operation,counterName});
    }
  }
  const simulation = doc.simulation ?? {};
  if (!same([...bindings.keys()].sort(),Object.keys(simulation).sort())) return 'Every declared resource operation needs exactly one saved fixture binding.';
  for (const [name,{operation}] of bindings) {
    const binding = simulation[name];
    if (!keysExactly(binding,['action','world_pointer','cases','result_template','result_value_pointer']) || binding.action !== 'fixture.lookup' ||
        binding.result_template !== null || binding.result_value_pointer !== '' || !pointerTokens(binding.world_pointer)?.length ||
        !safeCount(atPointer(world,binding.world_pointer)) || !Array.isArray(binding.cases) || !binding.cases.length)
      return 'Saved fixture binding is malformed or unsupported.';
    const tokens = pointerTokens(binding.world_pointer);
    if (counters.some(other => tokens.slice(0,other.length).every((v,i) => v === other[i]) || other.slice(0,tokens.length).every((v,i) => v === tokens[i]))) return 'Fixture counter paths overlap.';
    counters.push(tokens);
    const indices = new Set();
    for (const item of binding.cases) {
      if (!keysExactly(item,['args','call_index','result']) || !object(item.args) || !literal(item.args) ||
          !safeCount(item.call_index) || item.call_index === 0 || indices.has(item.call_index) ||
          !schemaAccepts(item.args,operation.arguments_schema) || !schemaAccepts(item.result,operation.result_schema))
        return 'Saved fixture cases are malformed or do not satisfy the resource schema.';
      indices.add(item.call_index);
    }
  }
  return {resources:Object.fromEntries([...bindings.values()].map(({counterName}) => [counterName,0])),internal:{}};
}
function schemaAccepts(value, schema) {
  if (!object(schema) || !literal(value)) return false;
  const admission = checkInput(value,schema,0);
  return !admission.refusals.length && !admission.warnings.length;
}
function supportedChecks(checks) {
  return Array.isArray(checks) && checks.length > 0 && checks.every(check =>
    keysExactly(check,['criterion_id','target','path','op','value']) && ['result','world','calls','error'].includes(check.target) &&
    pointerTokens(check.path) !== null && ['equals','count'].includes(check.op) && literal(check.value) &&
    (check.op !== 'count' || nonnegativeInteger(check.value)));
}
function executeCall(step, doc, prompt, root, ports, world) {
  const iface = prompt.interface, entry = iface.entries.find(entry => entry.operation === step.operation);
  if (!validCall(entry?.implementation)) return {step:unrun(step,'Call implementation metadata is malformed or unsupported.')};
  if (step.simulation_overrides !== undefined && (!object(step.simulation_overrides) || Object.keys(step.simulation_overrides).length))
    return {step:unrun(step,'Step simulation overrides are not supported.')};
  if (!literal(step.input) || !schemaAccepts(step.input,entry.input_schema)) return {step:unrun(step,'Typed input is referenced, invalid or unsupported.')};
  if (!supportedChecks(step.checks)) return {step:unrun(step,'A typed check is unsupported.')};
  const plan = fixturePlan(iface,step.entry_path,doc,world);
  if (typeof plan === 'string') return {step:unrun(step,plan)};
  for (const path of [join(root,'.pdd'),join(root,'.pdd','.gitignore'),join(root,'.pdd','code-test'),join(root,'.pdd','code-test','latest.json')]) {
    try { if (lstatSync(path).isSymbolicLink()) return {step:unrun(step,'Code test result path is a symbolic link.')}; }
    catch (error) { if (error.code !== 'ENOENT') return {step:unrun(step,'Code test result path is unsafe.')}; }
  }
  let response;
  try {
    const words = entry.implementation.command;
    const result = ports.spawn(words[0],words.slice(1),{cwd:root,input:stringifyScenarioJson({schema_version:CALL_VERSION,operation:step.operation,
      symbol:entry.implementation.symbol,input:step.input,initial_world:world,simulation:doc.simulation ?? {}}),encoding:null,timeout:600000,maxBuffer:10_485_760});
    if (result.error || result.status !== 0 || result.signal) throw Error(result.error?.message ?? result.signal ?? `exit ${result.status}`);
    response = parseScenarioJson(typeof result.stdout === 'string' ? result.stdout : new TextDecoder('utf-8',{fatal:true}).decode(result.stdout));
    const hasResult = Object.hasOwn(response ?? {},'result');
    if (!keysExactly(response,['schema_version',hasResult ? 'result' : 'error','world','calls']) || response.schema_version !== CALL_VERSION || !object(response.world) || !literal(response.world) ||
        !keysExactly(response.calls,['resources','internal']) || !keysExactly(response.calls.internal,[]) ||
        !keysExactly(response.calls.resources,Object.keys(plan.resources)) || !Object.values(response.calls.resources).every(safeCount)) throw Error('Invalid response envelope or per-step calls.');
    if (hasResult ? !schemaAccepts(response.result,entry.result_schema) :
        !keysExactly(response.error,['code']) || !entry.errors.includes(response.error.code)) throw Error('Response result or error does not satisfy the entry schema.');
  } catch (error) { return {step:unrun(step,`Typed command did not complete: ${error.message}`)}; }
  const checks = step.checks.map(check => {
    const selected = atPointer(response[check.target],check.path);
    const actual = check.op === 'count' ? Array.isArray(selected) ? selected.length : object(selected) ? Object.keys(selected).length :
      typeof selected === 'string' ? [...selected].length : MISSING : selected;
    return {criterion_id:check.criterion_id,target:check.target,path:check.path,op:check.op,status:actual !== MISSING && same(actual,check.value) ? 'passed':'failed',
      expected:check.value,actual:actual === MISSING ? {missing:true} : actual};
  });
  const expectedError = Object.hasOwn(step,'expected_error'), hasError = Object.hasOwn(response,'error');
  const outcomeMatches = expectedError ? hasError && response.error.code === step.expected_error : !hasError;
  return {world:response.world,step:{step_id:step.step_id,status:outcomeMatches && checks.every(check => check.status === 'passed') ? 'passed':'failed',checks,
    ...(!outcomeMatches ? {reason:expectedError ? `Expected application error ${step.expected_error}.` : `Unexpected application error ${response.error.code}.`} : {})}};
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
    let refusal = test.error || scenarioShapeRefusal(test.doc,test.path), doc, admittedPrompts;
    try {
      const admitted = admitScenario(root,found,test,source), admission = admitted.row;
      admittedPrompts = admitted.prompts;
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
      let world = doc.initial_world, worldKnown = true;
      for (const step of doc.steps) {
        const prompt = admittedPrompts.get(step.entry_path);
        const typed = Array.isArray(prompt.interface?.entries) && prompt.interface.entries.find(entry => entry.operation === step.operation)?.implementation?.kind === 'call';
        let outcome;
        if (typed) {
          if (!worldKnown) outcome = unrun(step,'The required starting world is unknown after an unrun typed step.');
          else {
            const observed = executeCall(step,doc,prompt,root,{spawn},world);
            outcome = observed.step;
            if (Object.hasOwn(observed,'world')) world = observed.world;
            else worldKnown = false;
          }
        } else outcome = executeCli(step,doc,found,root,{spawn});
        steps.push({scenario:test.path,step:outcome});
      }
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
  if(json) stdout.write(stringifyScenarioJson(report)+'\n'); else for(const row of stories) { stdout.write(`${row.status.toUpperCase()}  ${row.story}  ${commit ?? 'commit unknown'}  ${dirty === null ? 'dirty unknown' : dirty ? 'dirty' : 'clean'}\n`); for(const {scenario, step} of groups.get(row.story) ?? []) { if(step.reason) stdout.write(`  ${step.step_id}: ${step.status}: ${step.reason}\n`); for(const check of step.checks ?? []) if(check.status === 'failed') stdout.write(`  ${scenario} · step ${step.step_id} · ${check.criterion_id} ${check.path}: expected ${stringifyScenarioJson(check.expected)}, actual ${stringifyScenarioJson(check.actual)}\n`); } }
  return commit && stories.every(row=>row.status==='passed') ? 0 : 1;
}
