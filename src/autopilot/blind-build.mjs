// Prompt: prompts/cli/blind-build.prompt.md
import { spawn as nodeSpawn, spawnSync } from 'node:child_process';
import { createHash, randomBytes } from 'node:crypto';
import { closeSync, existsSync, mkdirSync, openSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import { tmpdir as osTmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { codeTestReport, runCliStep, writeLocalReport } from '../compiled-test.mjs';
import { captureSource, checkInput, stringifyScenarioJson } from '../runtime-seam.mjs';
import { agentCommand, jobEnvironment } from '../agent-job.mjs';
import { loadAgentDefinitions } from '../agent-config.mjs';

const EXCLUDED = ['user_stories/', 'tests/', 'selected scenarios', 'code', 'chat'];
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const sha256 = text => createHash('sha256').update(text).digest('hex');
const pretty = value => stringifyScenarioJson(value, 2) + '\n';
const inputKey = (entry, operation, input) => JSON.stringify([entry, operation, input]);
const readJsonFile = path => {
  let text;
  try { text = readFileSync(path, 'utf8'); } catch { return {value:null, reason:`${path.split('/').pop()} is missing`}; }
  try { return {value:JSON.parse(text), reason:null}; } catch { return {value:null, reason:`${path.split('/').pop()} is not valid JSON`}; }
};
const isCode = text => /Generated from\s+\S+\.prompt\.md/.test(text.split('\n').slice(0, 2).join('\n'));

// The prompt packet: the prompts and declared dependencies that captureSource selects, never Stories, cases or code.
function packetFiles(root, selected, found, ports) {
  const capture = ports.captureSource ?? captureSource;
  const captured = capture(root, {selected, found});
  const skip = new Set(selected.flatMap(test => [test.path, test.storyPath].filter(Boolean)));
  const paths = (Array.isArray(captured.files) ? captured.files : Object.keys(captured.files ?? {})).map(file => file.path ?? file);
  const files = [];
  for (const path of [...new Set(paths)].sort()) {
    if (skip.has(path) || path.startsWith('user_stories/') || path.startsWith('tests/') || path === 'pdd-bindings.json') continue;
    let content;
    try { content = readFileSync(join(root, path), 'utf8'); } catch { continue; }
    if (isCode(content)) continue;
    files.push({path, sha256:sha256(content), bytes:Buffer.byteLength(content), content});
  }
  return files;
}

function entriesOf(runs) {
  const entries = new Map();
  for (const run of runs) {
    const key = `${run.entry_path}\0${run.operation}`;
    if (!entries.has(key)) entries.set(key, {entry_path:run.entry_path, operation:run.operation, command:run.words.join(' '), words:run.words, input_schema:run.input_schema});
  }
  return [...entries.values()];
}

const progressRule = `Keep pdd-progress.json in this folder up to date after each step, as a JSON object {"status", "done", "doing", "stuck_on"}: status is "working", "done" or "stuck"; done lists the finished steps in words; doing is the current step; stuck_on names what blocks you (an error message, a failing command, a prompt sentence you cannot read one way) or is null. Set status to "done" when you finish.`;

// Each entry with its input schema: a collected input that the schema does not admit is dropped, so the agents must see it.
const entryLines = entries => entries.map(entry => `- ${entry.entry_path} (operation ${entry.operation}): ${entry.command}; input schema: ${JSON.stringify(entry.input_schema)}`);
const inputRule = 'Every input must match its entry\'s input schema exactly: use only the fields the schema lists (for example leave out "stdin" when the schema has no stdin). An input that the schema does not admit is dropped and never run.';

export function builderBrief({folder, entries, checkpoint = null}) {
  const lines = [
    `You are building a module from its prompts only. Your folder is ${folder}.`,
    'Read only the files in this folder. Do not look for tests, cases, other code, Git history or any file outside this folder.',
    '',
    'Entry prompts and the command that must run from this folder:',
    ...entryLines(entries),
    '',
    'Write the implementation in this folder so each command runs from this folder with the arguments and stdin that the prompt describes.',
    'Then write pdd-decisions.json: a JSON array of {"topic", "prompt_says", "choice", "example"}. List every choice the prompt did not decide, including small ones (number formats, signs, leading zeros, rounding, order of errors). prompt_says quotes the prompt words that left the choice open, or is "silent". example is one input where the choice shows: {"entry_path", "operation", "input"}.',
    inputRule,
    progressRule,
  ];
  if (checkpoint) lines.push('', 'continue from this checkpoint:', JSON.stringify(checkpoint, null, 2));
  return lines.join('\n') + '\n';
}

// Questions that find a second reading in any domain; a prober that only follows its own instinct misses whole kinds.
const proberQuestions = [
  'Go through the prompt sentence by sentence. For each sentence ask:',
  '1. Which value is meant: when a name comes back later (a total, a list, a path, a name), is it the value before or after an earlier step changed it (rounding, trimming, sorting, normalizing, filtering)?',
  '2. Same value, different form: are inputs that mean the same thing but are written differently treated alike (case, extra spaces, 2 and 2.0, a relative and an absolute path, an empty string and a missing value)?',
  '3. Edges: exactly at a limit, just past it, empty, one item, very large.',
  '4. Rules that overlap: when two rules apply to one input, which one wins (for example, which error is reported first)?',
  '5. What the prompt never mentions: one argument too many or too few, repeated items, unusual characters.',
  '6. Parts that must agree: do the parts of one output agree with each other (parts that add up to a printed whole, a count that matches a list)? Could a reading make them disagree?',
  '7. Order and format: the order of output lines or items, spaces, the final newline, letter case.',
];

export function proberBrief({folder, entries, checkpoint = null}) {
  const lines = [
    `You are reading prompts to find where they allow more than one reading. Your folder is ${folder}.`,
    'Do not write code. Read only the files in this folder.',
    '',
    'Entry prompts:',
    ...entryLines(entries),
    '',
    ...proberQuestions,
    '',
    'Write pdd-probes.json: a JSON array of {"topic", "readings", "inputs"}. readings lists the possible readings in words. inputs lists entry inputs {"entry_path", "operation", "input", "outcomes"}, where outcomes has one entry per reading, in the same order, saying in words what that reading gives for this input.',
    'Choose inputs whose outcomes differ between readings: if every reading gives the same outcome, the input cannot tell them apart, so choose another one. Outcomes describe each reading; do not say which reading is right.',
    inputRule,
    progressRule,
  ];
  if (checkpoint) lines.push('', 'continue from this checkpoint:', JSON.stringify(checkpoint, null, 2));
  return lines.join('\n') + '\n';
}

// Runs one headless agent in its folder; stops the whole process group at the time limit.
export function nativeRunAgent({agent, cwd, input, env, log, timeoutMs}) {
  return new Promise(resolve => {
    const {command, args} = agentCommand(agent);
    let fd, child, timedOut = false, killer = null, timer = null;
    try { fd = openSync(log, 'a'); } catch { fd = 'ignore'; }
    const finish = value => { if (timer) clearTimeout(timer); if (killer) clearTimeout(killer); if (typeof fd === 'number') try { closeSync(fd); } catch {} resolve(value); };
    try { child = nodeSpawn(command, args, {cwd, env, detached:true, stdio:['pipe', fd, fd]}); }
    catch (error) { finish({code:127, timedOut:false, error:error.message}); return; }
    child.on('error', error => finish({code:127, timedOut, error:error.message}));
    child.on('exit', (code, signal) => finish({code: code ?? (signal ? 128 : 1), timedOut, signal}));
    child.stdin.on('error', () => {});
    child.stdin.end(input);
    timer = setTimeout(() => {
      timedOut = true;
      try { process.kill(-child.pid, 'SIGTERM'); } catch {}
      killer = setTimeout(() => { try { process.kill(-child.pid, 'SIGKILL'); } catch {} }, 5000);
    }, timeoutMs);
  });
}

function tail(path, count = 20) {
  try { return readFileSync(path, 'utf8').split('\n').filter(line => line.length).slice(-count); } catch { return []; }
}

function checkpointOf(folder, log, reason) {
  const progress = readJsonFile(join(folder, 'pdd-progress.json'));
  return {progress: object(progress.value) ? progress.value : null, ...(object(progress.value) ? {} : {progress_reason: progress.reason ?? 'pdd-progress.json is not an object'}), log_tail: tail(log), reason};
}

function outcomeOf(result, folder, log) {
  if (result.timedOut) return {finished:false, checkpoint:checkpointOf(folder, log, 'time limit')};
  if (result.code !== 0) return {finished:false, checkpoint:checkpointOf(folder, log, result.error ? `could not start: ${result.error}` : `exit ${result.code}`)};
  const progress = readJsonFile(join(folder, 'pdd-progress.json'));
  if (object(progress.value) && progress.value.status === 'stuck') return {finished:false, checkpoint:checkpointOf(folder, log, 'stuck')};
  return {finished:true, checkpoint:null};
}

// Admits one collected input for comparison: a known CLI entry, a CLI input shape and the entry's input schema.
function admit(item, entries) {
  if (!object(item)) return {reason:'not an object'};
  const entry = entries.find(e => e.entry_path === item.entry_path && e.operation === item.operation);
  if (!entry) return {reason:'not a runnable CLI entry'};
  const input = item.input;
  if (!object(input) || !Array.isArray(input.argv) || !input.argv.every(x => typeof x === 'string') ||
      (input.stdin !== undefined && typeof input.stdin !== 'string') || Object.keys(input).some(k => !['argv', 'stdin'].includes(k)))
    return {reason:'CLI input is unsupported'};
  let admission;
  try { admission = checkInput(input, entry.input_schema, 0); } catch { return {reason:'input schema cannot admit this input'}; }
  if (admission.refusals?.length || admission.warnings?.length) return {reason:'input schema cannot admit this input'};
  return {entry, input};
}

function collectInputs({runs, decisions, probes, entries}) {
  const inputs = new Map(), dropped = [];
  const add = (source, topic, item) => {
    const admitted = admit(item, entries);
    if (admitted.reason) { dropped.push({source, topic, input:item?.input ?? item ?? null, reason:admitted.reason}); return; }
    const key = inputKey(admitted.entry.entry_path, admitted.entry.operation, admitted.input);
    if (!inputs.has(key)) inputs.set(key, {key, source, topic, entry:admitted.entry, input:admitted.input});
  };
  for (const run of runs) add('case', null, {entry_path:run.entry_path, operation:run.operation, input:run.input});
  for (const list of decisions) for (const decision of list ?? []) if (object(decision) && decision.example !== undefined) add('decision', decision.topic ?? null, decision.example);
  for (const probe of probes ?? []) if (object(probe)) for (const item of Array.isArray(probe.inputs) ? probe.inputs : []) add('probe', probe.topic ?? null, item);
  return {inputs:[...inputs.values()], dropped};
}

// A build's own folder path in its output (for example in an error message) is not a difference: it becomes BUILD.
function withoutFolder(result, folder) {
  if (result.not_run) return result;
  let real = folder; try { real = realpathSync(folder); } catch {}
  const paths = [...new Set([real, folder])].sort((a, b) => b.length - a.length);
  const clean = text => typeof text === 'string' ? paths.reduce((value, path) => value.split(path).join('BUILD'), text) : text;
  return {...result, stdout:clean(result.stdout), stderr:clean(result.stderr)};
}

function compare(builds, collected, ports) {
  const differences = [], keys = new Map();
  let agreed = 0;
  for (const item of collected.inputs) {
    const results = builds.map(build => withoutFolder(runCliStep({words:item.entry.words, input:item.input, cwd:build.folder}, ports), build.folder));
    const same = results.every(result => !result.not_run) && results.every(result => isDeepStrictEqual(result, results[0]));
    keys.set(item.key, !same);
    if (same) agreed++;
    else differences.push({source:item.source, topic:item.topic, entry_path:item.entry.entry_path, operation:item.entry.operation, input:item.input, results});
  }
  return {comparison:{inputs:collected.inputs.length, agreed, differences, dropped:collected.dropped}, keys};
}

const decisionList = folder => {
  const read = readJsonFile(join(folder, 'pdd-decisions.json'));
  if (read.reason) return {list:null, reason:read.reason};
  if (!Array.isArray(read.value)) return {list:null, reason:'pdd-decisions.json is not an array'};
  return {list:read.value.filter(object), reason:null};
};
const probeList = folder => {
  const read = readJsonFile(join(folder, 'pdd-probes.json'));
  if (read.reason) return {list:null, reason:read.reason};
  if (!Array.isArray(read.value)) return {list:null, reason:'pdd-probes.json is not an array'};
  return {list:read.value.filter(object), reason:null};
};
// An input separates the readings when the prober gave one outcome per reading and they are not all the same.
const separates = (input, readings) => object(input) && Array.isArray(input.outcomes) && Array.isArray(readings) && input.outcomes.length === readings.length &&
  new Set(input.outcomes.map(outcome => JSON.stringify(outcome))).size > 1;
const keyOf = item => object(item) && object(item.input) ? inputKey(item.entry_path, item.operation, item.input) : null;
const differs = (keys, key) => key && keys?.has(key) ? keys.get(key) : null;

function casesOf(stories) {
  const steps = stories.flatMap(story => story.steps);
  return {passed:steps.filter(step => step.status === 'passed').length, total:steps.length};
}

function summary(report) {
  const parts = [`Blind build: ${report.builds.map(build => build.cases ? `${build.cases.passed}/${build.cases.total}` : 'not finished').join(', ')} cases`];
  if (report.comparison) parts.push(`2 builds agree on ${report.comparison.agreed}/${report.comparison.inputs} inputs`);
  else if (report.builds.length === 2) parts.push('builds not compared');
  else parts.push('1 build');
  const decisionCount = report.decisions.reduce((sum, row) => sum + (row.list?.length ?? 0), 0);
  parts.push(report.probes ? `${decisionCount} decisions, ${report.probes.list?.length ?? 0} probes` : `${decisionCount} decisions`);
  return parts.join(' · ');
}

function textReport(report, paths) {
  const out = [summary(report)];
  const show = value => { const text = JSON.stringify(value); return text.length > 300 ? `${text.slice(0, 300)}…` : text; };
  // Without a progress file the last log line is often the only clue (a refused model, a missing login).
  const unfinished = (label, checkpoint, folder) => {
    const progress = checkpoint?.progress;
    out.push(`${label} not finished (${checkpoint?.reason}): doing ${progress?.doing ?? 'unknown'}; stuck on ${progress?.stuck_on ?? 'nothing reported'}`);
    if (!progress && checkpoint?.log_tail?.length) out.push(`  last log line: ${show(checkpoint.log_tail.at(-1))}`);
    out.push(`  folder ${folder}`);
  };
  for (const build of report.builds) if (!build.finished) unfinished(`build-${build.build}`, build.checkpoint, build.folder);
  if (report.probes?.checkpoint) unfinished('probe', report.probes.checkpoint, report.probes.folder);
  if (report.comparison_skipped) out.push(`Builds not compared: ${report.comparison_skipped}`);
  // Dropped inputs explain why a decision or probe was not compared.
  const dropped = report.comparison?.dropped ?? [];
  if (dropped.length) {
    const counts = new Map();
    for (const row of dropped) counts.set(row.reason, (counts.get(row.reason) ?? 0) + 1);
    out.push(`Dropped ${dropped.length} inputs, never run: ${[...counts].map(([reason, count]) => `${reason} (${count})`).join('; ')}`);
  }
  for (const difference of report.comparison?.differences ?? []) {
    out.push(`Differs (${difference.source}${difference.topic ? `: ${difference.topic}` : ''}): ${difference.entry_path} ${show(difference.input)}`);
    difference.results.forEach((result, index) => out.push(`  build-${index + 1}: ${show(result)}`));
  }
  const groups = {'Builds disagree':[], 'Reported, builds agree':[], 'Reported, no input separates the readings':[], 'Reported, not compared':[]};
  // Agreement on inputs that cannot tell the readings apart says nothing, so such a probe still needs a person.
  const group = item => item.differs === true ? 'Builds disagree' : item.separating_inputs === 0 ? 'Reported, no input separates the readings' : item.differs === false ? 'Reported, builds agree' : 'Reported, not compared';
  const place = (label, item) => groups[group(item)].push(`  ${label}: ${item.topic ?? '(no topic)'}${item.choice !== undefined ? ` — ${typeof item.choice === 'string' ? item.choice : show(item.choice)}` : ''}`);
  for (const row of report.decisions) {
    if (!row.list) out.push(`build-${row.build} decisions: ${row.reason}`);
    for (const item of row.list ?? []) place(`build-${row.build} decision`, item);
  }
  if (report.probes && !report.probes.list) out.push(`probes: ${report.probes.reason}`);
  for (const item of report.probes?.list ?? []) place('probe', item);
  for (const [label, lines] of Object.entries(groups)) if (lines.length) out.push(`${label}:`, ...lines);
  for (const build of report.builds) for (const story of build.stories) for (const step of story.steps) {
    if (step.status === 'not run') out.push(`build-${build.build} ${story.story} ${step.step_id}: not run: ${step.reason}`);
    for (const check of step.checks ?? []) if (check.status === 'failed') out.push(`build-${build.build} ${story.story} ${step.step_id} ${check.criterion_id} ${check.path}: expected ${show(check.expected)}, actual ${show(check.actual)}`);
  }
  out.push(`Manifest: ${paths.manifest}`, `Report: ${paths.report}`);
  return out.join('\n') + '\n';
}

function defaultId(now) {
  return `${new Date(now()).toISOString().replace(/[-:]/g, '').replace(/\.\d+Z$/, 'Z')}-${randomBytes(3).toString('hex')}`;
}

export async function runBlindBuild({root, words = [], builds = 1, agent = null, timeout = 30, resume = null, json = false}, ports = {}) {
  const {stdout, stderr} = ports;
  const spawn = ports.spawn ?? spawnSync, env = ports.env ?? process.env, now = ports.now ?? Date.now;
  const runAgent = ports.runAgent ?? nativeRunAgent;
  const timeoutMs = timeout * 60000;
  if (![1, 2].includes(builds)) { stderr.write('--builds must be 1 or 2.\n'); return 2; }

  // Resume reads the saved run; a fresh run picks the agent first so a bad name costs nothing.
  let state = null;
  const gitTop = spawn('git', ['rev-parse', '--show-toplevel'], {cwd:root, encoding:'utf8'});
  if (gitTop.status !== 0 || !gitTop.stdout?.trim()) { stderr.write('No Git project root is available.\n'); return 2; }
  const gitRoot = gitTop.stdout.trim();
  if (resume !== null) {
    if (!/^[A-Za-z0-9._-]+$/.test(resume)) { stderr.write(`Unknown blind build run: ${resume}\n`); return 2; }
    const saved = readJsonFile(join(gitRoot, '.pdd', 'blind-build', resume, 'state.json'));
    if (!object(saved.value)) { stderr.write(`Unknown blind build run: ${resume}\n`); return 2; }
    state = saved.value;
    words = state.words; builds = state.builds;
  }
  const definitions = ports.agents ?? loadAgentDefinitions({cwd:root, env});
  const wanted = state ? state.agent : agent;
  const chosen = wanted === null || wanted === undefined ? definitions[0]
    : definitions.find(d => [d.name, d.id].some(value => String(value).toLowerCase() === String(wanted).toLowerCase()));
  if (!chosen) { stderr.write(`Unknown agent: ${wanted}\n`); return 2; }

  const selection = codeTestReport({root, words, dry:true}, {spawn});
  if (selection.error) { stderr.write(`${selection.error}\n`); return 2; }
  if (!selection.runs.length) {
    const lines = selection.report.stories.flatMap(story => story.steps.filter(step => step.reason && step.reason !== 'Selection only.').map(step => `${story.story}: ${step.reason}`));
    stderr.write(`Blind build needs a Story with a CLI entry: ${lines.length ? lines.join('; ') : 'no runnable step'}\n`);
    return 2;
  }
  const entries = entriesOf(selection.runs);
  const files = packetFiles(gitRoot, selection.selected, selection.found, ports);
  const {commit, dirty} = selection.report;
  const id = state ? resume : (ports.id ?? (() => defaultId(now)))();
  const recordDir = join(gitRoot, '.pdd', 'blind-build', id);
  const manifest = state ? state.manifest : {id, commit, dirty, stories:selection.report.stories.map(story => story.story),
    files:files.map(({path, sha256:hash, bytes}) => ({path, sha256:hash, bytes})), excluded:EXCLUDED, isolation:'folder'};
  if (state) {
    const current = new Map(files.map(file => [file.path, file.sha256]));
    if (manifest.files.length !== files.length || manifest.files.some(file => current.get(file.path) !== file.sha256)) { stderr.write(`Blind build ${id}: the prompts changed since this run; start a new run.\n`); return 2; }
    if (!state.agents.every(agent => existsSync(agent.folder))) { stderr.write(`Blind build ${id}: the build folders are gone; start a new run.\n`); return 2; }
  } else if (!writeLocalReport(gitRoot, ['blind-build', id, 'manifest.json'], pretty(manifest), stderr)) return 1;

  // One folder per agent, outside the repository, holding only the packet.
  const base = state ? state.base : join(ports.tmpdir ?? osTmpdir(), `pdd-blind-${id}`);
  const agents = state ? state.agents : [
    ...Array.from({length:builds}, (_, index) => ({role:'build', name:`build-${index + 1}`, folder:join(base, `build-${index + 1}`), finished:false, checkpoint:null})),
    ...(builds === 2 ? [{role:'probe', name:'probe', folder:join(base, 'probe'), finished:false, checkpoint:null}] : []),
  ];
  if (!state) for (const item of agents) {
    for (const file of files) { mkdirSync(dirname(join(item.folder, file.path)), {recursive:true}); writeFileSync(join(item.folder, file.path), file.content); }
  }
  const childEnv = {...jobEnvironment(env, {stripGithubTokens:true}), ...chosen.env};
  const pending = agents.filter(item => !item.finished);
  const results = await Promise.all(pending.map(item => {
    const brief = (item.role === 'build' ? builderBrief : proberBrief)({folder:item.folder, entries, checkpoint:item.checkpoint});
    const log = join(recordDir, `${item.name}.log`);
    return Promise.resolve(runAgent({agent:chosen, cwd:item.folder, input:brief, env:childEnv, log, timeoutMs})).then(result => ({item, log, result}));
  }));
  for (const {item, log, result} of results) Object.assign(item, outcomeOf(result ?? {code:1}, item.folder, log));

  const buildAgents = agents.filter(item => item.role === 'build');
  // Only a finished build is checked and compared; an unfinished one keeps its folder and checkpoint.
  const buildRows = buildAgents.map((item, index) => {
    if (!item.finished) return {build:index + 1, folder:item.folder, finished:false, checkpoint:item.checkpoint, cases:null, stories:[]};
    const checked = codeTestReport({root, words, implementationRoot:item.folder}, {spawn});
    const stories = checked.report?.stories ?? [];
    return {build:index + 1, folder:item.folder, finished:item.finished, checkpoint:item.checkpoint, cases:casesOf(stories), stories};
  });
  const decisionRows = buildAgents.map((item, index) => ({build:index + 1, ...decisionList(item.folder)}));
  const probeAgent = agents.find(item => item.role === 'probe');
  const probeRead = probeAgent ? probeList(probeAgent.folder) : null;
  let comparison = null, keys = null;
  const notFinished = buildRows.filter(build => !build.finished).map(build => `build-${build.build}`);
  const comparisonSkipped = builds === 2 && notFinished.length ? `${notFinished.join(', ')} not finished` : null;
  if (builds === 2 && !comparisonSkipped) {
    const collected = collectInputs({runs:selection.runs, decisions:decisionRows.map(row => row.list), probes:probeRead.list, entries});
    ({comparison, keys} = compare(buildRows, collected, {spawn}));
  }
  const decisions = decisionRows.map(row => ({build:row.build, reason:row.reason, list:row.list?.map(item => ({...item, differs:differs(keys, keyOf(item.example))})) ?? null}));
  const probes = probeAgent ? {folder:probeAgent.folder, finished:probeAgent.finished, checkpoint:probeAgent.checkpoint, reason:probeRead.reason,
    list:probeRead.list?.map(item => {
      const inputs = Array.isArray(item.inputs) ? item.inputs : [];
      const marks = inputs.map(input => differs(keys, keyOf(input))).filter(mark => mark !== null);
      return {...item, differs:marks.includes(true) ? true : marks.length ? false : null, separating_inputs:inputs.filter(input => separates(input, item.readings)).length};
    }) ?? null} : null;
  const report = {target:'blind-build', id, commit, dirty, agent_runs:pending.length, agent:chosen.name, isolation:'folder', manifest, builds:buildRows, comparison, ...(comparisonSkipped ? {comparison_skipped:comparisonSkipped} : {}), decisions, probes};

  const saved = {words:[...words], builds, agent:chosen.name, base, manifest, agents:agents.map(({role, name, folder, finished, checkpoint}) => ({role, name, folder, finished, checkpoint}))};
  const text = pretty(report);
  if (!writeLocalReport(gitRoot, ['blind-build', id, 'state.json'], pretty(saved), stderr)) return 1;
  if (!writeLocalReport(gitRoot, ['blind-build', id, 'report.json'], text, stderr)) return 1;
  if (!writeLocalReport(gitRoot, ['blind-build', 'latest.json'], text, stderr)) return 1;
  const paths = {manifest:join('.pdd', 'blind-build', id, 'manifest.json'), report:join('.pdd', 'blind-build', id, 'report.json')};
  stdout.write(json ? stringifyScenarioJson(report) + '\n' : textReport(report, paths));

  const passed = buildRows.every(build => build.finished && build.cases?.total > 0 && build.cases.passed === build.cases.total);
  const agree = !comparison || (comparison.differences.length === 0 && (!probes || probes.finished));
  return commit && passed && agree ? 0 : 1;
}
