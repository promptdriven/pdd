import { test, after } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, existsSync, readdirSync, chmodSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, relative } from 'node:path';
import { spawnSync } from 'node:child_process';
import { proseSha256 } from '../src/runtime-seam.mjs';
import { runBlindBuild, nativeRunAgent } from '../src/autopilot/blind-build.mjs';

const bin = join(process.cwd(), 'bin/pdd.mjs');
const roots = [];
after(() => { for (const root of roots) rmSync(root, {recursive:true, force:true}); });
const temp = prefix => { const dir = mkdtempSync(join(tmpdir(), prefix)); roots.push(dir); return dir; };

// A one-entry CLI project: `node app.mjs WORD` prints WORD upper-cased. The Story checks one input.
const APP = "const w=process.argv[2]??'';if(w==='-0'){process.stderr.write('bad\\n');process.exitCode=2;}else process.stdout.write(w.toUpperCase()+'\\n');\n";
function project() {
  const root = temp('pdd-blind-project-');
  spawnSync('git', ['init', '-q', root]);
  for (const d of ['prompts', 'tests', 'user_stories']) mkdirSync(join(root, d));
  const iface = {status:'draft', prose_sha256:'HASH', entries:[{operation:'main', implementation:{kind:'cli', command:'node app.mjs'},
    input_schema:{type:'object', properties:{argv:{type:'array', items:{type:'string'}}, stdin:{type:'string'}}, required:['argv'], additionalProperties:false},
    result_schema:{type:'object', properties:{stdout:{type:'string'}, stderr:{type:'string'}, exit_code:{type:'integer'}}, required:['stdout', 'stderr', 'exit_code'], additionalProperties:false}, errors:[]}],
    resources:[], conventions:[{path:'/entries/0/input_schema', convention:'cli'}, {path:'/entries/0/result_schema', convention:'cli'}], calls:[], limits:{max_steps:4, max_model_calls:2}};
  const prompt = '# shout\n\nPrint the word in capitals. See [style](style.prompt.md).\n\n## Dependencies\n\n- [Style](style.prompt.md)\n\n<details><summary>Runtime interface</summary>\n\n```json\n' + JSON.stringify(iface) + '\n```\n</details>\n';
  writeFileSync(join(root, 'prompts/shout.prompt.md'), prompt.replace('HASH', proseSha256(prompt)));
  writeFileSync(join(root, 'prompts/style.prompt.md'), '# Style\n\nEnd each line with a newline.\n');
  writeFileSync(join(root, 'app.mjs'), '// Generated from prompts/shout.prompt.md\n' + APP);
  writeFileSync(join(root, 'user_stories/shout.md'), '# Shout\n\n## Acceptance criteria\n\n1. A word comes back in capitals.\n');
  const doc = {schema_version:'prompt-runtime.program-scenario.v1', story_path:'user_stories/shout.md', criteria:[{id:'AC1', text:'A word comes back in capitals.'}],
    initial_world:{}, simulation:{}, context:[], steps:[{step_id:'one', entry_path:'prompts/shout.prompt.md', operation:'main', input:{argv:['hi']},
      checks:[{criterion_id:'AC1', target:'result', path:'/stdout', op:'equals', value:'HI\n'}, {criterion_id:'AC1', target:'result', path:'/exit_code', op:'equals', value:0}]}]};
  writeFileSync(join(root, 'tests/shout.json'), JSON.stringify(doc));
  spawnSync('git', ['add', '.'], {cwd:root});
  spawnSync('git', ['-c', 'user.name=test', '-c', 'user.email=test@example.com', 'commit', '-qm', 'fixture'], {cwd:root});
  return root;
}

const EXAMPLE = argv => ({entry_path:'prompts/shout.prompt.md', operation:'main', input:{argv}});
// A fake agent port: a builder writes app.mjs (optionally a variant) and its decisions; the prober writes probes.
function fakeAgents({app = APP, variant = null, decisions = [{topic:'empty word', prompt_says:'silent', choice:'print an empty line', example:EXAMPLE([''])}],
  probes = [{topic:'negative zero', readings:['a word', 'an error'], inputs:[EXAMPLE(['-0'])]}], outcome = () => ({code:0})} = {}) {
  const calls = [];
  const runAgent = async request => {
    calls.push({...request, seen:readdirSync(request.cwd, {recursive:true}).sort()});
    const index = calls.length;
    const result = outcome(request, index);
    if (result.skipWork) return result;
    if (request.input.includes('Do not write code')) writeFileSync(join(request.cwd, 'pdd-probes.json'), JSON.stringify(probes));
    else {
      const builds = calls.filter(call => !call.input.includes('Do not write code')).length;
      writeFileSync(join(request.cwd, 'app.mjs'), builds === 2 && variant ? variant : app);
      writeFileSync(join(request.cwd, 'pdd-decisions.json'), JSON.stringify(decisions));
    }
    writeFileSync(join(request.cwd, 'pdd-progress.json'), JSON.stringify({status:'done', done:['all'], doing:null, stuck_on:null}));
    return result;
  };
  return {calls, runAgent};
}
const AGENTS = [{name:'Fake', id:'fake', kind:'codex', command:'fake-agent', env:{EXTRA:'1'}}];
async function blind(root, options = {}, ports = {}) {
  let out = '', err = '';
  const code = await runBlindBuild({root, words:['shout'], ...options}, {stdout:{write:s => { out += s; }}, stderr:{write:s => { err += s; }},
    agents:AGENTS, tmpdir:temp('pdd-blind-tmp-'), env:{PATH:process.env.PATH, HOME:process.env.HOME, GH_TOKEN:'secret', GITHUB_TOKEN:'secret'}, ...ports});
  return {code, out, err, report:existsSync(join(root, '.pdd/blind-build/latest.json')) ? JSON.parse(readFileSync(join(root, '.pdd/blind-build/latest.json'), 'utf8')) : null};
}

test('a builder gets only the prompts and their dependencies, outside the repository, and its build passes the cases', async () => {
  const root = project(), agents = fakeAgents();
  const {code, out, report} = await blind(root, {}, {runAgent:agents.runAgent, id:() => 'one'});
  assert.equal(code, 0, out);
  assert.match(out, /^Blind build: 1\/1 cases · 1 build · 1 decisions$/m);
  assert.equal(agents.calls.length, 1);
  const [call] = agents.calls;
  assert.deepEqual(call.seen, ['prompts', 'prompts/shout.prompt.md', 'prompts/style.prompt.md']);
  assert.ok(relative(root, call.cwd).startsWith('..'), 'the build folder is outside the repository');
  assert.equal(call.env.GH_TOKEN, undefined); assert.equal(call.env.GITHUB_TOKEN, undefined); assert.equal(call.env.EXTRA, '1');
  assert.match(call.input, /Read only the files in this folder/);
  assert.match(call.input, /prompts\/shout\.prompt\.md \(operation main\): node app\.mjs/);
  assert.match(call.input, /pdd-progress\.json/);
  // The brief shows each entry's input schema and never suggests fields that the schema may not have.
  assert.ok(call.input.includes('input schema: {"type":"object"'));
  assert.match(call.input, /use only the fields the schema lists/);
  assert.doesNotMatch(call.input, /"stdin": "\.\.\."/);
  const manifest = JSON.parse(readFileSync(join(root, '.pdd/blind-build/one/manifest.json'), 'utf8'));
  assert.deepEqual(manifest.files.map(file => file.path), ['prompts/shout.prompt.md', 'prompts/style.prompt.md']);
  assert.match(manifest.files[0].sha256, /^[0-9a-f]{64}$/);
  assert.equal(manifest.isolation, 'folder');
  assert.ok(manifest.excluded.includes('user_stories/') && manifest.excluded.includes('tests/') && manifest.excluded.includes('code'));
  assert.equal(report.builds[0].cases.passed, 1); assert.equal(report.comparison, null);
  assert.equal(report.decisions[0].list[0].differs, null);
  assert.equal(existsSync(join(report.builds[0].folder, 'app.mjs')), true, 'the build folder is kept');
});

test('two builds that read the prompt differently are caught, and decisions and probes are grouped by evidence', async () => {
  const root = project();
  const variant = "const w=process.argv[2]??'';process.stdout.write(w.toUpperCase()+'\\n');\n";
  const agents = fakeAgents({variant});
  const {code, out, report} = await blind(root, {builds:2}, {runAgent:agents.runAgent, id:() => 'two'});
  assert.equal(code, 1, 'a difference fails the check');
  assert.equal(agents.calls.length, 3);
  const probeCall = agents.calls.find(call => call.input.includes('Do not write code'));
  assert.ok(probeCall && !probeCall.input.includes('pdd-decisions.json'));
  assert.match(out, /^Blind build: 1\/1, 1\/1 cases · 2 builds agree on 2\/3 inputs · 2 decisions, 1 probes$/m);
  assert.equal(report.comparison.differences.length, 1);
  const [difference] = report.comparison.differences;
  assert.equal(difference.source, 'probe'); assert.deepEqual(difference.input, {argv:['-0']});
  assert.deepEqual(difference.results.map(result => result.exit_code), [2, 0]);
  assert.equal(report.probes.list[0].differs, true);
  assert.equal(report.decisions[0].list[0].differs, false);
  assert.match(out, /Builds disagree:\n  probe: negative zero/);
  assert.match(out, /Reported, builds agree:\n  build-1 decision: empty word/);
});

test('a build folder path in the output is not a difference between builds', async () => {
  const root = project();
  // Both builds print their own working folder in the error, as a stack trace or a file error would.
  const app = "const w=process.argv[2]??'';if(w==='-0'){process.stderr.write('bad input in '+process.cwd()+'\\n');process.exitCode=2;}else process.stdout.write(w.toUpperCase()+'\\n');\n";
  const agents = fakeAgents({app});
  const {code, out, report} = await blind(root, {builds:2}, {runAgent:agents.runAgent});
  assert.equal(code, 0, out);
  assert.equal(report.comparison.differences.length, 0);
  assert.equal(report.comparison.agreed, 3);
  assert.equal(report.probes.list[0].differs, false);
});

test('a build that did not finish is neither checked nor compared, and its last log line is shown', async () => {
  const root = project();
  const agents = fakeAgents({outcome:(request, index) => {
    if (index !== 2) return {code:0};
    writeFileSync(request.log, '{"type":"turn.started"}\n{"type":"turn.failed","error":{"message":"model is not supported"}}\n');
    return {code:1, skipWork:true};
  }});
  const {code, out, report} = await blind(root, {builds:2}, {runAgent:agents.runAgent});
  assert.equal(code, 1);
  assert.equal(report.builds[1].finished, false);
  assert.equal(report.builds[1].cases, null); assert.deepEqual(report.builds[1].stories, []);
  assert.equal(report.builds[0].cases.passed, 1);
  assert.equal(report.comparison, null); assert.equal(report.comparison_skipped, 'build-2 not finished');
  assert.match(out, /^Blind build: 1\/1, not finished cases · builds not compared · 1 decisions, 1 probes$/m);
  assert.match(out, /build-2 not finished \(exit 1\): doing unknown; stuck on nothing reported\n  last log line: .*model is not supported/);
  assert.match(out, /Builds not compared: build-2 not finished/);
  assert.doesNotMatch(out, /^Differs/m);
});

test('the prober is asked the general questions and for one outcome per reading, and a probe whose inputs cannot tell its readings apart still needs a person', async () => {
  const root = project();
  const agents = fakeAgents({probes:[
    {topic:'which value', readings:['before', 'after'], inputs:[{...EXAMPLE(['x']), outcomes:['X', 'X']}]},
    {topic:'empty word', readings:['blank line', 'error'], inputs:[{...EXAMPLE(['']), outcomes:['prints a blank line', 'exits 2']}]},
  ]});
  const {out, report} = await blind(root, {builds:2}, {runAgent:agents.runAgent});
  const brief = agents.calls.find(call => call.input.includes('Do not write code')).input;
  for (const question of ['Which value is meant', 'Same value, different form', 'Edges', 'Rules that overlap', 'What the prompt never mentions', 'Parts that must agree', 'Order and format'])
    assert.ok(brief.includes(question), question);
  assert.match(brief, /outcomes has one entry per reading/);
  assert.match(brief, /if every reading gives the same outcome, the input cannot tell them apart/);
  assert.deepEqual(report.probes.list.map(item => [item.topic, item.differs, item.separating_inputs]), [['which value', false, 0], ['empty word', false, 1]]);
  assert.match(out, /Reported, builds agree:\n(  .*\n)*  probe: empty word/);
  assert.match(out, /Reported, no input separates the readings:\n  probe: which value/);
});

test('an input that the entry schema does not admit is dropped with a reason and never run', async () => {
  const root = project();
  const agents = fakeAgents({probes:[{topic:'numbers', readings:['x'], inputs:[EXAMPLE([3]), {entry_path:'prompts/other.prompt.md', operation:'main', input:{argv:['x']}}]}]});
  const {out, report} = await blind(root, {builds:2}, {runAgent:agents.runAgent});
  assert.deepEqual(report.comparison.dropped.map(row => row.reason).sort(), ['CLI input is unsupported', 'not a runnable CLI entry']);
  assert.match(out, /^Dropped 2 inputs, never run: (CLI input is unsupported \(1\); not a runnable CLI entry \(1\)|not a runnable CLI entry \(1\); CLI input is unsupported \(1\))$/m);
  assert.equal(report.probes.list[0].differs, null);
});

test('an unfinished agent leaves a checkpoint, and --resume continues only that agent in the same folder', async () => {
  const root = project();
  let stop = true;
  const agents = fakeAgents({outcome:(request, index) => {
    if (index === 1 && stop) {
      writeFileSync(join(request.cwd, 'pdd-progress.json'), JSON.stringify({status:'working', done:['parse arguments'], doing:'upper-case output', stuck_on:'node app.mjs exits 1: SyntaxError'}));
      writeFileSync(request.log, 'line 1\nSyntaxError: Unexpected token\n');
      return {code:null, timedOut:true, skipWork:true};
    }
    return {code:0};
  }});
  const first = await blind(root, {timeout:1}, {runAgent:agents.runAgent, id:() => 'slow'});
  assert.equal(first.code, 1);
  assert.equal(first.report.builds[0].finished, false);
  assert.deepEqual(first.report.builds[0].checkpoint.progress.done, ['parse arguments']);
  assert.equal(first.report.builds[0].checkpoint.reason, 'time limit');
  assert.deepEqual(first.report.builds[0].checkpoint.log_tail, ['line 1', 'SyntaxError: Unexpected token']);
  assert.match(first.out, /build-1 not finished \(time limit\): doing upper-case output; stuck on node app\.mjs exits 1: SyntaxError/);
  assert.equal(agents.calls[0].timeoutMs, 60000);
  const folder = first.report.builds[0].folder;
  stop = false;
  const second = await blind(root, {resume:'slow', words:[]}, {runAgent:agents.runAgent});
  assert.equal(second.code, 0, second.out + second.err);
  assert.equal(agents.calls.length, 2);
  assert.equal(agents.calls[1].cwd, folder);
  assert.match(agents.calls[1].input, /continue from this checkpoint:/);
  assert.match(agents.calls[1].input, /upper-case output/);
  assert.equal(second.report.id, 'slow'); assert.equal(second.report.builds[0].finished, true);
});

test('--resume refuses an unknown run and a run whose prompts changed', async () => {
  const root = project();
  const unknown = await blind(root, {resume:'nope', words:[]}, {runAgent:fakeAgents().runAgent});
  assert.equal(unknown.code, 2); assert.match(unknown.err, /Unknown blind build run: nope/);
  const agents = fakeAgents({outcome:() => ({code:1, skipWork:true})});
  await blind(root, {}, {runAgent:agents.runAgent, id:() => 'changed'});
  writeFileSync(join(root, 'prompts/style.prompt.md'), '# Style\n\nEnd each line with two newlines.\n');
  const changed = await blind(root, {resume:'changed', words:[]}, {runAgent:agents.runAgent});
  assert.equal(changed.code, 2); assert.match(changed.err, /prompts changed since this run/);
  assert.equal(agents.calls.length, 1);
});

test('an unknown agent name stops before any work, and a Story without a CLI entry cannot be built', async () => {
  const root = project(), agents = fakeAgents();
  const unknown = await blind(root, {agent:'nobody'}, {runAgent:agents.runAgent});
  assert.equal(unknown.code, 2); assert.match(unknown.err, /Unknown agent: nobody/);
  const prompt = join(root, 'prompts/shout.prompt.md');
  writeFileSync(prompt, readFileSync(prompt, 'utf8').replace('"command":"node app.mjs"', '"command":"node app.mjs; rm -rf x"'));
  const none = await blind(root, {}, {runAgent:agents.runAgent});
  assert.equal(none.code, 2); assert.match(none.err, /Blind build needs a Story with a CLI entry/);
  assert.equal(agents.calls.length, 0);
});

test('the native agent runner stops the agent at its time limit and keeps its log', async () => {
  const dir = temp('pdd-blind-native-'), agent = join(dir, 'agent.sh'), log = join(dir, 'agent.log');
  writeFileSync(agent, '#!/bin/sh\necho started\nsleep 30\n'); chmodSync(agent, 0o755);
  const started = Date.now();
  const result = await nativeRunAgent({agent:{kind:'codex', command:agent}, cwd:dir, input:'brief', env:process.env, log, timeoutMs:3000});
  assert.equal(result.timedOut, true);
  assert.ok(Date.now() - started < 15000);
  assert.match(readFileSync(log, 'utf8'), /started/);
});

test('the CLI routes --blind-build and refuses mixed options before any agent runs', () => {
  const root = project();
  const run = args => spawnSync(process.execPath, [bin, 'test', ...args], {cwd:root, encoding:'utf8', env:{...process.env, GH_TOKEN:'', GITHUB_TOKEN:'', PDD_RUNTIME_URL:'http://127.0.0.1:1'}});
  const mixed = run(['--blind-build', '--resume', 'x', 'shout']);
  assert.equal(mixed.status, 2); assert.match(mixed.stderr, /--resume ID takes no Stories/);
  const other = run(['--blind-build', '--lf']);
  assert.equal(other.status, 2); assert.match(other.stderr, /accepts only --builds/);
  const unknown = run(['--blind-build', '--resume', 'missing']);
  assert.equal(unknown.status, 2); assert.match(unknown.stderr, /Unknown blind build run: missing/);
  // Option values arrive as text: --builds 2 must reach the agent check, not fail as an invalid build count.
  const two = run(['--blind-build', '--builds', '2', '--timeout', '5', '--agent', 'no-such-agent', 'shout']);
  assert.equal(two.status, 2); assert.doesNotMatch(two.stderr, /--builds must be/); assert.match(two.stderr, /Unknown agent: no-such-agent/);
});
