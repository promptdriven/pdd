import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync, existsSync, mkdirSync, rmSync, readdirSync} from 'node:fs';
import {join} from 'node:path';
import {Readable} from 'node:stream';
import {spawn, spawnSync} from 'node:child_process';
import * as client from '../src/runtime-client.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
import {parseArgv} from '../src/argument-parser.mjs';
import {proseSha256} from '../src/runtime-preflight.mjs';
import {harbor, fakeRuntime, portsFor, PLACE, TOKEN} from './runtime-fake.mjs';

// Story vectors exercise the real shared engine without a Story, then the save
// and pdd test boundaries. The controlled owner proves local replay, not AI.
const result = {stdout: 'Done #4: Call mom\n', stderr: '', exit_code: 0};
const initial = {kv: {todos: [{id: 4, text: 'Call mom', done: false}]}};
const after = {kv: {todos: [{id: 4, text: 'Call mom', done: true}]}};
const input = {argv: ['done', '4']};
const file = 'tests/finish-task.json';
const object = properties => ({type: 'object', properties, required: Object.keys(properties), additionalProperties: false});
function terminal(ports, answer = 'y\n') {
  ports.stdin = Readable.from([answer]); ports.stdin.isTTY = true;
  ports.stdout.isTTY = true;
  return ports;
}
async function recorded(t, observation = {input_world: initial, world: after}) {
  const setup = harbor(t, root => {
    rmSync(join(root, 'tests'), {recursive: true}); mkdirSync(join(root, 'tests'));
    rmSync(join(root, 'user_stories'), {recursive: true}); mkdirSync(join(root, 'user_stories'));
    const iface = {status: 'draft', prose_sha256: '', entries: [{operation: 'main',
      input_schema: object({argv: {type: 'array', items: {type: 'string'}}}),
      result_schema: object({stdout: {type: 'string'}, stderr: {type: 'string'}, exit_code: {type: 'integer'}}), errors: []}],
      calls: [], resources: [], limits: {max_steps: 1, max_model_calls: 1},
      conventions: ['input_schema', 'result_schema'].map(key => ({path: '/entries/0/' + key, convention: 'cli'}))};
    const content = () => '# todo\n\nFor done 4, finish task 4 and print Done #4: Call mom followed by a newline. For list, print 4: Call mom followed by a newline without changing the data.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n```json\n' + JSON.stringify(iface) + '\n```\n</details>\n';
    iface.prose_sha256 = proseSha256(content()); writeFileSync(join(root, PLACE), content());
  });
  let savedDoc, checks = [];
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.json) {
      const answer = f.job(entry.json.requestId, 'call', 'passed', {program_result: result, report: observation}, 1);
      f.jobs.set(answer.id, answer); return {status: 200, json: answer};
    }
    const id = entry.url.split('/').at(-1);
    if (f.jobs.has(id)) return {status: 200, json: f.jobs.get(id)};
    if (entry.command === 'lint') return {status: 200, json: f.lint(entry.request.requestId)};
    if (entry.command === 'check') {
      const unpack = spawnSync('tar', ['-xOf', '-', file], {input: entry.tar});
      assert.equal(unpack.status, 0, unpack.stderr.toString()); savedDoc = JSON.parse(unpack.stdout);
      // An independent tiny todo oracle checks every uploaded result check.
      checks = savedDoc.steps.flatMap(step => step.checks.map(check => {
        const finishing = step.input.argv[0] === 'done';
        const output = finishing ? result : {stdout: '4: Call mom\n', stderr: '', exit_code: 0};
        const actual = check.target === 'world' ? (finishing ? after : initial) : check.path === '/stdout' ? output.stdout : output;
        assert.deepEqual(actual, check.value, 'saved case must replay with the required answer');
        return {...check, expected: check.value, actual, passed: true};
      }));
      return {status: 202, json: f.check(entry.request.requestId, 'queued')};
    }
    return {status: 200, json: f.check(id, 'passed', checks)};
  });
  const env = {HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin};
  const io = () => portsFor(env, {stdin: Readable.from([]), caseHandoff: async ({testPath}) => ({kind: 'closed-editor', testPath})}).ports;
  assert.equal(existsSync(join(setup.repo, file)), false, 'the run has no Story or test');
  await client.runDoorCall({root: setup.repo, origin: fake.origin, sessionId: '11111111-1111-4111-8111-111111111111', login: 'octo', prompt: PLACE, operation: 'main'}, input, io());
  // The person chooses a Story only after running the command.
  const storyPath = 'user_stories/finish-task.md', criterion = 'Task 4 can be finished.';
  writeFileSync(join(setup.repo, storyPath), '# Finish task\n\nI can finish a task.\n\n## Acceptance criteria\n\n1. ' + criterion + '\n');
  const doc = {schema_version: 'prompt-runtime.program-scenario.v1', story_path: storyPath,
    criteria: [{id: 'AC1', text: criterion}], initial_world: initial, simulation: {}, context: [], steps: [{
      step_id: 'prior', entry_path: PLACE, operation: 'main', input: {argv: ['list']}, checks: [
        {criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: '4: Call mom\n'},
        {criterion_id: 'AC1', target: 'world', path: '', op: 'equals', value: initial}]}]};
  writeFileSync(join(setup.repo, file), JSON.stringify(doc, null, 2) + '\n');
  return {...setup, fake, io, doc, savedDoc: () => savedDoc};
}
const save = (f, ports) => client.runSaveLast({cwd: f.repo, words: ['finish-task'], options: {'--save-last': true}}, ports);

test('AC1/2/5: confirm a Story-free run, append exactly once, and replay it through pdd test', async t => {
  assert.equal(typeof client.runSaveLast, 'function');
  const f = await recorded(t), io = terminal(f.io()), before = readFileSync(join(f.repo, file), 'utf8');
  assert.equal(await save(f, io), 0, io.stderr.text);
  assert.ok(io.stdout.text.indexOf('Input:') < io.stdout.text.indexOf('Data before:'));
  assert.ok(io.stdout.text.indexOf('Data before:') < io.stdout.text.indexOf('Output:'));
  assert.ok(io.stdout.text.indexOf('Output:') < io.stdout.text.indexOf('Is this answer right? [y/N]'));
  assert.ok(io.stdout.text.includes(JSON.stringify(initial, null, 2)));
  const doc = JSON.parse(readFileSync(join(f.repo, file))), step = doc.steps[1];
  assert.deepEqual(doc.steps[0], f.doc.steps[0]); assert.deepEqual(doc.initial_world, initial);
  assert.deepEqual(step.input, input); assert.deepEqual(step.checks[0].value, result);
  assert.equal(io.stdout.text.split('\n').at(-2), `Added to ${file} as step ${step.step_id}. Review the data before this step, then run: pdd test finish-task`);
  assert.equal(readFileSync(join(f.repo, file), 'utf8').split('"steps"')[0], before.split('"steps"')[0]);
  assert.equal(await save(f, f.io()), 0); assert.equal(JSON.parse(readFileSync(join(f.repo, file))).steps.length, 2);
  const replay = f.io(); assert.equal(await client.runCheck({cwd: f.repo, words: ['finish-task']}, replay), 0, replay.stderr.text + replay.stdout.text);
  assert.deepEqual(f.savedDoc().steps[1], step); assert.equal(f.fake.jsonPosts.length, 1, 'saving must not execute the command again');
});

test('AC2: retry after a lost saved flag reports the committed collision-resolved step', async t => {
  const f = await recorded(t), repoDir = join(f.state, 'repos');
  const repoFile = join(repoDir, readdirSync(repoDir)[0]);
  const repo = JSON.parse(readFileSync(repoFile, 'utf8'));
  const proposed = `try-${repo.last_run.id}`;
  const doc = JSON.parse(readFileSync(join(f.repo, file), 'utf8'));
  doc.steps[0].step_id = proposed;
  writeFileSync(join(f.repo, file), JSON.stringify(doc, null, 2) + '\n');
  const first = terminal(f.io());
  assert.equal(await save(f, first), 0, first.stderr.text);
  const published = readFileSync(join(f.repo, file), 'utf8');
  assert.equal(JSON.parse(published).steps[1].step_id, `${proposed}-2`);
  const savedRepo = JSON.parse(readFileSync(repoFile, 'utf8'));
  delete savedRepo.last_run.saved;
  writeFileSync(repoFile, JSON.stringify(savedRepo));
  const retry = terminal(f.io());
  assert.equal(await save(f, retry), 0, retry.stderr.text);
  assert.match(retry.stdout.text, new RegExp(`as step ${proposed}-2\\.`));
  assert.equal(readFileSync(join(f.repo, file), 'utf8'), published);
});

for (const answer of ['N\n', '\n', 'yes\n', 'wrong\n', '']) test(`AC3: ${JSON.stringify(answer)} writes no case or pending receipt`, async t => {
  const f = await recorded(t), before = readFileSync(join(f.repo, file), 'utf8'), io = terminal(f.io(), answer);
  io.caseHandoff = () => assert.fail('a declined expectation cannot hand off a file');
  assert.equal(await save(f, io), 0, io.stderr.text);
  assert.equal(readFileSync(join(f.repo, file), 'utf8'), before);
  assert.equal(existsSync(join(f.state, 'case-import')), false);
  assert.match(io.stdout.text, /right expected value by hand/);
});

for (const [stdinTTY, stdoutTTY] of [[false, false], [false, true], [true, false]]) test(`AC4: terminal flags ${stdinTTY}/${stdoutTTY} cannot save`, async t => {
  const f = await recorded(t), before = readFileSync(join(f.repo, file), 'utf8'), io = f.io();
  io.interactive = true; io.stdout.isTTY = stdoutTTY;
  io.stdin = {isTTY: stdinTTY, [Symbol.asyncIterator]() { assert.fail('headless save cannot consume input'); }};
  io.caseHandoff = () => assert.fail('editor handoff cannot approve an answer');
  assert.equal(await save(f, io), 125); assert.match(io.stderr.text, /person must answer.*terminal/);
  assert.equal(readFileSync(join(f.repo, file), 'utf8'), before); assert.equal(existsSync(join(f.state, 'case-import')), false);
});

test('AC6: changed prompt, missing data and incompatible data cannot be committed', async t => {
  for (const mode of ['changed', 'missing', 'incompatible']) {
    const f = await recorded(t, mode === 'missing' ? {} : mode === 'incompatible' ? {input_world: after, world: after} : undefined);
    if (mode === 'changed') writeFileSync(join(f.repo, PLACE), readFileSync(join(f.repo, PLACE), 'utf8') + '\nChanged.\n');
    const before = readFileSync(join(f.repo, file), 'utf8'), io = terminal(f.io());
    assert.equal(await save(f, io), 125, mode); assert.equal(readFileSync(join(f.repo, file), 'utf8'), before);
    assert.match(io.stderr.text, mode === 'changed' ? /prompt changed/ : mode === 'missing' ? /confirmed data before/ : /starting world/);
  }
});

test('AC6: a refused later call invalidates the previous saveable run', async t => {
  const f = await recorded(t), io = f.io(); io.signal = AbortSignal.abort();
  await assert.rejects(client.runDoorCall({root: f.repo, origin: f.fake.origin, sessionId: '11111111-1111-4111-8111-111111111111', login: 'octo', prompt: PLACE, operation: 'main'}, input, io));
  const saving = terminal(f.io()); assert.equal(await save(f, saving), 125); assert.match(saving.stderr.text, /unknown/);
  assert.equal(JSON.parse(readFileSync(join(f.repo, file))).steps.length, 1);
});

test('CLI catalogs save-last, forwards stdin and refuses saving with a pipe', async t => {
  assert.doesNotThrow(() => parseArgv(['run', '--save-last', 'finish-task']), 'save-last must be a public command');
  assert.equal(parseArgv(['run', '--save-last', 'finish-task']).local, 'runtime-save');
  const f = await recorded(t), tools = join(f.sandbox, 'tools'); mkdirSync(tools);
  writeFileSync(join(tools, 'gh'), `#!/bin/sh\nif [ "$1" = auth ]; then echo ${TOKEN}; else echo 'octo 4242'; fi\n`, {mode: 0o700});
  const io = f.io(), env = {...io.env, PATH: tools + ':' + process.env.PATH};
  assert.equal(await runPdd(['run', '--save-last', 'finish-task'], {cwd: f.repo, env, stdin: io.stdin, stdout: io.stdout, stderr: io.stderr}), 125);
  assert.match(io.stderr.text, /person must answer.*terminal/);
  const accepted = terminal(f.io(), 'y\ny\n');
  assert.equal(await runPdd(['run', '--save-last', 'finish-task'], {cwd: f.repo, env, stdin: accepted.stdin, stdout: accepted.stdout, stderr: accepted.stderr}), 0, accepted.stderr.text);
  assert.equal(JSON.parse(readFileSync(join(f.repo, file))).steps.length, 2);
});

test('AC6: an older completion cannot make a newer unknown run saveable', async t => {
  const f = await recorded(t), descriptor = {root: f.repo, origin: f.fake.origin,
    sessionId: '11111111-1111-4111-8111-111111111111', login: 'octo', prompt: PLACE, operation: 'main'};
  let release, started;
  const sent = new Promise(done => { started = done; });
  const waiting = new Promise(done => { release = done; });
  let answer;
  const older = f.io(); older.fetch = async (_url, init) => {
    if (init.method === 'POST') {
      const request = JSON.parse(init.body);
      answer = f.fake.job(request.requestId, 'call', 'passed', {program_result: result, report: {input_world: initial, world: after}}, 1);
      started(); await waiting;
    }
    return new Response(JSON.stringify(answer), {status: 200});
  };
  const oldCall = client.runDoorCall(descriptor, input, older); await sent;
  const newer = f.io(); newer.signal = AbortSignal.abort();
  await assert.rejects(client.runDoorCall(descriptor, input, newer));
  release(); await oldCall;
  const saving = terminal(f.io()); assert.equal(await save(f, saving), 125);
  assert.match(saving.stderr.text, /unknown/); assert.equal(JSON.parse(readFileSync(join(f.repo, file))).steps.length, 1);
});

test('AC6: a pending Try cannot restore an older confirmed run', {timeout: 10000}, async t => {
  const f = await recorded(t), repoDir = join(f.state, 'repos');
  const repoFile = join(repoDir, readdirSync(repoDir).find(name => name.endsWith('.json')));
  const repo = JSON.parse(readFileSync(repoFile, 'utf8'));
  repo.unrelated = {keep: 'value'};
  writeFileSync(repoFile, JSON.stringify(repo));
  let release, started;
  const paused = new Promise(resolve => { started = resolve; });
  const waiting = new Promise(resolve => { release = resolve; });
  const trying = f.io();
  trying.fetch = async (url, init) => {
    if (String(url).endsWith('/v1/lint') && init.method === 'POST') { started(); await waiting; }
    return fetch(url, init);
  };
  const pending = client.runTry({cwd: f.repo, words: ['finish-task'], options: {'--no-open': true, '--no-wait': true}}, trying);
  await paused;
  const newer = f.io(); newer.signal = AbortSignal.abort();
  await assert.rejects(client.runDoorCall({root: f.repo, origin: f.fake.origin,
    sessionId: '11111111-1111-4111-8111-111111111111', login: 'octo', prompt: PLACE, operation: 'main'}, input, newer));
  release(); await pending;
  const latest = JSON.parse(readFileSync(repoFile, 'utf8'));
  assert.equal(latest.last_run.state, 'unknown');
  assert.deepEqual(latest.unrelated, {keep: 'value'});
  assert.ok(latest.tries[file], 'the Try is recorded');
  const saving = terminal(f.io()); assert.equal(await save(f, saving), 125);
  assert.match(saving.stderr.text, /unknown/);
  assert.equal(JSON.parse(readFileSync(join(f.repo, file))).steps.length, 1);
});

test('AC6: a separate process cannot confirm over a newer unknown invocation', {timeout: 10000}, async t => {
  const f = await recorded(t), repoDir = join(f.state, 'repos');
  const repoFile = join(repoDir, readdirSync(repoDir).find(name => name.endsWith('.json')));
  const repo = JSON.parse(readFileSync(repoFile, 'utf8')); repo.unrelated = {keep: 'value'};
  writeFileSync(repoFile, JSON.stringify(repo));
  const release = join(f.sandbox, 'release'), script = join(f.sandbox, 'older.mjs');
  const clientUrl = new URL('../src/runtime-client.mjs', import.meta.url).href;
  const fakeUrl = new URL('./runtime-fake.mjs', import.meta.url).href;
  writeFileSync(script, `import fs from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {runDoorCall} from ${JSON.stringify(clientUrl)};
import {portsFor} from ${JSON.stringify(fakeUrl)};
const [root, state, home, origin, repoFile, release] = process.argv.slice(2);
const io = portsFor({HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: origin}).ports;
let ready = false, paused = false, answer;
const read = fs.readFileSync;
fs.readFileSync = function(path, ...args) {
  const value = read.call(this, path, ...args);
  if (ready && !paused && String(path) === repoFile) {
    paused = true; process.send('paused');
    const deadline = Date.now() + 5000;
    while (!fs.existsSync(release)) {
      if (Date.now() >= deadline) throw Error('timed out waiting for release');
      Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 10);
    }
  }
  return value;
};
syncBuiltinESMExports();
io.fetch = async (_url, init) => {
  if (init.method === 'POST') {
    const id = JSON.parse(init.body).requestId;
    answer = {requestId:id,id,command:'call',state:'passed',result:{program_result:${JSON.stringify(result)},report:{input_world:${JSON.stringify(initial)},world:${JSON.stringify(after)}}}};
  } else ready = true;
  return new Response(JSON.stringify(answer), {status:200});
};
await runDoorCall({root,origin,sessionId:'11111111-1111-4111-8111-111111111111',login:'octo',prompt:${JSON.stringify(PLACE)},operation:'main'}, ${JSON.stringify(input)}, io);
`);
  const child = spawn(process.execPath, [script, f.repo, f.state, f.home, f.fake.origin, repoFile, release], {stdio: ['ignore', 'ignore', 'pipe', 'ipc']});
  let errors = ''; child.stderr.on('data', chunk => { errors += chunk; });
  const exited = new Promise(resolve => child.once('exit', (code, signal) => resolve({code, signal})));
  t.after(async () => {
    try { writeFileSync(release, 'cleanup'); } catch (error) { if (error.code !== 'ENOENT') throw error; }
    child.kill();
    await exited;
  });
  await new Promise((resolve, reject) => { child.once('message', resolve); child.once('error', reject); child.once('exit', () => reject(Error(errors || 'older process exited before pause'))); });
  const newer = f.io(); newer.signal = AbortSignal.abort();
  const newCall = assert.rejects(client.runDoorCall({root: f.repo, origin: f.fake.origin, sessionId: '11111111-1111-4111-8111-111111111111', login: 'octo', prompt: PLACE, operation: 'main'}, input, newer));
  // On the old code the newer invocation finishes here; with the lock it waits
  // for the paused owner, so release that owner after a bounded interval.
  await Promise.race([newCall, new Promise(resolve => setTimeout(resolve, 150))]);
  writeFileSync(release, 'continue');
  await newCall;
  assert.deepEqual(await exited, {code: 0, signal: null}, errors);
  const latest = JSON.parse(readFileSync(repoFile, 'utf8'));
  assert.equal(latest.last_run.state, 'unknown'); assert.deepEqual(latest.unrelated, {keep: 'value'});
  const before = readFileSync(join(f.repo, file), 'utf8'), saving = terminal(f.io());
  assert.equal(await save(f, saving), 125); assert.match(saving.stderr.text, /unknown/);
  assert.equal(readFileSync(join(f.repo, file), 'utf8'), before);
});

test('AC6: shim invalidation cannot restore an older confirmed run', {timeout: 10000}, async t => {
  const f = await recorded(t), repoDir = join(f.state, 'repos');
  const repoFile = join(repoDir, readdirSync(repoDir).find(name => name.endsWith('.json')));
  const descriptorPath = join(f.sandbox, 'shim.door.json'), release = join(f.sandbox, 'shim-release');
  const script = join(f.sandbox, 'shim.mjs'), sessionId = '11111111-1111-4111-8111-111111111111';
  const repo = JSON.parse(readFileSync(repoFile, 'utf8')); repo.unrelated = {keep: 'value'};
  writeFileSync(repoFile, JSON.stringify(repo));
  writeFileSync(descriptorPath, JSON.stringify({version: 1, root: f.repo, sessionId, repoState: repoFile, prompt: PLACE, promptHash: 'deliberately-invalid'}));
  const shimUrl = new URL('../src/try-doors.mjs', import.meta.url).href;
  writeFileSync(script, `import fs from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {runShim} from ${JSON.stringify(shimUrl)};
const [descriptor, repoFile, release] = process.argv.slice(2);
const read = fs.readFileSync;
let paused = false;
fs.readFileSync = function(path, ...args) {
  const value = read.call(this, path, ...args);
  if (!paused && String(path) === repoFile) {
    paused = true; process.send('paused');
    const deadline = Date.now() + 5000;
    while (!fs.existsSync(release)) {
      if (Date.now() >= deadline) throw Error('timed out waiting for release');
      Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 10);
    }
  }
  return value;
};
syncBuiltinESMExports();
const code = await runShim(descriptor, []);
if (code !== 125) process.exitCode = 1;
`);
  const child = spawn(process.execPath, [script, descriptorPath, repoFile, release], {stdio: ['ignore', 'ignore', 'pipe', 'ipc']});
  let errors = ''; child.stderr.on('data', chunk => { errors += chunk; });
  const exited = new Promise(resolve => child.once('exit', (code, signal) => resolve({code, signal})));
  t.after(async () => {
    try { writeFileSync(release, 'cleanup'); } catch (error) { if (error.code !== 'ENOENT') throw error; }
    child.kill(); await exited;
  });
  await new Promise((resolve, reject) => { child.once('message', resolve); child.once('error', reject); child.once('exit', () => reject(Error(errors || 'shim exited before pause'))); });
  const newer = f.io(); newer.signal = AbortSignal.abort();
  const newCall = assert.rejects(client.runDoorCall({root: f.repo, origin: f.fake.origin, sessionId, login: 'octo', prompt: PLACE, operation: 'main'}, input, newer));
  await Promise.race([newCall, new Promise(resolve => setTimeout(resolve, 150))]);
  writeFileSync(release, 'continue');
  await newCall;
  assert.deepEqual(await exited, {code: 0, signal: null}, errors);
  const latest = JSON.parse(readFileSync(repoFile, 'utf8'));
  assert.equal(latest.last_run.state, 'unknown');
  assert.deepEqual(latest.unrelated, {keep: 'value'});
  assert.deepEqual(latest.last_door, {descriptor: descriptorPath, last: join(f.sandbox, `${sessionId}.last.json`)});
  const before = readFileSync(join(f.repo, file), 'utf8'), saving = terminal(f.io());
  assert.equal(await save(f, saving), 125); assert.match(saving.stderr.text, /unknown/);
  assert.equal(readFileSync(join(f.repo, file), 'utf8'), before);
});

test('AC2: saving preserves dispatched input when the caller mutates its object', async t => {
  const f = await recorded(t), mutableInput = {argv: ['done', '4']}, io = f.io();
  let answer;
  io.fetch = async (_url, init) => {
    if (init.method === 'POST') {
      const request = JSON.parse(init.body); mutableInput.argv[1] = '999';
      answer = f.fake.job(request.requestId, 'call', 'passed', {program_result: result, report: {input_world: initial, world: after}}, 1);
    }
    return new Response(JSON.stringify(answer), {status: 200});
  };
  await client.runDoorCall({root: f.repo, origin: f.fake.origin, sessionId: '11111111-1111-4111-8111-111111111111',
    login: 'octo', prompt: PLACE, operation: 'main'}, mutableInput, io);
  const saving = terminal(f.io()); assert.equal(await save(f, saving), 0, saving.stderr.text);
  assert.deepEqual(JSON.parse(readFileSync(join(f.repo, file))).steps[1].input, input);
});

test('workspace excludes the recorded prompt before authentication', async t => {
  const f = await recorded(t), other = 'prompts/other.prompt.md';
  writeFileSync(join(f.repo, other), readFileSync(join(f.repo, PLACE)));
  const doc = JSON.parse(readFileSync(join(f.repo, file))); doc.steps[0].entry_path = other;
  writeFileSync(join(f.repo, file), JSON.stringify(doc));
  writeFileSync(join(f.repo, 'pdd-workspace.json'), JSON.stringify({allowed_paths: ['tests/', 'user_stories/', other]}));
  const io = terminal(f.io()); let auth = 0; io.gh = () => { auth++; throw Error('unexpected authentication'); };
  assert.equal(await save(f, io), 125); assert.equal(auth, 0); assert.match(io.stderr.text, /workspace-path-outside/);
});

for (const timing of ['answer', 'handoff']) test(`changed prompt during ${timing} refuses the case`, async t => {
  const f = await recorded(t), before = readFileSync(join(f.repo, file), 'utf8'), io = terminal(f.io());
  const change = () => writeFileSync(join(f.repo, PLACE), readFileSync(join(f.repo, PLACE), 'utf8') + '\nChanged while waiting.\n');
  if (timing === 'answer') io.stdin = Object.assign(Readable.from((async function* () { change(); yield 'y\n'; })()), {isTTY: true});
  else io.caseHandoff = async ({testPath}) => { change(); return {kind: 'closed-editor', testPath}; };
  assert.equal(await save(f, io), 125); assert.match(io.stderr.text, /prompt changed/);
  assert.equal(readFileSync(join(f.repo, file), 'utf8'), before);
});

test('Story scenario replays each declared operation and result check', async t => {
  const scenario = JSON.parse(readFileSync(new URL('./runtime/save-run-as-test.json', import.meta.url), 'utf8'));
  const f = await recorded(t);
  for (const step of scenario.steps) {
    assert.equal(typeof client[step.operation], 'function', step.operation);
    const actual = await client[step.operation]({...step.input, cwd: f.repo}, terminal(f.io(), 'N\n'));
    for (const check of step.checks) {
      assert.equal(check.target, 'result'); assert.equal(check.path, ''); assert.equal(check.op, 'equals');
      assert.deepEqual(actual, check.value, `${step.step_id}/${check.criterion_id}`);
    }
  }
});
