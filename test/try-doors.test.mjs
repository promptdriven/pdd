import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync, statSync, symlinkSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { runTry } from '../src/runtime-client.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { harbor, fakeRuntime, portsFor, PLACE, TOKEN } from './runtime-fake.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';

function clip(t, stdin = true) {
  return harbor(t, root => {
    rmSync(join(root, 'tests/unknown-item.json'));
    const input = { type: 'object', properties: { argv: { type: 'array', items: { type: 'string' } }, ...(stdin ? { stdin: { type: 'string' } } : {}) }, required: ['argv'], additionalProperties: false };
    const result = { type: 'object', properties: { stdout: { type: 'string' }, stderr: { type: 'string' }, exit_code: { type: 'integer' } }, required: ['stdout', 'stderr', 'exit_code'], additionalProperties: false };
    const iface = { status: 'draft', prose_sha256: '', entries: [{ operation: 'main', input_schema: input, result_schema: result, errors: [] }], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 1 }, conventions: ['input_schema', 'result_schema'].map(key => ({ path: `/entries/0/${key}`, convention: 'cli' })) };
    const content = () => `# paperclip\n\nPrint each argument on its own line.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\x60\x60\x60json\n${JSON.stringify(iface)}\n\x60\x60\x60\n</details>\n`;
    iface.prose_sha256 = proseSha256(content()); writeFileSync(join(root, PLACE), content());
    writeFileSync(join(root, 'user_stories/place-order.md'), '# Arguments\n\nI can pass words.\n\n## Acceptance criteria\n\n1. Each argument prints on its own line.\n');
    const doc = { schema_version: 'prompt-runtime.program-scenario.v1', story_path: 'user_stories/place-order.md', criteria: [{ id: 'AC1', text: 'Each argument prints on its own line.' }], initial_world: {}, simulation: {}, context: [], steps: [{ step_id: 'two-words', entry_path: PLACE, operation: 'main', input: { argv: ['say', 'two words'] }, checks: [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'say\ntwo words\n' }] }] };
    writeFileSync(join(root, 'tests/place-order.json'), JSON.stringify(doc, null, 2) + '\n');
  });
}

async function opened(t, setup, options = {}, callReply) {
  let n = 0;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.json) {
      if (callReply) { const response = callReply(entry, f); if (response.json) f.jobs.set(entry.json.requestId, response.json); return response; }
      n += 1;
      const input = entry.json.input, result = { stdout: input.argv.join('\n') + '\n' + (input.stdin ?? ''), stderr: input.argv[0] === 'bad' ? 'invalid\n' : '', exit_code: input.argv[0] === 'bad' ? 7 : 0 };
      const response = { status: 200, json: { ...f.job(entry.json.requestId, 'call', 'passed', { program_result: result, report: { verdict: 'passed', result, remaining_calls: 40 - n }, output: result }), session_id: entry.url.split('/')[3] } };
      f.jobs.set(entry.json.requestId, response.json); return response;
    }
    if (f.jobs.has(entry.url.split('/').at(-1))) return { status: 200, json: f.jobs.get(entry.url.split('/').at(-1)) };
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    return { status: 200, json: f.tryJob(entry.url.split('/').at(-1)) };
  });
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };
  const makePorts = extra => portsFor(env, { stdin: Readable.from([]), ...extra }).ports;
  const ports = makePorts({ shell: async (shell, env) => { assert.ok(env.PATH.startsWith(join(setup.repo, '.pdd/try/bin') + ':')); return 0; }, openUrl: async () => assert.fail('door must not open browser') });
  const code = await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--cli': true, ...options } }, ports);
  return { fake, ports, makePorts, code, descriptor: readdirSync(join(setup.state, 'tries')).filter(p => p.endsWith('.door.json')).map(p => join(setup.state, 'tries', p))[0] };
}

test('doors: CLI flags and optional HTTP port parse without swallowing Story', () => {
  assert.equal(parseArgv(['try', 'story', '--cli', '--shell']).options['--shell'], true);
  assert.equal(parseArgv(['try', 'story', '--serve']).options['--serve'], '8080');
  assert.equal(parseArgv(['try', '--serve', 'story']).operands[0], 'story');
  assert.equal(parseArgv(['try', 'story', '--serve', '8123']).options['--serve'], '8123');
  assert.throws(() => parseArgv(['try', 'story', '--serve', '70000']));
});

test('doors: create one safe launcher, preserve argv/stdin/streams/exit and reuse Try', async t => {
  const setup = clip(t), ready = await opened(t, setup);
  assert.equal(ready.code, 0, ready.ports.stderr.text + ready.ports.stdout.text);
  const shim = join(setup.repo, '.pdd/try/bin/paperclip');
  assert.equal(statSync(shim).mode & 0o777, 0o700);
  assert.match(ready.ports.stdout.text, /export PATH=/);
  assert.match(ready.ports.stdout.text, /paperclip say 'two words'/);
  assert.ok(!readFileSync(shim, 'utf8').includes(TOKEN));
  const { runShim } = await import('../src/try-doors.mjs');
  const args = ['say', 'two words', '', '$(touch /tmp/DO-NOT-CREATE)', '--help'];
  const io = ready.makePorts({ stdin: Readable.from(['piped\n']) });
  assert.equal(await runShim(ready.descriptor, args, io), 0, io.stderr.text);
  assert.deepEqual(ready.fake.jsonPosts[0].json.input, { argv: args, stdin: 'piped\n' });
  assert.equal(io.stdout.text, args.join('\n') + '\npiped\n');
  assert.equal(io.stderr.text, '');
  const bad = ready.makePorts();
  assert.equal(await runShim(ready.descriptor, ['bad'], bad), 7);
  assert.equal(bad.stderr.text, 'invalid\n');
  const reuse = ready.makePorts();
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--cli': true } }, reuse), 0);
  assert.equal(ready.fake.posts.filter(p => p.command === 'try').length, 1);
});

test('doors: save last appends observed case only once in the original test', async t => {
  const setup = clip(t), ready = await opened(t, setup);
  assert.equal(ready.code, 0, ready.ports.stderr.text);
  const { runShim } = await import('../src/try-doors.mjs');
  assert.equal(await runShim(ready.descriptor, ['bad'], ready.makePorts()), 7);
  const file = join(setup.repo, 'tests/place-order.json'), before = readFileSync(file, 'utf8');
  const save = ready.makePorts();
  assert.equal(await runTry({ cwd: setup.repo, options: { '--save-last': true } }, save), 0, save.stderr.text);
  const doc = JSON.parse(readFileSync(file, 'utf8'));
  assert.equal(doc.steps.length, 2);
  assert.deepEqual(doc.steps[1].input, { argv: ['bad'], stdin: '' });
  assert.deepEqual(doc.steps[1].checks[0].value, { stdout: 'bad\n', stderr: 'invalid\n', exit_code: 7 });
  assert.match(save.stdout.text, /added to tests\/place-order.json/);
  assert.equal(readFileSync(file, 'utf8').slice(0, before.indexOf('"steps"')), before.slice(0, before.indexOf('"steps"')));
  assert.equal(await runTry({ cwd: setup.repo, options: { '--save-last': true } }, ready.makePorts()), 0);
  assert.equal(JSON.parse(readFileSync(file, 'utf8')).steps.length, 2);
});

test('doors: wrapper failures use 125, never call as another login or follow launcher symlinks', async t => {
  const setup = clip(t), ready = await opened(t, setup);
  assert.equal(ready.code, 0, ready.ports.stderr.text);
  const { runShim } = await import('../src/try-doors.mjs');
  const wrong = ready.makePorts({ gh: args => args[0] === 'auth' ? { status: 0, stdout: TOKEN } : { status: 0, stdout: 'other 1234' } });
  assert.equal(await runShim(ready.descriptor, ['--help'], wrong), 125);
  assert.match(wrong.stderr.text, /^pdd try:.*belong/);
  assert.equal(ready.fake.jsonPosts.length, 0);
  const missing = ready.makePorts();
  assert.equal(await runShim('/missing/config', [], missing), 125);
  assert.match(missing.stderr.text, /^pdd try:/);
  const shim = join(setup.repo, '.pdd/try/bin/paperclip'); rmSync(shim); symlinkSync(join(setup.repo, 'README.md'), shim);
  const denied = ready.makePorts();
  assert.notEqual(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--cli': true } }, denied), 0);
  assert.match(denied.stderr.text, /symbolic link/);
});


test('doors: a lost POST reads the accepted ID and never dispatches twice', async t => {
  const setup = clip(t);
  const ready = await opened(t, setup, {}, (entry, f) => {
    const result = { stdout: 'once\n', stderr: '', exit_code: 0 };
    f.jobs.set(entry.json.requestId, { ...f.job(entry.json.requestId, 'call', 'passed', { program_result: result, report: { result } }), session_id: entry.url.split('/')[3] });
    return { destroy: true };
  });
  assert.equal(ready.code, 0, ready.ports.stderr.text);
  const { runShim } = await import('../src/try-doors.mjs'), io = ready.makePorts();
  assert.equal(await runShim(ready.descriptor, ['help'], io), 0, io.stderr.text);
  assert.equal(io.stdout.text, 'once\n');
  assert.equal(ready.fake.jsonPosts.length, 1);
  assert.ok(ready.fake.gets.some(g => g.url.endsWith(ready.fake.jsonPosts[0].json.requestId)));
});

test('doors: budget refusal and unknown outcome leave no stale output eligible for Save', async t => {
  const setup = clip(t);
  let budget = false;
  const ready = await opened(t, setup, {}, (entry, f) => {
    const report = budget ? { refusal: { code: 'session-call-cap' } } : { result: { stdout: 'ok\n', stderr: '', exit_code: 0 } };
    return { status: 200, json: { ...f.job(entry.json.requestId, 'call', budget ? 'refused' : 'passed', { program_result: report.result, report, refusals: budget ? [{ code: 'session-call-cap', message: 'This Try has no AI calls left.' }] : [] }), session_id: entry.url.split('/')[3] } };
  });
  assert.equal(ready.code, 0, ready.ports.stderr.text);
  const { runShim } = await import('../src/try-doors.mjs');
  assert.equal(await runShim(ready.descriptor, ['ok'], ready.makePorts()), 0);
  budget = true;
  const io = ready.makePorts();
  assert.equal(await runShim(ready.descriptor, ['again'], io), 125);
  assert.equal(io.stdout.text, '');
  assert.equal(io.stderr.text, 'pdd try: This Try has no AI calls left.\n');
  const save = ready.makePorts();
  assert.equal(await runTry({ cwd: setup.repo, options: { '--save-last': true } }, save), 125);
  assert.match(save.stderr.text, /unknown/);
  assert.equal(JSON.parse(readFileSync(join(setup.repo, 'tests/place-order.json'))).steps.length, 1);
});

test('doors: unsupported nonempty stdin is refused before dispatch; --shell gets the PATH', async t => {
  const setup = clip(t, false), ready = await opened(t, setup, { '--shell': true });
  // The shell launch is injected below, so this test checks startup without a real interactive shell.
  assert.equal(ready.code, 0, ready.ports.stderr.text);
  const { runShim } = await import('../src/try-doors.mjs');
  const io = ready.makePorts({ stdin: Readable.from(['data']) });
  assert.equal(await runShim(ready.descriptor, [], io), 125);
  assert.match(io.stderr.text, /does not declare stdin/);
  assert.equal(ready.fake.jsonPosts.length, 0);
});

test('doors: real launcher executes from CommonJS project', async t => {
  const { spawn } = await import('node:child_process');
  const { mkdirSync } = await import('node:fs');
  for (const name of ['paperclip']) {
    const setup = clip(t);
    writeFileSync(join(setup.repo, 'package.json'), '{"type":"commonjs"}');
    const promptFile = join(setup.repo, PLACE);
    let content = readFileSync(promptFile, 'utf8').replace('# paperclip', `# ${name}`);
    const digest = proseSha256(content);
    content = content.replace(/"prose_sha256":"[a-f0-9]+"/, `"prose_sha256":"${digest}"`);
    writeFileSync(promptFile, content);
    const ghBin = join(setup.sandbox, 'tools'); mkdirSync(ghBin);
    writeFileSync(join(ghBin, 'gh'), `#!/bin/sh\nif [ "$1" = auth ]; then printf '%s\\n' '${TOKEN}'; else printf '%s\\n' 'octo 4242'; fi\n`, { mode: 0o700 });
    // Capture this gh executable when creating the private descriptor.
    const ready = await opened(t, setup);
    assert.equal(ready.code, 0, ready.ports.stderr.text);
    const d = JSON.parse(readFileSync(ready.descriptor)); d.ghPath = join(ghBin, 'gh'); writeFileSync(ready.descriptor, JSON.stringify(d));
    const bin = join(setup.repo, '.pdd/try/bin'), shim = join(bin, name);
    const outcome = await new Promise((done, reject) => {
      const child = spawn(shim, ['say', 'two words', ''], { env: { ...process.env, PATH: `${bin}:${ghBin}:${process.env.PATH}` }, stdio: ['ignore', 'pipe', 'pipe'] });
      let stdout = '', stderr = ''; child.stdout.on('data', s => stdout += s); child.stderr.on('data', s => stderr += s);
      const timer = setTimeout(() => child.kill('SIGKILL'), 5000);
      child.on('error', reject); child.on('exit', code => { clearTimeout(timer); done({ code, stdout, stderr }); });
    });
    assert.deepEqual(outcome, { code: 0, stdout: 'say\ntwo words\n\n', stderr: '' }, name);
    assert.equal(ready.fake.jsonPosts.length, 1, name);
  }
});

test('doors: a changed local prompt cannot reuse the old session or save old output', async t => {
  const setup = clip(t), ready = await opened(t, setup);
  assert.equal(ready.code, 0, ready.ports.stderr.text);
  const { runShim } = await import('../src/try-doors.mjs');
  const file = join(setup.repo, PLACE); writeFileSync(file, readFileSync(file, 'utf8').replace('Print each', 'Show each'));
  const io = ready.makePorts();
  assert.equal(await runShim(ready.descriptor, ['say'], io), 125);
  assert.match(io.stderr.text, /prompt changed/);
  assert.equal(ready.fake.jsonPosts.length, 0);
});

test('doors: cancellation after accepted dispatch returns unknown promptly without redispatch', async t => {
  const setup = clip(t), controller = new AbortController();
  const ready = await opened(t, setup, {}, (entry, f) => {
    controller.abort();
    return { status: 202, json: { ...f.job(entry.json.requestId, 'call', 'running'), session_id: entry.url.split('/')[3] } };
  });
  assert.equal(ready.code, 0, ready.ports.stderr.text);
  const { runShim } = await import('../src/try-doors.mjs'), io = ready.makePorts({ signal: controller.signal });
  assert.equal(await runShim(ready.descriptor, ['say'], io), 125);
  assert.match(io.stderr.text, /result is unknown/);
  assert.equal(ready.fake.jsonPosts.length, 1);
});


test('doors: dependency names are refused before creating PATH launchers', async t => {
  for (const name of ['node', 'gh', 'git', 'pdd', 'Node', 'GH', 'Git', 'PDD']) {
    const setup = clip(t), file = join(setup.repo, PLACE);
    let text = readFileSync(file, 'utf8').replace('# paperclip', `# ${name}`);
    text = text.replace(/"prose_sha256":"[a-f0-9]+"/, `"prose_sha256":"${proseSha256(text)}"`);
    writeFileSync(file, text);
    const ready = await opened(t, setup);
    assert.equal(ready.code, 125, name);
    assert.match(ready.ports.stderr.text, /reserved/);
  }
});
