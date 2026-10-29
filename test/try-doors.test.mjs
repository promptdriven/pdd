import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, rmSync, statSync, symlinkSync, readdirSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { runTry } from '../src/runtime-client.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { harbor, fakeRuntime, portsFor, PLACE, TOKEN } from './runtime-fake.mjs';
import { proseSha256, fillHashes } from '../src/runtime-preflight.mjs';

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
      const response = { status: 200, json: { ...f.job(entry.json.requestId, 'call', 'passed', { program_result: result, report: { verdict: 'passed', result, remaining_calls: 40 - n }, output: result }, 1), session_id: entry.url.split('/')[3] } };
      f.jobs.set(entry.json.requestId, response.json); return response;
    }
    if (f.jobs.has(entry.url.split('/').at(-1))) return { status: 200, json: f.jobs.get(entry.url.split('/').at(-1)) };
    if (entry.url.endsWith('/model')) return { status: 200, json: { calls: { cap: 40, remaining: 40 } } };
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
  assert.match(ready.ports.stderr.text, /Try budget 400 calls; 400 remaining/);
  assert.doesNotMatch(ready.ports.stdout.text, /budget|charged only/);
  assert.match(ready.ports.stdout.text, /paperclip say 'two words'/);
  assert.ok(!readFileSync(shim, 'utf8').includes(TOKEN));
  const { runShim } = await import('../src/try-doors.mjs');
  const args = ['say', 'two words', '', '$(touch /tmp/DO-NOT-CREATE)', '--help'];
  const io = ready.makePorts({ stdin: Readable.from(['piped\n']) });
  assert.equal(await runShim(ready.descriptor, args, io), 0, io.stderr.text);
  assert.deepEqual(ready.fake.jsonPosts[0].json.input, { argv: args, stdin: 'piped\n' });
  assert.equal(io.stdout.text, args.join('\n') + '\npiped\n');
  assert.equal(io.stderr.text, 'Try AI usage: 1 this command · 1 used · 39 remaining (session cap 40).\n');
  const bad = ready.makePorts();
  assert.equal(await runShim(ready.descriptor, ['bad'], bad), 7);
  assert.equal(bad.stderr.text, 'invalid\nTry AI usage: 1 this command · 2 used · 38 remaining (session cap 40).\n');
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
  assert.equal(io.stderr.text, 'pdd try: This Try has no AI calls left.\nTry AI usage: 0 this command · unknown used · unknown remaining (session cap 40).\n');
  const save = ready.makePorts();
  assert.equal(await runTry({ cwd: setup.repo, options: { '--save-last': true } }, save), 125);
  assert.match(save.stderr.text, /unknown/);
  assert.equal(JSON.parse(readFileSync(join(setup.repo, 'tests/place-order.json'))).steps.length, 1);
});

test('RELEASE3: undeclared stdin is untouched; --shell gets the PATH', async t => {
  const setup = clip(t, false), ready = await opened(t, setup, { '--shell': true });
  // The shell launch is injected below, so this test checks startup without a real interactive shell.
  assert.equal(ready.code, 0, ready.ports.stderr.text);
  const { runShim } = await import('../src/try-doors.mjs');
  const input = Readable.from(['amount one\n', 'amount two\n']);
  const io = ready.makePorts({ stdin: input });
  assert.equal(await runShim(ready.descriptor, [], io), 0, io.stderr.text);
  assert.equal(input.readableDidRead, false);
  assert.deepEqual(ready.fake.jsonPosts[0].json.input, { argv: [] });
  const neverClosing = ready.makePorts({ stdin: { isTTY: false, [Symbol.asyncIterator]() { throw Error('must not touch an undeclared stream'); } } });
  assert.equal(await runShim(ready.descriptor, ['again'], neverClosing), 0, neverClosing.stderr.text);
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
    assert.deepEqual(outcome, { code: 0, stdout: 'say\ntwo words\n\n', stderr: 'Try AI usage: 1 this command · 1 used · 39 remaining (session cap 40).\n' }, name);
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

test('doors: a queued lint ending refused prints the confirmed reason and sends no Try', async t => {
  const setup = clip(t), message = 'Lint waited 20 seconds for a free slot. No checks ran. Retry with a new request ID.';
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST'
    ? { status: 202, json: f.job(entry.request.requestId, 'lint', 'queued') }
    : { status: 200, json: f.job(entry.url.split('/').at(-1), 'lint', 'refused', { report: { refusal: { code: 'lint-queue-timeout', message }, provider_calls: 0, dispatch: 'not_started' }, refusals: [{ code: 'lint-queue-timeout', message }] }) });
  const ports = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }).ports;
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--cli': true } }, ports), 125);
  assert.equal(ports.stdout.text, '');
  assert.equal(ports.stderr.text.trimEnd().split('\n').at(-1), `pdd try: ${message}`);
  assert.deepEqual(fake.posts.map(post => post.command), ['lint']);
});


test('RELEASE2: reused HTTP Try refuses changed or missing source records before model/listener', async t => {
  for (const mode of ['changed', 'missing-record', 'missing-file']) {
    const setup = clip(t), ready = await opened(t, setup);
    assert.equal(ready.code, 0, ready.ports.stderr.text);
    if (mode === 'changed') { writeFileSync(join(setup.repo, PLACE), readFileSync(join(setup.repo, PLACE), 'utf8').replace('Print each', 'Show each')); fillHashes({root:setup.repo}); }
    else if (mode === 'missing-file') {
      const descriptor = JSON.parse(readFileSync(ready.descriptor));
      const file = descriptor.repoState, data = JSON.parse(readFileSync(file));
      data.tries['tests/place-order.json'].prompt_hashes['prompts/removed.prompt.md'] = 'a'.repeat(64);
      writeFileSync(file, JSON.stringify(data));
    } else {
      const file = JSON.parse(readFileSync(ready.descriptor)).repoState, data = JSON.parse(readFileSync(file));
      delete data.tries['tests/place-order.json'].prompt_hashes; writeFileSync(file, JSON.stringify(data));
    }
    const reads = ready.fake.gets.length;
    const io = ready.makePorts({ serve: () => assert.fail('changed source cannot start a listener') });
    assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--serve': '0' } }, io), 125);
    assert.match(io.stderr.text, /--new/);
    assert.equal(ready.fake.posts.length, 2, 'no replacement Try/lint');
    assert.ok(ready.fake.gets.slice(reads).every(r => !r.url.endsWith('/model')), 'refuse before metadata');
  }
});

test('RELEASE6: preserve the stable gh symlink and recover a removed saved executable safely', async t => {
  const setup = clip(t), ready = await opened(t, setup), dir = join(setup.sandbox, 'tools'); mkdirSync(dir);
  const target = join(dir, 'gh-v2'), stable = join(dir, 'gh');
  writeFileSync(target, '#!/bin/sh\ncase "$1 $2" in\n"auth token") printf "%s\\n" "'+TOKEN+'";;\n"api user") printf "%s\\n" "octo 4242";;\n*) exit 91;;\nesac\n', {mode:0o755});
  symlinkSync('gh-v2', stable);
  const env = { ...ready.ports.env, PATH: dir+':'+(process.env.PATH || '') };
  assert.equal(await runTry({cwd:setup.repo,words:['place-order'],options:{'--cli':true}},ready.makePorts({env})),0);
  const descriptor = JSON.parse(readFileSync(ready.descriptor));
  assert.equal(descriptor.ghPath, stable, 'do not pin the versioned executable behind a package-manager symlink');
  descriptor.ghPath = join(dir, 'removed-gh-v1'); writeFileSync(ready.descriptor, JSON.stringify(descriptor));
  const {runShim} = await import('../src/try-doors.mjs');
  const io = ready.makePorts({gh:undefined,env});
  assert.equal(await runShim(ready.descriptor,['upgraded'],io),0,io.stderr.text);
  assert.deepEqual(ready.fake.jsonPosts.at(-1).json.input, {argv:['upgraded'],stdin:''});
});

test('RELEASE2: changed source cannot reopen a paused HTTP Try', async t => {
  const setup=clip(t),ready=await opened(t,setup);
  const file=join(setup.repo,PLACE);writeFileSync(file,readFileSync(file,'utf8').replace('Print each','Show each'));fillHashes({root:setup.repo});
  const id=JSON.parse(readFileSync(ready.descriptor)).sessionId;let reopened=0;
  const fetch=async(url,init)=>{
    const path=new URL(url).pathname;
    if(path==='/v1/runs/'+id)return new Response(JSON.stringify(ready.fake.tryJob(id,undefined,'paused')),{status:200});
    if(path.endsWith('/reopen')){reopened++;return new Response(JSON.stringify(ready.fake.tryJob(id)),{status:200});}
    return globalThis.fetch(url,init);
  };
  const io=ready.makePorts({fetch,serve:()=>assert.fail('changed source cannot serve')});
  assert.equal(await runTry({cwd:setup.repo,words:['place-order'],options:{'--serve':'0'}},io),125);
  assert.match(io.stderr.text,/--new/);assert.equal(reopened,0,'source identity checked before any reopen POST');
});

test('RELEASE6: missing gh target with only a PDD launcher on PATH fails closed before dispatch', async t => {
  const setup=clip(t),ready=await opened(t,setup),dir=join(setup.sandbox,'unsafe-bin');mkdirSync(dir);
  const marker=join(dir,'was-executed');
  writeFileSync(join(dir,'gh'),'#!/bin/sh\n# PDD Try launcher v1\nprintf executed > "'+marker+'"\nprintf "'+TOKEN+'\\n"\n',{mode:0o755});
  const descriptor=JSON.parse(readFileSync(ready.descriptor));descriptor.ghPath=join(dir,'removed-gh');writeFileSync(ready.descriptor,JSON.stringify(descriptor));
  const {runShim}=await import('../src/try-doors.mjs');
  const io=ready.makePorts({gh:undefined,env:{...ready.ports.env,PATH:dir}});
  assert.equal(await runShim(ready.descriptor,['safe'],io),125);
  assert.equal(readdirSync(dir).includes('was-executed'),false,'never execute a rejected launcher');
  assert.equal(ready.fake.jsonPosts.length,0);
});

test('RELEASE3: the actual launcher leaves a shell read loop input open for its next command', async t => {
  const {spawn}=await import('node:child_process');
  const setup=clip(t,false);
  setup.state=join(setup.sandbox, "state 'q' \" $(touch INJECTED)");
  const ready=await opened(t,setup),tools=join(setup.sandbox,'loop-tools');mkdirSync(tools);
  writeFileSync(join(tools,'gh'),`#!/bin/sh\nif [ "$1" = auth ]; then printf '%s\\n' '${TOKEN}'; else printf '%s\\n' 'octo 4242'; fi\n`,{mode:0o700});
  const descriptor=JSON.parse(readFileSync(ready.descriptor));descriptor.ghPath=join(tools,'gh');writeFileSync(ready.descriptor,JSON.stringify(descriptor));
  const shim=join(setup.repo,'.pdd/try/bin/paperclip');
  const loop=join(tools,'read-loop.sh');
  writeFileSync(loop,'while IFS= read -r a; do "$1" "$a" || exit; done\n');
  const outcome=await new Promise((done,reject)=>{
    const child=spawn('/bin/sh',[loop,shim],{cwd:setup.sandbox,env:{...process.env,PATH:tools+':'+process.env.PATH},stdio:['pipe','pipe','pipe']});
    let stdout='',stderr='',continued=false;
    const timer=setTimeout(()=>{child.kill('SIGKILL');reject(Error('The first command waited for the enclosing input pipe to close'));},15000);
    child.on('error',reject);child.stdin.on('error',reject);
    child.stdout.on('data',chunk=>{stdout+=chunk;if(!continued&&stdout==='first\n'){continued=true;child.stdin.end('second\n');}});
    child.stderr.on('data',chunk=>stderr+=chunk);
    child.on('close',code=>{clearTimeout(timer);done({code,stdout,stderr,continued});});
    child.stdin.write('first\n'); // Deliberately keep the pipe open until the first command returns.
  });
  assert.deepEqual(outcome,{code:0,stdout:'first\nsecond\n',stderr:'Try AI usage: 1 this command · 1 used · 39 remaining (session cap 40).\nTry AI usage: 1 this command · 2 used · 38 remaining (session cap 40).\n',continued:true});
  assert.equal(readdirSync(setup.sandbox).includes('INJECTED'),false);
  assert.deepEqual(ready.fake.jsonPosts.map(p=>p.json.input),[{argv:['first']},{argv:['second']}]);
});

test('hcli-4: startup and each CLI command show session usage only on stderr', async t => {
  const setup = clip(t), ready = await opened(t, setup);
  assert.equal(ready.code, 0);
  assert.match(ready.ports.stderr.text, /Try AI usage:.*0 used.*40 remaining.*cap 40/);
  const { runShim } = await import('../src/try-doors.mjs'), io = ready.makePorts();
  assert.equal(await runShim(ready.descriptor, ['say', 'hello'], io), 0);
  assert.equal(io.stdout.text, 'say\nhello\n');
  assert.match(io.stderr.text, /Try AI usage:.*1 this command.*1 used.*39 remaining.*cap 40/);
  assert.equal(ready.fake.jsonPosts.length, 1);
});


test('hcli-4: unterminated program stderr is preserved and separated from accounting', async t => {
  const ready = await opened(t, clip(t), {}, (e, f) => {
    const result = { stdout: 'exact stdout', stderr: 'exact stderr', exit_code: 7 };
    return { status: 200, json: { ...f.job(e.json.requestId, 'call', 'passed', { program_result: result, report: { remaining_calls: 38 } }, 2), session_id: e.url.split('/')[3] } };
  });
  const { runShim } = await import('../src/try-doors.mjs'), io = ready.makePorts();
  assert.equal(await runShim(ready.descriptor, ['bad'], io), 7); assert.equal(io.stdout.text, 'exact stdout');
  assert.equal(io.stderr.text, 'exact stderr\nTry AI usage: 2 this command · 2 used · 38 remaining (session cap 40).\n');
});
