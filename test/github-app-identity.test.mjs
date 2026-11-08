import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { nativeGithubCounter, githubLedger, githubMachineEntries, githubUsage, githubBudget, githubEtagCache, githubReply } from '../src/github-calls.mjs';
import { chatLaunch, chatCommand } from '../src/workflow-chat.mjs';
import { commandGithubFloor } from '../src/issue-dependencies-github.mjs';
import { tomlBasicString } from './helpers/codex-config-args.mjs';
import { githubAppWorld } from './helpers/github-app-world.mjs';

function runner(w, action) {
  return nativeGithubCounter(async (file, args, options) => file === 'git' ? w.gitExec(file, args, options) : action(args, options),
    { env: w.env, stateRoot: w.stateRoot, now: () => w.time, appPorts: w.appPorts });
}
function shellSet(command, name) {
  const match = command.match(new RegExp(`shell_environment_policy\\.set\\.${name}=("(?:[^"\\\\]|\\\\.)*")`));
  return match ? tomlBasicString(match[1]) : undefined;
}
const args = ['api', '--method', 'POST', 'repos/acme/widgets/issues/1/comments', '--input', '-'];
const opts = w => ({ cwd: w.cwd, env: { ...w.env, GH_TOKEN: 'personal-fake-token', GITHUB_TOKEN: 'other-personal-fake-token' }, input: '{"body":"claim"}' });

// Existing public runner boundary: on the base this uses the personal token.
test('App credentials replace personal credentials, refresh, and stay out of results and ledgers', async t => {
  const w = await githubAppWorld(t), calls = [];
  githubLedger({ root: w.stateRoot, repository: w.repository }).record({ at: w.time, purpose: 'setup', api: 'rest', status: 200 });
  const run = runner(w, async (argv, options) => {
    calls.push(options);
    assert.ok(w.tokens.includes(options.env.GH_TOKEN), 'App token must replace the personal credential');
    assert.ok(options.env.GH_TOKEN === options.env.GITHUB_TOKEN);
    assert.equal(options.input, '{"body":"claim"}');
    assert.ok(!argv.some(arg => w.tokens.includes(arg)));
    return { code: 0, stdout: `actor ${w.bot} ${options.env.GH_TOKEN}`, stderr: options.env.GH_TOKEN };
  });
  const first = await run('gh', args, opts(w));
  assert.ok(first.stdout.includes(w.bot)); assert.ok(w.tokens.every(token => !JSON.stringify(first).includes(token)));
  assert.equal(w.tokens.length, 1);
  await Promise.all([run('gh', args, opts(w)), run('gh', args, opts(w))]);
  assert.equal(w.tokens.length, 1);
  w.time += 55 * 60000;
  await Promise.all([run('gh', args, opts(w)), run('gh', args, opts(w))]);
  assert.equal(w.tokens.length, 2, 'refresh must coalesce at the five minute boundary');
  const secondProcess = runner(w, async (_args, options) => { assert.ok(options.env.GH_TOKEN === w.tokens.at(-1)); return { code: 0, stdout: '', stderr: '' }; });
  await secondProcess('gh', args, opts(w)); assert.equal(w.tokens.length, 2, 'a separate process reuses the private cache');
  const entries = githubMachineEntries({ root: w.stateRoot, identity: w.identity });
  assert.equal(entries.length, 6); assert.ok(w.tokens.every(token => !JSON.stringify(entries).includes(token)));
  const cache = join(w.home, '.cache', 'pdd', 'github-app');
  const { statSync } = await import('node:fs');
  assert.equal(statSync(cache).mode & 0o777, 0o700);
  assert.equal(statSync(join(cache, readdirSync(cache)[0])).mode & 0o777, 0o600);
});

test('App command errors redact the credential and do not replay writes', async t => {
  const w = await githubAppWorld(t); let writes = 0;
  const run = runner(w, async (_args, options) => { writes++; throw Object.assign(Error(options.env.GH_TOKEN), { code: 1, stdout: options.env.GH_TOKEN, stderr: `HTTP 403 ${options.env.GH_TOKEN}` }); });
  await assert.rejects(run('gh', args, opts(w)), error => {
    assert.equal(error.code, 1); assert.equal(error.githubIdentity, w.identity);
    assert.ok(w.tokens.every(token => ![error.message, error.stdout, error.stderr].join('').includes(token)));
    return true;
  });
  assert.equal(writes, 1);
  await assert.rejects(run('gh', ['auth', 'token'], opts(w)), { code: 'github_app_invalid' });
  assert.equal(writes, 1);
});

test('App start needs no personal login, names the bot, and budgets only the installation', async t => {
  const w = await githubAppWorld(t);
  githubLedger({ root: w.stateRoot, repository: w.repository }).record({ at: w.time, api: 'rest', purpose: 'other', status: 200, resource: 'core', limit: 5000, remaining: 0, resetAt: w.time + 3600000 });
  const started = await w.invoke('start');
  assert.equal(started.exitCode, 0, started.message);
  assert.equal(w.state().githubIdentity, w.identity);
  assert.equal(w.state().githubBot, w.bot);
  assert.ok(!w.ghOptions.some(call => call.args[0] === 'auth'));
  assert.ok(w.launches.length > 0, 'personal reserve must not stop the App');
  const usage = githubUsage(githubMachineEntries({ root: w.stateRoot, identity: w.identity }), w.time, w.identity);
  assert.equal(githubBudget({ usage }).allowed, 4500);
  const status = await w.invoke('status');
  assert.equal(status.exitCode, 0); assert.ok(status.message.includes(w.bot));
  assert.ok(w.tokens.every(token => !JSON.stringify(w.state()).includes(token) && !w.launches.join('').includes(token) && !status.message.includes(token)));
  assert.ok(shellSet(w.launches[0], 'PATH').includes('github-app'));
  assert.equal(shellSet(w.launches[0], 'PDD_GITHUB_APP_ROOT'), w.cwd);
});

for (const defect of ['partial', 'missing-key', 'bad-key', 'in-repo-key', 'not-installed', 'wrong-app', 'permissions', 'token-refused', 'repo-refused', 'expiry', 'empty-token']) {
  test(`App start refuses ${defect} before claims, timers or chats`, async t => {
    const w = await githubAppWorld(t); let timers = 0;
    w.ports.timer = async () => { timers++; return true; };
    if (defect === 'partial') w.configure({ id: '1234' });
    if (defect === 'missing-key') w.configure({ ...w.app, privateKeyFile: join(w.dir, 'absent.pem') });
    if (defect === 'bad-key') writeFileSync(w.keyFile, 'invalid-key');
    if (defect === 'in-repo-key') { const file = join(w.cwd, 'key.pem'); writeFileSync(file, readFileSync(w.keyFile)); w.configure({ ...w.app, privateKeyFile: file }); }
    if (defect === 'not-installed') w.installed = false;
    if (defect === 'wrong-app') w.wrongApp = true;
    if (defect === 'permissions') delete w.permissions.issues;
    if (defect === 'token-refused') { w.authFailure = 401; w.remoteError = 'DO-NOT-PRINT-TOKEN-RESPONSE'; }
    if (defect === 'repo-refused') { w.accessFailure = 403; w.remoteError = 'DO-NOT-PRINT-TOKEN-RESPONSE'; }
    if (defect === 'expiry') w.badExpiry = true;
    if (defect === 'empty-token') w.badToken = true;
    const result = await w.invoke('start');
    assert.equal(result.exitCode, 1, 'App authentication failure must stop start');
    assert.match(result.message, /App/i);
    assert.equal(w.ghOptions.length, 0); assert.equal(w.launches.length, 0); assert.equal(timers, 0);
    assert.ok(!result.message.includes('DO-NOT-PRINT-TOKEN-RESPONSE'));
  });
}

test('expired App token refresh failure holds the tick with no personal fallback', async t => {
  const w = await githubAppWorld(t);
  assert.equal((await w.invoke('start')).exitCode, 0);
  w.time += 3600001; w.authFailure = 401;
  const before = w.ghOptions.length, launches = w.launches.length;
  await assert.rejects(w.tick(), { code: 'github_app_invalid' });
  assert.equal(w.ghOptions.length, before); assert.equal(w.launches.length, launches);
});

test('personal login stays the default without App settings', async t => {
  const w = await githubAppWorld(t);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto' } }));
  let called = 0;
  const run = runner(w, async (_args, options) => { called++; assert.equal(options.env.GH_TOKEN, 'personal-fake-token'); return { stdout: 'personal', stderr: '', code: 0 }; });
  assert.equal((await run('gh', args, opts(w))).stdout, 'personal');
  assert.equal(called, 1); assert.equal(w.http.length, 0);
});

test('worker launches route gh through the App after a later terminal opens an area', async t => {
  const w = await githubAppWorld(t), runDir = join(w.dir, 'run'); mkdirSync(runDir);
  const launch = chatLaunch({ run: { sourceRoot: w.cwd, root: w.cwd, runDir }, agent: 'codex', env: w.env });
  assert.equal(launch.githubEnv?.PDD_GITHUB_APP_ROOT, w.cwd, 'worker must bind its source checkout App');
  const command = chatCommand({ agent: 'codex', cwd: w.cwd, sessionId: 'session', ...launch });
  assert.equal(shellSet(command, 'PDD_GITHUB_APP_ROOT'), w.cwd);
  assert.ok(shellSet(command, 'PATH').includes('github-app'));
});

test('App ledger usage and native floor ignore personal and other installation buckets', async t => {
  const w = await githubAppWorld(t), ledger = githubLedger({ root: w.stateRoot, repository: w.repository });
  const entry = { at: w.time, api: 'rest', purpose: 'setup', status: 200, resource: 'core', limit: 5000, remaining: 0, resetAt: w.time + 3600000 };
  ledger.record(entry);
  ledger.record({ ...entry, identity: 'app:1234:installation:1111' });
  ledger.record({ ...entry, identity: w.identity, limit: 15000, remaining: 14000 });
  const usage = githubUsage(ledger.read(), w.time, w.identity);
  assert.equal(usage.calls, 1); assert.equal(usage.rate.core.limit, 15000);
  const guard = await commandGithubFloor({ cwd: w.cwd, repository: w.repository }, { env: w.env, autopilotStateRoot: w.stateRoot, execFile: w.gitExec, githubApp: w.appPorts, now: () => w.time });
  assert.equal(guard.blocked(), false, 'App floor must use its installation allowance');
});

test('App conditional cache cannot reuse a personal or another installation body', async t => {
  const w = await githubAppWorld(t), options = { root: w.stateRoot, repository: w.repository, now: () => w.time };
  const personal = githubEtagCache(options); personal.set('repos/acme/widgets', { etag: 'personal', body: 'private-personal-result' }); personal.save();
  assert.equal(githubEtagCache({ ...options, identity: w.identity }).get('repos/acme/widgets'), undefined);
});

test('unsafe shared credential cache is refused before gh runs', async t => {
  const w = await githubAppWorld(t); const folder = join(w.home, '.cache', 'pdd', 'github-app'); mkdirSync(folder, { recursive: true }); chmodSync(folder, 0o755);
  const run = runner(w, async () => assert.fail('must not run gh with an unsafe cache'));
  await assert.rejects(run('gh', args, opts(w)), { code: 'github_app_invalid' });
});

test('native gh shell route gives claims, comments and PRs one App author', async t => {
  const w = await githubAppWorld(t);
  w.time = Date.now();
  // Seed the real private cache through the public native runner and local token endpoint.
  await runner(w, async () => ({ code: 0, stdout: '', stderr: '' }))('gh', args, opts(w));
  const fakeBin = join(w.dir, 'fake-bin'), runDir = join(w.dir, 'native-run'); mkdirSync(fakeBin); mkdirSync(runDir);
  const fakeSource = new URL('./helpers/github-repo-fake.mjs', import.meta.url).href;
  writeFileSync(join(fakeBin, 'gh'), `#!${process.execPath}
(async () => {
  const { createGithubRepoFake } = await import(${JSON.stringify(fakeSource)});
  const actor = /^fake-installation-token-/.test(process.env.GH_TOKEN ?? '') ? 'pdd-autopilot[bot]' : 'person';
  const f = createGithubRepoFake({ repository:'acme/widgets', owner:actor, issues:1 });
  const argv = process.argv.slice(2);
  if (argv[0] === 'pr') { console.log(JSON.stringify({ user:{login:actor}, number:2 })); return; }
  if (argv.some(x => x.endsWith('/labels'))) { console.log(JSON.stringify({ actor:{login:f.label(1,'pdd:working',actor).actor} })); return; }
  let input = ''; for await (const chunk of process.stdin) input += chunk;
  const r = await f.gh(argv, { input }); process.stdout.write(r.stdout); process.exitCode = r.code;
})();
`, { mode: 0o755 });
  const env = { ...w.env, PATH: `${fakeBin}:${w.env.PATH}` };
  const launch = chatLaunch({ run: { sourceRoot: w.cwd, root: w.cwd, runDir }, agent: 'codex', env });
  const { runAgentProcess } = await import('../src/agent-adapters.mjs');
  const invoke = argv => runAgentProcess('gh', argv, { cwd: w.cwd, env: { ...env, ...launch.githubEnv }, input: '{"body":"claim"}' });
  const label = await invoke(['api', '--method', 'POST', 'repos/acme/widgets/issues/1/labels']);
  assert.equal(label.code, 0, label.stderr); assert.equal(JSON.parse(label.stdout).actor.login, w.bot, 'claim label must show the App');
  const comment = await invoke(args);
  assert.equal(comment.code, 0, comment.stderr); assert.equal(JSON.parse(githubReply(comment.stdout).body).user.login, w.bot, 'claim and discussion comments must show the App');
  const pull = await invoke(['pr', 'create', '--repo', 'acme/widgets', '--title', 'Synthetic change', '--body', 'Synthetic body']);
  assert.equal(pull.code, 0, pull.stderr); assert.equal(JSON.parse(pull.stdout).user.login, w.bot, 'PR must show the App');
  assert.equal(w.tokens.length, 1, 'separate shell commands reuse the same live credential');
});

test('native Git push uses installation authentication without personal Git credentials', async t => {
  const w = await githubAppWorld(t); let pushes = 0;
  const run = nativeGithubCounter(async (file, argv, options) => {
    if (file !== 'git' || argv[0] !== 'push') return w.gitExec(file, argv, options);
    pushes++;
    const env = options.env, settings = Array.from({ length: Number(env.GIT_CONFIG_COUNT ?? 0) }, (_, i) => [env[`GIT_CONFIG_KEY_${i}`], env[`GIT_CONFIG_VALUE_${i}`]]);
    const header = settings.filter(([key]) => key === 'http.https://github.com/.extraheader').at(-1)?.[1] ?? '';
    const encoded = header.split(' ').at(-1), decoded = Buffer.from(encoded, 'base64').toString();
    assert.ok(w.tokens.some(token => decoded === `x-access-token:${token}`), 'git push must use the App credential');
    assert.ok(settings.some(([key, value]) => key === 'credential.helper' && value === ''));
    assert.ok(settings.some(([key, value]) => key === 'url.https://github.com/.insteadOf' && value === 'git@github.com:'));
    assert.equal(env.GIT_TERMINAL_PROMPT, '0');
    assert.ok(settings.some(([key, value]) => key === 'fetch.prune' && value === 'true'), 'retain unrelated Git environment config');
    assert.ok(!JSON.stringify(argv).includes(encoded));
    return { code: 0, stdout: encoded, stderr: env.GH_TOKEN };
  }, { env: w.env, stateRoot: w.stateRoot, now: () => w.time, appPorts: w.appPorts });
  const result = await run('git', ['push', 'origin', 'HEAD:refs/heads/synthetic'], { cwd: w.cwd, env: { ...w.env, GIT_CONFIG_COUNT: '1', GIT_CONFIG_KEY_0: 'fetch.prune', GIT_CONFIG_VALUE_0: 'true' } });
  assert.equal(pushes, 1); assert.equal(result.stdout, '[redacted]'); assert.equal(result.stderr, '[redacted]');
});

test('worker Git wrapper rewrites SSH pushes to authenticated HTTPS without recursion', async t => {
  const w = await githubAppWorld(t); w.time = Date.now();
  await runner(w, async () => ({ code: 0, stdout: '', stderr: '' }))('gh', args, opts(w));
  const fakeBin = join(w.dir, 'git-bin'), runDir = join(w.dir, 'git-run'); mkdirSync(fakeBin); mkdirSync(runDir);
  // Git's exec directory need not contain the top-level binary. Resolve it through the unchanged PATH.
  const { execFileSync } = await import('node:child_process');
  const gitBinary = execFileSync('sh', ['-c', 'command -v git'], { env: w.env, encoding: 'utf8' }).trim();
  execFileSync(gitBinary, ['remote', 'set-url', 'origin', 'git@github.com:acme/widgets.git'], { cwd: w.cwd });
  writeFileSync(join(fakeBin, 'git'), `#!${process.execPath}
const { spawnSync } = require('node:child_process');
const git = (args) => spawnSync(${JSON.stringify(gitBinary)}, args, { env:process.env, cwd:process.cwd(), encoding:'utf8' });
const argv = process.argv.slice(2);
if (argv[0] === 'push') {
  const header = git(['config','--get-all','http.https://github.com/.extraheader']).stdout.trim().split('\\n').at(-1) ?? '';
  const token = Buffer.from(header.split(' ').at(-1),'base64').toString();
  console.log(JSON.stringify({ authenticated: token.startsWith('x-access-token:fake-installation-token-'), remote:git(['remote','get-url','origin']).stdout.trim() }));
} else { const result = git(argv); process.stdout.write(result.stdout); process.stderr.write(result.stderr); process.exitCode=result.status; }
`, { mode: 0o755 });
  const env = { ...w.env, PATH: `${fakeBin}:${w.env.PATH}` }, launch = chatLaunch({ run: { sourceRoot: w.cwd, root: w.cwd, runDir }, agent: 'codex', env });
  const { runAgentProcess } = await import('../src/agent-adapters.mjs');
  const pushed = await runAgentProcess('git', ['push', 'origin', 'HEAD:refs/heads/synthetic'], { cwd: w.cwd, env: { ...env, ...launch.githubEnv } });
  assert.equal(pushed.code, 0, pushed.stderr);
  assert.deepEqual(JSON.parse(pushed.stdout), { authenticated: true, remote: 'https://github.com/acme/widgets.git' });
  const origin = execFileSync(gitBinary, ['remote', 'get-url', 'origin'], { cwd: w.cwd, encoding: 'utf8' }).trim();
  assert.equal(origin, 'git@github.com:acme/widgets.git', 'the stored remote must stay unchanged');
});

test('gh PR creation passes App Git authentication to a nested push', async t => {
  const w = await githubAppWorld(t); w.time = Date.now();
  await runner(w, async () => ({ code: 0, stdout: '', stderr: '' }))('gh', args, opts(w));
  const fakeBin = join(w.dir, 'nested-bin'), runDir = join(w.dir, 'nested-run'); mkdirSync(fakeBin); mkdirSync(runDir);
  writeFileSync(join(fakeBin, 'gh'), `#!${process.execPath}
const { spawnSync } = require('node:child_process');
const r = spawnSync('git', ['push','origin','HEAD:refs/heads/synthetic'], { env:process.env, encoding:'utf8' });
process.stdout.write(r.stdout); process.stderr.write(r.stderr); process.exitCode = r.status;
`, { mode: 0o755 });
  const { execFileSync } = await import('node:child_process');
  const gitBinary = execFileSync('sh', ['-c', 'command -v git'], { env: w.env, encoding: 'utf8' }).trim();
  writeFileSync(join(fakeBin, 'git'), `#!${process.execPath}
if (process.argv[2] !== 'push') {
  const { spawnSync } = require('node:child_process');
  const r = spawnSync(${JSON.stringify(gitBinary)}, process.argv.slice(2), { env:process.env, encoding:'utf8' });
  process.stdout.write(r.stdout); process.stderr.write(r.stderr); process.exitCode=r.status;
} else {
const config = Array.from({length:Number(process.env.GIT_CONFIG_COUNT ?? 0)}, (_, i) => [process.env['GIT_CONFIG_KEY_'+i],process.env['GIT_CONFIG_VALUE_'+i]]);
const header = config.filter(([key]) => key === 'http.https://github.com/.extraheader').at(-1)?.[1] ?? '';
const credential = Buffer.from(header.split(' ').at(-1),'base64').toString();
console.log(JSON.stringify({ appPush:credential.startsWith('x-access-token:fake-installation-token-') }));
}
`, { mode: 0o755 });
  const env = { ...w.env, PATH: `${fakeBin}:${w.env.PATH}` };
  const launch = chatLaunch({ run: { sourceRoot: w.cwd, root: w.cwd, runDir }, agent: 'codex', env });
  const { runAgentProcess } = await import('../src/agent-adapters.mjs');
  const result = await runAgentProcess('gh', ['pr', 'create', '--repo', w.repository], { cwd: w.cwd, env: { ...env, ...launch.githubEnv } });
  assert.equal(result.code, 0, result.stderr);
  assert.equal(JSON.parse(result.stdout).appPush, true, 'gh must authenticate its nested Git push as the App');
});

test('hosted interpreter health keeps personal gh authentication behind the App wrapper', async t => {
  const w = await githubAppWorld(t), fakeBin = join(w.dir, 'runtime-bin'), runDir = join(w.dir, 'runtime-run'); mkdirSync(fakeBin); mkdirSync(runDir);
  writeFileSync(join(fakeBin, 'gh'), `#!${process.execPath}
if (process.argv[2] === 'auth' && process.argv[3] === 'token') console.log('personal-runtime-fake-token');
else process.exitCode = 1;
`, { mode: 0o755 });
  const env = { ...w.env, PATH: `${fakeBin}:${w.env.PATH}` }, launch = chatLaunch({ run: { sourceRoot: w.cwd, root: w.cwd, runDir }, agent: 'codex', env });
  const { checkRuntimeHealth } = await import('../src/runtime-client.mjs'); let sent = false;
  const result = await checkRuntimeHealth({ env: { ...env, ...launch.githubEnv } }, { fetch: async (_url, init) => {
    sent = true;
    const headers = new Headers(init.headers);
    assert.ok(headers.get('authorization') === 'Bearer personal-runtime-fake-token', 'interpreter must retain the personal login');
    return new Response('{}', { status: 200, headers: { 'Content-Type': 'application/json' } });
  } });
  assert.equal(result.state, 'healthy'); assert.equal(sent, true); assert.equal(w.tokens.length, 0);
});

for (const preferred of [false, true]) test(`automatic App worker keeps personal interpreter authentication with preferred gh ${preferred}`, async t => {
  const w = await githubAppWorld(t), fakeBin = join(w.dir, 'automatic-runtime-bin'), runDir = join(w.dir, 'automatic-runtime-run');
  mkdirSync(fakeBin); mkdirSync(runDir);
  const callsFile = join(w.dir, 'personal-gh-calls.json');
  writeFileSync(join(fakeBin, 'gh'), `#!${process.execPath}
require('node:fs').writeFileSync(${JSON.stringify(callsFile)}, JSON.stringify(process.argv.slice(2)));
if (process.argv[2] === 'auth' && process.argv[3] === 'token') console.log('personal-runtime-fake-token');
else process.exitCode = 1;
`, { mode: 0o755 });
  const env = { ...w.env, PATH: `${fakeBin}:${w.env.PATH}`, PDD_GITHUB_ROOT: w.stateRoot };
  const launch = chatLaunch({ run: { sourceRoot: w.cwd, root: w.cwd, runDir, automaticOrigin: true }, agent: 'codex', env });
  assert.equal(launch.githubEnv.PDD_GITHUB_APP_ROOT, w.cwd);
  const writeExecutable = join(launch.githubEnv.PATH.split(':')[0], 'gh');
  const { checkRuntimeHealth } = await import('../src/runtime-client.mjs');
  let sent = 0;
  const result = await checkRuntimeHealth({ env: { ...env, ...launch.githubEnv } }, {
    ...(preferred ? { ghPath: writeExecutable } : {}),
    fetch: async (_url, init) => {
      sent++;
      assert.ok(new Headers(init.headers).get('authorization') === 'Bearer personal-runtime-fake-token');
      return new Response('{}', { status: 200, headers: { 'Content-Type': 'application/json' } });
    },
  });
  assert.equal(result.state, 'healthy');
  assert.equal(sent, 1);
  assert.deepEqual(JSON.parse(readFileSync(callsFile, 'utf8')), ['auth', 'token']);
  assert.equal(w.tokens.length, 0);
  assert.ok(!JSON.stringify(result).includes('personal-runtime-fake-token'));
});
