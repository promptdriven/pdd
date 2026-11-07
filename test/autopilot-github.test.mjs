import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { runPdd } from '../src/pdd-cli.mjs';

// These tests never call GitHub: each one injects a fake GitHub port, or puts a fake gh first on PATH.
const capture = () => ({ text: '', write(value) { this.text += value; } });
const decode = content => JSON.parse(Buffer.from(content, 'base64').toString('utf8'));
const file = (value, sha) => ({ text: `${JSON.stringify(value)}\n`, sha });
function repo(t) {
  const cwd = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-autopilot-github-')));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', '-b', 'main', cwd]);
  const git = (...args) => execFileSync('git', ['-c', 'user.name=PDD Test', '-c', 'user.email=pdd@example.invalid', ...args], { cwd, encoding: 'utf8' });
  return { cwd, git };
}
async function invoke(cwd, argv, extra = {}) {
  const stdout = capture(), stderr = capture();
  const exitCode = await runPdd(argv, { cwd, stdout, stderr, ...extra });
  return { exitCode, stdout: stdout.text, stderr: stderr.text };
}
// A fake GitHub REST API for acme/widgets. files maps a branch to its pdd.json; refuse is the status of a direct PUT on main.
function fakeGithub({ files = {}, refuse = 0, offline = '' } = {}) {
  const calls = [];
  let blobs = 0;
  const github = {
    async repository() {
      if (offline === 'repository') throw Object.assign(Error('workflow_github_command_failed'), { code: 'workflow_github_command_failed', detail: 'gh auth login' });
      return { repository: 'acme/widgets', defaultBranch: 'main' };
    },
    async request(request) {
      calls.push(structuredClone(request));
      if (offline === 'request') throw Error('no HTTP answer');
      const { method, path, body } = request;
      if (offline === '401') return { status: 401, body: { message: 'Bad credentials' } };
      const contents = /^repos\/acme\/widgets\/contents\/pdd\.json\?ref=(.+)$/.exec(path);
      if (method === 'GET' && contents) {
        const found = files[decodeURIComponent(contents[1])];
        return found ? { status: 200, body: { type: 'file', encoding: 'base64', sha: found.sha, content: Buffer.from(found.text).toString('base64') } }
          : { status: 404, body: { message: 'Not Found' } };
      }
      if (method === 'PUT' && path === 'repos/acme/widgets/contents/pdd.json') {
        if (refuse && body.branch === 'main') return { status: refuse, body: { message: 'Changes must be made through a pull request.' } };
        if (files[body.branch]?.sha !== body.sha) return { status: 409, body: { message: 'sha mismatch' } };
        files[body.branch] = { text: Buffer.from(body.content, 'base64').toString('utf8'), sha: `blob-${++blobs}` };
        return { status: 200, body: { commit: { sha: `c${blobs}`, html_url: `https://github.com/acme/widgets/commit/c${blobs}` } } };
      }
      if (method === 'GET' && path === 'repos/acme/widgets/git/ref/heads/main') return { status: 200, body: { object: { sha: 'head-of-main' } } };
      if (method === 'POST' && path === 'repos/acme/widgets/git/refs') { files[body.ref.replace('refs/heads/', '')] = files.main && { ...files.main }; return { status: 201, body: {} }; }
      if (method === 'POST' && path === 'repos/acme/widgets/pulls') return { status: 201, body: { html_url: 'https://github.com/acme/widgets/pull/7' } };
      return { status: 404, body: { message: 'Not Found' } };
    },
  };
  return { ports: { github, shortId: () => 'a1b2c3d4' }, calls, files };
}
const writes = calls => calls.filter(call => call.method !== 'GET');

// Wrong: a mode command makes an empty commit on GitHub when GitHub already has the same setting.
test('autopilot-github: a mode command that GitHub already has writes nothing there', async t => {
  const { cwd } = repo(t);
  const fake = fakeGithub({ files: { main: file({ keep: 1, autopilot: { trust: [], mode: 'auto' } }, 'blob-main') } });
  const result = await invoke(cwd, ['autopilot', 'auto'], { autopilotGithubPorts: fake.ports });
  assert.equal(result.exitCode, 0, result.stderr);
  assert.equal(result.stdout, 'Autopilot: auto. Explicit trust: (none).\npdd.json on GitHub is already up to date.\n');
  assert.deepEqual(writes(fake.calls), []);
  assert.deepEqual(JSON.parse(readFileSync(join(cwd, 'pdd.json'))).autopilot, { mode: 'auto', trust: [] });
});

// Wrong: the mode stays in this checkout, the write goes to the current branch, or it carries other local edits to GitHub.
test('autopilot-github: mode and trust commands write only pdd.json to the default branch with the current blob sha', async t => {
  const { cwd, git } = repo(t);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ strict_approvals: true, autopilot: { mode: 'off', trust: [] } }));
  git('add', 'pdd.json'); git('commit', '-q', '-m', 'start'); git('switch', '-q', '-c', 'my-work');
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ strict_approvals: false, autopilot: { mode: 'off', trust: [] } }));
  writeFileSync(join(cwd, 'notes.txt'), 'uncommitted work\n');
  const before = { head: git('rev-parse', 'HEAD'), branch: git('branch', '--show-current'), status: git('status', '--porcelain', '--untracked-files=all') };
  const fake = fakeGithub({ files: { main: file({ strict_approvals: true, autopilot: { mode: 'off', trust: [] } }, 'blob-main') } });

  const auto = await invoke(cwd, ['autopilot', 'auto'], { autopilotGithubPorts: fake.ports });
  assert.equal(auto.exitCode, 0, auto.stderr);
  assert.equal(auto.stderr, '');
  assert.match(auto.stdout, /^Updated pdd\.json on GitHub \(main\): https:\/\/github\.com\/acme\/widgets\/commit\/c1$/m);
  const [put] = writes(fake.calls);
  assert.equal(writes(fake.calls).length, 1, JSON.stringify(fake.calls));
  assert.equal(put.method, 'PUT');
  assert.equal(put.path, 'repos/acme/widgets/contents/pdd.json');
  assert.equal(put.body.branch, 'main');
  assert.equal(put.body.sha, 'blob-main');
  assert.equal(put.body.message, 'Set PDD Autopilot mode to auto');
  // GitHub keeps its own strict_approvals; only the autopilot key changes.
  assert.deepEqual(decode(put.body.content), { strict_approvals: true, autopilot: { mode: 'auto', trust: [] } });

  const trust = await invoke(cwd, ['autopilot', 'trust', 'Dana'], { autopilotGithubPorts: fake.ports });
  assert.equal(trust.exitCode, 0, trust.stderr);
  const second = writes(fake.calls)[1];
  assert.equal(second.body.sha, 'blob-1', 'The second write uses the blob sha of the first');
  assert.equal(second.body.message, 'Update PDD Autopilot trust list');
  assert.deepEqual(decode(second.body.content).autopilot, { mode: 'auto', trust: ['Dana'] });

  // The checkout is the same: branch, HEAD, the other uncommitted file and the same changed and untracked paths.
  assert.equal(git('rev-parse', 'HEAD'), before.head);
  assert.equal(git('branch', '--show-current'), before.branch);
  assert.equal(git('status', '--porcelain', '--untracked-files=all'), before.status);
  assert.equal(readFileSync(join(cwd, 'notes.txt'), 'utf8'), 'uncommitted work\n');
  assert.equal(JSON.parse(readFileSync(join(cwd, 'pdd.json'))).strict_approvals, false);
});

// Wrong (protected default branch): the command fails, or says the mode is on GitHub when no PR exists.
test('autopilot-github: a default branch that refuses the write gets a branch and a PR that changes only pdd.json', async t => {
  for (const status of [403, 409, 422]) {
    const { cwd } = repo(t);
    const fake = fakeGithub({ refuse: status, files: { main: file({ keep: 1, autopilot: { mode: 'off', trust: [] } }, 'blob-main') } });
    const result = await invoke(cwd, ['autopilot', 'auto'], { autopilotGithubPorts: fake.ports });
    assert.equal(result.exitCode, 0, result.stderr);
    assert.match(result.stdout, /^main does not accept a direct change, so pdd opened https:\/\/github\.com\/acme\/widgets\/pull\/7\. Merge it before Autopilot workers use the new mode\.$/m, `${status}`);
    const branch = 'pdd/autopilot-settings-a1b2c3d4';
    assert.deepEqual(writes(fake.calls).map(call => [call.method, call.path, call.body.branch ?? call.body.ref ?? call.body.head]), [
      ['PUT', 'repos/acme/widgets/contents/pdd.json', 'main'],
      ['POST', 'repos/acme/widgets/git/refs', `refs/heads/${branch}`],
      ['PUT', 'repos/acme/widgets/contents/pdd.json', branch],
      ['POST', 'repos/acme/widgets/pulls', branch],
    ], `${status}`);
    const [, ref, put, pull] = writes(fake.calls);
    assert.equal(ref.body.sha, 'head-of-main');
    assert.equal(put.body.sha, 'blob-main');
    assert.deepEqual(decode(put.body.content), { keep: 1, autopilot: { mode: 'auto', trust: [] } });
    assert.equal(pull.body.base, 'main');
    assert.equal(pull.body.title, 'Turn on PDD Autopilot');
    assert.equal(fake.files.main.sha, 'blob-main', 'main stays unchanged');
  }
  const { cwd } = repo(t);
  const fake = fakeGithub({ refuse: 409, files: { main: file({ autopilot: { mode: 'auto', trust: [] } }, 'blob-main') } });
  assert.equal((await invoke(cwd, ['autopilot', 'observe'], { autopilotGithubPorts: fake.ports })).exitCode, 0);
  assert.equal(writes(fake.calls).at(-1).body.title, 'Update PDD Autopilot settings');
});

// Wrong (offline or signed out): the command fails and loses the local mode, or says nothing about GitHub.
test('autopilot-github: without GitHub the local write stays, exit is 0 and one line says how to retry', async t => {
  for (const offline of ['repository', 'request', '401']) {
    const { cwd } = repo(t);
    const fake = fakeGithub({ offline });
    const result = await invoke(cwd, ['autopilot', 'observe'], { autopilotGithubPorts: fake.ports });
    assert.equal(result.exitCode, 0, result.stderr);
    assert.equal(result.stderr, '');
    const lines = result.stdout.trimEnd().split('\n');
    assert.equal(lines.length, 2, result.stdout);
    assert.match(lines[1], /^pdd\.json on GitHub was not updated: .+\. To retry, run pdd autopilot observe\.$/, offline);
    assert.deepEqual(writes(fake.calls), []);
    assert.equal(JSON.parse(readFileSync(join(cwd, 'pdd.json'))).autopilot.mode, 'observe');
  }
  // The native port: a repository with no origin remote stops before gh.
  const { cwd } = repo(t);
  const result = await invoke(cwd, ['autopilot', 'trust', 'Dana']);
  assert.equal(result.exitCode, 0, result.stderr);
  assert.match(result.stdout, /^pdd\.json on GitHub was not updated: this repository has no origin remote\. .*To retry, run pdd autopilot trust Dana\.$/m);
});

// Wrong: start runs with a mode that the workers on GitHub do not have, and nothing says so.
test('autopilot-github: start and status warn once when GitHub has other settings, and never write', async t => {
  const { cwd } = repo(t);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: ['Dana'] } }));
  const launcher = { runAutopilotLauncher: async () => ({ exitCode: 0, message: 'Autopilot running.' }) };
  for (const command of ['start', 'status']) {
    const fake = fakeGithub({ files: { main: file({ autopilot: { mode: 'observe', trust: [] } }, 'blob-main') } });
    const result = await invoke(cwd, ['autopilot', command], { autopilotLauncher: launcher, autopilotGithubPorts: fake.ports });
    assert.equal(result.exitCode, 0, result.stderr);
    assert.equal(result.stdout, 'Autopilot running.\n');
    assert.equal(result.stderr.trimEnd().split('\n').length, 1, result.stderr);
    assert.match(result.stderr, /^Warning: pdd\.json on GitHub \(main\) has other Autopilot settings \(GitHub: observe, trust \(none\); this checkout: auto, trust Dana\)\..*run pdd autopilot auto\.\n$/);
    assert.deepEqual(writes(fake.calls), [], command);
  }
  for (const fake of [fakeGithub({ files: { main: file({ autopilot: { trust: ['DANA'], mode: 'auto' } }, 'blob-main') } }), fakeGithub({ offline: 'request' })]) {
    const result = await invoke(cwd, ['autopilot', 'start'], { autopilotLauncher: launcher, autopilotGithubPorts: fake.ports });
    assert.equal(result.exitCode, 0);
    assert.equal(result.stderr, '', 'The same settings, or no GitHub, print no warning');
  }
  const stopped = fakeGithub();
  assert.equal((await invoke(cwd, ['autopilot', 'stop'], { autopilotLauncher: launcher, autopilotGithubPorts: stopped.ports })).exitCode, 0);
  assert.deepEqual(stopped.calls, [], 'stop does not read GitHub');
});

// Wrong: the native gh port sends another request than the fake port shows, or misreads a refusal of gh.
test('autopilot-github: the public CLI uses gh api for the read, the write and the PR fallback', t => {
  const { cwd, git } = repo(t);
  git('remote', 'add', 'origin', 'https://github.com/acme/widgets.git');
  const bin = join(cwd, '.fake-bin'), log = join(cwd, '.fake-gh.log'), routes = join(cwd, '.fake-gh.json');
  mkdirSync(bin);
  writeFileSync(join(bin, 'gh'), `#!${process.execPath}
const fs = require('node:fs');
const args = process.argv.slice(2), input = args.includes('--input') ? fs.readFileSync(0, 'utf8') : '';
fs.appendFileSync(${JSON.stringify(log)}, JSON.stringify({ args, input }) + '\\n');
if (args[0] === 'repo') { process.stdout.write(JSON.stringify({ nameWithOwner: 'acme/widgets', defaultBranchRef: { name: 'main' }, url: 'https://github.com/acme/widgets' })); process.exit(0); }
const method = args[args.indexOf('--method') + 1], path = args.find(arg => arg.startsWith('repos/'));
const body = input ? JSON.parse(input) : {};
// The branch suffix is random: one route serves each suffix.
const key = [method, path, body.branch ?? ''].join(' ').replace(/autopilot-settings-[0-9a-f]{8}/g, 'autopilot-settings-ID');
const reply = JSON.parse(fs.readFileSync(${JSON.stringify(routes)}, 'utf8'))[key] ?? { status: 404, body: { message: 'Not Found' } };
process.stdout.write(JSON.stringify(reply.body));
if (reply.status >= 300) { process.stderr.write('gh: ' + reply.body.message + ' (HTTP ' + reply.status + ')\\n'); process.exit(1); }
`, { mode: 0o755 });
  const content = Buffer.from(`${JSON.stringify({ keep: 1, autopilot: { mode: 'off', trust: [] } })}\n`).toString('base64');
  const fileReply = { status: 200, body: { type: 'file', encoding: 'base64', sha: 'blob-main', content } };
  const commit = { status: 200, body: { commit: { html_url: 'https://github.com/acme/widgets/commit/c1' } } };
  const env = { ...process.env, PATH: `${bin}:${process.env.PATH}` };
  const pdd = mode => spawnSync(process.execPath, [fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url)), 'autopilot', mode], { cwd, env, encoding: 'utf8', timeout: 20000 });
  const calls = () => readFileSync(log, 'utf8').trim().split('\n').map(line => JSON.parse(line)).filter(call => call.args[0] === 'api');

  writeFileSync(routes, JSON.stringify({ 'GET repos/acme/widgets/contents/pdd.json?ref=main ': fileReply, 'PUT repos/acme/widgets/contents/pdd.json main': commit }));
  const direct = pdd('auto');
  assert.equal(direct.status, 0, direct.stderr);
  assert.match(direct.stdout, /^Updated pdd\.json on GitHub \(main\): https:\/\/github\.com\/acme\/widgets\/commit\/c1$/m);
  const put = calls().find(call => call.args.includes('PUT'));
  assert.deepEqual(put.args.slice(0, 3), ['api', '--method', 'PUT']);
  assert.ok(put.args.includes('repos/acme/widgets/contents/pdd.json') && put.args.at(-2) === '--input' && put.args.at(-1) === '-', put.args.join(' '));
  const body = JSON.parse(put.input);
  assert.equal(body.sha, 'blob-main'); assert.equal(body.branch, 'main');
  assert.deepEqual(decode(body.content), { keep: 1, autopilot: { mode: 'auto', trust: [] } });

  rmSync(log);
  writeFileSync(routes, JSON.stringify({
    'GET repos/acme/widgets/contents/pdd.json?ref=main ': fileReply,
    'PUT repos/acme/widgets/contents/pdd.json main': { status: 409, body: { message: 'Changes must be made through a pull request.' } },
    'GET repos/acme/widgets/git/ref/heads/main ': { status: 200, body: { object: { sha: 'head-of-main' } } },
    'POST repos/acme/widgets/git/refs ': { status: 200, body: { ref: 'refs/heads/pdd/autopilot-settings-ID' } },
    'GET repos/acme/widgets/contents/pdd.json?ref=pdd%2Fautopilot-settings-ID ': fileReply,
    'PUT repos/acme/widgets/contents/pdd.json pdd/autopilot-settings-ID': commit,
    'POST repos/acme/widgets/pulls ': { status: 200, body: { html_url: 'https://github.com/acme/widgets/pull/7' } },
  }));
  const fallback = pdd('observe');
  assert.equal(fallback.status, 0, fallback.stderr);
  assert.match(fallback.stdout, /^main does not accept a direct change, so pdd opened https:\/\/github\.com\/acme\/widgets\/pull\/7\. Merge it/m);
  const sent = calls();
  const name = JSON.parse(sent.find(call => call.args.includes('repos/acme/widgets/git/refs')).input).ref.replace('refs/heads/', '');
  assert.match(name, /^pdd\/autopilot-settings-[0-9a-f]{8}$/);
  const onBranch = JSON.parse(sent.filter(call => call.args.includes('PUT')).at(-1).input);
  assert.equal(onBranch.branch, name); assert.equal(onBranch.sha, 'blob-main');
  const pull = JSON.parse(sent.find(call => call.args.includes('repos/acme/widgets/pulls')).input);
  assert.deepEqual([pull.head, pull.base, pull.title], [name, 'main', 'Turn on PDD Autopilot']);

  // gh that is not signed in has no HTTP answer: the local write stays.
  writeFileSync(join(bin, 'gh'), '#!/bin/sh\necho "To get started with GitHub CLI, please run:  gh auth login" >&2\nexit 4\n', { mode: 0o755 });
  const signedOut = pdd('off');
  assert.equal(signedOut.status, 0, signedOut.stderr);
  assert.match(signedOut.stdout, /^pdd\.json on GitHub was not updated: GitHub could not be reached or gh is not signed in\. .*run pdd autopilot off\.$/m);
  assert.equal(JSON.parse(readFileSync(join(cwd, 'pdd.json'))).autopilot.mode, 'off');
});
