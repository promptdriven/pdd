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
// A fake GitHub REST API for acme/widgets. files maps a branch to its pdd.json; refuse is the status of a direct PUT on main;
// onPut can make a teammate's commit between the read and the write; pulls are open PRs that exist before the test.
function fakeGithub({ files = {}, refuse = 0, offline = '', refs = 201, onPut, pulls: seeded = [] } = {}) {
  const calls = [], pulls = seeded.map(({ number, ref, repo = 'acme/widgets' }) => ({ number, state: 'open', html_url: `https://github.com/acme/widgets/pull/${number}`, head: { ref, repo: { full_name: repo } }, comments: [] }));
  let blobs = 0;
  const pull = path => pulls.find(item => path.endsWith(`/${item.number}`) || path.endsWith(`/${item.number}/comments`));
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
      if (method === 'GET' && path.startsWith('repos/acme/widgets/pulls?state=open&base=main&per_page=100&page=')) {
        return { status: 200, body: path.endsWith('page=1') ? structuredClone(pulls.filter(item => item.state === 'open')) : [] };
      }
      if (method === 'PUT' && path === 'repos/acme/widgets/contents/pdd.json') {
        onPut?.(body, files);
        if (refuse && body.branch === 'main') return { status: refuse, body: { message: 'Changes must be made through a pull request.' } };
        if (files[body.branch] && !body.sha) return { status: 422, body: { message: 'Invalid request. "sha" wasn\'t supplied.' } };
        if (files[body.branch]?.sha !== body.sha) return { status: 409, body: { message: `pdd.json does not match ${body.sha}` } };
        files[body.branch] = { text: Buffer.from(body.content, 'base64').toString('utf8'), sha: `blob-${++blobs}` };
        return { status: 200, body: { commit: { sha: `c${blobs}`, html_url: `https://github.com/acme/widgets/commit/c${blobs}` } } };
      }
      if (method === 'GET' && path === 'repos/acme/widgets/git/ref/heads/main') return { status: 200, body: { object: { sha: 'head-of-main' } } };
      if (method === 'POST' && path === 'repos/acme/widgets/git/refs') {
        if (refs !== 201) return { status: refs, body: { message: 'Resource not accessible by integration' } };
        files[body.ref.replace('refs/heads/', '')] = files.main && { ...files.main };
        return { status: 201, body: {} };
      }
      if (method === 'POST' && path === 'repos/acme/widgets/pulls') {
        const number = 7 + pulls.filter(item => item.number >= 7).length;
        pulls.push({ number, state: 'open', html_url: `https://github.com/acme/widgets/pull/${number}`, title: body.title, body: body.body, head: { ref: body.head, repo: { full_name: 'acme/widgets' } }, comments: [] });
        return { status: 201, body: { html_url: `https://github.com/acme/widgets/pull/${number}` } };
      }
      if (method === 'PATCH' && /^repos\/acme\/widgets\/pulls\/\d+$/.test(path) && pull(path)) { Object.assign(pull(path), body); return { status: 200, body: {} }; }
      if (method === 'POST' && /^repos\/acme\/widgets\/issues\/\d+\/comments$/.test(path) && pull(path)) { pull(path).comments.push(body.body); return { status: 201, body: {} }; }
      return { status: 404, body: { message: 'Not Found' } };
    },
  };
  return { ports: { github, shortId: () => 'a1b2c3d4' }, calls, files, pulls, open: () => pulls.filter(item => item.state === 'open') };
}
const writes = calls => calls.filter(call => call.method !== 'GET');
const lines = text => text.trimEnd().split('\n');
const PULL = 'pdd.json on GitHub is updated. To update your local copy, run git restore pdd.json, then git pull.';
const noGithub = Error('Tests never call GitHub');
// For a test that runs the native port: real git, and a gh that never runs.
function gitOnly(blocked) {
  return async (file, args, { cwd }) => {
    if (file !== 'git') { blocked.push([file, ...args]); throw noGithub; }
    const result = spawnSync('git', args, { cwd, encoding: 'utf8' });
    if (result.status) throw Object.assign(Error('git failed'), { code: result.status, stdout: result.stdout, stderr: result.stderr });
    return { stdout: result.stdout, stderr: result.stderr };
  };
}

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

// Wrong: the mode stays in this checkout, the write goes to the current branch, it carries other local edits to GitHub,
// or the person is not told to pull the new commit.
test('autopilot-github: mode and trust commands write only pdd.json to the default branch, then say to pull', async t => {
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
  assert.deepEqual(lines(auto.stdout), ['Autopilot: auto. Explicit trust: (none).', 'Updated pdd.json on GitHub (main): https://github.com/acme/widgets/commit/c1', PULL]);
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
  assert.equal(lines(trust.stdout).at(-1), PULL);
  const second = writes(fake.calls)[1];
  assert.equal(second.body.sha, 'blob-1', 'The second write uses the blob sha of the first');
  assert.equal(second.body.message, 'Add Dana to the PDD Autopilot trust list');
  assert.deepEqual(decode(second.body.content).autopilot, { mode: 'auto', trust: ['Dana'] });

  // The checkout is the same: branch, HEAD, the other uncommitted file and the same changed and untracked paths.
  assert.equal(git('rev-parse', 'HEAD'), before.head);
  assert.equal(git('branch', '--show-current'), before.branch);
  assert.equal(git('status', '--porcelain', '--untracked-files=all'), before.status);
  assert.equal(readFileSync(join(cwd, 'notes.txt'), 'utf8'), 'uncommitted work\n');
  assert.equal(JSON.parse(readFileSync(join(cwd, 'pdd.json'))).strict_approvals, false);
});

// Wrong: the printed hint does not work, because the local write leaves pdd.json changed and a plain git pull stops on it.
test('autopilot-github: the printed commands update the local copy after a direct write', async t => {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-autopilot-github-pull-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const git = (cwd, ...args) => spawnSync('git', ['-c', 'user.name=PDD Test', '-c', 'user.email=pdd@example.invalid', ...args], { cwd, encoding: 'utf8' });
  const origin = join(root, 'origin.git'), hub = join(root, 'github'), cwd = join(root, 'checkout');
  git(root, 'init', '-q', '--bare', '-b', 'main', origin);
  git(root, 'clone', '-q', origin, hub);
  writeFileSync(join(hub, 'pdd.json'), `${JSON.stringify({ autopilot: { mode: 'off', trust: [] } })}\n`);
  git(hub, 'add', 'pdd.json'); git(hub, 'commit', '-q', '-m', 'start'); git(hub, 'push', '-q', 'origin', 'HEAD:main');
  git(root, 'clone', '-q', origin, cwd);
  // The fake GitHub PUT also makes the real commit on origin/main.
  const fake = fakeGithub({ files: { main: file({ autopilot: { mode: 'off', trust: [] } }, 'blob-main') }, onPut: body => {
    writeFileSync(join(hub, 'pdd.json'), Buffer.from(body.content, 'base64'));
    git(hub, 'commit', '-q', '-am', body.message); git(hub, 'push', '-q', 'origin', 'HEAD:main');
  } });
  const result = await invoke(cwd, ['autopilot', 'auto'], { autopilotGithubPorts: fake.ports });
  assert.equal(result.exitCode, 0, result.stderr);
  const hint = lines(result.stdout).at(-1);
  assert.equal(hint, PULL);
  assert.notEqual(git(cwd, 'pull', '-q', '--ff-only').status, 0, 'a plain git pull stops on the local pdd.json change');
  const [, restore, pull] = /run (git restore pdd\.json), then (git pull)\.$/.exec(hint);
  for (const command of [restore, pull]) { const run = git(cwd, ...command.split(' ').slice(1)); assert.equal(run.status, 0, `${command}: ${run.stderr}`); }
  assert.equal(git(cwd, 'rev-parse', 'HEAD').stdout, git(cwd, 'rev-parse', 'origin/main').stdout);
  assert.equal(git(cwd, 'status', '--porcelain').stdout, '');
  assert.deepEqual(JSON.parse(readFileSync(join(cwd, 'pdd.json'), 'utf8')).autopilot, { mode: 'auto', trust: [] });
});

// Wrong (M2): a stale checkout copies its whole autopilot value to GitHub, so trust turns the mode on again,
// or a mode command trusts again a name that a teammate removed on GitHub.
test('autopilot-github: a stale checkout changes only the part of its command on GitHub, and says that the checkout differs', async t => {
  const { cwd } = repo(t);
  const fake = fakeGithub({ files: { main: file({ keep: 1, autopilot: { mode: 'off', trust: [] } }, 'blob-main') } });
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: ['Eve'] } }));
  const trust = await invoke(cwd, ['autopilot', 'trust', 'Dana'], { autopilotGithubPorts: fake.ports });
  assert.equal(trust.exitCode, 0, trust.stderr);
  let put = writes(fake.calls).at(-1);
  assert.deepEqual(decode(put.body.content), { keep: 1, autopilot: { mode: 'off', trust: ['Dana'] } }, 'trust does not change the mode');
  assert.equal(put.body.message, 'Add Dana to the PDD Autopilot trust list');
  assert.deepEqual(lines(trust.stdout), ['Autopilot: auto. Explicit trust: Eve, Dana.', 'Updated pdd.json on GitHub (main): https://github.com/acme/widgets/commit/c1',
    'This checkout has other Autopilot settings (GitHub: off, trust Dana; this checkout: auto, trust Eve, Dana).', PULL]);

  // A teammate removed Eve on GitHub; this checkout still has her.
  fake.files.main = file({ keep: 1, autopilot: { mode: 'auto', trust: ['Bo'] } }, 'blob-teammate');
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'off', trust: ['Eve', 'Bo'] } }));
  const observe = await invoke(cwd, ['autopilot', 'observe'], { autopilotGithubPorts: fake.ports });
  assert.equal(observe.exitCode, 0, observe.stderr);
  put = writes(fake.calls).at(-1);
  assert.deepEqual(decode(put.body.content).autopilot, { mode: 'observe', trust: ['Bo'] }, 'observe does not trust Eve again');
  assert.equal(put.body.sha, 'blob-teammate');
  assert.equal(put.body.message, 'Set PDD Autopilot mode to observe');
  assert.match(observe.stdout, /^This checkout has other Autopilot settings \(GitHub: observe, trust Bo; this checkout: observe, trust Eve, Bo\)\.$/m);

  const untrust = await invoke(cwd, ['autopilot', 'untrust', 'bo'], { autopilotGithubPorts: fake.ports });
  assert.equal(untrust.exitCode, 0, untrust.stderr);
  put = writes(fake.calls).at(-1);
  assert.equal(put.body.message, 'Remove bo from the PDD Autopilot trust list');
  assert.deepEqual(decode(put.body.content).autopilot, { mode: 'observe', trust: [] });
  // A name that GitHub does not have: nothing to write, also when this checkout has it.
  const count = writes(fake.calls).length;
  const absent = await invoke(cwd, ['autopilot', 'untrust', 'Eve'], { autopilotGithubPorts: fake.ports });
  assert.equal(absent.exitCode, 0, absent.stderr);
  assert.equal(writes(fake.calls).length, count);
  assert.match(absent.stdout, /^pdd\.json on GitHub is already up to date\.$/m);
});

// Wrong (F1): another commit between the read and the write makes pdd open a PR and say that main refuses direct changes.
test('autopilot-github: a blob sha conflict reads GitHub again and retries the direct write once', async t => {
  for (const [name, start, teammate] of [
    ['409 on a changed file', file({ keep: 1, autopilot: { mode: 'off', trust: [] } }, 'blob-main'), { keep: 2, autopilot: { mode: 'off', trust: ['Zed'] } }],
    ['422 on a file made meanwhile', undefined, { keep: 2, autopilot: { mode: 'off', trust: ['Zed'] } }],
  ]) {
    const { cwd } = repo(t);
    let commits = 0;
    const fake = fakeGithub({ files: start ? { main: start } : {}, onPut: (body, files) => { if (!commits++) files.main = file(teammate, 'blob-teammate'); } });
    const result = await invoke(cwd, ['autopilot', 'auto'], { autopilotGithubPorts: fake.ports });
    assert.equal(result.exitCode, 0, result.stderr);
    assert.deepEqual(writes(fake.calls).map(call => [call.method, call.body.branch, call.body.sha]), [['PUT', 'main', start?.sha], ['PUT', 'main', 'blob-teammate']], name);
    assert.deepEqual(decode(writes(fake.calls)[1].body.content), { keep: 2, autopilot: { mode: 'auto', trust: ['Zed'] } }, name);
    assert.deepEqual(lines(result.stdout).slice(1), ['Updated pdd.json on GitHub (main): https://github.com/acme/widgets/commit/c1',
      'This checkout has other Autopilot settings (GitHub: auto, trust Zed; this checkout: auto, trust (none)).', PULL], name);
    assert.doesNotMatch(result.stdout, /does not accept/);
  }
  // A second conflict stops with one line; it never opens a PR.
  const { cwd } = repo(t);
  let sha = 0;
  const fake = fakeGithub({ files: { main: file({ autopilot: { mode: 'off', trust: [] } }, 'blob-main') }, onPut: (body, files) => { files.main = file({ keep: ++sha }, `blob-teammate-${sha}`); } });
  const result = await invoke(cwd, ['autopilot', 'auto'], { autopilotGithubPorts: fake.ports });
  assert.equal(result.exitCode, 0, result.stderr);
  assert.deepEqual(writes(fake.calls).map(call => call.method), ['PUT', 'PUT']);
  assert.equal(lines(result.stdout)[1], 'pdd.json on GitHub was not updated: pdd.json on main changed again while pdd wrote it. This checkout has the new setting. To retry, run pdd autopilot auto.');
});

// Wrong (protected default branch): the command fails, or says the mode is on GitHub when no PR exists, or blames protection for no push access.
test('autopilot-github: a default branch that refuses the write gets a branch and a PR that changes only pdd.json', async t => {
  for (const status of [403, 409, 422]) {
    const { cwd } = repo(t);
    const fake = fakeGithub({ refuse: status, files: { main: file({ keep: 1, autopilot: { mode: 'off', trust: [] } }, 'blob-main') } });
    const result = await invoke(cwd, ['autopilot', 'auto'], { autopilotGithubPorts: fake.ports });
    assert.equal(result.exitCode, 0, result.stderr);
    assert.deepEqual(lines(result.stdout).slice(1), ['main does not accept a direct change, so pdd opened https://github.com/acme/widgets/pull/7. Merge it before Autopilot workers use the new mode.'], `${status}`);
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
  let { cwd } = repo(t);
  let fake = fakeGithub({ refuse: 409, files: { main: file({ autopilot: { mode: 'auto', trust: [] } }, 'blob-main') } });
  assert.equal((await invoke(cwd, ['autopilot', 'observe'], { autopilotGithubPorts: fake.ports })).exitCode, 0);
  assert.equal(writes(fake.calls).at(-1).body.title, 'Update PDD Autopilot settings');
  // No push access: the line says so, and does not blame branch protection.
  ({ cwd } = repo(t));
  fake = fakeGithub({ refuse: 403, refs: 403, files: { main: file({ autopilot: { mode: 'off', trust: [] } }, 'blob-main') } });
  const denied = await invoke(cwd, ['autopilot', 'auto'], { autopilotGithubPorts: fake.ports });
  assert.equal(denied.exitCode, 0, denied.stderr);
  assert.equal(lines(denied.stdout)[1], 'pdd.json on GitHub was not updated: you cannot push to acme/widgets (HTTP 403). This checkout has the new setting. To retry, run pdd autopilot auto.');
});

// Wrong (M1): each rerun opens one more settings PR, and a status warning sends the person to make the next one.
test('autopilot-github: an open settings PR is reused, named by status and updated with one commit', async t => {
  const { cwd } = repo(t);
  const fake = fakeGithub({ refuse: 409, files: { main: file({ keep: 1, autopilot: { mode: 'off', trust: [] } }, 'blob-main') } });
  const branch = 'pdd/autopilot-settings-a1b2c3d4', url = 'https://github.com/acme/widgets/pull/7';
  assert.equal((await invoke(cwd, ['autopilot', 'auto'], { autopilotGithubPorts: fake.ports })).exitCode, 0);
  assert.deepEqual(fake.open().map(pull => pull.html_url), [url]);

  const count = writes(fake.calls).length;
  const again = await invoke(cwd, ['autopilot', 'auto'], { autopilotGithubPorts: fake.ports });
  assert.equal(again.exitCode, 0, again.stderr);
  assert.equal(writes(fake.calls).length, count, 'The same setting writes nothing');
  assert.deepEqual(lines(again.stdout).slice(1), [`The open PR ${url} already has this setting. Merge it before Autopilot workers use the new mode.`]);

  const launcher = { runAutopilotLauncher: async () => ({ exitCode: 0, message: 'Autopilot running.' }) };
  const status = await invoke(cwd, ['autopilot', 'status'], { autopilotLauncher: launcher, autopilotGithubPorts: fake.ports });
  assert.equal(status.exitCode, 0);
  assert.equal(status.stderr, `Warning: pdd.json on GitHub (main) has other Autopilot settings (GitHub: off, trust (none); this checkout: auto, trust (none)). Autopilot workers use the GitHub copy. The settings PR ${url} is open: Autopilot workers use its change only after the merge. To change the GitHub copy, run pdd autopilot auto.\n`);

  const trust = await invoke(cwd, ['autopilot', 'trust', 'Dana'], { autopilotGithubPorts: fake.ports });
  assert.equal(trust.exitCode, 0, trust.stderr);
  assert.deepEqual(lines(trust.stdout).slice(1), [`pdd updated the open PR ${url}. Merge it before Autopilot workers use the new trust list.`]);
  const [put, patch] = writes(fake.calls).slice(count);
  assert.deepEqual([put.method, put.body.branch, put.body.sha, put.body.message], ['PUT', branch, 'blob-1', 'Add Dana to the PDD Autopilot trust list']);
  assert.deepEqual([patch.method, patch.path, patch.body.title], ['PATCH', 'repos/acme/widgets/pulls/7', 'Turn on PDD Autopilot']);
  assert.equal(writes(fake.calls).length, count + 2);
  assert.deepEqual(JSON.parse(fake.files[branch].text).autopilot, { mode: 'auto', trust: ['Dana'] });
  assert.deepEqual(fake.open().map(pull => pull.html_url), [url], 'Still one open settings PR');
  assert.equal(fake.files.main.sha, 'blob-main', 'main stays unchanged');
});

// Wrong (M1): off says "up to date" while a "Turn on" PR stays open, and a later merge turns Autopilot on against the last command.
test('autopilot-github: a setting that returns to the default-branch value closes the settings PRs with a comment', async t => {
  let { cwd } = repo(t);
  let fake = fakeGithub({ refuse: 409, files: { main: file({ autopilot: { mode: 'off', trust: [] } }, 'blob-main') } });
  assert.equal((await invoke(cwd, ['autopilot', 'auto'], { autopilotGithubPorts: fake.ports })).exitCode, 0);
  const count = writes(fake.calls).length;
  const off = await invoke(cwd, ['autopilot', 'off'], { autopilotGithubPorts: fake.ports });
  assert.equal(off.exitCode, 0, off.stderr);
  assert.deepEqual(lines(off.stdout).slice(1), ['pdd closed https://github.com/acme/widgets/pull/7, because main already has this setting.']);
  assert.doesNotMatch(off.stdout, /up to date/);
  assert.deepEqual(writes(fake.calls).slice(count).map(call => [call.method, call.path, call.body.state]), [
    ['POST', 'repos/acme/widgets/issues/7/comments', undefined], ['PATCH', 'repos/acme/widgets/pulls/7', 'closed']]);
  assert.deepEqual(fake.pulls[0].comments, ['pdd closed this PR: main already has these Autopilot settings.']);
  assert.deepEqual(fake.open(), []);

  // Two old settings PRs and one from a fork: the newest one is updated, the older one is closed, the fork PR stays.
  ({ cwd } = repo(t));
  const turnOn = file({ autopilot: { mode: 'auto', trust: [] } }, 'blob-pr');
  fake = fakeGithub({ refuse: 409, files: { main: file({ autopilot: { mode: 'off', trust: [] } }, 'blob-main'), 'pdd/autopilot-settings-old': turnOn, 'pdd/autopilot-settings-new': { ...turnOn } },
    pulls: [{ number: 3, ref: 'pdd/autopilot-settings-old' }, { number: 5, ref: 'pdd/autopilot-settings-new' }, { number: 6, ref: 'pdd/autopilot-settings-fork', repo: 'eve/widgets' }] });
  const observe = await invoke(cwd, ['autopilot', 'observe'], { autopilotGithubPorts: fake.ports });
  assert.equal(observe.exitCode, 0, observe.stderr);
  assert.deepEqual(lines(observe.stdout).slice(1), ['pdd updated the open PR https://github.com/acme/widgets/pull/5. Merge it before Autopilot workers use the new mode.']);
  assert.deepEqual(fake.open().map(pull => pull.number), [5, 6]);
  assert.deepEqual(fake.pulls[0].comments, ['pdd closed this PR: https://github.com/acme/widgets/pull/5 has the newest Autopilot settings.']);
  assert.deepEqual(JSON.parse(fake.files['pdd/autopilot-settings-new'].text).autopilot, { mode: 'observe', trust: [] });
  const back = await invoke(cwd, ['autopilot', 'off'], { autopilotGithubPorts: fake.ports });
  assert.deepEqual(lines(back.stdout).slice(1), ['pdd closed https://github.com/acme/widgets/pull/5, because main already has this setting.']);
  assert.deepEqual(fake.open().map(pull => pull.number), [6]);
});

// Wrong (F2): pdd writes the whole GitHub file again, so a 4-space or tab file becomes 2-space and the diff touches every line.
test('autopilot-github: the GitHub file keeps its indent, key order and other bytes', async t => {
  const cases = [
    ['{\n    "z": 1.50,\n    "autopilot": {\n        "trust": [],\n        "mode": "off"\n    },\n    "a": true\n}\n', ['autopilot', 'auto'],
      '{\n    "z": 1.50,\n    "autopilot": {\n        "trust": [],\n        "mode": "auto"\n    },\n    "a": true\n}\n'],
    ['{\n    "z": 1.50,\n    "autopilot": {\n        "trust": [],\n        "mode": "off"\n    },\n    "a": true\n}\n', ['autopilot', 'trust', 'Dana'],
      '{\n    "z": 1.50,\n    "autopilot": {\n        "trust": [\n            "Dana"\n        ],\n        "mode": "off"\n    },\n    "a": true\n}\n'],
    ['{\n\t"keep": 1\n}\n', ['autopilot', 'observe'], '{\n\t"keep": 1,\n\t"autopilot": {\n\t\t"mode": "observe",\n\t\t"trust": []\n\t}\n}\n'],
    ['{\r\n  "keep": 1\r\n}\r\n', ['autopilot', 'observe'], '{\r\n  "keep": 1,\r\n  "autopilot": {\r\n    "mode": "observe",\r\n    "trust": []\r\n  }\r\n}\r\n'],
    ['{"keep":1,"autopilot":{"mode":"off","trust":["Eve"]}}\n', ['autopilot', 'trust', 'Dana'], '{"keep":1,"autopilot":{"mode":"off","trust":["Eve","Dana"]}}\n'],
    ['{\n  "autopilot": { "mode": "off", "trust": ["Eve", "Bo"] }\n}\n', ['autopilot', 'untrust', 'eve'], '{\n  "autopilot": { "mode": "off", "trust": ["Bo"] }\n}\n'],
    ['{\n  "autopilot": "auto"\n}', ['autopilot', 'off'], '{\n  "autopilot": {\n    "mode": "off",\n    "trust": []\n  }\n}'],
  ];
  for (const [before, argv, after] of cases) {
    const { cwd } = repo(t);
    writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'off', trust: ['Eve', 'Bo'] } }));
    const fake = fakeGithub({ files: { main: { text: before, sha: 'blob-main' } } });
    const result = await invoke(cwd, argv, { autopilotGithubPorts: fake.ports });
    assert.equal(result.exitCode, 0, result.stderr);
    assert.equal(fake.files.main.text, after, `${argv.join(' ')} on ${JSON.stringify(before)}`);
  }
});

// Wrong (offline or signed out): the command fails and loses the local mode, or says nothing about GitHub.
test('autopilot-github: without GitHub the local write stays, exit is 0 and one line says how to retry', async t => {
  for (const offline of ['repository', 'request', '401']) {
    const { cwd } = repo(t);
    const fake = fakeGithub({ offline });
    const result = await invoke(cwd, ['autopilot', 'observe'], { autopilotGithubPorts: fake.ports });
    assert.equal(result.exitCode, 0, result.stderr);
    assert.equal(result.stderr, '');
    assert.equal(lines(result.stdout).length, 2, result.stdout);
    assert.match(lines(result.stdout)[1], /^pdd\.json on GitHub was not updated: .+\. To retry, run pdd autopilot observe\.$/, offline);
    assert.deepEqual(writes(fake.calls), []);
    assert.equal(JSON.parse(readFileSync(join(cwd, 'pdd.json'))).autopilot.mode, 'observe');
  }
  // The native port: a repository with no origin remote stops before gh. A stub stands in for gh, so no real gh can run.
  const { cwd } = repo(t);
  const blocked = [];
  const result = await invoke(cwd, ['autopilot', 'trust', 'Dana'], { autopilotGithubPorts: { execFile: gitOnly(blocked) } });
  assert.equal(result.exitCode, 0, result.stderr);
  assert.match(result.stdout, /^pdd\.json on GitHub was not updated: this repository has no origin remote\. .*To retry, run pdd autopilot trust Dana\.$/m);
  assert.deepEqual(blocked, []);
});

// Wrong: start runs with a mode that the workers on GitHub do not have, and nothing says so, or the warning names a command that does not fix the difference.
test('autopilot-github: start and status warn once when GitHub has other settings, and never write', async t => {
  const { cwd } = repo(t);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: ['Dana'] } }));
  const launcher = { runAutopilotLauncher: async () => ({ exitCode: 0, message: 'Autopilot running.' }) };
  for (const command of ['start', 'status']) {
    const fake = fakeGithub({ files: { main: file({ autopilot: { mode: 'observe', trust: ['Eve'] } }, 'blob-main') } });
    const result = await invoke(cwd, ['autopilot', command], { autopilotLauncher: launcher, autopilotGithubPorts: fake.ports });
    assert.equal(result.exitCode, 0, result.stderr);
    assert.equal(result.stdout, 'Autopilot running.\n');
    assert.equal(result.stderr, 'Warning: pdd.json on GitHub (main) has other Autopilot settings (GitHub: observe, trust Eve; this checkout: auto, trust Dana). Autopilot workers use the GitHub copy. '
      + 'To change the GitHub copy, run pdd autopilot auto and pdd autopilot trust Dana and pdd autopilot untrust Eve.\n');
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

// Wrong (F4): setup saves a first mode in this checkout and says nothing, so the person thinks Autopilot is on; or setup writes to GitHub.
test('autopilot-github: setup that saves a first mode says how to update GitHub, and sends nothing there', async t => {
  const hint = mode => `Setup saved the Autopilot mode only in this checkout. Autopilot workers read pdd.json on GitHub; to update it there, run pdd autopilot ${mode}.`;
  for (const [answer, mode] of [['auto', 'auto'], ['', 'off']]) {
    const { cwd } = repo(t);
    const home = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-autopilot-github-home-')));
    t.after(() => rmSync(home, { recursive: true, force: true }));
    const fake = fakeGithub();
    const setup = () => invoke(cwd, ['setup'], { packageRoot: fileURLToPath(new URL('..', import.meta.url)), env: { HOME: home, PATH: process.env.PATH }, stdin: { isTTY: true },
      pathDiagnostic: () => [], workflowAgents: { checkWorkflowAgents: async () => ({ ok: true, agent: 'codex', message: '' }) }, setupAgentMcp: async () => 0,
      autopilotPorts: { terminal: { mode: async () => ({ answer }), names: async () => ({ names: [] }) }, github: { lookup: async () => ({ owner: 'Ada', writers: [], complete: true }) } },
      autopilotGithubPorts: fake.ports });
    const first = await setup();
    assert.equal(first.exitCode, 0, first.stderr);
    assert.equal(JSON.parse(readFileSync(join(cwd, 'pdd.json'))).autopilot.mode, mode);
    assert.deepEqual(lines(first.stdout).filter(line => line.includes('pdd autopilot')), [hint(mode)]);
    const second = await setup();
    assert.equal(second.exitCode, 0, second.stderr);
    assert.equal(second.stdout.includes(hint(mode)), false, 'A saved mode prints no hint again');
    assert.deepEqual(fake.calls, [], 'setup never calls GitHub');
  }
});

// Wrong: the native gh port sends another request than the fake port shows, or misreads a refusal of gh.
test('autopilot-github: the public CLI uses gh api for the read, the write and the PR fallback', t => {
  const { cwd, git } = repo(t);
  const PULLS = 'GET repos/acme/widgets/pulls?state=open&base=main&per_page=100&page=1 ';
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

  const noPulls = { status: 200, body: [] };
  writeFileSync(routes, JSON.stringify({ 'GET repos/acme/widgets/contents/pdd.json?ref=main ': fileReply, [PULLS]: noPulls, 'PUT repos/acme/widgets/contents/pdd.json main': commit }));
  const direct = pdd('auto');
  assert.equal(direct.status, 0, direct.stderr);
  assert.deepEqual(lines(direct.stdout).slice(1), ['Updated pdd.json on GitHub (main): https://github.com/acme/widgets/commit/c1', PULL]);
  assert.ok(calls().some(call => call.args.includes(PULLS.slice(4, -1))), 'The open settings PRs are read through gh api');
  const put = calls().find(call => call.args.includes('PUT'));
  assert.deepEqual(put.args.slice(0, 3), ['api', '--method', 'PUT']);
  assert.ok(put.args.includes('repos/acme/widgets/contents/pdd.json') && put.args.at(-2) === '--input' && put.args.at(-1) === '-', put.args.join(' '));
  const body = JSON.parse(put.input);
  assert.equal(body.sha, 'blob-main'); assert.equal(body.branch, 'main');
  assert.deepEqual(decode(body.content), { keep: 1, autopilot: { mode: 'auto', trust: [] } });

  rmSync(log);
  writeFileSync(routes, JSON.stringify({
    'GET repos/acme/widgets/contents/pdd.json?ref=main ': fileReply,
    [PULLS]: noPulls,
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
