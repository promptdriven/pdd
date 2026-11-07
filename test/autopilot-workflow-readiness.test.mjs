import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync, existsSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { runAutopilotLauncher, tickAutopilot } from '../src/autopilot-launcher.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

// #3050: Autopilot checks that `pdd workflow run` can make an issue worktree before it
// starts a timer or offers new work. Real temporary Git repositories; fake gh, Herdr and timer.
const NOT_GIT = 'This folder is not a Git repository. cd into the repo you want Autopilot to work on, then run the command again.';
const packageRoot = resolve('.');
const capture = () => ({ text: '', write(s) { this.text += s; } });
const git = (cwd, ...args) => execFileSync('git', args, { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
const issue = number => ({ number, state: 'open', title: `Issue ${number}`, body: 'trusted body', user: { login: 'owner' }, author_association: 'OWNER', created_at: '2026-11-04T00:01:00Z', updated_at: '2026-11-04T00:01:00Z', comments: 0, labels: [], html_url: `https://github.com/owner/repo/issues/${number}` });

function repository(dir, name, origin, mode = 'auto') {
  const cwd = join(dir, name);
  mkdirSync(cwd);
  git(cwd, 'init', '-q', '-b', 'main');
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode, trust: [] } }));
  git(cwd, 'add', 'pdd.json');
  git(cwd, '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '-q', '-m', 'init');
  if (origin) git(cwd, 'remote', 'add', 'origin', origin);
  return realpathSync(cwd);
}

function fixture(t, origin = 'https://github.com/owner/repo.git') {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-autopilot-readiness-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'home'); mkdirSync(home);
  const cwd = repository(dir, 'repo', origin);
  const f = { dir, home, cwd, time: Date.parse('2026-11-04T00:00:00Z'), calls: [], timers: [], prompts: [], herdrCalls: [], issues: [], warnings: [] };
  f.ports = {
    stateRoot: join(home, 'state'), now: () => f.time, warn: text => f.warnings.push(text),
    readRunProgress: async () => [], pathDiagnostic: () => [],
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }),
    run: async (command, args, options = {}) => {
      f.calls.push([command, ...args]);
      if (command === 'git') {
        try { return { code: 0, stdout: execFileSync('git', args, { cwd: options.cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }), stderr: '' }; }
        catch (error) { return { code: error.status ?? 1, stdout: String(error.stdout ?? ''), stderr: String(error.stderr ?? '') }; }
      }
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"owner/repo","url":"https://github.com/owner/repo"}', stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      if (command === 'gh' && args[0] === 'api') {
        if (args.some(x => String(x).includes('/reviews?'))) return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n[]', stderr: '' };
        if (args.some(x => String(x).includes('/permission'))) return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n{"permission":"none"}', stderr: '' };
        return { code: 0, stdout: '{}', stderr: '' };
      }
      if (command === 'herdr') return { code: 0, stdout: '1.0', stderr: '' };
      throw Error(`unexpected process ${command} ${args}`);
    },
    timer: async (action, state) => { f.timers.push([action, state.cwd]); return action === 'start' || action === 'status' && f.timers.some(([a, c]) => a === 'start' && c === state.cwd); },
    queryIssues: async () => ({ status: 200, etag: '"one"', issues: structuredClone(f.issues) }),
    comments: async () => [],
    reconcileDependencyIntake: async () => ({ eligible: f.issues.map(row => row.html_url), queued: [], skipped: [] }),
    herdr: async args => {
      f.herdrCalls.push(args);
      if (args[0] === 'status') return { running: true };
      const live = { pane_id: 'p1', workspace_id: 'w1', cwd: f.cwd, foreground_cwd: f.cwd, tab_id: 't1', terminal_id: 'term1', agent: 'codex', agent_status: 'idle', agent_session: 'session' };
      if (args[0] === 'workspace') return { result: { type: 'workspace_info', workspace: { workspace_id: 'w1' }, root_pane: { pane_id: 'p1' } } };
      if (args[0] === 'pane' && args[1] === 'get') return { result: { type: 'pane_info', pane: live } };
      if (args[0] === 'agent' && args[1] === 'get') {
        if (!f.agentStarted) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' });
        return { result: { type: 'agent_info', agent: live } };
      }
      if (args[0] === 'pane' && args[1] === 'run') { f.agentStarted = true; return {}; }
      if (args[0] === 'pane' && args[1] === 'read') return '';
      if (args[0] === 'agent' && args[1] === 'prompt') {
        const instruction = args.at(-1), match = /Artifact path: (.+)/.exec(instruction);
        f.prompts.push(match ? readFileSync(JSON.parse(match[1]), 'utf8') : instruction);
      }
      return {};
    },
  };
  f.invoke = (command, extra = {}) => runAutopilotLauncher({ command, cwd: f.cwd, env: { HOME: home, PATH: process.env.PATH }, packageRoot, issues: [], ...extra }, f.ports);
  f.stateFile = () => join(f.ports.stateRoot, `${createHash('sha256').update(f.cwd).digest('hex').slice(0, 20)}.json`);
  f.state = () => existsSync(f.stateFile()) ? JSON.parse(readFileSync(f.stateFile(), 'utf8')) : null;
  f.tick = () => tickAutopilot(f.stateFile(), f.ports);
  f.commonDir = () => realpathSync(git(f.cwd, 'rev-parse', '--path-format=absolute', '--git-common-dir').trim());
  // The allocator keeps its records in the common Git folder and makes worktrees beside the checkout.
  f.allocated = () => existsSync(join(f.commonDir(), 'pdd', 'worktree-assignments')) || existsSync(`${f.cwd}.pdd-worktrees`)
    || git(f.cwd, 'worktree', 'list', '--porcelain').split('\n').filter(row => row.startsWith('worktree ')).length !== 1;
  return f;
}

test('start refuses a checkout whose origin names another repository, before any timer, chat or claim', async t => {
  const f = fixture(t, 'https://github.com/other/thing.git');
  // Another checkout on this machine already runs Autopilot; its state and timer must stay as they are.
  mkdirSync(f.ports.stateRoot, { recursive: true });
  const other = join(f.ports.stateRoot, `${'a'.repeat(20)}.json`), otherText = JSON.stringify({ repo: 'owner/elsewhere', cwd: join(f.dir, 'elsewhere'), enabled: true, timerInstalled: true });
  writeFileSync(other, otherText);

  const result = await f.invoke('start');

  assert.equal(result.exitCode, 1, result.message);
  assert.match(result.message, /^Autopilot did not start: pdd workflows cannot start in /);
  assert.ok(result.message.includes(f.cwd), 'the message names the folder');
  assert.ok(result.message.includes('Its origin remote names other/thing, not owner/repo.'), result.message);
  assert.ok(result.message.includes('Run Autopilot from a normal clone of owner/repo.'), result.message);
  assert.doesNotMatch(result.message, /github\.com/, 'the origin URL is not printed');
  assert.deepEqual(f.timers, [], 'no timer was started, stopped or changed');
  assert.deepEqual(f.herdrCalls, [], 'no Herdr workspace or chat was opened');
  assert.ok(!f.calls.some(([command, sub]) => command === 'gh' && sub === 'api'), 'no GitHub claim, label or comment');
  assert.equal(f.state()?.enabled ?? false, false, 'Autopilot is not enabled for this checkout');
  assert.equal(f.allocated(), false, 'no allocation record or worktree');
  assert.equal(readFileSync(other, 'utf8'), otherText, "another checkout's Autopilot is unchanged");
});

test('start in a normal clone of the repository starts as before and names the repository and folder', async t => {
  const f = fixture(t);

  const result = await f.invoke('start');

  assert.equal(result.exitCode, 0, result.message);
  assert.ok(result.message.startsWith(`Autopilot started for owner/repo in ${f.cwd}.`), result.message);
  assert.deepEqual(f.timers.filter(([action]) => action === 'start'), [['start', f.cwd]]);
  assert.equal(f.state().enabled, true);
  assert.equal(f.state().cwd, f.cwd);
  assert.equal(f.allocated(), false, 'the check is read-only: no allocation record or worktree');
});

test('a tick holds new issue work while workflows cannot start, then offers it when they can', async t => {
  const f = fixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  const delivered = f.prompts.length;
  f.issues = [issue(7)];
  git(f.cwd, 'remote', 'set-url', 'origin', 'https://github.com/other/thing.git');
  f.time += 30 * 60 * 1000;

  await f.tick();

  assert.equal(f.prompts.length, delivered, 'no packet offers the issue');
  assert.ok(f.warnings.some(text => text.includes('Autopilot held 1 issue(s): pdd workflows cannot start in') && text.includes(f.cwd) && text.includes('Its origin remote names other/thing, not owner/repo.')), f.warnings.join('\n'));
  assert.equal(f.allocated(), false);

  git(f.cwd, 'remote', 'set-url', 'origin', 'https://github.com/owner/repo.git');
  f.time += 30 * 60 * 1000;
  await f.tick();

  assert.equal(f.prompts.length, delivered + 1, 'the held issue is offered once workflows can start');
  assert.match(f.prompts.at(-1), /"number":7/);
});

test('status names the folder and says why workflows cannot start there, without GitHub', async t => {
  const f = fixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);

  const ready = await f.invoke('status');
  assert.equal(ready.exitCode, 0, ready.message);
  assert.ok(ready.message.split('\n')[0].includes(`owner/repo in ${f.cwd}`), ready.message);
  assert.doesNotMatch(ready.message, /Workflows cannot start/);

  git(f.cwd, 'remote', 'set-url', 'origin', 'https://github.com/other/thing.git');
  f.calls.length = 0;
  const other = await f.invoke('status');
  assert.equal(other.exitCode, 0, other.message);
  assert.equal(other.message.split('\n')[1], 'Workflows cannot start in this folder: Its origin remote names other/thing, not owner/repo. Run Autopilot from a normal clone of owner/repo.');

  git(f.cwd, 'remote', 'set-url', 'origin', join(f.dir, 'somewhere-local.git'));
  const local = await f.invoke('status');
  assert.equal(local.message.split('\n')[1], 'Workflows cannot start in this folder: Its origin remote is not a GitHub repository address. Run Autopilot from a normal clone of owner/repo.');
  assert.ok(!f.calls.some(([command]) => command === 'gh'), 'status makes no GitHub call');
});

test('outside a Git repository every Autopilot command that needs a repo says so and exits 1', async t => {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-autopilot-nogit-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'home'), cwd = join(dir, 'folder'); mkdirSync(home); mkdirSync(cwd);
  for (const argv of [['start'], ['stop'], ['status'], ['add', '5'], ['off'], ['observe'], ['auto'], ['trust', 'someone'], ['untrust', 'someone']]) {
    const stdout = capture(), stderr = capture();
    const exitCode = await runPdd(['autopilot', ...argv], { cwd, env: { HOME: home, PATH: process.env.PATH }, stdout, stderr,
      autopilotLauncherPorts: { stateRoot: join(home, 'state') }, autopilotGithub: { checkAutopilotSettings: async () => { throw Error('no GitHub'); }, publishAutopilotSettings: async () => { throw Error('no GitHub'); } } });
    assert.equal(exitCode, 1, `${argv[0]}: ${stderr.text}`);
    assert.equal(stderr.text, `${NOT_GIT}\n`, argv[0]);
    assert.equal(stdout.text, '', argv[0]);
  }
  assert.equal(existsSync(join(home, 'state')) && readdirSync(join(home, 'state')).length > 0, false, 'nothing is saved');
});

test('status --all lists every repository with Autopilot on this machine from any folder, read-only and without GitHub', async t => {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-autopilot-all-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'home'), outside = join(dir, 'not-a-repo'), stateRoot = join(home, 'state');
  mkdirSync(home); mkdirSync(outside); mkdirSync(stateRoot);
  const one = repository(dir, 'one', 'https://github.com/owner/one.git', 'auto');
  const two = repository(dir, 'two', 'https://github.com/owner/two.git', 'observe');
  const id = cwd => createHash('sha256').update(cwd).digest('hex').slice(0, 20);
  const files = {
    [join(stateRoot, `${id(one)}.json`)]: JSON.stringify({ repo: 'owner/one', cwd: one, id: id(one), enabled: true, paneId: 'p1', workspaceId: 'w1', agent: { id: 'codex', kind: 'codex' }, environment: { HOME: home } }),
    [join(stateRoot, `${id(two)}.json`)]: JSON.stringify({ repo: 'owner/two', cwd: two, id: id(two), enabled: false, environment: { HOME: home } }),
  };
  for (const [file, text] of Object.entries(files)) writeFileSync(file, text);
  const calls = [];
  const ports = {
    stateRoot,
    timer: async (action, state) => { calls.push(['timer', action]); return action === 'status' && state.id === id(one); },
    herdr: async args => {
      calls.push(['herdr', ...args]);
      if (args[0] === 'status') return { running: true };
      if (args[0] === 'agent' && args[1] === 'get' && args[2] === 'p1') return { result: { type: 'agent_info', agent: { pane_id: 'p1', workspace_id: 'w1', cwd: one, agent: 'codex', agent_status: 'idle' } } };
      throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' });
    },
    run: async (command, args, options = {}) => {
      calls.push([command, ...args]);
      assert.equal(command, 'git', 'only local Git reads');
      try { return { code: 0, stdout: execFileSync('git', args, { cwd: options.cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }), stderr: '' }; }
      catch (error) { return { code: error.status ?? 1, stdout: String(error.stdout ?? ''), stderr: String(error.stderr ?? '') }; }
    },
  };
  const stdout = capture(), stderr = capture();
  const exitCode = await runPdd(['autopilot', 'status', '--all'], { cwd: outside, env: { HOME: home, PATH: process.env.PATH }, stdout, stderr, autopilotLauncherPorts: ports,
    autopilotGithub: { checkAutopilotSettings: async () => { calls.push(['github']); return 'GitHub was read'; } } });

  assert.equal(exitCode, 0, stderr.text);
  assert.equal(stderr.text, '');
  const lines = stdout.text.trimEnd().split('\n');
  assert.equal(lines[0], 'Autopilot on this machine (2):');
  const row = repo => lines.find(text => text.startsWith(`${repo} in `));
  assert.equal(row('owner/one'), `owner/one in ${one} · mode auto · Autopilot enabled · timer active · coordinator idle`);
  assert.equal(row('owner/two'), `owner/two in ${two} · mode observe · Autopilot disabled · timer inactive · coordinator unavailable (not recorded)`);
  assert.equal(lines.length, 3);
  assert.ok(!calls.some(([kind]) => ['gh', 'github'].includes(kind)), 'no GitHub call');
  assert.ok(!calls.some(([kind, action]) => kind === 'timer' && action !== 'status'), 'timers are only read');
  for (const [file, text] of Object.entries(files)) assert.equal(readFileSync(file, 'utf8'), text, 'saved state is unchanged');

  const empty = capture();
  assert.equal(await runPdd(['autopilot', 'status', '--all'], { cwd: outside, env: { HOME: join(dir, 'nobody'), PATH: process.env.PATH }, stdout: empty, stderr: capture(), autopilotLauncherPorts: { ...ports, stateRoot: join(dir, 'nobody', 'state') } }), 0);
  assert.equal(empty.text, 'No Autopilot on this machine.\n');
  assert.equal(dirname(outside), dir);
});
