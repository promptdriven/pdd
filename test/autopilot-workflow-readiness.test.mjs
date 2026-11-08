import { isolatedCheckCapacity } from './helpers/check-machine.mjs';
import { healthyMachine } from './helpers/healthy-machine.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync, existsSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { runAutopilotLauncher, tickAutopilot, withAutopilotModeLock } from '../src/autopilot-launcher.mjs';
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

// `git clone --separate-git-dir`: Git registers the Git directory itself as the primary worktree and finds no
// work tree there, so the allocator cannot find the primary checkout and refuses. This stays refused after #2698.
function separateGitDir(cwd) {
  git(cwd, 'init', '-q', '--separate-git-dir', `${cwd}-git`);
  return cwd;
}

function fixture(t, origin = 'https://github.com/owner/repo.git', layout = 'normal') {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-autopilot-readiness-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'home'); mkdirSync(home);
  const cwd = repository(dir, 'repo', origin);
  if (layout === 'separate-git-dir') separateGitDir(cwd);
  const f = { dir, home, cwd, time: Date.parse('2026-11-04T00:00:00Z'), calls: [], timers: [], prompts: [], herdrCalls: [], issues: [], warnings: [] };
  f.ports = {
    ...healthyMachine, checkCapacityPorts: isolatedCheckCapacity(dir), stateRoot: join(home, 'state'), now: () => f.time, warn: text => f.warnings.push(text),
    readRunProgress: async () => [], pathDiagnostic: () => [],
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }),
    run: async (command, args, options = {}) => {
      f.calls.push([command, ...args]);
      if (command === 'git') {
        if (f.gitTimesOut?.(args)) throw Error('timeout');
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
    comments: async number => structuredClone(f.comments?.[number] ?? []),
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

test('start refuses a checkout whose Git layout the allocator cannot verify, before any timer, chat or claim', async t => {
  // The origin names the right repository, so only the allocator's own layout check can refuse here.
  const f = fixture(t, 'https://github.com/owner/repo.git', 'separate-git-dir');

  const result = await f.invoke('start');

  assert.equal(result.exitCode, 1, result.message);
  assert.equal(result.message, `Autopilot did not start: pdd workflows cannot start in ${f.cwd}. pdd cannot verify the Git layout of this checkout, so it cannot make issue worktrees here. Run Autopilot from a normal clone of owner/repo. Nothing was started or claimed, and every timer is unchanged.`);
  assert.ok(f.calls.some(call => call.join(' ') === 'git worktree list --porcelain -z'), 'the allocator read the Git registration');
  assert.deepEqual(f.timers, [], 'no timer was started, stopped or changed');
  assert.deepEqual(f.herdrCalls, [], 'no Herdr workspace or chat was opened');
  assert.ok(!f.calls.some(([command, sub]) => command === 'gh' && sub === 'api'), 'no GitHub claim, label or comment');
  assert.equal(f.state()?.enabled ?? false, false, 'Autopilot is not enabled for this checkout');
  assert.equal(f.allocated(), false, 'no allocation record or worktree');
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

test('a tick holds new issue work in a checkout whose Git layout the allocator cannot verify', async t => {
  // Autopilot already runs here, for example since before this check existed. Then the checkout gets a separate Git directory.
  const f = fixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  const delivered = f.prompts.length;
  separateGitDir(f.cwd);
  f.issues = [issue(7)];
  f.calls.length = 0;
  f.time += 30 * 60 * 1000;

  await f.tick();

  assert.equal(f.prompts.length, delivered, 'no packet offers the issue');
  assert.ok(f.calls.some(call => call.join(' ') === 'git worktree list --porcelain -z'), 'the allocator read the Git registration');
  assert.deepEqual(f.warnings, [`Autopilot held 1 issue(s): pdd workflows cannot start in ${f.cwd}. pdd cannot verify the Git layout of this checkout, so it cannot make issue worktrees here. Run Autopilot from a normal clone of owner/repo.`]);
  assert.equal(f.allocated(), false, 'no allocation record or worktree');
  assert.ok(!f.calls.some(([command, ...args]) => command === 'gh' && args.includes('--method')), 'no claim, label or comment');
});

test('while workflows cannot start, a tick still delivers a trusted comment on a held issue and holds only new work', async t => {
  const f = fixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  // Issue 8 waits for its code PR (pdd:code-pending). The first tick only records it.
  f.issues = [{ ...issue(8), labels: [{ name: 'pdd:code-pending' }] }];
  f.time += 30 * 60 * 1000;
  await f.tick();
  const delivered = f.prompts.length;

  git(f.cwd, 'remote', 'set-url', 'origin', 'https://github.com/other/thing.git');
  f.comments = { 8: [{ id: 81, user: { login: 'owner' }, author_association: 'OWNER', body: 'The code PR can merge now.', created_at: '2026-11-04T02:00:00Z', updated_at: '2026-11-04T02:00:00Z' }] };
  f.issues = [{ ...issue(8), labels: [{ name: 'pdd:code-pending' }], comments: 1, updated_at: '2026-11-04T02:00:00Z' }, issue(7)];
  f.time += 30 * 60 * 1000;
  await f.tick();

  assert.equal(f.prompts.length, delivered + 1, 'one packet goes out');
  assert.match(f.prompts.at(-1), /The code PR can merge now\./, 'the trusted comment on the held issue is delivered');
  assert.doesNotMatch(f.prompts.at(-1), /"number":7/, 'the new issue is held');
  assert.ok(f.warnings.some(text => text.startsWith('Autopilot held 1 issue(s): pdd workflows cannot start in')), f.warnings.join('\n'));
});

test('while workflows cannot start, an own live claim still gets its heartbeat and its new trusted comment, and only new claim or start work is held', async t => {
  const f = fixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  const { coordinatorId, machine } = f.state();
  const heartbeats = [];
  f.ports.refreshClaimHeartbeat = async input => { heartbeats.push(input.claim.issue); };
  // Issue 9 has this coordinator's live claim. Issue 10 has an expired claim: a takeover is new claim work.
  const working = { ...issue(9), labels: [{ name: 'pdd:working' }] }, expired = { ...issue(10), labels: [{ name: 'pdd:working' }] };
  f.ports.reconcileDependencyIntake = async () => ({ eligible: f.issues.map(row => row.html_url), queued: [], skipped: [], claims: [
    { issue: working.html_url, active: true, expired: false, coordinatorId, machine, commentId: 'c9', labelEventId: 'l9' },
    { issue: expired.html_url, active: false, expired: true, lastSeen: '2026-11-01T00:00:00Z' }] });
  f.issues = [working, expired];
  f.time += 30 * 60 * 1000;
  await f.tick();
  const delivered = f.prompts.length;

  git(f.cwd, 'remote', 'set-url', 'origin', 'https://github.com/other/thing.git');
  const comment = (id, body) => ({ id, user: { login: 'owner' }, author_association: 'OWNER', body, created_at: '2026-11-04T00:45:00Z', updated_at: '2026-11-04T00:45:00Z' });
  f.comments = { 9: [comment(91, 'Please address the review.')], 10: [comment(101, 'Take this over.')] };
  f.issues = [{ ...working, comments: 1, updated_at: '2026-11-04T00:45:00Z' }, { ...expired, comments: 1, updated_at: '2026-11-04T00:45:00Z' }, issue(7)];
  heartbeats.length = 0; f.warnings.length = 0;
  f.time += 30 * 60 * 1000;
  await f.tick();

  assert.deepEqual(heartbeats, [working.html_url], 'the own live claim gets its heartbeat');
  assert.equal(f.prompts.length, delivered + 1, 'one packet goes out');
  assert.match(f.prompts.at(-1), /"number":9/);
  assert.match(f.prompts.at(-1), /Please address the review\./, 'the new trusted comment on the live claim is delivered');
  assert.doesNotMatch(f.prompts.at(-1), /"number":10|Take this over\./, 'the expired claim is held');
  assert.doesNotMatch(f.prompts.at(-1), /"number":7/, 'the new issue is held');
  assert.deepEqual(f.warnings, [`Autopilot held 2 issue(s): pdd workflows cannot start in ${f.cwd}. Its origin remote names other/thing, not owner/repo. Run Autopilot from a normal clone of owner/repo.`]);
  assert.equal(f.allocated(), false);
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

test('status accepts every origin form that the allocator accepts, and names a Git read failure as one', async t => {
  const f = fixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  for (const origin of ['https://GitHub.com/owner/repo.git', 'https://github.com:443/owner/repo.git', 'https://github.com/Owner/Repo', 'ssh://git@github.com/owner/repo.git', 'git@github.com:owner/repo.git']) {
    git(f.cwd, 'remote', 'set-url', 'origin', origin);
    const status = await f.invoke('status');
    assert.equal(status.exitCode, 0, status.message);
    assert.doesNotMatch(status.message, /Workflows cannot start/, origin);
  }

  f.gitTimesOut = args => args[0] === 'remote';
  const slow = await f.invoke('status');
  assert.equal(slow.message.split('\n')[1], 'Workflows cannot start in this folder: pdd could not read Git in this checkout. Try again.');
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

// Git translates its messages. These commands give the same answer when Git prints German.
const AUTOPILOT_COMMANDS = [['start'], ['stop'], ['status'], ['add', '5'], ['off'], ['observe'], ['auto'], ['trust', 'someone'], ['untrust', 'someone']];
const GERMAN = { LANG: 'de_DE.UTF-8', LC_ALL: 'de_DE.UTF-8' };

test('outside a Git repository the message is the same when real Git prints German', async t => {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-autopilot-nogit-de-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'home'), cwd = join(dir, 'folder'); mkdirSync(home); mkdirSync(cwd);
  const env = { HOME: home, PATH: process.env.PATH, ...GERMAN };
  const probe = spawnSync('git', ['rev-parse', '--show-toplevel'], { cwd, env, encoding: 'utf8' });
  if (probe.status === 0 || /not a git repository/i.test(probe.stderr)) {
    t.skip(probe.status === 0 ? 'the temporary folder is inside a Git repository' : 'Git prints no German messages here (no de_DE.UTF-8 locale or no Git translations)');
    return;
  }
  for (const argv of AUTOPILOT_COMMANDS) {
    const run = spawnSync(process.execPath, [join(packageRoot, 'bin', 'pdd.mjs'), 'autopilot', ...argv], { cwd, env, encoding: 'utf8' });
    assert.equal(run.status, 1, `${argv[0]}: ${run.stderr}`);
    assert.equal(run.stderr, `${NOT_GIT}\n`, argv[0]);
    assert.equal(run.stdout, '', argv[0]);
  }
  assert.equal(existsSync(join(home, '.local')), false, 'nothing is saved');
});

test('outside a Git repository the message is the same when Git prints another language', async t => {
  // Git on a machine with a German locale: it prints English only when the call itself sets the C locale.
  const message = env => {
    const locale = env.LC_ALL || env.LC_MESSAGES || env.LANG || '';
    return ['C', 'POSIX'].includes(locale) ? 'fatal: not a git repository (or any of the parent directories): .git\n'
      : 'Schwerwiegend: Kein Git-Repository (oder irgendeines der Elternverzeichnisse): .git\n';
  };
  const machine = { ...process.env, ...GERMAN }, calls = [];
  const notGit = (command, args) => { calls.push([command, ...args].join(' ')); assert.equal(command, 'git'); };
  const run = async (command, args, options = {}) => { notGit(command, args); return { code: 128, stdout: '', stderr: message(options.env ?? machine) }; };
  const execFile = async (command, args, options = {}) => { notGit(command, args); throw Object.assign(Error('Command failed'), { code: 128, stdout: '', stderr: message(options.env ?? machine) }); };
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-autopilot-nogit-fake-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'home'), cwd = join(dir, 'folder'), stateRoot = join(home, 'state'); mkdirSync(home); mkdirSync(cwd);
  const env = { HOME: home, PATH: process.env.PATH, ...GERMAN };
  for (const argv of AUTOPILOT_COMMANDS) {
    const stdout = capture(), stderr = capture();
    const exitCode = await runPdd(['autopilot', ...argv], { cwd, env, stdout, stderr, autopilotLauncherPorts: { stateRoot, run }, autopilotPorts: { execFile },
      autopilotGithub: { checkAutopilotSettings: async () => { throw Error('no GitHub'); }, publishAutopilotSettings: async () => { throw Error('no GitHub'); } } });
    assert.equal(exitCode, 1, `${argv[0]}: ${stderr.text}`);
    assert.equal(stderr.text, `${NOT_GIT}\n`, argv[0]);
    assert.equal(stdout.text, '', argv[0]);
  }
  // The settings write boundary hands a folder outside Git to the settings action, which then says so.
  const locked = await withAutopilotModeLock({ cwd, env }, async () => ({ exitCode: 1, message: NOT_GIT }), { stateRoot, execFile });
  assert.equal(locked.message, NOT_GIT);
  assert.deepEqual([...new Set(calls)], ['git rev-parse --show-toplevel'], 'only the Git root lookup runs');
  assert.equal(existsSync(stateRoot), false, 'nothing is saved');
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
  const row = repo => lines.find(text => text.startsWith(`${repo} in `)).split(' · Health:')[0];
  assert.equal(lines.slice(1).every(line => /Health:.*unknown/.test(line)), true);
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

test('status --all keeps each line independent when a saved folder is gone or a state file is broken', async t => {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-autopilot-all-gone-')));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'home'), outside = join(dir, 'not-a-repo'), stateRoot = join(home, 'state');
  mkdirSync(home); mkdirSync(outside); mkdirSync(stateRoot);
  const one = repository(dir, 'one', 'https://github.com/owner/one.git', 'auto');
  const two = repository(dir, 'two', 'https://github.com/owner/two.git', 'observe');
  const gone = join(dir, 'gone'), id = cwd => createHash('sha256').update(cwd).digest('hex').slice(0, 20);
  const goneId = '0'.repeat(20); // Sorts first, so a failure there would reach every later line.
  const files = {
    [join(stateRoot, `${goneId}.json`)]: JSON.stringify({ repo: 'owner/gone', cwd: gone, enabled: true, timerInstalled: true, paneId: 'p0', workspaceId: 'w0', agent: { id: 'codex', kind: 'codex' } }),
    [join(stateRoot, `${'1'.repeat(20)}.json`)]: JSON.stringify({ repo: 'owner/plain', cwd: outside, enabled: false }),
    [join(stateRoot, `${id(one)}.json`)]: JSON.stringify({ repo: 'owner/one', cwd: one, enabled: true, paneId: 'p1', workspaceId: 'w1', agent: { id: 'codex', kind: 'codex' } }),
    [join(stateRoot, `${id(two)}.json`)]: JSON.stringify({ repo: 'owner/two', cwd: two, enabled: false }),
    [join(stateRoot, `${'e'.repeat(20)}.json`)]: '[]',
    [join(stateRoot, `${'f'.repeat(20)}.json`)]: 'null',
  };
  for (const [file, text] of Object.entries(files)) writeFileSync(file, text);
  // The timer of the deleted folder is still installed.
  const active = new Set([goneId, id(one)].map(name => `gui/501/pdd-autopilot-${name}`));
  const calls = [];
  const ports = {
    stateRoot, platform: 'darwin', uid: 501,
    run: async (command, args, options = {}) => {
      calls.push({ command, args, cwd: options.cwd });
      // Like a real spawn: a missing working folder fails before the program runs.
      if (!existsSync(options.cwd)) throw Object.assign(Error(`spawn ${command} ENOENT`), { code: 'ENOENT' });
      if (command === 'git') {
        try { return { code: 0, stdout: execFileSync('git', args, { cwd: options.cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }), stderr: '' }; }
        catch (error) { return { code: error.status ?? 1, stdout: String(error.stdout ?? ''), stderr: String(error.stderr ?? '') }; }
      }
      if (command === 'launchctl') return { code: args[0] === 'print' && active.has(args[1]) ? 0 : 113, stdout: '', stderr: '' };
      if (command === 'herdr') {
        const [, , kind, action, pane] = args;
        if (kind === 'status') return { code: 0, stdout: '{"running":true}', stderr: '' };
        if (kind === 'agent' && action === 'get' && pane === 'p1') return { code: 0, stdout: JSON.stringify({ result: { type: 'agent_info', agent: { pane_id: 'p1', workspace_id: 'w1', cwd: one, agent: 'codex', agent_status: 'idle' } } }), stderr: '' };
        return { code: 1, stdout: '', stderr: '{"error":{"code":"agent_not_found","message":"agent not found"}}' };
      }
      throw Error(`unexpected process ${command} ${args}`);
    },
  };
  const stdout = capture(), stderr = capture();
  const exitCode = await runPdd(['autopilot', 'status', '--all'], { cwd: outside, env: { HOME: home, PATH: process.env.PATH }, stdout, stderr, autopilotLauncherPorts: ports,
    autopilotGithub: { checkAutopilotSettings: async () => { throw Error('no GitHub'); } } });

  assert.equal(exitCode, 0, stderr.text);
  // Lines follow the order of the state file names; the ids of one and two depend on the temporary folder.
  const expected = {
    [goneId]: `owner/gone in ${gone} · mode unknown (folder missing) · Autopilot enabled · timer active · coordinator unavailable (missing)`,
    ['1'.repeat(20)]: `owner/plain in ${outside} · mode unknown (not a Git repository) · Autopilot disabled · timer inactive · coordinator unavailable (not recorded)`,
    [id(one)]: `owner/one in ${one} · mode auto · Autopilot enabled · timer active · coordinator idle`,
    [id(two)]: `owner/two in ${two} · mode observe · Autopilot disabled · timer inactive · coordinator unavailable (not recorded)`,
    ['e'.repeat(20)]: `${'e'.repeat(20)}.json: saved state unreadable`,
    ['f'.repeat(20)]: `${'f'.repeat(20)}.json: saved state unreadable`,
  };
  const lines = stdout.text.trimEnd().split('\n').map(line => line.split(' · Health:')[0]);
  assert.equal(lines[0], 'Autopilot on this machine (6):');
  assert.equal(lines[1], expected[goneId], 'the missing folder sorts first');
  assert.deepEqual(lines.slice(1), Object.keys(expected).sort().map(name => expected[name]));
  assert.ok(!calls.some(call => call.cwd === gone), 'no process runs in the missing folder');
  assert.ok(!calls.some(({ command, args }) => command === 'gh' || command === 'launchctl' && args[0] !== 'print'), 'no GitHub call and timers are only read');
  for (const [file, text] of Object.entries(files)) assert.equal(readFileSync(file, 'utf8'), text, 'saved state is unchanged');
});
