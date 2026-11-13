import './helpers/test-home.mjs';
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
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"owner/repo","defaultBranchRef":{"name":"main"},"url":"https://github.com/owner/repo"}', stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      if (command === 'gh' && args[0] === 'api') {
        const endpoint = args.find(word => /^repos\//.test(word)), subject = /^repos\/owner\/repo\/issues\/(\d+)$/.exec(endpoint ?? '');
        if (subject) { const row = f.issues.find(row => row.number === Number(subject[1])); return {code:row ? 0 : 1, stdout:`HTTP/2.0 ${row ? 200 : 404}\r\n\r\n${JSON.stringify(row ?? {})}`}; }
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
      // #3123 admission reads complete native pane inventory before allocation.
      if (args[0] === 'pane' && args[1] === 'list') return {result: {type: 'pane_list', panes: [live]}};
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

