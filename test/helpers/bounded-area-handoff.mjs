// Public-boundary fixture for the approved bounded-area-handoff cases.
// All Git repositories and run state are temporary; gh and Herdr never run.
import assert from 'node:assert/strict';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { fakeHerdr } from './fake-herdr.mjs';
import { startRun, stepDone, approveRun, openRun } from '../../src/workflow-runner.mjs';

const exec = promisify(callbackExec);
export const packageRoot = resolve(import.meta.dirname, '../..');
export async function handoffFixture(t, { steps = ['scope'], optional = [], strict = false, buildApproval = false } = {}) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-handoff-')));
  t.after(() => rmSync(base, { recursive: true, force: true }));
  const source = join(base, 'project "界'), state = join(base, 'state'), home = join(base, 'home');
  for (const path of [source, state, home, join(home, '.claude')]) mkdirSync(path);
  const git = (...args) => execFileSync('git', args, { cwd: source, encoding: 'utf8' }).trim();
  git('init', '-q', '-b', 'main'); git('config', 'user.email', 'test@example.invalid'); git('config', 'user.name', 'Handoff fixture');
  git('remote', 'add', 'origin', 'https://github.com/example/project.git');
  const skill = join(source, '.agents/skills/pdd-handoff'); mkdirSync(skill, { recursive: true });
  writeFileSync(join(skill, 'SKILL.md'), '# Isolated handoff workflow\n');
  writeFileSync(join(skill, 'workflow.json'), JSON.stringify({ version: 2, areas: [
    { name: 'plan', steps, optional, gate: 'approve' },
    { name: 'build', steps: ['current', 'finish'], gate: buildApproval ? 'approve' : 'pr' },
    ...(buildApproval ? [{ name: 'release', steps: ['publish'], gate: 'pr' }] : []),
  ] }));
  if (strict) writeFileSync(join(source, 'pdd.json'), JSON.stringify({ strict_approvals: true }));
  writeFileSync(join(source, 'value.mjs'), 'export const value = 1;\n');
  git('add', '.'); git('commit', '-qm', 'isolated fixture');
  git('update-ref', 'refs/remotes/origin/main', git('rev-parse', 'HEAD'));
  const f = { source, base, herdr: fakeHerdr(), calls: [], prs: [], confirmations: [], clock: Date.parse('2026-11-12T00:00:00Z') };
  f.herdr.now = () => f.clock;
  const execFile = async (file, args, options = {}) => {
    f.calls.push({ file, args });
    if (file === 'git' && args[0] === 'push') {
      const [from, to] = args[2].split(':');
      const sha = (await exec('git', ['rev-parse', from], { cwd: options.cwd })).stdout.trim();
      await exec('git', ['update-ref', to.replace('refs/heads/', 'refs/remotes/origin/'), sha], { cwd: options.cwd });
      return { stdout: '' };
    }
    if (file === 'git' && args[0] === 'ls-remote') return { stdout: '' };
    if (file === 'git' && args[0] === 'fetch') return { stdout: '' };
    if (file === 'gh' && args[0] === 'repo' && args[1] === 'view') return { stdout: JSON.stringify({ nameWithOwner: 'example/project', defaultBranchRef: { name: 'main' }, url: 'https://github.com/example/project' }) };
    if (file === 'gh' && args[0] === 'api' && args[1] === 'repos/example/project/issues/17') return { stdout: JSON.stringify({ number: 17, html_url: 'https://github.com/example/project/issues/17', title: 'Bound earlier handoffs', body: 'Isolated native handoff fixture.' }) };
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'list') return { stdout: JSON.stringify(f.prs) };
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'create') {
      const value = flag => args[args.indexOf(flag) + 1];
      f.prs.push({ number: 23, body: options.input, url: 'https://github.com/example/project/pull/23', state: 'OPEN',
        headRefName: value('--head'), baseRefName: value('--base'), title: value('--title'),
        headRefOid: (await exec('git', ['rev-parse', 'HEAD'], { cwd: options.cwd })).stdout.trim(),
        headRepository: { name: 'project' }, headRepositoryOwner: { login: 'example' }, isCrossRepository: false, mergeCommit: null });
      return { stdout: f.prs.at(-1).url };
    }
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'view') return { stdout: JSON.stringify({ state: 'OPEN', body: f.prs.at(-1)?.body, statusCheckRollup: [] }) };
    assert.equal(file, 'git', 'only local git runs; all external services are injected');
    assert.ok(!['push', 'clone', 'pull', 'ls-remote'].includes(args[0]), 'no external git operation');
    return exec(file, args, { ...options, encoding: 'utf8' });
  };
  f.ports = { skipMetricsDelivery: true, execFile, herdr: f.herdr.herdr, stateDir: state, queueRoot: join(base, 'suite-queue'), layoutDirectory: join(state, 'herdr-layout'),
    now: () => f.clock, sleep: async ms => { f.clock += ms; }, findNativeSessions: stage => f.herdr.findNativeSessions(stage),
    env: { HOME: home, XDG_CONFIG_HOME: join(home, '.config'), CLAUDE_CONFIG_DIR: join(home, '.claude') },
    isTTY: true, pdd: '/abs/node /abs/pdd.mjs', attach: async () => 0,
    confirm: async text => { f.confirmations.push(text); return true; },
    readApprovalEvidence: async () => assert.fail('No native approval history is needed'),
  };
  const statusPath = join(git('rev-parse', '--path-format=absolute', '--git-common-dir'), 'pdd/runs/17/status.json');
  // Seed absent earlier completions in a controlled ledger while retaining the real displayed gate.
  f.removeDone = step => { const run = f.record(); delete run.done[step]; writeFileSync(statusPath, JSON.stringify(run)); };
  // Historical PR custody is an input to the persistence vector, not a new publication.
  f.seedPriorPr = () => { const run = f.record(); run.pr = [{ number: 23, url: 'https://github.com/example/project/pull/23', stage: 'plan', branch: run.branch, base: 'main', state: 'open' }]; writeFileSync(statusPath, JSON.stringify(run)); };
  f.record = () => JSON.parse(readFileSync(statusPath, 'utf8'));
  f.brief = () => {
    const chat = f.record().chats.at(-1), pane = f.herdr.paneOf(chat);
    assert.ok(pane.commands.some(command => command.includes(chat.messageFile)), 'the recorded message file is delivered as the native start input');
    return readFileSync(chat.messageFile, 'utf8');
  };
  f.start = async () => { const out = await startRun({ name: 'handoff', issue: '17', agent: 'claude', cwd: source, packageRoot }, f.ports); assert.equal(out.exitCode, 0, out.message); return f.record(); };
  f.done = async (step, summary) => { f.clock += 1000; const out = await stepDone({ step, summary, cwd: f.record().root, packageRoot }, { ...f.ports, isTTY: false, env: { ...f.ports.env, PDD_AGENT_SESSION: '1' } }); assert.equal(out.exitCode, 0, out.message); return out; };
  f.approve = async extra => { f.clock += 1000; return approveRun({ ref: '17', cwd: source, packageRoot, ...extra }, f.ports); };
  f.open = async extra => { f.clock += 1000; return openRun({ ref: '17', cwd: source, packageRoot, ...extra }, f.ports); };
  return f;
}
