import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { startRun, stepDone, approveRun, runStatus } from '../../src/workflow-runner.mjs';
import { viewRun } from '../../src/workflow-view.mjs';
import { fakeHerdr } from './fake-herdr.mjs';

export const packageRoot = resolve(import.meta.dirname, '../..');
export const cases = JSON.parse(readFileSync(join(packageRoot, 'test/fixtures/workflow-step-results-2922-cases.json'), 'utf8'));
export const scenario = JSON.parse(readFileSync(join(packageRoot, 'test/runtime/workflow-step-results-2922.json'), 'utf8'));
export const gitEnv = { ...process.env, GIT_CONFIG_GLOBAL: '/dev/null', GIT_CONFIG_NOSYSTEM: '1', GIT_TERMINAL_PROMPT: '0' };
const gitOptions = ['-c', 'user.name=Synthetic 2922 fixture', '-c', 'user.email=synthetic-2922@example.invalid',
  '-c', 'core.hooksPath=/dev/null', '-c', 'commit.gpgsign=false', '-c', 'tag.gpgsign=false'];
const ok = result => assert.equal(result.exitCode, 0, result.message);

// Real Git, filesystem, selection and workflow transitions. Only GitHub, Herdr and
// the existing result reader are supplied. Confirmation is SYNTHETIC fixture input,
// never a person's authorization, and all effects stay in this disposable tree.
export async function setup(t, { completed = true } = {}) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-step-results-2922-')));
  t.after(() => rmSync(base, { recursive: true, force: true }));
  const source = join(base, 'project'), remote = join(base, 'origin.git'), home = join(base, 'home'), stateDir = join(base, 'state');
  for (const dir of [source, home, stateDir]) mkdirSync(dir);
  const git = (cwd, ...args) => execFileSync('git', [...gitOptions, ...args], { cwd, env: gitEnv, encoding: 'utf8' }).trim();
  git(base, 'init', '--bare', '-q', '-b', 'main', remote);
  git(source, 'init', '-q', '-b', 'main');
  const skill = join(source, '.agents/skills/pdd-bug'); mkdirSync(skill, { recursive: true });
  writeFileSync(join(skill, 'SKILL.md'), '# Synthetic 2922 isolated workflow\n');
  writeFileSync(join(skill, 'workflow.json'), JSON.stringify({ version: 2, areas: [
    { ...cases.input.selectedRun.areas[0], gate: 'approve' },
    { ...cases.input.selectedRun.areas[1], gate: 'pr', before: 'approve' }
  ] }));
  writeFileSync(join(source, 'value.mjs'), 'export const value = 1;\n');
  git(source, 'add', '.'); git(source, 'commit', '-qm', 'Synthetic baseline');
  git(source, 'remote', 'add', 'origin', 'https://github.com/example/project.git');
  git(source, 'push', remote, 'main');
  const h = fakeHerdr(), f = { base, source, remote, home, stateDir, git, h, clock: 0, results: [], prs: [], calls: [], confirmations: [] };
  h.now = () => f.clock;
  const execFile = async (file, args, options) => {
    f.calls.push({ file, args: [...args] });
    if (file === 'git') {
      // Explicit local transport mapping, with real fetch/push/ls-remote behavior.
      const transport = ['fetch', 'push', 'ls-remote'].includes(args[0]) ? ['-c', `url.${remote}.insteadOf=https://github.com/example/project.git`] : [];
      try {
        return { stdout: execFileSync('git', [...gitOptions, ...transport, ...args], { ...options, env: gitEnv, encoding: 'utf8' }) };
      } catch (error) {
        // execFile's rejected exit code is numeric; execFileSync calls it status.
        // Preserve real nonzero exits (notably an absent branch) at the port.
        if (Number.isInteger(error.status)) error.code = error.status;
        throw error;
      }
    }
    assert.equal(file, 'gh', `No external service/program permitted: ${file}`);
    if (args[0] === 'repo' && args[1] === 'view') return { stdout: JSON.stringify({ nameWithOwner: 'example/project', defaultBranchRef: { name: 'main' }, url: 'https://github.com/example/project' }) };
    if (args[0] === 'api' && args[1] === 'repos/example/project/issues/2922') return { stdout: JSON.stringify({ number: 2922, html_url: cases.input.selectedRun.issue.url, title: cases.input.selectedRun.issue.title, body: 'SYNTHETIC local fixture; no live check.' }) };
    if (args[0] === 'pr' && args[1] === 'list') return { stdout: JSON.stringify(f.prs) };
    if (args[0] === 'pr' && args[1] === 'create') {
      const flag = name => args[args.indexOf(name) + 1];
      const pr = { number: 23, url: 'https://github.com/example/project/pull/23', state: 'OPEN', headRefName: flag('--head'), baseRefName: flag('--base'),
        headRefOid: git(options.cwd, 'rev-parse', 'HEAD'), body: String(options.input ?? ''),
        headRepository: { name: 'project' }, headRepositoryOwner: { login: 'example' }, isCrossRepository: false, mergeCommit: null };
      f.prs.push(pr); return { stdout: `${pr.url}\n` };
    }
    if (args[0] === 'pr' && args[1] === 'view') return { stdout: JSON.stringify({ ...f.prs[0], state: f.merged ? 'MERGED' : 'OPEN', statusCheckRollup: [] }) };
    if (args[0] === 'pr' && args[1] === 'edit') { f.prs[0].body = String(options.input ?? ''); return { stdout: '' }; }
    assert.fail(`Unexpected GitHub port request: ${args.join(' ')}`);
  };
  f.ports = { execFile, herdr: h.herdr, stateDir, layoutDirectory: join(stateDir, 'layout'), now: () => f.clock,
    sleep: async ms => { f.clock += ms; }, findNativeSessions: h.findNativeSessions,
    env: { HOME: home }, isTTY: true,
    confirm: async question => { f.confirmations.push({ input: 'SYNTHETIC terminal fixture: yes', question }); return true; },
    readRunResults: () => structuredClone(f.results) };
  ok(await startRun({ name: 'bug', issue: '2922', agent: 'codex', cwd: source, packageRoot }, f.ports));
  const runPath = join(source, '.git/pdd/runs/2922/status.json');
  f.record = () => JSON.parse(readFileSync(runPath, 'utf8'));
  f.root = f.record().root;
  for (const step of ['reproduce', 'check']) {
    const supplied = cases.input.selectedRun.done[step]; f.clock = supplied.at; f.results = supplied.pddResults ?? [];
    ok(await stepDone({ step, summary: supplied.summary, cwd: f.root }, f.ports));
  }
  f.clock = 2100; ok(await approveRun({ ref: '2922', cwd: source }, f.ports));
  for (const step of ['verify', 'finish']) {
    const supplied = cases.input.selectedRun.done[step]; f.clock = supplied.at; f.results = supplied.pddResults ?? [];
    ok(await stepDone({ step, summary: supplied.summary, cwd: f.root }, f.ports));
  }
  f.results = cases.input.runWideResults;
  if (completed) {
    writeFileSync(join(f.root, 'value.mjs'), 'export const value = 2; // SYNTHETIC fixture\n');
    git(f.root, 'add', 'value.mjs'); git(f.root, 'commit', '-qm', 'Synthetic code fixture');
    f.clock = 4100; ok(await approveRun({ ref: '2922', cwd: source }, f.ports));
    f.clock = 4200; f.merged = true;
    // Public status refresh obtains the synthetic merged PR observation. It is
    // setup only: no displayed value is used as an assertion oracle.
    ok(await runStatus({ ref: '2922', cwd: source }, f.ports));
  }
  const saved = f.record();
  // Establish native setup BEFORE observing any acceptance/replay output.
  assert.equal(saved.repo, cases.expected.selectedRun.repo);
  assert.equal(saved.number, cases.expected.selectedRun.number);
  assert.equal(saved.areas[saved.area].name, cases.expected.selectedRun.currentArea);
  assert.deepEqual(saved.areas.map(({ name, steps, optional }) => ({ name, steps, optional })), cases.input.selectedRun.areas);
  assert.deepEqual(saved.done, cases.input.selectedRun.done, 'Exact saved setup, including absent versus empty fields and time anchors');
  assert.equal(saved.state, completed ? 'completed' : 'waiting');
  if (completed) assert.equal(saved.gate, null);
  assert.deepEqual(f.results, []);
  // Generated identity/path/base and lifecycle metadata are native, not literal
  // /project, synthetic-2922 or aaaa... fixtures. Done times/data stay exact.
  assert.ok(saved.runId && saved.runId !== cases.input.selectedRun.runId);
  assert.equal(realpathSync(saved.root), f.root);
  assert.equal(saved.sourceRoot, source);
  assert.equal(saved.runDir, join(source, '.git/pdd/runs/2922'));
  assert.equal(saved.baseSha, git(source, 'rev-parse', 'main'));
  assert.equal(saved.startedAt, 0);
  f.input = operation => ({ ...operation.input, cwd: source });
  f.observe = operation => operation.export === 'viewRun' ? viewRun(f.input(operation), f.ports) : runStatus(f.input(operation), f.ports);
  return f;
}
