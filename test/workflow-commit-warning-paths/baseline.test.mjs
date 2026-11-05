import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { startRun, stepDone, approveRun } from '../../src/workflow-runner.mjs';
import { fakeHerdr } from '../helpers/fake-herdr.mjs';

const exec = promisify(callbackExec);
const packageRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const issueUrl = 'https://github.com/example/project/issues/17';
const cases = JSON.parse(readFileSync(new URL('./cases.json', import.meta.url), 'utf8')).cases;
const steps = JSON.parse(readFileSync(join(packageRoot, 'skills/pdd-small-change/workflow.json'), 'utf8')).areas.at(-1).steps;
const afterVerify = steps.slice(steps.indexOf('verify') + 1);
async function fixture(t, { agent = 'claude', name = 'small-change' } = {}) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-runner-')));

  const source = join(base, 'project'), state = join(base, 'state'), home = join(base, 'home');
  for (const dir of [source, state, home, join(home, '.claude')]) mkdirSync(dir);
  const git = (cwd, ...args) => execFileSync('git', args, { cwd, encoding: 'utf8' }).trim();
  git(source, 'init', '-q', '-b', 'main'); git(source, 'config', 'user.email', 'test@example.invalid'); git(source, 'config', 'user.name', 'Runner Test');
  git(source, 'remote', 'add', 'origin', 'https://github.com/example/project.git');
  writeFileSync(join(source, 'value.mjs'), 'export const value = 1;\n'); git(source, 'add', '.'); git(source, 'commit', '-qm', 'initial');
  git(source, 'update-ref', 'refs/remotes/origin/main', git(source, 'rev-parse', 'HEAD'));
  const f = { base, source, state, git, herdr: fakeHerdr(), prs: [], pushes: [], edits: [], fetches: 0, clock: Date.parse('2026-10-27T17:00:00Z'), ci: [], merged: false, mergedNumbers: [] };
  f.herdr.now = () => f.clock;
  async function execFile(file, args, opts) {
    if (file === 'git' && args[0] === 'push') {
      f.pushes.push(args);
      // Like a real push, keep the remote-tracking branch current.
      const [from, to] = args[2].split(':'), sha = (await exec('git', ['rev-parse', from], { cwd: opts.cwd })).stdout.trim();
      await exec('git', ['update-ref', to.replace('refs/heads/', 'refs/remotes/origin/'), sha], { cwd: opts.cwd });
      return { stdout: '' };
    }
    if (file === 'git' && args[0] === 'ls-remote') {
      // The remote branch as the last push left it (pushes keep the remote-tracking branch current).
      const ref = args.at(-1), local = await exec('git', ['rev-parse', '--verify', '--quiet', ref.replace('refs/heads/', 'refs/remotes/origin/')], { cwd: opts.cwd }).catch(() => ({ stdout: '' }));
      return local.stdout.trim() ? { stdout: `${local.stdout.trim()}\t${ref}\n` } : { stdout: '', code: 2 };
    }
    if (file === 'git' && args[0] === 'fetch') {
      f.fetches++;
      const branch = args[2].replace(/^refs\/heads\//, '').split(':')[0];
      const merged = f.prs.find(pr => f.mergedNumbers.includes(pr.number) && pr.baseRefName === branch);
      if (merged) await exec('git', ['update-ref', `refs/remotes/origin/${branch}`, merged.headRefOid], { cwd: opts.cwd });
      return { stdout: '' };
    }
    if (file !== 'gh') return exec(file, args, { ...opts, encoding: 'utf8' });
    if (args[0] === 'repo' && args[1] === 'view') return { stdout: JSON.stringify({ nameWithOwner: 'example/project', defaultBranchRef: { name: 'main' }, url: 'https://github.com/example/project' }) };
    if (args[0] === 'api' && args[1] === 'repos/example/project/issues/17') return { stdout: JSON.stringify({ number: 17, html_url: issueUrl, title: 'Use value two', body: f.issueBody ?? 'Value must be two.' }) };
    if (args[0] === 'pr' && args[1] === 'create' && f.createError) { const stderr = f.createError; f.createError = null; return { stdout: '', stderr, code: 1 }; }
    if (args[0] === 'pr' && args[1] === 'create') {
      const value = flag => args[args.indexOf(flag) + 1];
      const number = 23 + f.prs.length;
      const pr = { number, url: `https://github.com/example/project/pull/${number}`, state: 'OPEN', headRefName: value('--head'), baseRefName: value('--base'),
        headRefOid: (await exec('git', ['rev-parse', 'HEAD'], { cwd: opts.cwd })).stdout.trim(), body: String(opts.input ?? ''), title: value('--title'),
        headRepository: { name: 'project' }, headRepositoryOwner: { login: 'example' }, isCrossRepository: false, mergeCommit: null };
      f.prs.push(pr); return { stdout: pr.url + '\n' };
    }
    if (args[0] === 'pr' && args[1] === 'list') {
      const head = args.includes('--head') ? args[args.indexOf('--head') + 1] : null, search = args.includes('--search') ? args[args.indexOf('--search') + 1].split('"')[1] : null;
      // The synthetic remote-tracking refs model remote effects, including an external push.
      for (const pr of f.prs) {
        const observed = await exec('git', ['rev-parse', '--verify', `refs/remotes/origin/${pr.headRefName}`], {cwd:opts.cwd}).catch(()=>null);
        if (observed) pr.headRefOid = observed.stdout.trim();
      }
      return { stdout: JSON.stringify(f.prs.filter(pr => (!head || pr.headRefName === head) && (!search || pr.body.includes(search)))) };
    }
    if (args[0] === 'pr' && args[1] === 'view') {
      const pr = f.prs.find(item => item.url === args[2]);
      return { stdout: JSON.stringify({ state: f.merged || f.mergedNumbers.includes(pr?.number) ? 'MERGED' : 'OPEN', mergedAt: null, statusCheckRollup: f.ci, body: pr?.body }) };
    }
    if (args[0] === 'pr' && args[1] === 'edit') {
      const pr = f.prs.find(item => item.url === args[2]) ?? assert.fail(`no PR ${args[2]}`);
      pr.body = String(opts.input ?? ''); f.edits.push(pr.number); return { stdout: '' };
    }
    throw Error(`unexpected gh ${args.join(' ')}`);
  }
  f.prompts = [];
  f.ports = { execFile, herdr: f.herdr.herdr, stateDir: state, layoutDirectory: join(state, 'herdr-layout'), now: () => f.clock, sleep: async ms => { f.clock += ms; }, findNativeSessions: stage => f.herdr.findNativeSessions(stage),
    env: { HOME: home, CLAUDE_CONFIG_DIR: join(home, '.claude') }, isTTY: true, pdd: '/abs/node /abs/pdd.mjs',
    confirm: async question => { f.prompts.push(question); return f.answer ?? true; },
    attach: async () => 0, readApprovalEvidence: async () => assert.fail('A terminal person needs no chat evidence') };
  f.run = () => startRun({ name, issue: '17', agent, cwd: source, packageRoot }, f.ports);
  f.record = () => JSON.parse(readFileSync(join(f.git(source, 'rev-parse', '--path-format=absolute', '--git-common-dir'), 'pdd', 'runs', '17', 'status.json'), 'utf8'));
  f.tick = (ms = 1000) => { f.clock += ms; };
  f.agentPorts = extra => ({ ...f.ports, isTTY: false, env: { ...f.ports.env, PDD_AGENT_SESSION: '1' }, ...extra });
  return f;
}

for (const scenario of cases) {
  test(scenario.id, async t => {
    const f = await fixture(t);
    t.after(() => rmSync(f.base, { recursive: true, force: true }));
    const start = await f.run();
    let run = f.record();
    f.tick();
    const scope = await stepDone({ step: 'scope', summary: 'scope', cwd: run.root }, f.agentPorts());
    const atGate = f.record();
    await t.test('scope saves the plan approval gate before publication', () => {
      assert.equal(start.exitCode, 0);
      assert.equal(scope.exitCode, 0);
      assert.equal(atGate.state, 'waiting');
      assert.equal(atGate.areas[atGate.area].name, 'plan');
      assert.equal(atGate.gate?.kind, 'approve');
      assert.equal(atGate.gate?.area, 'plan');
      assert.equal(f.prs.length, 0);
      assert.equal(f.pushes.length, 0);
    });
    f.tick();
    const approval = await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { HOME: f.ports.env.HOME } });
    run = f.record();
    await t.test('approval advances to the first build step', () => {
      assert.equal(approval.exitCode, 0);
      assert.equal(run.gate, null);
      assert.equal(run.state, 'running');
      assert.equal(run.areas[run.area].name, 'build');
      assert.equal(run.areas[run.area].steps.find(step => !run.done[step]), 'change');
    });
    // A clean worktree still needs a prior change for the PR to have a diff.
    if (scenario.id === 'clean') {
      writeFileSync(join(run.root, 'value.mjs'), 'already committed\n');
      f.git(run.root, 'add', 'value.mjs');
      f.git(run.root, 'commit', '-qm', 'prior change');
    }
    const before = f.git(run.root, 'rev-parse', 'HEAD');
    for (const path of scenario.given.modifiedTracked ?? []) writeFileSync(join(run.root, path), 'changed\n');
    for (const path of scenario.given.untracked ?? []) writeFileSync(join(run.root, path), 'new\n');
    if (scenario.given.rename) f.git(run.root, 'mv', scenario.given.rename.from, scenario.given.rename.to);
    f.tick();
    await stepDone({ step: 'change', summary: 'change', cwd: run.root }, f.agentPorts());
    f.tick();
    writeFileSync(join(run.runDir, 'verify.md'), 'offline fixture\n');
    let out = await stepDone({ step: 'verify', summary: 'fixture', cwd: run.root }, f.agentPorts());
    for (const step of afterVerify) {
      f.tick();
      out = await stepDone({ step, summary: `${step} done`, cwd: run.root }, f.agentPorts());
    }
    const head = f.git(run.root, 'rev-parse', 'HEAD');
    await t.test('gate and publication controls', () => {
      assert.equal(start.exitCode, 0);
      assert.equal(scope.exitCode, 0);
      assert.equal(approval.exitCode, 0);
      assert.equal(out.exitCode, scenario.expect.exitCode);
      assert.equal(f.prs.length, 1);
      assert.match(out.message, /PR: https:\/\/github\.com\/example\/project\/pull\/23/);
    });
    if (scenario.id === 'clean') {
      await t.test('no automatic commit or warning', () => {
        assert.equal(head !== before, scenario.expect.automaticCommit);
        assert.equal(out.message.includes('warning: pdd committed'), scenario.expect.automaticCommitWarning);
      });
      return;
    }
    await t.test('actual committed destination paths', () => {
      assert.notEqual(head, before);
      const raw = execFileSync('git', ['diff-tree', '--no-commit-id', '--name-status', '-r', '-M', '-z', 'HEAD'], { cwd: run.root });
      const fields = raw.toString('utf8').split('\0');
      const paths = [];
      for (let i = 0; i < fields.length && fields[i];) {
        const status = fields[i++];
        const first = fields[i++];
        paths.push(status.startsWith('R') ? fields[i++] : first);
      }
      assert.deepEqual(paths.sort(), [...scenario.expect.committedPaths].sort());
    });
    const warning = out.message.match(/^warning: pdd committed (\d+) uncommitted file\(s\): (.*)\.$/m);
    await t.test('warning wording and count', () => {
      assert.ok(warning, 'expected unchanged automatic commit warning wording');
      assert.equal(Number(warning[1]), scenario.expect.warningPaths.length);
    });
    await t.test('exact warning path set', () => {
      assert.ok(warning, 'expected automatic commit warning');
      assert.deepEqual(warning[2].split(', ').sort(), [...scenario.expect.warningPaths].sort());
    });
  });
}
