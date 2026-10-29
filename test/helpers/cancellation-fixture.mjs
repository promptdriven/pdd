import assert from 'node:assert/strict';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { mkdtempSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { startRun } from '../../src/workflow-runner.mjs';
import { readRun, runDirFor, writeRun } from '../../src/workflow-runs.mjs';

const exec = promisify(callbackExec);
export const packageRoot = resolve(import.meta.dirname, '../..');
export async function cancellationFixture(t, { override = false } = {}) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-cancel-'))), source = join(base, 'project'), stateDir = join(base, 'state'), home = join(base, 'home');
  t.after(() => rmSync(base, { force: true, recursive: true }));
  for (const dir of [source, stateDir, home]) mkdirSync(dir);
  const git = (...args) => execFileSync('git', args, { cwd: source, encoding: 'utf8' }).trim();
  git('init', '-q', '-b', 'alpha'); git('config', 'user.name', 'Cancellation Test'); git('config', 'user.email', 'test@example.invalid');
  git('remote', 'add', 'origin', 'https://github.com/example/project.git');
  writeFileSync(join(source, 'work.txt'), 'keep original work\n');
  git('add', '.'); git('commit', '-qm', 'initial'); git('update-ref', 'refs/remotes/origin/alpha', git('rev-parse', 'HEAD'));
  if (override) {
    const dir = join(source, '.agents/skills/pdd-small-change'); mkdirSync(dir, { recursive: true });
    writeFileSync(join(dir, 'workflow.json'), JSON.stringify({ version: 2, areas: [
      { name: 'plan', steps: ['scope', 'change'], optional: [], gate: 'approve' },
      { name: 'build', steps: ['verify', 'formal'], optional: [], gate: 'pr' }] }));
  }
  const commonDir = join(source, '.git'), runDir = runDirFor(commonDir, 17), events = [], chats = [];
  const claim = join(commonDir, 'pdd/worktree-assignments/issues/17.json');
  const f = { base, source, stateDir, home, commonDir, runDir, claim, events, chats, git, answer: true };
  f.read = () => readRun(runDir);
  f.ports = {
    env: { HOME: home }, stateDir, now: () => 600000, isTTY: true, pdd: 'pdd',
    execFile: async (file, args, options) => {
      if (file === 'git' && args[0] === 'fetch') return { stdout: '' };
      assert.ok(file === 'git' && !['push'].includes(args[0]), `Unexpected external effect: ${file} ${args}`);
      return exec(file, args, options);
    },
    resolveWorkflowIssue: async ({ issue }) => ({ repository: 'example/project', defaultBranch: 'alpha',
      issue: { number: Number(issue), title: 'Synthetic cancellation test', url: `https://github.com/example/project/issues/${issue}` } }),
    confirm: async question => { events.push(['confirm', question]); return f.answer; },
    startChat: async ({ run, area }) => { events.push(['start', run.runId]); const chat = { area, agent: run.agent, paneId: `pane-${run.runId}`, tabId: `tab-${run.runId}`, startedAt: 600000, session: null, configDir: null, label: `${run.repo} ${area}` }; chats.push(chat); return chat; },
    herdr: async args => {
      events.push(['herdr', ...args]);
      if (args[0] === 'pane' && args[1] === 'process-info') return { result: { process_info: { shell_pid: 2000000000, foreground_process_group_id: 2000000000, foreground_processes: [] } } };
      if (args[0] === 'tab' && args[1] === 'close') return {};
      if (args[0] === 'agent' && args[1] === 'get') throw Object.assign(Error('no agent'), { code: 'agent_not_found' });
      assert.fail(`Unexpected Herdr request: ${args}`);
    },
    writeRun: (run, ports) => { events.push(['save', run.runId, run.state]); return writeRun(run, ports); },
  };
  f.start = async (extra = {}) => startRun({ name: 'small-change', issue: '17', cwd: source, packageRoot, ...extra }, f.ports);
  const started = await f.start(); assert.equal(started.exitCode, 0, started.message);
  f.old = f.read();
  // These representative fields and actual retained files are independent of the cancellation implementation.
  f.old.pr = [{ number: 12, stage: 'code', state: 'open', url: 'https://github.com/example/project/pull/12' }];
  f.old.decisions = [{ area: 'previous', at: 10, decision: 'approve' }];
  f.old.artifacts = ['evidence.txt']; f.old.journal = 'keep journal';
  writeFileSync(join(f.old.root, 'uncommitted.txt'), 'keep uncommitted work\n');
  writeFileSync(join(runDir, 'journal.md'), 'keep journal bytes\n'); writeFileSync(join(runDir, 'evidence.txt'), 'keep artifact bytes\n');
  writeRun(f.old, f.ports); f.old = f.read(); f.events.length = 0;
  return f;
}
