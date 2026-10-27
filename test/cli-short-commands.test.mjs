import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { parseArgv } from '../src/argument-parser.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const id = '123e4567-e89b-42d3-a456-426614174000';
const id2 = '123e4567-e89b-42d3-a456-426614174001';
const capture = () => ({ text: '', write(value) { this.text += value; } });
const transport = Object.fromEntries(['runHerdrStage', 'inspectHerdrStage', 'attachHerdrStage', 'closeHerdrStage'].map(name => [name, () => assert.fail(`unexpected ${name}`)]));
const cwd = () => { const root = mkdtempSync(join(tmpdir(), 'pdd-short-')); mkdirSync(join(root, '.git')); return root; };
const records = entries => { entries.forEach((entry, index) => { entry.runDir ??= `/tmp/fake-run-${index}`; }); const fake = {
  readRunIndex: async ports => { fake.seen.push(ports); return { entries, dropped: 0 }; },
  readJournalLast: async runDir => ({ value: { state: entries.find(entry => entry.runDir === runDir)?.state ?? entries[0].state }, warnings: [] }),
  runStatusFromState: async state => ({ runId: state.runId, workflow: state.name, repo: state.repo, issue: state.issue,
    state: state.index === 1 ? 'waiting' : 'running', stage: { id: 'approve' }, steps: [] }),
  seen: [],
}; return fake; };

test('short command parser admits issue forms, prefixes, confirmation and status-all', () => {
  assert.equal(parseArgv(['workflow', 'approve']).local, 'workflow-approve');
  assert.equal(parseArgv(['workflow', 'approve', '#2', '--yes']).operands[0], '#2');
  assert.equal(parseArgv(['workflow', 'resume', '123e4567']).operands[0], '123e4567');
  assert.equal(parseArgv(['workflow', 'resume', id]).operands[0], id);
  assert.equal(parseArgv(['workflow', 'changes', 'owner/repo#2', 'please', 'retry']).operands.length, 3);
  assert.equal(parseArgv(['workflow', 'status', '--all']).options['--all'], true);
  assert.equal(parseArgv(['workflow', 'watch', 'https://github.com/owner/repo/issues/2']).local, 'workflow-watch');
});

test('approve resolves a local issue, asks in a TTY, and passes the full UUID to the runner', async t => {
  const root = cwd(); t.after(() => rmSync(root, { recursive: true, force: true }));
  const entry = { runId: id, repo: 'owner/repo', issue: { number: 2, title: 'Plan it' }, state: { runId: id, name: 'small-change', repo: 'owner/repo', issue: { number: 2, title: 'Plan it' }, index: 1 } };
  const fake = records([entry]); let called;
  const stdout = capture(), stderr = capture();
  const code = await runPdd(['workflow', 'approve', '2'], { cwd: root, stdout, stderr, stdinIsTTY: true, input: async () => 'y', workflowRecords: fake,
    workflowRunner: { resumeWorkflow: async input => { called = input; return { exitCode: 2, state: 'waiting', message: 'waiting' }; } }, workflowStages: transport });
  assert.equal(code, 2); assert.deepEqual(called, { runId: id, cwd: root, packageRoot: process.cwd(), decision: 'approve' });
  assert.match(stdout.text, /Approve the plan for owner\/repo#2 "Plan it"\? \(y\/N\)/); assert.equal(stderr.text, '');
});

test('decisions refuse non-TTY, --yes without TTY, and require evidence for agent relays', async t => {
  const root = cwd(); t.after(() => rmSync(root, { recursive: true, force: true }));
  const entry = { runId: id, repo: 'owner/repo', issue: { number: 2, title: 'Plan it' }, state: { runId: id, name: 'small-change', repo: 'owner/repo', issue: { number: 2 }, index: 1 } };
  for (const args of [['workflow', 'approve', '2'], ['workflow', 'approve', '2', '--yes']]) {
    const stderr = capture(); assert.equal(await runPdd(args, { cwd: root, stderr, stdout: capture(), stdinIsTTY: false, workflowRecords: records([entry]), workflowRunner: { resumeWorkflow: () => assert.fail('no mutation') } }), 2);
    assert.match(stderr.text, /real TTY/);
  }
  const stderr = capture(); assert.equal(await runPdd(['workflow', 'skip', '2'], { cwd: root, stderr, stdout: capture(), stdinIsTTY: false, env: { PDD_AGENT_SESSION: `${id}/scope` }, workflowRecords: records([entry]), workflowRunner: { resumeWorkflow: () => assert.fail('no mutation') } }), 1);
  assert.match(stderr.text, /could not confirm|USER message|evidence is unavailable/);
  const stdout = capture(); let called = false;
  assert.equal(await runPdd(['workflow', 'skip', '2'], { cwd: root, stderr: capture(), stdout, stdinIsTTY: false, env: { PDD_AGENT_SESSION: `${id}/scope` }, approvalEvidence: async () => true, workflowRecords: records([entry]), workflowStages: transport, workflowRunner: { resumeWorkflow: async () => { called = true; return { exitCode: 2, state: 'waiting', message: 'waiting' }; } } }), 2);
  assert.equal(called, true);
});

test('status --all refuses to guess when two repositories share an issue number', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-outside-')); t.after(() => rmSync(root, { recursive: true, force: true }));
  const entries = [
    { runId: id, repo: 'one/app', issue: { number: 45, title: 'One' }, state: { runId: id, name: 'small-change', repo: 'one/app', issue: { number: 45, title: 'One' }, index: 1 } },
    { runId: id2, repo: 'two/app', issue: { number: 45, title: 'Two' }, state: { runId: id2, name: 'small-change', repo: 'two/app', issue: { number: 45, title: 'Two' }, index: 1 } },
  ];
  const fake = records(entries), stderr = capture(), stdout = capture();
  assert.equal(await runPdd(['workflow', 'approve', '45'], { cwd: root, stdout, stderr, workflowRecords: fake, stdinIsTTY: true }), 2);
  assert.match(stderr.text, /one\/app#45 "One"/); assert.match(stderr.text, /two\/app#45 "Two"/);
  stdout.text = ''; stderr.text = '';
  assert.equal(await runPdd(['workflow', 'status', '--all'], { cwd: root, stdout, stderr, workflowRecords: fake }), 0);
  assert.match(stdout.text, /one\/app#45 "One"/); assert.match(stdout.text, /two\/app#45 "Two"/);
  assert.doesNotMatch(stdout.text, new RegExp(id)); assert.doesNotMatch(stdout.text, /resume [0-9a-f]{8}-/);
});

test('bare issue numbers bind to the git common directory from run worktrees and subfolders', async t => {
  const home = mkdtempSync(join(tmpdir(), 'pdd-home-'));
  const repoA = mkdtempSync(join(tmpdir(), 'pdd-repo-a-'));
  const repoB = mkdtempSync(join(tmpdir(), 'pdd-repo-b-'));
  mkdirSync(join(repoA, '.git', 'pdd', 'workflows', id), { recursive: true });
  mkdirSync(join(repoB, '.git', 'pdd', 'workflows', id2), { recursive: true });
  const runWorktree = join(repoA, 'run-worktree', 'issue-5', 'nested'); mkdirSync(runWorktree, { recursive: true });
  const bSubfolder = join(repoB, 'src', 'nested'); mkdirSync(bSubfolder, { recursive: true });
  mkdirSync(join(home, '.pdd'), { recursive: true });
  t.after(() => { rmSync(home, { recursive: true, force: true }); rmSync(repoA, { recursive: true, force: true }); rmSync(repoB, { recursive: true, force: true }); });
  const entries = [
    { runId: id, repo: 'one/app', root: runWorktree, runDir: join(repoA, '.git', 'pdd', 'workflows', id), issue: { number: 2, title: 'A two' }, state: { runId: id, name: 'small-change', repo: 'one/app', issue: { number: 2, title: 'A two' }, index: 1 } },
    { runId: id2, repo: 'two/app', root: bSubfolder, runDir: join(repoB, '.git', 'pdd', 'workflows', id2), issue: { number: 2, title: 'B two' }, state: { runId: id2, name: 'small-change', repo: 'two/app', issue: { number: 2, title: 'B two' }, index: 1 } },
  ];
  const fake = records(entries), transport = Object.fromEntries(['runHerdrStage', 'inspectHerdrStage', 'attachHerdrStage', 'closeHerdrStage'].map(name => [name, () => assert.fail(`unexpected ${name}`)]));
  const answer = async () => 'n';
  const aErr = capture(), aOut = capture();
  assert.equal(await runPdd(['workflow', 'approve', '2'], { cwd: runWorktree, stdout: aOut, stderr: aErr, stdinIsTTY: true, input: answer, workflowRecords: fake }), 2);
  assert.match(aOut.text, /Approve the plan for one\/app#2 "A two"/);
  const bErr = capture(), bOut = capture();
  assert.equal(await runPdd(['workflow', 'approve', '2'], { cwd: bSubfolder, stdout: bOut, stderr: bErr, stdinIsTTY: true, input: answer, workflowRecords: fake }), 2);
  assert.match(bOut.text, /Approve the plan for two\/app#2 "B two"/);
  const outsideErr = capture();
  assert.equal(await runPdd(['workflow', 'approve', '2'], { cwd: home, stdout: capture(), stderr: outsideErr, stdinIsTTY: true, input: answer, workflowRecords: fake }), 2);
  assert.match(outsideErr.text, /one\/app#2 "A two"/); assert.match(outsideErr.text, /two\/app#2 "B two"/);
  assert.match(outsideErr.text, /pdd workflow approve one\/app#2/); assert.match(outsideErr.text, /pdd workflow approve two\/app#2/);
  void transport;
});
