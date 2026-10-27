import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, readFileSync, rmSync, existsSync, mkdirSync, symlinkSync, linkSync, unlinkSync, cpSync, readdirSync, openSync, closeSync, writeSync, readSync, statSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { constants as bufferConstants } from 'node:buffer';
import { join, resolve } from 'node:path';
import { createHash, randomUUID } from 'node:crypto';
import { execFile as callbackExec, spawn } from 'node:child_process';
import { promisify } from 'node:util';
import { runWorkflow, resumeWorkflow, attachWorkflow, WORKFLOW_STAGES } from '../src/workflow-runner.mjs';
import { loadGuidance as actualGuidance } from '../src/guidance.mjs';
import { runHerdrStage, inspectHerdrStage, closeHerdrStage, closeHerdrRun } from '../src/workflow-stage-herdr.mjs';

const exec = promisify(callbackExec);
const packageRoot = resolve(import.meta.dirname, '..');
const sha = value => createHash('sha256').update(value).digest('hex');
const issueUrl = 'https://github.com/example/project/issues/17';
const output = { write() {} };
async function fixture(t, options = {}) {
  const activePackageRoot = options.packageRoot ?? packageRoot;
  let cwd = mkdtempSync(join(tmpdir(), 'pdd-runner-'));
  const sourceCwd = cwd;
  t.after(() => rmSync(sourceCwd, { recursive: true, force: true }));
  const git = async (...args) => (await exec('git', args, { cwd })).stdout.trim();
  await git('init', '-b', 'main'); await git('config', 'user.email', 'test@example.invalid');
  await git('config', 'user.name', 'Runner Test'); await git('remote', 'add', 'origin', 'https://github.com/example/project.git');
  writeFileSync(join(cwd, 'value.mjs'), 'export const value = 1;\n');
  writeFileSync(join(cwd, 'check.mjs'), "import assert from 'node:assert/strict'; import {value} from './value.mjs'; assert.equal(value, 2);\n");
  await git('add', '.'); await git('commit', '-m', 'initial');
  const initial = await git('rev-parse', 'HEAD');
  await git('update-ref', 'refs/remotes/origin/main', initial);
  const calls = [], native = [], contexts = [];
  const f = { cwd, sourceCwd, gitDir: join(cwd, '.git'), git, calls, native, contexts, initial, pr: null, merged: false, options, closes: 0 };
  const plan = [[process.execPath, 'check.mjs']];
  async function execFile(file, args, opts) {
    calls.push({ file, args: [...args] });
    if (file === 'git' && args[0] === 'push') {
      assert.equal(f.saved(native.at(-1).input.runId).pending.kind, 'pr', 'PR intent must be durable BEFORE push');
      if (options.preAuthPushFailure && !f.authFixed) throw Object.assign(Error('Username prompt timed out'), { code: 'ETIMEDOUT' });
      if (options.preAuthPushFailure) {
        const events = readFileSync(join(f.gitDir, 'pdd/workflows', native.at(-1).input.runId, 'journal.jsonl'), 'utf8').trim().split('\n').map(JSON.parse);
        assert.equal(events.at(-1).event, 'pr.unpublished_retry_intent', 'explicit retry intent durable BEFORE recovered push');
      }
      return { stdout: '', stderr: '' };
    }
    if (file === 'git' && args[0] === 'ls-remote' && args.includes('--exit-code')) {
      if (f.remoteUnreadable) throw Object.assign(Error('authentication unreadable'), { code: 128, stdout: '', stderr: 'authentication failed' });
      return { code: f.remoteHead ? 0 : 2, stdout: f.remoteHead ? `${f.remoteHead}\t${args.at(-1)}\n` : '', stderr: '' };
    }
    if (file === 'git' && args[0] === 'ls-remote') return { stdout: f.pr ? `${f.pr.headRefOid}\trefs/heads/${f.pr.headRefName}\n` : '', stderr: '' };
    if (file !== 'gh') return exec(file, args, opts);
    if (args[0] === 'repo' && args[1] === 'view') return { stdout: JSON.stringify({ nameWithOwner: 'example/project', defaultBranchRef: { name: 'main' }, url: 'https://github.com/example/project' }) };
    if (args[0] === 'api' && args[1] === 'repos/example/project/issues/17') return { stdout: JSON.stringify({ number: 17, html_url: issueUrl, title: 'Use value two', body: 'The observable result must be two.', state: 'OPEN', isPullRequest: false }) };
    if (args[0] === 'pr' && args[1] === 'create') {
      const value = flag => args[args.indexOf(flag) + 1];
      f.pr = { number: 23, url: 'https://github.com/example/project/pull/23', state: 'OPEN',
        headRefName: value('--head'), baseRefName: value('--base'), headRefOid: await git('rev-parse', 'HEAD'),
        body: readFileSync(value('--body-file'), 'utf8'), title: value('--title'),
        headRepository: { name: 'project' }, headRepositoryOwner: { login: 'example' }, baseRepository: { nameWithOwner: 'example/project' },
        isCrossRepository: false, mergeCommit: null, mergedAt: null };
      if (options.lostPrReply) throw Error('lost create reply');
      return { stdout: f.pr.url + '\n' };
    }
    if (args[0] === 'pr' && ['list', 'view'].includes(args[1])) {
      if (f.prUnreadable) throw Error('PR lookup unreadable');
      if (f.pr && f.merged) Object.assign(f.pr, { state: 'MERGED', mergedAt: '2026-10-24T00:00:00Z', mergeCommit: { oid: f.pr.headRefOid } });
      return { stdout: JSON.stringify(args[1] === 'list' ? f.pr ? [f.pr] : [] : f.pr) };
    }
    throw Error(`Unexpected fake GitHub command: ${args.join(' ')}`);
  }
  const ports = { execFile, stdout: output, stderr: output,
    async loadGuidance(value) { contexts.push(value); return actualGuidance(value); },
    async launchNativeSession(value) {
      const input = JSON.parse(value.request.split('PDD_STAGE_INPUT_JSON\n')[1].split('\nPDD_STAGE_INPUT_END')[0]);
      native.push({ ...value, input });
      if (options.pauseNative) await options.pauseNative;
      if (options.nativeCode !== undefined) return options.nativeCode;
      if (options.failStage === input.stageId) return 8;
      if (options.missingHandoff) return 0;
      if (['scope', 'prompt-story', 'change', 'build'].includes(input.stageId)) {
        if ((await git('branch', '--show-current')) === 'main') await git('switch', '-c', 'pdd-test-topic');
      }
      const files = [];
      const add = (path, contents, role) => {
        if (contents !== null) writeFileSync(join(cwd, path), contents);
        files.push({ path, sha256: sha(readFileSync(join(cwd, path))), role });
      };
      if (input.protocol === 'proposal') add('cases.json', '[{"expected":2}]\n', 'cases');
      if (input.protocol === 'proposal' && input.requiredRoles.includes('prompt')) {
        add('module.prompt.md', 'Return the observable value two.\n', 'prompt');
        add('STORY.md', 'The person sees two.\n', 'story');
      }
      if (input.protocol === 'work') {
        add('value.mjs', `export const value = ${options.wrongBehavior ? 3 : 2};\n`, 'implementation');
        if (options.changeAccepted) writeFileSync(join(cwd, 'cases.json'), '[{"expected":3}]\n');
      }
      if (input.protocol === 'verify') {
        let contents = null;
        if (options.mutatingTest) contents = "import {writeFileSync} from 'node:fs'; writeFileSync('value.mjs', 'export const value = 3;\\n');\n";
        if (options.mutatingHandoff) contents = `import {readFileSync,writeFileSync} from 'node:fs'; const path=${JSON.stringify(input.handoffPath)}; const h=JSON.parse(readFileSync(path)); h.summary='changed during checks'; writeFileSync(path,JSON.stringify(h));\n`;
        add('check.mjs', contents, 'tests');
      }
      if (files.length) {
        await git('add', '.');
        if (await git('status', '--porcelain')) await git('commit', '-m', input.stageId);
      }
      const h = { version: 1, runId: input.runId, stageId: input.stageId, issueUrl,
        inputRevision: options.staleHandoff ? initial.replace(/^./, initial[0] === 'a' ? 'b' : 'a') : input.inputRevision,
        summary: `Completed current ${input.stageId}; observable expectations remain independent.`, files };
      if (['proposal', 'verify'].includes(input.protocol)) h.testCommands = plan;
      if (input.stageId === 'verify' && options.changedPlan) h.testCommands = [[process.execPath, '-e', 'process.exit(0)']];
      if (input.stageId === 'change' && options.emptyWork) h.files = [];
      writeFileSync(input.handoffPath, JSON.stringify(h)); return 0;
    } };
  f.ports = ports;
  const assignments = new Map();
  if (!options.defaultWorktree) {
  ports.allocateIssueWorktree = async ({ runId, repository, issueNumber, workflowName, baseRef }) => {
    const inputPath = join(sourceCwd, '.git', 'pdd', 'workflow-inputs', runId, 'input.jsonl');
    const savedInput = JSON.parse(readFileSync(inputPath, 'utf8'));
    assert.ok(savedInput.baseContext.includes('# Prompting guide'), 'full guide bytes durable BEFORE allocation');
    assert.ok(savedInput.definition.files.some(file => file.path === 'workflow.json'));
    if (options.onAllocate) options.onAllocate(savedInput);
    if (assignments.size) return { state: 'conflict', assignment: [...assignments.values()][0], message: 'Issue already assigned; original retained.' };
    const commonDir = join(sourceCwd, '.git'), id = randomUUID();
    const worktreePath = join(commonDir, 'pdd', 'worktrees', id), branch = `pdd/${workflowName}-${issueNumber}-${id.slice(0,8)}`;
    const baseSha = (await exec('git', ['rev-parse', baseRef], { cwd: sourceCwd })).stdout.trim();
    mkdirSync(join(commonDir, 'pdd', 'worktrees'), { recursive: true });
    await exec('git', ['worktree', 'add', '-b', branch, worktreePath, baseSha], { cwd: sourceCwd });
    cwd = worktreePath; f.cwd = cwd;
    f.gitDir = await git('rev-parse', '--absolute-git-dir');
    const assignment = { version: 1, runId, repository, issueNumber, workflowName, commonDir, sourceRoot: sourceCwd,
      worktreePath, gitDir: f.gitDir, branch, baseRef, baseSha };
    assignments.set(runId, assignment);
    return { state: 'ready', assignment, message: 'Actual disposable worktree ready.' };
  };
  ports.lookupIssueWorktree = async ({ runId }) => ({ state: assignments.has(runId) ? 'ready' : 'recovery_required',
    assignment: assignments.get(runId) ?? null, message: 'Read-only original assignment.' });
  }
  const foreground = ports.launchNativeSession;
  ports.runHerdrStage = async (value, transportPorts) => {
    const backend = { version: 1, runId: value.runId, stageId: value.stageId, attemptId: value.attemptId,
      agent: value.agent, cwd: value.cwd, phase: 'ready', promptDigest: sha(`${value.context}\n\n# Current workflow stage\n${value.instructions}`),
      terminalId: `terminal-${value.attemptId}`, nativeSession: null, evidence: { readySeq: 1 } };
    await value.checkpoint(backend);
    const code = await foreground({ ...value, request: value.instructions });
    backend.transportFailed = code !== 0;
    backend.phase = 'candidate'; backend.evidence = { readySeq: 1, workingSeq: 2, settledSeq: 3 };
    await value.checkpoint(backend);
    return { state: code === 0 ? 'settled' : 'recovery_required', backend, evidence: backend.evidence, reason: `native code ${code}` };
  };
  ports.inspectHerdrStage = async ({ backend }) => ({ state: backend.transportFailed ? 'recovery_required' : 'settled', backend, evidence: backend.evidence });
  ports.closeHerdrStage = async ({ backend, acceptance }, transportPorts) => {
    f.closes++;
    assert.deepEqual(f.saved(backend.runId).pending.acceptance, acceptance, 'acceptance durable BEFORE cleanup');
    const closed = { ...backend, phase: 'closed', acceptanceDigest: sha(JSON.stringify(acceptance)) };
    await transportPorts.checkpoint(closed);
    return { state: 'closed', backend: closed, evidence: closed.evidence };
  };
  ports.attachHerdrStage = async () => 0;
  f.packageRoot = activePackageRoot;
  const executionPorts = () => !options.defaultWorktree ? ports : { ...ports,
    runHerdrStage: async (value, ...rest) => {
      cwd = value.cwd; f.cwd = cwd;
      f.gitDir = (await exec('git', ['rev-parse', '--absolute-git-dir'], { cwd })).stdout.trim();
      assert.notEqual(cwd, sourceCwd);
      assert.ok(existsSync(join(sourceCwd, '.git', 'pdd', 'worktree-assignments', 'runs', value.runId + '.json')));
      return ports.runHerdrStage(value, ...rest);
    } };
  f.run = (name = 'small-change', agent = 'claude') => runWorkflow({ name, issue: '17', agent, cwd, packageRoot: activePackageRoot }, executionPorts());
  f.resume = (runId, decision) => resumeWorkflow({ runId, decision, cwd: options.defaultWorktree ? sourceCwd : cwd, packageRoot: activePackageRoot }, executionPorts());
  f.saved = runId => readFileSync(join(f.gitDir, 'pdd', 'workflows', runId, 'journal.jsonl'), 'utf8').trim().split('\n').map(JSON.parse).at(-1).state;
  return f;
}
function projectWorkflow(f, marker = 'OWNED_RECIPE_A__') {
  const directory = join(f.sourceCwd, '.pdd', 'workflows', 'snapshot-check'); mkdirSync(directory, { recursive: true });
  const definition = { version: 1, name: 'snapshot-check', overview: 'WORKFLOW.md', stages: [
    { id: 'agree', kind: 'agent', protocol: 'proposal', approval: 'next-advance', requiredRoles: ['cases'], file: 'plan.md' },
    { id: 'implement', kind: 'agent', protocol: 'work', requiredRoles: ['implementation'], file: 'work.md' },
    { id: 'prove', kind: 'agent', protocol: 'verify', file: 'check.md' },
    { id: 'publish', kind: 'pr', publication: 'verified', file: 'pr.md' },
    { id: 'merged', kind: 'merge', prStage: 'publish', file: 'merge.md' }
  ] };
  writeFileSync(join(directory, 'workflow.json'), JSON.stringify(definition));
  for (const file of ['WORKFLOW.md', 'plan.md', 'work.md', 'check.md', 'pr.md', 'merge.md']) writeFileSync(join(directory, file), `# ${marker}\nUse only this workflow's current stage.\n`);
  return directory;
}

test('listed workflow totals distinguish native stages from human, optional and PR steps', () => {
  assert.deepEqual(Object.values(WORKFLOW_STAGES).map(stages => stages.length), [12, 11, 5]);
  assert.deepEqual(Object.values(WORKFLOW_STAGES).map(stages => stages.filter(s => s.kind === 'agent').length), [7, 6, 3]);
  assert.deepEqual(Object.values(WORKFLOW_STAGES).slice(0, 2).map(stages => stages.filter(s => s.kind === 'agent' && !s.optional).length), [5, 5]);
});

test('small change pins scope, inspection launches nothing, native checks execute, PR waits and actual merge completes', async t => {
  const f = await fixture(t); const started = await f.run();
  assert.equal(started.state, 'waiting'); assert.equal(started.exitCode, 2); assert.equal(started.stage, 'change');
  assert.match(started.runId, /^[\da-f-]{36}$/); assert.equal(f.native.length, 1);
  const inspect = await f.resume(started.runId); assert.equal(inspect.state, 'waiting'); assert.equal(f.native.length, 1);
  const progressed = await f.resume(started.runId, 'approve');
  assert.equal(progressed.state, 'waiting', progressed.message); assert.equal(progressed.stage, 'wait-merge');
  assert.deepEqual(f.native.map(v => v.input.stageId), ['scope', 'change', 'verify']);
  assert.ok(f.native.every(v => v.agent === 'claude' && v.cwd === f.cwd && v.context.startsWith('# PDD Alpha conversation guidance')));
  assert.ok(f.contexts.length >= 3); assert.ok(f.contexts.every(v => v.workflows === false));
  const saved = f.saved(started.runId); assert.equal(saved.completed.find(s => s.id === 'verify').handoff.checks[0].exitCode, 0);
  assert.equal(f.calls.filter(c => c.file === 'gh' && c.args[1] === 'create').length, 1);
  f.merged = true; const done = await f.resume(started.runId);
  assert.equal(done.state, 'completed', done.message); assert.equal(done.exitCode, 0); assert.equal(f.native.length, 3);
});

test('changed source invalidates a saved human advance and launches no replacement session', async t => {
  const f = await fixture(t); const first = await f.run(); writeFileSync(join(f.cwd, 'value.mjs'), 'export const value = 9;\n');
  const next = await f.resume(first.runId, 'approve'); assert.equal(next.state, 'failed'); assert.match(next.message, /HEAD or worktree changed/); assert.equal(f.native.length, 1);
});

test('whitespace changes in a space-bearing filename remain in the input fingerprint', async t => {
  const f = await fixture(t); writeFileSync(join(f.cwd, ' trailing '), 'a\n'); const first = await f.run();
  writeFileSync(join(f.cwd, ' trailing '), 'a\n\n'); const next = await f.resume(first.runId, 'approve');
  assert.equal(next.state, 'failed'); assert.equal(f.native.length, 1);
});

for (const [label, options] of [['missing', { missingHandoff: true }], ['stale', { staleHandoff: true }]]) {
  test(`native zero with ${label} handoff does not complete its stage or automatically relaunch`, async t => {
    const f = await fixture(t, options); const first = await f.run(); assert.equal(first.state, 'failed');
    assert.equal(f.saved(first.runId).index, 0); const again = await f.resume(first.runId, 'approve');
    assert.ok(['failed', 'recovery_required'].includes(again.state)); assert.equal(f.native.length, 1);
  });
}

test('native nonzero preserves uncertain intent and never relaunches on explicit resume', async t => {
  const f = await fixture(t, { nativeCode: 8 }); const first = await f.run();
  assert.equal(first.state, 'recovery_required'); assert.equal(first.exitCode, 1);
  assert.equal((await f.resume(first.runId, 'approve')).state, 'recovery_required'); assert.equal(f.native.length, 1);
});

test('independent real native test rejects a wrong implementation despite agent zero and valid files', async t => {
  const f = await fixture(t, { wrongBehavior: true }); const first = await f.run(); const failed = await f.resume(first.runId, 'approve');
  assert.equal(failed.state, 'failed', failed.message); assert.match(failed.message, /real native project check failed/);
  const checks = f.saved(first.runId).pending.checks; assert.equal(checks.length, 1); assert.notEqual(checks[0].exitCode, 0);
  assert.match(checks[0].stderr, /3 !== 2/);
  t.diagnostic(`Observed wrong-behavior control: ${JSON.stringify(checks[0].argv)} exited ${checks[0].exitCode}; real assertion: ${checks[0].stderr}`);
  assert.equal(f.calls.filter(c => c.file === 'gh' && c.args[1] === 'create').length, 0);
});

test('implementation cannot rewrite the accepted independent expectations', async t => {
  const f = await fixture(t, { changeAccepted: true }); const first = await f.run(); const failed = await f.resume(first.runId, 'approve');
  assert.equal(failed.state, 'failed'); assert.equal(f.saved(first.runId).index, 1); assert.equal(f.native.length, 2);
});

test('lost PR reply reconciles the identical original and never repeats push/create', async t => {
  const f = await fixture(t, { lostPrReply: true }); const first = await f.run(); const uncertain = await f.resume(first.runId, 'approve');
  assert.equal(uncertain.state, 'recovery_required', uncertain.message);
  const count = () => f.calls.filter(c => c.file === 'git' && c.args[0] === 'push' || c.file === 'gh' && c.args[1] === 'create').length;
  const before = count(); assert.equal(before, 2); const recovered = await f.resume(first.runId);
  assert.equal(recovered.state, 'waiting', recovered.message); assert.equal(count(), before); assert.equal(f.native.length, 3);
  assert.equal(f.saved(first.runId).completed.find(s => s.id === 'open-pr').pr.number, 23);
});

test('pre-auth push failure recovers only on explicit approve using the original unpublished PR intent', async t => {
  const f = await fixture(t, { preAuthPushFailure: true });
  const first = await f.run(); const failed = await f.resume(first.runId, 'approve');
  assert.equal(failed.state, 'recovery_required', failed.message);
  const saved = f.saved(first.runId), original = structuredClone(saved.pending.intent);
  const context = saved.context, expected = saved.expected, completed = saved.completed;
  const effects = () => f.calls.filter(c => c.file === 'git' && c.args[0] === 'push' || c.file === 'gh' && c.args[1] === 'create');
  assert.equal(effects().length, 1); f.authFixed = true;
  assert.equal((await f.resume(first.runId)).state, 'recovery_required');
  assert.equal(effects().length, 1, 'inspection after auth repair cannot publish');
  const recovered = await f.resume(first.runId, 'approve');
  assert.equal(recovered.state, 'waiting', recovered.message);
  const after = f.saved(first.runId), pr = after.completed.find(row => row.id === 'open-pr');
  assert.deepEqual(pr.intent, original); assert.equal(pr.pr.headSha, original.headSha);
  assert.equal(after.runId, first.runId); assert.equal(after.context, context);
  assert.deepEqual(after.expected, expected); assert.deepEqual(after.completed.slice(0, -1), completed);
  assert.equal(f.native.length, 3, 'no stage or attempt replay');
  assert.deepEqual(effects().map(c => c.file), ['git', 'git', 'gh']);
  assert.ok(f.calls.some(c => c.file === 'git' && c.args[0] === 'ls-remote' && c.args.includes('--exit-code')), 'recovery must freshly prove remote absence');
  assert.equal((await f.resume(first.runId, 'approve')).state, 'waiting');
  assert.equal(effects().length, 3, 'original open PR never republishes');
});

test('unpublished PR recovery refuses present remote head and unreadable PR or remote queries', async t => {
  for (const refusal of ['remoteHead', 'remoteUnreadable', 'prUnreadable']) {
    await t.test(refusal, async t => {
      const f = await fixture(t, { preAuthPushFailure: true }); const first = await f.run();
      assert.equal((await f.resume(first.runId, 'approve')).state, 'recovery_required');
      const original = structuredClone(f.saved(first.runId).pending.intent); f.authFixed = true;
      f[refusal] = refusal === 'remoteHead' ? original.headSha : true;
      const recovered = await f.resume(first.runId, 'approve');
      assert.equal(recovered.state, 'recovery_required', recovered.message);
      assert.deepEqual(f.saved(first.runId).pending.intent, original);
      assert.equal(f.calls.filter(c => c.file === 'git' && c.args[0] === 'push').length, 1);
      assert.equal(f.calls.filter(c => c.file === 'gh' && c.args[1] === 'create').length, 0);
      assert.equal(f.native.length, 3);
    });
  }
});

test('lost reply during unpublished PR recovery reconciles without another push or create', async t => {
  const f = await fixture(t, { preAuthPushFailure: true, lostPrReply: true }); const first = await f.run();
  assert.equal((await f.resume(first.runId, 'approve')).state, 'recovery_required'); f.authFixed = true;
  assert.equal((await f.resume(first.runId, 'approve')).state, 'recovery_required');
  assert.ok(f.pr, 'actual create happened before lost reply');
  const count = () => f.calls.filter(c => c.file === 'git' && c.args[0] === 'push' || c.file === 'gh' && c.args[1] === 'create').length;
  assert.equal(count(), 3);
  assert.equal((await f.resume(first.runId, 'approve')).state, 'waiting');
  assert.equal(count(), 3); assert.equal(f.native.length, 3);
});

test('an existing same issue/workflow run cannot be duplicated or switch its saved agent', async t => {
  const f = await fixture(t); const first = await f.run(); const second = await f.run('small-change', 'codex');
  assert.equal(second.runId, first.runId); assert.equal(second.state, 'waiting'); assert.equal(f.native.length, 1);
  assert.equal(f.saved(first.runId).agent, 'claude');
});

test('feature optional skips reach real human approval without inventing extra native stages', async t => {
  const f = await fixture(t); let state = await f.run('feature'); assert.equal(state.stage, 'visual');
  state = await f.resume(state.runId, 'skip'); assert.equal(state.stage, 'try', state.message);
  state = await f.resume(state.runId, 'skip'); assert.equal(state.stage, 'approve', state.message);
  assert.deepEqual(f.native.map(v => v.input.stageId), ['understand', 'prompt-story', 'check']);
  assert.equal((await f.resume(state.runId)).stage, 'approve');
  state = await f.resume(state.runId, 'approve'); assert.equal(state.stage, 'prompt-pr');
  state = await f.resume(state.runId, 'skip'); assert.equal(state.stage, 'code-merge', state.message);
  assert.deepEqual(f.native.map(v => v.input.stageId), ['understand', 'prompt-story', 'check', 'build', 'verify']);
});

test('current mandatory stage cannot be skipped', async t => {
  const f = await fixture(t); const first = await f.run(); const refused = await f.resume(first.runId, 'skip');
  assert.equal(refused.state, 'failed'); assert.match(refused.message, /Only an optional/); assert.equal(f.native.length, 1);
});

test('concurrent project command refuses before creating another native intent', async t => {
  let release; const gate = new Promise(resolve => { release = resolve; });
  const f = await fixture(t, { pauseNative: gate }); const running = f.run();
  while (!f.native.length) await new Promise(resolve => setTimeout(resolve, 5));
  const competing = await f.resume(f.native[0].input.runId, 'approve');
  assert.equal(competing.state, 'failed'); assert.match(competing.message, /Another workflow command/);
  release(); await running; assert.equal(f.native.length, 1); assert.equal(existsSync(join(f.gitDir, 'pdd/workflows/.lock')), false);
});

test('torn local journal refuses without a replacement operation', async t => {
  const f = await fixture(t); const first = await f.run(); const path = join(f.gitDir, 'pdd/workflows', first.runId, 'journal.jsonl');
  writeFileSync(path, readFileSync(path, 'utf8') + '{'); const failed = await f.resume(first.runId, 'approve');
  assert.equal(failed.state, 'failed'); assert.match(failed.message, /journal is incomplete/); assert.equal(f.native.length, 1);
});

test('a journal beyond the Node string limit resumes its latest optional stage without rewriting history', { timeout: 120000 }, async t => {
  const f = await fixture(t), recipe = join(f.sourceCwd, '.pdd/workflows/large-journal');
  mkdirSync(recipe, { recursive: true });
  writeFileSync(join(recipe, 'workflow.json'), JSON.stringify({ version: 1, name: 'large-journal', overview: 'WORKFLOW.md', stages: [
    { id: 'first', kind: 'agent', protocol: 'report', optional: true, file: 'first.md' },
    { id: 'second', kind: 'agent', protocol: 'report', optional: true, file: 'second.md' }
  ] }));
  for (const name of ['WORKFLOW.md', 'first.md', 'second.md']) writeFileSync(join(recipe, name), 'Report the current optional step.\n');
  const first = await f.run('large-journal'), saved = f.saved(first.runId);
  const journal = join(f.gitDir, 'pdd/workflows', first.runId, 'journal.jsonl');
  const context = saved.context, original = readFileSync(journal), expectedHash = createHash('sha256').update(original);
  let bytes = original.length, rows = saved.seq;
  const fd = openSync(journal, 'a');
  try {
    while (bytes <= bufferConstants.MAX_STRING_LENGTH + 64 * 1024 * 1024) {
      saved.seq = ++rows;
      const row = Buffer.from(JSON.stringify({ seq: rows, event: 'retained.snapshot', state: saved }) + '\n');
      writeSync(fd, row); expectedHash.update(row); bytes += row.length;
    }
  } finally { closeSync(fd); }
  assert.ok(bytes > bufferConstants.MAX_STRING_LENGTH);
  const recovered = await f.resume(first.runId, 'skip');
  assert.equal(recovered.state, 'waiting', recovered.message); assert.equal(recovered.runId, first.runId);
  assert.equal(recovered.stage, 'second'); assert.equal(f.native.length, 0, 'skipping never starts an agent');
  const input = openSync(journal, 'r'), actualHash = createHash('sha256'), chunk = Buffer.alloc(64 * 1024);
  let position = 0;
  try {
    while (position < bytes) {
      const count = readSync(input, chunk, 0, Math.min(chunk.length, bytes - position), position);
      assert.ok(count > 0); actualHash.update(chunk.subarray(0, count)); position += count;
    }
    const end = statSync(journal).size, tail = Buffer.alloc(Math.min(end, 512 * 1024));
    readSync(input, tail, 0, tail.length, end - tail.length);
    const last = JSON.parse(tail.toString('utf8').trimEnd().split('\n').at(-1));
    assert.ok(last.seq > rows); assert.equal(last.state.context, context);
    assert.equal(last.state.index, 1); assert.equal(last.state.completed[0].id, 'first');
    assert.equal(last.state.completed[0].skipped, true);
  } finally { closeSync(input); }
  assert.equal(actualHash.digest('hex'), expectedHash.digest('hex'), 'all original journal bytes remain unchanged');
  t.diagnostic(`Read ${bytes} bytes / ${rows} retained snapshots through normal same-run skip; original byte prefix unchanged.`);
});

test('streamed journal validates earlier history and refuses malformed or partial records before effects', async t => {
  for (const variant of ['sequence', 'run', 'malformed', 'partial']) {
    await t.test(variant, async t => {
      const f = await fixture(t); const first = await f.run();
      const path = join(f.gitDir, 'pdd/workflows', first.runId, 'journal.jsonl');
      const rows = readFileSync(path, 'utf8').trimEnd().split('\n').map(JSON.parse);
      if (variant === 'sequence') { rows[0].seq = 10; rows[0].state.seq = 10; }
      if (variant === 'run') rows[0].state.runId = randomUUID();
      let raw = rows.map(JSON.stringify).join('\n') + '\n';
      if (variant === 'malformed') raw = '{not json}\n' + raw;
      if (variant === 'partial') raw += '{"seq":';
      writeFileSync(path, raw);
      const before = f.native.length, response = await f.resume(first.runId, 'approve');
      assert.equal(response.state, 'failed', response.message); assert.equal(f.native.length, before);
      assert.equal(readFileSync(path, 'utf8'), raw, 'invalid history is never repaired or rewritten');
    });
  }
});

test('streamed journal handles split UTF8 records and trailing whitespace without losing saved identity', async t => {
  const f = await fixture(t); const first = await f.run();
  const path = join(f.gitDir, 'pdd/workflows', first.runId, 'journal.jsonl');
  const rows = readFileSync(path, 'utf8').trimEnd().split('\n').map(JSON.parse);
  rows[0].event = 'checkpoint 🎯 中文 '.repeat(20000);
  writeFileSync(path, rows.map(JSON.stringify).join('\n') + '\n \t\n');
  const before = f.native.length, response = await f.resume(first.runId);
  assert.equal(response.runId, first.runId); assert.equal(response.state, 'waiting', response.message);
  assert.equal(f.native.length, before);
});

test('separate prompt PR waits for real merge and refuses code work without its exact merged ancestry', async t => {
  const f = await fixture(t); let state = await f.run('feature');
  state = await f.resume(state.runId, 'skip'); state = await f.resume(state.runId, 'skip');
  state = await f.resume(state.runId, 'approve'); state = await f.resume(state.runId, 'approve');
  assert.equal(state.stage, 'prompt-merge', state.message);
  const before = f.native.length;
  f.merged = true;
  // A remote merged revision can be valid but not yet available in the local code branch.
  const actualHead = f.pr.headRefOid;
  f.pr.mergeCommit = { oid: 'a'.repeat(40) };
  const underlying = f.ports.execFile;
  f.ports.execFile = async (file, args, options) => {
    const answer = await underlying(file, args, options);
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'list') {
      const rows = JSON.parse(answer.stdout); rows.forEach(pr => { pr.mergeCommit = { oid: 'a'.repeat(40) }; });
      return { stdout: JSON.stringify(rows) };
    }
    return answer;
  };
  state = await f.resume(state.runId); assert.equal(state.stage, 'build'); assert.equal(state.state, 'waiting');
  state = await f.resume(state.runId, 'approve'); assert.equal(state.state, 'waiting');
  assert.match(state.message, /exact merged proposal revision/); assert.equal(f.native.length, before);
  assert.equal(f.saved(state.runId).completed.find(s => s.id === 'prompt-merge').pr.headSha, actualHead);
});

test('saved run identity cannot be substituted under a different journal directory', async t => {
  const f = await fixture(t); const first = await f.run();
  const path = join(f.gitDir, 'pdd/workflows', first.runId, 'journal.jsonl');
  const rows = readFileSync(path, 'utf8').trim().split('\n').map(JSON.parse);
  for (const row of rows) row.state.runId = '00000000-0000-4000-8000-000000000000';
  writeFileSync(path, rows.map(JSON.stringify).join('\n') + '\n');
  const refused = await f.resume(first.runId, 'approve'); assert.equal(refused.state, 'failed'); assert.equal(f.native.length, 1);
});


test('verify cannot replace the human accepted native argv with a success-only command', async t => {
  const f = await fixture(t, { changedPlan: true }); const first = await f.run();
  const refused = await f.resume(first.runId, 'approve'); assert.equal(refused.state, 'failed');
  assert.match(refused.message, /actual accepted native test plan/);
  assert.equal(f.calls.filter(c => c.file === process.execPath).length, 0);
});

test('work stages cannot use the report-only empty artifact exception', async t => {
  const f = await fixture(t, { emptyWork: true }); const first = await f.run();
  const refused = await f.resume(first.runId, 'approve'); assert.equal(refused.state, 'failed');
  assert.match(refused.message, /requires concrete project artifacts/); assert.equal(f.native.length, 2);
});


test('a zero-exit native check that mutates execution input cannot certify the changed implementation', async t => {
  const f = await fixture(t, { mutatingTest: true }); const first = await f.run();
  const refused = await f.resume(first.runId, 'approve'); assert.equal(refused.state, 'failed');
  assert.match(refused.message, /changed their execution input/);
  assert.equal(f.saved(first.runId).pending.checks[0].exitCode, 0);
});

test('a zero-exit check that rewrites the closed handoff is detected by independent reread', async t => {
  const f = await fixture(t, { mutatingHandoff: true }); const first = await f.run();
  const refused = await f.resume(first.runId, 'approve'); assert.equal(refused.state, 'failed');
  assert.match(refused.message, /exact workflow handoff changed/);
  assert.equal(f.saved(first.runId).pending.checks[0].exitCode, 0);
});


test('journal directory redirection refuses without creating or modifying a project target', async t => {
  const f = await fixture(t); const target = join(f.cwd, 'notes'); mkdirSync(target);
  writeFileSync(join(target, 'sentinel'), 'preserve me'); symlinkSync(target, join(f.gitDir, 'pdd'));
  const refused = await f.run(); assert.equal(refused.state, 'failed'); assert.equal(f.native.length, 0);
  assert.equal(readFileSync(join(target, 'sentinel'), 'utf8'), 'preserve me'); assert.equal(existsSync(join(target, 'workflows')), false);
});

test('a multiply linked saved journal refuses without writing through its project alias', async t => {
  const f = await fixture(t); const first = await f.run();
  const journal = join(f.gitDir, 'pdd/workflows', first.runId, 'journal.jsonl');
  const alias = join(f.cwd, 'journal-alias'); linkSync(journal, alias); const before = readFileSync(alias, 'utf8');
  const refused = await f.resume(first.runId, 'approve'); assert.equal(refused.state, 'failed'); assert.equal(f.native.length, 1);
  assert.match(refused.message, /single ordinary metadata file/);
  assert.equal(readFileSync(alias, 'utf8'), before); unlinkSync(alias);
});


test('an unknown resume ID creates no placeholder that could block the next genuine run', async t => {
  const f = await fixture(t); const unknown = '00000000-0000-4000-8000-000000000000';
  const refused = await f.resume(unknown); assert.equal(refused.state, 'recovery_required');
  assert.equal(existsSync(join(f.gitDir, 'pdd/workflows', unknown)), false);
  const actual = await f.run(); assert.equal(actual.state, 'waiting', actual.message); assert.equal(f.native.length, 1);
});

test('an uncertain build cannot consume the clean merged-base transition exception', async t => {
  const f = await fixture(t, { failStage: 'build' }); let state = await f.run('feature');
  state = await f.resume(state.runId, 'skip'); state = await f.resume(state.runId, 'skip');
  state = await f.resume(state.runId, 'approve'); state = await f.resume(state.runId, 'approve');
  f.merged = true; state = await f.resume(state.runId, 'approve');
  assert.equal(state.state, 'recovery_required'); assert.equal(state.stage, 'build');
  const prior = f.saved(state.runId).expected;
  writeFileSync(join(f.cwd, 'local.txt'), 'a new committed input'); await f.git('add', '.'); await f.git('commit', '-m', 'local change');
  const count = f.native.length; const refused = await f.resume(state.runId, 'approve'); assert.equal(refused.state, 'recovery_required');
  assert.deepEqual(f.saved(state.runId).expected, prior); assert.equal(f.native.length, count);
});


test('merge observation rejects a replacement PR with the same intent and a different saved number/URL', async t => {
  const f = await fixture(t); const started = await f.run(); const waiting = await f.resume(started.runId, 'approve');
  assert.equal(waiting.stage, 'wait-merge'); const before = f.saved(started.runId).index;
  f.pr.number = 24; f.pr.url = 'https://github.com/example/project/pull/24'; f.merged = true;
  const refused = await f.resume(started.runId); assert.equal(refused.state, 'recovery_required');
  assert.match(refused.message, /saved original PR/); assert.equal(f.saved(started.runId).index, before);
  assert.equal(f.saved(started.runId).completed.some(step => step.id === 'wait-merge'), false);
});

test('saved optional skip survives interruption before skipped completion and cannot publish on approve', async t => {
  const f = await fixture(t); let state = await f.run('feature');
  state = await f.resume(state.runId, 'skip'); state = await f.resume(state.runId, 'skip');
  state = await f.resume(state.runId, 'approve'); assert.equal(state.stage, 'prompt-pr');
  // Stop before the next native launch, then retain only the exact durable decision boundary.
  f.ports.runHerdrStage = async () => { throw Error('synthetic next-stage stop before native'); };
  await f.resume(state.runId, 'skip');
  const journal = join(f.gitDir, 'pdd/workflows', state.runId, 'journal.jsonl');
  const rows = readFileSync(journal, 'utf8').trim().split('\n').map(JSON.parse);
  const boundary = rows.findIndex(row => row.event === 'optional.decision' && row.state.optional?.['prompt-pr']?.decision === 'skip');
  assert.ok(boundary >= 0); writeFileSync(journal, rows.slice(0, boundary + 1).map(JSON.stringify).join('\n') + '\n');
  const before = f.native.length; await f.resume(state.runId, 'approve');
  assert.equal(f.calls.filter(call => call.file === 'git' && call.args[0] === 'push' || call.file === 'gh' && call.args[1] === 'create').length, 0);
  assert.equal(f.native.length, before);
  const saved = f.saved(state.runId);
  assert.equal(saved.completed.find(step => step.id === 'prompt-pr')?.skipped, true);
  assert.equal(saved.completed.find(step => step.id === 'prompt-merge')?.skipped, true);
  assert.equal(saved.definitions[saved.index].id, 'build');
});

test('editable renamed workflow snapshots full bytes BEFORE allocation and leaves original dirty checkout untouched', async t => {
  let captured;
  const f = await fixture(t, { onAllocate: input => { captured = input; } });
  projectWorkflow(f); writeFileSync(join(f.sourceCwd, 'user-notes'), 'preserve uncommitted notes');
  const before = (await exec('git', ['status', '--porcelain=v1', '--untracked-files=all'], { cwd: f.sourceCwd })).stdout;
  const state = await f.run('snapshot-check');
  assert.equal(state.state, 'waiting', state.message); assert.equal(state.stage, 'implement');
  assert.ok(captured.baseContext.includes('Preservation sets the boundary'));
  assert.ok(captured.definition.files.some(file => file.content.includes('OWNED_RECIPE_A__')));
  assert.notEqual(f.cwd, f.sourceCwd); assert.equal(f.native[0].cwd, f.cwd);
  assert.ok(f.native[0].context.includes(`Current assigned project: ${f.cwd}`));
  assert.ok(f.native[0].context.includes('OWNED_RECIPE_A__'));
  assert.equal(existsSync(join(f.sourceCwd, 'cases.json')), false);
  assert.equal((await exec('git', ['status', '--porcelain=v1', '--untracked-files=all'], { cwd: f.sourceCwd })).stdout, before);
  const progressed = await f.resume(state.runId, 'approve');
  assert.equal(progressed.stage, 'merged', progressed.message);
  assert.deepEqual(f.native.map(stage => stage.input.stageId), ['agree', 'implement', 'prove']);
  assert.equal(f.saved(state.runId).completed.find(stage => stage.id === 'prove').handoff.checks[0].exitCode, 0);
  assert.equal(f.native[1].backend.phase, 'closed', 'next stage donates only prior closed backend');
  assert.notEqual(f.native[1].attemptId, f.native[0].attemptId);
});
test('changed recipe source or missing whole override cannot replace saved instructions on resume', async t => {
  const f = await fixture(t); const directory = projectWorkflow(f); const first = await f.run('snapshot-check');
  writeFileSync(join(directory, 'work.md'), '# OWNED_RECIPE_B__\nDifferent instructions.');
  const refused = await f.resume(first.runId, 'approve');
  assert.equal(refused.state, 'failed'); assert.match(refused.message, /definition or Markdown source changed/);
  assert.equal(f.native.length, 1); assert.ok(f.saved(first.runId).context.includes('OWNED_RECIPE_A__'));
});
test('full canonical guide/skill context is bound separately from the recipe digest', async t => {
  const localPackage = mkdtempSync(join(tmpdir(), 'pdd-context-package-'));
  t.after(() => rmSync(localPackage, { recursive: true, force: true }));
  for (const directory of ['docs', 'skills', '.pdd']) cpSync(join(packageRoot, directory), join(localPackage, directory), { recursive: true });
  const f = await fixture(t, { packageRoot: localPackage }); const first = await f.run();
  const guide = join(localPackage, 'docs', 'prompting-guide.md');
  writeFileSync(guide, readFileSync(guide, 'utf8') + '\nChanged canonical guide after acceptance.\n');
  const refused = await f.resume(first.runId, 'approve');
  assert.equal(refused.state, 'failed'); assert.match(refused.message, /Canonical guide\/skill\/context changed/);
  assert.equal(f.native.length, 1);
});
test('same-name workflows in separate projects retain distinct accepted content and assigned contexts', async t => {
  const a = await fixture(t), c = await fixture(t); projectWorkflow(a); projectWorkflow(c, 'OWNED_RECIPE_C__');
  const sa = await a.run('snapshot-check'), sc = await c.run('snapshot-check');
  assert.equal(sa.state, 'waiting', sa.message); assert.equal(sc.state, 'waiting', sc.message);
  assert.ok(a.native[0].context.includes('OWNED_RECIPE_A__')); assert.ok(!a.native[0].context.includes('OWNED_RECIPE_C__'));
  assert.ok(c.native[0].context.includes('OWNED_RECIPE_C__')); assert.ok(!c.native[0].context.includes(a.sourceCwd));
  assert.notEqual(a.saved(sa.runId).definition.digest, c.saved(sc.runId).definition.digest);
});
for (const variant of ['torn', 'tampered', 'symlink', 'hardlink']) {
  test(`saved preallocation input ${variant} refuses without reconstructing current context`, async t => {
    const f = await fixture(t); const first = await f.run();
    const inputPath = join(f.sourceCwd, '.git/pdd/workflow-inputs', first.runId, 'input.jsonl');
    const original = readFileSync(inputPath, 'utf8');
    if (variant === 'torn') writeFileSync(inputPath, original.slice(0, -1));
    if (variant === 'tampered') { const input = JSON.parse(original); input.baseContext += ' unapproved'; writeFileSync(inputPath, JSON.stringify(input) + '\n'); }
    if (variant === 'symlink') {
      const target = join(f.sourceCwd, '.git', 'redirected-input'); writeFileSync(target, original);
      unlinkSync(inputPath); symlinkSync(target, inputPath);
    }
    if (variant === 'hardlink') linkSync(inputPath, join(f.sourceCwd, '.git', 'input-alias'));
    const refused = await f.resume(first.runId, 'approve');
    assert.equal(refused.state, 'failed'); assert.equal(f.native.length, 1);
  });
}
test('five distinct issues retain unresolved stages without a repository cap while same-issue and same-run exclusivity remain', async t => {
  const f = await fixture(t, { defaultWorktree: true });
  const originalExec = f.ports.execFile, starts = [], inspected = [];
  f.ports.execFile = async (file, args, options) => {
    const match = file === 'gh' && args[0] === 'api' && /^repos\/example\/project\/issues\/(\d+)$/.exec(args[1]);
    if (match) return { stdout: JSON.stringify({ number: Number(match[1]), html_url: `https://github.com/example/project/issues/${match[1]}`,
      title: 'Independent issue', body: 'Keep this issue stage independent.', state: 'OPEN', isPullRequest: false }) };
    return originalExec(file, args, options);
  };
  f.ports.runHerdrStage = async (input, ports) => {
    starts.push(input);
    const backend = { version: 1, runId: input.runId, stageId: input.stageId, attemptId: input.attemptId,
      agent: input.agent, cwd: input.cwd, phase: 'submitted', nativeSession: null,
      promptDigest: sha(`${input.context}\n\n# Current workflow stage\n${input.instructions}`), evidence: { readySeq: 1 } };
    await ports.checkpoint(backend);
    return { state: 'recovery_required', backend, evidence: backend.evidence, reason: 'Retained uncertain original stage; no resend.' };
  };
  f.ports.inspectHerdrStage = async ({ backend }) => {
    inspected.push(structuredClone(backend));
    return { state: 'recovery_required', backend, evidence: backend.evidence, reason: 'Retained original uncertainty.' };
  };
  const runs = [];
  for (let issue = 21; issue <= 25; issue++) {
    const outcome = await runWorkflow({ name: 'small-change', issue: String(issue), agent: 'codex', cwd: f.sourceCwd, packageRoot }, f.ports);
    assert.equal(outcome.state, 'recovery_required', outcome.message);
    assert.equal(outcome.stage, 'scope');
    runs.push(outcome);
  }
  assert.equal(starts.length, 5);
  assert.equal(new Set(starts.map(input => input.runId)).size, 5);
  assert.equal(new Set(starts.map(input => input.cwd)).size, 5);
  assert.equal(existsSync(join(f.sourceCwd, '.git/pdd/workflow-admission')), false, 'no repository admission state is created');
  const duplicate = await runWorkflow({ name: 'small-change', issue: '21', agent: 'codex', cwd: f.sourceCwd, packageRoot }, f.ports);
  assert.equal(duplicate.runId, runs[0].runId, duplicate.message);
  assert.equal(duplicate.state, 'recovery_required');
  for (const decision of [undefined, 'approve']) {
    const resumed = await resumeWorkflow({ runId: runs[0].runId, decision, cwd: f.sourceCwd, packageRoot }, f.ports);
    assert.equal(resumed.runId, runs[0].runId);
    assert.equal(resumed.state, 'recovery_required', resumed.message);
  }
  assert.equal(starts.length, 5, 'duplicate and uncertain original resume never create another stage');
  assert.equal(inspected.length, 2);
  assert.ok(inspected.every(backend => backend.attemptId === starts[0].attemptId));
});
test('historical admission claims remain byte-identical through normal stage acceptance and cleanup', async t => {
  const f = await fixture(t), root = join(f.sourceCwd, '.git/pdd/workflow-admission'); mkdirSync(root, { recursive: true });
  const claims = Array.from({ length: 4 }, (_, i) => ({ path: join(root, `slot-${i}.jsonl`),
    bytes: JSON.stringify({ runId: randomUUID(), attemptId: randomUUID(), cwd: `/retained/unknown-${i}` }) + '\n' }));
  for (const claim of claims) writeFileSync(claim.path, claim.bytes);
  const first = await f.run();
  assert.equal(first.state, 'waiting', first.message); assert.equal(first.stage, 'change');
  assert.equal(f.native.length, 1); assert.equal(f.closes, 1);
  assert.equal(f.saved(first.runId).accepted, undefined, 'a newly authored proposal still requires the next explicit advance');
  assert.equal(Object.hasOwn(f.saved(first.runId).pending ?? {}, 'admissionSlot'), false);
  for (const claim of claims) assert.equal(readFileSync(claim.path, 'utf8'), claim.bytes);
});
test('cleanup ambiguity retains accepted evidence and never retries close or prompt', async t => {
  const f = await fixture(t); let closeCalls = 0;
  f.ports.closeHerdrStage = async ({ backend }, ports) => {
    closeCalls++; await ports.checkpoint({ ...backend, phase: 'close_intent' });
    return { state: 'recovery_required', backend: { ...backend, phase: 'close_intent' }, reason: 'lost close reply' };
  };
  const first = await f.run(); assert.equal(first.state, 'recovery_required');
  const saved = f.saved(first.runId); assert.equal(saved.pending.kind, 'cleanup');
  assert.match(saved.pending.acceptance.evidenceDigest, /^[a-f0-9]{64}$/);
  const again = await f.resume(first.runId, 'approve'); assert.equal(again.state, 'recovery_required');
  assert.equal(closeCalls, 1); assert.equal(f.native.length, 1);
});
test('cross-process attach watcher stays open while the controller accepts the settled original', async t => {
  let release;
  const gate = new Promise(resolve => { release = resolve; });
  const f = await fixture(t, { pauseNative: gate }); const running = f.run();
  while (!f.native.length) await new Promise(resolve => setTimeout(resolve, 5));
  const runId = f.native[0].input.runId, assignment = f.saved(runId).assignment;
  const script = `import {attachWorkflow} from ${JSON.stringify(new URL('../src/workflow-runner.mjs', import.meta.url).href)};
    import {loadGuidance} from ${JSON.stringify(new URL('../src/guidance.mjs', import.meta.url).href)};
    const result=await attachWorkflow({runId:${JSON.stringify(runId)},cwd:${JSON.stringify(f.sourceCwd)},packageRoot:${JSON.stringify(packageRoot)}}, {
      loadGuidance,lookupIssueWorktree:async()=>({state:'ready',assignment:${JSON.stringify(assignment)}}), allocateIssueWorktree:async()=>{throw Error('no allocation')},
      attachHerdrStage:async()=>{process.stdout.write('ATTACHED\\n');await new Promise(resolve=>process.stdin.once('data',resolve));return 0;}});
    process.stdout.write(JSON.stringify(result)+'\\n');`;
  const child = spawn(process.execPath, ['--input-type=module', '-e', script], { cwd: f.sourceCwd, stdio: ['pipe','pipe','pipe'] });
  let output = '', errors = ''; child.stdout.on('data', value => { output += value; }); child.stderr.on('data', value => { errors += value; });
  const closed = new Promise(resolve => child.once('close', code => resolve(code)));
  try {
    for (let i = 0; i < 200 && !output.includes('ATTACHED'); i++) await new Promise(resolve => setTimeout(resolve, 10));
    assert.ok(output.includes('ATTACHED'), errors + output);
    release(); const paused = await running; assert.equal(paused.state, 'waiting', paused.message);
    assert.equal(f.closes, 1); assert.equal(f.saved(runId).pending, null);
    assert.equal(output.includes('attached'),false,'viewer is still open when acceptance finishes');
  } finally { release(); child.stdin.end('detach\n'); }
  assert.equal(await closed, 0, errors);
  const inspected = await f.resume(runId);
  assert.equal(inspected.state, 'waiting', inspected.message);
  assert.equal(f.native.length, 1); assert.equal(f.closes, 1);
});

test('fresh-process resume refuses edited source before any replacement stage delivery', async t => {
  const f = await fixture(t); const directory = projectWorkflow(f); const first = await f.run('snapshot-check');
  const assignment = f.saved(first.runId).assignment;
  writeFileSync(join(directory, 'work.md'), '# OWNED_RECIPE_B__\nChanged after accepted A.\n');
  const script = `import {resumeWorkflow} from ${JSON.stringify(new URL('../src/workflow-runner.mjs', import.meta.url).href)};
    import {loadGuidance} from ${JSON.stringify(new URL('../src/guidance.mjs', import.meta.url).href)};
    import {execFile as callback} from 'node:child_process';import {promisify} from 'node:util';const exec=promisify(callback);
    const result=await resumeWorkflow(${JSON.stringify({runId:first.runId,cwd:f.sourceCwd,packageRoot,decision:'approve'})},{loadGuidance,
      lookupIssueWorktree:async()=>({state:'ready',assignment:${JSON.stringify(assignment)}}),allocateIssueWorktree:async()=>{throw Error('no allocation')},
      runHerdrStage:async()=>{throw Error('UNEXPECTED_STAGE_DELIVERY');},
      execFile:async(file,args,options)=>file==='gh'?{stdout:JSON.stringify(args[0]==='repo'?{nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'}:{number:17,html_url:${JSON.stringify(issueUrl)},title:'Use two',body:'Two',isPullRequest:false})}:exec(file,args,options)});
    process.stdout.write(JSON.stringify(result));`;
  const child = await exec(process.execPath, ['--input-type=module', '-e', script], { cwd: f.sourceCwd });
  const refused = JSON.parse(child.stdout);
  assert.equal(refused.state, 'failed'); assert.match(refused.message, /definition or Markdown source changed/);
  assert.equal(f.native.length, 1); assert.equal(f.saved(first.runId).index, 1);
});

async function joinedHerdr(t, {dirty=false} = {}) {
  const f = await fixture(t, { defaultWorktree: true }); const foreground = f.ports.launchNativeSession;
  const sessions = new Map(), calls = [];
  function transport(base) {
    return {...base, layoutDirectory:join(f.sourceCwd,'.git','layout-test'), quietMs:0, pollMs: 1, startupMs: 100, activityMs: 100, timeoutMs: 1000,
      sleep: async () => {},
      spawnServer: async (session, cwd) => { assert.equal(cwd,f.cwd); sessions.set(session,{seed:'seed',active:null,repo:false,run:false}); calls.push('server'); },
      execFile: async (file, argv, options) => {
        assert.equal(file,'herdr'); assert.equal(options.cwd,f.cwd); assert.equal(options.shell,false);
        const session=argv[1], a=argv.slice(2), server=sessions.get(session);
        const reply=value=>({stdout:JSON.stringify(value),stderr:''});
        if(a[0]==='status') return reply({running:Boolean(server),session,compatible:true,endpoint_compatible:true,protocol:22,version:'0.9.1',socket:`/owned/${session}`});
        if(a[0]==='workspace'&&a[1]==='list') return reply({id:'cli:workspace:list',result:{type:'workspace_list',workspaces:[{workspace_id:'seed'},...(server.repo?[{workspace_id:'repo',label:'project',worktree:{checkout_path:f.sourceCwd,repo_key:join(f.sourceCwd,'.git')}}]:[]),...(server.run?[{workspace_id:'run',label:'#17 small-change',worktree:{checkout_path:f.cwd,repo_key:join(f.sourceCwd,'.git'),is_linked_worktree:true}}]:[])]}});
        if(a[0]==='workspace'&&a[1]==='create'){server.repo=true;return reply({id:'cli:workspace:create',result:{workspace:{workspace_id:'repo'}}});}
        if(a[0]==='worktree'&&a[1]==='open'){server.run=true;return reply({id:'cli:worktree:open',result:{workspace:{workspace_id:'run'},tab:{tab_id:'run:root'},root_pane:{pane_id:'run:root-pane',terminal_id:'root-terminal'}}});}
        if(a[0]==='pane'&&a[1]==='list')return reply({id:'cli:pane:list',result:{type:'pane_list',panes:[{workspace_id:'run',tab_id:'run:root',pane_id:'run:root-pane',terminal_id:'root-terminal',cwd:f.cwd}]}});
        if(a[0]==='tab'&&a[1]==='list')return reply({id:'cli:tab:list',result:{type:'tab_list',tabs:[{tab_id:'run:root'},...(server.active?[{tab_id:server.active.tab_id}]:[])]}});
        if(a[0]==='pane'&&a[1]==='send-text')return reply({id:'cli:pane:send-text',result:{type:'ok'}});
        if(a[0]==='tab'&&a[1]==='create') {
          assert.equal(server.active,null);const id=`stage-${calls.filter(x=>x==='create').length}`;calls.push('create');
          server.active={workspace_id:'run',tab_id:`${id}:tab`,pane_id:`${id}:pane`,terminal_id:`${id}:terminal`,cwd:f.cwd,agent_status:'idle',state_change_seq:10,interactive_ready:true,launch_pending:false};
          return reply({id:'cli:tab:create',result:{workspace:{workspace_id:'run'},tab:{tab_id:server.active.tab_id},root_pane:{pane_id:server.active.pane_id,terminal_id:server.active.terminal_id}}});
        }
        const native=server.active;
        if(a[0]==='agent'&&a[1]==='start') {calls.push('start');native.name=a[2];native.agent=a[a.indexOf('--kind')+1];if(calls.filter(x=>x==='start').length===1){native.agent_status='blocked';native.interactive_ready=false;}return reply({result:{agent:native}});}
        if(a[0]==='agent'&&a[1]==='get') return reply({result:{agent:native}});
        if(a[0]==='agent'&&a[1]==='prompt') {
          calls.push('prompt');assert.equal(native.state_change_seq,10);
          const marker='\n\n# Current workflow stage\n', index=a[3].lastIndexOf(marker);
          await foreground({agent:native.agent,cwd:f.cwd,context:a[3].slice(0,index),request:a[3].slice(index+marker.length)});
          if(dirty && JSON.parse(a[3].split('PDD_STAGE_INPUT_JSON\n')[1].split('\nPDD_STAGE_INPUT_END')[0]).stageId==='verify')writeFileSync(join(f.cwd,'untracked-scope-case.md'),'Independent scope case retained outside commits.\n');
          native.agent_status='working';native.interactive_ready=false;native.state_change_seq=11;
          const acknowledgement=structuredClone(native);
          queueMicrotask(()=>{native.agent_status='done';native.interactive_ready=true;native.state_change_seq=12;});
          return reply({result:{agent:acknowledgement}});
        }
        if(a[0]==='workspace'&&a[1]==='close'){assert.equal(a[2],'run');assert.equal(server.active,null);server.run=false;calls.push('run-close');return reply({id:'cli:workspace:close',result:{type:'ok'}});}
        if(a[0]==='tab'&&a[1]==='close') {calls.push('close');assert.equal(a[2],native.tab_id);server.active=null;return reply({id:'cli:tab:close',result:{type:'ok'}});}
        assert.fail('Unexpected stand-in Herdr operation '+JSON.stringify(a));
      }};
  }
  f.ports.runHerdrStage=(input,ports)=>runHerdrStage(input,transport(ports));
  f.ports.inspectHerdrStage=(input,ports)=>inspectHerdrStage(input,transport(ports));
  f.ports.closeHerdrStage=(input,ports)=>closeHerdrStage(input,transport(ports));
  f.ports.closeHerdrRun=(input,ports)=>closeHerdrRun(input,transport(ports));
  const first=await f.run();assert.equal(first.state,'waiting',first.message);assert.equal(first.stage,'scope');
  const original=f.saved(first.runId).pending;assert.equal(original.backend.phase,'start_intent');
  assert.equal(calls.filter(x=>x==='prompt').length,0);assert.equal(calls.filter(x=>x==='start').length,1);
  const inspection=await f.resume(first.runId);assert.equal(inspection.state,'waiting',inspection.message);
  assert.equal(calls.filter(x=>x==='prompt').length,0);assert.equal(calls.filter(x=>x==='start').length,1);
  const live=[...sessions.values()][0].active;live.agent_status='idle';live.interactive_ready=true;
  const continued=await f.resume(first.runId,'approve');assert.equal(continued.stage,'change',continued.message);
  const accepted=f.saved(first.runId).completed[0];
  assert.equal(accepted.backend.attemptId,original.attemptId);assert.equal(accepted.backend.terminalId,original.backend.terminalId);
  assert.equal(calls.filter(x=>x==='start').length,1);assert.equal(calls.filter(x=>x==='create').length,1);
  assert.equal(calls.filter(x=>x==='prompt').length,1);
  const progressed=await f.resume(first.runId,'approve');
  if(dirty) {
    assert.equal(progressed.state,'failed');assert.match(progressed.message,/workflow_github_worktree_dirty/);
    assert.equal([...sessions.values()][0].run,false,'failed publication must close the run workspace');
    assert.equal([...sessions.values()][0].repo,true);assert.equal(existsSync(f.cwd),true);
    assert.equal(f.saved(first.runId).herdrLayoutClosed,true);return;
  }
  assert.equal(progressed.stage,'wait-merge',progressed.message);
  assert.equal(calls.filter(x=>x==='server').length,1);assert.equal(calls.filter(x=>x==='prompt').length,3);assert.equal(calls.filter(x=>x==='close').length,3);
  const saved=f.saved(first.runId), stages=saved.completed.filter(stage=>stage.backend);
  assert.equal(new Set(stages.map(stage=>stage.backend.terminalId)).size,3);
  for(const stage of stages) {assert.equal(stage.backend.phase,'closed');assert.match(stage.acceptance.evidenceDigest,/^[a-f0-9]{64}$/);}
  assert.equal([...sessions.values()][0].active,null);
  assert.equal([...sessions.values()][0].run,true,'merge wait retains run workspace');
  assert.equal(calls.includes('run-close'),false);
  f.merged=true;
  const done=await f.resume(first.runId);assert.equal(done.state,'completed',done.message);
  assert.equal([...sessions.values()][0].run,false);assert.equal([...sessions.values()][0].repo,true);
  assert.equal(calls.filter(x=>x==='run-close').length,1);
  assert.equal(f.saved(first.runId).herdrLayoutClosed,true);
  assert.equal(existsSync(f.cwd),true,'run layout closure does not remove Git worktree');
  assert.equal((await f.resume(first.runId)).state,'completed');assert.equal(calls.filter(x=>x==='run-close').length,1);
}
test('main joins frozen native adapter through same-agent first dispatch, accepted cleanup and next-stage server donation', t=>joinedHerdr(t));
test('terminal publication exception closes the run workspace while preserving untracked Git artifacts',t=>joinedHerdr(t,{dirty:true}));

test('resume owns the controller lock before reading the journal and cannot advance a stale optional snapshot', async t => {
  const f=await fixture(t), recipe=join(f.sourceCwd,'.pdd/workflows/journal-race');mkdirSync(recipe,{recursive:true});
  writeFileSync(join(recipe,'workflow.json'),JSON.stringify({version:1,name:'journal-race',overview:'WORKFLOW.md',stages:[
    {id:'first',kind:'agent',protocol:'report',optional:true,file:'first.md'},
    {id:'second',kind:'agent',protocol:'report',optional:true,file:'second.md'}]}));
  for(const name of ['WORKFLOW.md','first.md','second.md'])writeFileSync(join(recipe,name),'Report only the current step.\n');
  const first=await f.run('journal-race');assert.equal(first.stage,'first');assert.equal(f.native.length,0);
  const saved=f.saved(first.runId), journal=join(f.gitDir,'pdd/workflows',first.runId,'journal.jsonl');
  const releasePath=join(f.sourceCwd,'.git','release-journal-reader');
  const script=`import fs from 'node:fs';import {syncBuiltinESMExports} from 'node:module';
    const open=fs.openSync;let intercepted=false;
    fs.openSync=function(path,...args){const value=open.call(this,path,...args);
      if(String(path)===${JSON.stringify(journal)}&&!intercepted){intercepted=true;process.stdout.write('JOURNAL_READ\\n');
        const wait=new Int32Array(new SharedArrayBuffer(4));const end=Date.now()+15000;
        while(!fs.existsSync(${JSON.stringify(releasePath)})){if(Date.now()>end)throw Error('Test reader release timed out');Atomics.wait(wait,0,0,5);}}
      return value;};syncBuiltinESMExports();
    const {resumeWorkflow}=await import(${JSON.stringify(new URL('../src/workflow-runner.mjs',import.meta.url).href)});
    const {loadGuidance}=await import(${JSON.stringify(new URL('../src/guidance.mjs',import.meta.url).href)});
    const {execFile:callback}=await import('node:child_process');const {promisify}=await import('node:util');const exec=promisify(callback);
    const result=await resumeWorkflow(${JSON.stringify({runId:first.runId,cwd:f.sourceCwd,packageRoot,decision:'approve'})},{loadGuidance,
      allocateIssueWorktree:async()=>{throw Error('No allocation');},lookupIssueWorktree:async()=>({state:'ready',assignment:${JSON.stringify(saved.assignment)}}),
      execFile:async(file,args,options)=>file==='gh'?{stdout:JSON.stringify(args[0]==='repo'?{nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'}:{number:17,html_url:${JSON.stringify(issueUrl)},title:'Report',body:'Report only',isPullRequest:false})}:exec(file,args,options),
      runHerdrStage:async(input)=>{const data=JSON.parse(input.instructions.split('PDD_STAGE_INPUT_JSON\\n')[1].split('\\nPDD_STAGE_INPUT_END')[0]);
        fs.writeFileSync(data.handoffPath,JSON.stringify({version:1,runId:input.runId,stageId:input.stageId,issueUrl:${JSON.stringify(issueUrl)},inputRevision:data.inputRevision,summary:'Substantive report for this stage only.',files:[]}));
        const {createHash}=await import('node:crypto');const backend={version:1,runId:input.runId,stageId:input.stageId,attemptId:input.attemptId,agent:input.agent,cwd:input.cwd,phase:'candidate',terminalId:'test-terminal',promptDigest:createHash('sha256').update(input.context+'\\n\\n# Current workflow stage\\n'+input.instructions).digest('hex'),evidence:{readySeq:1,workingSeq:2,settledSeq:3}};
        await input.checkpoint(backend);return{state:'settled',backend,evidence:backend.evidence};},
      inspectHerdrStage:async({backend})=>({state:'settled',backend,evidence:backend.evidence}),
      closeHerdrStage:async({backend},ports)=>{const closed={...backend,phase:'closed'};await ports.checkpoint(closed);return{state:'closed',backend:closed};}});
    process.stdout.write(JSON.stringify(result)+'\\n');`;
  const child=spawn(process.execPath,['--input-type=module','-e',script],{cwd:f.sourceCwd,stdio:['ignore','pipe','pipe']});
  let output='',errors='';child.stdout.on('data',value=>{output+=value;});child.stderr.on('data',value=>{errors+=value;});
  const closed=new Promise(resolve=>child.once('close',resolve));let competing;
  try{
    for(let i=0;i<400&&!output.includes('JOURNAL_READ');i++)await new Promise(resolve=>setTimeout(resolve,10));
    assert.ok(output.includes('JOURNAL_READ'),output+errors);
    competing=await f.resume(first.runId,'skip');
  }finally{writeFileSync(releasePath,'release');}
  assert.equal(await closed,0,output+errors);
  const rows=readFileSync(journal,'utf8').trim().split('\n').map(JSON.parse);
  t.diagnostic(`Competing controller: ${competing?.state}; duplicate sequences: ${new Set(rows.map(row=>row.seq)).size!==rows.length}`);
  assert.equal(competing.state,'failed',competing.message);assert.match(competing.message,/Another workflow command/);
  assert.equal(new Set(rows.map(row=>row.seq)).size,rows.length);
  assert.equal(rows.at(-1).state.index,1);assert.equal(rows.at(-1).state.completed[0].id,'first');
  assert.equal(rows.at(-1).state.completed[0].skipped,undefined);
});

test('verified publication refuses source changed by a later report despite earlier successful real checks', async t => {
  const f=await fixture(t), directory=projectWorkflow(f), path=join(directory,'workflow.json');
  const definition=JSON.parse(readFileSync(path,'utf8'));
  definition.stages.splice(3,0,{id:'later-report',kind:'agent',protocol:'report',requiredRoles:['implementation'],file:'later.md'});
  writeFileSync(path,JSON.stringify(definition));writeFileSync(join(directory,'later.md'),'Report current source changes.\n');
  const run=f.ports.runHerdrStage;
  f.ports.runHerdrStage=async(...args)=>{
    const result=await run(...args);
    if(args[0].stageId==='later-report'){
      writeFileSync(join(f.cwd,'value.mjs'),'export const value = 3;\n');await f.git('add','value.mjs');await f.git('commit','-m','late source change');
      const input=f.native.at(-1).input, handoff=JSON.parse(readFileSync(input.handoffPath,'utf8'));
      handoff.files=[{path:'value.mjs',sha256:sha(readFileSync(join(f.cwd,'value.mjs'))),role:'implementation'}];
      writeFileSync(input.handoffPath,JSON.stringify(handoff));
    }
    return result;
  };
  const first=await f.run('snapshot-check'), refused=await f.resume(first.runId,'approve');
  assert.equal(refused.state,'failed',refused.message);assert.match(refused.message,/checks for this exact current source/);
  const verified=f.saved(first.runId).completed.find(stage=>stage.id==='prove');assert.equal(verified.handoff.checks[0].exitCode,0);
  assert.notEqual(verified.verification.output.head,await f.git('rev-parse','HEAD'));
  assert.equal(f.calls.filter(call=>call.file==='git'&&call.args[0]==='push'||call.file==='gh'&&call.args[1]==='create').length,0);
});

test('default allocator and lookup preserve the original issue run across providers and complete real assigned checks', async t => {
  const f=await fixture(t,{defaultWorktree:true});
  assert.equal('allocateIssueWorktree' in f.ports,false);assert.equal('lookupIssueWorktree' in f.ports,false);
  const first=await f.run();assert.equal(first.state,'waiting',first.message);assert.equal(first.stage,'change');
  const original=f.saved(first.runId).assignment;
  const conflict=await f.run('small-change','codex');
  assert.equal(conflict.runId,first.runId,conflict.message);assert.equal(conflict.state,'waiting',conflict.message);
  assert.equal(f.native.length,1);assert.equal(f.saved(first.runId).agent,'claude');
  const progressed=await f.resume(first.runId,'approve');assert.equal(progressed.stage,'wait-merge',progressed.message);
  assert.deepEqual(f.saved(first.runId).assignment,original);
  assert.equal(f.saved(first.runId).completed.find(stage=>stage.id==='verify').handoff.checks[0].exitCode,0);
  assert.equal((await exec('git',['status','--porcelain'],{cwd:f.sourceCwd})).stdout,'');
});


test('default conflict with a live original controller reports its original identity without reading stale progress or launching twice', async t => {
  let release;const gate=new Promise(resolve=>{release=resolve;});const f=await fixture(t,{defaultWorktree:true,pauseNative:gate});
  const running=f.run();let competing;
  try{
    while(!f.native.length)await new Promise(resolve=>setTimeout(resolve,5));
    const runId=f.native[0].input.runId;
    competing=await f.run('small-change','codex');
    assert.equal(competing.runId,runId,competing.message);assert.equal(competing.state,'failed');
    assert.match(competing.message,/Another workflow command/);assert.equal(f.native.length,1);
    assert.equal(f.saved(runId).pending.kind,'agent');
  }finally{release();await running;}
  assert.equal(f.calls.filter(call=>call.file==='git'&&call.args[0]==='worktree'&&call.args[1]==='add').length,1);
});

test('default conflict refuses an aliased issue claim before accepting it as an assignment or replaying allocation', async t => {
  const f=await fixture(t,{defaultWorktree:true});const first=await f.run();
  const root=join(f.sourceCwd,'.git/pdd/worktree-assignments'),claim=join(root,'issues/17.json');
  const record=join(root,'runs',first.runId+'.json'),before=readFileSync(record,'utf8');
  unlinkSync(claim);symlinkSync(record,claim);
  const refused=await f.run('small-change','codex');assert.equal(refused.state,'failed');
  assert.match(refused.message,/issue claim is not an ordinary owned metadata record/);
  assert.equal(readFileSync(record,'utf8'),before);assert.equal(f.native.length,1);
  assert.equal(f.calls.filter(call=>call.file==='git'&&call.args[0]==='worktree'&&call.args[1]==='add').length,1);
});

async function unsentFirstDispatch(t, phase) {
  const f = await fixture(t), run = f.ports.runHerdrStage, calls = [], observations = [];
  let original;
  f.setupBlocked = true;
  f.ports.runHerdrStage = async (value, ports) => {
    const { checkpoint, ...request } = value; calls.push(structuredClone(request));
    if (!original) {
      original = { version: 1, runId: value.runId, stageId: value.stageId, attemptId: value.attemptId,
        agent: value.agent, cwd: value.cwd, phase, promptDigest: sha(`${value.context}\n\n# Current workflow stage\n${value.instructions}`),
        session: 'owned-session', server: { session: 'owned-session', socket: '/captured/owned.sock', protocol: 22, version: '0.9.1' },
        agentName: 'same-original-agent', workspaceId: 'same-workspace', tabId: 'same-tab', paneId: 'same-pane',
        terminalId: `terminal-${value.attemptId}`, nativeSession: null, evidence: phase === 'ready' ? { readySeq: 1 } : {} };
      await checkpoint(original);
      return { state: 'blocked', backend: original, evidence: original.evidence, reason: 'Finish native setup with pdd workflow attach RUN_ID' };
    }
    assert.deepEqual(request, { ...calls[0], backend: original }, 'continue only original exact request/agent identity');
    if (f.setupBlocked) return { state: 'blocked', backend: original, evidence: original.evidence, reason: 'Finish native setup with pdd workflow attach RUN_ID' };
    const outcome = await run({ ...value, checkpoint: backend => checkpoint({ ...original, ...backend }) }, ports);
    return { ...outcome, backend: { ...original, ...outcome.backend } };
  };
  const inspect = f.ports.inspectHerdrStage;
  f.ports.inspectHerdrStage = async (value, ports) => {
    observations.push(structuredClone(value));
    return value.backend.phase === 'candidate' ? inspect(value, ports)
      : { state: 'recovery_required', backend: value.backend, evidence: value.backend.evidence, reason: 'no_observed_prompt_activity' };
  };
  const first = await f.run(); assert.equal(first.state, 'waiting', first.message); assert.equal(f.native.length, 0);
  const journal = join(f.gitDir, 'pdd/workflows', first.runId, 'journal.jsonl');
  return { f, first, calls, observations, rewrite(change) {
    const rows = readFileSync(journal, 'utf8').trim().split('\n').map(JSON.parse);
    change(rows.at(-1).state); writeFileSync(journal, rows.map(JSON.stringify).join('\n') + '\n');
  } };
}

for (const phase of ['start_intent', 'ready']) for (const legacy of [true, false])
  test(`same-agent first dispatch resumes ${phase} using exact ${legacy ? 'legacy digest-bound' : 'saved'} request after normal setup`, async t => {
    const { f, first, calls, rewrite } = await unsentFirstDispatch(t, phase);
    if (legacy) rewrite(state => { delete state.pending.instructions; });
    const original = f.saved(first.runId), attempt = original.pending.attemptId;
    const inspected = await f.resume(first.runId); assert.equal(inspected.state, 'recovery_required'); assert.equal(calls.length, 1);
    const blocked = await f.resume(first.runId, 'approve');
    assert.equal(blocked.state, 'waiting'); assert.match(blocked.message, /workflow attach/); assert.equal(calls.length, 2); assert.equal(f.native.length, 0);
    f.setupBlocked = false;
    const continued = await f.resume(first.runId, 'approve');
    assert.equal(continued.state, 'waiting', continued.message); assert.equal(continued.stage, 'change');
    assert.equal(continued.runId, first.runId); assert.equal(calls.length, 3); assert.equal(f.native.length, 1);
    assert.equal(f.native[0].attemptId, attempt); assert.equal(f.native[0].context, calls[0].context);
    assert.equal(f.native[0].instructions, calls[0].instructions);
    assert.deepEqual(f.saved(first.runId).assignment, original.assignment);
    assert.equal(f.saved(first.runId).completed[0].backend.agentName, original.pending.backend.agentName);
  });

test('first-dispatch selector leaves every delivery or later phase inspection-only with no native call', async t => {
  const { f, first, calls, rewrite } = await unsentFirstDispatch(t, 'start_intent');
  f.ports.inspectHerdrStage = async ({ backend }) => ({ state: 'recovery_required', backend, evidence: backend.evidence, reason: 'original inspection only' });
  for (const phase of ['server_intent', 'workspace_intent', 'prompt_intent', 'submitted', 'candidate', 'close_intent', 'closed', 'unknown']) {
    rewrite(state => { state.pending.backend.phase = phase; });
    const seen = await f.resume(first.runId, 'approve'); assert.equal(seen.state, 'recovery_required', `${phase}: ${seen.message}`);
    assert.equal(calls.length, 1); assert.equal(f.native.length, 0);
  }
});

test('first-dispatch continuation refuses changed original request or worktree before native call', async t => {
  const { f, first, calls, rewrite } = await unsentFirstDispatch(t, 'start_intent');
  const instructions = f.saved(first.runId).pending.instructions;
  rewrite(state => { state.pending.instructions += '\nChanged prompt'; });
  const tampered = await f.resume(first.runId, 'approve');
  assert.equal(tampered.state, 'failed'); assert.match(tampered.message, /request bytes cannot be proved/); assert.equal(calls.length, 1);
  rewrite(state => { state.pending.instructions = instructions; });
  writeFileSync(join(f.cwd, 'value.mjs'), 'export const value = 9;\n');
  const changed = await f.resume(first.runId, 'approve');
  assert.equal(changed.state, 'failed'); assert.match(changed.message, /HEAD or worktree changed/); assert.equal(calls.length, 1);
});

test('live observations use saved identities, follow durable stage/test/PR records and cannot mutate the run', async t => {
  const f = await fixture(t), events = [], out = { text: '', write(value) { this.text += value; } };
  f.ports.stdout = out;
  f.ports.onProgress = event => {
    events.push(structuredClone(event));
    if (event.event === 'run.started') assert.equal(f.saved(event.runId).runId, event.runId);
    event.runId = 'mutated';
    if (event.stage) event.stage.id = 'mutated';
  };
  const start = await f.run();
  assert.equal(start.state, 'waiting');
  const gate = events.at(-1);
  assert.equal(gate.title, 'Use value two');assert.equal(gate.agent, 'claude');
  assert.equal(gate.state, 'waiting');assert.equal(gate.stage.id, 'change');assert.equal(gate.backend,null,'closed prior workspace is not current');
  assert.ok(gate.files.some(path => path.endsWith('cases.json')));
  assert.match(gate.summary, /Completed current scope/);
  assert.ok(events.some(e => e.event === 'agent.intent' && e.stage.id === 'scope'));
  assert.ok(events.some(e => e.event === 'agent.completed' && e.ended === 'scope'));
  const result = await f.resume(start.runId, 'approve');
  assert.equal(result.stage, 'wait-merge');
  assert.ok(events.some(e => e.event === 'test.intent'));
  assert.ok(events.some(e => e.event === 'test.completed'));
  assert.deepEqual(events.at(-1).prs, ['https://github.com/example/project/pull/23']);
  assert.ok(events.every(e => e.runId === start.runId));
  assert.doesNotMatch(out.text, /moved on/, 'the controller terminal already shows "<stage> done"');
  f.ports.onProgress = () => { throw Error('broken display'); };
  f.merged = true;
  assert.equal((await f.resume(start.runId)).state, 'completed');
});

test('feature approval progress retains proposal artifacts after later report-only stages', async t => {
  const f = await fixture(t), events = [];
  f.ports.onProgress = event => events.push(event);
  let result = await f.run('feature');
  while (result.state === 'waiting' && result.stage !== 'approve') {
    result = await f.resume(result.runId, 'skip');
  }
  assert.equal(result.stage, 'approve', result.message);
  const gate = events.at(-1);
  for (const name of ['module.prompt.md', 'STORY.md', 'cases.json']) assert.ok(gate.files.some(path => path.endsWith(name)), name);
  assert.ok(gate.files.some(path => /prompt-story-.*\.json$/.test(path)));
});

test('real runner passes repository layout binding to the production stage adapter',async t=>{
 const f=await fixture(t,{defaultWorktree:true});let observed;
 f.ports.runHerdrStage=async(input,ports)=>{
   observed=input;
   return runHerdrStage(input,{...ports,layoutDirectory:join(f.sourceCwd,'.layout'),execFile:async()=>{throw Object.assign(Error('stop before native launch'),{code:'STOP'});}});
 };
 const outcome=await f.run();
 assert.equal(outcome.state,'recovery_required');
 assert.equal(observed.repository,'example/project');assert.equal(observed.issueNumber,17);assert.equal(observed.workflowName,'small-change');
 assert.equal(observed.sourceRoot,f.sourceCwd);assert.equal(observed.commonDir,join(f.sourceCwd,'.git'));
 assert.notEqual(observed.cwd,f.sourceCwd);assert.equal(f.saved(outcome.runId).pending.backend.session,'pdd');
});
