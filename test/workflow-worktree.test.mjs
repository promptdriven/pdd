import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { randomUUID } from 'node:crypto';
import { mkdtemp, readFile, writeFile, rm, readdir, lstat, symlink, mkdir } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, dirname, basename } from 'node:path';
import { allocateIssueWorktree, lookupIssueWorktree } from '../src/workflow-worktree.mjs';

const execute = promisify(execFile);
async function fixture(t) {
  const temp = await mkdtemp(join(tmpdir(), 'pdd-worktrees-')), cwd = join(temp, 'project');
  await mkdir(cwd); t.after(() => rm(temp, { recursive: true, force: true }));
  const gitAt = (path, ...args) => execute('git', args, { cwd: path, encoding: 'utf8' });
  const git = (...args) => gitAt(cwd, ...args);
  await git('init', '--initial-branch=main'); await git('config', 'user.name', 'Disposable test');
  await git('config', 'user.email', 'test@example.invalid');
  await writeFile(join(cwd, 'source.txt'), 'committed base\n'); await git('add', 'source.txt'); await git('commit', '-m', 'Base');
  await git('remote', 'add', 'origin', 'https://github.com/Acme/Project.git');
  const common = join(cwd, '.git'), calls = [];
  const ports = { async execFile(file, args, options) {
    assert.equal(file, 'git'); assert.deepEqual(Object.keys(options), ['cwd']);
    calls.push({ file, args: [...args], cwd: options.cwd });
    return execute(file, args, { ...options, encoding: 'utf8' });
  } };
  const input = (issueNumber = 1, extra = {}) => ({ cwd, repository: 'Acme/Project', issueNumber,
    runId: randomUUID(), workflowName: 'feature', baseRef: 'main', ...extra });
  return { temp, cwd, git, gitAt, common, calls, ports, input };
}
const adds = calls => calls.filter(c => c.args[0] === 'worktree' && c.args[1] === 'add');
const readOnly = calls => calls.every(c => ['rev-parse', 'remote', 'symbolic-ref', 'merge-base'].includes(c.args[0])
  || c.args[0] === 'worktree' && c.args[1] === 'list');
const metadata = (f, runId) => join(f.common, 'pdd', 'worktree-assignments', 'runs', runId + '.json');

async function snapshot(path) {
  const entries = [];
  for (const name of (await readdir(path)).sort()) {
    const child = join(path, name), stat = await lstat(child);
    if (stat.isDirectory()) entries.push([name, await snapshot(child)]);
    else entries.push([name, await readFile(child, 'utf8')]);
  }
  return entries;
}

test('two issues allocate concurrently into distinct actual worktrees and commits cannot affect peers or dirty caller', async t => {
  const f = await fixture(t);
  await writeFile(join(f.cwd, 'source.txt'), 'user unsaved bytes\n');
  await writeFile(join(f.cwd, 'untracked.txt'), 'user untracked\n');
  const before = (await f.git('status', '--porcelain=v1', '-z', '--untracked-files=all')).stdout;
  const aInput = f.input(101), bInput = f.input(102);
  const [a, b] = await Promise.all([allocateIssueWorktree(aInput, f.ports), allocateIssueWorktree(bInput, f.ports)]);
  assert.equal(a.state, 'ready', a.message); assert.equal(b.state, 'ready', b.message);
  const x = a.assignment, y = b.assignment;
  for (const key of ['worktreePath', 'gitDir', 'branch']) assert.notEqual(x[key], y[key]);
  assert.equal(x.commonDir, f.common); assert.equal(y.commonDir, f.common);
  assert.equal(x.sourceRoot, f.cwd); assert.equal(x.baseSha, (await f.git('rev-parse', 'main')).stdout.trim());
  assert.equal(x.worktreePath, join(f.common, 'pdd', 'worktrees', basename(x.worktreePath)));
  assert.match(basename(x.worktreePath), /^[a-f0-9-]{36}$/);
  assert.match(x.branch, /^pdd\/feature-101-[a-f0-9]{8}$/);
  assert.equal(await readFile(join(x.worktreePath, 'source.txt'), 'utf8'), 'committed base\n');
  await writeFile(join(x.worktreePath, 'source.txt'), 'issue101 only\n');
  await f.gitAt(x.worktreePath, 'add', 'source.txt'); await f.gitAt(x.worktreePath, 'commit', '-m', 'Issue101 change');
  assert.equal(await readFile(join(y.worktreePath, 'source.txt'), 'utf8'), 'committed base\n');
  assert.equal(await readFile(join(f.cwd, 'source.txt'), 'utf8'), 'user unsaved bytes\n');
  assert.equal(await readFile(join(f.cwd, 'untracked.txt'), 'utf8'), 'user untracked\n');
  assert.equal((await f.git('status', '--porcelain=v1', '-z', '--untracked-files=all')).stdout, before);
  assert.equal((await f.git('symbolic-ref', '--short', 'HEAD')).stdout.trim(), 'main');
  assert.equal(adds(f.calls).length, 2);
  f.calls.length = 0;
  assert.deepEqual((await lookupIssueWorktree({ cwd: f.cwd, runId: x.runId }, f.ports)).assignment, x);
  assert(readOnly(f.calls));
});

test('same common-repo issue claim is exclusive across workflow names and linked checkouts', async t => {
  const f = await fixture(t), first = f.input(7), second = f.input(7, { workflowName: 'bug' });
  const outcomes = await Promise.all([allocateIssueWorktree(first, f.ports), allocateIssueWorktree(second, f.ports)]);
  assert.deepEqual(outcomes.map(o => o.state).sort(), ['conflict', 'ready']);
  assert.equal(adds(f.calls).length, 1);
  const a = outcomes.find(o => o.state === 'ready').assignment;
  assert.equal((await allocateIssueWorktree(f.input(7, { cwd: a.worktreePath, workflowName: 'small-change' }), f.ports)).state, 'conflict');
  assert.equal(adds(f.calls).length, 1);
});

test('intent and claim exist with same inode before add; same run resume only reads', async t => {
  const f = await fixture(t), input = f.input(8), ordinary = f.ports.execFile;
  const ports = { async execFile(file, args, options) {
    if (args[0] === 'worktree' && args[1] === 'add') {
      const intentFile = metadata(f, input.runId), claimFile = join(dirname(dirname(intentFile)), 'issues', '8.json');
      const [run, issue] = await Promise.all([lstat(intentFile), lstat(claimFile)]);
      assert.equal(run.ino, issue.ino); assert.equal(run.nlink, 2);
      const saved = JSON.parse(await readFile(intentFile, 'utf8'));
      assert.equal(saved.branch, args[3]); assert.equal(saved.worktreePath, args[4]); assert.equal(saved.baseSha, args[5]);
    }
    return ordinary(file, args, options);
  } };
  const initial = await allocateIssueWorktree(input, ports); assert.equal(initial.state, 'ready');
  f.calls.length = 0;
  const before = await snapshot(join(f.common, 'pdd', 'worktree-assignments'));
  assert.deepEqual((await allocateIssueWorktree(input, ports)).assignment, initial.assignment);
  assert.deepEqual(await snapshot(join(f.common, 'pdd', 'worktree-assignments')), before);
  assert(readOnly(f.calls));
});

test('lost add reply recovers only the exact physically created identity, with no second add', async t => {
  const f = await fixture(t), input = f.input(9), ordinary = f.ports.execFile;
  const ports = { async execFile(file, args, options) {
    const response = await ordinary(file, args, options);
    if (args[0] === 'worktree' && args[1] === 'add') throw new Error('reply lost after real add');
    return response;
  } };
  const initial = await allocateIssueWorktree(input, ports); assert.equal(initial.state, 'ready', initial.message);
  f.calls.length = 0;
  assert.deepEqual((await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, ports)).assignment, initial.assignment);
  assert.deepEqual((await allocateIssueWorktree(input, ports)).assignment, initial.assignment);
  assert.equal(adds(f.calls).length, 0); assert(readOnly(f.calls));
});

test('rejected zero add without effect stays uncertain, retains intent and refuses blind repeat', async t => {
  const f = await fixture(t), input = f.input(10), ordinary = f.ports.execFile; let attempts = 0;
  const ports = { async execFile(file, args, options) {
    if (args[0] === 'worktree' && args[1] === 'add') { attempts++; throw Object.assign(new Error('lost add'), { code: 0, stdout: '' }); }
    return ordinary(file, args, options);
  } };
  assert.equal((await allocateIssueWorktree(input, ports)).state, 'recovery_required');
  const savedBytes = await readFile(metadata(f, input.runId), 'utf8');
  f.calls.length = 0;
  assert.equal((await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, ports)).state, 'recovery_required');
  assert.equal((await allocateIssueWorktree(input, ports)).state, 'recovery_required');
  assert.equal((await allocateIssueWorktree(f.input(10), ports)).state, 'conflict');
  assert.equal(attempts, 1); assert.equal(await readFile(metadata(f, input.runId), 'utf8'), savedBytes);
  assert.equal(adds(f.calls).length, 0);
});

test('missing lookup performs only reads and creates no metadata', async t => {
  const f = await fixture(t);
  assert.equal((await lookupIssueWorktree({ cwd: f.cwd, runId: randomUUID() }, f.ports)).state, 'recovery_required');
  await assert.rejects(lstat(join(f.common, 'pdd')), { code: 'ENOENT' });
  assert(readOnly(f.calls));
});

test('saved run cannot be retargeted to another issue, workflow or base', async t => {
  const f = await fixture(t), input = f.input(11);
  assert.equal((await allocateIssueWorktree(input, f.ports)).state, 'ready'); f.calls.length = 0;
  for (const change of [{ issueNumber: 12 }, { workflowName: 'bug' }, { baseRef: 'HEAD' }])
    assert.equal((await allocateIssueWorktree({ ...input, ...change }, f.ports)).state, 'conflict');
  assert.equal(adds(f.calls).length, 0);
});

test('foreign origin, missing base and revision expressions do not allocate', async t => {
  const f = await fixture(t);
  assert.equal((await allocateIssueWorktree(f.input(1, { repository: 'Other/Project' }), f.ports)).state, 'conflict');
  for (const baseRef of ['absent', 'main~0']) assert.equal((await allocateIssueWorktree(f.input(1, { baseRef }), f.ports)).state, 'recovery_required');
  assert.equal(adds(f.calls).length, 0);
  await assert.rejects(lstat(join(f.common, 'pdd', 'worktree-assignments', 'issues', '1.json')), { code: 'ENOENT' });
});

test('metadata ancestor aliases refuse without writing through to another directory', async t => {
  const f = await fixture(t), outside = join(f.temp, 'outside'); await mkdir(outside);
  await symlink(outside, join(f.common, 'pdd'), 'dir');
  assert.equal((await allocateIssueWorktree(f.input(), f.ports)).state, 'recovery_required');
  assert.deepEqual(await readdir(outside), []); assert.equal(adds(f.calls).length, 0);
});

test('changed branch, Git directory pointer, or origin cannot be adopted during lookup', async t => {
  const f = await fixture(t), input = f.input(15), initial = await allocateIssueWorktree(input, f.ports);
  assert.equal(initial.state, 'ready'); const a = initial.assignment;
  await f.gitAt(a.worktreePath, 'switch', '-c', 'unowned'); f.calls.length = 0;
  assert.equal((await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, f.ports)).state, 'recovery_required');
  assert.equal(adds(f.calls).length, 0);
  await f.gitAt(a.worktreePath, 'switch', a.branch);
  const gitFile = join(a.worktreePath, '.git'), saved = await readFile(gitFile, 'utf8');
  await writeFile(gitFile, 'gitdir: ' + f.common + '\n');
  assert.equal((await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, f.ports)).state, 'recovery_required');
  await writeFile(gitFile, saved);
  await f.git('remote', 'set-url', 'origin', 'https://github.com/Other/Project.git');
  assert.equal((await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, f.ports)).state, 'recovery_required');
});

test('partial intent or missing issue claim is retained and never repaired or added', async t => {
  const f = await fixture(t), input = f.input(16), ordinary = f.ports.execFile;
  const ports = { async execFile(file, args, options) {
    if (args[0] === 'worktree' && args[1] === 'add') throw new Error('no effect');
    return ordinary(file, args, options);
  } };
  assert.equal((await allocateIssueWorktree(input, ports)).state, 'recovery_required');
  const runFile = metadata(f, input.runId), issueFile = join(dirname(dirname(runFile)), 'issues', '16.json');
  await rm(issueFile); // Test simulates interrupted/missing durable claim; helper never deletes it.
  f.calls.length = 0;
  assert.equal((await allocateIssueWorktree(input, ports)).state, 'recovery_required');
  await assert.rejects(lstat(issueFile), { code: 'ENOENT' }); assert.equal(adds(f.calls).length, 0);
  await writeFile(runFile, '{partial');
  assert.equal((await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, ports)).state, 'recovery_required');
  assert.equal(await readFile(runFile, 'utf8'), '{partial');
});


const moduleUrl = new URL('../src/workflow-worktree.mjs', import.meta.url).href;
function subprocessAllocator(input, crash) {
  const code = `import { allocateIssueWorktree } from ${JSON.stringify(moduleUrl)};
    import { execFile } from 'node:child_process'; import { promisify } from 'node:util';
    const execute = promisify(execFile), crash = process.argv[2];
    const ports = { async execFile(file,args,options) {
      const add = args[0] === 'worktree' && args[1] === 'add';
      if (add && crash === 'before') process.exit(77);
      const response = await execute(file,args,{...options,encoding:'utf8'});
      if (add && crash === 'after') process.exit(78);
      return response;
    }};
    console.log(JSON.stringify(await allocateIssueWorktree(JSON.parse(process.argv[1]), ports)));`;
  return execute(process.execPath, ['--input-type=module', '-e', code, JSON.stringify(input), crash ?? 'none'],
    { cwd: input.cwd, encoding: 'utf8', timeout: 20_000 });
}

test('separate processes allocate two issues with both index entries, commit isolation and dirty caller preserved', async t => {
  const f = await fixture(t), aInput = f.input(201), bInput = f.input(202);
  await writeFile(join(f.cwd, 'source.txt'), 'person dirty bytes\n');
  await writeFile(join(f.cwd, 'untracked.txt'), 'person untracked bytes\n');
  const before = (await f.git('status', '--porcelain=v1', '-z', '--untracked-files=all')).stdout;
  const replies = await Promise.all([subprocessAllocator(aInput), subprocessAllocator(bInput)]);
  const outcomes = replies.map(r => JSON.parse(r.stdout));
  assert(outcomes.every(r => r.state === 'ready'), JSON.stringify(outcomes));
  const [a, b] = outcomes.map(r => r.assignment);
  for (const key of ['worktreePath', 'gitDir', 'branch']) assert.notEqual(a[key], b[key]);
  await writeFile(join(a.worktreePath, 'source.txt'), 'first issue committed change\n');
  await f.gitAt(a.worktreePath, 'add', 'source.txt'); await f.gitAt(a.worktreePath, 'commit', '-m', 'Only first issue');
  assert.equal(await readFile(join(b.worktreePath, 'source.txt'), 'utf8'), 'committed base\n');
  assert.equal(await readFile(join(f.cwd, 'source.txt'), 'utf8'), 'person dirty bytes\n');
  assert.equal(await readFile(join(f.cwd, 'untracked.txt'), 'utf8'), 'person untracked bytes\n');
  assert.equal((await f.git('status', '--porcelain=v1', '-z', '--untracked-files=all')).stdout, before);
  assert.equal((await f.git('symbolic-ref', '--short', 'HEAD')).stdout.trim(), 'main');
  const runs = join(f.common, 'pdd', 'worktree-assignments', 'runs');
  const issues = join(dirname(runs), 'issues');
  assert.deepEqual((await readdir(runs)).sort(), [aInput.runId + '.json', bInput.runId + '.json'].sort());
  assert.deepEqual((await readdir(issues)).sort(), ['201.json', '202.json']);
  for (const input of [aInput, bInput]) {
    const outcome = await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, f.ports);
    assert.equal(outcome.state, 'ready'); assert.equal(outcome.assignment.issueNumber, input.issueNumber);
    assert.equal(JSON.parse(await readFile(metadata(f, input.runId), 'utf8')).worktreePath, outcome.assignment.worktreePath);
  }
});

test('separate processes competing for the same common issue across workflow names allocate only once', async t => {
  const f = await fixture(t), first = f.input(203), second = f.input(203, { workflowName: 'bug' });
  const replies = await Promise.all([subprocessAllocator(first), subprocessAllocator(second)]);
  const outcomes = replies.map(r => JSON.parse(r.stdout));
  assert.deepEqual(outcomes.map(r => r.state).sort(), ['conflict', 'ready']);
  const list = (await f.git('worktree', 'list', '--porcelain')).stdout;
  assert.equal((list.match(/^worktree /gm) ?? []).length, 2);
  const winner = outcomes.find(r => r.state === 'ready').assignment;
  const claim = JSON.parse(await readFile(join(f.common, 'pdd', 'worktree-assignments', 'issues', '203.json'), 'utf8'));
  assert.equal(claim.runId, winner.runId);
});

for (const crash of ['before', 'after']) test(`actual process death ${crash} add keeps the same indexed identity and never allocates again`, async t => {
  const f = await fixture(t), input = f.input(crash === 'before' ? 204 : 205);
  await assert.rejects(subprocessAllocator(input, crash), error => error.code === (crash === 'before' ? 77 : 78));
  const saved = await readFile(metadata(f, input.runId), 'utf8'), intent = JSON.parse(saved);
  const expected = crash === 'before' ? 'recovery_required' : 'ready';
  f.calls.length = 0;
  const read = await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, f.ports);
  assert.equal(read.state, expected);
  const resumed = await allocateIssueWorktree(input, f.ports);
  assert.equal(resumed.state, expected);
  if (crash === 'after') assert.equal(resumed.assignment.worktreePath, intent.worktreePath);
  assert.equal(await readFile(metadata(f, input.runId), 'utf8'), saved);
  assert.equal(adds(f.calls).length, 0); assert(readOnly(f.calls));
  assert.equal((await allocateIssueWorktree(f.input(input.issueNumber), f.ports)).state, 'conflict');
});

test('an unowned directory appearing at the intended path is retained and never adopted or cleaned', async t => {
  const f = await fixture(t), input = f.input(206), ordinary = f.ports.execFile; let intended;
  const ports = { async execFile(file, args, options) {
    if (args[0] === 'worktree' && args[1] === 'add') {
      intended = args[4]; await mkdir(intended);
      await writeFile(join(intended, 'foreign.txt'), 'unowned bytes\n');
    }
    return ordinary(file, args, options);
  } };
  assert.equal((await allocateIssueWorktree(input, ports)).state, 'recovery_required');
  assert.equal(await readFile(join(intended, 'foreign.txt'), 'utf8'), 'unowned bytes\n');
  f.calls.length = 0;
  assert.equal((await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, ports)).state, 'recovery_required');
  assert.equal((await allocateIssueWorktree(input, ports)).state, 'recovery_required');
  assert.equal(await readFile(join(intended, 'foreign.txt'), 'utf8'), 'unowned bytes\n');
  assert.equal(adds(f.calls).length, 0); assert(readOnly(f.calls));
});

test('a colliding existing branch refuses allocation without deleting or reusing it', async t => {
  const f = await fixture(t), ordinary = f.ports.execFile; let branch;
  const ports = { async execFile(file, args, options) {
    if (args[0] === 'show-ref') { branch = args.at(-1).slice('refs/heads/'.length); await f.git('branch', branch, 'main'); }
    return ordinary(file, args, options);
  } };
  const input = f.input(207);
  assert.equal((await allocateIssueWorktree(input, ports)).state, 'conflict');
  assert.equal(adds(f.calls).length, 0);
  assert.equal((await f.git('rev-parse', branch)).stdout, (await f.git('rev-parse', 'main')).stdout);
  await assert.rejects(lstat(metadata(f, input.runId)), { code: 'ENOENT' });
});

test('advancing the base ref does not rebind an existing assignment to the newer commit', async t => {
  const f = await fixture(t), input = f.input(208), initial = await allocateIssueWorktree(input, f.ports);
  assert.equal(initial.state, 'ready');
  await writeFile(join(f.cwd, 'source.txt'), 'new main commit\n');
  await f.git('add', 'source.txt'); await f.git('commit', '-m', 'Advance main');
  const newer = (await f.git('rev-parse', 'main')).stdout.trim();
  assert.notEqual(newer, initial.assignment.baseSha);
  f.calls.length = 0;
  assert.deepEqual((await allocateIssueWorktree(input, f.ports)).assignment, initial.assignment);
  assert.equal(await readFile(join(initial.assignment.worktreePath, 'source.txt'), 'utf8'), 'committed base\n');
  assert.equal(adds(f.calls).length, 0); assert(readOnly(f.calls));
});

const shellArg = value => "'" + value.replaceAll("'", "'\\''") + "'";
async function waitForFile(path) {
  const deadline = Date.now() + 10_000;
  while (Date.now() < deadline) {
    try { await lstat(path); return; } catch (error) { if (error.code !== 'ENOENT') throw error; }
    await new Promise(resolve => setTimeout(resolve, 10));
  }
  assert.fail('Real Git checkout did not reach the bounded smudge-filter boundary');
}

for (const completion of ['completed', 'interrupted']) test(`actual Git initializing registration stays uncertain until ${completion} checkout is resolved`, async t => {
  const f = await fixture(t), gate = join(f.temp, 'checkout-gate'), script = join(f.temp, 'checkout-filter.mjs');
  await mkdir(gate);
  await writeFile(join(f.cwd, '.gitattributes'), 'source.txt filter=pdd-boundary\n');
  await f.git('add', '.gitattributes'); await f.git('commit', '-m', 'Retained source attributes');
  await writeFile(script, `import { readFileSync, writeFileSync, existsSync } from 'node:fs';
    import { join } from 'node:path';
    const bytes = readFileSync(0), gate = process.argv[2];
    writeFileSync(join(gate, 'entered'), '');
    const deadline = Date.now() + 15000;
    while (!existsSync(join(gate, 'release'))) {
      if (Date.now() > deadline) process.exit(70);
      await new Promise(resolve => setTimeout(resolve, 10));
    }
    process.stdout.write(bytes);`);
  await f.git('config', 'filter.pdd-boundary.smudge', [process.execPath, script, gate].map(shellArg).join(' '));
  await f.git('config', 'filter.pdd-boundary.required', 'true');
  const input = f.input(completion === 'completed' ? 209 : 210), ordinary = f.ports.execFile;
  let addChild, attempts = 0;
  const ports = { async execFile(file, args, options) {
    if (args[0] !== 'worktree' || args[1] !== 'add') return ordinary(file, args, options);
    attempts++; f.calls.push({ file, args: [...args], cwd: options.cwd });
    const pending = execute(file, args, { ...options, encoding: 'utf8', timeout: 20_000 });
    addChild = pending.child;
    return pending;
  } };
  const allocating = allocateIssueWorktree(input, ports);
  try {
    await waitForFile(join(gate, 'entered'));
    const saved = await readFile(metadata(f, input.runId), 'utf8'), intent = JSON.parse(saved);
    const before = await snapshot(join(f.common, 'pdd', 'worktree-assignments'));
    const registered = (await f.git('worktree', 'list', '--porcelain', '-z')).stdout;
    assert(registered.includes('worktree ' + intent.worktreePath + '\0'));
    assert(registered.includes('HEAD ' + intent.baseSha + '\0'));
    assert(registered.includes('branch refs/heads/' + intent.branch + '\0'));
    assert(registered.includes('locked initializing\0'));
    assert.equal((await f.gitAt(intent.worktreePath, 'rev-parse', '--path-format=absolute', '--git-dir')).stdout.trim(), intent.gitDir);
    f.calls.length = 0;
    const observed = await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, ports);
    assert.equal(observed.state, 'recovery_required'); assert.equal(observed.assignment, null);
    assert.equal((await allocateIssueWorktree(input, ports)).state, 'recovery_required');
    assert(readOnly(f.calls)); assert.equal(attempts, 1);
    assert.deepEqual(await snapshot(join(f.common, 'pdd', 'worktree-assignments')), before);
    assert.equal(await readFile(join(intent.gitDir, 'locked'), 'utf8'), 'initializing\n');
    if (completion === 'interrupted') assert.equal(addChild.kill('SIGKILL'), true);
    await writeFile(join(gate, 'release'), '');
    const outcome = await allocating;
    assert.equal(outcome.state, completion === 'completed' ? 'ready' : 'recovery_required');
    f.calls.length = 0;
    const recovered = await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, ports);
    assert.equal(recovered.state, completion === 'completed' ? 'ready' : 'recovery_required');
    assert.equal((await allocateIssueWorktree(input, ports)).state, recovered.state);
    assert.equal(attempts, 1); assert(readOnly(f.calls));
    assert.equal(await readFile(metadata(f, input.runId), 'utf8'), saved);
    if (completion === 'completed') {
      assert.equal(await readFile(join(intent.worktreePath, 'source.txt'), 'utf8'), 'committed base\n');
      assert.equal(recovered.assignment.worktreePath, intent.worktreePath);
    } else assert.equal(await readFile(join(intent.gitDir, 'locked'), 'utf8'), 'initializing\n');
  } finally {
    await writeFile(join(gate, 'release'), '');
    await allocating;
  }
});


test('completed worktrees remain ready under ordinary protective locks with and without reasons', async t => {
  const f = await fixture(t), input = f.input(211), initial = await allocateIssueWorktree(input, f.ports);
  assert.equal(initial.state, 'ready');
  const a = initial.assignment, before = await snapshot(join(f.common, 'pdd', 'worktree-assignments'));
  await writeFile(join(a.worktreePath, 'source.txt'), 'person later work\n');
  for (const args of [['--reason', 'person protecting completed work'], []]) {
    await f.git('worktree', 'lock', ...args, a.worktreePath); f.calls.length = 0;
    assert.deepEqual((await lookupIssueWorktree({ cwd: f.cwd, runId: input.runId }, f.ports)).assignment, a);
    assert.deepEqual((await allocateIssueWorktree(input, f.ports)).assignment, a);
    assert(readOnly(f.calls)); assert.equal(adds(f.calls).length, 0);
    assert.deepEqual(await snapshot(join(f.common, 'pdd', 'worktree-assignments')), before);
    assert.equal(await readFile(join(a.worktreePath, 'source.txt'), 'utf8'), 'person later work\n');
    await f.git('worktree', 'unlock', a.worktreePath); // Fixture alone changes the protective lock.
    if (args.length) {
      await f.gitAt(a.worktreePath, 'add', 'source.txt');
      await f.gitAt(a.worktreePath, 'commit', '-m', 'Later assigned work');
    }
  }
});
