import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import * as fs from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import test from 'node:test';
import { assertWorkflowArtifacts, readWorkflowHandoff, runWorkflowTestCommands } from '../src/workflow-artifacts.mjs';

const hash = bytes => createHash('sha256').update(bytes).digest('hex');

async function fixture(t) {
  const cwd = await fs.realpath(await fs.mkdtemp(join(tmpdir(), 'pdd-artifacts-')));
  t.after(() => fs.rm(cwd, { recursive: true, force: true }));
  const handoffPath = join(cwd, '.git/pdd/run/handoff.json');
  await fs.mkdir(dirname(handoffPath), { recursive: true });
  const expected = { runId: 'run-1', stageId: 'prompt-story', issueUrl: 'https://github.com/example/project/issues/1', inputRevision: 'revision-1' };
  const files = [];
  for (const [path, role, text] of [['prompts/task.prompt.md', 'prompt', 'Required behavior.'], ['story/task.md', 'story', 'Observable behavior.'], ['cases/task.json', 'cases', '{"expected":8}']]) {
    await fs.mkdir(dirname(join(cwd, path)), { recursive: true });
    await fs.writeFile(join(cwd, path), text);
    files.push({ path, role, sha256: hash(text) });
  }
  const data = { version: 1, ...expected, summary: 'Draft contract and independent cases.', files, testCommands: [['node', '--test', 'test/task.test.mjs']] };
  const save = value => fs.writeFile(handoffPath, JSON.stringify(value));
  await save(data);
  return { cwd, handoffPath, expected, data, save, request: { cwd, handoffPath, expected, requiredRoles: ['prompt', 'story', 'cases'] } };
}

// Wrong behavior: trust a model's listed paths/digests or drop required-role validation.
test('handoff returns exact bound bytes and requires selected prompt/story/cases roles', async t => {
  const f = await fixture(t);
  assert.deepEqual(await readWorkflowHandoff(f.request), f.data);
  await assertWorkflowArtifacts({ cwd: f.cwd, files: f.data.files });
  await f.save({ ...f.data, files: f.data.files.slice(0, 2) });
  await assert.rejects(readWorkflowHandoff(f.request), /role/);
});

// Wrong behavior: approve a stale run/stage/issue/input merely because files are unchanged.
test('all four caller identities are mandatory and exact', async t => {
  const f = await fixture(t);
  for (const key of ['runId', 'stageId', 'issueUrl', 'inputRevision']) {
    await t.test(key, async () => {
      await f.save({ ...f.data, [key]: f.data[key] + '-stale' });
      await assert.rejects(readWorkflowHandoff(f.request), /identity/);
    });
  }
  await f.save(f.data);
  await assert.rejects(readWorkflowHandoff({ ...f.request, expected: { ...f.expected, inputRevision: '' } }));
  await assert.rejects(readWorkflowHandoff({ ...f.request, expected: undefined }));
});

// Wrong behavior: silently discard unknown fields or accept duplicate file claims.
test('closed schema refuses unknown fields, duplicate paths and invalid roles', async t => {
  const f = await fixture(t);
  const invalid = [
    { ...f.data, approved: true },
    { ...f.data, version: 2 },
    { ...f.data, summary: '  ' },
    { ...f.data, files: [{ ...f.data.files[0], observed: true }] },
    { ...f.data, files: [f.data.files[0], f.data.files[0]] },
    { ...f.data, files: [{ ...f.data.files[0], role: 'testplan' }] },
    { ...f.data, files: [{ ...f.data.files[0], sha256: 'model says PASS' }] },
  ];
  for (const value of invalid) {
    await f.save(value);
    await assert.rejects(readWorkflowHandoff({ ...f.request, requiredRoles: [] }));
  }
});

// Wrong behavior: force fake executable artifacts into report-only stages.
test('empty report files are allowed only when requested roles are satisfied', async t => {
  const f = await fixture(t);
  const report = { ...f.data, files: [] };
  delete report.testCommands;
  await f.save(report);
  assert.deepEqual(await readWorkflowHandoff({ ...f.request, requiredRoles: [] }), report);
  await assert.rejects(readWorkflowHandoff(f.request), /role/);
  await assertWorkflowArtifacts({ cwd: f.cwd, files: [] });
});

// Wrong behavior: trust the digest that was correct before an agent rewrote its artifact.
test('actual changed bytes fail both initial handoff and later artifact reassertion', async t => {
  const f = await fixture(t);
  const accepted = await readWorkflowHandoff(f.request);
  await fs.writeFile(join(f.cwd, accepted.files[0].path), 'Different implementation.');
  await assert.rejects(readWorkflowHandoff(f.request), /hash/);
  await assert.rejects(assertWorkflowArtifacts({ cwd: f.cwd, files: accepted.files }), /hash/);
});

// Wrong behavior: normalize traversal or absolute names into apparently safe files.
test('artifact escape, Git metadata and noncanonical paths are refused', async t => {
  const f = await fixture(t);
  for (const path of ['../outside', '/etc/passwd', 'a/../../outside', '.git/config', 'a/.GiT/config', 'a//b', './a', 'a/../b', 'a\\b', 'C:/project/file']) {
    await assert.rejects(assertWorkflowArtifacts({ cwd: f.cwd, files: [{ ...f.data.files[0], path }] }));
  }
});

// Wrong behavior: realpath follows an outside file or a symlink ancestor before containment checks.
test('symlink files/ancestors and directory artifacts never count as regular project files', async t => {
  const f = await fixture(t);
  const outside = await fs.mkdtemp(join(tmpdir(), 'pdd-outside-'));
  t.after(() => fs.rm(outside, { recursive: true, force: true }));
  await fs.writeFile(join(outside, 'secret'), 'Same bytes do not authorize an outside file.');
  await fs.symlink(join(outside, 'secret'), join(f.cwd, 'linked-file'));
  await fs.symlink(outside, join(f.cwd, 'linked-parent'));
  for (const path of ['linked-file', 'linked-parent/secret', 'prompts']) {
    await assert.rejects(assertWorkflowArtifacts({ cwd: f.cwd, files: [{ path, role: 'evidence', sha256: hash('Same bytes do not authorize an outside file.') }] }));
  }
  const alias = join(outside, 'project-alias');
  await fs.symlink(f.cwd, alias);
  await assert.rejects(assertWorkflowArtifacts({ cwd: alias, files: f.data.files }));
});

// Wrong behavior: read any JSON file supplied by the model instead of caller-selected Git metadata.
test('handoff itself must be regular and contained in the actual Git directory', async t => {
  const f = await fixture(t);
  const local = join(f.cwd, 'model-handoff.json');
  await fs.writeFile(local, JSON.stringify(f.data));
  await assert.rejects(readWorkflowHandoff({ ...f.request, handoffPath: local }));
  await fs.unlink(f.handoffPath);
  await fs.symlink(local, f.handoffPath);
  await assert.rejects(readWorkflowHandoff(f.request));
  await fs.unlink(f.handoffPath);
  await fs.rm(dirname(f.handoffPath), { recursive: true });
  await fs.symlink(f.cwd, dirname(f.handoffPath));
  await assert.rejects(readWorkflowHandoff(f.request));
});

test('a real linked-worktree Git pointer supports a caller-bound external metadata path', async t => {
  const f = await fixture(t);
  const metadata = await fs.realpath(await fs.mkdtemp(join(tmpdir(), 'pdd-git-metadata-')));
  t.after(() => fs.rm(metadata, { recursive: true, force: true }));
  await fs.rm(join(f.cwd, '.git'), { recursive: true });
  await fs.writeFile(join(f.cwd, '.git'), 'gitdir: ' + metadata + '\n');
  const handoffPath = join(metadata, 'handoff.json');
  await fs.writeFile(handoffPath, JSON.stringify(f.data));
  assert.deepEqual(await readWorkflowHandoff({ ...f.request, handoffPath }), f.data);
  await fs.unlink(join(f.cwd, '.git'));
  await fs.symlink(metadata, join(f.cwd, '.git'));
  await assert.rejects(readWorkflowHandoff({ ...f.request, handoffPath }));
});

// Wrong behavior: read a different inode or ignore a source rewrite during validation.
test('a file changed while the descriptor is read cannot supply a valid handoff', async t => {
  const f = await fixture(t);
  const target = join(f.cwd, f.data.files[0].path);
  const io = { ...fs, open: async (path, ...args) => {
    const handle = await fs.open(path, ...args);
    if (path !== target) return handle;
    return { stat: () => handle.stat(), close: () => handle.close(), readFile: async () => {
      const bytes = await handle.readFile();
      await fs.writeFile(target, 'changed during read');
      return bytes;
    } };
  } };
  await assert.rejects(readWorkflowHandoff(f.request, { fs: io }), /changed/);
});

// Wrong behavior: turn missing tests, strings or shell command text into an empty successful run.
test('missing/malformed/shell argv is refused before any command executes', async t => {
  const f = await fixture(t);
  let called = 0;
  const ports = { execFile: () => { called++; throw new Error('must not execute'); } };
  for (const commands of [undefined, [], 'node --test', ['node --test'], [[]], [['']], [['node --test']], [['sh', '-c', 'echo PASS']], [['node', 1]], [['node', '\0']]]) {
    await assert.rejects(runWorkflowTestCommands({ cwd: f.cwd, testCommands: commands }, ports));
  }
  assert.equal(called, 0);
  await f.save({ ...f.data, testCommands: ['node --test'] });
  await assert.rejects(readWorkflowHandoff(f.request));
});

// Wrong behavior: stringify argv and run a shell, or accept PASS text despite a nonzero exit.
test('callback execFile receives literal argv/cwd and records all real failures', async t => {
  const f = await fixture(t);
  const seen = [];
  const commands = [['node', '--test', 'test/a file;literal.mjs'], ['node', 'fail'], ['missing-tool'], ['node', 'last']];
  const execFile = (file, args, options, done) => {
    seen.push({ file, args, options });
    if (args[0] === 'fail') done(Object.assign(new Error('failed'), { code: 7 }), 'PASS is only text', 'actual failure');
    else if (file === 'missing-tool') done(Object.assign(new Error('spawn missing-tool ENOENT'), { code: 'ENOENT' }));
    else done(null, 'observed output', '');
  };
  const report = await runWorkflowTestCommands({ cwd: f.cwd, testCommands: commands }, { execFile });
  assert.equal(report.passed, false);
  assert.deepEqual(report.results.map(row => row.exitCode), [0, 7, null, 0]);
  assert.deepEqual(report.results.map(row => row.argv), commands);
  assert.deepEqual(seen[0], { file: 'node', args: ['--test', 'test/a file;literal.mjs'], options: { cwd: f.cwd } });
  assert.equal(report.results[1].stdout, 'PASS is only text');
  assert.match(report.results[2].stderr, /ENOENT/);
});

test('promisified execution preserves explicit nonzero, signal and operational rejection outcomes', async t => {
  const f = await fixture(t);
  const outcomes = [{ stdout: 'actual zero', stderr: '' }, { exitCode: 4, stdout: 'PASS' }, { exitCode: null }, { signal: 'SIGTERM' }, undefined,
    Object.assign(new Error('rejected'), { code: 0 }), Object.assign(new Error('nonzero'), { code: 5, stdout: 'actual output' })];
  const report = await runWorkflowTestCommands({ cwd: f.cwd, testCommands: outcomes.map(() => ['node', '--test']) }, {
    execFile: async () => { const next = outcomes.shift(); if (next instanceof Error) throw next; return next; },
  });
  assert.equal(report.passed, false);
  assert.deepEqual(report.results.map(row => row.exitCode), [0, 4, null, null, null, null, 5]);
});

// Harmless native control: proves default execution uses the real local Node process and its exit code.
test('default execFile records genuine local stdout/stderr and a nonzero process exit', async t => {
  const f = await fixture(t);
  const commands = [[process.execPath, '-e', 'process.stdout.write(process.argv[1]);', 'literal;not-a-shell'],
    [process.execPath, '-e', 'process.stdout.write("PASS");process.stderr.write("failed");process.exitCode=3;']];
  const report = await runWorkflowTestCommands({ cwd: f.cwd, testCommands: commands });
  assert.equal(report.passed, false);
  assert.deepEqual(report.results.map(row => row.exitCode), [0, 3]);
  assert.equal(report.results[0].stdout, 'literal;not-a-shell');
  assert.equal(report.results[1].stdout, 'PASS');
  assert.equal(report.results[1].stderr, 'failed');
  assert.equal((await runWorkflowTestCommands({ cwd: f.cwd, testCommands: commands.slice(0, 1) })).passed, true);
});
