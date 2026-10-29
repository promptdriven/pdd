import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { mkdtemp, mkdir, readFile, rm, symlink } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { readFileSync } from 'node:fs';
import { prepareWorkflowPr } from '../src/workflow-github.mjs';

const vectors = JSON.parse(readFileSync('tests/runtime/workflow-github-symlinked-repo.json', 'utf8'));

test('replays workflow-github symlinked repository vectors through prepareWorkflowPr', async t => {
  const parent = await mkdtemp(join(tmpdir(), 'pdd-github-vectors-'));
  t.after(() => rm(parent, { recursive: true, force: true }));
  const realCwd = join(parent, 'repo'), cwd = join(parent, 'alias'), outside = join(parent, 'outside');
  await mkdir(realCwd); await mkdir(outside); await symlink(realCwd, cwd, 'dir');
  const execute = promisify(execFile), git = (...args) => execute('git', args, { cwd, encoding: 'utf8' });
  await git('init', '--initial-branch=main'); await git('config', 'user.name', 'Replay'); await git('config', 'user.email', 'replay@example.invalid');
  await git('commit', '--allow-empty', '-m', 'Base'); await git('remote', 'add', 'origin', 'https://github.com/Acme/Project.git');
  await git('update-ref', 'refs/remotes/origin/main', 'HEAD'); await git('switch', '-c', 'topic/replay'); await git('commit', '--allow-empty', '-m', 'Topic');
  const ports = { async execFile(file, args, options) {
    assert.deepEqual(options, { cwd });
    if (file === 'git') return execute(file, args, { ...options, encoding: 'utf8' });
    return { stdout: JSON.stringify({ nameWithOwner: 'Acme/Project', defaultBranchRef: { name: 'main' }, url: 'https://github.com/Acme/Project' }) };
  } };
  for (const step of vectors.steps) {
    const input = { ...step.input, cwd: step.input.cwd === '/tmp/repo-alias' ? cwd : step.input.cwd.replace('/tmp/repo-alias', cwd) };
    if (input.bodyFile === 'pr-body.md') input.bodyFile = join(cwd, input.bodyFile);
    if (input.bodyFile.startsWith('/tmp/outside')) input.bodyFile = join(outside, 'pr-body.md');
    if (step.expected_error) await assert.rejects(prepareWorkflowPr(input, ports), error => error.code === step.expected_error);
    else {
      const result = await prepareWorkflowPr(input, ports);
      const expected = step.checks[0].value.replace('/tmp/repo-alias', cwd);
      assert.equal(result.bodyFile, expected);
      assert.match(await readFile(result.bodyFile, 'utf8'), /pdd-workflow:run-2444:prompt/);
    }
  }
});
