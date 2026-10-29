import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, rm, symlink } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { readFileSync } from 'node:fs';
import { prepareWorkflowPr } from '../src/workflow-github.mjs';

const vectors = JSON.parse(readFileSync('tests/runtime/workflow-github-symlinked-repo.json', 'utf8'));
test('replays symlinked repository vector without body-file I/O', async t => {
  const parent = await mkdtemp(join(tmpdir(), 'pdd-github-vectors-')); t.after(() => rm(parent, { recursive: true, force: true }));
  const realCwd = join(parent, 'repo'), cwd = join(parent, 'run-folder-with-any-name'); await mkdir(realCwd); await symlink(realCwd, cwd, 'dir');
  const base = { async execFile(file, args, options) {
    assert.equal(options.cwd, cwd);
    if (file === 'git') {
      const outputs = { 'remote get-url origin': 'git@github.com:Acme/Project.git', 'rev-parse --show-toplevel': realCwd, 'status --porcelain=v1 -z --untracked-files=all': '', 'symbolic-ref --quiet --short HEAD': 'topic/replay', 'rev-parse --verify HEAD': 'a'.repeat(40), 'rev-parse --verify refs/remotes/origin/main^{commit}': 'a'.repeat(40), 'rev-list --count refs/remotes/origin/main..HEAD': '1', 'log -1 --format=%s': 'Replay topic' };
      const out = outputs[args.join(' ')]; if (out !== undefined) return { stdout: out }; if (args[0] === 'check-ref-format') return { stdout: '' }; throw new Error(`unexpected git ${args.join(' ')}`);
    }
    return { stdout: JSON.stringify({ nameWithOwner: 'Acme/Project', defaultBranchRef: { name: 'main' }, url: 'https://github.com/Acme/Project' }) };
  } };
  const step = vectors.steps[0], result = await prepareWorkflowPr({ ...step.input, cwd }, base);
  assert.equal(result.marker, 'pdd-workflow:run-2444:prompt'); assert.equal('bodyFile' in result, false);
});
