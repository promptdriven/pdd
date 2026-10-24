// Generated from prompts/cli/workflow-worktree.prompt.md (sha256: ac7a5fdcdabdfaa549c8e32735b4a7d4791a76cec923da74178dfa9dad93ae1e).
import { execFile } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { constants } from 'node:fs';
import { lstat, realpath, mkdir, open, link } from 'node:fs/promises';
import { basename, dirname, isAbsolute, join } from 'node:path';
import { promisify } from 'node:util';

const execute = promisify(execFile);
const UUID = /^[a-f0-9]{8}-[a-f0-9]{4}-4[a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$/;
const SHA = /^[a-f0-9]{40}$/;
const safe = (value, max = 160) => typeof value === 'string' && value.length <= max && /^[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(value);
const plain = value => typeof value === 'string' && value.length > 0 && !/[\x00-\x1f\x7f]/.test(value);
const repoName = value => plain(value) && /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(value);
const sameRepo = (a, b) => a.toLowerCase() === b.toLowerCase();
const result = (state, message, assignment = null) => ({ state, assignment, message });
const fail = () => { throw new Error('workflow_worktree_identity_unavailable'); };
const equal = (a, b) => JSON.stringify(a) === JSON.stringify(b);

function commands(ports) {
  const run = ports.execFile ?? ((file, args, { cwd }) => execute(file, args,
    { cwd, encoding: 'utf8', shell: false, timeout: 60_000, maxBuffer: 8 * 1024 * 1024 }));
  async function raw(cwd, args) {
    let response;
    try { response = await run('git', args, { cwd }); }
    catch (error) {
      if (!Number.isInteger(error?.code) || error.code === 0) fail();
      response = { stdout: error.stdout ?? '', code: error.code };
    }
    if (!response || typeof response.stdout !== 'string' || response.code !== undefined && !Number.isInteger(response.code)) fail();
    return { stdout: response.stdout, code: response.code ?? 0 };
  }
  return { raw, async git(cwd, args) {
    const response = await raw(cwd, args);
    if (response.code !== 0) fail();
    return response.stdout;
  } };
}

function originRepo(value) {
  if (value.startsWith('git@github.com:')) value = 'https://github.com/' + value.slice(15);
  let url;
  try { url = new URL(value); } catch { fail(); }
  if (url.hostname !== 'github.com' || url.port || url.search || url.hash || url.password
    || !['https:', 'ssh:'].includes(url.protocol) || url.username && !(url.protocol === 'ssh:' && url.username === 'git')) fail();
  const repository = url.pathname.slice(1).replace(/\.git$/, '');
  if (!repoName(repository)) fail();
  return repository;
}

async function canonicalDirectory(path) {
  if (!isAbsolute(path) || await realpath(path) !== path || !(await lstat(path)).isDirectory()) fail();
  return path;
}

async function context(cwd, c) {
  if (!plain(cwd)) fail();
  const sourceRoot = await realpath((await c.git(cwd, ['rev-parse', '--show-toplevel'])).trim());
  const commonDir = await realpath((await c.git(cwd, ['rev-parse', '--path-format=absolute', '--git-common-dir'])).trim());
  const repository = originRepo((await c.git(cwd, ['remote', 'get-url', 'origin'])).trim());
  await canonicalDirectory(sourceRoot); await canonicalDirectory(commonDir);
  return { sourceRoot, commonDir, repository };
}

function locations(commonDir, runId, issueNumber) {
  const root = join(commonDir, 'pdd'), index = join(root, 'worktree-assignments');
  return { root, index, runs: join(index, 'runs'), issues: join(index, 'issues'), worktrees: join(root, 'worktrees'),
    run: join(index, 'runs', runId + '.json'), issue: join(index, 'issues', String(issueNumber) + '.json') };
}

async function exists(path) {
  try { await lstat(path); return true; } catch (error) { if (error.code !== 'ENOENT') throw error; return false; }
}

async function syncDirectory(path) {
  const handle = await open(path, constants.O_RDONLY | constants.O_DIRECTORY | constants.O_NOFOLLOW);
  try { await handle.sync(); } finally { await handle.close(); }
}

async function ensureDirectory(path) {
  try { await mkdir(path, { mode: 0o700 }); } catch (error) { if (error.code !== 'EEXIST') throw error; }
  await canonicalDirectory(path);
  await syncDirectory(dirname(path));
}

async function checkDirectories(p) {
  for (const path of [p.root, p.index, p.runs, p.issues, p.worktrees]) await canonicalDirectory(path);
}

async function readRecord(file) {
  const before = await lstat(file);
  if (!before.isFile() || before.nlink > 2) fail();
  const handle = await open(file, constants.O_RDONLY | constants.O_NOFOLLOW);
  try {
    const actual = await handle.stat();
    if (actual.ino !== before.ino || actual.dev !== before.dev) fail();
    return JSON.parse(await handle.readFile('utf8'));
  } finally { await handle.close(); }
}

function assignmentShape(a, commonDir, runId) {
  const keys = 'baseRef,baseSha,branch,commonDir,gitDir,issueNumber,repository,runId,sourceRoot,version,workflowName,worktreePath';
  if (!a || Object.keys(a).sort().join(',') !== keys || a.version !== 1 || a.runId !== runId
    || !safe(a.runId) || !repoName(a.repository) || !Number.isSafeInteger(a.issueNumber) || a.issueNumber < 1
    || !safe(a.workflowName, 80) || a.commonDir !== commonDir || !plain(a.baseRef) || !SHA.test(a.baseSha)
    || !plain(a.sourceRoot) || !isAbsolute(a.sourceRoot) || !plain(a.worktreePath)) fail();
  const id = basename(a.worktreePath);
  if (!UUID.test(id) || a.worktreePath !== join(commonDir, 'pdd', 'worktrees', id)
    || a.gitDir !== join(commonDir, 'worktrees', id) || a.branch !== branchName(a.workflowName, a.issueNumber, id)) fail();
  return a;
}

function branchName(workflowName, issueNumber, id) {
  const name = workflowName.toLowerCase().replace(/[^a-z0-9-]/g, '-').replace(/-+/g, '-').slice(0, 40);
  return `pdd/${name}-${issueNumber}-${id.slice(0, 8)}`;
}

async function ownedRecord(ctx, runId) {
  const p = locations(ctx.commonDir, runId);
  await checkDirectories(p);
  const a = assignmentShape(await readRecord(p.run), ctx.commonDir, runId);
  if (!sameRepo(a.repository, ctx.repository)) fail();
  const issueFile = locations(ctx.commonDir, runId, a.issueNumber).issue;
  const claim = await readRecord(issueFile);
  if (!equal(claim, a)) fail();
  const [runStat, issueStat] = await Promise.all([lstat(p.run), lstat(issueFile)]);
  if (runStat.dev !== issueStat.dev || runStat.ino !== issueStat.ino || runStat.nlink !== 2 || issueStat.nlink !== 2) fail();
  return a;
}

function registrations(output) {
  const records = []; let record;
  for (const field of output.split('\0')) {
    if (field.startsWith('worktree ')) { record = {}; records.push(record); }
    if (field && record) {
      const split = field.indexOf(' '), key = split < 0 ? field : field.slice(0, split), value = split < 0 ? true : field.slice(split + 1);
      if (Object.hasOwn(record, key)) fail();
      record[key] = value;
    }
  }
  return records;
}

async function reconcile(ctx, a, c) {
  await canonicalDirectory(a.sourceRoot);
  const original = await context(a.sourceRoot, c);
  if (original.commonDir !== a.commonDir || !sameRepo(original.repository, a.repository)) fail();
  await canonicalDirectory(a.worktreePath); await canonicalDirectory(a.gitDir);
  await canonicalDirectory(join(a.commonDir, 'worktrees'));
  const gitFile = await lstat(join(a.worktreePath, '.git'));
  if (!gitFile.isFile() || gitFile.nlink !== 1) fail();
  const actual = await context(a.worktreePath, c);
  const actualGitDir = (await c.git(a.worktreePath, ['rev-parse', '--path-format=absolute', '--git-dir'])).trim();
  const branch = (await c.git(a.worktreePath, ['symbolic-ref', '--quiet', '--short', 'HEAD'])).trim();
  const head = (await c.git(a.worktreePath, ['rev-parse', '--verify', 'HEAD'])).trim();
  if (actual.sourceRoot !== a.worktreePath || actual.commonDir !== a.commonDir || actualGitDir !== a.gitDir
    || branch !== a.branch || !SHA.test(head) || !sameRepo(actual.repository, a.repository)) fail();
  await c.git(a.worktreePath, ['merge-base', '--is-ancestor', a.baseSha, head]);
  const listed = registrations(await c.git(ctx.sourceRoot, ['worktree', 'list', '--porcelain', '-z']));
  const matching = listed.filter(r => r.worktree === a.worktreePath || r.branch === 'refs/heads/' + a.branch);
  if (matching.length !== 1 || matching[0].worktree !== a.worktreePath || matching[0].branch !== 'refs/heads/' + a.branch
    || matching[0].locked === 'initializing' || matching[0].HEAD !== head || matching[0].bare || matching[0].detached || matching[0].prunable) fail();
  // Re-read immutable custody after all awaited Git reads.
  if (!equal(await ownedRecord(ctx, a.runId), a)) fail();
  return result('ready', 'Verified the original issue worktree assignment.', a);
}

export async function lookupIssueWorktree(input, ports = {}) {
  try {
    const { cwd, runId } = structuredClone(input ?? {});
    if (!safe(runId)) fail();
    const c = commands(ports), ctx = await context(cwd, c);
    return await reconcile(ctx, await ownedRecord(ctx, runId), c);
  } catch { return result('recovery_required', 'The original worktree assignment is absent, incomplete or changed. Inspect this same run; do not allocate again.'); }
}

export async function allocateIssueWorktree(input, ports = {}) {
  let saved = false;
  try {
    const { cwd, repository, issueNumber, runId, workflowName, baseRef } = structuredClone(input ?? {});
    if (!repoName(repository) || !safe(runId) || !safe(workflowName, 80) || !Number.isSafeInteger(issueNumber)
      || issueNumber < 1 || !plain(baseRef) || baseRef.startsWith('-')) return result('conflict', 'Supply a valid repository, issue, run, workflow and existing local base ref.');
    const c = commands(ports), ctx = await context(cwd, c);
    if (!sameRepo(ctx.repository, repository)) return result('conflict', 'The requested repository does not match this checkout origin.');
    const p = locations(ctx.commonDir, runId, issueNumber);
    if (await exists(p.run)) {
      const a = await ownedRecord(ctx, runId);
      if (!sameRepo(a.repository, repository) || a.issueNumber !== issueNumber || a.workflowName !== workflowName || a.baseRef !== baseRef)
        return result('conflict', 'This run already names a different issue, workflow or base.');
      return await reconcile(ctx, a, c);
    }
    if (await exists(p.issue)) return result('conflict', 'This issue already has a persistent worktree claim in this repository.');
    for (const directory of [p.root, p.index, p.runs, p.issues, p.worktrees]) await ensureDirectory(directory);
    const fullRef = (await c.git(ctx.sourceRoot, ['rev-parse', '--symbolic-full-name', '--verify', '--end-of-options', baseRef])).trim();
    if (!fullRef.startsWith('refs/')) fail();
    const baseSha = (await c.git(ctx.sourceRoot, ['rev-parse', '--verify', '--end-of-options', `${baseRef}^{commit}`])).trim();
    if (!SHA.test(baseSha)) fail();
    const id = randomUUID(), branch = branchName(workflowName, issueNumber, id);
    await c.git(ctx.sourceRoot, ['check-ref-format', '--branch', branch]);
    const branchExists = await c.raw(ctx.sourceRoot, ['show-ref', '--verify', '--quiet', 'refs/heads/' + branch]);
    if (branchExists.code !== 1) return result('conflict', 'Cannot establish an unused branch for this allocation.');
    const a = { version: 1, runId, repository, issueNumber, workflowName, commonDir: ctx.commonDir, sourceRoot: ctx.sourceRoot,
      worktreePath: join(p.worktrees, id), gitDir: join(ctx.commonDir, 'worktrees', id), branch, baseRef, baseSha };
    if (await exists(a.worktreePath) || await exists(a.gitDir)) return result('conflict', 'The intended worktree path or Git directory is already occupied.');
    let handle;
    try { handle = await open(p.run, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600); }
    catch (error) { if (error.code === 'EEXIST') return result('recovery_required', 'This run was claimed concurrently. Read its original assignment; do not allocate again.'); throw error; }
    saved = true;
    try { await handle.writeFile(JSON.stringify(a) + '\n', 'utf8'); await handle.sync(); } finally { await handle.close(); }
    await syncDirectory(p.runs);
    try { await link(p.run, p.issue); }
    catch (error) { if (error.code === 'EEXIST') return result('conflict', 'Another run claimed this issue. This run intent is retained without allocating.'); throw error; }
    await syncDirectory(p.issues);
    // Intent and exclusive claim are durable. No existing intent can ever enter this add path again.
    if (!equal(await ownedRecord(ctx, runId), a)) fail();
    try { await c.git(ctx.sourceRoot, ['worktree', 'add', '-b', a.branch, a.worktreePath, a.baseSha]); }
    catch { /* A lost or rejected reply cannot justify a second add. Verify this same physical identity. */ }
    return await reconcile(ctx, a, c);
  } catch {
    return result('recovery_required', saved
      ? 'Allocation is unconfirmed. Preserve the saved run and inspect its exact intended path; never repeat add or delete work.'
      : 'Cannot establish repository or allocation metadata identity. No new worktree is confirmed.');
  }
}
