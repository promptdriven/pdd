// Layer-0 GitHub repository identifier and URL parsing primitives.
import { execFile as execFileCallback } from 'node:child_process';
import { promisify } from 'node:util';
import { nativeGithubCounter } from '../github-calls.mjs';

const execFileAsync = promisify(execFileCallback);

const REPO_PATTERN = /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/;
const REPO_LAX_PATTERN = /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/;
const CONTROLS = /[\x00-\x1f\x7f]/g;
const nonEmptyText = value => typeof value === 'string' && value.length > 0 && !/[\u0000-\u001f\u007f]/u.test(value);
const fail = code => { throw Object.assign(new Error(code), { code }); };

const executeRaw = (file, args, options) => new Promise((resolveResult, reject) => {
  const { input, ...execOptions } = options;
  const child = execFileCallback(file, args, execOptions, (error, stdout, stderr) => {
    if (error) { error.stdout = stdout; error.stderr = stderr; reject(error); }
    else resolveResult({ stdout, stderr });
  });
  if (input !== undefined) { child.stdin.on('error', () => {}); child.stdin.end(input); }
});

const countedExec = nativeGithubCounter((file, args, { cwd, input }) => executeRaw(file, args, {
  cwd,
  input,
  encoding: 'utf8',
  shell: false,
  maxBuffer: 8 * 1024 * 1024,
}));

/**
 * Case-insensitive comparison of two `owner/repo` strings.
 */
export function sameRepo(a, b) {
  return typeof a === 'string' && typeof b === 'string' && a.toLowerCase() === b.toLowerCase();
}

/**
 * Validate and normalize an `OWNER/REPO` string, rejecting dot segments and malformed input.
 */
export function validateRepoName(repo) {
  if (typeof repo !== 'string' || !REPO_LAX_PATTERN.test(repo.trim())) {
    throw Object.assign(
      new Error(`Invalid repository "${repo ?? ''}". Expected OWNER/REPO (for example "owner/repo").`),
      { code: 'invalid-repo' },
    );
  }
  const trimmed = repo.trim();
  const [owner, name] = trimmed.split('/');
  if (owner === '.' || owner === '..' || name === '.' || name === '..') {
    throw Object.assign(
      new Error(`Invalid repository "${repo}". Expected OWNER/REPO without "." or ".." path segments.`),
      { code: 'invalid-repo' },
    );
  }
  return trimmed;
}

/**
 * Parse a GitHub HTTPS or SSH remote URL into canonical `owner/repo`, or `null` if not a
 * standard GitHub origin URL without credentials, query, port, or fragment.
 */
export function githubOriginRepository(remote) {
  let value = String(remote ?? '').trim();
  if (!value) return null;
  if (value.startsWith('git@github.com:')) value = `https://github.com/${value.slice(15)}`;
  let url;
  try {
    url = new URL(value);
  } catch {
    return null;
  }
  if (
    url.hostname !== 'github.com'
    || url.port
    || url.search
    || url.hash
    || url.password
    || !['https:', 'ssh:'].includes(url.protocol)
    || (url.username && !(url.protocol === 'ssh:' && url.username === 'git'))
  ) {
    return null;
  }
  const repository = url.pathname.slice(1).replace(/\.git$/, '');
  if (!REPO_PATTERN.test(repository)) return null;
  const [owner, name] = repository.split('/');
  if (owner === '.' || owner === '..' || name === '.' || name === '..') return null;
  return repository;
}

/**
 * Parse a GitHub issue URL (`https://github.com/owner/repo/issues/123` or `github.com/owner/repo/issues/123`)
 * into `{ repository, issue }` (lowercase repository, positive safe integer issue), or `null`.
 */
export function parseGitHubIssueUrl(raw) {
  if (typeof raw !== 'string') return null;
  const trimmed = raw.replace(CONTROLS, '').trim().replace(/[.,;:!?)'"\]]+$/, '');
  const candidate = /^https?:\/\//i.test(trimmed)
    ? trimmed
    : (/^github\.com\//i.test(trimmed) ? `https://${trimmed}` : null);
  if (!candidate) return null;
  try {
    const parsed = new URL(candidate);
    if (
      (parsed.protocol !== 'https:' && parsed.protocol !== 'http:')
      || parsed.hostname.toLowerCase() !== 'github.com'
      || parsed.username
      || parsed.password
      || parsed.port
    ) {
      return null;
    }
    const match = /^\/([\w.-]+\/[\w.-]+)\/issues\/([1-9]\d*)\/?$/.exec(parsed.pathname);
    if (!match) return null;
    const issue = Number(match[2]);
    return Number.isSafeInteger(issue) ? { repository: match[1].toLowerCase(), issue } : null;
  } catch {
    return null;
  }
}

/**
 * Resolve `owner/repo` from an explicit `repository` argument or the `origin` remote of `cwd`.
 */
export async function resolveRepository({ cwd = process.cwd(), repository = null, execFile } = {}) {
  if (typeof repository === 'string' && repository.trim()) {
    return validateRepoName(repository);
  }
  const exec = execFile ?? ((file, args, options) => execFileAsync(file, args, { ...options, encoding: 'utf8' }));
  try {
    const res = await exec('git', ['remote', 'get-url', 'origin'], { cwd });
    return githubOriginRepository(String(res?.stdout ?? '').trim());
  } catch {
    return null;
  }
}

/**
 * Resolve and verify the GitHub repository and default branch for `cwd` via `git remote get-url origin`
 * and `gh repo view`, matching strict repository-mismatch diagnostics.
 */
export async function resolveWorkflowRepository({ cwd } = {}, ports = {}) {
  if (!nonEmptyText(cwd)) fail('workflow_github_cwd_required');
  const run = ports.execFile ?? countedExec;
  const command = async (file, args) => {
    let result;
    try {
      result = await run(file, args, { cwd });
    } catch (error) {
      if (!Number.isInteger(error?.code) || error.code === 0) fail('workflow_github_command_unavailable');
      result = { code: error.code, stdout: error.stdout ?? '', stderr: error.stderr ?? '' };
    }
    if (!result || typeof result.stdout !== 'string'
      || (result.code !== undefined && !Number.isInteger(result.code))) {
      fail('workflow_github_command_invalid');
    }
    const code = result.code ?? 0;
    if (code !== 0) {
      throw Object.assign(new Error('workflow_github_command_failed'), {
        code: 'workflow_github_command_failed',
        detail: typeof result.stderr === 'string' ? result.stderr : '',
      });
    }
    return result.stdout;
  };
  const remote = (await command('git', ['remote', 'get-url', 'origin'])).trim();
  const repository = githubOriginRepository(remote);
  if (!repository) fail('workflow_github_origin_invalid');
  let actual;
  try {
    actual = JSON.parse(await command('gh', ['repo', 'view', repository, '--json', 'nameWithOwner,defaultBranchRef,url']));
  } catch (error) {
    if (error?.code?.startsWith('workflow_github_')) throw error;
    fail('workflow_github_json_invalid');
  }
  if (
    !actual
    || !nonEmptyText(actual.nameWithOwner)
    || !REPO_PATTERN.test(actual.nameWithOwner)
    || !sameRepo(actual.nameWithOwner, repository)
    || !nonEmptyText(actual.defaultBranchRef?.name)
    || actual.url !== `https://github.com/${actual.nameWithOwner}`
  ) {
    fail('workflow_github_repository_mismatch');
  }
  return { repository: actual.nameWithOwner, defaultBranch: actual.defaultBranchRef.name };
}
