// Layer-0 GitHub repository identifier and URL parsing primitives.
import { execFile as execFileCallback } from 'node:child_process';
import { promisify } from 'node:util';

const execFileAsync = promisify(execFileCallback);

const REPO_PATTERN = /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/;
const REPO_LAX_PATTERN = /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/;
const CONTROLS = /[\x00-\x1f\x7f]/g;

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
