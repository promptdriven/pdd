// Generated from prompts/cli/autopilot-base.prompt.md (sha256: 0e88eee1fa9c731f81dfce090112f791d88320e39c40de9b4bd6fb3b69dd3b48).
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { nativeGithubCounter } from './github-calls.mjs';

const nativeExec = nativeGithubCounter(promisify(execFile));
const named = value => typeof value === 'string' && value.trim().length > 0 && !/[\x00-\x1f\x7f]/.test(value);
const branchName = value => named(value) && value !== 'HEAD' && !value.startsWith('-') && !value.startsWith('refs/');
const repositoryName = value => typeof value === 'string' && /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(value);
function readConfig(cwd) {
  try { return JSON.parse(readFileSync(join(cwd, 'pdd.json'), 'utf8')); }
  catch (error) { if (error.code === 'ENOENT') return {}; throw Error('Cannot read base settings from pdd.json.'); }
}
async function command(ports, cwd, file, args) {
  const result = await (ports.execFile ?? nativeExec)(file, args, { cwd, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 });
  if (!result || result.code !== undefined && result.code !== 0) throw Error('Read failed.');
  return result.stdout;
}
export async function selectAutopilotBase({ cwd, defaultBranch }, ports = {}) {
  const config = await (ports.readConfig ?? readConfig)(cwd);
  if (!config || typeof config !== 'object' || Array.isArray(config)) throw Error('Invalid pdd.json base settings.');
  const base = Object.hasOwn(config.autopilot ?? {}, 'base') ? config.autopilot.base : defaultBranch;
  if (!branchName(base)) throw Error('Automatic base unavailable: set autopilot.base to a branch name or read the repository default branch.');
  try { await command(ports, cwd, 'git', ['check-ref-format', `refs/heads/${base}`]); }
  catch { throw Error('Invalid automatic base branch in pdd.json or repository metadata.'); }
  return base;
}

// Safety observations are fresh. No caller can substitute a prose decision for an ancestry read.
export async function checkAutopilotBase({ run, pr }, ports = {}) {
  const refuse = message => ({ exitCode: 1, message: `Automatic merge refused: ${message}` });
  if (!run || !repositoryName(run.repo) || !branchName(run.baseBranch) || !/^[1-9][0-9]*$/.test(String(pr))
    || !(run.pr ?? []).some(item => String(item.number) === String(pr))) return refuse('the saved run, base or PR identity is unavailable.');
  const base = run.baseBranch, repo = run.repo;
  const api = async (path, options = []) => JSON.parse(await command(ports, run.root, 'gh', ['api', path, ...options]));
  let stage = 'PR target';
  try {
    const pull = await api(`repos/${repo}/pulls/${pr}`);
    if (pull.number !== Number(pr) || !named(pull.base?.ref) || !repositoryName(pull.base?.repo?.full_name)
      || pull.base.repo.full_name.toLowerCase() !== repo.toLowerCase()) return refuse('the PR target could not be verified.');
    if (pull.base.ref !== base) return refuse(`PR #${pr} targets ${pull.base.ref}, but the run saved ${base}.`);
    stage = 'default branch';
    const metadata = await api(`repos/${repo}`), defaultBranch = metadata.default_branch;
    if (!branchName(defaultBranch)) return refuse('the current default branch is unavailable.');
    stage = 'releases';
    const pages = await api(`repos/${repo}/releases?per_page=100`, ['--paginate', '--slurp']);
    if (!Array.isArray(pages) || pages.some(page => !Array.isArray(page))) return refuse('release history is unavailable.');
    const releases = pages.flat();
    if (releases.some(release => !release || typeof release.draft !== 'boolean'
      || !release.draft && (!named(release.tag_name) || !Number.isFinite(Date.parse(release.published_at))))) return refuse('release history is incomplete.');
    const latest = releases.filter(release => !release.draft).sort((a, b) => Date.parse(b.published_at) - Date.parse(a.published_at))[0];
    for (const [ref, description] of [[defaultBranch, 'default branch'], ...(latest ? [[latest.tag_name, 'newest release tag']] : [])]) {
      stage = `${description} ancestry`;
      const comparison = await api(`repos/${repo}/compare/${encodeURIComponent(ref)}...${encodeURIComponent(base)}`);
      if (!Number.isSafeInteger(comparison.behind_by) || comparison.behind_by < 0
        || !['identical', 'ahead', 'behind', 'diverged'].includes(comparison.status)) return refuse(`${base}: ${description} ${ref} ancestry is unavailable.`);
      if (comparison.behind_by > 0 || !['identical', 'ahead'].includes(comparison.status)) return refuse(`${base} does not contain ${description} ${ref} (${comparison.behind_by} commit(s) behind).`);
    }
    return { exitCode: 0, message: `Base check: PR #${pr} targets saved base ${base}; contains default branch ${defaultBranch} and ${latest ? `newest release tag ${latest.tag_name}` : 'no published release is present'}.` };
  } catch { return refuse(`${base}: could not verify ${stage}; retry the read before merging.`); }
}
