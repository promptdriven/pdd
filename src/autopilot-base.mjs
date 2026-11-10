// Generated from prompts/cli/autopilot-base.prompt.md (sha256: 70c9aed4bcad412a3db9ba4341c255eff72f2681bb0a4bf1250b4ae9316d7eed).
import * as nativeFs from 'node:fs';
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { nativeGithubCounter } from './github-calls.mjs';
import { readSuiteReceipt } from './test-suite-queue.mjs';
import { findVerificationRecipe, judgeRealValidation, judgeSuiteReceipt } from './workflow-pr-evidence.mjs';

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
export function verificationRecipeStatePath(run) {
  const common = run?.commonDir ?? (run?.sourceRoot ? join(run.sourceRoot, '.git') : run?.root ? join(run.root, '.git') : null);
  return common ? join(common, 'pdd', 'verification-recipe.json') : null;
}

export function readVerificationRecipeState(run, fsPort = nativeFs) {
  const root = run?.sourceRoot ?? run?.root ?? null;
  const found = findVerificationRecipe(root, fsPort);
  const statePath = verificationRecipeStatePath(run);
  let prRecord = null;
  if (statePath) {
    try { prRecord = JSON.parse(fsPort.readFileSync(statePath, 'utf8')); } catch {}
  }
  if (found.present || prRecord?.status === 'merged') {
    return { present: true, waiting: false, recipe: found.recipe ?? prRecord?.recipe ?? 'docs/verification-recipe.md', path: found.path ?? prRecord?.path ?? 'docs/verification-recipe.md', prRecord };
  }
  return { present: false, waiting: true, recipe: null, path: null, prRecord };
}

function writeVerificationRecipeState(run, prRecord, fsPort = nativeFs) {
  const statePath = verificationRecipeStatePath(run);
  if (!statePath) return;
  fsPort.mkdirSync(dirname(statePath), { recursive: true });
  fsPort.writeFileSync(statePath, JSON.stringify(prRecord, null, 2) + '\n');
}

export function draftVerificationRecipeText(root, fsPort = nativeFs) {
  let testCmd = 'npm test';
  try {
    const pkg = JSON.parse(fsPort.readFileSync(join(root, 'package.json'), 'utf8'));
    if (typeof pkg?.scripts?.test === 'string' && pkg.scripts.test.trim()) testCmd = pkg.scripts.test.trim();
  } catch {}
  return [
    '# Verification',
    '',
    '## Verification',
    '',
    '- **Setup:** clean checkout with dependencies installed.',
    `- **Run:** \`${testCmd}\``,
    '- **Expected result:** the real product behavior reproduces the reported defect on the old code and passes on the new code with exit code 0.',
    '- **Teardown:** remove any temporary files created during the check.',
    '',
  ].join('\n');
}

export async function ensureVerificationRecipe(run, ports = {}) {
  const fsPort = ports.fs ?? nativeFs;
  if (!run || !['bug', 'feature'].includes(run.workflow)) return { present: true, waiting: false, prRecord: null };
  const state = readVerificationRecipeState(run, fsPort);
  if (state.present) return state;
  const existing = state.prRecord;
  if (existing && Number.isSafeInteger(existing.pr) && existing.pr > 0) {
    const waitingRuns = [...new Set([...(existing.waitingRuns ?? []), run.number].filter(Number.isSafeInteger))].sort((a, b) => a - b);
    const updated = {
      ...existing,
      waitingRuns,
      groupedQuestion: {
        id: existing.groupedQuestion?.id ?? `verification-recipe-${existing.pr}`,
        pr: existing.pr,
        url: existing.url,
        waitingRuns,
        questionCount: 1,
        text: `Review and merge the verification recipe small-change PR #${existing.pr} once so waiting bug/feature runs (${waitingRuns.map(n => `#${n}`).join(', ')}) can verify and merge.`,
      },
    };
    writeVerificationRecipeState(run, updated, fsPort);
    if (run.runDir && updated.draftContent) {
      try { fsPort.writeFileSync(join(run.runDir, 'draft-verification-recipe.md'), updated.draftContent); } catch {}
    }
    return { present: false, waiting: true, recipe: null, path: null, prRecord: updated };
  }
  const sourceRoot = run.sourceRoot ?? run.root;
  const baseBranch = run.baseBranch ?? 'main';
  const branch = 'pdd/verification-recipe';
  const draftContent = draftVerificationRecipeText(sourceRoot, fsPort);
  const workDir = join(run.commonDir ?? join(sourceRoot, '.git'), 'pdd', 'verification-recipe-worktree');
  let prNumber = null, prUrl = null, headSha = null;
  try {
    try { fsPort.rmSync(workDir, { recursive: true, force: true }); } catch {}
    await command(ports, sourceRoot, 'git', ['worktree', 'add', '--detach', workDir, baseBranch]);
    fsPort.mkdirSync(join(workDir, 'docs'), { recursive: true });
    fsPort.writeFileSync(join(workDir, 'docs', 'verification-recipe.md'), draftContent);
    await command(ports, workDir, 'git', ['add', 'docs/verification-recipe.md']);
    await command(ports, workDir, 'git', ['commit', '-qm', 'chore(verification): draft repository verification recipe']);
    headSha = (await command(ports, workDir, 'git', ['rev-parse', 'HEAD'])).trim();
    await command(ports, workDir, 'git', ['push', 'origin', `HEAD:refs/heads/${branch}`]);
    const body = [
      '<!-- pdd-workflow:verification-recipe:small-change -->',
      '⏳ Waiting for a person to review and merge the repository verification recipe',
      '',
      '## Summary',
      '',
      '- **Problem:** This repository has no verification recipe (`docs/verification-recipe.md` or `## Verification` in `AGENTS.md`).',
      '- **Change:** Draft `docs/verification-recipe.md` once as a `small-change` PR so a person can review it once.',
      '- **Result:** Bug and feature Autopilot merges wait for this recipe PR with one grouped question instead of one per run.',
      '',
      '**Merge:** waiting for a person to merge.',
    ].join('\n');
    const out = (await command(ports, workDir, 'gh', ['pr', 'create', '--repo', run.repo, '--base', baseBranch, '--head', branch, '--title', 'chore(verification): draft repository verification recipe', '--body', body])).trim();
    prUrl = out.split(/\r?\n/).find(line => /^https?:\/\//.test(line.trim()))?.trim() ?? out;
    const match = /\/pull\/(\d+)/.exec(prUrl);
    prNumber = match ? Number(match[1]) : 1;
  } finally {
    try { await command(ports, sourceRoot, 'git', ['worktree', 'remove', '--force', workDir]); } catch {}
    try { fsPort.rmSync(workDir, { recursive: true, force: true }); } catch {}
  }
  const waitingRuns = [run.number].filter(Number.isSafeInteger);
  const prRecord = {
    schema: 'pdd.verification-recipe.v1',
    repo: run.repo,
    baseBranch,
    branch,
    path: 'docs/verification-recipe.md',
    recipe: 'docs/verification-recipe.md',
    pr: prNumber,
    url: prUrl,
    headSha,
    status: 'open',
    workflow: 'small-change',
    createdByRun: run.number,
    waitingRuns,
    draftContent,
    groupedQuestion: {
      id: `verification-recipe-${prNumber}`,
      pr: prNumber,
      url: prUrl,
      waitingRuns,
      questionCount: 1,
      text: `Review and merge the verification recipe small-change PR #${prNumber} once so waiting bug/feature runs (${waitingRuns.map(n => `#${n}`).join(', ')}) can verify and merge.`,
    },
  };
  writeVerificationRecipeState(run, prRecord, fsPort);
  if (run.runDir) {
    try { fsPort.writeFileSync(join(run.runDir, 'draft-verification-recipe.md'), draftContent); } catch {}
  }
  return { present: false, waiting: true, recipe: null, path: null, prRecord };
}

function readRealValidationFile(runDir, fsPort = nativeFs) {
  if (!runDir) return { content: '', error: 'missing' };
  const file = join(runDir, 'real-validation.json');
  try {
    if (!fsPort.lstatSync(file).isFile()) return { content: '', error: 'not-a-file' };
    return { content: fsPort.readFileSync(file, 'utf8'), error: '' };
  } catch (error) {
    return { content: '', error: error.code === 'ENOENT' ? 'missing' : 'unreadable' };
  }
}

export async function checkAutopilotBase({ run, pr }, ports = {}) {
  const refuse = message => ({ exitCode: 1, message: `Automatic merge refused: ${message}` });
  if (!run || !repositoryName(run.repo) || !branchName(run.baseBranch) || !/^[1-9][0-9]*$/.test(String(pr))
    || !(run.pr ?? []).some(item => String(item.number) === String(pr))) return refuse('the saved run, base or PR identity is unavailable.');
  const savedPr = (run.pr ?? []).find(item => String(item.number) === String(pr));
  const base = run.baseBranch, repo = run.repo, fsPort = ports.fs ?? nativeFs;
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
    if (pull.merged !== true && pull.head !== undefined && savedPr?.stage !== 'prompt-pr') {
      const headSha = typeof pull.head?.sha === 'string' ? pull.head.sha.trim().toLowerCase() : '';
      if (!/^[a-f0-9]{40}$/.test(headSha)) return refuse(`PR #${pr} head SHA is unavailable.`);
      stage = 'full-suite receipt';
      const rawReceipt = (ports.readSuiteReceipt ?? readSuiteReceipt)({ cwd: run.root, headSha, env: ports.env ?? process.env }, ports.suitePorts ?? {});
      const receiptVerdict = judgeSuiteReceipt(rawReceipt, { headSha });
      if (receiptVerdict.status !== 'passed') return refuse(`PR #${pr} full-suite receipt check failed: ${receiptVerdict.reason}.`);
      if (['bug', 'feature'].includes(run.workflow)) {
        stage = 'verification recipe';
        let recipeState = readVerificationRecipeState(run, fsPort);
        if (!recipeState.present && recipeState.prRecord?.pr) {
          try {
            const recipePull = await api(`repos/${repo}/pulls/${recipeState.prRecord.pr}`);
            if (recipePull?.merged === true) {
              const mergedRecord = { ...recipeState.prRecord, status: 'merged', waiting: false };
              writeVerificationRecipeState(run, mergedRecord, fsPort);
              recipeState = { present: true, waiting: false, recipe: mergedRecord.recipe, path: mergedRecord.path, prRecord: mergedRecord };
            }
          } catch {}
        }
        if (!recipeState.present) {
          recipeState = await ensureVerificationRecipe(run, { ...ports, fs: fsPort });
          const prInfo = recipeState.prRecord?.pr ? `small-change PR #${recipeState.prRecord.pr}` : 'verification recipe PR';
          const questionText = recipeState.prRecord?.groupedQuestion?.text ?? 'Review and merge the verification recipe small-change PR once.';
          return refuse(`PR #${pr} is waiting for the repository verification recipe (${prInfo}). ${questionText}`);
        }
        stage = 'fresh-verifier real validation';
        const builderSessions = (run.chats ?? []).filter(chat => ['spec', 'code', 'build', 'change'].includes(chat.area)).map(chat => chat.session?.id).filter(Boolean);
        const rawReal = readRealValidationFile(run.runDir, fsPort);
        const realVerdict = judgeRealValidation(rawReal, { runId: run.runId, workflow: run.workflow, headSha, builderSessions });
        if (realVerdict.status !== 'passed') return refuse(`PR #${pr} fresh-verifier real validation held: ${realVerdict.reason}.`);
      }
    }
    return { exitCode: 0, message: `Base check: PR #${pr} targets saved base ${base}; contains default branch ${defaultBranch} and ${latest ? `newest release tag ${latest.tag_name}` : 'no published release is present'}.` };
  } catch { return refuse(`${base}: could not verify ${stage}; retry the read before merging.`); }
}
