// Owned by prompts/cli/autopilot-cleanup.prompt.md.
import { resolve } from 'node:path';
import { listRuns, readRun } from './workflow-runs.mjs';
import { lookupIssueWorktree } from './workflow-worktree.mjs';
import { runAgentProcess } from './agent-adapters.mjs';
const ended = run => ['completed', 'cancelled'].includes(run?.state) && !run.gate;
const identity = run => JSON.stringify([run?.runId, run?.root, run?.branch, run?.state, run?.repo]);
export async function cleanupWorktrees({ cwd, repository }, ports = {}) {
  const result = { removed: [], kept: [] };
  const runs = () => (ports.listRuns ?? (input => listRuns(input, { execFile: async (file, args, options) => {
    const row = await execute(file, args, options); if (row.code !== 0) throw Error('unavailable'); return row;
  } })))({ cwd, cancelled: true });
  const execute = ports.execute ?? ((file, args, options) => runAgentProcess(file, args, { ...options, timeoutMs: 10_000, maxBytes: 1024 * 1024 }));
  const command = async (file, args, at) => { const row = await execute(file, args, { cwd: at }); if (row.code !== 0) throw Error('unavailable'); return row.stdout.trim(); };
  const git = (args, at) => command('git', args, at);
  const read = ports.readRun ?? readRun;
  const lookup = ports.lookup ?? (input => lookupIssueWorktree(input, { execFile: async (file, args, options) => {
    const row = await execute(file, args, options); return { ...row, code: row.code };
  } }));
  const lock = ports.lock ?? (async run => (await import('./workflow-runner.mjs')).acquireRunLock(run.runDir));
  let rows; try { rows = await runs(); } catch { return result; }
  const protectedRoot = (list, root) => list.some(run => !ended(run) && run.root === root);
  for (const observed of rows) {
    let run = observed;
    if (!ended(run) || run.repo?.toLowerCase() !== repository.toLowerCase()) continue;
    let release;
    try {
      if (![run.root, run.branch, run.runDir, run.runId, run.sourceRoot].every(value => typeof value === 'string' && value)
        || resolve(run.root) === resolve(cwd) || protectedRoot(rows, run.root)) throw Error('keep');
      const current = await read(run.runDir);
      if (current?.runId !== run.runId) {
        const archive = `${run.runDir}-cancelled-${run.runId.slice(0, 8)}`;
        const archived = await read(archive);
        if (!ended(archived) || identity(archived) !== identity(run)) throw Error('keep');
        run = { ...run, runDir: archive };
      }
      release = await lock(run);
      const same = async () => { const current = await read(run.runDir); return ended(current) && identity(current) === identity(run); };
      if (!await same()) throw Error('keep');
      const owned = await lookup({ cwd, runId: run.runId, branch: run.branch });
      const a = owned.assignment;
      if (owned.state !== 'ready' || a?.worktreePath !== run.root || a?.branch !== run.branch || a?.runId !== run.runId) throw Error('keep');
      const prs = JSON.parse(await command('gh', ['pr', 'list', '--repo', repository, '--state', 'all', '--head', run.branch,
        '--limit', '100', '--json', 'state,headRefName'], cwd));
      if (!Array.isArray(prs) || !prs.length || prs.length >= 100 || prs.some(pr => pr.headRefName !== run.branch || !['CLOSED', 'MERGED'].includes(pr.state))) throw Error('keep');
      const clean = async () => {
        if (await git(['symbolic-ref', '--quiet', '--short', 'HEAD'], run.root) !== run.branch) return false;
        if (await git(['status', '--porcelain=v1', '--untracked-files=all'], run.root)) return false;
        if (await git(['rev-list', '--count', '@{upstream}..HEAD'], run.root) !== '0') return false;
        const head = await git(['rev-parse', '--verify', 'HEAD'], run.root);
        return /^[0-9a-f]{40,64}$/.test(head) && head === await git(['rev-parse', '--verify', '@{upstream}'], run.root);
      };
      if (!await clean() || !await same() || protectedRoot(await runs(), run.root)) throw Error('keep');
      await git(['worktree', 'remove', run.root], run.sourceRoot);
      result.removed.push(run.runId);
    } catch { result.kept.push(run.runId); }
    finally { release?.(); }
  }
  return result;
}
