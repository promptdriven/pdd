// Generated from prompts/cli/update-sync.prompt.md.
// Read-only compatibility wrapper delegating diff -> owner -> changed-symbols inspection to src/core/changed-map.mjs.
import {
  analyzeChangedMap,
  extractDiffSummary,
  formatChangedMapJson,
  formatChangedMapText,
} from './core/changed-map.mjs';

export { extractDiffSummary };

const WRITE_RETIRED_MESSAGE = [
  'Location: pdd update --write',
  'Invariant: pdd update is read-only and does not write .pdd/sync/ sidecars or rewrite source header hashes.',
  'Fix: inspect affected prompts with read-only `pdd update` (or `pdd status --changed`), update owning *.prompt.md prose directly, and verify with `pdd lint`.',
  'Rerun: pdd update [FILE...] [--from RANGE] [--branch] [--all] [--json]',
].join('\n');

export function analyzeUpdate({ cwd = process.cwd(), files = [], from, all = false, branch = false, check = false, write = false } = {}, ports = {}) {
  if (check && write) {
    return { ok: false, exitCode: 2, error: 'Cannot combine --check and --write.', report: null, root: null };
  }
  if (write) {
    return { ok: false, exitCode: 2, error: WRITE_RETIRED_MESSAGE, report: null, root: null };
  }

  const mode = check ? 'check' : 'plan';
  const isDefaultScope = files.length === 0 && from === undefined && !all && !branch;
  let analyzed = analyzeChangedMap({ cwd, files, from, all, branch }, ports);
  if (analyzed.error !== null) {
    const message = analyzed.error === 'This command works inside a Git repository.'
      ? 'pdd update works inside a Git repository.'
      : analyzed.error;
    return { ok: false, exitCode: analyzed.exitCode, error: message, report: null, root: null };
  }
  if (
    check
    && isDefaultScope
    && analyzed.report.modules.length === 0
    && analyzed.report.prompts.length === 0
    && analyzed.report.scope.files.length === 0
  ) {
    const widened = analyzeChangedMap({ cwd, all: true }, ports);
    if (widened.error === null) {
      analyzed = {
        ...widened,
        report: {
          ...widened.report,
          scope: { ...widened.report.scope, widened_from: 'working-tree' },
        },
      };
    }
  }

  const base = analyzed.report;
  const drifted = base.modules
    .filter(mod => mod.status !== 'current')
    .map(mod => ({ path: mod.path, owner: mod.owner, status: mod.status }));
  const ok = mode === 'check' ? drifted.length === 0 : true;
  const exitCode = mode === 'check' && drifted.length > 0 ? 1 : 0;

  return {
    ok,
    exitCode,
    error: null,
    root: analyzed.root,
    report: {
      schema_version: 'pdd.update-sync.v1',
      ok,
      mode,
      scope: base.scope,
      prompts: base.prompts.map(group => ({
        ...group,
        instructions: group.status === 'current'
          ? ['In sync; no action needed.']
          : [`Review changed files (${group.modules.join(', ')}) and reconcile ${group.prompt} if behavior changed.`],
      })),
      modules: base.modules,
      unowned: base.unowned,
      drifted,
      updated: [],
    },
  };
}

export function formatUpdateJson(report) {
  return formatChangedMapJson(report);
}

export function formatUpdateText(report) {
  return formatChangedMapText(report, `pdd update (${report.mode})`);
}

export function runUpdate(
  { cwd = process.cwd(), files = [], from, all = false, branch = false, check = false, write = false, json = false } = {},
  { stdout = process.stdout, stderr = process.stderr, ...ports } = {},
) {
  const result = analyzeUpdate({ cwd, files, from, all, branch, check, write }, ports);
  if (result.error !== null) {
    stderr.write(`${result.error}\n`);
    return result.exitCode;
  }
  stdout.write(json ? formatUpdateJson(result.report) : formatUpdateText(result.report));
  return result.exitCode;
}
