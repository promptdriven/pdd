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

const FAILING_STATUSES = new Set(['prompt-stale', 'deleted']);
const reminderFor = mod => `Verify ${mod.owner} still matches ${mod.path} (OK for pure bugfixes or split prompt/code PRs).`;

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
  ) {
    const widened = analyzeChangedMap({ cwd, all: true }, ports);
    if (widened.error !== null) {
      return { ok: false, exitCode: widened.exitCode, error: widened.error, report: null, root: null };
    }
    analyzed = {
      ...widened,
      report: {
        ...widened.report,
        scope: { ...widened.report.scope, widened_from: 'working-tree' },
      },
    };
  }

  const base = analyzed.report;
  const drifted = base.modules
    .filter(mod => FAILING_STATUSES.has(mod.status))
    .map(mod => ({ path: mod.path, owner: mod.owner, status: mod.status }));
  const reminders = base.modules
    .filter(mod => mod.status === 'changed')
    .map(mod => ({ path: mod.path, owner: mod.owner, status: mod.status, message: reminderFor(mod) }));
  const ok = mode === 'check' ? drifted.length === 0 : true;
  const exitCode = mode === 'check' && drifted.length > 0 ? 1 : 0;

  const modsByPrompt = new Map();
  for (const mod of base.modules) {
    if (!modsByPrompt.has(mod.owner)) modsByPrompt.set(mod.owner, []);
    modsByPrompt.get(mod.owner).push(mod);
  }
  const instructionsFor = group => {
    const rows = modsByPrompt.get(group.prompt) ?? [];
    const out = [];
    const stale = rows.filter(r => r.status === 'prompt-stale').map(r => r.path);
    if (stale.length) {
      out.push(`Legacy header hash disagrees with ${group.prompt} for ${stale.join(', ')}; verify behavior and update or remove the legacy sha256 header.`);
    }
    const deleted = rows.filter(r => r.status === 'deleted').map(r => r.path);
    if (deleted.length) {
      out.push(`Bound module(s) missing on disk (${deleted.join(', ')}); remove stale entries from pdd-bindings.json or restore the file.`);
    }
    for (const mod of rows.filter(r => r.status === 'changed')) {
      out.push(reminderFor(mod));
    }
    if (out.length) return out;
    if (group.status === 'reconciled') return [`Co-changed with ${group.prompt}; reconciled.`];
    if (group.prompt_changed) {
      return [`${group.prompt} changed without code edits; verify owned modules (${group.modules.join(', ')}) match (OK for prompt-first PRs).`];
    }
    return ['In sync; no action needed.'];
  };

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
        instructions: instructionsFor(group),
      })),
      modules: base.modules,
      unowned: base.unowned,
      drifted,
      reminders,
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
