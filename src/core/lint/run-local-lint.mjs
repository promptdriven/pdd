// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// 100% offline (<1s) CLI handler for `local: 'lint'` (0 AI, 0 network, 0 batch-state writes, PDD files only + --diff).
import { execFileSync } from 'node:child_process';
import { realpathSync } from 'node:fs';
import { lintSvgLayouts as defaultLintSvgLayouts } from '../../svg-layout.mjs';
import { gitFiles } from '../../shared/git-context.mjs';
import { resolveLintScope } from './lint-scope.mjs';
import { loadBaseTrustedLintCommands } from './project-config.mjs';
import { lintRepoProject, runConfiguredLintCommands } from './project-lint.mjs';
import { runDiffSpotlight } from './test-inventory.mjs';

function resolveGitRoot(cwd) {
  try {
    const out = execFileSync('git', ['rev-parse', '--show-toplevel'], {
      cwd,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
      timeout: 10_000,
    }).trim();
    return out ? realpathSync(out) : realpathSync(cwd);
  } catch {
    return realpathSync(cwd);
  }
}

/**
 * Run deterministic offline PDD lint with 0 network calls, 0 AI calls, and 0 batch-state writes.
 * Clean repos print `Local lint: 0 errors, 0 warnings. (0 AI calls, 0 network calls)` to stdout with empty stderr.
 */
export function runLocalLint(
  {
    cwd = process.cwd(),
    words = [],
    json = false,
    diff = undefined,
    baseRef = undefined,
    runCommands = false,
    trustWorkingTree = false,
    includeSvg = true,
    config,
    workspaceRoot,
    workspacePolicy,
    env = process.env,
  } = {},
  ports = {},
) {
  const stdout = ports.stdout ?? process.stdout;
  const stderr = ports.stderr ?? process.stderr;
  const root = resolveGitRoot(cwd);

  let repoFiles = [];
  try {
    repoFiles = (ports.gitFiles ?? gitFiles)(root);
  } catch (err) {
    const msg = `Local lint failed to list repository files: ${err?.message || String(err)}. Run inside a Git repository.`;
    if (json) stdout.write(`${JSON.stringify({ schema_version: 'pdd.local-lint.v1', ok: false, exit_code: 2, local_only: true, summary_line: msg, problems: [msg], warnings: [], findings: [] }, null, 2)}\n`);
    else stderr.write(`${msg}\n`);
    return 2;
  }

  const isDiffRequested = diff !== undefined && diff !== false;
  const resolvedDiffBase = typeof diff === 'string' && diff.trim()
    ? diff.trim()
    : (typeof baseRef === 'string' && baseRef.trim() ? baseRef.trim() : undefined);
  const enforceBaseTrust = Boolean(isDiffRequested && !trustWorkingTree);
  const targetWords = Array.isArray(words) ? words : [];

  // 1. In --diff mode, compute the Git diff FIRST so base-unavailable fails closed and working-tree deletions are stripped.
  let diffResult = null;
  if (isDiffRequested) {
    diffResult = (ports.runDiffSpotlight ?? runDiffSpotlight)({ cwd: root, baseRef: resolvedDiffBase });
    if (diffResult && diffResult.baseAvailable === false) {
      const problems = diffResult.errors.map(e => e.formatted);
      const warnings = diffResult.advisories.map(a => `Warning: ${a}`);
      const errLabel = `${problems.length} ${problems.length === 1 ? 'error' : 'errors'}`;
      const warnLabel = `${warnings.length} ${warnings.length === 1 ? 'warning' : 'warnings'}`;
      const summaryLine = `Local lint: ${errLabel}, ${warnLabel}. (0 AI calls, 0 network calls)`;
      const payload = {
        schema_version: 'pdd.local-lint.v1',
        ok: false,
        exit_code: 1,
        local_only: true,
        summary_line: summaryLine,
        problems,
        warnings,
        findings: [],
        diff: diffResult,
      };
      if (json) {
        stdout.write(`${JSON.stringify(payload, null, 2)}\n`);
        return 1;
      }
      for (const warn of warnings) stdout.write(`${warn}\n`);
      for (const err of problems) stderr.write(`${err}\n`);
      stdout.write(`${summaryLine}\n`);
      return 1;
    }
  }

  // 2. Build ONE upfront LintScope separating full-repo lookup index from reporting scope.
  const scope = resolveLintScope({
    root,
    cwd,
    files: repoFiles,
    words: targetWords,
    diffEntries: targetWords.length === 0 && diffResult && Array.isArray(diffResult.changedEntries) ? diffResult.changedEntries : null,
    touchedFiles: targetWords.length === 0 && diffResult && !Array.isArray(diffResult.changedEntries) && Array.isArray(diffResult.touchedFiles) ? diffResult.touchedFiles : null,
    extraDeletedPaths: targetWords.length > 0 && diffResult && Array.isArray(diffResult.deletedPaths) ? diffResult.deletedPaths : null,
    workspaceRoot,
    workspacePolicy,
  });

  if (scope.unmatched.length > 0) {
    const problems = scope.unmatched.map(w => `No prompt, Story, or test matched "${w}". Run \`pdd files\` to list available Stories and prompts.`);
    const summaryLine = `Local lint: ${problems.length} unmatched target${problems.length === 1 ? '' : 's'}. (0 AI calls, 0 network calls)`;
    if (json) stdout.write(`${JSON.stringify({ schema_version: 'pdd.local-lint.v1', ok: false, exit_code: 2, local_only: true, summary_line: summaryLine, problems, unmatched: scope.unmatched, warnings: [], findings: [] }, null, 2)}\n`);
    else { for (const p of problems) stderr.write(`${p}\n`); }
    return 2;
  }

  // Combined `--diff` + explicit targets: re-run diff spotlight strictly scoped to the resolved target closure.
  if (isDiffRequested && targetWords.length > 0) {
    const scopePaths = new Set([
      ...scope.directFiles,
      ...scope.prompts,
      ...scope.stories,
      ...scope.scenarios,
      ...scope.codeFiles,
      ...scope.testFiles,
      ...scope.appMaps,
    ]);
    diffResult = (ports.runDiffSpotlight ?? runDiffSpotlight)({ cwd: root, baseRef: resolvedDiffBase, filterPaths: scopePaths });
  }

  const effectiveFiles = scope.effectiveFiles;

  // 3. Run deterministic project lint strictly scoped while keeping full-repo lookup index intact.
  const project = lintRepoProject({
    root,
    files: effectiveFiles,
    scope,
    config,
    workspaceRoot,
    workspacePolicy,
    enforceBaseTrust,
    trustBaseRef: resolvedDiffBase,
  });

  // 4. Run SVG/app-map/scenario layout checks strictly scoped while keeping full-repo lookup index intact.
  const svgWarnings = [];
  const scenarioErrors = [];
  if (includeSvg && effectiveFiles.length > 0) {
    try {
      const lintSvg = ports.lintSvgLayouts ?? defaultLintSvgLayouts;
      const svgArgs = scope.fullRepo
        ? { root, files: effectiveFiles, includeShortDiagnostics: true }
        : {
            root,
            files: effectiveFiles,
            promptPaths: [...scope.prompts].sort(),
            appMapPaths: [...scope.appMaps].sort(),
            scenarioPaths: [...scope.scenarios].sort(),
            includeShortDiagnostics: true,
          };
      const rawSvg = lintSvg(svgArgs);
      if (Array.isArray(rawSvg)) {
        for (const entry of rawSvg) {
          if (typeof entry === 'string' && entry.includes('compact scenario compile failed [')) {
            const m = entry.match(/^Warning:\s*([^\s:(]+)(?:\s*\(([^)]+)\))?:\s*(compact scenario compile failed \[[^\]]+\]:\s*[\s\S]*)$/);
            if (m) {
              const [, filePath, section, detail] = m;
              const locDetail = section ? `(${section}) ${detail}` : detail;
              scenarioErrors.push(`Error: scenario: ${filePath}:1 [compact-scenario-compile] ${locDetail}\n  Fix: Fix the compact scenario structure or operator in ${filePath} (see stories.md in the pdd skill or run \`pdd help prompting\`).\n  Rerun: pdd lint`);
            } else {
              scenarioErrors.push(entry.replace(/^Warning:\s*/, 'Error: scenario: '));
            }
          } else {
            svgWarnings.push(entry);
          }
        }
      }
    } catch {
      // Missing or unconfigured SVG layouts never block offline PDD lint.
    }
  }

  let commandResult = null;
  const commandWarnings = [];
  if (runCommands) {
    let cmdsToRun = [];
    if (trustWorkingTree) {
      cmdsToRun = project.commands;
    } else {
      const trusted = loadBaseTrustedLintCommands(root, { baseRef: resolvedDiffBase });
      cmdsToRun = trusted.commands;
      if (trusted.skippedUntrusted) {
        commandWarnings.push('Warning: lint config: pdd.json:1 [lint-commands-untrusted] Working-tree changes to "lint.commands" were skipped because only merge-base pdd.json commands are trusted by default.');
      }
    }
    if (cmdsToRun.length > 0) {
      commandResult = (ports.runConfiguredLintCommands ?? runConfiguredLintCommands)(
        { root, commands: cmdsToRun, env },
        ports,
      );
    }
  }

  const problems = [
    ...project.errors,
    ...scenarioErrors,
    ...(diffResult ? diffResult.errors.map(e => e.formatted) : []),
    ...(commandResult ? commandResult.errors : []),
  ];
  const warnings = [
    ...new Set([
      ...svgWarnings,
      ...project.warnings,
      ...commandWarnings,
      ...(diffResult ? diffResult.advisories.map(a => `Warning: ${a}`) : []),
    ]),
  ];
  const exitCode = problems.length > 0 ? 1 : 0;
  const ok = exitCode === 0;
  const errLabel = `${problems.length} ${problems.length === 1 ? 'error' : 'errors'}`;
  const warnLabel = `${warnings.length} ${warnings.length === 1 ? 'warning' : 'warnings'}`;
  const summaryLine = `Local lint: ${errLabel}, ${warnLabel}. (0 AI calls, 0 network calls)`;

  const payload = {
    schema_version: 'pdd.local-lint.v1',
    ok,
    exit_code: exitCode,
    local_only: true,
    summary_line: summaryLine,
    problems,
    warnings,
    findings: project.findings,
    ...(diffResult ? { diff: diffResult } : {}),
    ...(commandResult ? { commands: commandResult.results } : {}),
  };

  if (json) {
    stdout.write(`${JSON.stringify(payload, null, 2)}\n`);
    return exitCode;
  }

  for (const warn of warnings) stdout.write(`${warn}\n`);
  for (const err of problems) stderr.write(`${err}\n`);
  stdout.write(`${summaryLine}\n`);
  return exitCode;
}
