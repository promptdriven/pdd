// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// 100% offline (<1s) CLI handler for `local: 'lint'` (0 AI, 0 network, 0 batch-state writes, PDD files only + --diff).
import { execFileSync } from 'node:child_process';
import { realpathSync } from 'node:fs';
import { posix } from 'node:path';
import { isLintableStoryPath } from '../../story-lint.mjs';
import { lintSvgLayouts as defaultLintSvgLayouts } from '../../svg-layout.mjs';
import { gitFiles } from '../../shared/git-context.mjs';
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

function resolveScopedTargets(allFiles, words = []) {
  if (!Array.isArray(words) || !words.length) return { promptPaths: undefined, tests: undefined, unmatched: [] };
  const fileSet = new Set(allFiles);
  const prompts = new Set();
  const tests = new Set();
  const unmatched = [];

  for (const raw of words) {
    const word = String(raw ?? '').trim().replace(/^\.\//, '');
    if (!word) continue;
    let matchedAny = false;
    if (fileSet.has(word)) {
      if (word.endsWith('.prompt.md')) { prompts.add(word); matchedAny = true; }
      else if (isLintableStoryPath(word) || word.endsWith('.json')) { tests.add(word); matchedAny = true; }
    }
    if (!matchedAny) {
      const slug = word.replace(/\.md$/i, '').replace(/\.json$/i, '');
      for (const f of allFiles) {
        if (isLintableStoryPath(f) && posix.basename(f, '.md') === slug) { tests.add(f); matchedAny = true; }
        if (/^(?:tests?|__tests__)\/.*\.json$/i.test(f) && posix.basename(f, '.json') === slug) { tests.add(f); matchedAny = true; }
        if (f.endsWith('.prompt.md') && posix.basename(f, '.prompt.md') === slug) { prompts.add(f); matchedAny = true; }
      }
    }
    if (!matchedAny) unmatched.push(word);
  }
  return {
    promptPaths: prompts.size ? [...prompts].sort() : (tests.size ? [] : undefined),
    tests: tests.size ? [...tests].sort() : undefined,
    unmatched,
  };
}

/**
 * Run deterministic offline PDD lint with 0 network calls, 0 AI calls, and 0 batch-state writes.
 * Clean repos print `Local lint: 0 errors, 0 warnings. (0 AI/network calls)` to stdout with empty stderr.
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

  const { promptPaths, tests, unmatched } = resolveScopedTargets(repoFiles, words);
  if (unmatched.length > 0) {
    const problems = unmatched.map(w => `No prompt, Story, or test matched "${w}". Run \`pdd files\` to list available Stories and prompts.`);
    const summaryLine = `Local lint: ${problems.length} unmatched target${problems.length === 1 ? '' : 's'}. (0 AI calls, 0 network calls)`;
    if (json) stdout.write(`${JSON.stringify({ schema_version: 'pdd.local-lint.v1', ok: false, exit_code: 2, local_only: true, summary_line: summaryLine, problems, unmatched, warnings: [], findings: [] }, null, 2)}\n`);
    else { for (const p of problems) stderr.write(`${p}\n`); }
    return 2;
  }
  const resolvedDiffBase = typeof diff === 'string' && diff.trim()
    ? diff.trim()
    : (typeof baseRef === 'string' && baseRef.trim() ? baseRef.trim() : undefined);
  const enforceBaseTrust = Boolean(diff !== undefined && diff !== false && !trustWorkingTree);

  const project = lintRepoProject({
    root,
    files: repoFiles,
    promptPaths,
    tests,
    config,
    workspaceRoot,
    workspacePolicy,
    enforceBaseTrust,
    trustBaseRef: resolvedDiffBase,
  });

  const svgWarnings = [];
  const scenarioErrors = [];
  if (includeSvg && repoFiles.length > 0) {
    try {
      const lintSvg = ports.lintSvgLayouts ?? defaultLintSvgLayouts;
      const rawSvg = lintSvg({
        root,
        files: repoFiles,
        ...(promptPaths !== undefined ? { promptPaths } : {}),
        ...(tests !== undefined ? { tests } : {}),
        includeShortDiagnostics: true,
      });
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

  let diffResult = null;
  if (diff !== undefined && diff !== false) {
    diffResult = (ports.runDiffSpotlight ?? runDiffSpotlight)({ cwd: root, baseRef: resolvedDiffBase });
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
        const changedKeys = [
          ...(trusted.skippedCommands ? ['"lint.commands"'] : []),
          ...(trusted.skippedMutationCommand ? ['"lint.mutation_command"'] : []),
        ].join(' and ') || '"lint.commands"';
        commandWarnings.push(`Warning: lint config: pdd.json:1 [lint-commands-untrusted] Working-tree changes to ${changedKeys} were skipped because only merge-base pdd.json commands are trusted by default.`);
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
