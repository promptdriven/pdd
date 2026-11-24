// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Single-pass PDD-files-only project lint orchestrator (Layer-1 Core: ZERO autopilot/, ZERO runtime-seam/).
import { spawnSync } from 'node:child_process';
import { realpathSync } from 'node:fs';
import { posix } from 'node:path';
import { findTestPromptViolations, headerEntries, isTestOwnedPath, resolveOwners } from '../../file-owner.mjs';
import { auditProductPlan } from '../../product-documents.mjs';
import { isLintableStoryPath, lintStory } from '../../story-lint.mjs';
import { gitFiles } from '../../shared/git-context.mjs';
import { causeText, isSecretPath } from '../../shared/safe-read.mjs';
import { workspace } from '../../shared/workspace-policy.mjs';
import { HEAD_BYTES, canonicalRepoPath, formatDiagnosticLine, formatTeachingDetail, readSafeHeadUtf8, readSafeUtf8, scrubChildEnv } from './diagnostics.mjs';
import {
  EXAMPLE_DIR,
  FIXTURE_DIR,
  extractBoundModules,
  isContractDocPath,
  isCustomRuleTestFile,
  isEligibleProductionCodeFile,
  scenarioPromptRefs,
} from './lint-scope.mjs';
import { collectNativeOnlyContractFindings } from './native-only-contract.mjs';
import { collectNativeOnlyPortParityFindings } from './native-port-parity.mjs';
import { evaluateCustomRulesOnFile, loadBaseTrustedLintOverrides, loadProjectLintConfig, matchesAnyCustomRule } from './project-config.mjs';
import { extractDependencyLinkTargets, isNativeOnlyPrompt } from './prompt-metadata.mjs';
import { collectPromptCodeBlockFindings, collectPromptDependencyFindings, collectPromptSizeFindings, collectPromptStructureFindings } from './prompt-rules.mjs';
import { collectStoryUnboundCriteriaFindings } from './story-criteria-parity.mjs';

const PROMPT_SIZE_MIN_CODE_LINES = 25;
const STORY_HARD_ERROR_RULES = new Set(['story-missing-criteria']);
const NON_SUPPRESSIBLE_CONFIG_CODES = new Set(['lint-config-invalid', 'lint-config-untrusted']);

function resolveTargetStories({ realRoot, scopedFiles, scopedSet, promptPaths, tests, targetPrompts }) {
  if (promptPaths === undefined && tests === undefined) return scopedFiles.filter(isLintableStoryPath);
  const byStem = new Map();
  for (const f of scopedFiles) {
    if (!isLintableStoryPath(f)) continue;
    const stem = posix.basename(f).replace(/\.md$/i, '');
    if (!byStem.has(stem)) byStem.set(stem, []);
    byStem.get(stem).push(f);
  }
  const inferStory = (doc, scenarioPath) => {
    if (typeof doc?.story_path === 'string' && doc.story_path.trim()) return doc.story_path.trim().replace(/^\.\//, '');
    if (!doc || typeof doc !== 'object' || Array.isArray(doc)) return null;
    const base = posix.basename(scenarioPath, '.json');
    const owners = byStem.has(base) ? [base] : [];
    for (let at = base.lastIndexOf('.'); at > 0; at = base.lastIndexOf('.', at - 1)) if (byStem.has(base.slice(0, at))) owners.push(base.slice(0, at));
    return owners.length === 1 && (byStem.get(owners[0]) ?? []).length === 1 ? byStem.get(owners[0])[0] : null;
  };
  const candidates = new Set();
  if (Array.isArray(tests)) {
    for (const entry of tests) {
      if (entry && typeof entry === 'object' && typeof entry.storyPath === 'string') candidates.add(entry.storyPath.replace(/^\.\//, ''));
      const tPath = typeof entry === 'string' ? entry.replace(/^\.\//, '') : entry?.path?.replace(/^\.\//, '');
      if (!tPath || !scopedSet.has(tPath)) continue;
      if (isLintableStoryPath(tPath)) candidates.add(tPath);
      else if (tPath.endsWith('.json')) {
        const raw = readSafeUtf8(realRoot, tPath);
        if (raw) try { const s = inferStory(JSON.parse(raw), tPath); if (s) candidates.add(s); } catch {}
      }
    }
  } else if (Array.isArray(promptPaths) && targetPrompts.length > 0) {
    const pSet = new Set(targetPrompts);
    for (const sc of scopedFiles.filter(p => /^(?:tests?|__tests__)\/.*\.json$/i.test(p))) {
      const raw = readSafeUtf8(realRoot, sc);
      if (!raw) continue;
      try { const doc = JSON.parse(raw), s = inferStory(doc, sc); if (s && scenarioPromptRefs(doc).some(r => pSet.has(r))) candidates.add(s); } catch {}
    }
  }
  return [...candidates].filter(p => scopedSet.has(p) && isLintableStoryPath(p)).sort();
}

export function runConfiguredLintCommands({ root, commands = [], timeoutMs = 120_000, env = process.env } = {}, ports = {}) {
  const results = [], errors = [];
  if (!Array.isArray(commands) || !commands.length) return { ok: true, results, errors };
  const runner = ports.spawnSync ?? spawnSync;
  const scrubbedEnv = scrubChildEnv(env);
  for (const item of commands) {
    const id = item?.id ?? 'lint-command', command = item?.command;
    if (typeof command !== 'string' || !command.trim()) continue;
    const proc = runner(command, { cwd: root, env: scrubbedEnv, shell: true, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
    const exitCode = typeof proc.status === 'number' ? proc.status : 1;
    const ok = exitCode === 0 && !proc.error && !proc.signal;
    const summary = causeText(proc.stderr || proc.stdout || proc.error?.message || (proc.signal ? `signal ${proc.signal}` : ''));
    results.push({ id, command, ok, exitCode, signal: proc.signal ?? null, summary });
    if (!ok) {
      const detail = formatTeachingDetail({
        invariant: `Configured native linter "${id}" (\`${command}\`) exited with ${proc.signal ? `signal ${proc.signal}` : `code ${exitCode}`}${summary ? `: ${summary}` : ''}`,
        fix: `Fix the reported issues from \`${command}\``,
        rerun: command,
      });
      errors.push(`Error: native lint command: pdd.json:1 [lint-command-failed:${id}] ${detail}`);
    }
  }
  return { ok: errors.length === 0, results, errors };
}

export function lintRepoProject({ root, files, promptPaths, tests, scope, config, workspaceRoot, workspacePolicy, trustBaseRef, enforceBaseTrust = false, requireFullStoryCriteria = false } = {}) {
  const empty = { ok: true, configured: false, warnings: [], errors: [], findings: [], commands: [], untrustedConfigOverrides: [] };
  if (!root || typeof root !== 'string') return empty;
  let realRoot, policy;
  try {
    realRoot = realpathSync(root);
    policy = workspacePolicy ?? workspace.policy({ root: typeof workspaceRoot === 'string' && workspaceRoot.trim() ? realpathSync(workspaceRoot) : realRoot });
  } catch { return empty; }

  let rawFiles;
  try { rawFiles = Array.isArray(files) ? files : (Array.isArray(scope?.effectiveFiles) ? scope.effectiveFiles : gitFiles(realRoot)); } catch { return empty; }

  const lintConfig = loadProjectLintConfig(config !== undefined ? config : realRoot);
  let effectiveDisabled = lintConfig.disabledRules;
  let effectiveSeverities = lintConfig.ruleSeverities;
  const untrustedConfigOverrides = [];
  if (config === undefined && (enforceBaseTrust || trustBaseRef !== undefined)) {
    const baseTrusted = loadBaseTrustedLintOverrides(realRoot, { baseRef: trustBaseRef });
    effectiveDisabled = new Set(baseTrusted.disabledRules);
    effectiveSeverities = new Map(baseTrusted.ruleSeverities);
    for (const id of lintConfig.disabledRules) {
      if (!baseTrusted.disabledRules.has(id)) {
        untrustedConfigOverrides.push(`${id} (disable)`);
      }
    }
    for (const [id, wtSev] of lintConfig.ruleSeverities.entries()) {
      const baseSev = baseTrusted.ruleSeverities.get(id);
      if (wtSev === 'error') {
        effectiveSeverities.set(id, 'error');
        effectiveDisabled.delete(id);
      } else if (wtSev === 'off') {
        if (baseSev !== 'off' && !baseTrusted.disabledRules.has(id)) {
          if (!untrustedConfigOverrides.includes(`${id} (disable)`)) untrustedConfigOverrides.push(`${id}: off`);
        }
      } else if (wtSev === 'warn') {
        if (baseSev === 'warn' || baseSev === 'off') {
          effectiveSeverities.set(id, 'warn');
          effectiveDisabled.delete(id);
        } else {
          untrustedConfigOverrides.push(`${id}: warn`);
        }
      }
    }
  }

  // Full repository lookup index (always complete so unchanged linked prompts/files resolve cleanly).
  const hasExplicitScope = Boolean(scope && scope.fullRepo === false);
  const allowedFiles = [...new Set(rawFiles)].filter(p => canonicalRepoPath(p) && !isSecretPath(p) && workspace.allows(policy, p)).sort();
  const allowedSet = new Set(allowedFiles);
  const selectedInputs = [
    ...(Array.isArray(promptPaths) ? promptPaths : []).filter(p => typeof p === 'string').map(p => p.replace(/^\.\//, '')),
    ...(Array.isArray(tests) ? tests : []).map(t => (typeof t === 'string' ? t : t?.path)).filter(p => typeof p === 'string').map(p => p.replace(/^\.\//, '')),
    ...(hasExplicitScope ? [...scope.directFiles, ...(scope.deletedOrRenamedOldPaths ?? [])] : []),
  ];
  const scopedFiles = selectedInputs.some(p => FIXTURE_DIR.test(p)) ? allowedFiles : allowedFiles.filter(p => !FIXTURE_DIR.test(p));
  const scopedSet = new Set(scopedFiles);

  const allPrompts = scopedFiles.filter(p => p.endsWith('.prompt.md'));
  const allPromptSet = new Set(allPrompts);
  const prodCodePaths = scopedFiles.filter(isEligibleProductionCodeFile);
  const promptCache = scope?.caches?.promptCache ?? new Map();
  const headCache = scope?.caches?.headCache ?? new Map();
  const fullCache = scope?.caches?.fullCache ?? new Map();
  const getPrompt = p => (promptCache.has(p) ? promptCache.get(p) : (promptCache.set(p, readSafeUtf8(realRoot, p)), promptCache.get(p)));
  const getHead = p => (headCache.has(p) ? headCache.get(p) : (headCache.set(p, readSafeHeadUtf8(realRoot, p, HEAD_BYTES + 1)), headCache.get(p)));
  const getFull = p => (fullCache.has(p) ? fullCache.get(p) : (fullCache.set(p, readSafeUtf8(realRoot, p)), fullCache.get(p)));

  const rawFindings = [...lintConfig.configErrors.map(err => ({ ...err, defaultSeverity: 'error' }))];
  if (untrustedConfigOverrides.length > 0) {
    rawFindings.push({
      filePath: 'pdd.json',
      line: 1,
      order: 0,
      code: 'lint-config-untrusted',
      category: 'lint config',
      defaultSeverity: 'warn',
      detail: formatTeachingDetail({
        invariant: `Working-tree/branch lint overrides (${untrustedConfigOverrides.join(', ')}) are not yet trusted on merge base and were ignored`,
        fix: 'Fix the underlying lint errors instead of disabling or weakening lint rules in pdd.json or rules/lint/*.json',
        rerun: 'pdd lint --diff',
      }),
    });
  }

  const ownedByPrompt = new Map(), ownersByCode = new Map(), heads = [], brokenHeaderCandidates = [];
  const rawBindings = scopedSet.has('pdd-bindings.json') ? getFull('pdd-bindings.json') : null;
  const boundModulePaths = [...new Set(
    extractBoundModules(rawBindings)
      .map(e => e.module)
      .filter(m => scopedSet.has(m) && !isTestOwnedPath(m) && !m.endsWith('.prompt.md')),
  )];
  const prodCodeSet = new Set(prodCodePaths);
  const extraBoundPaths = boundModulePaths.filter(m => !prodCodeSet.has(m));

  for (const codePath of prodCodePaths) {
    const head = getHead(codePath);
    heads.push({ path: codePath, content: head });
    if (typeof head !== 'string') continue;
    for (const entry of headerEntries(head)) {
      if (!allowedSet.has(entry.prompt)) {
        const line = Math.max(1, head.split(/\r?\n/).findIndex(l => l.includes(entry.prompt)) + 1);
        brokenHeaderCandidates.push({ codePath, line, prompt: entry.prompt });
      }
    }
  }
  for (const extraPath of extraBoundPaths) {
    heads.push({ path: extraPath, content: getHead(extraPath) });
  }

  const ownershipPaths = extraBoundPaths.length ? [...prodCodePaths, ...extraBoundPaths].sort() : prodCodePaths;
  const duplicateOwnerRows = [];
  if (allPrompts.length && ownershipPaths.length) {
    const promptRows = allPrompts.map(p => ({ path: p, content: getPrompt(p) })).filter(r => typeof r.content === 'string');
    for (const row of resolveOwners({ paths: ownershipPaths, allPaths: scopedFiles, bindings: rawBindings, heads, prompts: promptRows }).files) {
      if (!row.owners.length) continue;
      ownersByCode.set(row.path, row.owners);
      for (const o of row.owners) { if (!ownedByPrompt.has(o)) ownedByPrompt.set(o, []); ownedByPrompt.get(o).push(row.path); }
      const validOwners = [...new Set(row.owners.filter(o => allPromptSet.has(o)))].sort();
      if (validOwners.length >= 2) duplicateOwnerRows.push({ path: row.path, owners: validOwners });
    }
  }

  // Determine reporting scope (strictly controls WHICH files are reported, never what exists in lookup index).
  const isLegacyScoped = !hasExplicitScope && (promptPaths !== undefined || tests !== undefined);
  const isReportingScoped = hasExplicitScope || isLegacyScoped;

  const targetPrompts = hasExplicitScope
    ? [...scope.prompts].filter(p => scopedSet.has(p) && p.endsWith('.prompt.md')).sort()
    : (Array.isArray(promptPaths)
      ? [...new Set(promptPaths.filter(p => typeof p === 'string').map(p => p.replace(/^\.\//, '')).filter(p => scopedSet.has(p) && p.endsWith('.prompt.md')))].sort()
      : allPrompts);
  const targetPromptSet = new Set(targetPrompts);

  const reportCodeSet = hasExplicitScope
    ? scope.codeFiles
    : (isLegacyScoped
      ? new Set(ownershipPaths.filter(p => (ownersByCode.get(p) ?? []).some(o => targetPromptSet.has(o))))
      : null);

  for (const { codePath, line, prompt } of brokenHeaderCandidates) {
    if (reportCodeSet && !reportCodeSet.has(codePath)) continue;
    rawFindings.push({
      filePath: codePath, line, order: 1, code: 'broken-prompt-header', category: 'prompt ownership', defaultSeverity: 'error',
      detail: formatTeachingDetail({
        invariant: `Prompt header in ${codePath} references "${prompt}", which does not exist as a Git-visible file`,
        fix: `Update the \`// Prompt:\` / \`// Generated from\` header in ${codePath}:${line} to an existing .prompt.md path or remove it`,
        rerun: 'pdd lint',
      }),
    });
  }

  for (const dup of duplicateOwnerRows) {
    if (reportCodeSet && !reportCodeSet.has(dup.path) && !dup.owners.some(o => targetPromptSet.has(o))) continue;
    rawFindings.push({
      filePath: dup.path, line: 1, order: 2, code: 'duplicate-owner', category: 'prompt ownership', defaultSeverity: 'warn',
      detail: formatTeachingDetail({
        invariant: `${dup.path} is explicitly owned by ${dup.owners.length} prompts (${dup.owners.join(', ')}); one prompt should own each file`,
        fix: `Keep a single owning prompt for ${dup.path} by removing duplicate Prompt headers or pdd-bindings.json entries`,
        rerun: 'pdd lint',
      }),
    });
  }

  if (targetPrompts.length) {
    const check = findTestPromptViolations({ root: realRoot, promptPaths: targetPrompts, checkPaths: [], includeProse: true }, {
      files: () => scopedFiles,
      read: (p, lim) => { const t = p.endsWith('.prompt.md') ? getPrompt(p) : (lim <= HEAD_BYTES + 1 ? getHead(p) : getFull(p)); return typeof t === 'string' ? Buffer.from(t, 'utf8') : null; },
    });
    for (const v of check.violations) {
      rawFindings.push({
        filePath: v.prompt, line: 1, order: 1, code: 'misplaced-test-prompt', category: 'prompt ownership', defaultSeverity: 'warn',
        detail: `${v.message.replace(/^Error:\s*/i, '')} Prompts own production modules, not test files.`,
        fix: v.kind === 'test-prompt-path' ? `Delete ${v.prompt} and keep test assertions in native test files` : `Remove test-file ownership (${v.targets.join(', ')}) from ${v.prompt}`,
      });
    }
    rawFindings.push(...collectPromptDependencyFindings({ targetPrompts, allVisibleFiles: allowedFiles, getPromptText: getPrompt }));
  }

  for (const promptPath of targetPrompts) {
    const content = getPrompt(promptPath);
    if (typeof content !== 'string') continue;
    const ownedPaths = ownedByPrompt.get(promptPath) ?? [];
    const ownedCode = ownedPaths.map(p => ({ path: p, text: getFull(p) })).filter(r => typeof r.text === 'string');

    rawFindings.push(
      ...collectPromptCodeBlockFindings(content, { path: promptPath }),
      ...collectPromptStructureFindings(content, { path: promptPath, hasOwnedCode: ownedPaths.length > 0 }),
      ...collectPromptSizeFindings(content, ownedCode, { path: promptPath, minCodeLines: PROMPT_SIZE_MIN_CODE_LINES }),
    );
    if (isNativeOnlyPrompt(content)) {
      rawFindings.push(...collectNativeOnlyContractFindings(content, { path: promptPath }));
      const direct = extractDependencyLinkTargets(content, promptPath).filter(p => scopedSet.has(p));
      const directCheckable = direct.filter(t => t.endsWith('.prompt.md') && typeof getPrompt(t) === 'string' && !isNativeOnlyPrompt(getPrompt(t)));
      const directNativePeers = direct.filter(t => t.endsWith('.prompt.md') && typeof getPrompt(t) === 'string' && isNativeOnlyPrompt(getPrompt(t)));
      const directContracts = direct.filter(isContractDocPath);
      const visited = new Set([promptPath]);
      const queue = [...directCheckable.map(p => ({ path: p, isPrompt: true })), ...directContracts.map(p => ({ path: p, isPrompt: false }))];
      const depSources = [];
      while (queue.length) {
        const cur = queue.shift();
        if (visited.has(cur.path)) continue;
        visited.add(cur.path);
        const depText = cur.isPrompt ? getPrompt(cur.path) : readSafeUtf8(realRoot, cur.path);
        if (typeof depText !== 'string' || (cur.isPrompt && isNativeOnlyPrompt(depText))) continue;
        depSources.push({ path: cur.path, text: depText, isPrompt: cur.isPrompt });
        for (const next of extractDependencyLinkTargets(depText, cur.path)) {
          if (!visited.has(next) && scopedSet.has(next) && (next.endsWith('.prompt.md') || isContractDocPath(next))) {
            queue.push({ path: next, isPrompt: next.endsWith('.prompt.md') });
          }
        }
      }
      const explicitFrontmatterOnly = directCheckable.length === 0 && (directNativePeers.length > 0 || directContracts.length > 0);
      rawFindings.push(...collectNativeOnlyPortParityFindings(content, depSources, {
        path: promptPath,
        dependencyPaths: directCheckable,
        explicitFrontmatterOnly,
      }));
    }
    if (lintConfig.customRules.length) rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, { filePath: promptPath, kind: 'prompt', rawText: content }));
  }

  const targetStories = hasExplicitScope
    ? [...scope.stories].filter(p => scopedSet.has(p) && isLintableStoryPath(p)).sort()
    : resolveTargetStories({ realRoot, scopedFiles, scopedSet, promptPaths, tests, targetPrompts });
  for (const storyPath of targetStories) {
    const content = getFull(storyPath);
    if (typeof content !== 'string') continue;
    for (const problem of lintStory(content, { path: storyPath, criteriaHygiene: true }).problems) {
      rawFindings.push({
        filePath: storyPath, line: problem.line, order: 10, code: problem.code, category: 'Story hygiene',
        defaultSeverity: STORY_HARD_ERROR_RULES.has(problem.code) ? 'error' : 'warn',
        detail: problem.message,
        fix: problem.fix || `Update ${storyPath}:${problem.line} to satisfy Story hygiene rule "${problem.code}" (see \`pdd help prompting\`)`,
      });
    }
    if (lintConfig.customRules.length) rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, { filePath: storyPath, kind: 'story', rawText: content }));
  }
  if (targetStories.length) {
    rawFindings.push(...collectStoryUnboundCriteriaFindings({ realRoot, storyPaths: targetStories, scopedFiles, readFile: getFull, allowExplicitSubset: !requireFullStoryCriteria }));
  }

  const promptFilterSet = isReportingScoped ? targetPromptSet : null;
  if (lintConfig.customRules.some(r => r.severity !== 'off' && (r.targets.has('test') || r.targets.has('all')))) {
    const customTestPaths = hasExplicitScope
      ? [...scope.testFiles].filter(p => scopedSet.has(p) && isCustomRuleTestFile(p)).sort()
      : (isLegacyScoped ? [] : scopedFiles.filter(isCustomRuleTestFile));
    for (const testPath of customTestPaths) {
      if (!matchesAnyCustomRule(lintConfig.customRules, 'test', testPath)) continue;
      const content = getFull(testPath);
      if (typeof content === 'string') rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, { filePath: testPath, kind: 'test', rawText: content }));
    }
  }
  if (lintConfig.customRules.some(r => r.severity !== 'off' && (r.targets.has('code') || r.targets.has('all')))) {
    const customCodePaths = reportCodeSet
      ? prodCodePaths.filter(p => reportCodeSet.has(p))
      : prodCodePaths;
    for (const codePath of customCodePaths) {
      if (!matchesAnyCustomRule(lintConfig.customRules, 'code', codePath)) continue;
      const content = getFull(codePath);
      if (typeof content === 'string') rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, { filePath: codePath, kind: 'code', rawText: content }));
    }
  }

  // 19L Multi-app product plan audit hook (0ms when product/plan.md does not exist).
  const deletedPrompts = hasExplicitScope
    ? [...(scope.deletedOrRenamedOldPaths ?? [])].filter(p => p.endsWith('.prompt.md'))
    : [];
  const productPromptMatchSet = deletedPrompts.length
    ? new Set([...targetPromptSet, ...deletedPrompts])
    : targetPromptSet;
  const runProductAudit = hasExplicitScope
    ? (scope.productPlan || targetPrompts.length > 0 || deletedPrompts.length > 0)
    : (tests === undefined);
  if (runProductAudit && scopedSet.has('product/plan.md')) {
    const planText = readSafeUtf8(realRoot, 'product/plan.md');
    if (typeof planText === 'string' && planText.trim()) {
      const mapText = scopedSet.has('product/map.md') ? (readSafeUtf8(realRoot, 'product/map.md') ?? '') : '';
      const mentionsExamples = /\bexamples\b/i.test(mapText) || /\bexamples\b/i.test(planText);
      const promptFiles = allPrompts.filter(p => mentionsExamples || !EXAMPLE_DIR.test(p)).map(p => ({ path: p, content: getPrompt(p) })).filter(r => typeof r.content === 'string');
      const filterProductByPrompt = hasExplicitScope ? !scope.productPlan : Boolean(promptFilterSet);
      for (const item of auditProductPlan({ mapText, planText, promptFiles }).findings) {
        if (!filterProductByPrompt || (Array.isArray(item.relatedPrompts) && item.relatedPrompts.some(p => productPromptMatchSet.has(p)))) rawFindings.push({ ...item, defaultSeverity: 'warn' });
      }
    }
  }

  rawFindings.sort((a, b) => a.filePath.localeCompare(b.filePath) || a.line - b.line || (a.order ?? 0) - (b.order ?? 0) || a.code.localeCompare(b.code));
  const warnings = [], errors = [], findings = [], seen = new Set();
  for (const item of rawFindings) {
    if (!NON_SUPPRESSIBLE_CONFIG_CODES.has(item.code) && effectiveDisabled.has(item.code)) continue;
    const severity = NON_SUPPRESSIBLE_CONFIG_CODES.has(item.code)
      ? (item.defaultSeverity ?? 'error')
      : (effectiveSeverities.get(item.code) ?? item.defaultSeverity ?? 'warn');
    if (severity === 'off') continue;
    const formatted = formatDiagnosticLine(item, severity);
    if (seen.has(formatted)) continue;
    seen.add(formatted);
    findings.push({ path: item.filePath, line: item.line, code: item.code, category: item.category, severity, message: item.detail, formatted });
    if (severity === 'error') errors.push(formatted); else warnings.push(formatted);
  }
  return { ok: errors.length === 0, configured: lintConfig.configured, warnings, errors, findings, commands: lintConfig.commands, untrustedConfigOverrides };
}
