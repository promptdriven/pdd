// Project lint configuration loader (`pdd.json` "lint" + `rules/lint/*.json`), 100-rule cap, id dedup, base-trusted lint.commands.
import { spawnSync } from 'node:child_process';
import { lstatSync, readdirSync, realpathSync } from 'node:fs';
import { join } from 'node:path';
import { buildLineStarts, lineNumberAt, readSafeUtf8, resolveDefaultBaseRef } from './diagnostics.mjs';
import { countFileLines, countPromptProseLines, stripPromptMetadataPreservingLines } from './prompt-metadata.mjs';
import { compileGlobMatcher, parseRegexSafe } from './regex-safety.mjs';

export const MAX_CUSTOM_RULES = 100;
const MAX_LINT_COMMANDS = 16;
const RULE_ID_RE = /^[A-Za-z0-9][A-Za-z0-9_.-]{0,63}$/;
const VALID_TARGETS = new Set(['prompt', 'story', 'test', 'code', 'all']);
const VALID_SEVERITIES = new Set(['off', 'warn', 'error']);

function mergeLintConfigSection(rawLint, { sourcePath, allowCommands = true, disabledRules, ruleSeverities, customRuleMap, commandMap, configErrors }) {
  const addConfigError = detail => configErrors.push({
    filePath: sourcePath,
    line: 1,
    order: 0,
    code: 'lint-config-invalid',
    category: 'lint config',
    detail,
    fix: `Fix the invalid "lint" configuration entry in ${sourcePath}`,
  });

  if (typeof rawLint !== 'object' || rawLint === null || Array.isArray(rawLint)) {
    addConfigError(`"lint" in ${sourcePath} must be a JSON object.`);
    return;
  }

  if (rawLint.disable !== undefined) {
    if (!Array.isArray(rawLint.disable) || rawLint.disable.some(id => typeof id !== 'string' || !RULE_ID_RE.test(id))) {
      addConfigError(`"lint.disable" in ${sourcePath} must be an array of valid rule IDs.`);
    } else {
      for (const id of rawLint.disable) disabledRules.add(id);
    }
  }

  if (rawLint.rules !== undefined) {
    if (!rawLint.rules || typeof rawLint.rules !== 'object' || Array.isArray(rawLint.rules)) {
      addConfigError(`"lint.rules" in ${sourcePath} must be an object mapping rule IDs to "off", "warn", or "error".`);
    } else {
      for (const [id, spec] of Object.entries(rawLint.rules)) {
        if (!RULE_ID_RE.test(id)) { addConfigError(`Invalid rule ID "${id}" in "lint.rules".`); continue; }
        const sev = typeof spec === 'string' ? spec : (spec && typeof spec === 'object' && !Array.isArray(spec) ? spec.severity : null);
        if (!VALID_SEVERITIES.has(sev)) { addConfigError(`Rule "${id}" in "lint.rules" must use severity "off", "warn", or "error".`); continue; }
        ruleSeverities.set(id, sev);
        if (sev === 'off') disabledRules.add(id);
        else disabledRules.delete(id);
      }
    }
  }

  if (rawLint.commands !== undefined) {
    if (!allowCommands) {
      addConfigError(`"lint.commands" is only permitted in merge-base pdd.json, not ${sourcePath}.`);
    } else if (!Array.isArray(rawLint.commands)) {
      addConfigError(`"lint.commands" in ${sourcePath} must be an array of shell command strings or {id, command} objects.`);
    } else {
      for (let idx = 0; idx < rawLint.commands.length; idx++) {
        const entry = rawLint.commands[idx];
        const cmdObj = typeof entry === 'string'
          ? { id: `cmd-${idx + 1}`, command: entry.trim() }
          : (entry && typeof entry === 'object' && !Array.isArray(entry)
              ? { id: typeof entry.id === 'string' ? entry.id.trim() : `cmd-${idx + 1}`, command: typeof entry.command === 'string' ? entry.command.trim() : '' }
              : null);
        if (!cmdObj || !cmdObj.command || !RULE_ID_RE.test(cmdObj.id)) {
          addConfigError(`Entry ${idx} in "lint.commands" must be a nonblank command string or {id, command} object.`);
          continue;
        }
        if (!commandMap.has(cmdObj.id) && commandMap.size >= MAX_LINT_COMMANDS) {
          addConfigError(`"lint.commands" exceeds the maximum of ${MAX_LINT_COMMANDS} commands.`);
          break;
        }
        commandMap.set(cmdObj.id, cmdObj);
      }
    }
  }

  if (rawLint.custom_rules !== undefined) {
    if (!Array.isArray(rawLint.custom_rules)) {
      addConfigError(`"lint.custom_rules" in ${sourcePath} must be an array of rule objects.`);
    } else {
      for (let idx = 0; idx < rawLint.custom_rules.length; idx++) {
        const rawRule = rawLint.custom_rules[idx];
        if (!rawRule || typeof rawRule !== 'object' || Array.isArray(rawRule)) {
          addConfigError(`Entry ${idx} in "lint.custom_rules" must be an object.`);
          continue;
        }
        const id = rawRule.id;
        if (typeof id !== 'string' || !RULE_ID_RE.test(id)) {
          addConfigError(`Entry ${idx} in "lint.custom_rules" requires a valid "id" (letters, digits, "-", "_", ".").`);
          continue;
        }
        if (!customRuleMap.has(id) && customRuleMap.size >= MAX_CUSTOM_RULES) {
          addConfigError(`"lint.custom_rules" exceeds the maximum of ${MAX_CUSTOM_RULES} custom rules (while adding "${id}").`);
          continue;
        }
        const rawTarget = rawRule.target ?? (rawRule.include ? 'all' : 'prompt');
        const targetList = Array.isArray(rawTarget) ? rawTarget : [rawTarget];
        if (!targetList.length || targetList.some(t => typeof t !== 'string' || !VALID_TARGETS.has(t))) {
          addConfigError(`Custom rule "${id}" has invalid "target" (choose "prompt", "story", "test", "code", or "all").`);
          continue;
        }
        const severity = rawRule.severity ?? 'warn';
        if (!VALID_SEVERITIES.has(severity)) {
          addConfigError(`Custom rule "${id}" has invalid "severity" (choose "off", "warn", or "error").`);
          continue;
        }

        const toGlobs = (val, fieldName) => {
          if (val === undefined) return [];
          const arr = typeof val === 'string' ? [val] : (Array.isArray(val) ? val : null);
          if (!arr || arr.some(g => typeof g !== 'string')) {
            addConfigError(`Custom rule "${id}" field "${fieldName}" must be a glob string or array of strings.`);
            return null;
          }
          const compiled = arr.map(compileGlobMatcher);
          if (compiled.some(r => r === null)) {
            addConfigError(`Custom rule "${id}" field "${fieldName}" contains an invalid glob.`);
            return null;
          }
          return compiled;
        };

        const includeMatchers = toGlobs(rawRule.include, 'include');
        const excludeMatchers = toGlobs(rawRule.exclude, 'exclude');
        if (includeMatchers === null || excludeMatchers === null) continue;

        let forbidRegex = null;
        if (rawRule.forbid_pattern !== undefined) {
          forbidRegex = parseRegexSafe(rawRule.forbid_pattern, rawRule.flags ?? '');
          if (!forbidRegex) { addConfigError(`Custom rule "${id}" has an invalid "forbid_pattern" regular expression.`); continue; }
        }
        let requireRegex = null;
        if (rawRule.require_pattern !== undefined) {
          requireRegex = parseRegexSafe(rawRule.require_pattern, rawRule.flags ?? '');
          if (!requireRegex) { addConfigError(`Custom rule "${id}" has an invalid "require_pattern" regular expression.`); continue; }
        }
        let requireHeading = null;
        if (rawRule.require_heading !== undefined) {
          if (typeof rawRule.require_heading !== 'string' || !rawRule.require_heading.trim()) {
            addConfigError(`Custom rule "${id}" field "require_heading" must be a nonblank string.`);
            continue;
          }
          requireHeading = rawRule.require_heading.trim();
        }
        let maxLines = null;
        if (rawRule.max_lines !== undefined) {
          if (!Number.isInteger(rawRule.max_lines) || rawRule.max_lines < 1) {
            addConfigError(`Custom rule "${id}" field "max_lines" must be a positive integer.`);
            continue;
          }
          maxLines = rawRule.max_lines;
        }
        if (!forbidRegex && !requireRegex && !requireHeading && maxLines === null) {
          addConfigError(`Custom rule "${id}" must specify at least one check ("forbid_pattern", "require_pattern", "require_heading", or "max_lines").`);
          continue;
        }

        const message = typeof rawRule.message === 'string' && rawRule.message.trim()
          ? rawRule.message.trim()
          : `Custom project lint rule "${id}" failed.`;

        // Deduplicate by `id`: later overrides replace earlier definitions cleanly.
        customRuleMap.set(id, {
          id,
          targets: new Set(targetList),
          severity,
          includeMatchers,
          excludeMatchers,
          forbidRegex,
          requireRegex,
          requireHeading,
          maxLines,
          message,
        });
      }
    }
  }
}

function loadWorkspaceLintRuleFiles(realRoot, target) {
  let loadedAny = false;
  for (const relDir of ['rules', 'rules/lint']) {
    try {
      const st = lstatSync(join(realRoot, relDir));
      if (st.isSymbolicLink() || !st.isDirectory()) return false;
    } catch {
      return false;
    }
  }
  let entries;
  try { entries = readdirSync(join(realRoot, 'rules/lint')).filter(name => name.endsWith('.json')).sort(); }
  catch { return false; }

  for (const name of entries) {
    const relPath = `rules/lint/${name}`;
    try {
      if (lstatSync(join(realRoot, relPath)).isSymbolicLink()) {
        target.configErrors.push({
          filePath: relPath, line: 1, order: 0, code: 'lint-config-invalid', category: 'lint config',
          detail: `${relPath} must be a regular file, not a symlink.`,
          fix: `Replace symlink ${relPath} with a regular JSON file`,
        });
        loadedAny = true;
        continue;
      }
    } catch { continue; }
    const rawText = readSafeUtf8(realRoot, relPath);
    if (rawText === null) continue;
    loadedAny = true;
    let parsed;
    try { parsed = JSON.parse(rawText); }
    catch {
      target.configErrors.push({
        filePath: relPath, line: 1, order: 0, code: 'lint-config-invalid', category: 'lint config',
        detail: `${relPath} contains invalid JSON.`,
        fix: `Repair the JSON syntax in ${relPath}`,
      });
      continue;
    }
    const section = Array.isArray(parsed)
      ? { custom_rules: parsed }
      : (parsed && typeof parsed === 'object' && typeof parsed.id === 'string'
        && !Object.hasOwn(parsed, 'disable') && !Object.hasOwn(parsed, 'rules') && !Object.hasOwn(parsed, 'custom_rules')
        ? { custom_rules: [parsed] }
        : parsed);
    mergeLintConfigSection(section, { sourcePath: relPath, allowCommands: false, ...target });
  }
  return loadedAny;
}

export function loadProjectLintConfig(rootOrObject) {
  const empty = { configured: false, disabledRules: new Set(), ruleSeverities: new Map(), customRules: [], commands: [], configErrors: [] };
  if (!rootOrObject) return empty;
  const target = { disabledRules: new Set(), ruleSeverities: new Map(), customRuleMap: new Map(), commandMap: new Map(), configErrors: [] };
  const finalize = configured => ({
    configured,
    disabledRules: target.disabledRules,
    ruleSeverities: target.ruleSeverities,
    customRules: [...target.customRuleMap.values()],
    commands: [...target.commandMap.values()],
    configErrors: target.configErrors,
  });

  if (typeof rootOrObject === 'string') {
    let realRoot;
    try { realRoot = realpathSync(rootOrObject); } catch { return empty; }
    let configured = loadWorkspaceLintRuleFiles(realRoot, target);
    const rawText = readSafeUtf8(realRoot, 'pdd.json');
    if (rawText !== null) {
      let parsed;
      try { parsed = JSON.parse(rawText); }
      catch {
        target.configErrors.push({
          filePath: 'pdd.json', line: 1, order: 0, code: 'lint-config-invalid', category: 'lint config',
          detail: 'pdd.json contains invalid JSON.',
          fix: 'Repair the JSON syntax in pdd.json',
        });
        return finalize(true);
      }
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed) && Object.hasOwn(parsed, 'lint') && parsed.lint !== undefined && parsed.lint !== null) {
        configured = true;
        mergeLintConfigSection(parsed.lint, { sourcePath: 'pdd.json', ...target });
      }
    }
    return configured ? finalize(true) : empty;
  }

  if (typeof rootOrObject === 'object' && !Array.isArray(rootOrObject)) {
    const rawLint = Object.hasOwn(rootOrObject, 'lint') ? rootOrObject.lint : rootOrObject;
    if (rawLint === undefined || rawLint === null) return empty;
    mergeLintConfigSection(rawLint, { sourcePath: 'pdd.json', ...target });
    return finalize(true);
  }
  return empty;
}

function headingMatches(contentText, requiredHeading) {
  const hasHashes = /^#{1,6}\s+/.test(requiredHeading);
  const lower = requiredHeading.toLowerCase();
  for (const line of contentText.split(/\r?\n/)) {
    if (hasHashes) { if (line.trim().toLowerCase() === lower) return true; }
    else {
      const m = /^ {0,3}#{1,6}\s+(.+)$/.exec(line);
      if (m && m[1].trim().toLowerCase() === lower) return true;
    }
  }
  return false;
}

export function loadBaseTrustedLintCommands(root, { baseRef } = {}) {
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return { baseSha: null, source: null, commands: [], skippedUntrusted: false }; }
  let wtCommands = [];
  const wtRaw = readSafeUtf8(realRoot, 'pdd.json');
  if (wtRaw !== null) {
    try {
      const wtParsed = JSON.parse(wtRaw);
      const wtTarget = { disabledRules: new Set(), ruleSeverities: new Map(), customRuleMap: new Map(), commandMap: new Map(), configErrors: [] };
      if (wtParsed?.lint?.commands !== undefined) {
        mergeLintConfigSection({ commands: wtParsed.lint.commands }, { sourcePath: 'pdd.json', allowCommands: true, ...wtTarget });
      }
      wtCommands = [...wtTarget.commandMap.values()];
    } catch {}
  }

  const ref = baseRef || resolveDefaultBaseRef(realRoot);
  if (!ref) return { baseSha: null, source: null, commands: [], skippedUntrusted: wtCommands.length > 0 };
  const resolved = spawnSync('git', ['rev-parse', '--verify', `${ref}^{commit}`], { cwd: realRoot, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
  const commit = resolved.status === 0 && resolved.stdout.trim() ? resolved.stdout.trim() : null;
  if (!commit) return { baseSha: null, source: null, commands: [], skippedUntrusted: wtCommands.length > 0 };
  const mb = spawnSync('git', ['merge-base', 'HEAD', commit], { cwd: realRoot, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
  if (mb.status !== 0 || !mb.stdout.trim()) return { baseSha: null, source: null, commands: [], skippedUntrusted: wtCommands.length > 0 };
  const baseSha = mb.stdout.trim();

  const show = spawnSync('git', ['show', `${baseSha}:pdd.json`], { cwd: realRoot, encoding: 'utf8', maxBuffer: 2 * 1024 * 1024, stdio: ['ignore', 'pipe', 'ignore'] });
  const baseCommands = [];
  if (show.status === 0 && typeof show.stdout === 'string') {
    try {
      const parsed = JSON.parse(show.stdout);
      if (parsed?.lint && typeof parsed.lint === 'object' && !Array.isArray(parsed.lint)) {
        const t = { disabledRules: new Set(), ruleSeverities: new Map(), customRuleMap: new Map(), commandMap: new Map(), configErrors: [] };
        mergeLintConfigSection({ commands: parsed.lint.commands }, { sourcePath: `${baseSha}:pdd.json`, allowCommands: true, ...t });
        baseCommands.push(...t.commandMap.values());
      }
    } catch {}
  }

  const skippedUntrusted = wtCommands.length > 0 && JSON.stringify(wtCommands) !== JSON.stringify(baseCommands);
  return { baseSha, source: `${baseSha}:pdd.json`, commands: baseCommands, skippedUntrusted };
}

export function loadBaseTrustedLintOverrides(root, { baseRef } = {}) {
  const empty = { baseAvailable: false, baseSha: null, disabledRules: new Set(), ruleSeverities: new Map() };
  if (!root || typeof root !== 'string') return empty;
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return empty; }
  const ref = baseRef || resolveDefaultBaseRef(realRoot);
  if (!ref) return empty;
  const resolved = spawnSync('git', ['rev-parse', '--verify', `${ref}^{commit}`], { cwd: realRoot, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
  const commit = resolved.status === 0 && resolved.stdout.trim() ? resolved.stdout.trim() : null;
  if (!commit) return empty;
  const mb = spawnSync('git', ['merge-base', 'HEAD', commit], { cwd: realRoot, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
  if (mb.status !== 0 || !mb.stdout.trim()) return empty;
  const baseSha = mb.stdout.trim();

  const target = { disabledRules: new Set(), ruleSeverities: new Map(), customRuleMap: new Map(), commandMap: new Map(), configErrors: [] };
  const lsRules = spawnSync('git', ['ls-tree', '--name-only', baseSha, '--', 'rules/lint/'], {
    cwd: realRoot, encoding: 'utf8', maxBuffer: 2 * 1024 * 1024, stdio: ['ignore', 'pipe', 'ignore'],
  });
  if (lsRules.status === 0 && typeof lsRules.stdout === 'string') {
    const ruleFiles = lsRules.stdout.split(/\r?\n/).map(s => s.trim()).filter(s => s.endsWith('.json')).sort();
    for (const relPath of ruleFiles) {
      const showRule = spawnSync('git', ['show', `${baseSha}:${relPath}`], {
        cwd: realRoot, encoding: 'utf8', maxBuffer: 2 * 1024 * 1024, stdio: ['ignore', 'pipe', 'ignore'],
      });
      if (showRule.status !== 0 || typeof showRule.stdout !== 'string') continue;
      try {
        const parsed = JSON.parse(showRule.stdout);
        const section = Array.isArray(parsed)
          ? { custom_rules: parsed }
          : (parsed && typeof parsed === 'object' && typeof parsed.id === 'string'
            && !Object.hasOwn(parsed, 'disable') && !Object.hasOwn(parsed, 'rules') && !Object.hasOwn(parsed, 'custom_rules')
            ? { custom_rules: [parsed] }
            : parsed);
        mergeLintConfigSection(section, { sourcePath: `${baseSha}:${relPath}`, allowCommands: false, ...target });
      } catch {}
    }
  }

  const showPkg = spawnSync('git', ['show', `${baseSha}:pdd.json`], {
    cwd: realRoot, encoding: 'utf8', maxBuffer: 2 * 1024 * 1024, stdio: ['ignore', 'pipe', 'ignore'],
  });
  if (showPkg.status === 0 && typeof showPkg.stdout === 'string') {
    try {
      const parsed = JSON.parse(showPkg.stdout);
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed) && parsed.lint && typeof parsed.lint === 'object' && !Array.isArray(parsed.lint)) {
        mergeLintConfigSection(parsed.lint, { sourcePath: `${baseSha}:pdd.json`, allowCommands: true, ...target });
      }
    } catch {}
  }

  return { baseAvailable: true, baseSha, disabledRules: target.disabledRules, ruleSeverities: target.ruleSeverities };
}

export function matchesAnyCustomRule(customRules, kind, filePath) {
  for (const rule of customRules) {
    if (rule.severity === 'off') continue;
    if (!rule.targets.has('all') && !rule.targets.has(kind)) continue;
    if (rule.includeMatchers.length && !rule.includeMatchers.some(m => m.test(filePath))) continue;
    if (rule.excludeMatchers.some(m => m.test(filePath))) continue;
    return true;
  }
  return false;
}

export function evaluateCustomRulesOnFile(customRules, { filePath, kind, rawText }) {
  const findings = [];
  const inspectText = kind === 'prompt' ? stripPromptMetadataPreservingLines(rawText) : rawText;
  const lineCount = kind === 'prompt' ? countPromptProseLines(rawText) : countFileLines(rawText);
  const lineStarts = buildLineStarts(inspectText);

  for (let idx = 0; idx < customRules.length; idx++) {
    const rule = customRules[idx];
    if (rule.severity === 'off') continue;
    if (!rule.targets.has('all') && !rule.targets.has(kind)) continue;
    if (rule.includeMatchers.length && !rule.includeMatchers.some(m => m.test(filePath))) continue;
    if (rule.excludeMatchers.some(m => m.test(filePath))) continue;

    if (rule.forbidRegex) {
      const m = rule.forbidRegex.exec(inspectText);
      if (m) {
        findings.push({
          filePath, line: lineNumberAt(lineStarts, m.index), order: 50 + idx,
          code: rule.id, category: 'custom rule', defaultSeverity: rule.severity, detail: rule.message,
        });
      }
    }
    if (rule.requireRegex && !rule.requireRegex.test(inspectText)) {
      findings.push({ filePath, line: 1, order: 50 + idx, code: rule.id, category: 'custom rule', defaultSeverity: rule.severity, detail: rule.message });
    }
    if (rule.requireHeading && !headingMatches(inspectText, rule.requireHeading)) {
      findings.push({ filePath, line: 1, order: 50 + idx, code: rule.id, category: 'custom rule', defaultSeverity: rule.severity, detail: rule.message });
    }
    if (rule.maxLines !== null && lineCount > rule.maxLines) {
      findings.push({ filePath, line: 1, order: 50 + idx, code: rule.id, category: 'custom rule', defaultSeverity: rule.severity, detail: `${rule.message} (${lineCount} lines > max ${rule.maxLines}).` });
    }
  }
  return findings;
}
