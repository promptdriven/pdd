// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Project lint configuration loader (`pdd.json` "lint" + `rules/lint/*.json`), base-trusted lint.commands & overrides.
import { spawnSync } from 'node:child_process';
import { lstatSync, readdirSync, realpathSync } from 'node:fs';
import { join } from 'node:path';
import { readSafeUtf8, resolveDefaultBaseRef } from './diagnostics.mjs';

const MAX_LINT_COMMANDS = 16;
const RULE_ID_RE = /^[A-Za-z0-9][A-Za-z0-9_.-]{0,63}$/;
const VALID_SEVERITIES = new Set(['off', 'warn', 'error']);

function mergeLintConfigSection(rawLint, { sourcePath, allowCommands = true, disabledRules, ruleSeverities, commandMap, mutationCommandRef, scenarioConfigRef, configErrors }) {
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

  if (rawLint.scenario !== undefined) {
    if (!rawLint.scenario || typeof rawLint.scenario !== 'object' || Array.isArray(rawLint.scenario)) {
      addConfigError(`"lint.scenario" in ${sourcePath} must be a JSON object with optional positive integers "max_steps" and "max_world_bytes".`);
    } else {
      for (const [k, v] of Object.entries(rawLint.scenario)) {
        if (k !== 'max_steps' && k !== 'max_world_bytes') {
          addConfigError(`Unknown key "${k}" in "lint.scenario" (${sourcePath}); allowed keys are "max_steps" and "max_world_bytes".`);
          continue;
        }
        if (!Number.isSafeInteger(v) || v < 1 || v > 1_000_000_000) {
          addConfigError(`"lint.scenario.${k}" in ${sourcePath} must be a positive integer.`);
          continue;
        }
        if (scenarioConfigRef) {
          if (k === 'max_steps') scenarioConfigRef.maxSteps = v;
          if (k === 'max_world_bytes') scenarioConfigRef.maxWorldBytes = v;
        }
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

  if (rawLint.mutation_command !== undefined) {
    if (!allowCommands) {
      addConfigError(`"lint.mutation_command" is only permitted in merge-base pdd.json, not ${sourcePath}.`);
    } else if (typeof rawLint.mutation_command !== 'string' || !rawLint.mutation_command.trim()) {
      addConfigError(`"lint.mutation_command" in ${sourcePath} must be a nonblank command string.`);
    } else if (mutationCommandRef) {
      mutationCommandRef.value = rawLint.mutation_command.trim();
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
    if (Array.isArray(parsed)) continue;
    mergeLintConfigSection(parsed, { sourcePath: relPath, allowCommands: false, ...target });
  }
  return loadedAny;
}

export function loadProjectLintConfig(rootOrObject) {
  const empty = { configured: false, disabledRules: new Set(), ruleSeverities: new Map(), customRules: [], commands: [], mutationCommand: null, scenarioConfig: { maxSteps: null, maxWorldBytes: null }, configErrors: [] };
  if (!rootOrObject) return empty;
  const target = { disabledRules: new Set(), ruleSeverities: new Map(), commandMap: new Map(), mutationCommandRef: { value: null }, scenarioConfigRef: { maxSteps: null, maxWorldBytes: null }, configErrors: [] };
  const finalize = configured => ({
    configured,
    disabledRules: target.disabledRules,
    ruleSeverities: target.ruleSeverities,
    customRules: [],
    commands: [...target.commandMap.values()],
    mutationCommand: target.mutationCommandRef.value,
    scenarioConfig: { ...target.scenarioConfigRef },
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

export function loadBaseTrustedLintCommands(root, { baseRef } = {}) {
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return { baseSha: null, source: null, commands: [], mutationCommand: null, skippedUntrusted: false }; }
  let wtCommands = [];
  let wtMutationCommand = null;
  const wtRaw = readSafeUtf8(realRoot, 'pdd.json');
  if (wtRaw !== null) {
    try {
      const wtParsed = JSON.parse(wtRaw);
      const wtTarget = { disabledRules: new Set(), ruleSeverities: new Map(), commandMap: new Map(), mutationCommandRef: { value: null }, configErrors: [] };
      if (wtParsed?.lint?.commands !== undefined || wtParsed?.lint?.mutation_command !== undefined) {
        mergeLintConfigSection({ commands: wtParsed.lint.commands, mutation_command: wtParsed.lint.mutation_command }, { sourcePath: 'pdd.json', allowCommands: true, ...wtTarget });
      }
      wtCommands = [...wtTarget.commandMap.values()];
      wtMutationCommand = wtTarget.mutationCommandRef.value;
    } catch {}
  }

  const ref = baseRef || resolveDefaultBaseRef(realRoot);
  if (!ref) return { baseSha: null, source: null, commands: [], mutationCommand: null, skippedUntrusted: wtCommands.length > 0 || wtMutationCommand !== null };
  const resolved = spawnSync('git', ['rev-parse', '--verify', `${ref}^{commit}`], { cwd: realRoot, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
  const commit = resolved.status === 0 && resolved.stdout.trim() ? resolved.stdout.trim() : null;
  if (!commit) return { baseSha: null, source: null, commands: [], mutationCommand: null, skippedUntrusted: wtCommands.length > 0 || wtMutationCommand !== null };
  const mb = spawnSync('git', ['merge-base', 'HEAD', commit], { cwd: realRoot, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
  if (mb.status !== 0 || !mb.stdout.trim()) return { baseSha: null, source: null, commands: [], mutationCommand: null, skippedUntrusted: wtCommands.length > 0 || wtMutationCommand !== null };
  const baseSha = mb.stdout.trim();

  const show = spawnSync('git', ['show', `${baseSha}:pdd.json`], { cwd: realRoot, encoding: 'utf8', maxBuffer: 2 * 1024 * 1024, stdio: ['ignore', 'pipe', 'ignore'] });
  const baseCommands = [];
  let baseMutationCommand = null;
  if (show.status === 0 && typeof show.stdout === 'string') {
    try {
      const parsed = JSON.parse(show.stdout);
      if (parsed?.lint && typeof parsed.lint === 'object' && !Array.isArray(parsed.lint)) {
        const t = { disabledRules: new Set(), ruleSeverities: new Map(), commandMap: new Map(), mutationCommandRef: { value: null }, configErrors: [] };
        mergeLintConfigSection({ commands: parsed.lint.commands, mutation_command: parsed.lint.mutation_command }, { sourcePath: `${baseSha}:pdd.json`, allowCommands: true, ...t });
        baseCommands.push(...t.commandMap.values());
        baseMutationCommand = t.mutationCommandRef.value;
      }
    } catch {}
  }

  const skippedCommands = wtCommands.length > 0 && JSON.stringify(wtCommands) !== JSON.stringify(baseCommands);
  const skippedMutationCommand = wtMutationCommand !== null && wtMutationCommand !== baseMutationCommand;
  const skippedUntrusted = skippedCommands || skippedMutationCommand;
  return { baseSha, source: `${baseSha}:pdd.json`, commands: baseCommands, mutationCommand: baseMutationCommand, skippedCommands, skippedMutationCommand, skippedUntrusted };
}

export function loadBaseTrustedLintOverrides(root, { baseRef } = {}) {
  const empty = { baseAvailable: false, baseSha: null, disabledRules: new Set(), ruleSeverities: new Map(), scenarioConfig: { maxSteps: null, maxWorldBytes: null } };
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

  const target = { disabledRules: new Set(), ruleSeverities: new Map(), commandMap: new Map(), scenarioConfigRef: { maxSteps: null, maxWorldBytes: null }, configErrors: [] };
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
        if (Array.isArray(parsed)) continue;
        mergeLintConfigSection(parsed, { sourcePath: `${baseSha}:${relPath}`, allowCommands: false, ...target });
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

  return { baseAvailable: true, baseSha, disabledRules: target.disabledRules, ruleSeverities: target.ruleSeverities, scenarioConfig: { ...target.scenarioConfigRef } };
}
