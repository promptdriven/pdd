// Generated from prompts/cli/pdd-claude.prompt.md.
// Layer-1 pure Claude CLI flag tables, `--settings` extraction/merging, and `--` arg splicing.
import * as nativeFs from 'node:fs';
import { resolve } from 'node:path';
import { CloudAccountsError } from './cloud-error.mjs';

export const CLAUDE_VALUE_FLAGS = new Set([
  '--add-dir',
  '--agent',
  '--agents',
  '--allowedTools',
  '--allowed-tools',
  '--disallowedTools',
  '--disallowed-tools',
  '--append-system-prompt',
  '--append-system-prompt-file',
  '--autocompact',
  '--betas',
  '--debug-file',
  '--effort',
  '--environment',
  '--fallback-model',
  '--file',
  '--input-format',
  '--json-schema',
  '--max-budget-usd',
  '--mcp-config',
  '--model',
  '-n',
  '--name',
  '--output-format',
  '--permission-mode',
  '--permission-prompts',
  '--permission-prompt-tool',
  '--plugin-dir',
  '--plugin-url',
  '--remote-control-session-name-prefix',
  '--session-id',
  '--setting-sources',
  '--settings',
  '--system-prompt',
  '--system-prompt-file',
  '--system-prompt-snapshot',
  '--tools',
]);

export const CLAUDE_VARIADIC_VALUE_FLAGS = new Set([
  '--add-dir',
  '--allowedTools',
  '--allowed-tools',
  '--disallowedTools',
  '--disallowed-tools',
  '--betas',
  '--file',
  '--mcp-config',
  '--tools',
]);

export const CLAUDE_OPTIONAL_VALUE_FLAGS = new Set([
  '--cloud',
  '-d',
  '--debug',
  '--from-pr',
  '--prompt-suggestions',
  '-r',
  '--remote-control',
  '--resume',
  '--teleport',
  '-w',
  '--worktree',
]);

export const CLAUDE_BOOL_FLAGS = new Set([
  '--allow-dangerously-skip-permissions',
  '--ax-screen-reader',
  '--bare',
  '--bg',
  '--background',
  '--brief',
  '-c',
  '--continue',
  '--chrome',
  '--no-chrome',
  '--dangerously-skip-permissions',
  '--desktop',
  '--disable-slash-commands',
  '--exclude-dynamic-system-prompt-sections',
  '--fork-session',
  '--forward-subagent-text',
  '--ide',
  '--no-ide',
  '--include-hook-events',
  '--include-partial-messages',
  '--no-session-persistence',
  '-p',
  '--print',
  '--replay-user-messages',
  '--restricted',
  '--safe-mode',
  '--strict-mcp-config',
  '--tmux',
  '--verbose',
]);

export const CLAUDE_SESSION_ONLY_FLAGS = new Set([
  '--agent',
  '--agents',
  '--allow-dangerously-skip-permissions',
  '--allowedTools',
  '--allowed-tools',
  '--append-system-prompt',
  '--append-system-prompt-file',
  '--bare',
  '--betas',
  '--bg',
  '--background',
  '-c',
  '--continue',
  '--chrome',
  '--no-chrome',
  '--dangerously-skip-permissions',
  '--disallowedTools',
  '--disallowed-tools',
  '--fallback-model',
  '--file',
  '--fork-session',
  '--input-format',
  '--json-schema',
  '--max-budget-usd',
  '--mcp-config',
  '-n',
  '--name',
  '--no-session-persistence',
  '--output-format',
  '-p',
  '--print',
  '--permission-mode',
  '--permission-prompts',
  '--permission-prompt-tool',
  '-r',
  '--resume',
  '--restricted',
  '--safe-mode',
  '--session-id',
  '--strict-mcp-config',
  '--system-prompt',
  '--system-prompt-file',
  '--tools',
  '-w',
  '--worktree',
]);

/**
 * Find the index of a true `--` end-of-options separator in Claude CLI args,
 * skipping values consumed by Claude value flags so a flag value of `"--"` is not mistaken.
 */
export function findClaudeDoubleDashIndex(claudeArgs = []) {
  const args = Array.isArray(claudeArgs) ? claudeArgs.map(String) : [];
  for (let i = 0; i < args.length; i += 1) {
    const token = args[i];
    if (token === '--') return i;
    if (token.startsWith('--') && token.includes('=')) continue;
    if (CLAUDE_VALUE_FLAGS.has(token)) {
      i += 1;
      continue;
    }
  }
  return -1;
}

/**
 * Splice extra Claude CLI flags before any real `--` separator (or append at end).
 */
export function spliceClaudeExtraArgs(args = [], extraArgs = []) {
  const base = Array.isArray(args) ? [...args] : [];
  if (!Array.isArray(extraArgs) || extraArgs.length === 0) return base;
  const dd = findClaudeDoubleDashIndex(base);
  if (dd === -1) return [...base, ...extraArgs];
  return [...base.slice(0, dd), ...extraArgs, ...base.slice(dd)];
}

/**
 * Extract any user-provided `--settings` flags from `claudeArgs` (before `--`) and parse
 * the effective last value (JSON object string or JSON file path) so PDD can merge it with
 * the gateway `env` overlay instead of letting two `--settings` flags overwrite each other.
 */
export function extractAndParseUserClaudeSettings(claudeArgs = [], { cwd = process.cwd(), fs = nativeFs } = {}) {
  const args = Array.isArray(claudeArgs) ? claudeArgs.map(String) : [];
  const strippedArgs = [];
  let lastRawSettings = null;
  let sawDoubleDash = false;

  for (let i = 0; i < args.length; i += 1) {
    const token = args[i];
    if (sawDoubleDash) {
      strippedArgs.push(token);
      continue;
    }
    if (token === '--') {
      sawDoubleDash = true;
      strippedArgs.push(token);
      continue;
    }
    if (token === '--settings') {
      const next = args[i + 1];
      if (next === undefined) {
        throw new CloudAccountsError('Missing value for --settings.', {
          code: 'invalid_settings',
          exitCode: 2,
        });
      }
      lastRawSettings = next;
      i += 1;
      continue;
    }
    if (token.startsWith('--settings=')) {
      lastRawSettings = token.slice('--settings='.length);
      continue;
    }
    if (!token.includes('=') && CLAUDE_VALUE_FLAGS.has(token)) {
      strippedArgs.push(token);
      if (i + 1 < args.length) {
        strippedArgs.push(args[i + 1]);
        i += 1;
      }
      continue;
    }
    strippedArgs.push(token);
  }

  if (lastRawSettings === null) {
    return { strippedArgs, userSettings: null };
  }

  const trimmed = lastRawSettings.trim();
  if (!trimmed) {
    throw new CloudAccountsError('Empty value provided to --settings.', {
      code: 'invalid_settings',
      exitCode: 2,
    });
  }

  let parsed;
  if (trimmed.startsWith('{') || trimmed.startsWith('[')) {
    try {
      parsed = JSON.parse(trimmed);
    } catch (err) {
      throw new CloudAccountsError(`Invalid JSON passed to --settings: ${err?.message || err}`, {
        code: 'invalid_settings',
        exitCode: 2,
      });
    }
  } else {
    const targetPath = resolve(cwd, trimmed);
    let rawText;
    try {
      rawText = fs.readFileSync(targetPath, 'utf8');
    } catch (err) {
      throw new CloudAccountsError(`Could not read --settings file "${trimmed}": ${err?.message || err}`, {
        code: 'invalid_settings',
        exitCode: 2,
      });
    }
    try {
      parsed = JSON.parse(rawText);
    } catch (err) {
      throw new CloudAccountsError(`Invalid JSON in --settings file "${trimmed}": ${err?.message || err}`, {
        code: 'invalid_settings',
        exitCode: 2,
      });
    }
  }

  if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed)) {
    throw new CloudAccountsError('--settings must resolve to a JSON object.', {
      code: 'invalid_settings',
      exitCode: 2,
    });
  }
  return { strippedArgs, userSettings: parsed };
}

/**
 * Prepend `--settings <settingsPath>` onto stripped Claude arguments.
 */
export function injectClaudeSettingsArg(strippedArgs = [], settingsPath) {
  const args = Array.isArray(strippedArgs) ? [...strippedArgs] : [];
  return ['--settings', settingsPath, ...args];
}
