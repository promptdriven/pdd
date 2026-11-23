// Generated from prompts/cli/agent-adapters.prompt.md.
// Layer-0 local agent CLI process execution, auth status parsing, and read-only discovery.
import { executableMissing, runProcess } from './subprocess.mjs';
import { workspace } from './workspace-policy.mjs';

const AGENTS = [['codex', 'Codex'], ['claude', 'Claude'], ['gemini', 'Gemini']];

export { executableMissing };
export const runAgentProcess = runProcess;

/**
 * Interpret `codex login status` or `claude auth status --json` output into
 * `'ready' | 'signed_out' | 'unavailable'` without ever exposing credential text.
 */
export function parseAgentAuthStatus({ agent, result } = {}) {
  if (!result || !Number.isInteger(result.code) || typeof result.stdout !== 'string' || typeof result.stderr !== 'string') {
    return 'unavailable';
  }
  if (agent === 'claude') {
    try {
      const value = JSON.parse(result.stdout);
      if (value?.loggedIn === true && result.code === 0) return 'ready';
      if (value?.loggedIn === false && [0, 1].includes(result.code)) return 'signed_out';
    } catch {}
    return 'unavailable';
  }
  if (agent !== 'codex') return 'unavailable';
  const text = `${result.stdout}\n${result.stderr}`.replace(/\x1b\[[0-?]*[ -/]*[@-~]/g, '');
  const negative = /\bnot\s+(?:logged|signed)\s+in\b|\b(?:login|sign[ -]?in)\s+required\b/i.test(text);
  const affirmative = text.replace(/\bnot\s+(?:logged|signed)\s+in\b/gi, '');
  const positive = /\blogged in\b|\bapi key configured\b/i.test(affirmative);
  if (positive && negative) return 'unavailable';
  if ([0, 1].includes(result.code) && negative) return 'signed_out';
  return result.code === 0 && positive ? 'ready' : 'unavailable';
}

/**
 * Interpret `agy models` output (`0` + nonblank stdout -> `ready`; `1` + sign-in hint -> `signed_out`).
 */
export function agyStatus(result) {
  if (!result || !Number.isInteger(result.code) || typeof result.stdout !== 'string' || typeof result.stderr !== 'string') {
    return 'unavailable';
  }
  if (result.code === 0 && result.stdout.trim()) return 'ready';
  return result.code === 1 && /\bsign in\b/i.test(result.stdout + result.stderr) ? 'signed_out' : 'unavailable';
}

/**
 * Validate Gemini CLI `--help` output for required read-only Try flags.
 */
export function geminiCapabilityError(help) {
  if (help.code !== 0) return 'Gemini Try read-only capability discovery failed (--help).';
  const missing = ['--approval-mode', '--admin-policy', '--extensions', '--allowed-mcp-server-names', '--output-format']
    .find(flag => !help.stdout.includes(flag));
  return missing ? `Gemini Try read-only mode requires ${missing}; update Gemini CLI.` : null;
}

/**
 * Discover locally installed Codex/Claude/Gemini CLIs and their read-only capability + auth state
 * using cheap `--help` and status subcommands (never making a model call).
 */
export async function discoverAgents({
  cwd = process.cwd(),
  env = process.env,
  run = runAgentProcess,
  definitions,
  workspace: explicitWorkspace,
  loadDefinitions,
} = {}) {
  const wsPolicy = explicitWorkspace ?? workspace.policy({ root: cwd });
  if (wsPolicy.configured) {
    return (definitions ?? AGENTS.map(([id, name]) => ({ id, name }))).map(d => ({
      id: d.id,
      name: d.name,
      state: 'error',
      detail: 'Bounded agent connection is unavailable: packet-only context cannot be established.',
    }));
  }
  const activeDefinitions = definitions
    ?? (typeof loadDefinitions === 'function'
      ? loadDefinitions({ cwd, env })
      : AGENTS.map(([id, name]) => ({ id, name, kind: id, command: id, env: {} })));
  const result = [];
  for (const { id, name, kind, command, env: overrides } of activeDefinitions) {
    const childEnv = { ...env, ...overrides };
    const opts = { cwd, env: childEnv, timeoutMs: 10_000, maxBytes: 131_072 };
    try {
      const help = await run(command, ['--help'], opts);
      if (kind === 'gemini') {
        const detail = geminiCapabilityError(help);
        result.push({
          id,
          name,
          state: detail ? 'error' : 'available',
          detail: detail || 'Installed; sign-in is checked when you send a message.',
        });
        continue;
      }
      if (help.code !== 0) {
        result.push({ id, name, state: 'error', detail: 'The agent help command failed.' });
        continue;
      }
      const flags = kind === 'codex' ? ['--sandbox'] : ['--safe-mode', '--tools', '--permission-prompts'];
      if (flags.some(f => !help.stdout.includes(f))) {
        result.push({ id, name, state: 'error', detail: 'Update this agent to a version with the required read-only controls.' });
        continue;
      }
      const auth = await run(command, kind === 'codex' ? ['login', 'status'] : ['auth', 'status', '--json'], { ...opts, maxBytes: 16_384 });
      const state = parseAgentAuthStatus({ agent: kind, result: auth });
      result.push({ id, name, state: state === 'unavailable' ? 'error' : state });
    } catch (e) {
      result.push({ id, name, state: e.code === 'ENOENT' && e.executableMissing === true ? 'not_installed' : 'error' });
    }
  }
  return result;
}
