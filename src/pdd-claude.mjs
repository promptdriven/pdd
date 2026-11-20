// Generated from prompts/cli/pdd-claude.prompt.md.
// Dedicated PDD Claude launcher: keeps ~/.claude/settings.json and CLAUDE_CONFIG_DIR untouched,
// passes PDD Cloud gateway auth via a per-session 0600 --settings file, shares one PID-refcounted
// cloud lease across concurrent windows, and revokes + cleans up on exit.
import { spawn as nativeSpawn } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import {
  buildClaudeGatewaySettingsOverlay,
  CloudAccountsError,
  heartbeatCloudLease,
  leaseCloudAccount,
  releaseCloudLease,
  resolvePddStateBase,
  restoreLocalClaudeGatewayConfig,
} from './login-pool.mjs';
import { redactSecrets, rememberSecrets } from './secret-redaction.mjs';

const DEFAULT_LOCK_TIMEOUT_MS = 25_000;
const DEFAULT_STALE_LOCK_MS = 30_000;
const DEAD_LOCK_GRACE_MS = 1_500;
const DEFAULT_HEARTBEAT_INTERVAL_MS = 10 * 60 * 1000;
const MIN_REUSABLE_LEASE_REMAINING_MS = 5 * 60 * 1000;

const STRIPPED_CLAUDE_ENV_VARS = new Set([
  'CLAUDE_CODE_OAUTH_TOKEN',
  'ANTHROPIC_API_KEY',
  'ANTHROPIC_AUTH_TOKEN',
  'ANTHROPIC_BASE_URL',
  'CLAUDE_CODE_USE_BEDROCK',
  'CLAUDE_CODE_USE_VERTEX',
  'CLAUDE_CODE_USE_FOUNDRY',
]);

const NO_LEASE_TOP_FLAGS = new Set(['--version', '-v', '--help', '-h']);
const PASS_THROUGH_SUBCOMMANDS = new Set([
  'mcp',
  'plugin',
  'plugins',
  'doctor',
  'auto-mode',
  'update',
  'upgrade',
  'install',
  'import',
  'purge',
  'agents',
  'attach',
  'logs',
  'stop',
  'kill',
  'rm',
  'respawn',
  'gateway',
]);

const CLAUDE_VALUE_FLAGS = new Set([
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
  '--plugin-dir',
  '--plugin-url',
  '--session-id',
  '--setting-sources',
  '--settings',
  '--system-prompt',
  '--system-prompt-file',
  '--system-prompt-snapshot',
  '--tools',
]);

const CLAUDE_OPTIONAL_VALUE_FLAGS = new Set([
  '--cloud',
  '-d',
  '--debug',
  '--from-pr',
  '--prompt-suggestions',
  '-r',
  '--resume',
  '--teleport',
  '-w',
  '--worktree',
]);

const CLAUDE_BOOL_FLAGS = new Set([
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
  '--exclude-dynamic-system-prompt-sections',
  '--fork-session',
  '--ide',
  '--no-ide',
  '--include-partial-messages',
  '--no-session-persistence',
  '-p',
  '--print',
  '--replay-user-messages',
  '--strict-mcp-config',
  '--tmux',
  '--verbose',
]);

const PDD_CLAUDE_HELP_TEXT = [
  'pdd-claude — Launch Claude Code through your PDD Cloud shared account pool.',
  '',
  'Usage:',
  '  pdd-claude [CLAUDE_ARGS...]',
  '  pdd-claude --account <label> [CLAUDE_ARGS...]',
  '  pdd-claude logout',
  '  pdd-claude --pdd-help',
  '',
  'Behavior:',
  '  - Never modifies your personal ~/.claude/settings.json, ~/.claude.json, or stock `claude` login.',
  '  - Keeps all your chats, plugins, skills, hooks, CLAUDE.md, MCP servers, and Claude in Chrome.',
  '  - Injects a private 0600 temporary --settings file per session and deletes it immediately on exit.',
  '  - Shares one PDD Cloud lease across concurrent windows and revokes it when the last window exits.',
  '  - Automatically rotates accounts server-side when quota or auth fails (unless --account is set).',
  '',
].join('\n');

function sleepMs(ms) {
  return new Promise(resolveTimer => {
    setTimeout(resolveTimer, ms);
  });
}

function defaultIsPidAlive(pid) {
  if (!Number.isInteger(pid) || pid <= 0) return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch {
    return false;
  }
}

function writePrivateAtomic(fs, targetPath, content) {
  fs.mkdirSync(dirname(targetPath), { recursive: true, mode: 0o700 });
  const tmpPath = `${targetPath}.tmp-${process.pid}-${randomBytes(6).toString('hex')}`;
  try {
    fs.writeFileSync(tmpPath, content, { encoding: 'utf8', mode: 0o600 });
    try { fs.chmodSync?.(tmpPath, 0o600); } catch {}
    fs.renameSync(tmpPath, targetPath);
  } catch (err) {
    try { fs.unlinkSync(tmpPath); } catch {}
    throw err;
  }
}

function readJsonFileQuiet(fs, targetPath) {
  try {
    const parsed = JSON.parse(fs.readFileSync(targetPath, 'utf8'));
    return parsed && typeof parsed === 'object' && !Array.isArray(parsed) ? parsed : null;
  } catch {
    return null;
  }
}

function unlinkQuiet(fs, targetPath) {
  try {
    fs.unlinkSync(targetPath);
  } catch {}
}

function isKnownClaudeOrWrapperOption(token) {
  if (typeof token !== 'string' || !token) return false;
  if (token === '--' || token === '--account' || token.startsWith('--account=') || token === '--pdd-help') {
    return true;
  }
  const flagName = token.startsWith('--') && token.includes('=')
    ? token.slice(0, token.indexOf('='))
    : token;
  return NO_LEASE_TOP_FLAGS.has(flagName)
    || CLAUDE_VALUE_FLAGS.has(flagName)
    || CLAUDE_OPTIONAL_VALUE_FLAGS.has(flagName)
    || CLAUDE_BOOL_FLAGS.has(flagName);
}

/**
 * Parse optional leading `pdd-claude` wrapper flags (`--account`, `--pdd-help`) without
 * disturbing stock Claude Code flags or user prompt arguments.
 */
export function parsePddClaudeArgs(argv = []) {
  const args = Array.isArray(argv) ? argv.map(String) : [];
  let preferredAccount = null;
  let showPddHelp = false;
  let idx = 0;

  while (idx < args.length) {
    const token = args[idx];
    if (token === '--') {
      const nextToken = args[idx + 1];
      const nextIsPositionalDashPrompt = typeof nextToken === 'string'
        && nextToken.startsWith('-')
        && !isKnownClaudeOrWrapperOption(nextToken);
      if (idx > 0 && !nextIsPositionalDashPrompt) {
        idx += 1;
      }
      break;
    }
    if (token === '--pdd-help') {
      showPddHelp = true;
      idx += 1;
      continue;
    }
    if (token === '--account') {
      const next = args[idx + 1];
      if (!next || next === '--' || next.startsWith('-')) {
        throw new CloudAccountsError('Missing value for --account. Usage: pdd-claude --account <label> [CLAUDE_ARGS...]', {
          code: 'invalid_args',
          exitCode: 2,
        });
      }
      preferredAccount = next.trim();
      idx += 2;
      continue;
    }
    if (token.startsWith('--account=')) {
      const val = token.slice('--account='.length).trim();
      if (!val) {
        throw new CloudAccountsError('Missing value for --account. Usage: pdd-claude --account <label> [CLAUDE_ARGS...]', {
          code: 'invalid_args',
          exitCode: 2,
        });
      }
      preferredAccount = val;
      idx += 1;
      continue;
    }
    break;
  }

  return {
    preferredAccount,
    showPddHelp,
    claudeArgs: args.slice(idx),
  };
}

/**
 * Classify Claude Code CLI arguments so help, version, offline subcommands, and auth
 * commands route cleanly without waiting on a Cloud lease or injecting `--settings`.
 */
export function inspectClaudeInvocation(claudeArgs = []) {
  const args = Array.isArray(claudeArgs) ? claudeArgs.map(String) : [];
  let subcommand = null;
  let subcommandArg = null;
  let hasHelpOrVersion = false;
  let hasBareFlag = false;

  for (let i = 0; i < args.length; i += 1) {
    const token = args[i];
    if (token === '--') break;
    if (NO_LEASE_TOP_FLAGS.has(token)) {
      hasHelpOrVersion = true;
      continue;
    }
    if (token === '--bare') {
      hasBareFlag = true;
      continue;
    }
    if (subcommand === null) {
      if (token.startsWith('--') && token.includes('=')) {
        continue;
      }
      if (CLAUDE_VALUE_FLAGS.has(token)) {
        i += 1;
        continue;
      }
      if (CLAUDE_OPTIONAL_VALUE_FLAGS.has(token)) {
        const next = args[i + 1];
        if (next && next !== '--' && !next.startsWith('-')) {
          i += 1;
        }
        continue;
      }
      if (CLAUDE_BOOL_FLAGS.has(token)) {
        continue;
      }
      if (token.startsWith('-')) {
        continue;
      }
      subcommand = token;
      continue;
    }
    if (subcommandArg === null && !token.startsWith('-')) {
      subcommandArg = token;
    }
  }

  if (hasHelpOrVersion) {
    return { mode: 'pass_through', subcommand, subcommandArg, hasBareFlag };
  }
  if (subcommand === 'logout') {
    return { mode: 'logout', subcommand, subcommandArg, hasBareFlag };
  }
  if (
    subcommand === 'login'
    || subcommand === 'setup-token'
    || (subcommand === 'auth' && (subcommandArg === 'login' || subcommandArg === 'logout'))
  ) {
    return { mode: 'login_hint', subcommand, subcommandArg, hasBareFlag };
  }
  if (subcommand === 'auth' || (subcommand && PASS_THROUGH_SUBCOMMANDS.has(subcommand))) {
    return { mode: 'pass_through', subcommand, subcommandArg, hasBareFlag };
  }
  return { mode: 'leased', subcommand, subcommandArg, hasBareFlag };
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

export function injectClaudeSettingsArg(strippedArgs = [], settingsPath) {
  const args = Array.isArray(strippedArgs) ? [...strippedArgs] : [];
  const ddIndex = args.indexOf('--');
  if (ddIndex === -1) {
    return ['--settings', settingsPath, ...args];
  }
  return ['--settings', settingsPath, ...args.slice(0, ddIndex), ...args.slice(ddIndex)];
}

export function buildPddClaudeChildEnv(baseEnv = process.env) {
  const out = {};
  for (const [k, v] of Object.entries(baseEnv ?? {})) {
    if (typeof v !== 'string') continue;
    if (k.startsWith('PDD_')) continue;
    if (STRIPPED_CLAUDE_ENV_VARS.has(k)) continue;
    out[k] = v;
  }
  return out;
}

export function resolveClaudeRuntimeRoot(env = process.env) {
  const override = typeof env?.PDD_CLAUDE_RUNTIME_ROOT === 'string' && env.PDD_CLAUDE_RUNTIME_ROOT.trim();
  if (override) return resolve(override);
  return join(resolvePddStateBase(env), 'claude-runtime');
}

export function sharedClaudeRuntimeDir(env = process.env, uid = typeof process.getuid === 'function' ? process.getuid() : 'user') {
  return join(resolveClaudeRuntimeRoot(env), `pdd-claude-${uid}`);
}

function assertSafePrivateDir(fs, dirPath) {
  fs.mkdirSync(dirPath, { recursive: true, mode: 0o700 });
  const stat = fs.lstatSync(dirPath);
  if (stat.isSymbolicLink() || !stat.isDirectory()) {
    throw new CloudAccountsError(`Refusing unsafe pdd-claude runtime path "${dirPath}".`, {
      code: 'unsafe_runtime_dir',
    });
  }
  if (typeof process.getuid === 'function' && typeof stat.uid === 'number' && stat.uid !== process.getuid()) {
    throw new CloudAccountsError(`Refusing pdd-claude runtime path "${dirPath}" owned by another user.`, {
      code: 'unsafe_runtime_dir',
    });
  }
  try { fs.chmodSync?.(dirPath, 0o700); } catch {}
}

export async function withClaudeRuntimeLock(runtimeDir, fn, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = ports.now ?? Date.now;
  const sleep = ports.sleep ?? sleepMs;
  const isPidAlive = ports.isPidAlive ?? defaultIsPidAlive;
  const timeoutMs = ports.lockTimeoutMs ?? DEFAULT_LOCK_TIMEOUT_MS;
  const staleMs = ports.staleLockMs ?? DEFAULT_STALE_LOCK_MS;

  assertSafePrivateDir(fs, runtimeDir);
  const lockDir = join(runtimeDir, '.lock');
  const ownerFile = join(lockDir, 'owner.json');
  const lockToken = randomBytes(12).toString('hex');
  const deadline = now() + timeoutMs;

  let acquired = false;
  let wroteOwner = false;
  while (now() <= deadline) {
    try {
      fs.mkdirSync(lockDir, { mode: 0o700 });
      acquired = true;
      try {
        fs.writeFileSync(ownerFile, JSON.stringify({
          pid: process.pid,
          lockToken,
          acquiredAt: now(),
        }), { mode: 0o600 });
        wroteOwner = true;
      } catch {}
      break;
    } catch (err) {
      if (err?.code !== 'EEXIST') throw err;
      try {
        const stat = fs.lstatSync(lockDir);
        const owner = readJsonFileQuiet(fs, ownerFile);
        const ageMs = now() - (typeof owner?.acquiredAt === 'number' ? owner.acquiredAt : stat.mtimeMs);
        const deadOwner = owner && Number.isInteger(owner.pid) && !isPidAlive(owner.pid) && ageMs >= DEAD_LOCK_GRACE_MS;
        if (deadOwner || ageMs >= staleMs) {
          const reclaimDir = `${lockDir}.stale-${process.pid}-${randomBytes(4).toString('hex')}`;
          try {
            fs.renameSync(lockDir, reclaimDir);
            fs.rmSync(reclaimDir, { recursive: true, force: true });
          } catch {}
          continue;
        }
      } catch {}
      await sleep(40 + Math.floor(Math.random() * 50));
    }
  }

  if (!acquired) {
    throw new CloudAccountsError(`Timed out acquiring pdd-claude runtime lock in "${runtimeDir}".`, {
      code: 'runtime_lock_timeout',
    });
  }

  try {
    return await fn();
  } finally {
    try {
      const currentOwner = readJsonFileQuiet(fs, ownerFile);
      const ownsLock = wroteOwner
        ? currentOwner?.lockToken === lockToken
        : currentOwner === null;
      if (ownsLock) {
        fs.rmSync(lockDir, { recursive: true, force: true });
      }
    } catch {}
  }
}

function sweepDeadPids(fs, pidsDir, isPidAlive) {
  let live = [];
  let entries = [];
  try { entries = fs.readdirSync(pidsDir); } catch { return live; }
  for (const name of entries) {
    const pid = Number(name);
    const full = join(pidsDir, name);
    if (!Number.isInteger(pid) || pid <= 0 || !isPidAlive(pid)) {
      unlinkQuiet(fs, full);
    } else {
      live.push(pid);
    }
  }
  return live;
}

function sweepStaleSessionFiles(fs, sessionsDir, livePids) {
  const liveSet = new Set(livePids);
  let entries = [];
  try { entries = fs.readdirSync(sessionsDir); } catch { return; }
  for (const name of entries) {
    const match = /^settings-(\d+)-[a-f0-9]+\.json$/.exec(name);
    if (!match || !liveSet.has(Number(match[1]))) {
      unlinkQuiet(fs, join(sessionsDir, name));
    }
  }
}

function isReusableClaudeLease(meta, nowMs) {
  if (!meta || typeof meta !== 'object') return false;
  if (meta.auto_rotate !== true) return false;
  if (typeof meta.lease_id !== 'string' || !meta.lease_id.trim()) return false;
  const token = String(meta.claude_oauth_token || meta.gateway_bearer_token || '').trim();
  if (!token) return false;
  const expiresMs = Date.parse(String(meta.expires_at ?? ''));
  if (!Number.isFinite(expiresMs)) return false;
  return (expiresMs - nowMs) > MIN_REUSABLE_LEASE_REMAINING_MS;
}

function writeSessionSettingsFile(fs, sessionsDir, pid, lease, { env, userSettings }, ports) {
  fs.mkdirSync(sessionsDir, { recursive: true, mode: 0o700 });
  try { fs.chmodSync?.(sessionsDir, 0o700); } catch {}
  const { settings } = buildClaudeGatewaySettingsOverlay(lease, { env, userSettings }, ports);
  const fileName = `settings-${pid}-${randomBytes(6).toString('hex')}.json`;
  const settingsPath = join(sessionsDir, fileName);
  writePrivateAtomic(fs, settingsPath, `${JSON.stringify(settings, null, 2)}\n`);
  return settingsPath;
}

function normalizeLeaseRecord(reply, nowMs) {
  const lease = reply?.lease ?? {};
  const token = String(lease.claude_oauth_token || lease.gateway_bearer_token || '').trim();
  if (!token) {
    throw new CloudAccountsError('PDD Cloud Claude lease did not include a gateway grant token.', {
      code: 'invalid_lease',
    });
  }
  rememberSecrets(token);
  return {
    lease_id: lease.lease_id ?? null,
    account_id: reply?.account?.account_id ?? null,
    label: reply?.account?.label ?? null,
    delivery_mode: lease.delivery_mode ?? 'gateway_grant',
    anthropic_base_url: lease.anthropic_base_url ?? null,
    claude_oauth_token: token,
    gateway_bearer_token: token,
    expires_at: lease.expires_at ?? null,
    auto_rotate: lease.auto_rotate !== false,
    created_at: new Date(nowMs).toISOString(),
    last_heartbeat_at: new Date(nowMs).toISOString(),
  };
}

export async function acquireSharedClaudeRuntimeSession({
  cwd = process.cwd(),
  env = process.env,
  pid = process.pid,
  userSettings = null,
} = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = ports.now ?? Date.now;
  const isPidAlive = ports.isPidAlive ?? defaultIsPidAlive;
  const leaseFn = ports.leaseCloudAccount ?? leaseCloudAccount;

  const runtimeRoot = resolveClaudeRuntimeRoot(env);
  assertSafePrivateDir(fs, runtimeRoot);
  const runtimeDir = sharedClaudeRuntimeDir(env, ports.uid);
  const pidsDir = join(runtimeDir, 'pids');
  const sessionsDir = join(runtimeDir, 'sessions');
  const leasePath = join(runtimeDir, 'lease.json');

  try {
    restoreLocalClaudeGatewayConfig({ env, removeManagedFile: false }, ports);
  } catch {}

  return await withClaudeRuntimeLock(runtimeDir, async () => {
    fs.mkdirSync(pidsDir, { recursive: true, mode: 0o700 });
    fs.mkdirSync(sessionsDir, { recursive: true, mode: 0o700 });
    const livePids = sweepDeadPids(fs, pidsDir, isPidAlive);
    sweepStaleSessionFiles(fs, sessionsDir, livePids);

    let leaseMeta = readJsonFileQuiet(fs, leasePath);
    let reused = true;
    if (!isReusableClaudeLease(leaseMeta, now())) {
      reused = false;
      const reply = await leaseFn({
        provider: 'claude',
        holderId: 'pdd-claude-shared',
        autoRotate: true,
        updateState: false,
      }, { cwd, env }, ports);
      if (reply?.state !== 'leased' || !reply?.lease) {
        const wake = reply?.wake_at ? ` Next ready at ${reply.wake_at}.` : '';
        throw new CloudAccountsError(
          `No ready PDD Cloud Claude account is available (${reply?.state || 'unavailable'}).${wake} Run \`pdd accounts list\` to inspect your pool.`,
          { code: 'no_ready_account', exitCode: 1 },
        );
      }
      leaseMeta = normalizeLeaseRecord(reply, now());
      writePrivateAtomic(fs, leasePath, `${JSON.stringify(leaseMeta, null, 2)}\n`);
    } else {
      rememberSecrets(leaseMeta.claude_oauth_token, leaseMeta.gateway_bearer_token);
    }

    const settingsPath = writeSessionSettingsFile(fs, sessionsDir, pid, leaseMeta, { env, userSettings }, ports);
    writePrivateAtomic(fs, join(pidsDir, String(pid)), `${JSON.stringify({ pid, startedAt: now() })}\n`);

    return {
      mode: 'shared',
      runtimeDir,
      leasePath,
      settingsPath,
      pid,
      reused,
      lease: leaseMeta,
    };
  }, ports);
}

export async function releaseSharedClaudeRuntimeSession(session, { cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  if (!session?.runtimeDir) return { releasedLeaseId: null };
  const fs = ports.fs ?? nativeFs;
  const isPidAlive = ports.isPidAlive ?? defaultIsPidAlive;
  const releaseFn = ports.releaseCloudLease ?? releaseCloudLease;
  const pidsDir = join(session.runtimeDir, 'pids');
  const sessionsDir = join(session.runtimeDir, 'sessions');
  const leasePath = join(session.runtimeDir, 'lease.json');

  unlinkQuiet(fs, session.settingsPath);

  let leaseIdToRevoke = null;
  await withClaudeRuntimeLock(session.runtimeDir, async () => {
    unlinkQuiet(fs, join(pidsDir, String(session.pid)));
    const remaining = sweepDeadPids(fs, pidsDir, isPidAlive);
    sweepStaleSessionFiles(fs, sessionsDir, remaining);
    if (remaining.length === 0) {
      const meta = readJsonFileQuiet(fs, leasePath);
      if (typeof meta?.lease_id === 'string' && meta.lease_id.trim()) {
        leaseIdToRevoke = meta.lease_id.trim();
      }
      unlinkQuiet(fs, leasePath);
    }
  }, ports);

  if (leaseIdToRevoke) {
    try {
      await releaseFn(leaseIdToRevoke, { cwd, env }, ports);
    } catch {}
  }
  return { releasedLeaseId: leaseIdToRevoke };
}

export async function acquirePinnedClaudeRuntimeSession({
  preferredAccount,
  cwd = process.cwd(),
  env = process.env,
  pid = process.pid,
  userSettings = null,
} = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = ports.now ?? Date.now;
  const leaseFn = ports.leaseCloudAccount ?? leaseCloudAccount;

  const runtimeRoot = resolveClaudeRuntimeRoot(env);
  assertSafePrivateDir(fs, runtimeRoot);
  const runtimeDir = fs.mkdtempSync(join(runtimeRoot, 'pdd-claude-pin-'));
  try { fs.chmodSync?.(runtimeDir, 0o700); } catch {}

  try {
    restoreLocalClaudeGatewayConfig({ env, removeManagedFile: false }, ports);
  } catch {}

  try {
    const reply = await leaseFn({
      provider: 'claude',
      preferredLabel: preferredAccount,
      holderId: `pdd-claude-pin-${pid}`,
      autoRotate: false,
      updateState: false,
    }, { cwd, env }, ports);
    if (reply?.state !== 'leased' || !reply?.lease) {
      const wake = reply?.wake_at ? ` Next ready at ${reply.wake_at}.` : '';
      throw new CloudAccountsError(
        `Could not lease PDD Cloud Claude account "${preferredAccount}" (${reply?.state || 'unavailable'}).${wake} Run \`pdd accounts list\` to inspect your pool.`,
        { code: 'no_ready_account', exitCode: 1 },
      );
    }
    const leaseMeta = { ...normalizeLeaseRecord(reply, now()), auto_rotate: false };
    const leasePath = join(runtimeDir, 'lease.json');
    writePrivateAtomic(fs, leasePath, `${JSON.stringify(leaseMeta, null, 2)}\n`);
    const settingsPath = writeSessionSettingsFile(fs, join(runtimeDir, 'sessions'), pid, leaseMeta, { env, userSettings }, ports);
    return {
      mode: 'pinned',
      runtimeDir,
      leasePath,
      settingsPath,
      pid,
      reused: false,
      lease: leaseMeta,
    };
  } catch (err) {
    try { fs.rmSync(runtimeDir, { recursive: true, force: true }); } catch {}
    throw err;
  }
}

export async function releasePinnedClaudeRuntimeSession(session, { cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  if (!session?.runtimeDir) return { releasedLeaseId: null };
  const fs = ports.fs ?? nativeFs;
  const releaseFn = ports.releaseCloudLease ?? releaseCloudLease;
  const leaseId = typeof session.lease?.lease_id === 'string' && session.lease.lease_id.trim()
    ? session.lease.lease_id.trim()
    : null;
  try { fs.rmSync(session.runtimeDir, { recursive: true, force: true }); } catch {}
  if (leaseId) {
    try {
      await releaseFn(leaseId, { cwd, env }, ports);
    } catch {}
  }
  return { releasedLeaseId: leaseId };
}

export function startClaudeLeaseHeartbeat(session, { cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  if (!session?.lease?.lease_id) return () => {};
  const fs = ports.fs ?? nativeFs;
  const now = ports.now ?? Date.now;
  const heartbeatFn = ports.heartbeatCloudLease ?? heartbeatCloudLease;
  const intervalMs = ports.heartbeatIntervalMs ?? DEFAULT_HEARTBEAT_INTERVAL_MS;
  const minSpacingMs = Math.max(1_000, Math.floor(intervalMs * 0.6));

  let stopped = false;
  let timer = null;

  const scheduleNext = () => {
    if (stopped) return;
    const jitter = Math.floor(Math.random() * Math.min(30_000, Math.floor(intervalMs * 0.15)));
    timer = setTimeout(tick, intervalMs + jitter);
    timer.unref?.();
  };

  const tick = async () => {
    if (stopped) return;
    try {
      const meta = readJsonFileQuiet(fs, session.leasePath);
      const leaseId = typeof meta?.lease_id === 'string' && meta.lease_id.trim()
        ? meta.lease_id.trim()
        : null;
      if (!leaseId) {
        stopped = true;
        return;
      }
      const lastBeatMs = Date.parse(String(meta?.last_heartbeat_at ?? ''));
      if (Number.isFinite(lastBeatMs) && (now() - lastBeatMs) < minSpacingMs) {
        scheduleNext();
        return;
      }
      const beat = await heartbeatFn(leaseId, { cwd, env }, ports);
      if (stopped) return;
      const persistUpdate = async () => {
        const latest = readJsonFileQuiet(fs, session.leasePath);
        if (!latest || latest.lease_id !== leaseId) return;
        const updated = {
          ...latest,
          expires_at: beat?.expires_at ?? latest.expires_at,
          account_id: beat?.account_id ?? latest.account_id,
          last_heartbeat_at: new Date(now()).toISOString(),
        };
        writePrivateAtomic(fs, session.leasePath, `${JSON.stringify(updated, null, 2)}\n`);
      };
      if (session.mode === 'shared') {
        await withClaudeRuntimeLock(session.runtimeDir, persistUpdate, ports);
      } else {
        await persistUpdate();
      }
    } catch (err) {
      const status = err?.status ?? 0;
      if (status === 401 || status === 403 || status === 404) {
        const clearDeadLease = async () => {
          unlinkQuiet(fs, session.leasePath);
        };
        try {
          if (session.mode === 'shared') {
            await withClaudeRuntimeLock(session.runtimeDir, clearDeadLease, ports);
          } else {
            await clearDeadLease();
          }
        } catch {}
        stopped = true;
        return;
      }
    }
    scheduleNext();
  };

  scheduleNext();
  return () => {
    stopped = true;
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  };
}

export async function logoutSharedClaudeRuntime({ cwd = process.cwd(), env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const releaseFn = ports.releaseCloudLease ?? releaseCloudLease;
  const runtimeDir = sharedClaudeRuntimeDir(env, ports.uid);
  const leasePath = join(runtimeDir, 'lease.json');
  const sessionsDir = join(runtimeDir, 'sessions');

  let revokedLeaseId = null;
  if (fs.existsSync?.(runtimeDir)) {
    await withClaudeRuntimeLock(runtimeDir, async () => {
      const meta = readJsonFileQuiet(fs, leasePath);
      if (typeof meta?.lease_id === 'string' && meta.lease_id.trim()) {
        revokedLeaseId = meta.lease_id.trim();
      }
      unlinkQuiet(fs, leasePath);
      try {
        for (const name of fs.readdirSync(sessionsDir)) {
          unlinkQuiet(fs, join(sessionsDir, name));
        }
      } catch {}
    }, ports);
  }

  if (revokedLeaseId) {
    try {
      await releaseFn(revokedLeaseId, { cwd, env }, ports);
    } catch {}
  }

  const restored = restoreLocalClaudeGatewayConfig({ env }, ports);
  return { revokedLeaseId, restored };
}

function spawnClaudePassthrough(claudeBin, args, { cwd, env }, ports = {}) {
  const spawnImpl = ports.spawn ?? nativeSpawn;
  return new Promise(resolveExit => {
    let child;
    try {
      child = spawnImpl(claudeBin, args, { cwd, env, stdio: 'inherit' });
    } catch (err) {
      resolveExit({ exitCode: err?.code === 'ENOENT' ? 127 : 1, error: err });
      return;
    }
    const forward = sig => {
      try { child.kill?.(sig); } catch {}
    };
    const onSigInt = () => forward('SIGINT');
    const onSigTerm = () => forward('SIGTERM');
    const onSigHup = () => forward('SIGHUP');
    process.on('SIGINT', onSigInt);
    process.on('SIGTERM', onSigTerm);
    process.on('SIGHUP', onSigHup);

    const detach = () => {
      process.off('SIGINT', onSigInt);
      process.off('SIGTERM', onSigTerm);
      process.off('SIGHUP', onSigHup);
    };

    child.on('error', err => {
      detach();
      resolveExit({ exitCode: err?.code === 'ENOENT' ? 127 : 1, error: err });
    });
    child.on('close', (code, signal) => {
      detach();
      if (typeof code === 'number') resolveExit({ exitCode: code });
      else if (signal === 'SIGINT') resolveExit({ exitCode: 130 });
      else if (signal === 'SIGTERM') resolveExit({ exitCode: 143 });
      else if (signal === 'SIGHUP') resolveExit({ exitCode: 129 });
      else resolveExit({ exitCode: 1 });
    });
  });
}

export async function runPddClaudeCli(argv = [], {
  cwd = process.cwd(),
  env = process.env,
  stdout = process.stdout,
  stderr = process.stderr,
} = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const claudeBin = ports.claudeBin ?? (typeof env?.PDD_CLAUDE_BIN === 'string' && env.PDD_CLAUDE_BIN.trim() ? env.PDD_CLAUDE_BIN.trim() : 'claude');

  let parsed;
  try {
    parsed = parsePddClaudeArgs(argv);
  } catch (err) {
    stderr.write(`${redactSecrets(err?.message || String(err))}\n`);
    return { exitCode: err?.exitCode ?? 2 };
  }

  if (parsed.showPddHelp) {
    stdout.write(PDD_CLAUDE_HELP_TEXT);
    return { exitCode: 0 };
  }

  const inspection = inspectClaudeInvocation(parsed.claudeArgs);

  if (inspection.mode === 'logout') {
    try {
      const res = await logoutSharedClaudeRuntime({ cwd, env }, ports);
      if (res.revokedLeaseId) {
        stdout.write('Ended shared pdd-claude session and revoked its PDD Cloud lease. Your personal ~/.claude login was not modified.\n');
      } else {
        stdout.write('No active shared pdd-claude session found. Your personal ~/.claude login was not modified.\n');
      }
      return { exitCode: 0 };
    } catch (err) {
      stderr.write(`${redactSecrets(err?.message || String(err))}\n`);
      return { exitCode: err?.exitCode ?? 1 };
    }
  }

  if (inspection.mode === 'login_hint') {
    stdout.write(
      'pdd-claude uses your PDD Cloud shared account pool and never modifies your personal Claude login.\n'
      + '  - Enroll a Claude account into PDD Cloud: pdd accounts add --provider claude\n'
      + '  - End the shared pdd-claude session:      pdd-claude logout\n'
      + '  - Manage your personal Claude login:      claude auth login / claude auth logout\n',
    );
    return { exitCode: 0 };
  }

  if (inspection.mode === 'pass_through') {
    const res = await spawnClaudePassthrough(claudeBin, parsed.claudeArgs, { cwd, env }, ports);
    if (res.error) {
      stderr.write(`Failed to launch "${claudeBin}": ${redactSecrets(res.error.message || String(res.error))}\n`);
    }
    return { exitCode: res.exitCode };
  }

  if (inspection.hasBareFlag) {
    stderr.write('Warning: `claude --bare` disables OAuth authentication in Claude Code; pdd-claude pool tokens require standard mode (without `--bare`).\n');
  }

  let extracted;
  try {
    extracted = extractAndParseUserClaudeSettings(parsed.claudeArgs, { cwd, fs });
  } catch (err) {
    stderr.write(`${redactSecrets(err?.message || String(err))}\n`);
    return { exitCode: err?.exitCode ?? 2 };
  }

  let session = null;
  let stopHeartbeat = () => {};
  try {
    session = parsed.preferredAccount
      ? await acquirePinnedClaudeRuntimeSession({
          preferredAccount: parsed.preferredAccount,
          cwd,
          env,
          pid: ports.pid ?? process.pid,
          userSettings: extracted.userSettings,
        }, ports)
      : await acquireSharedClaudeRuntimeSession({
          cwd,
          env,
          pid: ports.pid ?? process.pid,
          userSettings: extracted.userSettings,
        }, ports);

    stopHeartbeat = startClaudeLeaseHeartbeat(session, { cwd, env }, ports);

    const finalArgs = injectClaudeSettingsArg(extracted.strippedArgs, session.settingsPath);
    const childEnv = buildPddClaudeChildEnv(env);
    const res = await spawnClaudePassthrough(claudeBin, finalArgs, { cwd, env: childEnv }, ports);
    if (res.error) {
      stderr.write(`Failed to launch "${claudeBin}": ${redactSecrets(res.error.message || String(res.error))}\n`);
    }
    return { exitCode: res.exitCode };
  } catch (err) {
    stderr.write(`${redactSecrets(err?.message || String(err))}\n`);
    return { exitCode: err?.exitCode ?? 1 };
  } finally {
    stopHeartbeat();
    if (session) {
      try {
        if (session.mode === 'pinned') {
          await releasePinnedClaudeRuntimeSession(session, { cwd, env }, ports);
        } else {
          await releaseSharedClaudeRuntimeSession(session, { cwd, env }, ports);
        }
      } catch {}
    }
  }
}
