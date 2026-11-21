// Generated from prompts/cli/login-pool.prompt.md.
// Layer-2 Autopilot local-folder `pool.json` loader, cooldown ledger, and login selector.
import * as nativeFs from 'node:fs';
import { dirname, isAbsolute, join, resolve } from 'node:path';
import {
  ALL_CONFIG_VARS,
  ALL_FOLDER_KEYS,
  CONFIG_VAR,
  FOLDER_KEY,
  KINDS,
  POOL_FALLBACK_COOLDOWN_MS,
  isCreditOrResetAccount,
  loginEnvironment,
} from '../accounts/pool-env.mjs';
import * as codexLimitsModule from '../codex-limits.mjs';
import { knownSecretValues, rememberSecrets } from '../secret-redaction.mjs';
import { agyStatus, parseAgentAuthStatus, runAgentProcess } from '../shared/agent-process.mjs';
import { readJsonObjectQuiet, writeAtomicPrivate } from '../shared/atomic-fs.mjs';
import { readBoundedUtf8 } from '../shared/safe-read.mjs';

const readCodexLimits = (...args) => codexLimitsModule.readCodexLimits(...args);

const ENTRY_KEYS = new Set([
  'id', 'kind', 'command', 'model', 'plan', 'credits',
  'allowReset', 'allow_reset', 'paused', ...ALL_FOLDER_KEYS, 'env',
]);
const TOP_KEYS = new Set(['reset', 'weeklyStopPercent', 'logins']);
const CONTROLS = /[\u0000-\u001f\u007f-\u009f]/;
const SECRET_ENV_KEY = /(?:_TOKEN|_SECRET|_API_KEY|_PASSWORD|_CREDENTIAL|^SECRET_|API_KEY$|^OPENAI_API_KEY$|^ANTHROPIC_API_KEY$|^GEMINI_API_KEY$|^GOOGLE_API_KEY$|^CLAUDE_CODE_OAUTH_TOKEN$|^CODEX_ACCESS_TOKEN$)/i;

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const bad = message => { throw new Error(`Invalid login pool: ${message}`); };

function expandPoolHome(value, home) {
  if (value === '~' || value.startsWith('~/')) {
    if (typeof home !== 'string' || !home) bad('HOME is required for tilde paths.');
    return value === '~' ? home : join(home, value.slice(2));
  }
  return value;
}

function statNoFollow(fs, filePath) {
  try {
    return (fs.lstatSync ?? nativeFs.lstatSync)(filePath);
  } catch (error) {
    if (error?.code === 'ENOENT') return null;
    bad('cannot inspect pool file.');
  }
}

function readPoolJson(fs, filePath) {
  const info = statNoFollow(fs, filePath);
  if (!info) bad(`file not found at ${filePath}.`);
  if (!info.isFile() || info.isSymbolicLink()) bad('pool file must be a regular file and not a symlink.');
  if (info.size > 65_536) bad('pool file exceeds 65536 bytes.');
  let raw;
  try {
    raw = readBoundedUtf8(filePath, { maxBytes: 65_536, noFollow: true, fs });
  } catch (error) {
    if (error?.code === 'file_too_large') bad('pool file exceeds 65536 bytes.');
    if (error?.code === 'not_regular_file') bad('pool file must be regular and at most 65536 bytes.');
    bad('cannot read pool file.');
  }
  try {
    return JSON.parse(raw);
  } catch {
    bad('pool file must contain valid JSON.');
  }
}

export function resolvePoolPath({ cwd = process.cwd(), env = process.env, poolPath } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  if (poolPath !== undefined && poolPath !== null) {
    if (typeof poolPath !== 'string' || !poolPath.trim() || CONTROLS.test(poolPath)) {
      bad('pool path must be a nonblank path or off.');
    }
    const trimmed = poolPath.trim();
    if (trimmed === 'off' || trimmed === 'none') return null;
    return resolve(cwd, expandPoolHome(trimmed, env.HOME));
  }
  const candidates = [];
  const xdg = typeof env.XDG_CONFIG_HOME === 'string' && env.XDG_CONFIG_HOME.trim()
    ? env.XDG_CONFIG_HOME.trim()
    : (typeof env.HOME === 'string' && env.HOME ? join(env.HOME, '.config') : '');
  if (xdg) candidates.push(join(xdg, 'pdd', 'pool.json'));
  if (typeof env.HOME === 'string' && env.HOME) candidates.push(join(env.HOME, '.pdd', 'pool.json'));
  for (const candidate of candidates) {
    if (statNoFollow(fs, candidate)) return candidate;
  }
  return null;
}

function normalizeFallback(fallbackAgent, env) {
  const kind = KINDS.includes(fallbackAgent?.kind) ? fallbackAgent.kind : 'codex';
  const id = typeof fallbackAgent?.id === 'string' && /^[A-Za-z0-9._-]{1,80}$/.test(fallbackAgent.id) ? fallbackAgent.id : kind;
  const command = typeof fallbackAgent?.command === 'string' && fallbackAgent.command.trim() ? fallbackAgent.command.trim() : kind;
  const model = typeof fallbackAgent?.model === 'string' && fallbackAgent.model.trim() ? fallbackAgent.model.trim() : null;
  const configVar = CONFIG_VAR[kind];
  const configDir = typeof env?.[configVar] === 'string' && env[configVar].trim() ? env[configVar].trim() : null;
  return {
    id,
    kind,
    command,
    model,
    plan: null,
    credits: fallbackAgent?.credits === true,
    allowReset: fallbackAgent?.allowReset === true || fallbackAgent?.allow_reset === true,
    paused: false,
    configVar,
    configDir,
    env: object(fallbackAgent?.env) ? { ...fallbackAgent.env } : {},
  };
}

export function loadLoginPool({ cwd = process.cwd(), env = process.env, poolPath, fallbackAgent } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const resolved = resolvePoolPath({ cwd, env, poolPath }, { fs });
  if (!resolved) {
    return {
      configured: false,
      poolPath: null,
      reset: 'never',
      weeklyStopPercent: 97,
      logins: [normalizeFallback(fallbackAgent, env)],
    };
  }
  const config = readPoolJson(fs, resolved);
  if (!object(config) || Object.keys(config).some(k => !TOP_KEYS.has(k))) {
    bad('expected an object with logins, optional weeklyStopPercent and optional reset.');
  }
  if ('reset' in config && config.reset !== 'never') {
    bad('reset must be "never"; Autopilot never spends reset credits.');
  }
  let weeklyStopPercent = 97;
  if ('weeklyStopPercent' in config) {
    if (
      typeof config.weeklyStopPercent !== 'number'
      || !Number.isFinite(config.weeklyStopPercent)
      || config.weeklyStopPercent <= 0
      || config.weeklyStopPercent > 100
    ) {
      bad('weeklyStopPercent must be a finite number in (0, 100].');
    }
    weeklyStopPercent = config.weeklyStopPercent;
  }
  if (!Array.isArray(config.logins) || config.logins.length < 1 || config.logins.length > 24) {
    bad('logins must be a non-empty array of at most 24 entries.');
  }
  const seenIds = new Set();
  const baseDir = dirname(resolved);
  const logins = config.logins.map(item => {
    if (!object(item) || Object.keys(item).some(k => !ENTRY_KEYS.has(k))) bad('invalid login entry.');
    if (!KINDS.includes(item.kind)) bad(`unknown login kind ${JSON.stringify(item.kind)} (expected codex, claude, gemini or agy).`);
    const id = item.id === undefined ? item.kind : item.id;
    if (typeof id !== 'string' || !/^[A-Za-z0-9._-]{1,80}$/.test(id)) bad('login id must match [A-Za-z0-9._-]{1,80}.');
    if (seenIds.has(id)) bad(`duplicate login id ${JSON.stringify(id)}.`);
    seenIds.add(id);
    const rawCmd = item.command === undefined ? item.kind : item.command;
    if (typeof rawCmd !== 'string' || !rawCmd.trim() || rawCmd.length > 4096 || CONTROLS.test(rawCmd)) bad(`invalid command for login ${id}.`);
    let command = expandPoolHome(rawCmd.trim(), env.HOME);
    if (!isAbsolute(command) && command.includes('/')) command = resolve(baseDir, command);
    let model = null;
    if (item.model !== undefined) {
      if (typeof item.model !== 'string' || !item.model.trim() || item.model.length > 200 || CONTROLS.test(item.model)) bad(`invalid model for login ${id}.`);
      model = item.model.trim();
    }
    let plan = null;
    if (item.plan !== undefined) {
      if (typeof item.plan !== 'string' || !item.plan.trim() || item.plan.length > 64 || CONTROLS.test(item.plan)) bad(`invalid plan for login ${id}.`);
      plan = item.plan.trim().toLowerCase();
    }
    if (item.credits !== undefined && typeof item.credits !== 'boolean') bad(`credits must be boolean for login ${id}.`);
    if (item.allowReset !== undefined && typeof item.allowReset !== 'boolean') bad(`allowReset must be boolean for login ${id}.`);
    if (item.allow_reset !== undefined && typeof item.allow_reset !== 'boolean') bad(`allow_reset must be boolean for login ${id}.`);
    if (item.paused !== undefined && typeof item.paused !== 'boolean') bad(`paused must be boolean for login ${id}.`);
    const ownFolderKey = FOLDER_KEY[item.kind];
    for (const key of Object.values(FOLDER_KEY)) {
      if (key !== ownFolderKey && item[key] !== undefined) bad(`${key} cannot be set on ${item.kind} login ${id}.`);
    }
    if (item[ownFolderKey] !== undefined && item.configHome !== undefined) bad(`set either ${ownFolderKey} or configHome on login ${id}, not both.`);
    const rawFolder = item[ownFolderKey] ?? item.configHome;
    let configDir = null;
    if (rawFolder !== undefined) {
      if (typeof rawFolder !== 'string' || !rawFolder.trim() || rawFolder.length > 4096 || CONTROLS.test(rawFolder)) bad(`invalid profile folder for login ${id}.`);
      configDir = resolve(baseDir, expandPoolHome(rawFolder.trim(), env.HOME));
    }
    const rawEnv = item.env === undefined ? {} : item.env;
    if (!object(rawEnv) || Object.keys(rawEnv).length > 32) bad(`invalid env map for login ${id}.`);
    const childEnv = {};
    for (const [k, v] of Object.entries(rawEnv)) {
      if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(k) || typeof v !== 'string' || v.length > 4096 || v.includes('\0')) bad(`invalid env entry ${k} on login ${id}.`);
      if (SECRET_ENV_KEY.test(k) || ALL_CONFIG_VARS.includes(k)) {
        bad(`env key ${k} is not permitted in pool.json; keep credentials in local CLI profile folders.`);
      }
      childEnv[k] = expandPoolHome(v, env.HOME);
    }
    return {
      id,
      kind: item.kind,
      command,
      model,
      plan,
      credits: item.credits === true,
      allowReset: item.allowReset === true || item.allow_reset === true,
      paused: item.paused === true,
      configVar: CONFIG_VAR[item.kind],
      configDir,
      env: childEnv,
    };
  });
  return { configured: true, poolPath: resolved, reset: 'never', weeklyStopPercent, logins };
}

const poolStatePath = stateRoot => join(stateRoot, 'login-pool.json');

export function readPoolCooldowns({ stateRoot, now = Date.now() } = {}, ports = {}) {
  if (!stateRoot) return {};
  const raw = readJsonObjectQuiet(ports.fs ?? nativeFs, poolStatePath(stateRoot));
  if (!object(raw?.logins)) return {};
  const active = {};
  for (const [id, row] of Object.entries(raw.logins)) {
    if (object(row) && typeof row.until === 'number' && Number.isFinite(row.until) && row.until > now) {
      active[id] = {
        until: row.until,
        resetAt: typeof row.resetAt === 'number' && Number.isFinite(row.resetAt) ? row.resetAt : null,
        reason: typeof row.reason === 'string' ? row.reason.slice(0, 200) : 'quota',
        at: typeof row.at === 'number' && Number.isFinite(row.at) ? row.at : now,
      };
    }
  }
  return active;
}

export function markLoginExhausted({ stateRoot, loginId, resetAt = null, reason = 'quota', now = Date.now() } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const validReset = typeof resetAt === 'number' && Number.isFinite(resetAt) && resetAt > now ? Math.ceil(resetAt) : null;
  const until = validReset ?? (now + POOL_FALLBACK_COOLDOWN_MS);
  const entry = {
    until,
    resetAt: validReset,
    reason: typeof reason === 'string' && reason.trim() ? reason.trim().slice(0, 200) : 'quota',
    at: now,
  };
  if (stateRoot && typeof loginId === 'string' && loginId) {
    const logins = readPoolCooldowns({ stateRoot, now }, { fs });
    logins[loginId] = entry;
    writeAtomicPrivate(fs, poolStatePath(stateRoot), `${JSON.stringify({ logins }, null, 2)}\n`);
  }
  return { id: loginId, ...entry };
}

export function clearPoolCooldowns({ stateRoot } = {}, ports = {}) {
  if (!stateRoot) return;
  const fs = ports.fs ?? nativeFs;
  try { (fs.rmSync ?? fs.unlinkSync)?.(poolStatePath(stateRoot), { force: true }); } catch {}
}

function hasExpiredClaudeCredentialsFile(fs, env, now) {
  if (env.CLAUDE_CODE_OAUTH_TOKEN || env.ANTHROPIC_API_KEY) return false;
  const base = env.CLAUDE_CONFIG_DIR || (env.HOME ? join(env.HOME, '.claude') : '');
  if (!base) return false;
  try {
    const settings = JSON.parse(fs.readFileSync(join(base, 'settings.json'), 'utf8'));
    rememberSecrets(...knownSecretValues(settings));
    if (settings?.env?.CLAUDE_CODE_OAUTH_TOKEN || settings?.env?.ANTHROPIC_API_KEY || settings?.apiKeyHelper) return false;
  } catch {}
  try {
    const creds = JSON.parse(fs.readFileSync(join(base, '.credentials.json'), 'utf8'));
    rememberSecrets(...knownSecretValues(creds));
    const oauth = object(creds?.claudeAiOauth) ? creds.claudeAiOauth : creds;
    const rawExp = oauth?.expiresAt ?? oauth?.expires_at;
    const expNum = typeof rawExp === 'number' ? rawExp : (typeof rawExp === 'string' && rawExp.trim() ? Number(rawExp) : NaN);
    const expMs = Number.isFinite(expNum) && expNum > 0
      ? (expNum > 1e11 ? expNum : expNum * 1000)
      : (typeof rawExp === 'string' ? Date.parse(rawExp) : NaN);
    const refresh = oauth?.refreshToken ?? oauth?.refresh_token;
    const hasRefresh = typeof refresh === 'string' && Boolean(refresh.trim());
    if (Number.isFinite(expMs) && expMs <= now && !hasRefresh) return true;
  } catch {}
  return false;
}

async function defaultProbeLogin(login, { cwd, env, fs = nativeFs, now = Date.now(), run = runAgentProcess }) {
  const exec = (args, opts = {}) => run(login.command, args, { cwd, env, input: '', timeoutMs: 10_000, maxBytes: 16_384, ...opts });
  try {
    if (login.kind === 'claude' && hasExpiredClaudeCredentialsFile(fs, env, now)) {
      return { ok: false, reason: 'expired' };
    }
    if (login.kind === 'codex' || login.kind === 'claude') {
      const status = await exec(login.kind === 'codex' ? ['login', 'status'] : ['auth', 'status', '--json']);
      return parseAgentAuthStatus({ agent: login.kind, result: status }) === 'ready' ? { ok: true } : { ok: false, reason: 'signed_out' };
    }
    if (login.kind === 'agy') {
      const status = await exec(['models']);
      return agyStatus(status) === 'ready' ? { ok: true } : { ok: false, reason: 'signed_out' };
    }
    if (login.kind === 'gemini') {
      const info = await exec(['--version']);
      if (info?.code !== 0) return { ok: false, reason: 'missing' };
      if (Boolean(env.GEMINI_API_KEY || env.GOOGLE_API_KEY) || env.GOOGLE_GENAI_USE_VERTEXAI === 'true' || env.GOOGLE_GENAI_USE_GCA === 'true') return { ok: true };
      const base = env.GEMINI_CLI_HOME || env.HOME || '';
      for (const candidate of [join(base, '.gemini', 'oauth_creds.json'), join(base, 'oauth_creds.json')]) {
        try {
          const creds = JSON.parse(fs.readFileSync(candidate, 'utf8'));
          rememberSecrets(...knownSecretValues(creds));
          if (typeof creds?.refresh_token === 'string' && creds.refresh_token) return { ok: true };
        } catch {}
      }
      return { ok: false, reason: 'signed_out' };
    }
  } catch {
    return { ok: false, reason: 'unavailable' };
  }
  return { ok: false, reason: 'unavailable' };
}

function agentSpecOf(login) {
  return {
    id: login.id,
    kind: login.kind,
    command: login.command,
    ...(login.model ? { model: login.model } : {}),
  };
}

export async function selectPoolLogin({
  cwd = process.cwd(),
  env = process.env,
  poolPath,
  pool: preloadedPool,
  fallbackAgent,
  stateRoot,
  allowLimited = false,
  allowCredits = false,
  allowedKinds,
} = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = (ports.now ?? Date.now)();
  const pool = preloadedPool ?? loadLoginPool({ cwd, env, poolPath, fallbackAgent }, { fs });
  const kindFilter = Array.isArray(allowedKinds) ? new Set(allowedKinds) : null;
  const active = pool.logins.filter(login => !login.paused && (!kindFilter || kindFilter.has(login.kind)));
  const eligible = active.filter(login => allowCredits || !isCreditOrResetAccount(login));
  if (kindFilter && eligible.length === 0) {
    return {
      state: 'unavailable',
      configured: pool.configured,
      poolPath: pool.poolPath,
      poolSize: 0,
      resetAt: null,
      cooling: [],
      unavailable: active.filter(login => !allowCredits && isCreditOrResetAccount(login)).map(login => ({ id: login.id, reason: 'credit_or_reset_guarded' })),
    };
  }
  const cooldowns = stateRoot ? readPoolCooldowns({ stateRoot, now }, { fs }) : {};
  const cooling = [];
  const unavailable = [];
  let fallbackLimited = null;

  for (const login of active) {
    if (!allowCredits && isCreditOrResetAccount(login)) {
      unavailable.push({ id: login.id, reason: 'credit_or_reset_guarded' });
      continue;
    }
    const cd = cooldowns[login.id];
    if (cd && cd.until > now) {
      cooling.push({ id: login.id, until: cd.until, resetAt: cd.resetAt ?? cd.until, reason: cd.reason });
      if (!allowLimited) continue;
    }
    const childEnv = loginEnvironment(env, login);
    const probe = ports.probeLogin
      ? await ports.probeLogin(login, childEnv)
      : await defaultProbeLogin(login, { cwd, env: childEnv, fs, now, run: ports.run });
    const probeOk = probe === true || probe?.ok === true;
    if (!probeOk) {
      unavailable.push({ id: login.id, reason: probe?.reason ?? 'unavailable' });
      continue;
    }
    if (login.kind === 'codex') {
      const limits = await (ports.readCodexLimits ?? readCodexLimits)(
        { command: login.command, cwd, env: childEnv, weeklyStopPercent: pool.weeklyStopPercent },
        ports.codexLimitPorts,
      );
      if (limits.state === 'limited') {
        const entry = markLoginExhausted({
          stateRoot,
          loginId: login.id,
          resetAt: limits.resetAt,
          reason: limits.usedPercent != null ? `usage-limit (${limits.usedPercent}%)` : 'usage-limit',
          now,
        }, { fs });
        if (!cooling.some(row => row.id === login.id)) cooling.push({ id: login.id, until: entry.until, resetAt: entry.resetAt ?? entry.until, reason: entry.reason });
        if (allowLimited && !fallbackLimited) fallbackLimited = { login, env: childEnv };
        continue;
      }
      if (limits.state === 'unknown' && (login.plan === 'pro' || isCreditOrResetAccount(login))) {
        const entry = markLoginExhausted({
          stateRoot,
          loginId: login.id,
          resetAt: null,
          reason: 'pro-limits-unverified',
          now,
        }, { fs });
        if (!cooling.some(row => row.id === login.id)) cooling.push({ id: login.id, until: entry.until, resetAt: entry.until, reason: entry.reason });
        continue;
      }
    }
    if (cd && cd.until > now && allowLimited) {
      if (!fallbackLimited) fallbackLimited = { login, env: childEnv };
      continue;
    }
    return {
      state: 'ready',
      configured: pool.configured,
      poolPath: pool.poolPath,
      poolSize: eligible.length,
      login,
      agent: agentSpecOf(login),
      env: childEnv,
    };
  }

  if (allowLimited && fallbackLimited) {
    return {
      state: 'ready',
      limited: true,
      configured: pool.configured,
      poolPath: pool.poolPath,
      poolSize: eligible.length,
      login: fallbackLimited.login,
      agent: agentSpecOf(fallbackLimited.login),
      env: fallbackLimited.env,
    };
  }

  const resetTimes = cooling.map(row => row.until).filter(v => typeof v === 'number' && Number.isFinite(v));
  return {
    state: 'exhausted',
    configured: pool.configured,
    poolPath: pool.poolPath,
    poolSize: eligible.length,
    resetAt: resetTimes.length ? Math.min(...resetTimes) : null,
    cooling,
    unavailable,
  };
}
