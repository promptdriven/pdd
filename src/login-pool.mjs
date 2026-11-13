// Generated from prompts/cli/login-pool.prompt.md (sha256: c2de39ef404f8630e517be9dab8bf7060157d5145d955ef0367e8a456934695c).
import * as nativeFs from 'node:fs';
import { dirname, isAbsolute, join, resolve } from 'node:path';
import { randomUUID } from 'node:crypto';
import { parseAgentAuthStatus, runAgentProcess } from './agent-adapters.mjs';
import { readCodexLimits } from './codex-limits.mjs';
import { knownSecretValues, rememberSecrets } from './secret-redaction.mjs';
import { checkWorkflowAgents } from './workflow-agents.mjs';

const KINDS = ['codex', 'claude', 'gemini', 'agy'];
const CONFIG_VAR = Object.freeze({
  codex: 'CODEX_HOME',
  claude: 'CLAUDE_CONFIG_DIR',
  gemini: 'GEMINI_CLI_HOME',
  agy: 'ANTIGRAVITY_APP_DATA_DIR',
});
const FOLDER_KEY = Object.freeze({
  codex: 'codexHome',
  claude: 'claudeConfigDir',
  gemini: 'geminiCliHome',
  agy: 'appDataDir',
});
const ALL_CONFIG_VARS = Object.values(CONFIG_VAR);
const ALL_FOLDER_KEYS = [...Object.values(FOLDER_KEY), 'configHome'];
const ENTRY_KEYS = new Set(['id', 'kind', 'command', 'model', 'plan', 'credits', 'paused', ...ALL_FOLDER_KEYS, 'env']);
const TOP_KEYS = new Set(['reset', 'weeklyStopPercent', 'logins']);
const CONTROLS = /[\u0000-\u001f\u007f-\u009f]/;
const SECRET_ENV_KEY = /(?:_TOKEN|_SECRET|_API_KEY|_PASSWORD|_CREDENTIAL|^SECRET_|API_KEY$|^OPENAI_API_KEY$|^ANTHROPIC_API_KEY$|^GEMINI_API_KEY$|^GOOGLE_API_KEY$|^CLAUDE_CODE_OAUTH_TOKEN$|^CODEX_ACCESS_TOKEN$)/i;
export const POOL_FALLBACK_COOLDOWN_MS = 30 * 60 * 1000;

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const bad = message => { throw new Error(`Invalid login pool: ${message}`); };

function expandHome(value, home) {
  if (value === '~' || value.startsWith('~/')) {
    if (typeof home !== 'string' || !home) bad('HOME is required for tilde paths.');
    return value === '~' ? home : join(home, value.slice(2));
  }
  return value;
}

function statNoFollow(fs, path) {
  try { return (fs.lstatSync ?? nativeFs.lstatSync)(path); }
  catch (error) { if (error?.code === 'ENOENT') return null; bad('cannot inspect pool file.'); }
}

function readPoolJson(fs, path) {
  const info = statNoFollow(fs, path);
  if (!info) bad(`file not found at ${path}.`);
  if (!info.isFile() || info.isSymbolicLink()) bad('pool file must be a regular file and not a symlink.');
  if (info.size > 65_536) bad('pool file exceeds 65536 bytes.');
  if (fs.openSync && fs.fstatSync && fs.readSync && fs.closeSync || fs === nativeFs) {
    const f = fs.openSync ? fs : nativeFs;
    const flags = (f.constants?.O_RDONLY ?? 0) | (f.constants?.O_NOFOLLOW ?? 0) | (f.constants?.O_NONBLOCK ?? 0);
    let fd;
    try {
      fd = f.openSync(path, flags);
      const actual = f.fstatSync(fd);
      if (!actual.isFile() || actual.size > 65_536) bad('pool file must be regular and at most 65536 bytes.');
      const buf = Buffer.alloc(65_537);
      let len = 0;
      while (len < buf.length) {
        const n = f.readSync(fd, buf, len, buf.length - len, null);
        if (!n) break;
        len += n;
      }
      if (len > 65_536) bad('pool file exceeds 65536 bytes.');
      try { return JSON.parse(buf.subarray(0, len).toString('utf8')); }
      catch { bad('pool file must contain valid JSON.'); }
    } catch (error) {
      if (error?.message?.startsWith('Invalid login pool:')) throw error;
      bad('cannot read pool file.');
    } finally {
      if (fd !== undefined) try { f.closeSync(fd); } catch {}
    }
  }
  let raw;
  try { raw = fs.readFileSync(path, 'utf8'); } catch { bad('cannot read pool file.'); }
  if (Buffer.byteLength(raw, 'utf8') > 65_536) bad('pool file exceeds 65536 bytes.');
  try { return JSON.parse(raw); } catch { bad('pool file must contain valid JSON.'); }
}

export function resolvePoolPath({ cwd = process.cwd(), env = process.env, poolPath } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  if (poolPath !== undefined && poolPath !== null) {
    if (typeof poolPath !== 'string' || !poolPath.trim() || CONTROLS.test(poolPath)) bad('pool path must be a nonblank path or off.');
    const trimmed = poolPath.trim();
    if (trimmed === 'off' || trimmed === 'none') return null;
    return resolve(cwd, expandHome(trimmed, env.HOME));
  }
  const candidates = [];
  const xdg = typeof env.XDG_CONFIG_HOME === 'string' && env.XDG_CONFIG_HOME.trim() ? env.XDG_CONFIG_HOME.trim()
    : typeof env.HOME === 'string' && env.HOME ? join(env.HOME, '.config') : '';
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
    credits: false,
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
  if (!object(config) || Object.keys(config).some(k => !TOP_KEYS.has(k))) bad('expected an object with logins, optional weeklyStopPercent and optional reset.');
  if ('reset' in config && config.reset !== 'never') bad('reset must be "never"; Autopilot never spends reset credits.');
  let weeklyStopPercent = 97;
  if ('weeklyStopPercent' in config) {
    if (typeof config.weeklyStopPercent !== 'number' || !Number.isFinite(config.weeklyStopPercent) || config.weeklyStopPercent <= 0 || config.weeklyStopPercent > 100) {
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
    let command = expandHome(rawCmd.trim(), env.HOME);
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
      configDir = resolve(baseDir, expandHome(rawFolder.trim(), env.HOME));
    }
    const rawEnv = item.env === undefined ? {} : item.env;
    if (!object(rawEnv) || Object.keys(rawEnv).length > 32) bad(`invalid env map for login ${id}.`);
    const childEnv = {};
    for (const [k, v] of Object.entries(rawEnv)) {
      if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(k) || typeof v !== 'string' || v.length > 4096 || v.includes('\0')) bad(`invalid env entry ${k} on login ${id}.`);
      if (SECRET_ENV_KEY.test(k) || ALL_CONFIG_VARS.includes(k)) {
        bad(`env key ${k} is not permitted in pool.json; keep credentials in local CLI profile folders.`);
      }
      childEnv[k] = expandHome(v, env.HOME);
    }
    return {
      id,
      kind: item.kind,
      command,
      model,
      plan,
      credits: item.credits === true,
      paused: item.paused === true,
      configVar: CONFIG_VAR[item.kind],
      configDir,
      env: childEnv,
    };
  });
  return { configured: true, poolPath: resolved, reset: 'never', weeklyStopPercent, logins };
}

export function loginEnvironment(baseEnv = process.env, login) {
  const out = {};
  for (const [k, v] of Object.entries(baseEnv ?? {})) {
    if (typeof v === 'string') out[k] = v;
  }
  for (const key of [...ALL_CONFIG_VARS, 'CLAUDECODE']) delete out[key];
  if (login?.configVar && login?.configDir) out[login.configVar] = login.configDir;
  for (const [k, v] of Object.entries(login?.env ?? {})) {
    if (typeof v === 'string') out[k] = v;
  }
  return out;
}

export function isQuotaExhaustionMessage(text) {
  if (typeof text !== 'string') return false;
  const s = text.trim();
  if (!s) return false;
  if (/\b(?:test|tests|spec|specs|assert|assertion|expected|fixture|fixtures)\b/i.test(s)
    && /\b(?:fail|failed|expected|got|fixture|spec)\b/i.test(s)) return false;
  return /out of credits|credit balance is too low|insufficient[_ ]quota|exceeded your current quota|quota (?:exceeded|has been exhausted|exhausted)|resource_exhausted|hit your usage limit|usage[_ ]limit|weekly limit|daily limit|monthly limit|spend[_ ]control|spending limit|rate[_ ]limit|too many requests|\b(?:status|http|error|code)[:\s]+429\b|\b429\s+too many requests\b/i.test(s);
}

const poolStatePath = stateRoot => join(stateRoot, 'login-pool.json');

export function readPoolCooldowns({ stateRoot, now = Date.now() } = {}, ports = {}) {
  if (!stateRoot) return {};
  const fs = ports.fs ?? nativeFs;
  try {
    const raw = JSON.parse(fs.readFileSync(poolStatePath(stateRoot), 'utf8'));
    if (!object(raw) || !object(raw.logins)) return {};
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
  } catch {
    return {};
  }
}

function writePoolCooldowns(fs, stateRoot, logins) {
  if (!stateRoot) return;
  fs.mkdirSync(stateRoot, { recursive: true, mode: 0o700 });
  const target = poolStatePath(stateRoot);
  const tmp = `${target}.${process.pid}.${randomUUID()}.tmp`;
  fs.writeFileSync(tmp, `${JSON.stringify({ logins }, null, 2)}\n`, { mode: 0o600 });
  try { fs.chmodSync?.(tmp, 0o600); } catch {}
  fs.renameSync(tmp, target);
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
    writePoolCooldowns(fs, stateRoot, logins);
  }
  return { id: loginId, ...entry };
}

export function clearPoolCooldowns({ stateRoot } = {}, ports = {}) {
  if (!stateRoot) return;
  const fs = ports.fs ?? nativeFs;
  try { (fs.rmSync ?? fs.unlinkSync)?.(poolStatePath(stateRoot), { force: true }); } catch {}
}

async function defaultProbeLogin(login, { cwd, env, fs = nativeFs, run = runAgentProcess }) {
  const exec = (args, opts = {}) => run(login.command, args, { cwd, env, input: '', timeoutMs: 10_000, maxBytes: 16_384, ...opts });
  try {
    if (login.kind === 'codex' || login.kind === 'claude') {
      const status = await exec(login.kind === 'codex' ? ['login', 'status'] : ['auth', 'status', '--json']);
      return parseAgentAuthStatus({ agent: login.kind, result: status }) === 'ready' ? { ok: true } : { ok: false, reason: 'signed_out' };
    }
    if (login.kind === 'agy') {
      const result = await checkWorkflowAgents({ cwd, env, requested: 'agy' }, { run: (_file, args, opts) => exec(args, opts) });
      return result.ok ? { ok: true } : { ok: false, reason: 'signed_out' };
    }
    if (login.kind === 'gemini') {
      const info = await exec(['--version']);
      if (info?.code !== 0) return { ok: false, reason: 'missing' };
      if (['GEMINI_API_KEY', 'GOOGLE_API_KEY', 'GOOGLE_GENAI_USE_VERTEXAI', 'GOOGLE_GENAI_USE_GCA'].some(k => env[k])) return { ok: true };
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

export async function selectPoolLogin({ cwd = process.cwd(), env = process.env, poolPath, pool: preloadedPool, fallbackAgent, stateRoot, allowLimited = false } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = (ports.now ?? Date.now)();
  const pool = preloadedPool ?? loadLoginPool({ cwd, env, poolPath, fallbackAgent }, { fs });
  const active = pool.logins.filter(login => !login.paused);
  const cooldowns = stateRoot ? readPoolCooldowns({ stateRoot, now }, { fs }) : {};
  const cooling = [];
  const unavailable = [];
  let fallbackLimited = null;

  for (const login of active) {
    const cd = cooldowns[login.id];
    if (cd && cd.until > now) {
      cooling.push({ id: login.id, until: cd.until, resetAt: cd.resetAt ?? cd.until, reason: cd.reason });
      if (!allowLimited) continue;
    }
    const childEnv = loginEnvironment(env, login);
    const probe = ports.probeLogin
      ? await ports.probeLogin(login, childEnv)
      : await defaultProbeLogin(login, { cwd, env: childEnv, fs, run: ports.run });
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
      if (limits.state === 'unknown' && (login.plan === 'pro' || login.credits === true)) {
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
      poolSize: active.length,
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
      poolSize: active.length,
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
    poolSize: active.length,
    resetAt: resetTimes.length ? Math.min(...resetTimes) : null,
    cooling,
    unavailable,
  };
}
