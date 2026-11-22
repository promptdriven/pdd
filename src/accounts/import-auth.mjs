// Generated from prompts/cli/accounts-cli.prompt.md.
// Local Codex/Claude credential reading, provider detection, symlink guards, and refresh_token scrubbing.
import { randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { dirname, join, resolve, sep } from 'node:path';
import { knownSecretValues, rememberSecrets } from '../secret-redaction.mjs';
import { CloudAccountsError } from './cloud-error.mjs';
import { localClaudePaths, localCodexAuthPath, localCodexHome, pddManagedCodexHome } from './cloud-state.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);

export async function readStdinString(stdin, { idleTimeoutMs = 50 } = {}) {
  if (typeof stdin === 'string') return stdin;
  if (!stdin || stdin.isTTY || typeof stdin.on !== 'function' || stdin.readableEnded) return '';
  return new Promise(resolveRead => {
    const chunks = [];
    let gotData = false, timer = null;
    const finish = () => {
      if (timer) clearTimeout(timer);
      stdin.off?.('data', onData); stdin.off?.('end', onEnd); stdin.off?.('error', onEnd);
      if (stdin === process.stdin && !gotData) stdin.pause?.();
      resolveRead(Buffer.concat(chunks).toString('utf8'));
    };
    const onData = chunk => { gotData = true; if (timer) { clearTimeout(timer); timer = null; } chunks.push(Buffer.from(chunk)); };
    const onEnd = () => finish();
    if (stdin === process.stdin && idleTimeoutMs > 0) { timer = setTimeout(finish, idleTimeoutMs); timer.unref?.(); }
    stdin.on('data', onData); stdin.on('end', onEnd); stdin.on('error', onEnd); stdin.resume?.();
  });
}

export function stripAnsiText(raw) {
  return String(raw ?? '')
    .replace(/\x1b\][^\x07\x1b]*(?:\x07|\x1b\\)/g, '')
    .replace(/\x1b\[[0-?]*[ -/]*[@-~]/g, '')
    .replace(/\x1b[@-Z\\-_]/g, '')
    .replace(/\r\n/g, '\n')
    .replace(/\r/g, '\n');
}

function unwrapClaudeTokenLines(cleanText) {
  const lines = cleanText.split('\n'), out = [];
  for (let i = 0; i < lines.length; i += 1) {
    let cur = lines[i];
    const tokenTail = /(sk-ant-oat[A-Za-z0-9_-]{8,})\s*$/.exec(cur);
    if (tokenTail && (cur.trimEnd().length >= 50 || tokenTail[1].length >= 45)) {
      cur = cur.trimEnd();
      let tokLen = tokenTail[1].length;
      while (i + 1 < lines.length) {
        const contMatch = /^\s*([A-Za-z0-9_-]+)\s*$/.exec(lines[i + 1]);
        if (!contMatch) break;
        const frag = contMatch[1];
        if (tokLen >= 95 && !/[0-9_-]/.test(frag)) break;
        cur += frag; tokLen += frag.length; i += 1;
      }
    }
    out.push(cur);
  }
  return out.join('\n');
}

export function extractClaudeToken(text) {
  const match = /\b(sk-ant-oat[A-Za-z0-9_-]{8,})\b/.exec(unwrapClaudeTokenLines(stripAnsiText(text)));
  return match ? match[1] : '';
}

function rememberCodexPayloadSecrets(raw) {
  if (!object(raw)) return;
  rememberSecrets(...knownSecretValues(raw));
  if (object(raw.tokens)) {
    for (const val of Object.values(raw.tokens)) if (typeof val === 'string' && val.length >= 8) rememberSecrets(val);
  }
}

function rememberClaudePayloadSecrets(parsed) {
  if (!object(parsed)) return;
  rememberSecrets(...knownSecretValues(parsed));
  if (object(parsed.env)) rememberSecrets(...knownSecretValues(parsed.env));
  for (const key of ['oauth_token', 'claude_oauth_token']) {
    if (typeof parsed[key] === 'string' && parsed[key].trim()) rememberSecrets(parsed[key], parsed[key].trim());
  }
  if (object(parsed.claudeAiOauth)) {
    rememberSecrets(...knownSecretValues(parsed.claudeAiOauth));
    for (const [key, val] of Object.entries(parsed.claudeAiOauth)) {
      if (typeof val === 'string' && val.trim() && (/token|secret|key|credential/i.test(key) || val.trim().startsWith('sk-'))) {
        rememberSecrets(val, val.trim());
      }
    }
  }
}

function parseClaudeExpiresAtMs(expiresAt) {
  if (typeof expiresAt === 'number') return expiresAt;
  if (typeof expiresAt === 'string') {
    const trimmed = expiresAt.trim();
    if (!trimmed) return null;
    return /^-?\d+(?:\.\d+)?$/.test(trimmed) ? Number(trimmed) : Date.parse(trimmed);
  }
  return NaN;
}

export function parseClaudeTokenText(rawText, target, nowMs, { allowBareToken = true } = {}) {
  let parsed = null, isJson = false;
  try { parsed = JSON.parse(rawText); isJson = true; } catch {}
  if (isJson) {
    rememberClaudePayloadSecrets(parsed);
    if (object(parsed)) {
      const candidate = parsed?.env?.CLAUDE_CODE_OAUTH_TOKEN ?? parsed?.oauth_token ?? parsed?.claude_oauth_token ?? '';
      if (typeof candidate === 'string' && candidate.trim() && !/\s/.test(candidate.trim())) {
        const clean = candidate.trim(); rememberSecrets(clean); return clean;
      }
      if (object(parsed.claudeAiOauth)) {
        const oauth = parsed.claudeAiOauth, rawExpiresAt = oauth.expiresAt;
        if (rawExpiresAt !== undefined && rawExpiresAt !== null && !(typeof rawExpiresAt === 'string' && !rawExpiresAt.trim())) {
          const expMs = parseClaudeExpiresAtMs(rawExpiresAt);
          if (!Number.isFinite(expMs) || expMs <= nowMs + 60_000) {
            throw new CloudAccountsError(`${target} contains an expired short-lived Claude OAuth access token. Run pdd accounts add --provider claude or claude setup-token.`, { code: 'expired_local_login' });
          }
        }
        const accessToken = typeof oauth.accessToken === 'string' ? oauth.accessToken.trim() : '';
        if (accessToken && !/\s/.test(accessToken)) { rememberSecrets(accessToken); return accessToken; }
        return '';
      }
      const extracted = extractClaudeToken(rawText);
      if (extracted) { rememberSecrets(extracted); return extracted; }
      return '';
    }
    if (typeof parsed === 'string') {
      const strCandidate = extractClaudeToken(parsed) || (allowBareToken ? parsed.trim() : '');
      if (strCandidate && !/\s/.test(strCandidate)) { rememberSecrets(strCandidate); return strCandidate; }
    }
    return '';
  }
  const extracted = extractClaudeToken(rawText) || (allowBareToken ? rawText.trim() : '');
  if (extracted && !/\s/.test(extracted)) { rememberSecrets(extracted); return extracted; }
  return '';
}

function hasClaudeJsonCredentials(raw) {
  if (!object(raw)) return false;
  if (typeof raw?.env?.CLAUDE_CODE_OAUTH_TOKEN === 'string' && raw.env.CLAUDE_CODE_OAUTH_TOKEN.trim()) return true;
  if (typeof raw?.oauth_token === 'string' && raw.oauth_token.trim()) return true;
  if (typeof raw?.claude_oauth_token === 'string' && raw.claude_oauth_token.trim()) return true;
  if (object(raw?.claudeAiOauth)) {
    const o = raw.claudeAiOauth;
    return Boolean((typeof o.accessToken === 'string' && o.accessToken.trim()) || o.expiresAt !== undefined || (typeof o.refreshToken === 'string' && o.refreshToken.trim()));
  }
  return false;
}

export function readCodexFullAuthBundle(fs, env, explicitAuthPath = null) {
  const authPath = explicitAuthPath || localCodexAuthPath(env);
  let raw;
  try { raw = JSON.parse(fs.readFileSync(authPath, 'utf8')); }
  catch { throw new CloudAccountsError(`No Codex login found at ${authPath}. Run codex login first.`, { code: 'missing_local_login' }); }
  rememberCodexPayloadSecrets(raw);
  const tokens = raw?.tokens;
  if (!object(tokens)) throw new CloudAccountsError('Local Codex auth.json is missing OAuth tokens (access_token, refresh_token, id_token, account_id). Run codex login first.', { code: 'invalid_local_login' });
  const hasAccess = typeof tokens.access_token === 'string' && Boolean(tokens.access_token.trim());
  const hasRefresh = typeof tokens.refresh_token === 'string' && Boolean(tokens.refresh_token.trim());
  if (hasAccess && !hasRefresh) throw new CloudAccountsError('Local Codex auth.json already has a stripped refresh token. Run pdd accounts add --provider codex to sign in fresh.', { code: 'already_stripped' });
  const missing = ['access_token', 'refresh_token', 'id_token', 'account_id'].filter(k => typeof tokens[k] !== 'string' || !tokens[k].trim());
  if (missing.length > 0) throw new CloudAccountsError(`Local Codex auth.json is missing required OAuth token field${missing.length > 1 ? 's' : ''}: ${missing.join(', ')}. Run codex login first.`, { code: 'invalid_local_login' });
  return {
    authPath,
    authJson: raw,
    bundle: {
      auth_json: {
        OPENAI_API_KEY: raw.OPENAI_API_KEY ?? null,
        tokens: {
          access_token: tokens.access_token.trim(),
          refresh_token: tokens.refresh_token.trim(),
          id_token: tokens.id_token.trim(),
          account_id: tokens.account_id.trim(),
        },
      },
    },
  };
}

export function readLocalClaudeToken(fs, env, extraText = '', options = {}) {
  const nowMs = (typeof options?.now === 'function' ? options.now : Date.now)();
  if (typeof extraText === 'string' && extraText.trim()) {
    const fromExtra = parseClaudeTokenText(extraText, 'stdin', nowMs, { allowBareToken: false });
    if (fromExtra) return fromExtra;
  }
  const envTok = typeof env?.CLAUDE_CODE_OAUTH_TOKEN === 'string' ? env.CLAUDE_CODE_OAUTH_TOKEN.trim() : '';
  if (envTok) { rememberSecrets(envTok); return envTok; }
  const { settingsPath } = localClaudePaths(env);
  for (const candidatePath of [settingsPath, join(dirname(settingsPath), '.credentials.json')]) {
    try {
      const tok = parseClaudeTokenText(fs.readFileSync(candidatePath, 'utf8'), candidatePath, nowMs, { allowBareToken: false });
      if (tok) return tok;
    } catch (err) {
      if (err instanceof CloudAccountsError) throw err;
    }
  }
  throw new CloudAccountsError('No Claude OAuth token found. Run pdd accounts add --provider claude or claude setup-token, or pass CLAUDE_CODE_OAUTH_TOKEN.', { code: 'missing_local_login' });
}

export function readClaudeTokenFromPath(fs, fromPath, options = {}) {
  const nowMs = (typeof options?.now === 'function' ? options.now : Date.now)();
  let isDir = false;
  try { isDir = Boolean(fs.statSync(fromPath)?.isDirectory()); } catch {}
  if (isDir) {
    const settingsPath = join(fromPath, 'settings.json'), credentialsPath = join(fromPath, '.credentials.json');
    let foundAny = false, lastPath = settingsPath;
    for (const p of [settingsPath, credentialsPath]) {
      try {
        const raw = fs.readFileSync(p, 'utf8');
        foundAny = true; lastPath = p;
        const tok = parseClaudeTokenText(raw, p, nowMs, { allowBareToken: false });
        if (tok) return tok;
      } catch (err) { if (err instanceof CloudAccountsError) throw err; }
    }
    if (!foundAny) throw new CloudAccountsError(`No Claude token file found at ${settingsPath} or ${credentialsPath}.`, { code: 'missing_local_login' });
    throw new CloudAccountsError(`No valid Claude OAuth token found in ${lastPath}.`, { code: 'invalid_local_login' });
  }
  let rawText = '';
  try { rawText = fs.readFileSync(fromPath, 'utf8'); } catch { throw new CloudAccountsError(`No Claude token file found at ${fromPath}.`, { code: 'missing_local_login' }); }
  const token = parseClaudeTokenText(rawText, fromPath, nowMs, { allowBareToken: true });
  if (token) return token;
  throw new CloudAccountsError(`No valid Claude OAuth token found in ${fromPath}.`, { code: 'invalid_local_login' });
}

const isPathInsideRoot = (candidate, root) => {
  const normC = resolve(candidate), normR = resolve(root);
  return normC === normR || normC.startsWith(normR + sep) || normC.startsWith(`${normR}/`);
};

function resolveAllowedImportAuthFile(fs, authPath, env = process.env, { action = 'import' } = {}) {
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  const statFn = fs.statSync ?? nativeFs.statSync;
  const realFn = fs.realpathSync?.native ?? fs.realpathSync ?? nativeFs.realpathSync?.native ?? nativeFs.realpathSync;
  const managedHome = pddManagedCodexHome(env);
  const refuse = () => { throw new CloudAccountsError(`Refusing to ${action} symlinked Codex credential file: ${authPath}`, { code: 'symlink_refused' }); };
  if (typeof realFn !== 'function' || typeof statFn !== 'function') refuse();
  let realTarget;
  try {
    realTarget = String(realFn.call(fs, authPath));
    if (!statFn.call(fs, realTarget)?.isFile()) refuse();
    const dirSt = lstat(dirname(realTarget));
    if (!dirSt || dirSt.isSymbolicLink() || !dirSt.isDirectory()) refuse();
  } catch (err) {
    if (err instanceof CloudAccountsError) throw err;
    refuse();
  }
  if (isPathInsideRoot(realTarget, managedHome)) refuse();
  try { if (isPathInsideRoot(realTarget, String(realFn.call(fs, managedHome)))) refuse(); }
  catch (err) { if (err instanceof CloudAccountsError) throw err; }
  return realTarget;
}

export function resolveCodexImportSource(fs, cwd, env, fromOption) {
  const defaultAuth = localCodexAuthPath(env);
  if (!fromOption) return { authPath: defaultAuth, probeCodexHome: localCodexHome(env), isDefaultLocal: true };
  const resolved = resolve(cwd, String(fromOption).trim());
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  let rawSt = null;
  try { rawSt = lstat(resolved); } catch {}
  if (rawSt?.isSymbolicLink()) throw new CloudAccountsError(`Refusing to import symlinked Codex credential path: ${resolved}`, { code: 'symlink_refused' });
  const isDir = Boolean(rawSt?.isDirectory());
  const authPath = isDir ? join(resolved, 'auth.json') : resolved;
  return { authPath, probeCodexHome: isDir ? resolved : null, isDefaultLocal: resolve(authPath) === resolve(defaultAuth) };
}

export function assertNonSymlinkImportFile(fs, authPath, env = process.env) {
  if (!authPath) return authPath;
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  const parentDir = dirname(authPath);
  let parentSt = null;
  try { parentSt = lstat(parentDir); } catch {}
  if (parentSt?.isSymbolicLink()) throw new CloudAccountsError(`Refusing to import Codex credential file from symlinked directory: ${parentDir}`, { code: 'symlink_refused' });
  let st = null;
  try { st = lstat(authPath); } catch { return authPath; }
  return st?.isSymbolicLink() ? resolveAllowedImportAuthFile(fs, authPath, env, { action: 'import' }) : authPath;
}

export function scrubImportedCodexSourceRefreshToken(fs, authPath, env = process.env) {
  if (!authPath) return false;
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  const dir = dirname(authPath);
  let dirSt = null;
  try { dirSt = lstat(dir); } catch { return false; }
  if (!dirSt || dirSt.isSymbolicLink() || !dirSt.isDirectory()) {
    if (dirSt?.isSymbolicLink()) throw new CloudAccountsError(`Refusing to rewrite Codex credential file in symlinked directory: ${dir}`, { code: 'symlink_refused' });
    return false;
  }
  let st = null;
  try { st = lstat(authPath); } catch { return false; }
  if (!st) return false;
  let targetFilePath = authPath;
  if (st.isSymbolicLink()) targetFilePath = resolveAllowedImportAuthFile(fs, authPath, env, { action: 'rewrite' });
  else if (!st.isFile()) return false;
  let parsed = null;
  try { parsed = JSON.parse(fs.readFileSync(targetFilePath, 'utf8')); } catch { return false; }
  if (!object(parsed) || !object(parsed.tokens) || typeof parsed.tokens.refresh_token !== 'string' || parsed.tokens.refresh_token === '') return false;
  rememberCodexPayloadSecrets(parsed);
  const scrubbed = { ...parsed, tokens: { ...parsed.tokens, refresh_token: '' } };
  const tmpPath = join(dirname(targetFilePath), `.pdd-scrub-${process.pid}-${randomBytes(6).toString('hex')}.tmp`);
  try {
    fs.writeFileSync(tmpPath, `${JSON.stringify(scrubbed, null, 2)}\n`, { mode: 0o600 });
    try { (fs.chmodSync ?? nativeFs.chmodSync)(tmpPath, 0o600); } catch {}
    fs.renameSync(tmpPath, targetFilePath);
    return true;
  } catch (err) {
    try { (fs.rmSync ?? nativeFs.rmSync)(tmpPath, { force: true }); } catch {}
    throw err;
  }
}

export function detectImportProvider(fs, env = process.env, options = {}) {
  const cwd = options?.cwd ?? process.cwd();
  const fromOption = options?.fromOption ?? options?.from ?? null;
  const now = typeof options?.now === 'function' ? options.now : Date.now;
  if (fromOption) {
    const resolved = resolve(cwd, String(fromOption).trim());
    const lstat = fs.lstatSync ?? nativeFs.lstatSync;
    const parentDir = dirname(resolved);
    let parentSt = null;
    try { parentSt = lstat.call(fs, parentDir); } catch {}
    if (parentSt?.isSymbolicLink?.() && parentSt.uid !== 0) {
      throw new CloudAccountsError(`Refusing to import credential file from symlinked directory: ${parentDir}. Pass a real non-symlinked credential directory or file to --from, then rerun.`, { code: 'symlink_refused' });
    }
    let rawSt = null;
    try { rawSt = lstat.call(fs, resolved); } catch {}
    if (rawSt?.isSymbolicLink?.()) {
      throw new CloudAccountsError(`Refusing to import symlinked credential path: ${resolved}. Pass the real credential file or directory path to --from (not a symlink), then rerun.`, { code: 'symlink_refused' });
    }
    const isRegularNonSymlink = p => {
      let st;
      try { st = lstat.call(fs, p); } catch { return false; }
      if (st?.isSymbolicLink?.()) throw new CloudAccountsError(`Refusing to import symlinked credential file: ${p}. Pass a real non-symlinked credential file to --from, then rerun.`, { code: 'symlink_refused' });
      return Boolean(st?.isFile?.());
    };
    if (rawSt?.isDirectory?.()) {
      const authCandidate = join(resolved, 'auth.json');
      if (isRegularNonSymlink(authCandidate)) {
        try { const raw = JSON.parse(fs.readFileSync(authCandidate, 'utf8')); rememberCodexPayloadSecrets(raw); if (object(raw?.tokens)) return 'codex'; } catch {}
      }
      for (const fileName of ['settings.json', '.credentials.json']) {
        const candidate = join(resolved, fileName);
        if (!isRegularNonSymlink(candidate)) continue;
        try {
          const txt = fs.readFileSync(candidate, 'utf8');
          try { const raw = JSON.parse(txt); rememberClaudePayloadSecrets(raw); if (hasClaudeJsonCredentials(raw)) return 'claude'; } catch {}
          const extracted = extractClaudeToken(txt);
          if (extracted) { rememberSecrets(extracted); return 'claude'; }
        } catch {}
      }
      return 'codex';
    }
    if (!rawSt?.isFile?.()) return 'codex';
    try {
      const txt = fs.readFileSync(resolved, 'utf8');
      try {
        const raw = JSON.parse(txt);
        rememberCodexPayloadSecrets(raw); rememberClaudePayloadSecrets(raw);
        if (object(raw?.tokens)) return 'codex';
        if (hasClaudeJsonCredentials(raw)) return 'claude';
      } catch {}
      const extracted = extractClaudeToken(txt);
      if (extracted) { rememberSecrets(extracted); return 'claude'; }
    } catch {}
    return 'codex';
  }
  try {
    const raw = JSON.parse(fs.readFileSync(localCodexAuthPath(env), 'utf8'));
    rememberCodexPayloadSecrets(raw);
    const t = raw?.tokens;
    if (['access_token', 'refresh_token', 'id_token', 'account_id'].every(k => typeof t?.[k] === 'string' && t[k].trim())) return 'codex';
  } catch {}
  try { if (readLocalClaudeToken(fs, env, '', { now })) return 'claude'; }
  catch (err) { if (err?.code === 'expired_local_login') return 'claude'; }
  return 'codex';
}
