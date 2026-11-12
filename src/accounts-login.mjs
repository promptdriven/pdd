// Generated from prompts/cli/accounts-login.prompt.md (sha256: 05a24f0a5756be9619c9582d443cf2fe2ef9676b6f796f5dd949035ff7536fb0).
import * as realFs from 'node:fs/promises';
import { constants } from 'node:fs';
import { tmpdir as osTmpdir } from 'node:os';
import { isAbsolute, join } from 'node:path';
import { createHash, randomBytes } from 'node:crypto';

const MAX_LOGIN_BYTES = 64 * 1024;
// Non-blocking, so a named pipe in place of the file cannot hang the read.
const READ_NO_BLOCK = constants.O_RDONLY | constants.O_NONBLOCK;
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const facts = (state, accessExpiresAt = null, accountKey = null) => ({ state, accessExpiresAt, accountKey });

function checkHome(home) {
  if (typeof home !== 'string' || home === '' || !isAbsolute(home)) throw new TypeError('A login folder must be an absolute path.');
}

function claimsOf(token) {
  if (typeof token !== 'string') return null;
  try {
    const claims = JSON.parse(Buffer.from(token.split('.')[1] ?? '', 'base64url').toString('utf8'));
    return object(claims) ? claims : null;
  } catch { return null; }
}

function accessEnd(token) {
  const claims = claimsOf(token);
  if (!claims || typeof claims.exp !== 'number' || !Number.isFinite(claims.exp) || claims.exp < 0) return null;
  const ms = claims.exp * 1000;
  return ms <= 8.64e15 ? ms : null;
}

const sha256 = data => createHash('sha256').update(data).digest('hex');
const text = value => typeof value === 'string' && value.trim() !== '' ? value.trim() : null;

// Team workspace members share account_id; the user id (the login server's claim
// order) tells their logins apart.
function accountKeyOf(tokens) {
  const account = text(tokens.account_id);
  if (!account) return null;
  const claims = claimsOf(tokens.id_token) ?? {};
  const auth = object(claims['https://api.openai.com/auth']) ? claims['https://api.openai.com/auth'] : {};
  const user = text(auth.chatgpt_user_id) ?? text(auth.user_id) ?? text(claims.sub);
  return sha256(Buffer.from(user ? `${account}\n${user}` : account, 'utf8')).slice(0, 16);
}

// Reads the login file once. Returns the facts and, for a usable login, the parsed
// document. The document stays inside this module.
async function readLogin(home, fs) {
  let handle;
  try { handle = await fs.open(join(home, 'auth.json'), READ_NO_BLOCK); } catch (error) {
    return { facts: facts(error?.code === 'ENOENT' || error?.code === 'ENOTDIR' ? 'none' : 'unreadable') };
  }
  let bytes;
  try {
    if (!(await handle.stat()).isFile()) return { facts: facts('unreadable') };
    const buffer = Buffer.alloc(MAX_LOGIN_BYTES + 1);
    let size = 0;
    while (size < buffer.length) {
      const { bytesRead } = await handle.read(buffer, size, buffer.length - size, size);
      if (bytesRead === 0) break;
      size += bytesRead;
    }
    if (size > MAX_LOGIN_BYTES) return { facts: facts('unreadable') };
    bytes = buffer.subarray(0, size);
  } catch { return { facts: facts('unreadable') }; } finally {
    await handle.close().catch(() => {});
  }
  let doc;
  try { doc = JSON.parse(bytes.toString('utf8')); } catch { return { facts: facts('unreadable') }; }
  if (!object(doc)) return { facts: facts('unreadable') };
  const tokens = doc.tokens;
  if (tokens == null) return { facts: facts('none') };
  if (!object(tokens) || typeof tokens.access_token !== 'string' || tokens.access_token === ''
    || typeof tokens.refresh_token !== 'string') return { facts: facts('unreadable') };
  return { facts: facts(tokens.refresh_token === '' ? 'access' : 'full', accessEnd(tokens.access_token), accountKeyOf(tokens)), doc, bytes };
}

export async function codexLoginFacts(home, ports = {}) {
  checkHome(home);
  return (await readLogin(home, { ...realFs, ...ports.fs })).facts;
}

function accessOnly(doc) {
  const string = value => typeof value === 'string';
  const tokens = { ...(string(doc.tokens.id_token) ? { id_token: doc.tokens.id_token } : {}),
    access_token: doc.tokens.access_token, refresh_token: '',
    ...(string(doc.tokens.account_id) ? { account_id: doc.tokens.account_id } : {}) };
  // A fresh last_refresh keeps any age rule in Codex from starting a renewal.
  return { ...(string(doc.auth_mode) ? { auth_mode: doc.auth_mode } : {}), tokens, last_refresh: new Date().toISOString() };
}

const codedError = (code, message, extra = {}) => Object.assign(new Error(message), { code, ...extra });
const noLogin = state => codedError('PDD_NO_LOGIN', 'No readable Codex login in this folder.', { state });

export async function withAccessOnlyHome(home, fn, ports = {}) {
  checkHome(home);
  const fs = { ...realFs, ...ports.fs };
  const login = await readLogin(home, fs);
  if (!login.doc) throw noLogin(login.facts.state);
  let tempHome;
  try { tempHome = await fs.mkdtemp(join(ports.tmpdir ?? osTmpdir(), 'pdd-codex-read-')); } catch {
    throw codedError('PDD_TEMP_HOME_FAILED', 'Could not make the temporary login folder.');
  }
  let outcome;
  try {
    try {
      await fs.chmod(tempHome, 0o700);
      await fs.writeFile(join(tempHome, 'auth.json'), JSON.stringify(accessOnly(login.doc), null, 2) + '\n', { mode: 0o600, flag: 'wx' });
      await fs.writeFile(join(tempHome, 'config.toml'), 'cli_auth_credentials_store = "file"\n', { mode: 0o600, flag: 'wx' });
    } catch {
      outcome = { error: codedError('PDD_TEMP_HOME_FAILED', 'Could not make the temporary login folder.') };
    }
    if (!outcome) {
      try { outcome = { value: await fn(tempHome, login.facts) }; } catch (error) { outcome = { error }; }
    }
  } finally {
    try { await fs.rm(tempHome, { recursive: true, force: true }); } catch {
      outcome = { error: codedError('PDD_TEMP_HOME_LEFT', `Could not remove the temporary login folder ${tempHome}.`, { path: tempHome }) };
    }
  }
  if ('error' in outcome) throw outcome.error;
  return outcome.value;
}

// The only function that returns a login's text: the upload body, never logged.
export async function readLoginForUpload(home, ports = {}) {
  checkHome(home);
  const login = await readLogin(home, { ...realFs, ...ports.fs });
  if (!login.doc) throw noLogin(login.facts.state);
  return { text: login.bytes.toString('utf8'), sha256: sha256(login.bytes), facts: login.facts };
}

export async function makeAccessOnly(home, expectedSha256, ports = {}) {
  checkHome(home);
  if (typeof expectedSha256 !== 'string' || !/^[0-9a-f]{64}$/.test(expectedSha256))
    throw new TypeError('expectedSha256 must be a SHA-256 hex digest.');
  const fs = { ...realFs, ...ports.fs };
  const file = join(home, 'auth.json');
  const link = await fs.lstat(file).then(stat => stat.isSymbolicLink(), () => false);
  if (link) return { changed: false, reason: 'link' };
  const login = await readLogin(home, fs);
  if (!login.doc) return { changed: false, reason: 'no-login' };
  if (sha256(login.bytes) !== expectedSha256) return { changed: false, reason: 'bytes-changed' };
  if (login.doc.tokens.refresh_token === '') return { changed: false, reason: 'already-access' };
  const next = { ...login.doc, tokens: { ...login.doc.tokens, refresh_token: '' } };
  const temp = join(home, `.auth.json.pdd-${randomBytes(8).toString('hex')}.tmp`);
  let made = false;
  try {
    const handle = await fs.open(temp, 'wx', 0o600);
    made = true;
    try {
      await handle.writeFile(JSON.stringify(next, null, 2) + '\n');
      await handle.sync();
    } finally { await handle.close(); }
    // A renewal by Codex after the first read must win: check the bytes again.
    const again = await readLogin(home, fs);
    if (!again.bytes || sha256(again.bytes) !== expectedSha256) {
      await fs.rm(temp, { force: true });
      return { changed: false, reason: 'bytes-changed' };
    }
    await fs.rename(temp, file);
    return { changed: true, reason: 'rewritten' };
  } catch {
    if (made) await fs.rm(temp, { force: true }).catch(() => {});
    throw codedError('PDD_ACCESS_ONLY_FAILED', 'Could not make the login file access-only.');
  }
}
