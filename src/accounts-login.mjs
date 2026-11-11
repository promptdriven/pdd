// Generated from prompts/cli/accounts-login.prompt.md (sha256: d0bfb8324b954567820215c54378e470839ab1ed84a8685917eadf18604c9c68).
import * as realFs from 'node:fs/promises';
import { constants } from 'node:fs';
import { tmpdir as osTmpdir } from 'node:os';
import { isAbsolute, join } from 'node:path';
import { createHash } from 'node:crypto';

const MAX_LOGIN_BYTES = 64 * 1024;
// Non-blocking, so a named pipe in place of the file cannot hang the read.
const READ_NO_BLOCK = constants.O_RDONLY | constants.O_NONBLOCK;
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const facts = (state, accessExpiresAt = null, accountKey = null) => ({ state, accessExpiresAt, accountKey });

function checkHome(home) {
  if (typeof home !== 'string' || home === '' || !isAbsolute(home)) throw new TypeError('A login folder must be an absolute path.');
}

function accessEnd(token) {
  try {
    const claims = JSON.parse(Buffer.from(token.split('.')[1] ?? '', 'base64url').toString('utf8'));
    if (!object(claims) || typeof claims.exp !== 'number' || !Number.isFinite(claims.exp) || claims.exp < 0) return null;
    const ms = claims.exp * 1000;
    return ms <= 8.64e15 ? ms : null;
  } catch { return null; }
}

// Reads the login file once. Returns the facts and, for a usable login, the parsed
// document. The document stays inside this module.
async function readLogin(home, fs) {
  let handle;
  try { handle = await fs.open(join(home, 'auth.json'), READ_NO_BLOCK); } catch (error) {
    return { facts: facts(error?.code === 'ENOENT' || error?.code === 'ENOTDIR' ? 'none' : 'unreadable') };
  }
  let text;
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
    text = buffer.subarray(0, size).toString('utf8');
  } catch { return { facts: facts('unreadable') }; } finally {
    await handle.close().catch(() => {});
  }
  let doc;
  try { doc = JSON.parse(text); } catch { return { facts: facts('unreadable') }; }
  if (!object(doc)) return { facts: facts('unreadable') };
  const tokens = doc.tokens;
  if (tokens == null) return { facts: facts('none') };
  if (!object(tokens) || typeof tokens.access_token !== 'string' || tokens.access_token === ''
    || typeof tokens.refresh_token !== 'string') return { facts: facts('unreadable') };
  const accountKey = typeof tokens.account_id === 'string' && tokens.account_id !== ''
    ? createHash('sha256').update(tokens.account_id, 'utf8').digest('hex').slice(0, 16) : null;
  return { facts: facts(tokens.refresh_token === '' ? 'access' : 'full', accessEnd(tokens.access_token), accountKey), doc };
}

export async function codexLoginFacts(home, ports = {}) {
  checkHome(home);
  return (await readLogin(home, { ...realFs, ...ports.fs })).facts;
}

function accessOnly(doc) {
  const text = value => typeof value === 'string';
  const tokens = { ...(text(doc.tokens.id_token) ? { id_token: doc.tokens.id_token } : {}),
    access_token: doc.tokens.access_token, refresh_token: '',
    ...(text(doc.tokens.account_id) ? { account_id: doc.tokens.account_id } : {}) };
  // A fresh last_refresh keeps any age rule in Codex from starting a renewal.
  return { ...(text(doc.auth_mode) ? { auth_mode: doc.auth_mode } : {}), tokens, last_refresh: new Date().toISOString() };
}

const codedError = (code, message, extra = {}) => Object.assign(new Error(message), { code, ...extra });

export async function withAccessOnlyHome(home, fn, ports = {}) {
  checkHome(home);
  const fs = { ...realFs, ...ports.fs };
  const login = await readLogin(home, fs);
  if (!login.doc) throw codedError('PDD_NO_LOGIN', 'No readable Codex login in this folder.', { state: login.facts.state });
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
