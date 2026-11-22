// Generated from prompts/cli/accounts-cli.prompt.md.
// Legacy PTY Codex rollout session pinning and structured JSONL quota inspection (PDD_LEGACY_PTY_ROTATE=1).
import * as nativeFs from 'node:fs';
import { join, resolve } from 'node:path';
import { classifyRateLimitFailure } from '../login-pool.mjs';
import { fetchAccountsList } from './share-helpers.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);

const CODEX_VALUE_OPTIONS = new Set([
  '-c', '--config', '--enable', '--disable', '--remote', '--remote-auth-token-env',
  '-i', '--image', '-m', '--model', '--local-provider', '-p', '--profile',
  '-s', '--sandbox', '-C', '--cd', '--add-dir', '-a', '--ask-for-approval',
  '--color', '-o', '--output-last-message',
]);
const CODEX_PRESERVED_VALUE_OPTIONS = new Set([
  '-c', '--config', '--enable', '--disable', '--remote', '--remote-auth-token-env',
  '-i', '--image', '-m', '--model', '--local-provider', '-p', '--profile',
  '-s', '--sandbox', '-C', '--cd', '--add-dir', '-a', '--ask-for-approval',
]);
const CODEX_PRESERVED_FLAG_OPTIONS = new Set([
  '--oss', '--strict-config', '--approve-for-me',
  '--dangerously-bypass-approvals-and-sandbox', '--yolo', '--dangerously-bypass-hook-trust',
  '--worktree', '--search', '--no-alt-screen', '--no-daemon', '--include-non-interactive',
]);
const CODEX_NON_INTERACTIVE_SUBCOMMANDS = new Set([
  'agents', 'exec', 'e', 'review', 'login', 'logout', 'mcp', 'mcp-server',
  'plugin', 'app-server', 'remote-control', 'app', 'completion', 'update',
  'doctor', 'sandbox', 'debug', 'apply', 'a', 'queue', 'archive', 'delete',
  'migrate-rollouts', 'migrate-nfs-db', 'unarchive', 'cloud', 'exec-server',
  'features', 'help',
]);
const CODEX_INTERACTIVE_SUBCOMMANDS = new Set(['resume', 'fork']);
export const UUID_TOKEN_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
export const OUTPUT_SESSION_ID_RE = /(?:session[_\s-]*id|thread[_\s-]*id|conversation[_\s-]*id)["'\s:=]+([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})/i;
const ROLLOUT_FILE_RE = /^rollout-.*\.jsonl$/i;
const ROLLOUT_UUID_FILE_RE = /([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})\.jsonl$/i;
const QUOTA_ERROR_CODES = new Set(['usage_limit_exceeded', 'usage_limit_reached', 'insufficient_quota', 'quota_exceeded', 'out_of_credits', 'billing_hard_limit_reached']);
const MAX_ROLLOUT_HEADER_BYTES = 4 * 1024 * 1024;
const MAX_ROLLOUT_SLICE_BYTES = 2 * 1024 * 1024;

export function inspectCodexInvocation(args, baseCwd = process.cwd()) {
  let subcommand = '', hasHelpOrVersion = false, explicitSessionId = null, afterSubcommand = false, cdOverride = null;
  for (let i = 0; i < args.length; i += 1) {
    const word = String(args[i] ?? '');
    if (word === '--') break;
    if (word === '-h' || word === '--help' || word === '-V' || word === '--version') { hasHelpOrVersion = true; continue; }
    const eqIdx = word.indexOf('=');
    if (eqIdx > 0 && CODEX_VALUE_OPTIONS.has(word.slice(0, eqIdx))) {
      const flagName = word.slice(0, eqIdx);
      if (flagName === '-C' || flagName === '--cd') cdOverride = word.slice(eqIdx + 1);
      continue;
    }
    if (CODEX_VALUE_OPTIONS.has(word)) {
      if ((word === '-C' || word === '--cd') && i + 1 < args.length) cdOverride = String(args[i + 1] ?? '');
      i += 1;
      continue;
    }
    if (word.startsWith('-')) continue;
    if (!afterSubcommand) {
      if (CODEX_INTERACTIVE_SUBCOMMANDS.has(word) || CODEX_NON_INTERACTIVE_SUBCOMMANDS.has(word)) { subcommand = word; afterSubcommand = true; continue; }
      break;
    }
    if ((subcommand === 'resume' || subcommand === 'fork') && !explicitSessionId && UUID_TOKEN_RE.test(word)) { explicitSessionId = word; break; }
  }
  const effectiveCwd = cdOverride ? resolve(baseCwd || process.cwd(), cdOverride) : resolve(baseCwd || process.cwd());
  return {
    subcommand,
    isResume: subcommand === 'resume',
    isFork: subcommand === 'fork',
    interactive: !hasHelpOrVersion && (subcommand === '' || CODEX_INTERACTIVE_SUBCOMMANDS.has(subcommand)),
    explicitSessionId,
    effectiveCwd,
  };
}

export function buildCodexResumeArgs(initialArgs, sessionId) {
  const preserved = [];
  for (let i = 0; i < initialArgs.length; i += 1) {
    const word = String(initialArgs[i] ?? '');
    if (word === '--') break;
    if (CODEX_PRESERVED_VALUE_OPTIONS.has(word)) { if (i + 1 < initialArgs.length) { preserved.push(word, String(initialArgs[i + 1])); i += 1; } continue; }
    const eqIdx = word.indexOf('=');
    if (eqIdx > 0 && CODEX_PRESERVED_VALUE_OPTIONS.has(word.slice(0, eqIdx))) { preserved.push(word); continue; }
    if (eqIdx > 0 && CODEX_VALUE_OPTIONS.has(word.slice(0, eqIdx))) continue;
    if (CODEX_VALUE_OPTIONS.has(word)) { i += 1; continue; }
    if (CODEX_PRESERVED_FLAG_OPTIONS.has(word)) preserved.push(word);
  }
  return sessionId ? ['resume', ...preserved, sessionId] : ['resume', ...preserved, '--last'];
}

function canonicalPathSafe(fs, targetPath) {
  if (!targetPath) return '';
  try { return (fs.realpathSync ?? nativeFs.realpathSync)(targetPath); } catch { return resolve(targetPath); }
}

function pathsMatchCwd(fs, candidateCwd, expectedCwd) {
  if (!candidateCwd || !expectedCwd) return false;
  return resolve(candidateCwd) === resolve(expectedCwd) || canonicalPathSafe(fs, candidateCwd) === canonicalPathSafe(fs, expectedCwd);
}

export function safeFileSize(fs, filePath) {
  if (!filePath) return 0;
  try { const st = fs.statSync(filePath); return st?.isFile() ? st.size : 0; } catch { return 0; }
}

function readFirstJsonLine(fs, filePath) {
  let fd;
  try {
    if (typeof fs.openSync === 'function' && typeof fs.readSync === 'function' && typeof fs.closeSync === 'function') {
      fd = fs.openSync(filePath, 'r');
      const chunkBuf = Buffer.allocUnsafe(65_536), parts = [];
      let offset = 0, foundNewline = false;
      while (offset < MAX_ROLLOUT_HEADER_BYTES) {
        const bytesRead = fs.readSync(fd, chunkBuf, 0, Math.min(chunkBuf.length, MAX_ROLLOUT_HEADER_BYTES - offset), offset);
        if (bytesRead <= 0) break;
        const slice = chunkBuf.subarray(0, bytesRead), nlIdx = slice.indexOf(0x0a);
        if (nlIdx >= 0) { if (nlIdx > 0) parts.push(Buffer.from(slice.subarray(0, nlIdx))); foundNewline = true; break; }
        parts.push(Buffer.from(slice)); offset += bytesRead;
      }
      if (!foundNewline) return null;
      const firstLine = (parts.length === 1 ? parts[0] : (parts.length === 0 ? Buffer.alloc(0) : Buffer.concat(parts))).toString('utf8').trim();
      if (!firstLine) return null;
      const parsed = JSON.parse(firstLine);
      return object(parsed) ? parsed : null;
    }
    const raw = fs.readFileSync(filePath, 'utf8'), nl = raw.indexOf('\n');
    if (nl < 0) return null;
    const firstLine = raw.slice(0, nl);
    if (Buffer.byteLength(firstLine, 'utf8') > MAX_ROLLOUT_HEADER_BYTES || !firstLine.trim()) return null;
    const parsed = JSON.parse(firstLine.trim());
    return object(parsed) ? parsed : null;
  } catch { return null; } finally { if (fd !== undefined) { try { fs.closeSync(fd); } catch {} } }
}

function readRolloutChunkFromOffset(fs, filePath, startOffset) {
  let fd;
  try {
    if (typeof fs.openSync === 'function' && typeof fs.fstatSync === 'function' && typeof fs.readSync === 'function' && typeof fs.closeSync === 'function') {
      fd = fs.openSync(filePath, 'r');
      const size = fs.fstatSync(fd).size;
      if (size <= startOffset) return { status: 'empty', text: '', nextOffset: startOffset, eofSize: size };
      const len = Math.min(size - startOffset, MAX_ROLLOUT_SLICE_BYTES), buf = Buffer.allocUnsafe(len);
      let readTotal = 0;
      while (readTotal < len) { const n = fs.readSync(fd, buf, readTotal, len - readTotal, startOffset + readTotal); if (n <= 0) break; readTotal += n; }
      const validBuf = buf.subarray(0, readTotal), lastNl = validBuf.lastIndexOf(0x0a);
      if (lastNl >= 0) {
        const completeBuf = validBuf.subarray(0, lastNl + 1);
        return { status: 'lines', text: completeBuf.toString('utf8'), nextOffset: startOffset + completeBuf.length, eofSize: size };
      }
      if (size - startOffset <= MAX_ROLLOUT_SLICE_BYTES) return { status: 'partial', text: '', nextOffset: startOffset, eofSize: size };
      const scanBuf = Buffer.allocUnsafe(65_536);
      let pos = startOffset + readTotal;
      while (pos < size) {
        const n = fs.readSync(fd, scanBuf, 0, Math.min(scanBuf.length, size - pos), pos);
        if (n <= 0) break;
        const nl = scanBuf.subarray(0, n).indexOf(0x0a);
        if (nl >= 0) return { status: 'skipped_oversized', text: '', nextOffset: pos + nl + 1, eofSize: size };
        pos += n;
      }
      return { status: 'partial', text: '', nextOffset: startOffset, eofSize: size };
    }
    const raw = Buffer.from(fs.readFileSync(filePath, 'utf8'), 'utf8');
    if (raw.length <= startOffset) return { status: 'empty', text: '', nextOffset: startOffset, eofSize: raw.length };
    const windowBuf = raw.subarray(startOffset, Math.min(raw.length, startOffset + MAX_ROLLOUT_SLICE_BYTES)), lastNl = windowBuf.lastIndexOf(0x0a);
    if (lastNl >= 0) {
      const completeBuf = windowBuf.subarray(0, lastNl + 1);
      return { status: 'lines', text: completeBuf.toString('utf8'), nextOffset: startOffset + completeBuf.length, eofSize: raw.length };
    }
    if (raw.length - startOffset <= MAX_ROLLOUT_SLICE_BYTES) return { status: 'partial', text: '', nextOffset: startOffset, eofSize: raw.length };
    const nextNl = raw.indexOf(0x0a, startOffset + windowBuf.length);
    return nextNl >= 0 ? { status: 'skipped_oversized', text: '', nextOffset: nextNl + 1, eofSize: raw.length } : { status: 'partial', text: '', nextOffset: startOffset, eofSize: raw.length };
  } catch { return { status: 'empty', text: '', nextOffset: startOffset, eofSize: startOffset }; }
  finally { if (fd !== undefined) { try { fs.closeSync(fd); } catch {} } }
}

function collectRolloutFiles(fs, codexHomes, { minMtimeMs = null } = {}) {
  const visitedDirs = new Set(), seenFiles = new Set(), files = [];
  const walkSessions = (dir, depth) => {
    if (depth > 4) return;
    const canonDir = canonicalPathSafe(fs, dir);
    if (!canonDir || visitedDirs.has(canonDir)) return;
    visitedDirs.add(canonDir);
    let entries = [];
    try { entries = fs.readdirSync(dir, { withFileTypes: true }); } catch { return; }
    for (const ent of entries) {
      const full = join(dir, ent.name);
      if (ent.isDirectory()) walkSessions(full, depth + 1);
      else if (ent.isFile() && ROLLOUT_FILE_RE.test(ent.name)) {
        try {
          const st = fs.statSync(full);
          if (typeof minMtimeMs === 'number' && Number.isFinite(minMtimeMs) && st.mtimeMs < minMtimeMs) continue;
          const canonFile = canonicalPathSafe(fs, full);
          if (seenFiles.has(canonFile)) continue;
          seenFiles.add(canonFile);
          const uuidMatch = ROLLOUT_UUID_FILE_RE.exec(ent.name);
          files.push({ path: full, canonicalPath: canonFile, uuid: uuidMatch ? uuidMatch[1] : null, mtimeMs: st.mtimeMs });
        } catch {}
      }
    }
  };
  for (const home of [...new Set(codexHomes.filter(Boolean))]) walkSessions(join(home, 'sessions'), 0);
  return files;
}

const isSubagentSessionMeta = meta => object(meta) && (meta.thread_source === 'subagent' || Boolean(meta.parent_thread_id || (meta.source && typeof meta.source === 'object' && meta.source.subagent)));

function readSessionIndexIds(fs, codexHomes) {
  const ids = new Set(), seenIdx = new Set();
  for (const home of new Set(codexHomes.filter(Boolean))) {
    const idxPath = join(home, 'session_index.jsonl'), canonIdx = canonicalPathSafe(fs, idxPath);
    if (seenIdx.has(canonIdx)) continue;
    seenIdx.add(canonIdx);
    try {
      for (const line of fs.readFileSync(idxPath, 'utf8').split('\n')) {
        if (!line.trim()) continue;
        try { const row = JSON.parse(line); if (typeof row?.id === 'string' && UUID_TOKEN_RE.test(row.id)) ids.add(row.id); } catch {}
      }
    } catch {}
  }
  return ids;
}

export function snapshotPreSpawnCodexSessions(fs, codexHomes) {
  return { rolloutPaths: new Set(collectRolloutFiles(fs, codexHomes).map(f => f.canonicalPath)), sessionIds: readSessionIndexIds(fs, codexHomes) };
}

export function findRolloutPathBySessionId(fs, codexHomes, targetSessionId) {
  if (!targetSessionId) return null;
  const targetLower = targetSessionId.toLowerCase(), candidates = [];
  for (const item of collectRolloutFiles(fs, codexHomes)) {
    if (item.uuid && item.uuid.toLowerCase() === targetLower) { candidates.push(item); continue; }
    const header = readFirstJsonLine(fs, item.path);
    const meta = object(header?.payload) ? header.payload : header;
    if (String(meta?.id ?? meta?.session_id ?? '').toLowerCase() === targetLower) candidates.push(item);
  }
  candidates.sort((a, b) => b.mtimeMs - a.mtimeMs);
  return candidates[0]?.path ?? null;
}

export function discoverPinnedCodexRollout(fs, codexHomes, { preSpawnSnapshot, expectedCwd, turnStartedMs, explicitSessionId = null, excludedSessionId = null }) {
  if (explicitSessionId) return { sessionId: explicitSessionId, rolloutPath: findRolloutPathBySessionId(fs, codexHomes, explicitSessionId) };
  const matches = [];
  for (const item of collectRolloutFiles(fs, codexHomes, { minMtimeMs: turnStartedMs - 2000 })) {
    if (preSpawnSnapshot?.rolloutPaths?.has(item.canonicalPath)) continue;
    const header = readFirstJsonLine(fs, item.path);
    if (header?.type !== 'session_meta') continue;
    const meta = object(header.payload) ? header.payload : header;
    if (isSubagentSessionMeta(meta)) continue;
    const sid = [meta?.id, meta?.session_id, item.uuid].find(v => typeof v === 'string' && UUID_TOKEN_RE.test(v)) ?? null;
    if (!sid || preSpawnSnapshot?.sessionIds?.has(sid) || (excludedSessionId && sid.toLowerCase() === excludedSessionId.toLowerCase())) continue;
    const metaCwd = typeof meta?.cwd === 'string' && meta.cwd.trim() ? meta.cwd.trim() : null;
    if (!metaCwd || !pathsMatchCwd(fs, metaCwd, expectedCwd)) continue;
    const parsedTs = Date.parse(meta?.timestamp ?? header.timestamp ?? '');
    const sortTime = Number.isFinite(parsedTs) ? parsedTs : item.mtimeMs;
    if (sortTime < turnStartedMs - 2000) continue;
    matches.push({ sessionId: sid, rolloutPath: item.path, sortTime });
  }
  matches.sort((a, b) => a.sortTime - b.sortTime);
  return matches[0] ? { sessionId: matches[0].sessionId, rolloutPath: matches[0].rolloutPath } : null;
}

function hasStructuredHttpStatus(value, statusCode, depth = 0) {
  if (depth > 4 || !object(value)) return false;
  for (const [k, v] of Object.entries(value)) {
    if ((k === 'status' || k === 'http_status' || k === 'status_code' || k === 'http_status_code') && Number(v) === statusCode) return true;
    if (object(v) && hasStructuredHttpStatus(v, statusCode, depth + 1)) return true;
  }
  return false;
}

export function inspectRolloutQuotaError(fs, rolloutPath, fromByteOffset, turnStartedMs) {
  if (!rolloutPath) return { nextOffset: fromByteOffset, quotaError: null };
  let curOffset = fromByteOffset;
  for (let pass = 0; pass < 16; pass += 1) {
    const chunk = readRolloutChunkFromOffset(fs, rolloutPath, curOffset);
    if (chunk.status === 'empty' || chunk.status === 'partial') return { nextOffset: chunk.nextOffset, quotaError: null };
    curOffset = chunk.nextOffset;
    if (chunk.status === 'skipped_oversized') { if (curOffset >= chunk.eofSize) break; continue; }
    for (const rawLine of chunk.text.split('\n')) {
      const trimmed = rawLine.trim();
      if (!trimmed) continue;
      let row = null; try { row = JSON.parse(trimmed); } catch { continue; }
      if (!object(row)) continue;
      if (typeof row.timestamp === 'string') { const rowMs = Date.parse(row.timestamp); if (Number.isFinite(rowMs) && rowMs < turnStartedMs - 2000) continue; }
      let errObj = null, isTerminalTurnError = false;
      if (row.type === 'event_msg' && object(row.payload)) {
        if (row.payload.type === 'task_complete' && object(row.payload.error)) { errObj = row.payload.error; isTerminalTurnError = true; }
        else if (row.payload.type === 'error' || row.payload.type === 'turn_failed') { errObj = object(row.payload.error) ? row.payload.error : row.payload; isTerminalTurnError = row.payload.type === 'turn_failed'; }
      } else if (row.type === 'error' || row.type === 'turn.failed' || row.type === 'response.failed') {
        errObj = object(row.error) ? row.error : (object(row.payload?.error) ? row.payload.error : (object(row.payload) ? row.payload : row));
        isTerminalTurnError = true;
      }
      if (!object(errObj)) continue;
      const infoCode = typeof errObj.codex_error_info === 'string' ? errObj.codex_error_info.trim().toLowerCase() : '';
      const errCode = String(errObj.code ?? errObj.error_code ?? (typeof errObj.type === 'string' && errObj.type !== 'error' && errObj.type !== 'turn_failed' ? errObj.type : '')).trim().toLowerCase();
      const message = String(errObj.message ?? row.payload?.message ?? row.message ?? '').trim();
      const isHttp429 = hasStructuredHttpStatus(errObj, 429) || hasStructuredHttpStatus(row, 429);
      if (QUOTA_ERROR_CODES.has(infoCode) || QUOTA_ERROR_CODES.has(errCode)
        || ((isHttp429 || errCode === 'rate_limit_exceeded') && (!message || classifyRateLimitFailure(message) === 'quota_exhausted'))
        || (isTerminalTurnError && message && classifyRateLimitFailure(message) === 'quota_exhausted')) {
        return { nextOffset: curOffset, quotaError: { message: message || errCode || infoCode || 'usage_limit_reached' } };
      }
    }
    if (curOffset >= chunk.eofSize) break;
  }
  return { nextOffset: curOffset, quotaError: null };
}

export async function checkCloudAccountQuotaExhausted(accountId, { cwd, env }, ports = {}) {
  if (!accountId) return null;
  try {
    const acc = (await fetchAccountsList({ cwd, env, refresh: false }, ports)).accounts.find(a => a?.account_id === accountId) ?? null;
    if (object(acc) && (acc.limit_reached === true || (typeof acc.five_hour_used_percent === 'number' && acc.five_hour_used_percent >= 100) || (typeof acc.weekly_used_percent === 'number' && acc.weekly_used_percent >= 100))) return acc;
  } catch {}
  return null;
}

export function buildCodexExecutionEnv(baseEnv, managedHome) {
  const out = {};
  for (const [k, v] of Object.entries(baseEnv ?? {})) if (typeof v === 'string') out[k] = v;
  if (managedHome) {
    out.CODEX_HOME = managedHome;
    for (const k of ['OPENAI_API_KEY', 'CODEX_API_KEY', 'CODEX_ACCESS_TOKEN', 'OPENAI_BASE_URL']) delete out[k];
  }
  return out;
}
