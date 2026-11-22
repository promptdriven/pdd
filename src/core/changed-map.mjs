// Generated from prompts/cli/update-sync.prompt.md.
// Read-only polyglot diff -> owning prompt -> changed-symbols extractor for `pdd status --changed` and `pdd update`.
import { execFileSync } from 'node:child_process';
import { closeSync, constants as fsConstants, fstatSync, lstatSync, openSync, readSync, realpathSync } from 'node:fs';
import { isAbsolute, join, posix, relative, resolve, sep } from 'node:path';
import {
  findOwners,
  headerEntries,
  headerHashState,
  isTestOwnedPath,
  isTestPromptPath,
  promptClaims,
  promptHeaderHash,
} from '../file-owner.mjs';
import { gitFiles } from '../shared/git-context.mjs';
import { isSecretPath } from '../shared/safe-read.mjs';

const MAX_FILE_BYTES = 10 * 1024 * 1024;
const MAX_BINDINGS_BYTES = 65_536;
const BINARY_PROBE_BYTES = 8_192;
const EXTRA_SECRET_NAME = /^(?:\.env(?:\..+)?|credentials(?:\.[^/]+)?|\.aws-credentials)$/i;
const O_NOFOLLOW = fsConstants.O_NOFOLLOW ?? 0;
const NON_CANDIDATE_DIR = /^(?:user_stories|docs?|\.github|\.pdd)\//i;
const NON_CANDIDATE_EXT = /\.(?:mdx?|rst|txt|json|jsonl|ndjson|ya?ml|toml|ini|cfg|conf|lock|csv|tsv|xml|svg|png|jpe?g|gif|webp|ico|pdf|woff2?)$/i;
const DOTFILE_SEG = /(?:^|\/)\.[^/]+$/;
const SAFE_GIT_DIFF_PREFIX = ['--literal-pathspecs', '-c', 'core.quotepath=false', '-c', 'diff.noprefix=false', '-c', 'diff.mnemonicPrefix=false'];

const SYMBOL_PATTERNS = [
  /^\s*export\s+(?:default\s+)?(?:async\s+)?function\*?\s+([A-Za-z_$][\w$]*)/,
  /^\s*export\s+(?:default\s+)?(?:const|let|var|class|interface|type|enum)\s+([A-Za-z_$][\w$]*)/,
  /^(?:async\s+)?function\*?\s+([A-Za-z_$][\w$]*)\s*\(/,
  /^(?:async\s+)?def\s+([A-Za-z_]\w*)\s*\(/,
  /^class\s+([A-Za-z_]\w*)\b/,
  /^func\s+(?:\([^)]*\)\s*)?([A-Za-z_]\w*)\s*\(/,
  /^\s*pub(?:\([^)]*\))?\s+(?:async\s+)?(?:fn|struct|enum|trait|type|const)\s+([A-Za-z_]\w*)\b/,
];

const cmpPath = (a, b) => (a < b ? -1 : a > b ? 1 : 0);
const unique = values => [...new Set(values)];
const sanitizeOneLine = text => String(text ?? '').replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').slice(0, 200);
const canonicalPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');
const isBlockedSecretPath = path => isSecretPath(path) || EXTRA_SECRET_NAME.test(posix.basename(path));
const isPddInternalPath = path => path === '.pdd' || path.startsWith('.pdd/');

class ChangedMapStop extends Error {
  constructor(exitCode, message) { super(message); this.exitCode = exitCode; }
}

function parseFromRange(raw) {
  if (typeof raw !== 'string' || !raw || raw.length > 256 || /[\s\x00-\x1f\x7f]/.test(raw) || raw.includes('...') || raw.startsWith('-')) {
    throw new ChangedMapStop(2, `Invalid --from range: ${sanitizeOneLine(raw)}. Use <base>..<head> or <base>.`);
  }
  const parts = raw.split('..');
  if (parts.length === 1) return `${parts[0]}..HEAD`;
  if (parts.length === 2 && parts[0] && parts[1] && !parts[0].startsWith('-') && !parts[1].startsWith('-')) return `${parts[0]}..${parts[1]}`;
  throw new ChangedMapStop(2, `Invalid --from range: ${sanitizeOneLine(raw)}. Use <base>..<head> or <base>.`);
}

function readRegularBytes(root, relPath, limit = MAX_FILE_BYTES, { truncate = false } = {}) {
  let cur = root;
  const parts = relPath.split('/');
  for (let i = 0; i < parts.length; i++) {
    cur = join(cur, parts[i]);
    let st;
    try { st = lstatSync(cur); }
    catch (error) {
      if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return { status: 'missing', bytes: null };
      throw new ChangedMapStop(2, `Could not inspect path ${relPath}: ${sanitizeOneLine(error.message)}.`);
    }
    if (st.isSymbolicLink()) return { status: 'symlink', bytes: null };
    if (i === parts.length - 1 ? !st.isFile() : !st.isDirectory()) return { status: 'non-file', bytes: null };
  }
  let fd;
  try { fd = openSync(cur, fsConstants.O_RDONLY | O_NOFOLLOW); }
  catch (error) {
    if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return { status: 'missing', bytes: null };
    if (error.code === 'ELOOP') return { status: 'symlink', bytes: null };
    throw new ChangedMapStop(2, `Could not read ${relPath}: ${sanitizeOneLine(error.message)}.`);
  }
  try {
    const st = fstatSync(fd);
    if (!st.isFile()) return { status: 'non-file', bytes: null };
    const toRead = truncate ? Math.min(limit, st.size) : Math.min(limit + 1, st.size);
    const buffer = Buffer.alloc(toRead);
    let total = 0;
    while (total < toRead) {
      const count = readSync(fd, buffer, total, toRead - total, total);
      if (!count) break;
      total += count;
    }
    const slice = buffer.subarray(0, total);
    return !truncate && slice.length > limit ? { status: 'too-large', bytes: null } : { status: 'ok', bytes: slice };
  } finally { closeSync(fd); }
}

const gitExec = (cwd, args, encoding) => execFileSync('git', args, {
  cwd, maxBuffer: 32 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'], ...(encoding ? { encoding } : {}),
});
const defaultGitRoot = cwd => { try { const top = gitExec(cwd, ['rev-parse', '--show-toplevel'], 'utf8').trim(); return top ? realpathSync(top) : null; } catch { return null; } };
const hasGitHead = root => { try { gitExec(root, ['rev-parse', '--verify', 'HEAD']); return true; } catch { return false; } };
const splitNullTokens = buffer => {
  const tokens = String(Buffer.isBuffer(buffer) ? buffer.toString('utf8') : (buffer ?? '')).split('\0');
  if (tokens.length && tokens.at(-1) === '') tokens.pop();
  return tokens;
};

function parseNameStatusZ(buffer) {
  const tokens = splitNullTokens(buffer), entries = [];
  for (let i = 0; i < tokens.length;) {
    const code = tokens[i++];
    if (!code) continue;
    const letter = code[0];
    if (letter === 'R' || letter === 'C') {
      const oldPath = tokens[i++], newPath = tokens[i++];
      if (newPath) entries.push({ path: newPath, status: letter, renamedFrom: letter === 'R' ? (oldPath ?? null) : null, deleted: false, untracked: false });
    } else {
      const path = tokens[i++];
      if (path) entries.push({ path, status: letter, renamedFrom: null, deleted: letter === 'D', untracked: false });
    }
  }
  return entries;
}

function parsePorcelainZ(buffer) {
  const tokens = splitNullTokens(buffer), entries = [];
  for (let i = 0; i < tokens.length;) {
    const rec = tokens[i++];
    if (rec.length < 4) continue;
    const x = rec[0], y = rec[1], path = rec.slice(3);
    const renamedFrom = (x === 'R' || x === 'C' || y === 'R' || y === 'C') ? ((x === 'R' || y === 'R') ? (tokens[i++] ?? null) : (tokens[i++], null)) : null;
    const untracked = x === '?' && y === '?', deleted = !untracked && (x === 'D' || y === 'D') && x !== 'A' && y !== 'A';
    entries.push({ path, status: untracked ? 'A' : deleted ? 'D' : renamedFrom ? 'R' : (x === 'A' || y === 'A') ? 'A' : 'M', renamedFrom, deleted, untracked });
  }
  return entries;
}

function defaultGitRangeEntries(root, range) {
  try { return parseNameStatusZ(gitExec(root, [...SAFE_GIT_DIFF_PREFIX, 'diff', '--name-status', '-z', '-M', '--no-ext-diff', range, '--'])); }
  catch { throw new ChangedMapStop(2, `Git diff range unavailable: ${sanitizeOneLine(range)}.`); }
}

function defaultGitWorkingEntries(root) {
  const byPath = new Map();
  const add = e => { const p = byPath.get(e.path); byPath.set(e.path, p ? { ...p, renamedFrom: p.renamedFrom ?? e.renamedFrom, deleted: p.deleted && e.deleted, untracked: p.untracked || e.untracked } : e); };
  if (hasGitHead(root)) { try { for (const e of parseNameStatusZ(gitExec(root, [...SAFE_GIT_DIFF_PREFIX, 'diff', '--name-status', '-z', '-M', '--no-ext-diff', 'HEAD', '--']))) add(e); } catch {} }
  try { for (const e of parsePorcelainZ(gitExec(root, ['--literal-pathspecs', '-c', 'core.quotepath=false', 'status', '--porcelain=v1', '-z', '-uall']))) add(e); }
  catch (error) { throw new ChangedMapStop(2, `Git status failed: ${sanitizeOneLine(error.message)}.`); }
  return [...byPath.values()].sort((a, b) => cmpPath(a.path, b.path));
}

function defaultGitUntrackedSet(root, paths) {
  const set = new Set();
  if (!paths.length) return set;
  try { for (const e of parsePorcelainZ(gitExec(root, ['--literal-pathspecs', '-c', 'core.quotepath=false', 'status', '--porcelain=v1', '-z', '-uall', '--', ...paths]))) if (e.untracked) set.add(e.path); } catch {}
  return set;
}

function defaultGitUnifiedDiff(root, range, paths) {
  if (!paths.length) return '';
  const target = range || (hasGitHead(root) ? 'HEAD' : null);
  if (!target) return '';
  try { return gitExec(root, [...SAFE_GIT_DIFF_PREFIX, 'diff', '--src-prefix=a/', '--dst-prefix=b/', '--no-color', '--no-ext-diff', '-M', '-U0', target, '--', ...paths], 'utf8'); }
  catch { return ''; }
}

function splitDiffByFile(fullDiff, knownPaths = new Set()) {
  const byPath = new Map();
  for (const chunk of String(fullDiff || '').split(/^diff --git /m)) {
    if (!chunk) continue;
    const nl = chunk.indexOf('\n');
    const headerLine = (nl >= 0 ? chunk.slice(0, nl) : chunk).replace(/\r$/, '');
    const plus = /^\+\+\+ (?:b\/([^\r\n\t]+)|\/dev\/null)\t?\r?$/m.exec(chunk);
    const renameTo = /^rename to ([^\r\n]+)\r?$/m.exec(chunk);
    const minus = /^--- (?:a\/([^\r\n\t]+)|\/dev\/null)\t?\r?$/m.exec(chunk);
    let target = plus?.[1] || renameTo?.[1] || minus?.[1] || null;
    if (!target) {
      for (const candidate of knownPaths) if (headerLine.endsWith(` b/${candidate}`)) { target = candidate; break; }
      if (!target) { const idx = headerLine.lastIndexOf(' b/'); if (idx >= 0) target = headerLine.slice(idx + 3); }
    }
    if (target) byPath.set(target, `diff --git ${chunk}`);
  }
  return byPath;
}

/**
 * Count added/removed lines and extract added/removed/updated top-level symbols across JS/TS, Python, Go, and Rust.
 */
export function extractDiffSummary(diffText) {
  let added = 0, removed = 0;
  const addedSymbols = new Set(), removedSymbols = new Set();
  for (const line of String(diffText || '').split(/\r?\n/)) {
    if (line.startsWith('+++ ') || line.startsWith('--- ')) continue;
    const isAdd = line.startsWith('+'), isRem = line.startsWith('-');
    if (!isAdd && !isRem) continue;
    if (isAdd) added++; else removed++;
    const codeLine = line.slice(1);
    for (const pattern of SYMBOL_PATTERNS) {
      const m = pattern.exec(codeLine);
      if (m) { (isAdd ? addedSymbols : removedSymbols).add(m[1]); break; }
    }
  }
  const changed_symbols = unique([...addedSymbols, ...removedSymbols]).sort(cmpPath).map(symbol => ({
    kind: addedSymbols.has(symbol) && removedSymbols.has(symbol) ? 'updated' : addedSymbols.has(symbol) ? 'added' : 'removed',
    symbol,
  }));
  return { added, removed, changed_symbols };
}

function summarizeWholeFile(text) {
  if (!text) return { added: 0, removed: 0, changed_symbols: [] };
  const lines = text.split(/\r?\n/).filter((l, i, arr) => i < arr.length - 1 || l.length > 0);
  return extractDiffSummary(lines.map(l => `+${l}`).join('\n'));
}

function validateBindings(readBytes) {
  const res = readBytes('pdd-bindings.json', MAX_BINDINGS_BYTES);
  if (res.status === 'missing') return null;
  if (res.status === 'symlink') throw new ChangedMapStop(2, 'Symlinks are not allowed: pdd-bindings.json.');
  if (res.status !== 'ok' || res.bytes.includes(0)) throw new ChangedMapStop(2, 'pdd-bindings.json is malformed or unreadable; fix it before continuing.');
  let doc;
  try { doc = JSON.parse(new TextDecoder('utf-8').decode(res.bytes)); }
  catch { throw new ChangedMapStop(2, 'pdd-bindings.json is malformed or unreadable; fix it before continuing.'); }
  if (!doc || typeof doc !== 'object' || Array.isArray(doc) || doc.schema_version !== 'pdd.bindings.v1' || !Array.isArray(doc.modules)) {
    throw new ChangedMapStop(2, 'pdd-bindings.json is malformed or unreadable; fix it before continuing.');
  }
  return doc;
}

/**
 * Read-only diff -> owner -> changed-symbols analysis. Never mutates files or writes sidecars.
 */
export function analyzeChangedMap({ cwd = process.cwd(), files = [], from } = {}, ports = {}) {
  try {
    if (files.length > 0 && from !== undefined) throw new ChangedMapStop(2, 'Specify either file paths or --from RANGE, not both.');
    const normalizedRange = from !== undefined ? parseFromRange(from) : null;
    const root = ports.gitRoot ? ports.gitRoot(cwd) : defaultGitRoot(cwd);
    if (!root) throw new ChangedMapStop(2, 'This command works inside a Git repository.');

    const scopeKind = files.length > 0 ? 'files' : normalizedRange ? 'from' : 'working-tree';
    const readBytes = ports.readBytes ?? ((path, limit) => readRegularBytes(root, path, limit));
    const probeBytes = ports.probeBytes ?? ((path, limit) => readRegularBytes(root, path, limit, { truncate: true }));
    const listFiles = () => (ports.files ? ports.files() : gitFiles(root)).filter(p => !isBlockedSecretPath(p));
    const bindingsDoc = validateBindings(readBytes);

    const codeBytesMap = new Map(), unownedMap = new Map(), touchedMap = new Map();
    if (scopeKind === 'files') {
      let realCwd;
      try { realCwd = ports.realCwd ? ports.realCwd(cwd) : realpathSync(cwd); } catch { realCwd = root; }
      const resolved = [];
      for (const typed of files) {
        if (typeof typed !== 'string' || !typed.trim()) throw new ChangedMapStop(2, 'Invalid empty file path.');
        if (typed.startsWith('-')) throw new ChangedMapStop(2, `Invalid file path (leading '-' is not allowed): ${sanitizeOneLine(typed)}.`);
        if (/[\x00-\x1f\x7f\\]/.test(typed)) throw new ChangedMapStop(2, `Invalid file path: ${sanitizeOneLine(typed)}.`);
        if (typed.split('/').includes('..')) throw new ChangedMapStop(2, `Path traversal is not allowed: ${sanitizeOneLine(typed)}.`);
        const rel = relative(root, resolve(realCwd, typed)).split(sep).join('/');
        if (!canonicalPath(rel)) throw new ChangedMapStop(2, `${sanitizeOneLine(typed)} is not a file path inside this repository.`);
        if (isBlockedSecretPath(rel)) throw new ChangedMapStop(2, `Secret-looking path is not allowed: ${rel}.`);
        const read = readBytes(rel, MAX_FILE_BYTES);
        if (read.status === 'missing') throw new ChangedMapStop(2, `Missing file: ${rel}.`);
        if (read.status === 'symlink') throw new ChangedMapStop(2, `Symlinks are not allowed: ${rel}.`);
        if (read.status === 'non-file') throw new ChangedMapStop(2, `Not a regular file: ${rel}.`);
        if (read.status === 'too-large') throw new ChangedMapStop(2, `File exceeds 10 MiB limit: ${rel}.`);
        if (read.bytes.includes(0)) throw new ChangedMapStop(2, `Binary file is not supported: ${rel}.`);
        codeBytesMap.set(rel, read.bytes);
        resolved.push(rel);
      }
      const untracked = ports.gitUntrackedSet ? ports.gitUntrackedSet(root, resolved) : defaultGitUntrackedSet(root, resolved);
      for (const rel of resolved) touchedMap.set(rel, { path: rel, status: untracked.has(rel) ? 'A' : 'M', renamedFrom: null, deleted: false, untracked: untracked.has(rel) });
    } else {
      const rawEntries = scopeKind === 'from'
        ? (ports.gitRangeEntries ? ports.gitRangeEntries(root, normalizedRange) : defaultGitRangeEntries(root, normalizedRange))
        : (ports.gitWorkingEntries ? ports.gitWorkingEntries(root) : defaultGitWorkingEntries(root));
      for (const raw of rawEntries) {
        if (isPddInternalPath(raw.path)) continue;
        if (!canonicalPath(raw.path)) throw new ChangedMapStop(2, `Invalid touched path: ${sanitizeOneLine(raw.path)}.`);
        if (isBlockedSecretPath(raw.path)) throw new ChangedMapStop(2, `Secret-looking path is not allowed: ${raw.path}.`);
        if (raw.renamedFrom && (!canonicalPath(raw.renamedFrom) || isBlockedSecretPath(raw.renamedFrom))) {
          throw new ChangedMapStop(2, `Invalid or secret renamed path: ${sanitizeOneLine(raw.renamedFrom)}.`);
        }
        if (raw.deleted) { touchedMap.set(raw.path, { ...raw, deleted: true }); continue; }
        const probe = probeBytes(raw.path, BINARY_PROBE_BYTES);
        if (probe.status === 'missing') { touchedMap.set(raw.path, { ...raw, deleted: true }); continue; }
        if (probe.status === 'symlink') throw new ChangedMapStop(2, `Symlinks are not allowed: ${raw.path}.`);
        if (probe.status === 'non-file') { unownedMap.set(raw.path, { path: raw.path, reason: 'non-regular entry (skipped)' }); continue; }
        touchedMap.set(raw.path, { ...raw, deleted: false });
      }
    }

    const touchedEntries = [...touchedMap.values()].sort((a, b) => cmpPath(a.path, b.path));
    const scope = { kind: scopeKind, range: normalizedRange, files: touchedEntries.map(e => e.path) };
    if (!touchedEntries.length && !unownedMap.size) {
      return { ok: true, exitCode: 0, error: null, root, report: { schema_version: 'pdd.changed-map.v1', ok: true, scope, prompts: [], modules: [], unowned: [] } };
    }

    const touchedPrompts = touchedEntries.filter(e => e.path.endsWith('.prompt.md'));
    for (const entry of touchedPrompts) {
      if (!entry.deleted && isTestPromptPath(entry.path)) throw new ChangedMapStop(1, `Error: misplaced test prompt: ${entry.path}. Prompts own production modules, not test files.`);
    }

    const safeVisible = listFiles();
    const ownerReadCache = new Map();
    const ownerPorts = {
      files: () => safeVisible,
      read: (path, limit) => {
        if (!canonicalPath(path) || isBlockedSecretPath(path)) return null;
        const key = `${path}\0${limit}`;
        if (ownerReadCache.has(key)) return ownerReadCache.get(key);
        const value = ports.read ? ports.read(path, limit) : (() => { const r = probeBytes(path, limit); return r.status === 'ok' ? r.bytes : null; })();
        ownerReadCache.set(key, value);
        return value;
      },
    };

    const decodeUtf8 = bytes => new TextDecoder('utf-8', { ignoreBOM: true }).decode(bytes);
    const readTextOrStop = (rel, { missingCode = 2, missingMsg = `Cannot read file: ${rel}.`, allowMissing = false } = {}) => {
      let bytes = codeBytesMap.get(rel);
      if (!bytes) {
        const r = readBytes(rel, MAX_FILE_BYTES);
        if (r.status === 'symlink') throw new ChangedMapStop(2, `Symlinks are not allowed: ${rel}.`);
        if (r.status === 'too-large') throw new ChangedMapStop(missingCode, `File exceeds 10 MiB limit: ${rel}.`);
        if (r.status !== 'ok') { if (allowMissing) return null; throw new ChangedMapStop(missingCode, missingMsg); }
        bytes = r.bytes;
        codeBytesMap.set(rel, bytes);
      }
      if (bytes.includes(0)) throw new ChangedMapStop(2, `Binary file is not supported: ${rel}.`);
      return decodeUtf8(bytes);
    };

    const nonPromptMap = new Map(touchedEntries.filter(e => !e.path.endsWith('.prompt.md')).map(e => [e.path, e]));
    const touchedPromptTargets = new Set([...touchedPrompts.map(e => e.path), ...touchedEntries.filter(e => e.renamedFrom?.endsWith('.prompt.md')).map(e => e.renamedFrom)]);
    const promptTextMap = new Map();
    for (const entry of touchedPrompts.filter(e => !e.deleted)) {
      promptTextMap.set(entry.path, readTextOrStop(entry.path, { missingCode: 1, missingMsg: `Owning prompt is missing or unreadable: ${entry.path}.` }));
    }

    if (touchedPromptTargets.size > 0) {
      const candidates = new Set();
      for (const item of bindingsDoc?.modules ?? []) if (touchedPromptTargets.has(item?.prompt) && canonicalPath(item?.module) && !isBlockedSecretPath(item.module)) candidates.add(item.module);
      for (const [p, text] of promptTextMap.entries()) for (const claimed of promptClaims(p, text)) if (canonicalPath(claimed) && !isBlockedSecretPath(claimed) && !claimed.endsWith('.prompt.md')) candidates.add(claimed);
      for (const p of safeVisible) if (canonicalPath(p) && !p.endsWith('.prompt.md') && !isPddInternalPath(p) && !isTestOwnedPath(p) && !NON_CANDIDATE_DIR.test(p) && !DOTFILE_SEG.test(p) && !NON_CANDIDATE_EXT.test(p)) candidates.add(p);
      if (candidates.size) {
        for (const row of findOwners({ root, paths: [...candidates].sort(cmpPath) }, ownerPorts).files) {
          if (nonPromptMap.has(row.path) || !row.owners.some(o => touchedPromptTargets.has(o))) continue;
          const probe = probeBytes(row.path, BINARY_PROBE_BYTES);
          if (probe.status === 'symlink') throw new ChangedMapStop(2, `Symlinks are not allowed: ${row.path}.`);
          if (probe.status !== 'non-file') nonPromptMap.set(row.path, { path: row.path, status: probe.status === 'missing' ? 'D' : 'M', renamedFrom: null, deleted: probe.status === 'missing', untracked: false });
        }
      }
    }

    const candidateEntries = [...nonPromptMap.values()].sort((a, b) => cmpPath(a.path, b.path));
    const ownerByPath = new Map((candidateEntries.length ? findOwners({ root, paths: candidateEntries.map(e => e.path) }, ownerPorts).files : []).map(r => [r.path, r]));
    const ownedPairs = [], neededPrompts = new Set(), activeNeededPrompts = new Set(), codeTextMap = new Map();

    for (const entry of candidateEntries) {
      const ownerRow = ownerByPath.get(entry.path) ?? { path: entry.path, owner: null, owners: [], source: null, certain: true, note: '', headers: [] };
      if (!ownerRow.owners.length) {
        const probe = !entry.deleted ? (codeBytesMap.has(entry.path) ? { status: 'ok', bytes: codeBytesMap.get(entry.path) } : probeBytes(entry.path, BINARY_PROBE_BYTES)) : null;
        unownedMap.set(entry.path, { path: entry.path, reason: probe?.status === 'ok' && probe.bytes.includes(0) ? 'binary file (skipped)' : 'no owning prompt' });
        continue;
      }
      for (const owner of ownerRow.owners) {
        if (isBlockedSecretPath(owner)) throw new ChangedMapStop(2, `Secret-looking path is not allowed: ${owner}.`);
        if (isTestPromptPath(owner)) throw new ChangedMapStop(1, `Error: misplaced test prompt: ${entry.path} is claimed by ${owner}. Prompts own production modules, not test files.`);
      }
      if (!entry.deleted) codeTextMap.set(entry.path, readTextOrStop(entry.path));
      for (const owner of ownerRow.owners) { neededPrompts.add(owner); if (!entry.deleted) activeNeededPrompts.add(owner); ownedPairs.push({ entry, ownerRow, owner }); }
    }

    for (const promptPath of [...neededPrompts].sort(cmpPath)) {
      if (promptTextMap.has(promptPath)) continue;
      if (!canonicalPath(promptPath)) throw new ChangedMapStop(1, `Owning prompt path is invalid: ${sanitizeOneLine(promptPath)}.`);
      if (isBlockedSecretPath(promptPath)) throw new ChangedMapStop(2, `Secret-looking path is not allowed: ${promptPath}.`);
      const text = readTextOrStop(promptPath, { missingCode: 1, missingMsg: `Owning prompt is missing or unreadable: ${promptPath}.`, allowMissing: !activeNeededPrompts.has(promptPath) });
      if (text !== null) promptTextMap.set(promptPath, text);
    }

    const diffPaths = unique(ownedPairs.flatMap(p => [p.entry.path, ...(p.entry.renamedFrom ? [p.entry.renamedFrom] : [])])).sort(cmpPath);
    const fullDiff = diffPaths.length ? (ports.gitUnifiedDiff ? ports.gitUnifiedDiff(root, normalizedRange, diffPaths) : defaultGitUnifiedDiff(root, normalizedRange, diffPaths)) : '';
    const diffChunks = splitDiffByFile(fullDiff, new Set(ownedPairs.map(p => p.entry.path)));
    const modules = [], byPrompt = new Map();

    for (const { entry, ownerRow, owner } of ownedPairs) {
      const promptText = promptTextMap.get(owner) ?? null;
      const prompt_sha256 = promptText !== null ? promptHeaderHash(promptText) : null;
      const chunk = diffChunks.get(entry.path);
      const diff = chunk ? extractDiffSummary(chunk) : (!entry.deleted && (entry.untracked || entry.status === 'A') ? summarizeWholeFile(codeTextMap.get(entry.path) ?? '') : { added: 0, removed: 0, changed_symbols: [] });
      const headerRow = !entry.deleted ? (headerEntries(codeTextMap.get(entry.path)).find(h => h.prompt === owner) ?? null) : null;
      const headerState = headerRow && promptText !== null ? headerHashState(headerRow.sha256, promptText).state : null;
      const status = entry.deleted ? 'deleted' : headerState === 'stale' ? 'prompt-stale' : (diff.added > 0 || diff.removed > 0 || entry.renamedFrom) ? 'changed' : 'current';
      const row = {
        path: entry.path, owner, owners: ownerRow.owners, source: ownerRow.source, certain: ownerRow.certain, status,
        prompt_sha256, header_state: headerState, diff_stats: { added: diff.added, removed: diff.removed },
        changed_symbols: diff.changed_symbols, deleted: entry.deleted, renamed_from: entry.renamedFrom ?? null, note: ownerRow.note ?? '',
      };
      modules.push(row);
      if (!byPrompt.has(owner)) byPrompt.set(owner, []);
      byPrompt.get(owner).push(row);
    }

    const prompts = [...byPrompt.entries()].sort(([a], [b]) => cmpPath(a, b)).map(([prompt, rows]) => {
      rows.sort((a, b) => cmpPath(a.path, b.path));
      const added = rows.reduce((s, r) => s + r.diff_stats.added, 0);
      const removed = rows.reduce((s, r) => s + r.diff_stats.removed, 0);
      const symMap = new Map();
      for (const r of rows) for (const sym of r.changed_symbols) symMap.set(sym.symbol, symMap.has(sym.symbol) && symMap.get(sym.symbol) !== sym.kind ? 'updated' : sym.kind);
      const statuses = new Set(rows.map(r => r.status));
      const status = statuses.has('prompt-stale') ? 'prompt-stale' : statuses.has('changed') ? 'changed' : statuses.has('deleted') ? 'deleted' : 'current';
      return {
        prompt, status, prompt_sha256: rows[0]?.prompt_sha256 ?? null, owner_certain: rows.every(r => r.certain),
        modules: rows.map(r => r.path), diff_stats: { added, removed },
        changed_symbols: [...symMap.entries()].sort(([a], [b]) => cmpPath(a, b)).map(([symbol, kind]) => ({ kind, symbol })),
      };
    });
    modules.sort((a, b) => cmpPath(a.path, b.path) || cmpPath(a.owner, b.owner));
    const unowned = [...unownedMap.values()].sort((a, b) => cmpPath(a.path, b.path));
    return { ok: true, exitCode: 0, error: null, root, report: { schema_version: 'pdd.changed-map.v1', ok: true, scope, prompts, modules, unowned } };
  } catch (error) {
    if (error instanceof ChangedMapStop) return { ok: false, exitCode: error.exitCode, error: error.message, report: null, root: null };
    return { ok: false, exitCode: 2, error: `Changed-map analysis failed: ${sanitizeOneLine(error?.message ?? error)}.`, report: null, root: null };
  }
}

const formatSymbols = symbols => (symbols?.length ? `; symbols: ${symbols.map(s => `${({ added: '+', removed: '-', updated: '~' })[s.kind] ?? ''}${s.symbol}`).join(', ')}` : '');

export function formatChangedMapJson(report) { return `${JSON.stringify(report)}\n`; }

export function formatChangedMapText(report, heading = 'pdd status --changed') {
  if (!report.prompts.length && !report.unowned.length) return `${heading}: no touched files in scope.\n`;
  const lines = [`${heading}: ${report.prompts.length} prompt(s), ${report.modules.length} owned module(s), ${report.unowned.length} unowned`];
  const byPrompt = new Map();
  for (const mod of report.modules) { if (!byPrompt.has(mod.owner)) byPrompt.set(mod.owner, []); byPrompt.get(mod.owner).push(mod); }
  for (const group of report.prompts) {
    lines.push(`${group.prompt} [${group.status}] (prompt_sha256: ${group.prompt_sha256 ? group.prompt_sha256.slice(0, 12) : 'deleted'})`);
    for (const mod of byPrompt.get(group.prompt) ?? []) {
      const renamed = mod.renamed_from ? ` (renamed from ${mod.renamed_from})` : '';
      lines.push(`  - ${mod.path} [${mod.status}] (+${mod.diff_stats.added}/-${mod.diff_stats.removed})${formatSymbols(mod.changed_symbols)}${renamed}`);
      if (mod.note) lines.push(`    note: ${mod.note}`);
    }
  }
  if (report.unowned.length) {
    lines.push(`Unowned files (${report.unowned.length}):`);
    for (const item of report.unowned) lines.push(`  - ${item.path} (${item.reason})`);
  }
  return `${lines.join('\n')}\n`;
}
