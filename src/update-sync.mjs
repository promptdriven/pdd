// Generated from prompts/cli/update-sync.prompt.md (sha256: 22002b49827421c95f3fe301837d535c0844070f4d645f9118f86183538bdfc1).
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import {
  closeSync,
  constants as fsConstants,
  fstatSync,
  lstatSync,
  mkdirSync,
  openSync,
  readdirSync,
  readSync,
  realpathSync,
  renameSync,
  rmdirSync,
  unlinkSync,
  writeSync,
} from 'node:fs';
import { dirname, isAbsolute, join, posix, relative, resolve, sep } from 'node:path';
import {
  findOwners,
  headerEntries,
  headerHashState,
  isTestOwnedPath,
  isTestPromptPath,
  moduleContentHash,
  promptClaims,
  promptHeaderHash,
  updateHeaderHash,
} from './file-owner.mjs';
import { runtimePreflightSlice } from './runtime-seam.mjs';

const { gitFiles, isSecretPath } = runtimePreflightSlice();

const MAX_FILE_BYTES = 10 * 1024 * 1024;
const MAX_SIDECAR_BYTES = 65536;
const MAX_BINDINGS_BYTES = 65536;
const BINARY_PROBE_BYTES = 8192;
const SYNC_DIR_REL = '.pdd/sync';
const SYNC_SCHEMA_VERSION = 'pdd.module-sync.v1';
const HEX64 = /^[a-f0-9]{64}$/;
const EXTRA_SECRET_NAME = /^(?:\.env(?:\..+)?|credentials(?:\.[^/]+)?|\.aws-credentials)$/i;
const O_NOFOLLOW = fsConstants.O_NOFOLLOW ?? 0;

const NON_CANDIDATE_DIR = /^(?:user_stories|docs?|\.github|\.pdd)\//i;
const NON_CANDIDATE_EXT = /\.(?:mdx?|rst|txt|json|jsonl|ndjson|ya?ml|toml|ini|cfg|conf|lock|csv|tsv|xml|svg|png|jpe?g|gif|webp|ico|pdf|woff2?)$/i;
const DOTFILE_SEG = /(?:^|\/)\.[^/]+$/;

const cmpPath = (a, b) => (a < b ? -1 : a > b ? 1 : 0);
const unique = values => [...new Set(values)];
const sanitizeOneLine = text => String(text ?? '').replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').slice(0, 200);
const canonicalPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');
const isBlockedSecretPath = path => isSecretPath(path) || EXTRA_SECRET_NAME.test(posix.basename(path));
const isPddInternalPath = path => path === '.pdd' || path.startsWith('.pdd/');
const isSyncSidecarPath = path => path === SYNC_DIR_REL || path.startsWith(`${SYNC_DIR_REL}/`);
const shellArg = value => (/^[A-Za-z0-9_./@+-]+$/.test(value) ? value : `'${value.replace(/'/g, "'\\''")}'`);

class UpdateStop extends Error {
  constructor(exitCode, message) {
    super(message);
    this.exitCode = exitCode;
  }
}

export function syncRecordPathForModule(modulePath) {
  if (!canonicalPath(modulePath) || isBlockedSecretPath(modulePath) || isPddInternalPath(modulePath)) {
    throw new UpdateStop(2, `Invalid module path for sync record: ${sanitizeOneLine(modulePath)}.`);
  }
  return `${SYNC_DIR_REL}/${modulePath}.json`;
}

function parseFromRange(raw) {
  if (typeof raw !== 'string') throw new UpdateStop(2, 'Invalid --from range. Use <base>..<head> or <base>.');
  if (!raw || raw.length > 256 || /[\s\x00-\x1f\x7f]/.test(raw) || raw.includes('...') || raw.startsWith('-')) {
    throw new UpdateStop(2, `Invalid --from range: ${sanitizeOneLine(raw)}. Use <base>..<head> or <base>.`);
  }
  const parts = raw.split('..');
  if (parts.length === 1) return `${parts[0]}..HEAD`;
  if (parts.length === 2) {
    const [base, head] = parts;
    if (!base || !head || base.startsWith('-') || head.startsWith('-')) {
      throw new UpdateStop(2, `Invalid --from range: ${sanitizeOneLine(raw)}. Use <base>..<head> or <base>.`);
    }
    return `${base}..${head}`;
  }
  throw new UpdateStop(2, `Invalid --from range: ${sanitizeOneLine(raw)}. Use <base>..<head> or <base>.`);
}

function inspectRegularPath(root, relPath) {
  const parts = relPath.split('/');
  let cur = root;
  for (let i = 0; i < parts.length; i++) {
    cur = join(cur, parts[i]);
    let st;
    try { st = lstatSync(cur); }
    catch (error) {
      if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return { kind: 'missing', full: cur };
      throw new UpdateStop(2, `Could not inspect path ${relPath}: ${sanitizeOneLine(error.message)}.`);
    }
    if (st.isSymbolicLink()) return { kind: 'symlink', full: cur };
    if (i === parts.length - 1) {
      if (!st.isFile()) return { kind: 'non-file', full: cur };
    } else if (!st.isDirectory()) {
      return { kind: 'non-file', full: cur };
    }
  }
  return { kind: 'file', full: cur };
}

function readRegularBytes(root, relPath, limit = MAX_FILE_BYTES, { truncate = false } = {}) {
  const check = inspectRegularPath(root, relPath);
  if (check.kind === 'missing') return { status: 'missing', bytes: null };
  if (check.kind === 'symlink') return { status: 'symlink', bytes: null };
  if (check.kind !== 'file') return { status: 'non-file', bytes: null };
  let fd;
  try { fd = openSync(check.full, fsConstants.O_RDONLY | O_NOFOLLOW); }
  catch (error) {
    if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return { status: 'missing', bytes: null };
    if (error.code === 'ELOOP') return { status: 'symlink', bytes: null };
    throw new UpdateStop(2, `Could not read ${relPath}: ${sanitizeOneLine(error.message)}.`);
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
    if (!truncate && slice.length > limit) return { status: 'too-large', bytes: null };
    return { status: 'ok', bytes: slice };
  } catch (error) {
    throw new UpdateStop(2, `Could not read ${relPath}: ${sanitizeOneLine(error.message)}.`);
  } finally {
    closeSync(fd);
  }
}

function probeRegularBytes(root, relPath, limit = BINARY_PROBE_BYTES) {
  return readRegularBytes(root, relPath, limit, { truncate: true });
}

function writeRegularAtomicUtf8(root, relPath, text, { createParents = false, defaultMode = 0o644 } = {}) {
  const parts = relPath.split('/');
  let cur = root;
  for (let i = 0; i < parts.length - 1; i++) {
    cur = join(cur, parts[i]);
    let st = null;
    try { st = lstatSync(cur); }
    catch (error) {
      if (error.code !== 'ENOENT') throw new UpdateStop(2, `Could not access directory for ${relPath}: ${sanitizeOneLine(error.message)}.`);
    }
    if (st === null) {
      if (!createParents) throw new UpdateStop(2, `Parent directory is missing for ${relPath}.`);
      try { mkdirSync(cur); }
      catch (error) {
        if (error.code !== 'EEXIST') throw new UpdateStop(2, `Could not create directory for ${relPath}: ${sanitizeOneLine(error.message)}.`);
      }
      try { st = lstatSync(cur); }
      catch (error) { throw new UpdateStop(2, `Could not verify directory for ${relPath}: ${sanitizeOneLine(error.message)}.`); }
    }
    if (st.isSymbolicLink()) throw new UpdateStop(2, `Symlinks are not allowed: ${parts.slice(0, i + 1).join('/')}.`);
    if (!st.isDirectory()) throw new UpdateStop(2, `Path is not a directory: ${parts.slice(0, i + 1).join('/')}.`);
  }

  const targetFull = join(cur, parts.at(-1));
  let mode = defaultMode;
  try {
    const st = lstatSync(targetFull);
    if (st.isSymbolicLink()) throw new UpdateStop(2, `Symlinks are not allowed: ${relPath}.`);
    if (!st.isFile()) throw new UpdateStop(2, `Target is not a regular file: ${relPath}.`);
    mode = st.mode & 0o7777;
  } catch (error) {
    if (error instanceof UpdateStop) throw error;
    if (error.code === 'ENOENT') {
      if (!createParents) throw new UpdateStop(2, `Target is not a regular file: ${relPath}.`);
    } else {
      throw new UpdateStop(2, `Could not inspect ${relPath}: ${sanitizeOneLine(error.message)}.`);
    }
  }

  const tmpName = `.pdd-tmp-${process.pid}-${randomBytes(6).toString('hex')}`;
  const tmpFull = join(dirname(targetFull), tmpName);
  let fd;
  try {
    fd = openSync(tmpFull, fsConstants.O_CREAT | fsConstants.O_EXCL | fsConstants.O_WRONLY | O_NOFOLLOW, mode);
    const data = Buffer.from(text, 'utf8');
    let written = 0;
    while (written < data.length) {
      written += writeSync(fd, data, written, data.length - written);
    }
    closeSync(fd);
    fd = undefined;
    renameSync(tmpFull, targetFull);
  } catch (error) {
    if (fd !== undefined) {
      try { closeSync(fd); } catch {}
    }
    try { unlinkSync(tmpFull); } catch {}
    if (error instanceof UpdateStop) throw error;
    if (error.code === 'ELOOP') throw new UpdateStop(2, `Symlinks are not allowed: ${relPath}.`);
    throw new UpdateStop(2, `Could not write ${relPath}: ${sanitizeOneLine(error.message)}.`);
  }
}

function parseSyncRecordBytes(bytes, expectedModule, sidecarRel) {
  if (!bytes || bytes.includes(0)) throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
  let doc;
  try { doc = JSON.parse(new TextDecoder('utf-8').decode(bytes)); }
  catch { throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`); }
  if (!doc || typeof doc !== 'object' || Array.isArray(doc)) {
    throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
  }
  const allowed = new Set(['schema_version', 'module', 'prompt', 'module_sha256', 'prompt_sha256', 'prompts']);
  for (const key of Object.keys(doc)) {
    if (!allowed.has(key)) throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
  }
  if (doc.schema_version !== SYNC_SCHEMA_VERSION || doc.module !== expectedModule) {
    throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
  }
  if (typeof doc.prompt !== 'string' || !canonicalPath(doc.prompt) || !doc.prompt.endsWith('.prompt.md') || isBlockedSecretPath(doc.prompt)) {
    throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
  }
  if (!HEX64.test(doc.module_sha256 ?? '') || !HEX64.test(doc.prompt_sha256 ?? '')) {
    throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
  }
  let prompts = null;
  if (doc.prompts !== undefined) {
    if (!doc.prompts || typeof doc.prompts !== 'object' || Array.isArray(doc.prompts)) {
      throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
    }
    prompts = {};
    for (const [k, v] of Object.entries(doc.prompts)) {
      if (!canonicalPath(k) || !k.endsWith('.prompt.md') || isBlockedSecretPath(k) || !HEX64.test(v ?? '')) {
        throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
      }
      prompts[k] = v;
    }
  }
  return {
    schema_version: SYNC_SCHEMA_VERSION,
    module: doc.module,
    prompt: doc.prompt,
    module_sha256: doc.module_sha256,
    prompt_sha256: doc.prompt_sha256,
    ...(prompts ? { prompts } : {}),
  };
}

function recordOwners(record) {
  if (!record) return [];
  if (record.prompts) return unique([record.prompt, ...Object.keys(record.prompts)]).sort(cmpPath);
  return [record.prompt];
}

function recordPromptHash(record, owner) {
  if (!record) return null;
  if (record.prompts && Object.hasOwn(record.prompts, owner)) return record.prompts[owner];
  if (record.prompt === owner) return record.prompt_sha256;
  return null;
}

function readSyncRecord(root, modulePath, readBytes) {
  const sidecarRel = syncRecordPathForModule(modulePath);
  const res = readBytes(sidecarRel, MAX_SIDECAR_BYTES);
  if (res.status === 'missing') return null;
  if (res.status === 'symlink') throw new UpdateStop(2, `Symlinks are not allowed: ${sidecarRel}.`);
  if (res.status !== 'ok') throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
  return parseSyncRecordBytes(res.bytes, modulePath, sidecarRel);
}

function scanSyncRecords(root, readBytes) {
  const records = new Map();
  let cur = root;
  for (const seg of ['.pdd', 'sync']) {
    cur = join(cur, seg);
    let st;
    try { st = lstatSync(cur); }
    catch (error) {
      if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return records;
      throw new UpdateStop(2, `Could not inspect ${SYNC_DIR_REL}: ${sanitizeOneLine(error.message)}.`);
    }
    if (st.isSymbolicLink()) throw new UpdateStop(2, `Symlinks are not allowed: ${seg === '.pdd' ? '.pdd' : SYNC_DIR_REL}.`);
    if (!st.isDirectory()) throw new UpdateStop(2, `Path is not a directory: ${seg === '.pdd' ? '.pdd' : SYNC_DIR_REL}.`);
  }

  const walk = (absDir, relPrefix) => {
    let entries;
    try { entries = readdirSync(absDir); }
    catch (error) { throw new UpdateStop(2, `Could not read ${SYNC_DIR_REL}: ${sanitizeOneLine(error.message)}.`); }
    for (const name of entries.sort(cmpPath)) {
      if (name.startsWith('.pdd-tmp-')) continue;
      const absChild = join(absDir, name);
      const relInside = relPrefix ? `${relPrefix}/${name}` : name;
      const sidecarRel = `${SYNC_DIR_REL}/${relInside}`;
      let st;
      try { st = lstatSync(absChild); }
      catch (error) { throw new UpdateStop(2, `Could not inspect ${sidecarRel}: ${sanitizeOneLine(error.message)}.`); }
      if (st.isSymbolicLink()) throw new UpdateStop(2, `Symlinks are not allowed: ${sidecarRel}.`);
      if (st.isDirectory()) {
        walk(absChild, relInside);
      } else if (st.isFile() && name.endsWith('.json')) {
        const mod = relInside.slice(0, -'.json'.length);
        if (!canonicalPath(mod) || isBlockedSecretPath(mod) || isPddInternalPath(mod)) {
          throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
        }
        const res = readBytes(sidecarRel, MAX_SIDECAR_BYTES);
        if (res.status !== 'ok') throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
        records.set(mod, parseSyncRecordBytes(res.bytes, mod, sidecarRel));
      }
    }
  };
  walk(cur, '');
  return records;
}

function serializeSyncRecord({ modulePath, owners, promptHashes, moduleSha }) {
  const primary = owners[0];
  const doc = {
    schema_version: SYNC_SCHEMA_VERSION,
    module: modulePath,
    prompt: primary,
    module_sha256: moduleSha,
    prompt_sha256: promptHashes.get(primary),
  };
  if (owners.length > 1) {
    const prompts = {};
    for (const owner of [...owners].sort(cmpPath)) prompts[owner] = promptHashes.get(owner);
    doc.prompts = prompts;
  }
  return `${JSON.stringify(doc, null, 2)}\n`;
}

function pruneSyncRecord(root, modulePath) {
  const sidecarRel = syncRecordPathForModule(modulePath);
  const check = inspectRegularPath(root, sidecarRel);
  if (check.kind === 'missing') return { pruned: false, path: sidecarRel };
  if (check.kind === 'symlink') throw new UpdateStop(2, `Symlinks are not allowed: ${sidecarRel}.`);
  if (check.kind !== 'file') throw new UpdateStop(2, `Invalid sync record: ${sidecarRel}.`);
  try { unlinkSync(check.full); }
  catch (error) {
    if (error.code === 'ENOENT') return { pruned: false, path: sidecarRel };
    throw new UpdateStop(2, `Could not remove ${sidecarRel}: ${sanitizeOneLine(error.message)}.`);
  }
  const syncRoot = join(root, '.pdd', 'sync');
  let dir = dirname(check.full);
  while (dir.startsWith(syncRoot)) {
    try {
      const st = lstatSync(dir);
      if (st.isSymbolicLink() || !st.isDirectory()) break;
      if (readdirSync(dir).length > 0) break;
      rmdirSync(dir);
    } catch {
      break;
    }
    if (dir === syncRoot) break;
    dir = dirname(dir);
  }
  return { pruned: true, path: sidecarRel };
}

function validateBindingsFile(root, readBytes) {
  const res = readBytes('pdd-bindings.json', MAX_BINDINGS_BYTES);
  if (res.status === 'missing') return null;
  if (res.status === 'symlink') throw new UpdateStop(2, 'Symlinks are not allowed: pdd-bindings.json.');
  if (res.status !== 'ok' || res.bytes.includes(0)) {
    throw new UpdateStop(2, 'pdd-bindings.json is malformed or unreadable; fix it before running pdd update.');
  }
  let doc;
  try { doc = JSON.parse(new TextDecoder('utf-8').decode(res.bytes)); }
  catch { throw new UpdateStop(2, 'pdd-bindings.json is malformed or unreadable; fix it before running pdd update.'); }
  if (!doc || typeof doc !== 'object' || Array.isArray(doc) || doc.schema_version !== 'pdd.bindings.v1' || !Array.isArray(doc.modules)) {
    throw new UpdateStop(2, 'pdd-bindings.json is malformed or unreadable; fix it before running pdd update.');
  }
  return doc;
}

function defaultGitRoot(cwd) {
  try {
    const top = execFileSync('git', ['rev-parse', '--show-toplevel'], {
      cwd,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
    }).trim();
    return top ? realpathSync(top) : null;
  } catch {
    return null;
  }
}

function hasGitHead(root) {
  try {
    execFileSync('git', ['rev-parse', '--verify', 'HEAD'], { cwd: root, stdio: ['ignore', 'ignore', 'ignore'] });
    return true;
  } catch {
    return false;
  }
}

function parseNameStatusZ(buffer) {
  const raw = Buffer.isBuffer(buffer) ? buffer.toString('utf8') : String(buffer ?? '');
  if (!raw) return [];
  const tokens = raw.split('\0');
  if (tokens.length && tokens.at(-1) === '') tokens.pop();
  const entries = [];
  for (let i = 0; i < tokens.length;) {
    const code = tokens[i++];
    if (!code) continue;
    const letter = code[0];
    if (letter === 'R' || letter === 'C') {
      const oldPath = tokens[i++];
      const newPath = tokens[i++];
      if (newPath) entries.push({ path: newPath, status: letter, renamedFrom: letter === 'R' ? (oldPath ?? null) : null, deleted: false, untracked: false });
    } else {
      const path = tokens[i++];
      if (path) entries.push({ path, status: letter, renamedFrom: null, deleted: letter === 'D', untracked: false });
    }
  }
  return entries;
}

function parsePorcelainZ(buffer) {
  const raw = Buffer.isBuffer(buffer) ? buffer.toString('utf8') : String(buffer ?? '');
  if (!raw) return [];
  const tokens = raw.split('\0');
  if (tokens.length && tokens.at(-1) === '') tokens.pop();
  const entries = [];
  for (let i = 0; i < tokens.length;) {
    const rec = tokens[i++];
    if (rec.length < 4) continue;
    const x = rec[0], y = rec[1], path = rec.slice(3);
    let renamedFrom = null;
    if (x === 'R' || x === 'C' || y === 'R' || y === 'C') {
      renamedFrom = (x === 'R' || y === 'R') ? (tokens[i++] ?? null) : (tokens[i++], null);
    }
    const untracked = x === '?' && y === '?';
    const deleted = !untracked && (x === 'D' || y === 'D') && x !== 'A' && y !== 'A';
    const status = untracked ? 'A' : deleted ? 'D' : renamedFrom ? 'R' : (x === 'A' || y === 'A') ? 'A' : 'M';
    entries.push({ path, status, renamedFrom, deleted, untracked });
  }
  return entries;
}

const SAFE_GIT_DIFF_PREFIX = [
  '--literal-pathspecs',
  '-c', 'core.quotepath=false',
  '-c', 'diff.noprefix=false',
  '-c', 'diff.mnemonicPrefix=false',
];

function defaultGitRangeEntries(root, range) {
  try {
    const out = execFileSync('git', [...SAFE_GIT_DIFF_PREFIX, 'diff', '--name-status', '-z', '-M', '--no-ext-diff', range, '--'], {
      cwd: root,
      maxBuffer: 32 * 1024 * 1024,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    return parseNameStatusZ(out);
  } catch {
    throw new UpdateStop(2, `Git diff range unavailable: ${sanitizeOneLine(range)}.`);
  }
}

function defaultGitWorkingEntries(root) {
  const byPath = new Map();
  const addEntry = entry => {
    const prev = byPath.get(entry.path);
    if (!prev) { byPath.set(entry.path, entry); return; }
    byPath.set(entry.path, {
      ...prev,
      renamedFrom: prev.renamedFrom ?? entry.renamedFrom,
      deleted: prev.deleted && entry.deleted,
      untracked: prev.untracked || entry.untracked,
    });
  };
  if (hasGitHead(root)) {
    try {
      const diffOut = execFileSync('git', [...SAFE_GIT_DIFF_PREFIX, 'diff', '--name-status', '-z', '-M', '--no-ext-diff', 'HEAD', '--'], {
        cwd: root,
        maxBuffer: 32 * 1024 * 1024,
        stdio: ['ignore', 'pipe', 'pipe'],
      });
      for (const entry of parseNameStatusZ(diffOut)) addEntry(entry);
    } catch { /* fall through to status */ }
  }
  let statusOut;
  try {
    statusOut = execFileSync('git', ['--literal-pathspecs', '-c', 'core.quotepath=false', 'status', '--porcelain=v1', '-z', '-uall'], {
      cwd: root,
      maxBuffer: 32 * 1024 * 1024,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
  } catch (error) {
    throw new UpdateStop(2, `Git status failed: ${sanitizeOneLine(error.message)}.`);
  }
  for (const entry of parsePorcelainZ(statusOut)) addEntry(entry);
  return [...byPath.values()].sort((a, b) => cmpPath(a.path, b.path));
}

function defaultGitUntrackedSet(root, paths) {
  const set = new Set();
  if (!paths.length) return set;
  try {
    const out = execFileSync('git', ['--literal-pathspecs', '-c', 'core.quotepath=false', 'status', '--porcelain=v1', '-z', '-uall', '--', ...paths], {
      cwd: root,
      maxBuffer: 32 * 1024 * 1024,
      stdio: ['ignore', 'pipe', 'ignore'],
    });
    for (const entry of parsePorcelainZ(out)) {
      if (entry.untracked) set.add(entry.path);
    }
  } catch { /* treat as tracked if status probe fails */ }
  return set;
}

function defaultGitUnifiedDiff(root, range, paths) {
  if (!paths.length) return '';
  const args = [
    ...SAFE_GIT_DIFF_PREFIX,
    'diff',
    '--src-prefix=a/',
    '--dst-prefix=b/',
    '--no-color',
    '--no-ext-diff',
    '-M',
    '-U0',
  ];
  if (range) args.push(range);
  else if (hasGitHead(root)) args.push('HEAD');
  else return '';
  args.push('--', ...paths);
  try {
    return execFileSync('git', args, {
      cwd: root,
      encoding: 'utf8',
      maxBuffer: 32 * 1024 * 1024,
      stdio: ['ignore', 'pipe', 'ignore'],
    });
  } catch {
    return '';
  }
}

function splitDiffByFile(fullDiff, knownPaths = new Set()) {
  const byPath = new Map();
  if (!fullDiff) return byPath;
  const chunks = fullDiff.split(/^diff --git /m);
  for (const chunk of chunks) {
    if (!chunk) continue;
    const nl = chunk.indexOf('\n');
    const headerLine = (nl >= 0 ? chunk.slice(0, nl) : chunk).replace(/\r$/, '');
    const plusMatch = /^\+\+\+ (?:b\/([^\r\n\t]+)|\/dev\/null)\t?\r?$/m.exec(chunk);
    const renameToMatch = /^rename to ([^\r\n]+)\r?$/m.exec(chunk);
    const minusMatch = /^--- (?:a\/([^\r\n\t]+)|\/dev\/null)\t?\r?$/m.exec(chunk);
    let targetPath = (plusMatch && plusMatch[1]) || (renameToMatch && renameToMatch[1]) || (minusMatch && minusMatch[1]) || null;
    if (!targetPath) {
      for (const candidate of knownPaths) {
        if (headerLine.endsWith(` b/${candidate}`)) { targetPath = candidate; break; }
      }
      if (!targetPath) {
        const idx = headerLine.lastIndexOf(' b/');
        if (idx >= 0) targetPath = headerLine.slice(idx + 3);
      }
    }
    if (targetPath) byPath.set(targetPath, `diff --git ${chunk}`);
  }
  return byPath;
}

const SYMBOL_PATTERNS = [
  /^\s*export\s+(?:default\s+)?(?:async\s+)?function\*?\s+([A-Za-z_$][\w$]*)/,
  /^\s*export\s+(?:default\s+)?(?:const|let|var|class|interface|type|enum)\s+([A-Za-z_$][\w$]*)/,
  /^(?:async\s+)?function\*?\s+([A-Za-z_$][\w$]*)\s*\(/,
  /^(?:async\s+)?def\s+([A-Za-z_]\w*)\s*\(/,
  /^class\s+([A-Za-z_]\w*)\b/,
  /^func\s+(?:\([^)]*\)\s*)?([A-Za-z_]\w*)\s*\(/,
  /^\s*pub(?:\([^)]*\))?\s+(?:async\s+)?(?:fn|struct|enum|trait|type|const)\s+([A-Za-z_]\w*)\b/,
];

function matchSymbol(codeLine) {
  for (const pattern of SYMBOL_PATTERNS) {
    const match = pattern.exec(codeLine);
    if (match) return match[1];
  }
  return null;
}

export function extractDiffSummary(diffText) {
  let added = 0, removed = 0;
  const addedSymbols = new Set(), removedSymbols = new Set();
  if (typeof diffText === 'string' && diffText) {
    for (const line of diffText.split(/\r?\n/)) {
      if (line.startsWith('+++ ') || line.startsWith('--- ')) continue;
      if (line.startsWith('+')) {
        added++;
        const sym = matchSymbol(line.slice(1));
        if (sym) addedSymbols.add(sym);
      } else if (line.startsWith('-')) {
        removed++;
        const sym = matchSymbol(line.slice(1));
        if (sym) removedSymbols.add(sym);
      }
    }
  }
  const allSymbols = unique([...addedSymbols, ...removedSymbols]).sort(cmpPath);
  const changed_symbols = allSymbols.map(symbol => ({
    kind: addedSymbols.has(symbol) && removedSymbols.has(symbol) ? 'updated' : addedSymbols.has(symbol) ? 'added' : 'removed',
    symbol,
  }));
  return { added, removed, changed_symbols };
}

function summarizeWholeFileAsAdded(text) {
  if (!text) return { added: 0, removed: 0, changed_symbols: [] };
  const synthetic = text.split(/\r?\n/).filter((line, idx, arr) => idx < arr.length - 1 || line.length > 0).map(line => `+${line}`).join('\n');
  return extractDiffSummary(synthetic);
}

function aggregatePromptStatus(statuses) {
  const set = new Set(statuses);
  if (set.size === 0) return 'current';
  if (set.has('both-drifted') || (set.has('prompt-stale') && set.has('code-drifted'))) return 'both-drifted';
  if (set.has('code-drifted')) return 'code-drifted';
  if (set.has('prompt-stale')) return 'prompt-stale';
  if (set.has('unpinned')) return 'unpinned';
  if (set.has('unowned')) return 'unowned';
  if (set.has('deleted')) return 'deleted';
  return 'current';
}

function buildInstructions(promptPath, status, activePaths, deletedPaths, diffStats, driftedStale, range) {
  const activeList = activePaths.join(', ');
  const deletedList = deletedPaths.join(', ');
  const allList = [...activePaths, ...deletedPaths].join(', ');
  const statsStr = `+${diffStats.added}/-${diffStats.removed}`;
  const writeCmd = activePaths.length > 0 && !driftedStale
    ? `pdd update --write ${activePaths.map(shellArg).join(' ')}`
    : range
      ? `pdd update --from ${shellArg(range)} --write`
      : 'pdd update --write';

  switch (status) {
    case 'current':
      return ['In sync; no action needed.'];
    case 'unpinned':
      return [
        `Review diff in ${activeList || allList} (${statsStr}) and update ${promptPath} if behavior or domain rules changed.`,
        `Run \`${writeCmd}\` to record per-module derived hashes.`,
      ];
    case 'code-drifted':
      return [
        `Code changed since last pin in ${activeList || allList} (${statsStr}); update ${promptPath} to match the reviewed diff.`,
        `Run \`${writeCmd}\` after syncing ${promptPath}.`,
      ];
    case 'prompt-stale':
      return [
        `${promptPath} changed; verify ${activeList || allList} implements the updated contract.`,
        `Run \`${writeCmd}\` to refresh derived hashes.`,
      ];
    case 'both-drifted':
      return [
        `Both ${promptPath} and ${activeList || allList} (${statsStr}) changed; reconcile contract prose and code.`,
        `Run \`${writeCmd}\` once reconciled.`,
      ];
    case 'unowned':
      return driftedStale
        ? [`Previously pinned file(s) lost ownership (${activeList || allList}); run \`${writeCmd}\` to prune stale sync records.`]
        : [`Previously pinned file(s) lost ownership (${activeList || allList}); no stale sync records remain.`];
    case 'deleted':
      return driftedStale
        ? [`Owned file(s) deleted (${deletedList || allList}); update ${promptPath} and run \`${writeCmd}\` to prune stale sync records.`]
        : [`Owned file(s) deleted (${deletedList || allList}); no stale sync records remain.`];
    default:
      return [];
  }
}

function evaluateState({ ownedPairs, promptTextMap, codeTextMap, syncRecordMap, diffByPath, updated, range }) {
  const promptHashCache = new Map();
  for (const [promptPath, promptText] of promptTextMap.entries()) {
    promptHashCache.set(promptPath, promptHeaderHash(promptText));
  }

  const modules = [];
  const drifted = [];
  const byPrompt = new Map();

  for (const pair of ownedPairs) {
    const { entry, ownerRow, owner } = pair;
    const promptText = promptTextMap.get(owner) ?? null;
    const prompt_sha256 = promptHashCache.get(owner) ?? null;
    const record = syncRecordMap.get(entry.path) ?? null;
    const recPromptSha = recordPromptHash(record, owner);
    const hasPinForOwner = record !== null && recPromptSha !== null;
    const diffSummary = diffByPath.get(entry.path) ?? { added: 0, removed: 0, changed_symbols: [] };

    let status, module_sha256 = null, recorded_prompt_sha256 = null, recorded_module_sha256 = hasPinForOwner ? record.module_sha256 : (record?.module_sha256 ?? null), header_state = null;
    let isDrifted = false;

    if (entry.deleted) {
      status = 'deleted';
      recorded_prompt_sha256 = recPromptSha;
      isDrifted = record !== null;
    } else if (entry.orphanedSidecar) {
      status = 'unowned';
      recorded_prompt_sha256 = recPromptSha;
      isDrifted = record !== null;
    } else {
      const codeText = codeTextMap.get(entry.path);
      module_sha256 = moduleContentHash(codeText);
      const headerRow = headerEntries(codeText).find(h => h.prompt === owner) ?? null;
      const hashState = headerRow ? headerHashState(headerRow.sha256, promptText) : null;
      header_state = hashState ? hashState.state : null;
      recorded_prompt_sha256 = headerRow?.sha256 ?? recPromptSha ?? null;

      const headerStale = Boolean(headerRow?.sha256 && hashState?.state === 'stale');
      const pinPromptStale = Boolean(hasPinForOwner && prompt_sha256 !== null && recPromptSha !== prompt_sha256);
      const promptDrifted = headerStale || pinPromptStale;
      const codeDrifted = hasPinForOwner && record.module_sha256 !== module_sha256;

      if (promptDrifted && codeDrifted) status = 'both-drifted';
      else if (promptDrifted) status = 'prompt-stale';
      else if (codeDrifted) status = 'code-drifted';
      else if (hasPinForOwner) status = 'current';
      else status = 'unpinned';

      isDrifted = status !== 'current';
    }

    const row = {
      path: entry.path,
      owner,
      owners: ownerRow.owners,
      source: ownerRow.source,
      certain: ownerRow.certain,
      status,
      prompt_sha256,
      recorded_prompt_sha256,
      module_sha256,
      recorded_module_sha256,
      header_state,
      sync_record: syncRecordPathForModule(entry.path),
      diff_stats: { added: diffSummary.added, removed: diffSummary.removed },
      changed_symbols: diffSummary.changed_symbols,
      deleted: entry.deleted,
      renamed_from: entry.renamedFrom ?? null,
      note: ownerRow.note ?? '',
    };
    modules.push(row);
    if (isDrifted) drifted.push({ path: entry.path, owner, status });

    if (!byPrompt.has(owner)) byPrompt.set(owner, []);
    byPrompt.get(owner).push({ row, isDrifted, orphaned: Boolean(entry.orphanedSidecar) });
  }

  const prompts = [...byPrompt.entries()]
    .sort(([a], [b]) => cmpPath(a, b))
    .map(([prompt, items]) => {
      items.sort((a, b) => cmpPath(a.row.path, b.row.path));
      const statuses = items.map(item => item.row.status);
      const status = aggregatePromptStatus(statuses);
      const added = items.reduce((sum, item) => sum + item.row.diff_stats.added, 0);
      const removed = items.reduce((sum, item) => sum + item.row.diff_stats.removed, 0);
      const symMap = new Map();
      for (const item of items) {
        for (const sym of item.row.changed_symbols) {
          const prev = symMap.get(sym.symbol);
          if (!prev) symMap.set(sym.symbol, sym.kind);
          else if (prev !== sym.kind) symMap.set(sym.symbol, 'updated');
        }
      }
      const changed_symbols = [...symMap.entries()].sort(([a], [b]) => cmpPath(a, b)).map(([symbol, kind]) => ({ kind, symbol }));
      const modulePaths = items.map(item => item.row.path);
      const activePaths = items.filter(item => !item.row.deleted).map(item => item.row.path);
      const deletedPaths = items.filter(item => item.row.deleted).map(item => item.row.path);
      const driftedStale = items.some(item => (item.row.deleted || item.orphaned) && item.isDrifted);
      return {
        prompt,
        status,
        prompt_sha256: promptHashCache.get(prompt) ?? null,
        owner_certain: items.every(item => item.row.certain),
        modules: modulePaths,
        diff_stats: { added, removed },
        changed_symbols,
        instructions: buildInstructions(prompt, status, activePaths, deletedPaths, { added, removed }, driftedStale, range),
      };
    });

  modules.sort((a, b) => cmpPath(a.path, b.path) || cmpPath(a.owner, b.owner));
  drifted.sort((a, b) => cmpPath(a.path, b.path) || cmpPath(a.owner, b.owner));
  return { prompts, modules, drifted, updated };
}

function isEligiblePromptScanCodePath(path) {
  if (!canonicalPath(path) || path.endsWith('.prompt.md') || isBlockedSecretPath(path) || isSyncSidecarPath(path)) return false;
  if (isTestOwnedPath(path) || NON_CANDIDATE_DIR.test(path) || DOTFILE_SEG.test(path) || NON_CANDIDATE_EXT.test(path)) return false;
  return true;
}

export function analyzeUpdate({ cwd = process.cwd(), files = [], from, check = false, write = false } = {}, ports = {}) {
  try {
    if (check && write) throw new UpdateStop(2, 'Cannot combine --check and --write.');
    if (files.length > 0 && from !== undefined) throw new UpdateStop(2, 'Specify either file paths or --from RANGE, not both.');

    const normalizedRange = from !== undefined ? parseFromRange(from) : null;
    const root = ports.gitRoot ? ports.gitRoot(cwd) : defaultGitRoot(cwd);
    if (!root) throw new UpdateStop(2, 'pdd update works inside a Git repository.');

    const mode = write ? 'write' : check ? 'check' : 'plan';
    const scopeKind = files.length > 0 ? 'files' : normalizedRange ? 'from' : 'working-tree';
    const readBytes = ports.readBytes ?? ((path, limit) => readRegularBytes(root, path, limit));
    const probeBytes = ports.probeBytes ?? ((path, limit) => probeRegularBytes(root, path, limit));
    const listFiles = () => (ports.files ? ports.files() : gitFiles(root)).filter(p => !isBlockedSecretPath(p));

    // Fail closed if pdd-bindings.json exists and is malformed, unreadable, or a symlink.
    const bindingsDoc = validateBindingsFile(root, readBytes);

    const codeBytesMap = new Map();
    const unownedMap = new Map();
    const touchedMap = new Map();

    if (scopeKind === 'files') {
      let realCwd;
      try { realCwd = ports.realCwd ? ports.realCwd(cwd) : realpathSync(cwd); }
      catch { realCwd = root; }
      const resolvedPaths = [];
      for (const typed of files) {
        if (typeof typed !== 'string' || !typed.trim()) throw new UpdateStop(2, 'Invalid empty file path.');
        if (typed.startsWith('-')) throw new UpdateStop(2, `Invalid file path (leading '-' is not allowed): ${sanitizeOneLine(typed)}.`);
        if (/[\x00-\x1f\x7f\\]/.test(typed)) throw new UpdateStop(2, `Invalid file path: ${sanitizeOneLine(typed)}.`);
        if (typed.split('/').includes('..')) throw new UpdateStop(2, `Path traversal is not allowed: ${sanitizeOneLine(typed)}.`);
        const rel = relative(root, resolve(realCwd, typed)).split(sep).join('/');
        if (!canonicalPath(rel)) throw new UpdateStop(2, `${sanitizeOneLine(typed)} is not a file path inside this repository.`);
        if (isBlockedSecretPath(rel)) throw new UpdateStop(2, `Secret-looking path is not allowed: ${rel}.`);
        const read = readBytes(rel, MAX_FILE_BYTES);
        if (read.status === 'missing') throw new UpdateStop(2, `Missing file: ${rel}.`);
        if (read.status === 'symlink') throw new UpdateStop(2, `Symlinks are not allowed: ${rel}.`);
        if (read.status === 'non-file') throw new UpdateStop(2, `Not a regular file: ${rel}.`);
        if (read.status === 'too-large') throw new UpdateStop(2, `File exceeds 10 MiB limit: ${rel}.`);
        if (read.bytes.includes(0)) throw new UpdateStop(2, `Binary file is not supported: ${rel}.`);
        codeBytesMap.set(rel, read.bytes);
        resolvedPaths.push(rel);
      }
      const untrackedSet = ports.gitUntrackedSet ? ports.gitUntrackedSet(root, resolvedPaths) : defaultGitUntrackedSet(root, resolvedPaths);
      for (const rel of resolvedPaths) {
        const isUntracked = untrackedSet.has(rel);
        touchedMap.set(rel, { path: rel, status: isUntracked ? 'A' : 'M', renamedFrom: null, deleted: false, untracked: isUntracked });
      }
    } else {
      const rawEntries = scopeKind === 'from'
        ? (ports.gitRangeEntries ? ports.gitRangeEntries(root, normalizedRange) : defaultGitRangeEntries(root, normalizedRange))
        : (ports.gitWorkingEntries ? ports.gitWorkingEntries(root) : defaultGitWorkingEntries(root));
      for (const raw of rawEntries) {
        if (isSyncSidecarPath(raw.path)) continue;
        if (!canonicalPath(raw.path)) throw new UpdateStop(2, `Invalid touched path: ${sanitizeOneLine(raw.path)}.`);
        if (isBlockedSecretPath(raw.path)) throw new UpdateStop(2, `Secret-looking path is not allowed: ${raw.path}.`);
        if (raw.renamedFrom) {
          if (!canonicalPath(raw.renamedFrom)) throw new UpdateStop(2, `Invalid renamed path: ${sanitizeOneLine(raw.renamedFrom)}.`);
          if (isBlockedSecretPath(raw.renamedFrom)) throw new UpdateStop(2, `Secret-looking path is not allowed: ${raw.renamedFrom}.`);
        }
        if (raw.deleted) {
          touchedMap.set(raw.path, { ...raw, deleted: true });
          continue;
        }
        const probe = probeBytes(raw.path, BINARY_PROBE_BYTES);
        if (probe.status === 'missing') {
          touchedMap.set(raw.path, { ...raw, deleted: true });
          continue;
        }
        if (probe.status === 'symlink') throw new UpdateStop(2, `Symlinks are not allowed: ${raw.path}.`);
        if (probe.status === 'non-file') {
          unownedMap.set(raw.path, { path: raw.path, reason: 'non-regular entry (skipped)' });
          continue;
        }
        touchedMap.set(raw.path, { ...raw, deleted: false });
      }
    }

    const touchedEntries = [...touchedMap.values()].sort((a, b) => cmpPath(a.path, b.path));
    const scope = {
      kind: scopeKind,
      range: normalizedRange,
      files: touchedEntries.map(entry => entry.path),
    };

    if (!touchedEntries.length && !unownedMap.size) {
      const report = {
        schema_version: 'pdd.update-sync.v1',
        ok: true,
        mode,
        scope,
        prompts: [],
        modules: [],
        unowned: [],
        drifted: [],
        updated: [],
      };
      return { ok: true, exitCode: 0, error: null, report, root };
    }

    const touchedPrompts = touchedEntries.filter(entry => entry.path.endsWith('.prompt.md'));
    const touchedNonPrompts = touchedEntries.filter(entry => !entry.path.endsWith('.prompt.md'));
    for (const entry of touchedPrompts) {
      if (!entry.deleted && isTestPromptPath(entry.path)) {
        throw new UpdateStop(1, `Error: misplaced test prompt: ${entry.path}. Prompts own production modules, not test files.`);
      }
    }

    // Secret-safe memoized owner ports: never list or open secret files, and avoid duplicate prompt reads across findOwners calls.
    const safeVisible = listFiles();
    const ownerReadCache = new Map();
    const safeReadForOwner = (path, limit) => {
      if (!canonicalPath(path) || isBlockedSecretPath(path)) return null;
      const cacheKey = `${path}\0${limit}`;
      if (ownerReadCache.has(cacheKey)) {
        const cached = ownerReadCache.get(cacheKey);
        if (cached.error) throw cached.error;
        return cached.value;
      }
      try {
        let value;
        if (ports.read) {
          value = ports.read(path, limit);
        } else {
          const res = probeRegularBytes(root, path, limit);
          if (res.status === 'missing') value = null;
          else if (res.status !== 'ok') throw new Error(res.status);
          else value = res.bytes;
        }
        ownerReadCache.set(cacheKey, { value, error: null });
        return value;
      } catch (error) {
        ownerReadCache.set(cacheKey, { value: null, error });
        throw error;
      }
    };
    const ownerPorts = { files: () => safeVisible, read: safeReadForOwner };

    const nonPromptMap = new Map(touchedNonPrompts.map(entry => [entry.path, entry]));
    const activeTouchedPromptSet = new Set(touchedPrompts.filter(e => !e.deleted).map(e => e.path));
    const touchedPromptTargets = new Set([
      ...touchedPrompts.map(e => e.path),
      ...touchedPrompts.filter(e => e.renamedFrom?.endsWith('.prompt.md')).map(e => e.renamedFrom),
    ]);
    const promptTextMap = new Map();
    const syncRecordMap = new Map();

    // Load active touched prompt texts once (reused for claims and final evaluation).
    for (const promptPath of [...activeTouchedPromptSet].sort(cmpPath)) {
      let bytes = codeBytesMap.get(promptPath);
      if (!bytes) {
        const read = readBytes(promptPath, MAX_FILE_BYTES);
        if (read.status === 'symlink') throw new UpdateStop(2, `Symlinks are not allowed: ${promptPath}.`);
        if (read.status === 'too-large') throw new UpdateStop(1, `Owning prompt exceeds 10 MiB limit: ${promptPath}.`);
        if (read.status !== 'ok') throw new UpdateStop(1, `Owning prompt is missing or unreadable: ${promptPath}.`);
        if (read.bytes.includes(0)) throw new UpdateStop(2, `Binary file is not supported: ${promptPath}.`);
        bytes = read.bytes;
      }
      promptTextMap.set(promptPath, new TextDecoder('utf-8', { ignoreBOM: true }).decode(bytes));
    }

    // When any prompt is touched, deleted, or renamed, gather its owned modules from bindings, prose claims, .pdd/sync sidecars, and eligible non-secret code files.
    if (touchedPromptTargets.size > 0) {
      const allSyncRecords = scanSyncRecords(root, readBytes);
      const candidateSet = new Set();

      if (bindingsDoc) {
        for (const item of bindingsDoc.modules) {
          if (item && typeof item === 'object' && typeof item.module === 'string' && typeof item.prompt === 'string') {
            if (touchedPromptTargets.has(item.prompt) && canonicalPath(item.module) && !isBlockedSecretPath(item.module)) {
              candidateSet.add(item.module);
            }
          }
        }
      }
      for (const [promptPath, text] of promptTextMap.entries()) {
        for (const claimed of promptClaims(promptPath, text)) {
          if (canonicalPath(claimed) && !isBlockedSecretPath(claimed) && !claimed.endsWith('.prompt.md')) {
            candidateSet.add(claimed);
          }
        }
      }
      for (const [modPath, record] of allSyncRecords.entries()) {
        if (recordOwners(record).some(owner => touchedPromptTargets.has(owner))) {
          syncRecordMap.set(modPath, record);
          candidateSet.add(modPath);
        }
      }
      for (const p of safeVisible) {
        if (isEligiblePromptScanCodePath(p)) candidateSet.add(p);
      }

      const candidateList = [...candidateSet].sort(cmpPath);
      if (candidateList.length) {
        const allOwned = findOwners({ root, paths: candidateList }, ownerPorts);
        for (const row of allOwned.files) {
          const rec = syncRecordMap.get(row.path) ?? null;
          const ownedByTouched = row.owners.some(owner => touchedPromptTargets.has(owner))
            || (rec !== null && recordOwners(rec).some(owner => touchedPromptTargets.has(owner)));
          if (ownedByTouched && !nonPromptMap.has(row.path)) {
            const probe = probeBytes(row.path, BINARY_PROBE_BYTES);
            if (probe.status === 'symlink') throw new UpdateStop(2, `Symlinks are not allowed: ${row.path}.`);
            if (probe.status === 'non-file') continue;
            nonPromptMap.set(row.path, {
              path: row.path,
              status: probe.status === 'missing' ? 'D' : 'M',
              renamedFrom: null,
              deleted: probe.status === 'missing',
              untracked: false,
            });
          }
        }
      }
    }

    // For every renamed entry, also check if renamedFrom has a lingering .pdd/sync sidecar so renames to unowned/other-prompt/pinned targets never escape --check.
    const renamedFromEntries = [];
    for (const entry of nonPromptMap.values()) {
      if (entry.renamedFrom && !nonPromptMap.has(entry.renamedFrom) && !entry.renamedFrom.endsWith('.prompt.md') && !isPddInternalPath(entry.renamedFrom)) {
        const oldRec = syncRecordMap.get(entry.renamedFrom) ?? readSyncRecord(root, entry.renamedFrom, readBytes);
        if (oldRec) {
          syncRecordMap.set(entry.renamedFrom, oldRec);
          renamedFromEntries.push({
            path: entry.renamedFrom,
            status: 'D',
            renamedFrom: null,
            deleted: true,
            untracked: false,
            renamedTo: entry.path,
          });
        }
      }
    }
    for (const oldEntry of renamedFromEntries) nonPromptMap.set(oldEntry.path, oldEntry);

    const candidateEntries = [...nonPromptMap.values()].sort((a, b) => cmpPath(a.path, b.path));
    const ownerLookup = candidateEntries.length
      ? findOwners({ root, paths: candidateEntries.map(e => e.path) }, ownerPorts)
      : { files: [] };
    const ownerRowByPath = new Map(ownerLookup.files.map(row => [row.path, row]));

    // Load per-module sidecars for every candidate entry; for deleted files with a sidecar, ALWAYS union recorded sidecar owners into ownerRow.
    for (const entry of candidateEntries) {
      if (isPddInternalPath(entry.path)) continue;
      if (!syncRecordMap.has(entry.path)) {
        const rec = readSyncRecord(root, entry.path, readBytes);
        if (rec) syncRecordMap.set(entry.path, rec);
      }
      const existingOwner = ownerRowByPath.get(entry.path);
      if (existingOwner?.note?.includes('pdd-bindings.json could not be read')) {
        throw new UpdateStop(2, 'pdd-bindings.json is malformed or unreadable; fix it before running pdd update.');
      }
      const rec = syncRecordMap.get(entry.path) ?? null;
      if (entry.deleted && rec) {
        const recOwners = recordOwners(rec);
        if (!existingOwner?.owners?.length) {
          ownerRowByPath.set(entry.path, {
            path: entry.path,
            owner: recOwners[0] ?? null,
            owners: recOwners,
            source: 'sync-record',
            certain: true,
            note: '',
            headers: [],
          });
        } else {
          const mergedOwners = unique([...existingOwner.owners, ...recOwners]);
          ownerRowByPath.set(entry.path, {
            ...existingOwner,
            owner: mergedOwners[0] ?? null,
            owners: mergedOwners,
          });
        }
      }
    }

    const ownedPairs = [];
    const neededPrompts = new Set();
    const activeNeededPrompts = new Set();
    const codeTextMap = new Map();

    for (const entry of candidateEntries) {
      const ownerRow = ownerRowByPath.get(entry.path) ?? { path: entry.path, owner: null, owners: [], source: null, certain: true, note: '', headers: [] };
      if (!ownerRow.owners.length) {
        // Previously pinned file that lost all current owners in place: surface lingering sidecar as drifted and prune on --write.
        const staleRec = !isPddInternalPath(entry.path) ? (syncRecordMap.get(entry.path) ?? null) : null;
        if (!entry.deleted && staleRec) {
          const staleOwners = recordOwners(staleRec);
          for (const owner of staleOwners) {
            if (isBlockedSecretPath(owner)) throw new UpdateStop(2, `Secret-looking path is not allowed: ${owner}.`);
          }
          syncRecordPathForModule(entry.path);
          const orphanOwnerRow = {
            path: entry.path,
            owner: staleOwners[0] ?? null,
            owners: staleOwners,
            source: 'sync-record',
            certain: true,
            note: 'no longer owned; stale sync record remains',
            headers: [],
          };
          const orphanEntry = { ...entry, orphanedSidecar: true };
          for (const owner of staleOwners) {
            neededPrompts.add(owner);
            ownedPairs.push({ entry: orphanEntry, ownerRow: orphanOwnerRow, owner });
          }
          continue;
        }
        if (!entry.deleted) {
          const probe = codeBytesMap.has(entry.path)
            ? { status: 'ok', bytes: codeBytesMap.get(entry.path) }
            : probeBytes(entry.path, BINARY_PROBE_BYTES);
          if (probe.status === 'ok' && probe.bytes.includes(0)) {
            unownedMap.set(entry.path, { path: entry.path, reason: 'binary file (skipped)' });
            continue;
          }
        }
        unownedMap.set(entry.path, { path: entry.path, reason: 'no owning prompt' });
        continue;
      }
      for (const owner of ownerRow.owners) {
        if (isBlockedSecretPath(owner)) {
          throw new UpdateStop(2, `Secret-looking path is not allowed: ${owner}.`);
        }
      }
      const misplaced = ownerRow.owners.find(isTestPromptPath);
      if (misplaced) {
        throw new UpdateStop(1, `Error: misplaced test prompt: ${entry.path} is claimed by ${misplaced}. Prompts own production modules, not test files.`);
      }
      // Pre-validate sidecar destination path for every owned module BEFORE any write phase executes (0 writes on exit 2).
      syncRecordPathForModule(entry.path);
      if (!entry.deleted) {
        let bytes = codeBytesMap.get(entry.path);
        if (!bytes) {
          const read = readBytes(entry.path, MAX_FILE_BYTES);
          if (read.status === 'symlink') throw new UpdateStop(2, `Symlinks are not allowed: ${entry.path}.`);
          if (read.status === 'too-large') throw new UpdateStop(2, `File exceeds 10 MiB limit: ${entry.path}.`);
          if (read.status !== 'ok') throw new UpdateStop(2, `Cannot read file: ${entry.path}.`);
          bytes = read.bytes;
          codeBytesMap.set(entry.path, bytes);
        }
        if (bytes.includes(0)) throw new UpdateStop(2, `Binary file is not supported: ${entry.path}.`);
        codeTextMap.set(entry.path, new TextDecoder('utf-8', { ignoreBOM: true }).decode(bytes));
      }
      for (const owner of ownerRow.owners) {
        neededPrompts.add(owner);
        if (!entry.deleted) activeNeededPrompts.add(owner);
        ownedPairs.push({ entry, ownerRow, owner });
      }
    }

    for (const promptPath of [...neededPrompts].sort(cmpPath)) {
      if (promptTextMap.has(promptPath)) continue;
      if (!canonicalPath(promptPath)) throw new UpdateStop(1, `Owning prompt path is invalid: ${sanitizeOneLine(promptPath)}.`);
      if (isBlockedSecretPath(promptPath)) throw new UpdateStop(2, `Secret-looking path is not allowed: ${promptPath}.`);
      const read = readBytes(promptPath, MAX_FILE_BYTES);
      if (read.status === 'symlink') throw new UpdateStop(2, `Symlinks are not allowed: ${promptPath}.`);
      if (read.status === 'too-large') throw new UpdateStop(1, `Owning prompt exceeds 10 MiB limit: ${promptPath}.`);
      if (read.status !== 'ok') {
        if (activeNeededPrompts.has(promptPath)) {
          throw new UpdateStop(1, `Owning prompt is missing or unreadable: ${promptPath}.`);
        }
        // Prompt was deleted together with its owned module(s) or orphaned sidecar(s); allow --check to report stale sidecars and --write to prune them.
        continue;
      }
      if (read.bytes.includes(0)) throw new UpdateStop(2, `Binary file is not supported: ${promptPath}.`);
      promptTextMap.set(promptPath, new TextDecoder('utf-8', { ignoreBOM: true }).decode(read.bytes));
    }

    const diffPathspecs = unique(ownedPairs.flatMap(pair => [pair.entry.path, ...(pair.entry.renamedFrom ? [pair.entry.renamedFrom] : [])])).sort(cmpPath);
    const ownedPathSet = new Set(ownedPairs.map(pair => pair.entry.path));
    const fullDiff = diffPathspecs.length
      ? (ports.gitUnifiedDiff ? ports.gitUnifiedDiff(root, normalizedRange, diffPathspecs) : defaultGitUnifiedDiff(root, normalizedRange, diffPathspecs))
      : '';
    const diffChunks = splitDiffByFile(fullDiff, ownedPathSet);
    const diffByPath = new Map();
    for (const pair of ownedPairs) {
      if (diffByPath.has(pair.entry.path)) continue;
      const chunk = diffChunks.get(pair.entry.path);
      if (chunk) {
        diffByPath.set(pair.entry.path, extractDiffSummary(chunk));
      } else if (!pair.entry.deleted && !pair.entry.orphanedSidecar && (pair.entry.untracked || pair.entry.status === 'A')) {
        diffByPath.set(pair.entry.path, summarizeWholeFileAsAdded(codeTextMap.get(pair.entry.path) ?? ''));
      } else {
        diffByPath.set(pair.entry.path, { added: 0, removed: 0, changed_symbols: [] });
      }
    }

    const updated = [];
    if (write) {
      const writeUtf8 = ports.writeUtf8 ?? ((path, text, opts) => writeRegularAtomicUtf8(root, path, text, opts));
      const pruneSidecar = ports.pruneSidecar ?? (modPath => pruneSyncRecord(root, modPath));

      const promptHashMap = new Map();
      for (const [promptPath, text] of promptTextMap.entries()) promptHashMap.set(promptPath, promptHeaderHash(text));

      const activeOwnersByCode = new Map();
      const staleSidecarModules = new Set();
      for (const pair of ownedPairs) {
        if (pair.entry.deleted || pair.entry.orphanedSidecar) {
          staleSidecarModules.add(pair.entry.path);
          continue;
        }
        if (pair.entry.renamedFrom && pair.entry.renamedFrom !== pair.entry.path && !isPddInternalPath(pair.entry.renamedFrom)) {
          staleSidecarModules.add(pair.entry.renamedFrom);
        }
        if (!activeOwnersByCode.has(pair.entry.path)) activeOwnersByCode.set(pair.entry.path, []);
        activeOwnersByCode.get(pair.entry.path).push(pair.owner);
      }

      // 1. Prune stale sidecars for deleted, renamed-away, or unowned-in-place modules (never touching .prompt.md).
      for (const oldPath of [...staleSidecarModules].sort(cmpPath)) {
        if (activeOwnersByCode.has(oldPath)) continue;
        const pruned = pruneSidecar(oldPath);
        if (pruned.pruned) {
          syncRecordMap.delete(oldPath);
          updated.push({ path: pruned.path, kind: 'sync-prune', module: oldPath });
        }
      }

      // 2. Write disjoint per-module sidecars in .pdd/sync/<module>.json and refresh existing code headers atomically.
      for (const codePath of [...activeOwnersByCode.keys()].sort(cmpPath)) {
        const owners = unique(activeOwnersByCode.get(codePath));
        const originalCode = codeTextMap.get(codePath);
        let currentCode = originalCode;
        const headerUpdates = [];
        for (const owner of owners) {
          const expected = promptHashMap.get(owner);
          const { content: nextCode, changed } = updateHeaderHash(currentCode, owner, expected);
          if (changed) {
            currentCode = nextCode;
            headerUpdates.push({ path: codePath, kind: 'code-header', prompt: owner, prompt_sha256: expected });
          }
        }
        const moduleSha = moduleContentHash(currentCode);
        const sidecarRel = syncRecordPathForModule(codePath);
        const nextSidecarText = serializeSyncRecord({ modulePath: codePath, owners, promptHashes: promptHashMap, moduleSha });
        const prevSidecar = readBytes(sidecarRel, MAX_SIDECAR_BYTES);
        const prevSidecarText = prevSidecar.status === 'ok' ? new TextDecoder('utf-8').decode(prevSidecar.bytes) : null;

        if (nextSidecarText !== prevSidecarText) {
          writeUtf8(sidecarRel, nextSidecarText, { createParents: true, defaultMode: 0o644 });
          syncRecordMap.set(codePath, parseSyncRecordBytes(Buffer.from(nextSidecarText, 'utf8'), codePath, sidecarRel));
          updated.push({ path: sidecarRel, kind: 'sync-record', module: codePath, prompt: owners[0] });
        }
        if (currentCode !== originalCode) {
          writeUtf8(codePath, currentCode, { createParents: false });
          codeTextMap.set(codePath, currentCode);
          updated.push(...headerUpdates);
        }
      }
    }

    const evaluated = evaluateState({ ownedPairs, promptTextMap, codeTextMap, syncRecordMap, diffByPath, updated, range: normalizedRange });
    const unowned = [...unownedMap.values()].sort((a, b) => cmpPath(a.path, b.path));
    const ok = mode === 'check' ? evaluated.drifted.length === 0 : true;
    const exitCode = mode === 'check' && evaluated.drifted.length > 0 ? 1 : 0;

    const report = {
      schema_version: 'pdd.update-sync.v1',
      ok,
      mode,
      scope,
      prompts: evaluated.prompts,
      modules: evaluated.modules,
      unowned,
      drifted: evaluated.drifted,
      updated: evaluated.updated,
    };
    return { ok, exitCode, error: null, report, root };
  } catch (error) {
    if (error instanceof UpdateStop) {
      return { ok: false, exitCode: error.exitCode, error: error.message, report: null, root: null };
    }
    return { ok: false, exitCode: 2, error: `pdd update failed: ${sanitizeOneLine(error?.message ?? error)}.`, report: null, root: null };
  }
}

export function formatUpdateJson(report) {
  return `${JSON.stringify(report)}\n`;
}

function formatSymbols(symbols) {
  if (!symbols?.length) return '';
  const prefix = { added: '+', removed: '-', updated: '~' };
  return `; symbols: ${symbols.map(s => `${prefix[s.kind] ?? ''}${s.symbol}`).join(', ')}`;
}

export function formatUpdateText(report) {
  const lines = [];
  if (!report.prompts.length && !report.unowned.length) {
    lines.push(`pdd update (${report.mode}): no touched files in scope.`);
    return `${lines.join('\n')}\n`;
  }
  lines.push(
    `pdd update (${report.mode}): ${report.prompts.length} prompt(s), ${report.modules.length} owned module(s), ${report.drifted.length} drifted, ${report.unowned.length} unowned`,
  );
  const modulesByPrompt = new Map();
  for (const mod of report.modules) {
    if (!modulesByPrompt.has(mod.owner)) modulesByPrompt.set(mod.owner, []);
    modulesByPrompt.get(mod.owner).push(mod);
  }
  for (const group of report.prompts) {
    lines.push(`${group.prompt} [${group.status}] (prompt_sha256: ${group.prompt_sha256 ? group.prompt_sha256.slice(0, 12) : 'deleted'})`);
    for (const mod of modulesByPrompt.get(group.prompt) ?? []) {
      const renamed = mod.renamed_from ? ` (renamed from ${mod.renamed_from})` : '';
      lines.push(
        `  - ${mod.path} [${mod.status}] (+${mod.diff_stats.added}/-${mod.diff_stats.removed})${formatSymbols(mod.changed_symbols)}${renamed}`,
      );
      if (mod.note) lines.push(`    note: ${mod.note}`);
    }
    if (group.instructions?.length) {
      lines.push('  Next:');
      for (const step of group.instructions) lines.push(`    - ${step}`);
    }
  }
  if (report.updated?.length) {
    lines.push(`Updated (${report.updated.length}):`);
    for (const item of report.updated) {
      lines.push(`  - ${item.path} (${item.kind})`);
    }
  }
  if (report.unowned.length) {
    lines.push(`Unowned files (${report.unowned.length}):`);
    for (const item of report.unowned) {
      lines.push(`  - ${item.path} (${item.reason})`);
    }
  }
  return `${lines.join('\n')}\n`;
}

export function runUpdate(
  { cwd = process.cwd(), files = [], from, check = false, write = false, json = false } = {},
  { stdout = process.stdout, stderr = process.stderr, ...ports } = {},
) {
  const result = analyzeUpdate({ cwd, files, from, check, write }, ports);
  if (result.error !== null) {
    stderr.write(`${result.error}\n`);
    return result.exitCode;
  }
  stdout.write(json ? formatUpdateJson(result.report) : formatUpdateText(result.report));
  return result.exitCode;
}
