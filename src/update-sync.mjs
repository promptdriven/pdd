// Generated from prompts/cli/update-sync.prompt.md (sha256: 2319fbd461ec8b3a573216298330ba750878218df49b52dee91e562d4ba722ed).
import { execFileSync } from 'node:child_process';
import { closeSync, constants as fsConstants, fstatSync, lstatSync, openSync, readSync, realpathSync, writeSync } from 'node:fs';
import { isAbsolute, join, posix, relative, resolve, sep } from 'node:path';
import {
  findOwners,
  headerEntries,
  headerHashState,
  isTestPromptPath,
  moduleContentHash,
  parseModuleSyncPins,
  promptHeaderHash,
  updateHeaderHash,
  updateModuleSyncPins,
} from './file-owner.mjs';
import { runtimePreflightSlice } from './runtime-seam.mjs';

const { gitFiles, isSecretPath } = runtimePreflightSlice();

const MAX_FILE_BYTES = 10 * 1024 * 1024;
const BINARY_PROBE_BYTES = 8192;
const EXTRA_SECRET_NAME = /^(?:\.env(?:\..+)?|credentials(?:\.[^/]+)?|\.aws-credentials)$/i;
const O_NOFOLLOW = fsConstants.O_NOFOLLOW ?? 0;

const cmpPath = (a, b) => (a < b ? -1 : a > b ? 1 : 0);
const unique = values => [...new Set(values)];
const sanitizeOneLine = text => String(text ?? '').replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').slice(0, 200);
const canonicalPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');
const isBlockedSecretPath = path => isSecretPath(path) || EXTRA_SECRET_NAME.test(posix.basename(path));

class UpdateStop extends Error {
  constructor(exitCode, message) {
    super(message);
    this.exitCode = exitCode;
  }
}

function parseFromRange(raw) {
  if (typeof raw !== 'string') throw new UpdateStop(2, 'Invalid --from range. Use <base>..<head> or <base>.');
  if (!raw || raw.length > 256 || /[\s\x00-\x1f\x7f]/.test(raw) || raw.includes('...') || raw.startsWith('-')) {
    throw new UpdateStop(2, `Invalid --from range: ${sanitizeOneLine(raw)}. Use <base>..<head> or <base>.`);
  }
  const parts = raw.split('..');
  if (parts.length === 1) {
    return `${parts[0]}..HEAD`;
  }
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
      throw error;
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

function readRegularBytes(root, relPath, limit = MAX_FILE_BYTES) {
  const check = inspectRegularPath(root, relPath);
  if (check.kind === 'missing') return { status: 'missing', bytes: null };
  if (check.kind === 'symlink') return { status: 'symlink', bytes: null };
  if (check.kind !== 'file') return { status: 'non-file', bytes: null };
  let fd;
  try { fd = openSync(check.full, fsConstants.O_RDONLY | O_NOFOLLOW); }
  catch (error) {
    if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return { status: 'missing', bytes: null };
    if (error.code === 'ELOOP') return { status: 'symlink', bytes: null };
    throw error;
  }
  try {
    const st = fstatSync(fd);
    if (!st.isFile()) return { status: 'non-file', bytes: null };
    const toRead = Math.min(limit + 1, st.size);
    const buffer = Buffer.alloc(toRead);
    let total = 0;
    while (total < toRead) {
      const count = readSync(fd, buffer, total, toRead - total, total);
      if (!count) break;
      total += count;
    }
    const slice = buffer.subarray(0, total);
    if (slice.length > limit) return { status: 'too-large', bytes: null };
    return { status: 'ok', bytes: slice };
  } finally {
    closeSync(fd);
  }
}

function writeRegularUtf8(root, relPath, text) {
  const check = inspectRegularPath(root, relPath);
  if (check.kind === 'symlink') throw new UpdateStop(2, `Symlinks are not allowed: ${relPath}.`);
  if (check.kind !== 'file') throw new UpdateStop(2, `Target is not a regular file: ${relPath}.`);
  let fd;
  try { fd = openSync(check.full, fsConstants.O_WRONLY | fsConstants.O_TRUNC | O_NOFOLLOW); }
  catch (error) {
    if (error.code === 'ELOOP') throw new UpdateStop(2, `Symlinks are not allowed: ${relPath}.`);
    throw error;
  }
  try {
    const data = Buffer.from(text, 'utf8');
    let written = 0;
    while (written < data.length) {
      written += writeSync(fd, data, written, data.length - written);
    }
  } finally {
    closeSync(fd);
  }
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

function defaultGitRangeEntries(root, range) {
  try {
    const out = execFileSync('git', ['-c', 'core.quotepath=false', 'diff', '--name-status', '-z', '-M', '--no-ext-diff', range, '--'], {
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
      const diffOut = execFileSync('git', ['-c', 'core.quotepath=false', 'diff', '--name-status', '-z', '-M', '--no-ext-diff', 'HEAD', '--'], {
        cwd: root,
        maxBuffer: 32 * 1024 * 1024,
        stdio: ['ignore', 'pipe', 'pipe'],
      });
      for (const entry of parseNameStatusZ(diffOut)) addEntry(entry);
    } catch { /* fall through to status */ }
  }
  const statusOut = execFileSync('git', ['-c', 'core.quotepath=false', 'status', '--porcelain=v1', '-z', '-uall'], {
    cwd: root,
    maxBuffer: 32 * 1024 * 1024,
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  for (const entry of parsePorcelainZ(statusOut)) addEntry(entry);
  return [...byPath.values()].sort((a, b) => cmpPath(a.path, b.path));
}

function defaultGitUnifiedDiff(root, range, paths) {
  if (!paths.length) return '';
  const args = ['-c', 'core.quotepath=false', 'diff', '--no-color', '--no-ext-diff', '-U0'];
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

function splitDiffByFile(fullDiff) {
  const byPath = new Map();
  if (!fullDiff) return byPath;
  const chunks = fullDiff.split(/^diff --git /m);
  for (const chunk of chunks) {
    if (!chunk) continue;
    const headerLine = chunk.slice(0, chunk.indexOf('\n'));
    const bMatch = / b\/(.+)$/.exec(headerLine);
    const plusMatch = /^\+\+\+ (?:b\/(.+)|\/dev\/null)$/m.exec(chunk);
    const renameToMatch = /^rename to (.+)$/m.exec(chunk);
    const minusMatch = /^--- (?:a\/(.+)|\/dev\/null)$/m.exec(chunk);
    const targetPath = (plusMatch && plusMatch[1]) || (renameToMatch && renameToMatch[1]) || (minusMatch && minusMatch[1]) || (bMatch && bMatch[1]);
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
  if (set.has('deleted')) return 'deleted';
  return 'current';
}

function buildInstructions(promptPath, status, modulePaths, diffStats, driftedDeleted) {
  const modList = modulePaths.join(', ');
  const statsStr = `+${diffStats.added}/-${diffStats.removed}`;
  const activeArgs = modulePaths.join(' ');
  switch (status) {
    case 'current':
      return ['In sync; no action needed.'];
    case 'unpinned':
      return [
        `Review diff in ${modList} (${statsStr}) and update ${promptPath} if behavior or domain rules changed.`,
        `Run \`pdd update --write ${activeArgs}\` to record per-module derived hashes.`,
      ];
    case 'code-drifted':
      return [
        `Code changed since last pin in ${modList} (${statsStr}); update ${promptPath} to match the reviewed diff.`,
        `Run \`pdd update --write ${activeArgs}\` after syncing ${promptPath}.`,
      ];
    case 'prompt-stale':
      return [
        `${promptPath} changed; verify ${modList} implements the updated contract.`,
        `Run \`pdd update --write ${activeArgs}\` to refresh derived hashes.`,
      ];
    case 'both-drifted':
      return [
        `Both ${promptPath} and ${modList} (${statsStr}) changed; reconcile contract prose and code.`,
        `Run \`pdd update --write ${activeArgs}\` once reconciled.`,
      ];
    case 'deleted':
      return driftedDeleted
        ? [`Owned file(s) deleted (${modList}); update ${promptPath} and run \`pdd update --write\` to prune stale pins.`]
        : [`Owned file(s) deleted (${modList}); no stale pins remain in ${promptPath}.`];
    default:
      return [];
  }
}

function evaluateState({ ownedPairs, promptTextMap, codeTextMap, diffByPath, updated }) {
  const promptHashCache = new Map();
  const promptPinsCache = new Map();
  for (const [promptPath, promptText] of promptTextMap.entries()) {
    promptHashCache.set(promptPath, promptHeaderHash(promptText));
    promptPinsCache.set(promptPath, parseModuleSyncPins(promptText));
  }

  const modules = [];
  const drifted = [];
  const byPrompt = new Map();

  for (const pair of ownedPairs) {
    const { entry, ownerRow, owner } = pair;
    const promptText = promptTextMap.get(owner);
    const prompt_sha256 = promptHashCache.get(owner);
    const pins = promptPinsCache.get(owner);
    const pin = pins.get(entry.path) ?? null;
    const diffSummary = diffByPath.get(entry.path) ?? { added: 0, removed: 0, changed_symbols: [] };

    let status, module_sha256 = null, recorded_prompt_sha256 = null, recorded_module_sha256 = pin?.sha256 ?? null, header_state = null;
    let isDrifted = false;

    if (entry.deleted) {
      status = 'deleted';
      recorded_prompt_sha256 = pin?.promptSha256 ?? null;
      isDrifted = pin !== null;
    } else {
      const codeText = codeTextMap.get(entry.path);
      module_sha256 = moduleContentHash(codeText);
      const headerRow = headerEntries(codeText).find(h => h.prompt === owner) ?? null;
      const hashState = headerRow ? headerHashState(headerRow.sha256, promptText) : null;
      header_state = hashState ? hashState.state : null;
      recorded_prompt_sha256 = headerRow?.sha256 ?? pin?.promptSha256 ?? null;

      const headerStale = Boolean(headerRow?.sha256 && hashState?.state === 'stale');
      const pinPromptStale = Boolean(pin?.promptSha256 && pin.promptSha256 !== prompt_sha256);
      const promptDrifted = headerStale || pinPromptStale;
      const codeDrifted = pin !== null && pin.sha256 !== module_sha256;

      if (promptDrifted && codeDrifted) status = 'both-drifted';
      else if (promptDrifted) status = 'prompt-stale';
      else if (codeDrifted) status = 'code-drifted';
      else if (pin !== null) status = 'current';
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
      diff_stats: { added: diffSummary.added, removed: diffSummary.removed },
      changed_symbols: diffSummary.changed_symbols,
      deleted: entry.deleted,
      renamed_from: entry.renamedFrom ?? null,
      note: ownerRow.note ?? '',
    };
    modules.push(row);
    if (isDrifted) drifted.push({ path: entry.path, owner, status });

    if (!byPrompt.has(owner)) byPrompt.set(owner, []);
    byPrompt.get(owner).push({ row, isDrifted });
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
      const driftedDeleted = items.some(item => item.row.deleted && item.isDrifted);
      return {
        prompt,
        status,
        prompt_sha256: promptHashCache.get(prompt),
        owner_certain: items.every(item => item.row.certain),
        modules: modulePaths,
        diff_stats: { added, removed },
        changed_symbols,
        instructions: buildInstructions(prompt, status, modulePaths, { added, removed }, driftedDeleted),
      };
    });

  modules.sort((a, b) => cmpPath(a.path, b.path) || cmpPath(a.owner, b.owner));
  drifted.sort((a, b) => cmpPath(a.path, b.path) || cmpPath(a.owner, b.owner));
  return { prompts, modules, drifted, updated };
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
    const listFiles = ports.files ?? (() => gitFiles(root));

    const codeBytesMap = new Map();
    const unownedMap = new Map();
    const touchedMap = new Map();

    if (scopeKind === 'files') {
      let realCwd;
      try { realCwd = ports.realCwd ? ports.realCwd(cwd) : realpathSync(cwd); }
      catch { realCwd = root; }
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
        touchedMap.set(rel, { path: rel, status: 'M', renamedFrom: null, deleted: false, untracked: false });
      }
    } else {
      const rawEntries = scopeKind === 'from'
        ? (ports.gitRangeEntries ? ports.gitRangeEntries(root, normalizedRange) : defaultGitRangeEntries(root, normalizedRange))
        : (ports.gitWorkingEntries ? ports.gitWorkingEntries(root) : defaultGitWorkingEntries(root));
      for (const raw of rawEntries) {
        if (!canonicalPath(raw.path)) throw new UpdateStop(2, `Invalid touched path: ${sanitizeOneLine(raw.path)}.`);
        if (isBlockedSecretPath(raw.path)) throw new UpdateStop(2, `Secret-looking path is not allowed: ${raw.path}.`);
        if (raw.deleted) {
          touchedMap.set(raw.path, { ...raw, deleted: true });
          continue;
        }
        const probe = readBytes(raw.path, BINARY_PROBE_BYTES);
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
      if (isTestPromptPath(entry.path)) {
        throw new UpdateStop(1, `Error: misplaced test prompt: ${entry.path}. Prompts own production modules, not test files.`);
      }
    }

    const ownerPorts = {
      ...(ports.files ? { files: ports.files } : {}),
      ...(ports.read ? { read: ports.read } : {}),
    };

    const nonPromptMap = new Map(touchedNonPrompts.map(entry => [entry.path, entry]));
    const activeTouchedPromptSet = new Set(touchedPrompts.filter(e => !e.deleted).map(e => e.path));

    // When a prompt itself is touched, pull its owned code modules into scope so prompt-only edits surface prompt-stale drift.
    if (activeTouchedPromptSet.size > 0) {
      const visible = listFiles();
      const extraCandidates = new Set(visible.filter(p => !p.endsWith('.prompt.md')));
      for (const promptPath of activeTouchedPromptSet) {
        const read = readBytes(promptPath, MAX_FILE_BYTES);
        if (read.status === 'ok' && !read.bytes.includes(0)) {
          for (const pinPath of parseModuleSyncPins(read.bytes).keys()) extraCandidates.add(pinPath);
        }
      }
      const candidateList = [...extraCandidates].sort(cmpPath);
      if (candidateList.length) {
        const allOwned = findOwners({ root, paths: candidateList }, ownerPorts);
        for (const row of allOwned.files) {
          if (row.owners.some(owner => activeTouchedPromptSet.has(owner)) && !nonPromptMap.has(row.path)) {
            if (isBlockedSecretPath(row.path)) continue;
            const probe = readBytes(row.path, BINARY_PROBE_BYTES);
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

    const candidateEntries = [...nonPromptMap.values()].sort((a, b) => cmpPath(a.path, b.path));
    const ownerLookup = candidateEntries.length
      ? findOwners({ root, paths: candidateEntries.map(e => e.path) }, ownerPorts)
      : { files: [] };
    const ownerRowByPath = new Map(ownerLookup.files.map(row => [row.path, row]));

    // For deleted files with no current header/binding/prose owner, also check existing prompt pins so stale pins get detected/pruned.
    const deletedUnowned = candidateEntries.filter(entry => entry.deleted && !(ownerRowByPath.get(entry.path)?.owners?.length));
    if (deletedUnowned.length) {
      const visiblePrompts = listFiles().filter(p => p.endsWith('.prompt.md') && !isTestPromptPath(p));
      const pinOwners = new Map();
      for (const promptPath of visiblePrompts) {
        const read = readBytes(promptPath, MAX_FILE_BYTES);
        if (read.status !== 'ok' || read.bytes.includes(0)) continue;
        const pins = parseModuleSyncPins(read.bytes);
        for (const entry of deletedUnowned) {
          if (pins.has(entry.path)) {
            if (!pinOwners.has(entry.path)) pinOwners.set(entry.path, []);
            pinOwners.get(entry.path).push(promptPath);
          }
        }
      }
      for (const [delPath, owners] of pinOwners.entries()) {
        const sortedOwners = unique(owners).sort(cmpPath);
        ownerRowByPath.set(delPath, {
          path: delPath,
          owner: sortedOwners[0],
          owners: sortedOwners,
          source: 'pin',
          certain: true,
          note: '',
          headers: [],
        });
      }
    }

    const ownedPairs = [];
    const neededPrompts = new Set();
    const codeTextMap = new Map();

    for (const entry of candidateEntries) {
      const ownerRow = ownerRowByPath.get(entry.path) ?? { path: entry.path, owner: null, owners: [], source: null, certain: true, note: '', headers: [] };
      if (!ownerRow.owners.length) {
        if (!entry.deleted && !codeBytesMap.has(entry.path)) {
          const probe = readBytes(entry.path, BINARY_PROBE_BYTES);
          if (probe.status === 'ok' && probe.bytes.includes(0)) {
            unownedMap.set(entry.path, { path: entry.path, reason: 'binary file (skipped)' });
            continue;
          }
        }
        unownedMap.set(entry.path, { path: entry.path, reason: 'no owning prompt' });
        continue;
      }
      const misplaced = ownerRow.owners.find(isTestPromptPath);
      if (misplaced) {
        throw new UpdateStop(1, `Error: misplaced test prompt: ${entry.path} is claimed by ${misplaced}. Prompts own production modules, not test files.`);
      }
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
        ownedPairs.push({ entry, ownerRow, owner });
      }
    }

    const promptTextMap = new Map();
    for (const promptPath of [...neededPrompts].sort(cmpPath)) {
      if (!canonicalPath(promptPath)) throw new UpdateStop(1, `Owning prompt path is invalid: ${sanitizeOneLine(promptPath)}.`);
      const read = readBytes(promptPath, MAX_FILE_BYTES);
      if (read.status === 'symlink') throw new UpdateStop(2, `Symlinks are not allowed: ${promptPath}.`);
      if (read.status === 'too-large') throw new UpdateStop(1, `Owning prompt exceeds 10 MiB limit: ${promptPath}.`);
      if (read.status !== 'ok') throw new UpdateStop(1, `Owning prompt is missing or unreadable: ${promptPath}.`);
      if (read.bytes.includes(0)) throw new UpdateStop(2, `Binary file is not supported: ${promptPath}.`);
      promptTextMap.set(promptPath, new TextDecoder('utf-8', { ignoreBOM: true }).decode(read.bytes));
    }

    const ownedPaths = unique(ownedPairs.map(pair => pair.entry.path)).sort(cmpPath);
    const fullDiff = ownedPaths.length
      ? (ports.gitUnifiedDiff ? ports.gitUnifiedDiff(root, normalizedRange, ownedPaths) : defaultGitUnifiedDiff(root, normalizedRange, ownedPaths))
      : '';
    const diffChunks = splitDiffByFile(fullDiff);
    const diffByPath = new Map();
    for (const pair of ownedPairs) {
      if (diffByPath.has(pair.entry.path)) continue;
      const chunk = diffChunks.get(pair.entry.path);
      if (chunk) {
        diffByPath.set(pair.entry.path, extractDiffSummary(chunk));
      } else if (!pair.entry.deleted && (pair.entry.untracked || pair.entry.status === 'A')) {
        diffByPath.set(pair.entry.path, summarizeWholeFileAsAdded(codeTextMap.get(pair.entry.path) ?? ''));
      } else {
        diffByPath.set(pair.entry.path, { added: 0, removed: 0, changed_symbols: [] });
      }
    }

    const updated = [];
    if (write) {
      const writeUtf8 = ports.writeUtf8 ?? ((path, text) => writeRegularUtf8(root, path, text));

      // 1. Refresh per-module pins inside each affected owning prompt (strictly preserving prose and untouched module pins).
      const pairsByPrompt = new Map();
      for (const pair of ownedPairs) {
        if (!pairsByPrompt.has(pair.owner)) pairsByPrompt.set(pair.owner, []);
        pairsByPrompt.get(pair.owner).push(pair);
      }
      for (const promptPath of [...pairsByPrompt.keys()].sort(cmpPath)) {
        const promptText = promptTextMap.get(promptPath);
        const promptSha = promptHeaderHash(promptText);
        const pinUpdates = [];
        const touchedForPrompt = [];
        for (const pair of pairsByPrompt.get(promptPath)) {
          touchedForPrompt.push(pair.entry.path);
          if (pair.entry.deleted) {
            pinUpdates.push({ path: pair.entry.path, delete: true });
          } else {
            if (pair.entry.renamedFrom && pair.entry.renamedFrom !== pair.entry.path) {
              pinUpdates.push({ path: pair.entry.renamedFrom, delete: true });
            }
            const codeSha = moduleContentHash(codeTextMap.get(pair.entry.path));
            pinUpdates.push({ path: pair.entry.path, sha256: codeSha, promptSha256: promptSha });
          }
        }
        const { content: nextPrompt, changed } = updateModuleSyncPins(promptText, pinUpdates);
        if (changed) {
          writeUtf8(promptPath, nextPrompt);
          promptTextMap.set(promptPath, nextPrompt);
          updated.push({ path: promptPath, kind: 'prompt-pin', modules: unique(touchedForPrompt).sort(cmpPath) });
        }
      }

      // 2. Refresh existing provenance headers in each active touched owned code file (never injecting new headers).
      const ownersByCode = new Map();
      for (const pair of ownedPairs) {
        if (pair.entry.deleted) continue;
        if (!ownersByCode.has(pair.entry.path)) ownersByCode.set(pair.entry.path, []);
        ownersByCode.get(pair.entry.path).push(pair.owner);
      }
      for (const codePath of [...ownersByCode.keys()].sort(cmpPath)) {
        const original = codeTextMap.get(codePath);
        let current = original;
        const headerUpdates = [];
        for (const owner of unique(ownersByCode.get(codePath))) {
          const expected = promptHeaderHash(promptTextMap.get(owner));
          const { content: nextCode, changed } = updateHeaderHash(current, owner, expected);
          if (changed) {
            current = nextCode;
            headerUpdates.push({ path: codePath, kind: 'code-header', prompt: owner, prompt_sha256: expected });
          }
        }
        if (current !== original) {
          writeUtf8(codePath, current);
          codeTextMap.set(codePath, current);
          updated.push(...headerUpdates);
        }
      }
    }

    const evaluated = evaluateState({ ownedPairs, promptTextMap, codeTextMap, diffByPath, updated });
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
    throw error;
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
    lines.push(`${group.prompt} [${group.status}] (prompt_sha256: ${group.prompt_sha256.slice(0, 12)})`);
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
