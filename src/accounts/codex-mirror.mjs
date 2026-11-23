// Generated from prompts/cli/login-pool.prompt.md.
// Codex home baseline, symlink target resolution, path mirroring, and config writeback normalization.
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { basename, dirname, join, resolve, sep } from 'node:path';
import { isPathAtOrInside, writeAtomicPrivate } from '../shared/atomic-fs.mjs';
import { CloudAccountsError } from './cloud-error.mjs';
import { formatTomlKey, formatTomlValue, isTomlTable, parseCodexTomlQuiet, serializeTomlConfig } from './toml-codec.mjs';

export const MIRRORED_CODEX_DOT_TMP_ENTRIES = ['bundled-marketplaces', 'marketplaces', 'plugins', 'plugins.sha'];
const MIRRORED_CODEX_DOT_TMP_SET = new Set(MIRRORED_CODEX_DOT_TMP_ENTRIES);
const USER_CODEX_BASELINE_DIRS = ['sessions', 'archived_sessions', 'plugins', 'skills', 'rules', 'memories'];
const USER_CODEX_BASELINE_DOT_TMP_DIRS = ['bundled-marketplaces', 'marketplaces', 'plugins'];

export const ISOLATED_CODEX_HOME_EXACT = new Set([
  '.', '..', '.ds_store', 'auth.json', 'auth.lock', 'config.toml', '.config.toml.merge-lock',
  'model-switch-backups', 'app-server-daemon', 'app-server-control', 'ipc', 'tmp', '.tmp', 'log',
  'logs_2.sqlite', 'logs_2.sqlite-wal', 'logs_2.sqlite-shm', 'models_cache.json', 'shell_snapshots',
  'mcp-oauth-locks', '.sqlite-maintenance.lock', 'installation_id', '.codex-global-state.json',
  'version.json', 'vendor_imports',
]);

export function isIsolatedCodexHomeEntry(name) {
  if (typeof name !== 'string' || !name || name.includes('/') || name.includes('\\')) return true;
  const lower = name.toLowerCase();
  if (ISOLATED_CODEX_HOME_EXACT.has(lower)) return true;
  return lower.startsWith('auth.json') || lower.startsWith('config.toml')
    || lower === 'tmp' || lower === '.tmp' || lower.startsWith('.tmp') || lower.endsWith('.tmp')
    || /\.tmp[._~-]/i.test(lower) || lower.endsWith('.lock') || lower.endsWith('-lock')
    || lower.endsWith('-wal') || lower.endsWith('-shm') || lower.endsWith('-journal')
    || /\.bak[^/]*$/i.test(lower) || /^logs_.*\.sqlite/i.test(lower);
}

export function assertNoSymlinkCodexPath(fs, targetPath) {
  const lstat = typeof fs?.lstatSync === 'function' ? fs.lstatSync.bind(fs) : (fs === nativeFs ? nativeFs.lstatSync : null);
  if (!lstat) return;
  const parentDir = dirname(targetPath);
  try {
    const dirStat = lstat(parentDir);
    if (dirStat.isSymbolicLink() || !dirStat.isDirectory()) {
      throw new CloudAccountsError(`Refusing symlink or non-directory Codex folder at ${parentDir}.`, { code: 'symlink_refused' });
    }
  } catch (error) {
    if (error instanceof CloudAccountsError) throw error;
    if (error?.code !== 'ENOENT') throw error;
  }
  try {
    const fileStat = lstat(targetPath);
    if (fileStat.isSymbolicLink() || !fileStat.isFile()) {
      throw new CloudAccountsError(`Refusing symlink or non-regular Codex file at ${targetPath}.`, { code: 'symlink_refused' });
    }
  } catch (error) {
    if (error instanceof CloudAccountsError) throw error;
    if (error?.code !== 'ENOENT') throw error;
  }
}

export function resolveUserCodexConfigTarget(fs, userConfigPath, disallowedRoots = [], { strict = true } = {}) {
  const lstat = typeof fs?.lstatSync === 'function' ? fs.lstatSync.bind(fs) : (fs === nativeFs ? nativeFs.lstatSync : null);
  if (!lstat) return { exists: true, readPath: userConfigPath, writePath: userConfigPath };
  const rejectOrSkip = msg => {
    if (strict) throw new CloudAccountsError(msg, { code: 'symlink_refused' });
    return { exists: false, readPath: null, writePath: userConfigPath };
  };
  const parentDir = dirname(userConfigPath);
  try {
    const dirStat = lstat(parentDir);
    if (dirStat.isSymbolicLink() || !dirStat.isDirectory()) return rejectOrSkip(`Refusing symlink or non-directory Codex folder at ${parentDir}.`);
  } catch (error) {
    if (error instanceof CloudAccountsError) throw error;
    if (error?.code === 'ENOENT' || !strict) return { exists: false, readPath: null, writePath: userConfigPath };
    throw error;
  }
  let fileStat;
  try { fileStat = lstat(userConfigPath); }
  catch (error) {
    if (error?.code === 'ENOENT' || !strict) return { exists: false, readPath: null, writePath: userConfigPath };
    throw error;
  }
  if (!fileStat.isSymbolicLink()) {
    return fileStat.isFile() ? { exists: true, readPath: userConfigPath, writePath: userConfigPath } : rejectOrSkip(`Refusing symlink or non-regular Codex file at ${userConfigPath}.`);
  }
  const realFn = fs?.realpathSync?.native ?? fs?.realpathSync ?? nativeFs.realpathSync?.native ?? nativeFs.realpathSync;
  const statFn = typeof fs?.statSync === 'function' ? fs.statSync.bind(fs) : (fs === nativeFs ? nativeFs.statSync : null);
  if (typeof realFn !== 'function' || !statFn) return rejectOrSkip(`Refusing symlink or non-regular Codex file at ${userConfigPath}.`);
  let realTarget;
  try {
    realTarget = String(realFn.call(fs, userConfigPath));
    if (!statFn(realTarget).isFile()) return rejectOrSkip(`Refusing symlink or non-regular Codex file at ${userConfigPath}.`);
    const targetDirStat = lstat(dirname(realTarget));
    if (targetDirStat.isSymbolicLink() || !targetDirStat.isDirectory()) return rejectOrSkip(`Refusing symlink or non-directory Codex folder at ${dirname(realTarget)}.`);
  } catch (error) {
    if (error instanceof CloudAccountsError) throw error;
    return rejectOrSkip(`Refusing symlink or non-regular Codex file at ${userConfigPath}.`);
  }
  for (const root of disallowedRoots) {
    if (typeof root !== 'string' || !root) continue;
    if (isPathAtOrInside(realTarget, root, fs)) return rejectOrSkip(`Refusing symlink or non-regular Codex file at ${userConfigPath}.`);
    try {
      if (isPathAtOrInside(realTarget, String(realFn.call(fs, root)), fs)) return rejectOrSkip(`Refusing symlink or non-regular Codex file at ${userConfigPath}.`);
    } catch {}
  }
  return { exists: true, readPath: realTarget, writePath: realTarget, isSymlink: true };
}

export function canonicalizeCodexPath(fs, targetPath) {
  const resolved = resolve(targetPath);
  const realFn = fs?.realpathSync?.native ?? fs?.realpathSync ?? (fs === nativeFs ? (nativeFs.realpathSync?.native ?? nativeFs.realpathSync) : null);
  if (typeof realFn !== 'function') return resolved;
  let cur = resolved;
  const trailing = [];
  while (true) {
    try {
      const realBase = String(realFn.call(fs, cur));
      return trailing.length > 0 ? join(realBase, ...trailing.reverse()) : realBase;
    } catch {
      const parent = dirname(cur);
      if (parent === cur) return resolved;
      trailing.push(basename(cur));
      cur = parent;
    }
  }
}

function expandTildePath(rawPath, env = process.env) {
  if (typeof rawPath !== 'string') return '';
  if (rawPath.startsWith('~/') || rawPath.startsWith('~\\')) {
    const home = (typeof env?.HOME === 'string' && env.HOME.trim()) ? env.HOME.trim() : homedir();
    return join(home, rawPath.slice(2));
  }
  return rawPath;
}

function stripCodexHomePrefix(rawPath, prefixes, env = process.env) {
  if (typeof rawPath !== 'string' || !rawPath) return null;
  const expanded = expandTildePath(rawPath, env);
  for (const prefix of prefixes) {
    if (!prefix) continue;
    if (expanded.startsWith(`${prefix}/`) || expanded.startsWith(`${prefix}\\`)) return expanded.slice(prefix.length + 1);
  }
  return null;
}

function isMirroredCodexRelativePath(relPath) {
  if (typeof relPath !== 'string' || !relPath) return false;
  const segments = relPath.split(/[\\/]+/).filter(Boolean);
  if (segments.length === 0) return false;
  if (segments[0].toLowerCase() === '.tmp') return segments.length >= 2 && MIRRORED_CODEX_DOT_TMP_SET.has(segments[1]);
  return !isIsolatedCodexHomeEntry(segments[0]);
}

function collectCodexHomeMirrorMappings(parsed, { userCodexHome = null, runtimeCodexHome = null, env = process.env, fs = nativeFs } = {}) {
  if (!isTomlTable(parsed) || typeof userCodexHome !== 'string' || !userCodexHome.trim() || typeof runtimeCodexHome !== 'string' || !runtimeCodexHome.trim()) {
    return { marketplaceSources: [], hookStates: [] };
  }
  const resolvedUserHome = resolve(userCodexHome.trim()), realUserHome = canonicalizeCodexPath(fs, resolvedUserHome);
  const resolvedRuntimeHome = resolve(runtimeCodexHome.trim()), realRuntimeHome = canonicalizeCodexPath(fs, resolvedRuntimeHome);
  if (realUserHome === realRuntimeHome || resolvedUserHome === resolvedRuntimeHome) return { marketplaceSources: [], hookStates: [] };
  const userPrefixes = [...new Set([realUserHome, resolvedUserHome])].sort((a, b) => b.length - a.length);
  const marketplaceSources = [];
  if (isTomlTable(parsed.marketplaces)) {
    for (const [name, table] of Object.entries(parsed.marketplaces)) {
      if (!isTomlTable(table) || typeof table.source !== 'string') continue;
      const rel = stripCodexHomePrefix(table.source.trim(), userPrefixes, env);
      if (!rel || !isMirroredCodexRelativePath(rel)) continue;
      marketplaceSources.push({ name, rewritten: join(realRuntimeHome, ...rel.split(/[\\/]+/).filter(Boolean)) });
    }
  }
  const hookStates = [];
  if (isTomlTable(parsed.hooks) && isTomlTable(parsed.hooks.state)) {
    for (const [key, entry] of Object.entries(parsed.hooks.state)) {
      if (!isTomlTable(entry)) continue;
      const rest = stripCodexHomePrefix(key, userPrefixes, env);
      if (!rest || !isMirroredCodexRelativePath(rest.split(':')[0])) continue;
      hookStates.push({ rewrittenKey: `${realRuntimeHome}${sep}${rest}`, entry });
    }
  }
  return { marketplaceSources, hookStates };
}

export function remapCodexHomeConfigObject(configData, { userCodexHome = null, runtimeCodexHome = null, env = process.env, fs = nativeFs } = {}) {
  if (!isTomlTable(configData)) return configData;
  const { marketplaceSources, hookStates } = collectCodexHomeMirrorMappings(configData, { userCodexHome, runtimeCodexHome, env, fs });
  const homesDiffer = typeof userCodexHome === 'string' && userCodexHome.trim()
    && typeof runtimeCodexHome === 'string' && runtimeCodexHome.trim()
    && canonicalizeCodexPath(fs, resolve(userCodexHome.trim())) !== canonicalizeCodexPath(fs, resolve(runtimeCodexHome.trim()));
  const needsAllowSymlink = homesDiffer && configData.allow_symlinked_codex_home === undefined;
  if (marketplaceSources.length === 0 && hookStates.length === 0 && !needsAllowSymlink) return configData;
  const next = { ...configData };
  if (needsAllowSymlink) next.allow_symlinked_codex_home = true;
  if (marketplaceSources.length > 0 && isTomlTable(configData.marketplaces)) {
    const nextMarketplaces = { ...configData.marketplaces };
    for (const { name, rewritten } of marketplaceSources) {
      if (isTomlTable(nextMarketplaces[name])) nextMarketplaces[name] = { ...nextMarketplaces[name], source: rewritten };
    }
    next.marketplaces = nextMarketplaces;
  }
  if (hookStates.length > 0 && isTomlTable(configData.hooks) && isTomlTable(configData.hooks.state)) {
    const nextState = { ...configData.hooks.state };
    for (const { rewrittenKey, entry } of hookStates) nextState[rewrittenKey] = { ...entry };
    next.hooks = { ...configData.hooks, state: nextState };
  }
  return next;
}

export function buildCodexHomeMirrorCliArgs({ userCodexHome = null, runtimeCodexHome = null, userConfigText = null, env = process.env, fs = nativeFs } = {}) {
  const parsed = parseCodexTomlQuiet(userConfigText);
  const args = [];
  const homesDiffer = typeof userCodexHome === 'string' && userCodexHome.trim()
    && typeof runtimeCodexHome === 'string' && runtimeCodexHome.trim()
    && canonicalizeCodexPath(fs, resolve(userCodexHome.trim())) !== canonicalizeCodexPath(fs, resolve(runtimeCodexHome.trim()));
  if (homesDiffer && parsed?.allow_symlinked_codex_home !== false) args.push('-c', 'allow_symlinked_codex_home=true');
  if (!parsed) return args;
  const { marketplaceSources, hookStates } = collectCodexHomeMirrorMappings(parsed, { userCodexHome, runtimeCodexHome, env, fs });
  const inlineMarketplaces = [];
  for (const { name, rewritten } of marketplaceSources) {
    if (/^[A-Za-z0-9_-]+$/.test(name)) args.push('-c', `marketplaces.${name}.source=${JSON.stringify(rewritten)}`);
    else inlineMarketplaces.push(`${JSON.stringify(name)} = { source = ${JSON.stringify(rewritten)} }`);
  }
  if (inlineMarketplaces.length > 0) args.push('-c', `marketplaces={ ${inlineMarketplaces.join(', ')} }`);
  const hookStateEntries = [];
  for (const { rewrittenKey, entry } of hookStates) {
    const fields = [];
    for (const [field, value] of Object.entries(entry)) {
      if (value === undefined) continue;
      try { fields.push(`${formatTomlKey(field)} = ${formatTomlValue(value)}`); } catch {}
    }
    if (fields.length > 0) hookStateEntries.push(`${JSON.stringify(rewrittenKey)} = { ${fields.join(', ')} }`);
  }
  if (hookStateEntries.length > 0) args.push('-c', `hooks.state={ ${hookStateEntries.join(', ')} }`);
  return args;
}

function collectRuntimeWritebackNeedles(fs, runtimeCodexHome) {
  const resolvedRuntimeHome = resolve(runtimeCodexHome.trim());
  const realRuntimeHome = canonicalizeCodexPath(fs, resolvedRuntimeHome);
  const runtimePrefixes = [...new Set([realRuntimeHome, resolvedRuntimeHome])].sort((a, b) => b.length - a.length);
  const needles = runtimePrefixes.flatMap(p => (sep === '\\' ? [p, JSON.stringify(p).slice(1, -1)] : [p]));
  return { resolvedRuntimeHome, realRuntimeHome, runtimePrefixes, needles };
}

export function needsCodexConfigWritebackNormalization(fs, { runtimeCodexHome = null, userConfigPath = null, beforeContent = null } = {}) {
  if (typeof runtimeCodexHome !== 'string' || !runtimeCodexHome.trim() || typeof userConfigPath !== 'string' || !userConfigPath.trim()) return false;
  const { resolvedRuntimeHome, realRuntimeHome, needles } = collectRuntimeWritebackNeedles(fs, runtimeCodexHome);
  const target = resolveUserCodexConfigTarget(fs, userConfigPath, [resolvedRuntimeHome, realRuntimeHome], { strict: false });
  if (!target.exists || !target.readPath) return false;
  let afterContent;
  try { afterContent = fs.readFileSync(target.readPath, 'utf8'); } catch { return false; }
  if (typeof beforeContent === 'string' && afterContent === beforeContent) return false;
  return needles.some(n => n && afterContent.includes(n));
}

export function normalizeCodexConfigWriteback(fs, { userCodexHome = null, runtimeCodexHome = null, userConfigPath = null, beforeContent = null } = {}) {
  if (typeof userCodexHome !== 'string' || !userCodexHome.trim() || typeof runtimeCodexHome !== 'string' || !runtimeCodexHome.trim() || typeof userConfigPath !== 'string' || !userConfigPath.trim()) {
    return false;
  }
  const resolvedUserHome = resolve(userCodexHome.trim());
  const { resolvedRuntimeHome, realRuntimeHome, runtimePrefixes, needles } = collectRuntimeWritebackNeedles(fs, runtimeCodexHome);
  const target = resolveUserCodexConfigTarget(fs, userConfigPath, [resolvedRuntimeHome, realRuntimeHome], { strict: false });
  if (!target.exists || !target.readPath || !target.writePath) return false;
  let afterContent;
  try { afterContent = fs.readFileSync(target.readPath, 'utf8'); } catch { return false; }
  if (typeof beforeContent === 'string' && afterContent === beforeContent) return false;
  if (!needles.some(n => n && afterContent.includes(n))) return false;
  const parsed = parseCodexTomlQuiet(afterContent);
  if (!parsed) return false;
  let changed = false;
  const next = { ...parsed };
  if (isTomlTable(parsed.marketplaces)) {
    const nextMarketplaces = { ...parsed.marketplaces };
    for (const [name, table] of Object.entries(parsed.marketplaces)) {
      if (!isTomlTable(table) || typeof table.source !== 'string') continue;
      const rel = stripCodexHomePrefix(table.source.trim(), runtimePrefixes);
      if (!rel || !isMirroredCodexRelativePath(rel)) continue;
      nextMarketplaces[name] = { ...table, source: join(resolvedUserHome, ...rel.split(/[\\/]+/).filter(Boolean)) };
      changed = true;
    }
    if (changed) next.marketplaces = nextMarketplaces;
  }
  if (isTomlTable(parsed.hooks) && isTomlTable(parsed.hooks.state)) {
    const nextState = {};
    let hooksChanged = false;
    for (const [key, entry] of Object.entries(parsed.hooks.state)) {
      const rest = stripCodexHomePrefix(key, runtimePrefixes);
      if (rest && isTomlTable(entry) && isMirroredCodexRelativePath(rest.split(':')[0])) {
        nextState[`${resolvedUserHome}${sep}${rest}`] = entry;
        hooksChanged = true;
      } else if (!Object.hasOwn(nextState, key)) nextState[key] = entry;
    }
    if (hooksChanged) { next.hooks = { ...parsed.hooks, state: nextState }; changed = true; }
  }
  if (!changed) return false;
  try { writeAtomicPrivate(fs, target.writePath, serializeTomlConfig(next, target.writePath)); return true; } catch { return false; }
}

export function ensureUserCodexHomeBaseline(fs, userHome) {
  fs.mkdirSync(userHome, { recursive: true, mode: 0o700 });
  const cfgPath = join(userHome, 'config.toml');
  let cfgExists = false;
  try { (fs.lstatSync ?? fs.statSync)(cfgPath); cfgExists = true; } catch (err) { if (err?.code !== 'ENOENT') throw err; }
  if (!cfgExists) {
    try {
      fs.writeFileSync(cfgPath, '', { encoding: 'utf8', mode: 0o600, flag: 'wx' });
      try { fs.chmodSync?.(cfgPath, 0o600); } catch {}
    } catch (err) { if (err?.code !== 'EEXIST') throw err; }
  }
  for (const dirName of USER_CODEX_BASELINE_DIRS) {
    const dirPath = join(userHome, dirName);
    try { (fs.lstatSync ?? fs.statSync)(dirPath); } catch (err) { if (err?.code === 'ENOENT') { try { fs.mkdirSync(dirPath, { recursive: true, mode: 0o700 }); } catch {} } }
  }
  const dotTmpDir = join(userHome, '.tmp');
  let dotTmpIsSafe = false;
  try {
    const st = (fs.lstatSync ?? fs.statSync)(dotTmpDir);
    dotTmpIsSafe = st.isDirectory() && !st.isSymbolicLink();
  } catch (err) {
    if (err?.code === 'ENOENT') { try { fs.mkdirSync(dotTmpDir, { recursive: true, mode: 0o700 }); dotTmpIsSafe = true; } catch {} }
  }
  if (dotTmpIsSafe) {
    for (const subName of USER_CODEX_BASELINE_DOT_TMP_DIRS) {
      const subPath = join(dotTmpDir, subName);
      try { (fs.lstatSync ?? fs.statSync)(subPath); } catch (err) { if (err?.code === 'ENOENT') { try { fs.mkdirSync(subPath, { recursive: true, mode: 0o700 }); } catch {} } }
    }
  }
  return cfgPath;
}
