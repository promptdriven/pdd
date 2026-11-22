// Generated from prompts/cli/login-pool.prompt.md.
// Managed Codex home mirroring, daemon stopping, restore, and local auth materialization.
import { spawnSync as nativeSpawnSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { basename, join, resolve } from 'node:path';
import { isPathAtOrInside, writeAtomicPrivate } from '../shared/atomic-fs.mjs';
import {
  localCodexConfigPath,
  localCodexHome,
  managedCodexAuthPath,
  managedCodexConfigPath,
  pddManagedCodexHome,
  stripCodexAuthBundle,
} from './cloud-state.mjs';
import {
  buildCodexGatewayFeaturePatch,
  buildCodexGatewayProviderBlock,
  buildGatewayAuthJson,
  resolveCodexGatewayEndpoints,
  resolveEffectiveSqliteHome,
} from './codex-config.mjs';
import {
  assertNoSymlinkCodexPath,
  isIsolatedCodexHomeEntry,
  MIRRORED_CODEX_DOT_TMP_ENTRIES,
  remapCodexHomeConfigObject,
  resolveUserCodexConfigTarget,
} from './codex-mirror.mjs';
import {
  CODEX_GATEWAY_PROVIDER_ID,
  isManagedCodexGatewayUrl,
  isTomlTable,
  readCodexTomlObject,
  serializeTomlConfig,
  stripGatewayFromTomlObject,
} from './toml-codec.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const MANAGED_CODEX_HOME_BASELINE_LINKS = [
  'AGENTS.md', 'agents', 'skills', 'memories', 'sessions', 'rules', 'plugins',
  'hooks.json', '.hook-trust', 'browser', 'chrome-native-hosts-v2.json', 'computer-use', 'node_repl',
  'archived_sessions', 'history.jsonl', 'session_index.jsonl', 'state_5.sqlite', 'thread_history_1.sqlite',
];
const REPLACED_MANAGED_CACHE_DIRS = new Set(['plugins', 'browser', 'computer-use', 'node_repl', 'cache', 'packages']);
const REPLACED_MANAGED_CACHE_FILES = new Set(['chrome-native-hosts-v2.json']);
const isDisallowedCodexSymlinkTargetName = name => {
  const lower = String(name ?? '').toLowerCase();
  return lower.startsWith('auth.json') || lower.startsWith('config.toml');
};

export function stopCodexAppServerDaemon(codexHome, { env = process.env, fs = nativeFs, spawnSync, codexBin = null } = {}) {
  if (typeof codexHome !== 'string' || !codexHome.trim()) return false;
  if (fs !== nativeFs && typeof spawnSync !== 'function') return false;
  const runner = typeof spawnSync === 'function' ? spawnSync : nativeSpawnSync;
  const bin = (typeof codexBin === 'string' && codexBin.trim())
    || (typeof env?.PDD_CODEX_BIN === 'string' && env.PDD_CODEX_BIN.trim())
    || 'codex';
  try {
    runner(bin, ['app-server', 'daemon', 'stop'], { env: { ...env, CODEX_HOME: codexHome }, stdio: 'ignore', timeout: 2500 });
    return true;
  } catch {
    return false;
  }
}

export function isSafeCodexSourceEntry(fs, src, targetRoot, { sourceHome = null } = {}) {
  if (typeof src !== 'string' || !src) return false;
  if (isDisallowedCodexSymlinkTargetName(basename(src))) return false;
  const lstat = typeof fs?.lstatSync === 'function' ? fs.lstatSync.bind(fs) : (fs === nativeFs ? nativeFs.lstatSync : null);
  if (!lstat) return false;
  let srcStat;
  try { srcStat = lstat(src); } catch { return false; }
  if (!srcStat.isSymbolicLink()) return true;
  if (typeof fs?.readlinkSync === 'function') {
    try { if (isDisallowedCodexSymlinkTargetName(basename(String(fs.readlinkSync(src))))) return false; } catch {}
  }
  const realFn = fs?.realpathSync?.native ?? fs?.realpathSync ?? nativeFs.realpathSync?.native ?? nativeFs.realpathSync;
  if (typeof realFn !== 'function') return false;
  let realSrc;
  try { realSrc = String(realFn.call(fs, src)); } catch { return false; }
  if (isDisallowedCodexSymlinkTargetName(basename(realSrc))) return false;
  const roots = (Array.isArray(targetRoot) ? targetRoot : [targetRoot]).filter(r => typeof r === 'string' && r);
  for (const root of roots) {
    if (isPathAtOrInside(realSrc, root, fs)) return false;
    try { if (isPathAtOrInside(realSrc, String(realFn.call(fs, root)), fs)) return false; } catch {}
  }
  if (typeof sourceHome === 'string' && sourceHome) {
    if (isPathAtOrInside(sourceHome, realSrc, fs)) return false;
    try { if (isPathAtOrInside(String(realFn.call(fs, sourceHome)), realSrc, fs)) return false; } catch {}
  }
  return true;
}

function replaceSymlinkAtomic(fs, src, dst, { symlink, removeLink }) {
  const rename = typeof fs?.renameSync === 'function' ? fs.renameSync.bind(fs) : (fs === nativeFs ? nativeFs.renameSync : null);
  if (rename) {
    const tmpLink = `${dst}.link-${process.pid}-${randomBytes(4).toString('hex')}`;
    try { symlink(src, tmpLink); rename(tmpLink, dst); return; } catch { removeLink(tmpLink); }
  }
  removeLink(dst);
  try { symlink(src, dst); } catch {}
}

function syncManagedCodexDotTmpLinks(fs, resolvedSourceHome, resolvedManagedHome, forbiddenRoots, { lstat, symlink, removeLink }) {
  const sourceTmp = join(resolvedSourceHome, '.tmp'), managedTmp = join(resolvedManagedHome, '.tmp');
  let managedTmpStat = null;
  try { managedTmpStat = lstat(managedTmp); } catch {}
  if (managedTmpStat?.isSymbolicLink()) { removeLink(managedTmp); managedTmpStat = null; }
  let sourceTmpOk = false;
  if (isSafeCodexSourceEntry(fs, sourceTmp, forbiddenRoots, { sourceHome: resolvedSourceHome })) {
    try { sourceTmpOk = Boolean((fs.statSync ?? nativeFs.statSync).call(fs, sourceTmp)?.isDirectory()); } catch {}
  }
  const validEntries = new Set();
  if (sourceTmpOk) {
    for (const name of MIRRORED_CODEX_DOT_TMP_ENTRIES) {
      if (isSafeCodexSourceEntry(fs, join(sourceTmp, name), forbiddenRoots, { sourceHome: resolvedSourceHome })) validEntries.add(name);
    }
  }
  if (validEntries.size === 0) {
    if (managedTmpStat?.isDirectory()) {
      for (const name of MIRRORED_CODEX_DOT_TMP_ENTRIES) {
        try { if (lstat(join(managedTmp, name)).isSymbolicLink()) removeLink(join(managedTmp, name)); } catch {}
      }
    }
    return;
  }
  if (managedTmpStat && !managedTmpStat.isDirectory()) return;
  fs.mkdirSync(managedTmp, { recursive: true, mode: 0o700 });
  try { (fs.chmodSync ?? nativeFs.chmodSync)?.(managedTmp, 0o700); } catch {}
  for (const name of MIRRORED_CODEX_DOT_TMP_ENTRIES) {
    const src = join(sourceTmp, name), dst = join(managedTmp, name);
    let dstStat = null;
    try { dstStat = lstat(dst); } catch {}
    if (validEntries.has(name)) {
      if (!dstStat) { try { symlink(src, dst); } catch {} }
      else if (dstStat.isSymbolicLink()) {
        let cur = null; try { cur = fs.readlinkSync?.(dst) ?? null; } catch {}
        if (cur !== src) replaceSymlinkAtomic(fs, src, dst, { symlink, removeLink });
      } else if (dstStat.isFile()) {
        replaceSymlinkAtomic(fs, src, dst, { symlink, removeLink });
      } else if (dstStat.isDirectory()) {
        try { (fs.rmSync ?? nativeFs.rmSync)?.(dst, { recursive: true, force: true }); symlink(src, dst); } catch {}
      }
    } else if (dstStat?.isSymbolicLink()) {
      removeLink(dst);
    }
  }
}

export function syncManagedCodexHomeLinks(fs, sourceHome, managedHome, extraForbiddenRoots = [], { preserveLinks = null } = {}) {
  fs.mkdirSync(managedHome, { recursive: true, mode: 0o700 });
  try { (fs.chmodSync ?? nativeFs.chmodSync)?.(managedHome, 0o700); } catch {}
  const resolvedSourceHome = resolve(sourceHome), resolvedManagedHome = resolve(managedHome);
  if (resolvedSourceHome === resolvedManagedHome) return;
  try {
    const realFn = fs.realpathSync?.native ?? fs.realpathSync;
    if (typeof realFn === 'function' && realFn.call(fs, sourceHome) === realFn.call(fs, managedHome)) return;
  } catch {}
  const lstat = typeof fs?.lstatSync === 'function' ? fs.lstatSync.bind(fs) : (fs === nativeFs ? nativeFs.lstatSync : null);
  const symlink = typeof fs?.symlinkSync === 'function' ? fs.symlinkSync.bind(fs) : null;
  if (!lstat || !symlink) return;
  try { if (lstat(managedHome).isSymbolicLink()) return; } catch {}
  const removeLink = dst => { try { if (typeof fs.unlinkSync === 'function') fs.unlinkSync(dst); else fs.rmSync?.(dst, { force: true }); } catch {} };
  const hasReaddir = typeof fs?.readdirSync === 'function';
  let candidateNames;
  if (hasReaddir) {
    try { candidateNames = fs.readdirSync(sourceHome).map(item => (typeof item === 'string' ? item : item?.name)).filter(Boolean); }
    catch { candidateNames = []; }
  } else {
    candidateNames = MANAGED_CODEX_HOME_BASELINE_LINKS;
  }
  const forbiddenRoots = [managedHome, ...extraForbiddenRoots, resolvedSourceHome];
  const activeValidLinks = new Set();
  for (const name of candidateNames) {
    if (isIsolatedCodexHomeEntry(name)) continue;
    const src = join(resolvedSourceHome, name), dst = join(managedHome, name);
    if (isSafeCodexSourceEntry(fs, src, forbiddenRoots, { sourceHome: resolvedSourceHome })) {
      activeValidLinks.add(name);
      let dstStat = null;
      try { dstStat = lstat(dst); } catch {}
      if (!dstStat) { try { symlink(src, dst); } catch {} }
      else if (dstStat.isSymbolicLink()) {
        let cur = null; try { cur = fs.readlinkSync?.(dst) ?? null; } catch {}
        if (cur !== src) replaceSymlinkAtomic(fs, src, dst, { symlink, removeLink });
      } else if (dstStat.isDirectory() && !dstStat.isSymbolicLink() && (REPLACED_MANAGED_CACHE_DIRS.has(name) || (hasReaddir && (() => { try { return fs.readdirSync(dst).length === 0; } catch { return false; } })()))) {
        try { (fs.rmSync ?? nativeFs.rmSync)?.(dst, { recursive: true, force: true }); symlink(src, dst); } catch {}
      } else if (REPLACED_MANAGED_CACHE_FILES.has(name) && dstStat.isFile() && !dstStat.isSymbolicLink()) {
        replaceSymlinkAtomic(fs, src, dst, { symlink, removeLink });
      }
    } else {
      try { if (lstat(dst).isSymbolicLink()) removeLink(dst); } catch {}
    }
  }
  if (hasReaddir) {
    let managedEntries = [];
    try { managedEntries = fs.readdirSync(managedHome).map(item => (typeof item === 'string' ? item : item?.name)).filter(Boolean); } catch {}
    for (const name of managedEntries) {
      if (preserveLinks?.has(name) || (activeValidLinks.has(name) && !isIsolatedCodexHomeEntry(name))) continue;
      try { if (lstat(join(managedHome, name)).isSymbolicLink()) removeLink(join(managedHome, name)); } catch {}
    }
  }
  syncManagedCodexDotTmpLinks(fs, resolvedSourceHome, resolvedManagedHome, forbiddenRoots, { lstat, symlink, removeLink });
}

export function restoreLocalCodexGatewayConfig({ env = process.env, previousModelProvider = null, removeAuthFile = false } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const managedHome = pddManagedCodexHome(env), configPath = managedCodexConfigPath(env), authPath = managedCodexAuthPath(env), userConfigPath = localCodexConfigPath(env);
  let restoredConfig = false, removedAuth = false;
  assertNoSymlinkCodexPath(fs, configPath);
  const resolvedUserCfg = resolveUserCodexConfigTarget(fs, userConfigPath, [managedHome], { strict: true });
  const { exists: hasUserConfig, data: userConfigData } = resolvedUserCfg.exists && resolvedUserCfg.readPath ? readCodexTomlObject(fs, resolvedUserCfg.readPath) : { exists: false, data: {} };
  let cleanUserData = {};
  if (hasUserConfig) {
    const strippedUser = stripGatewayFromTomlObject(userConfigData, previousModelProvider);
    cleanUserData = strippedUser.nextData;
    if (strippedUser.changed) {
      writeAtomicPrivate(fs, resolvedUserCfg.writePath, serializeTomlConfig(strippedUser.nextData, userConfigPath));
      restoredConfig = true;
    }
  }
  const { exists: hasManagedConfig, data: managedConfigData } = readCodexTomlObject(fs, configPath);
  if (hasManagedConfig) {
    const hadManagedGatewayOpenai = isManagedCodexGatewayUrl(managedConfigData?.openai_base_url);
    const hadManagedGatewayChatgpt = isManagedCodexGatewayUrl(managedConfigData?.chatgpt_base_url);
    const strippedManaged = stripGatewayFromTomlObject(managedConfigData, previousModelProvider);
    if (strippedManaged.changed) {
      const nextManagedData = { ...strippedManaged.nextData, cli_auth_credentials_store: 'file' };
      if (hadManagedGatewayOpenai && typeof cleanUserData.openai_base_url === 'string' && cleanUserData.openai_base_url.trim()) nextManagedData.openai_base_url = cleanUserData.openai_base_url;
      if (hadManagedGatewayChatgpt && typeof cleanUserData.chatgpt_base_url === 'string' && cleanUserData.chatgpt_base_url.trim()) nextManagedData.chatgpt_base_url = cleanUserData.chatgpt_base_url;
      writeAtomicPrivate(fs, configPath, serializeTomlConfig(nextManagedData, configPath));
      restoredConfig = true;
    }
  }
  if (removeAuthFile) {
    assertNoSymlinkCodexPath(fs, authPath);
    try {
      if (fs.statSync?.(authPath)?.isFile()) {
        if (typeof fs.rmSync === 'function') fs.rmSync(authPath, { force: true }); else fs.unlinkSync?.(authPath);
        removedAuth = true;
      }
    } catch {}
  }
  if (restoredConfig || removedAuth) stopCodexAppServerDaemon(managedHome, { env, fs, spawnSync: ports.spawnSync });
  return { codexHome: managedHome, configPath, authPath, userConfigPath, restoredConfig, removedAuth };
}

function writeAtomicCodexPair(fs, authPath, authText, configPath, configText) {
  let prevAuth = null, prevConfig = null;
  try { prevAuth = fs.readFileSync(authPath, 'utf8'); } catch {}
  try { prevConfig = fs.readFileSync(configPath, 'utf8'); } catch {}
  try {
    writeAtomicPrivate(fs, configPath, configText);
    writeAtomicPrivate(fs, authPath, authText);
  } catch (err) {
    try { if (prevConfig !== null) writeAtomicPrivate(fs, configPath, prevConfig); else (fs.rmSync ?? nativeFs.rmSync)(configPath, { force: true }); } catch {}
    try { if (prevAuth !== null) writeAtomicPrivate(fs, authPath, prevAuth); else (fs.rmSync ?? nativeFs.rmSync)(authPath, { force: true }); } catch {}
    throw err;
  }
}

export function materializeLocalCodexAuth(authOrLease, { env = process.env, previousManagedCodexGateway = false, previousCodexModelProvider = null } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const managedHome = pddManagedCodexHome(env), authPath = managedCodexAuthPath(env), configPath = managedCodexConfigPath(env);
  const userHome = localCodexHome(env), userConfigPath = localCodexConfigPath(env);
  const isGateway = object(authOrLease) && authOrLease.delivery_mode === 'gateway_grant';
  const endpoints = isGateway ? resolveCodexGatewayEndpoints(authOrLease, { requireGatewayUrl: true }) : null;
  const stripped = isGateway ? null : stripCodexAuthBundle(authOrLease);

  assertNoSymlinkCodexPath(fs, authPath);
  assertNoSymlinkCodexPath(fs, configPath);
  const resolvedUserCfg = resolveUserCodexConfigTarget(fs, userConfigPath, [managedHome], { strict: true });
  const { exists: hasUserConfig, data: rawUserConfig } = resolvedUserCfg.exists && resolvedUserCfg.readPath ? readCodexTomlObject(fs, resolvedUserCfg.readPath) : { exists: false, data: {} };
  const userCurrentProvider = typeof rawUserConfig.model_provider === 'string' ? rawUserConfig.model_provider.trim() : '';
  const { data: rawManagedConfig } = readCodexTomlObject(fs, configPath, { strict: false });
  const managedCurrentProvider = typeof rawManagedConfig.model_provider === 'string' ? rawManagedConfig.model_provider.trim() : '';
  const fallbackPriorProvider = (userCurrentProvider && userCurrentProvider !== CODEX_GATEWAY_PROVIDER_ID)
    ? userCurrentProvider
    : (managedCurrentProvider && managedCurrentProvider !== CODEX_GATEWAY_PROVIDER_ID)
      ? managedCurrentProvider
      : (typeof previousCodexModelProvider === 'string' && previousCodexModelProvider.trim() && previousCodexModelProvider.trim() !== CODEX_GATEWAY_PROVIDER_ID ? previousCodexModelProvider.trim() : null);

  const cleanedUser = stripGatewayFromTomlObject(rawUserConfig, fallbackPriorProvider);
  if (hasUserConfig && (cleanedUser.changed || previousManagedCodexGateway) && cleanedUser.changed) {
    writeAtomicPrivate(fs, resolvedUserCfg.writePath, serializeTomlConfig(cleanedUser.nextData, userConfigPath));
  }
  syncManagedCodexHomeLinks(fs, userHome, managedHome);

  if (isGateway) {
    const { grantToken, gatewayUrl, backendApiUrl, codexApiUrl, nativeBackendApi, embeddedLeaseGrant } = endpoints;
    const prevProviders = isTomlTable(cleanedUser.nextData.model_providers) ? { ...cleanedUser.nextData.model_providers } : {};
    const effectiveSqliteHome = resolveEffectiveSqliteHome({ userCodexHome: userHome, parsedConfig: cleanedUser.nextData, env });
    const nextConfig = remapCodexHomeConfigObject({
      ...cleanedUser.nextData,
      cli_auth_credentials_store: 'file',
      openai_base_url: codexApiUrl,
      chatgpt_base_url: backendApiUrl,
      ...(effectiveSqliteHome ? { sqlite_home: effectiveSqliteHome } : {}),
      features: buildCodexGatewayFeaturePatch(cleanedUser.nextData.features, { nativeBackendApi }),
      model_providers: {
        ...prevProviders,
        [CODEX_GATEWAY_PROVIDER_ID]: buildCodexGatewayProviderBlock({ codexApiUrl, nativeBackendApi, embeddedLeaseGrant, grantToken, headerMode: 'inline' }),
      },
    }, { userCodexHome: userHome, runtimeCodexHome: managedHome, env, fs });
    delete nextConfig.model_provider;
    const serializedConfig = serializeTomlConfig(nextConfig, configPath);
    const authText = `${JSON.stringify(buildGatewayAuthJson({ grantToken, planType: authOrLease?.plan_type ?? authOrLease?.plan, now: ports.now ?? Date.now }), null, 2)}\n`;
    let existingConfigText = null;
    try { existingConfigText = fs.readFileSync(configPath, 'utf8'); } catch {}
    if (existingConfigText === serializedConfig) writeAtomicPrivate(fs, authPath, authText);
    else writeAtomicCodexPair(fs, authPath, authText, configPath, serializedConfig);
    return { codexHome: managedHome, authPath, configPath, managedCodexGateway: true, codexGatewayUrl: gatewayUrl, previousCodexModelProvider: fallbackPriorProvider };
  }

  const effectiveOwnerSqliteHome = resolveEffectiveSqliteHome({ userCodexHome: userHome, parsedConfig: cleanedUser.nextData, env });
  const nextOwnerConfig = remapCodexHomeConfigObject({
    ...cleanedUser.nextData,
    cli_auth_credentials_store: 'file',
    ...(effectiveOwnerSqliteHome ? { sqlite_home: effectiveOwnerSqliteHome } : {}),
  }, { userCodexHome: userHome, runtimeCodexHome: managedHome, env, fs });
  writeAtomicCodexPair(fs, authPath, `${JSON.stringify(stripped, null, 2)}\n`, configPath, serializeTomlConfig(nextOwnerConfig, configPath));
  return { codexHome: managedHome, authPath, configPath, stripped, managedCodexGateway: false, codexGatewayUrl: null, previousCodexModelProvider: null };
}
