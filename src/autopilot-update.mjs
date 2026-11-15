// Generated from prompts/cli/autopilot-update.prompt.md (sha256: 0377fd937a21bce9234ab7d248d5afbd584fd60fa27a2e8b27d25adaf9edb7c5).
import { spawnSync as nativeSpawnSync } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { isNewerRelease, parseReleaseVersion, pickLatestRelease } from './release-notice.mjs';

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));

const HOUR_MS = 60 * 60 * 1000;
const STATUS_FILE = 'autopilot-update.json';

export const validAutoUpdateMode = mode => ['release', 'main', 'off'].includes(mode);

function readJson(file, fs) {
  try {
    const parsed = JSON.parse(fs.readFileSync(file, 'utf8'));
    return parsed && typeof parsed === 'object' && !Array.isArray(parsed) ? parsed : null;
  } catch { return null; }
}

function writeJson(file, data, fs) {
  try {
    fs.mkdirSync(dirname(file), { recursive: true, mode: 0o700 });
    const tmp = `${file}.${process.pid}.${Date.now()}.tmp`;
    fs.writeFileSync(tmp, `${JSON.stringify(data)}\n`, { mode: 0o600 });
    fs.renameSync(tmp, file);
  } catch { /* Best-effort status persistence. */ }
}

function isMidWriteOrRuntimeJob(job) {
  if (!job || typeof job !== 'object') return false;
  if (job.phase === 'ending' || job.lane?.state === 'final') return true;
  if (job.runtimeWait?.state === 'sent' || job.runtime?.state === 'running') return true;
  return false;
}

export function hasMidWriteJobs(target, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const coreRoot = typeof target === 'string' ? target : target?.coreRoot;
  const stateRoot = (typeof target === 'object' && target !== null ? target.stateRoot : null) ?? ports.stateRoot ?? null;
  const roots = new Set();
  if (typeof coreRoot === 'string' && coreRoot) roots.add(coreRoot);
  if (typeof stateRoot === 'string' && stateRoot) {
    let entries = [];
    try { entries = fs.readdirSync(stateRoot); } catch { entries = []; }
    for (const entry of entries) {
      if (!entry.endsWith('-core')) continue;
      const candidate = join(stateRoot, entry);
      if (candidate !== coreRoot) {
        const saved = readJson(join(stateRoot, `${entry.slice(0, -5)}.json`), fs);
        if (saved && saved.enabled === false) continue;
      }
      roots.add(candidate);
    }
  }
  for (const root of roots) {
    let names = [];
    try { names = fs.readdirSync(join(root, 'jobs')).filter(name => name.endsWith('.json')); }
    catch { continue; }
    for (const name of names) {
      if (isMidWriteOrRuntimeJob(readJson(join(root, 'jobs', name), fs))) return true;
    }
  }
  return false;
}

export function detectGlobalInstallPrefix(packageRoot, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const uid = ports.uid !== undefined ? ports.uid : (typeof process.getuid === 'function' ? process.getuid() : null);
  if (typeof packageRoot !== 'string' || !packageRoot) return null;
  let real, info;
  try {
    real = fs.realpathSync(packageRoot);
    info = fs.statSync(real);
    if (!info.isDirectory()) return null;
    if (uid !== null && Number.isInteger(info.uid) && info.uid !== uid) return null;
    if (fs.existsSync(join(real, '.git'))) return null;
  } catch { return null; }
  const normalized = real.replace(/\\/g, '/').replace(/\/+$/, '');
  const match = /^(.*?)\/(?:lib\/)?node_modules\/(?:@promptdriven\/pdd|pdd)$/.exec(normalized);
  if (!match || !match[1]) return null;
  try {
    const prefixInfo = fs.statSync(match[1]);
    if (uid !== null && Number.isInteger(prefixInfo.uid) && prefixInfo.uid !== uid) return null;
  } catch { return null; }
  return { prefix: match[1], realPackageRoot: real };
}

function resolveInstalledRoot(prefix, fallbackRoot, fs) {
  for (const rel of ['lib/node_modules/@promptdriven/pdd', 'node_modules/@promptdriven/pdd', 'lib/node_modules/pdd', 'node_modules/pdd']) {
    const candidate = join(prefix, rel);
    try { if (fs.statSync(join(candidate, 'package.json')).isFile()) return candidate; } catch { /* Try next layout. */ }
  }
  return fallbackRoot;
}

async function ghApiJson(execute, endpoint) {
  const reply = await execute('gh', ['api', endpoint], { timeoutMs: 10000 });
  if (!reply || reply.code !== 0) {
    const detail = (reply?.stderr || reply?.stdout || `gh api ${endpoint} failed`).trim().split('\n')[0];
    throw Error(detail || `gh api ${endpoint} failed`);
  }
  return JSON.parse(reply.stdout || 'null');
}

export function autoUpdateStatusLine({ stateRoot }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  if (!stateRoot) return '';
  const saved = readJson(join(stateRoot, STATUS_FILE), fs);
  if (!saved) return '';
  if (saved.lastError) return `Auto-update (${saved.channel ?? 'release'}): last try failed (${String(saved.lastError).replace(/\s+/g, ' ').slice(0, 160)})`;
  if (saved.action === 'updated' && saved.toVersion && saved.updatedAt)
    return `Auto-update (${saved.channel ?? 'release'}): updated pdd ${saved.fromVersion ?? 'previous'} -> ${saved.toVersion} at ${new Date(saved.updatedAt).toISOString()}`;
  return '';
}

export async function maybeAutoUpdateAutopilot({ state, packageRoot, coreRoot, stateRoot, env = process.env }, ports = {}) {
  const mode = validAutoUpdateMode(state?.autoUpdate) ? state.autoUpdate : 'release';
  if (mode === 'off' || env.CI || env.PDD_AGENT_SESSION) return { action: 'disabled' };
  if (!stateRoot || !packageRoot) return { action: 'skipped', reason: 'missing-paths' };
  const fs = ports.fs ?? nativeFs;
  const now = (ports.now ?? Date.now)();
  const statusPath = join(stateRoot, STATUS_FILE);
  const previous = readJson(statusPath, fs);
  if (previous && Number.isFinite(previous.checkedAt) && now - previous.checkedAt < HOUR_MS)
    return { action: 'throttled' };
  if (hasMidWriteJobs({ coreRoot, stateRoot }, { fs }))
    return { action: 'deferred', reason: 'mid-write-job' };
  const globalInstall = detectGlobalInstallPrefix(packageRoot, { fs, uid: ports.uid });
  if (!globalInstall) {
    writeJson(statusPath, { ...(previous ?? {}), checkedAt: now, channel: mode, action: 'skipped', reason: 'non-global-or-unowned' }, fs);
    return { action: 'skipped', reason: 'non-global-or-unowned' };
  }
  const currentVersion = readJson(join(globalInstall.realPackageRoot, 'package.json'), fs)?.version;
  if (!parseReleaseVersion(currentVersion)) return { action: 'skipped', reason: 'unreadable-version' };
  const execute = ports.execute;
  if (typeof execute !== 'function') return { action: 'skipped', reason: 'missing-executor' };

  let targetSpec = null, targetLabel = null, nextSha = null;
  try {
    if (mode === 'release') {
      const payload = ports.fetchLatestRelease
        ? await ports.fetchLatestRelease()
        : await ghApiJson(execute, 'repos/promptdriven/pdd/releases?per_page=10');
      const picked = pickLatestRelease(payload);
      if (!picked) throw Error('Could not find a valid PDD release tag');
      if (!isNewerRelease(picked.version, currentVersion)) {
        writeJson(statusPath, { ...(previous ?? {}), checkedAt: now, channel: mode, action: 'up-to-date', version: currentVersion, lastError: null }, fs);
        return { action: 'up-to-date', version: currentVersion };
      }
      targetSpec = `github:promptdriven/pdd#${picked.tag}`;
      targetLabel = picked.tag;
    } else {
      const payload = ports.fetchMainHead
        ? await ports.fetchMainHead()
        : await ghApiJson(execute, 'repos/promptdriven/pdd/commits/main');
      const sha = typeof payload?.sha === 'string' && /^[0-9a-f]{40}$/i.test(payload.sha) ? payload.sha : null;
      if (!sha) throw Error('Could not read promptdriven/pdd main head');
      if (previous?.installedSha === sha) {
        writeJson(statusPath, { ...(previous ?? {}), checkedAt: now, channel: mode, action: 'up-to-date', version: currentVersion, installedSha: sha, lastError: null }, fs);
        return { action: 'up-to-date', version: currentVersion };
      }
      targetSpec = `github:promptdriven/pdd#${sha}`;
      targetLabel = sha.slice(0, 12);
      nextSha = sha;
    }
  } catch (error) {
    writeJson(statusPath, { ...(previous ?? {}), checkedAt: now, channel: mode, lastError: error.message || 'release lookup failed' }, fs);
    return { action: 'failed', error: error.message };
  }

  let releaseLock = null;
  try {
    if (ports.claimUpdateLock) {
      releaseLock = await ports.claimUpdateLock();
      if (!releaseLock) return { action: 'deferred', reason: 'lock-busy' };
    }
    if (hasMidWriteJobs({ coreRoot, stateRoot }, { fs })) return { action: 'deferred', reason: 'mid-write-job' };
    if (state?.cwd && state?.baseBranch) {
      try {
        const branch = await execute('git', ['rev-parse', '--abbrev-ref', 'HEAD'], { cwd: state.cwd, timeoutMs: 10000 });
        const status = await execute('git', ['status', '--porcelain'], { cwd: state.cwd, timeoutMs: 10000 });
        if (branch.code === 0 && branch.stdout.trim() === state.baseBranch && status.code === 0 && !status.stdout.trim())
          await execute('git', ['pull', '--ff-only', 'origin', state.baseBranch], { cwd: state.cwd, timeoutMs: 30000 });
      } catch { /* Checkout fast-forward is best-effort only. */ }
    }
    const install = await execute('npm', ['install', '-g', '--prefix', globalInstall.prefix, '--ignore-scripts', '--no-audit', '--no-fund', targetSpec], { timeoutMs: 120000 });
    if (install.code !== 0) throw Error((install.stderr || install.stdout || 'npm install failed').trim().split('\n')[0]);
    const installedRoot = resolveInstalledRoot(globalInstall.prefix, globalInstall.realPackageRoot, fs);
    const toVersion = readJson(join(installedRoot, 'package.json'), fs)?.version ?? currentVersion;
    try {
      const setup = ports.setupSkills ?? (await import('./skills-install.mjs')).setupSkills;
      setup({
        packageRoot: installedRoot,
        cwd: state?.cwd ?? process.cwd(),
        home: env.HOME || (ports.homedir ?? homedir)(),
        claudeConfigDir: env.CLAUDE_CONFIG_DIR,
        ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}),
      });
    } catch { /* Skill refresh never fails a completed binary update. */ }
    writeJson(statusPath, {
      checkedAt: now,
      updatedAt: now,
      channel: mode,
      action: 'updated',
      fromVersion: currentVersion,
      toVersion,
      target: targetLabel,
      ...(nextSha ? { installedSha: nextSha } : {}),
      lastError: null,
    }, fs);
    return { action: 'updated', fromVersion: currentVersion, toVersion };
  } catch (error) {
    writeJson(statusPath, { ...(previous ?? {}), checkedAt: now, channel: mode, lastError: error.message || 'update failed' }, fs);
    return { action: 'failed', error: error.message };
  } finally {
    releaseLock?.();
  }
}

const writeLine = (stream, text) => {
  if (stream && typeof stream.write === 'function') stream.write(`${text}\n`);
};

const canonicalDir = (folder, fs) => {
  try { return fs.realpathSync(folder); } catch { return folder; }
};

function formatStaleDetails(staleSkills) {
  if (!Array.isArray(staleSkills) || !staleSkills.length) return '';
  return staleSkills.map(({ name, state, version }) => state === 'older'
    ? `${name} is ${version ?? 'unknown'}`
    : `${name} differs (version ${version ?? 'unknown'})`).join(', ');
}

async function queryGitHubJson(endpoint, { fetchImpl, spawnSyncImpl, env = process.env } = {}) {
  const hasCustomFetch = typeof fetchImpl === 'function';
  const hasCustomSpawn = typeof spawnSyncImpl === 'function';
  const effectiveFetch = hasCustomFetch ? fetchImpl : (!hasCustomSpawn ? globalThis.fetch : null);
  const effectiveSpawn = hasCustomSpawn ? spawnSyncImpl : (!hasCustomFetch && !env.NODE_TEST_CONTEXT ? nativeSpawnSync : null);
  let fetchError = null;
  if (effectiveFetch) {
    try {
      const response = await effectiveFetch(`https://api.github.com/${endpoint}`, {
        headers: { Accept: 'application/vnd.github+json', 'User-Agent': 'pdd-cli' },
        signal: AbortSignal.timeout(10000),
      });
      if (response && typeof response.json === 'function') {
        if (response.ok === false) throw Error(`HTTP ${response.status}`);
        return await response.json();
      }
      return response;
    } catch (error) {
      fetchError = error;
      if (!effectiveSpawn) throw error;
    }
  }
  if (effectiveSpawn) {
    const reply = effectiveSpawn('gh', ['api', endpoint], { encoding: 'utf8', timeout: 10000, env });
    const code = reply?.status ?? reply?.code ?? (reply?.error ? 1 : 0);
    if (code !== 0) {
      const detail = (reply?.stderr || reply?.stdout || reply?.error?.message || fetchError?.message || `gh api ${endpoint} failed`).trim().split('\n')[0];
      throw Error(detail || `gh api ${endpoint} failed`);
    }
    return JSON.parse(reply.stdout || 'null');
  }
  throw fetchError ?? Error(`Could not query GitHub ${endpoint}`);
}

export async function resolveReleaseUpgradeTarget(options = {}) {
  const payload = await queryGitHubJson('repos/promptdriven/pdd/releases?per_page=10', options);
  const picked = pickLatestRelease(payload);
  if (!picked) throw Error('Could not find a valid PDD release tag');
  return {
    channel: 'release',
    ref: picked.tag,
    version: picked.version,
    spec: `github:promptdriven/pdd#${picked.tag}`,
  };
}

export async function resolveMainCommitTarget(options = {}) {
  const payload = await queryGitHubJson('repos/promptdriven/pdd/commits/main', options);
  const sha = typeof payload?.sha === 'string' && /^[0-9a-f]{40}$/i.test(payload.sha) ? payload.sha : null;
  if (!sha) throw Error('Could not read promptdriven/pdd main commit');
  return {
    channel: 'main',
    ref: sha,
    sha,
    spec: `github:promptdriven/pdd#${sha}`,
  };
}

export async function runCliUpgrade({
  env = process.env,
  stdout = process.stdout,
  stderr = process.stderr,
  main = false,
  spawnSyncImpl,
  fetchImpl,
  packageRoot = PACKAGE_ROOT,
  home,
  cwd = process.cwd(),
} = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const resolvedHome = home ?? env.HOME ?? (ports.homedir ?? homedir)();
  const globalInstall = detectGlobalInstallPrefix(packageRoot, { fs, uid: ports.uid });
  if (!globalInstall) {
    writeLine(stderr, 'pdd upgrade updates only a user-owned global npm installation (not a Git checkout or root-owned prefix). To update manually, run: npm install -g github:promptdriven/pdd && pdd setup');
    return { exitCode: 1, cliUpdated: false, updatedSkills: [], skippedSkills: [], failedSkills: [] };
  }
  const currentVersion = readJson(join(globalInstall.realPackageRoot, 'package.json'), fs)?.version;
  if (!parseReleaseVersion(currentVersion)) {
    writeLine(stderr, 'pdd upgrade could not read the installed pdd version. To reinstall, run: npm install -g github:promptdriven/pdd && pdd setup');
    return { exitCode: 1, cliUpdated: false, updatedSkills: [], skippedSkills: [], failedSkills: [] };
  }

  let target;
  try {
    target = main
      ? await resolveMainCommitTarget({ fetchImpl, spawnSyncImpl, env })
      : await resolveReleaseUpgradeTarget({ fetchImpl, spawnSyncImpl, env });
  } catch (error) {
    writeLine(stderr, `pdd upgrade could not check GitHub (${error?.message || 'lookup failed'}). To update manually, run: npm install -g github:promptdriven/pdd && pdd setup`);
    return { exitCode: 1, cliUpdated: false, fromVersion: currentVersion, toVersion: currentVersion, updatedSkills: [], skippedSkills: [], failedSkills: [] };
  }

  const effectiveSpawn = spawnSyncImpl ?? nativeSpawnSync;
  let cliUpdated = false;
  if (main || isNewerRelease(target.version, currentVersion)) {
    const install = effectiveSpawn('npm', ['install', '-g', '--prefix', globalInstall.prefix, '--ignore-scripts', '--no-audit', '--no-fund', target.spec], {
      encoding: 'utf8',
      timeout: 120000,
      env,
    });
    const code = install?.status ?? install?.code ?? (install?.error ? 1 : 0);
    if (code !== 0) {
      const detail = (install?.stderr || install?.stdout || install?.error?.message || 'npm install failed').trim().split('\n')[0];
      writeLine(stderr, `pdd upgrade failed to install ${target.spec} (${detail}). To retry, run: npm install -g --prefix ${globalInstall.prefix} --ignore-scripts ${target.spec} && pdd setup`);
      return { exitCode: 1, cliUpdated: false, fromVersion: currentVersion, toVersion: currentVersion, updatedSkills: [], skippedSkills: [], failedSkills: [] };
    }
    cliUpdated = true;
  }

  const targetPkgRoot = resolveInstalledRoot(globalInstall.prefix, globalInstall.realPackageRoot, fs);
  const toVersion = readJson(join(targetPkgRoot, 'package.json'), fs)?.version ?? (cliUpdated && target.version ? target.version : currentVersion);
  const stateHome = ports.stateHome ?? (env.XDG_STATE_HOME || (resolvedHome ? join(resolvedHome, '.local', 'state') : null));
  const stateRoot = env.PDD_STATE_DIR || (stateHome ? join(stateHome, 'pdd') : null);

  for (const cachePath of [stateHome ? join(stateHome, 'pdd', 'release-check.json') : null, stateRoot ? join(stateRoot, 'release-check.json') : null]) {
    if (cachePath) {
      try { fs.rmSync(cachePath, { force: true }); } catch { /* Stale release-notice cache removal is fail-open. */ }
    }
  }

  const failedSkills = [];
  const updatedSet = new Set();
  let skillsModule = null;
  try {
    skillsModule = ports.skillsInstall ?? await import('./skills-install.mjs');
    const { updated } = skillsModule.syncOwnedUserSkills({
      packageRoot: targetPkgRoot,
      home: resolvedHome,
      claudeConfigDir: env.CLAUDE_CONFIG_DIR,
      codexHome: env.CODEX_HOME,
      stateRoot,
      force: true,
      onError: (folder, error) => failedSkills.push({
        folder,
        reason: error?.code ?? error?.message ?? 'skill write failed',
        recovery: 'pdd setup',
      }),
    });
    for (const folder of updated) updatedSet.add(folder);
  } catch (error) {
    failedSkills.push({
      folder: resolvedHome || targetPkgRoot,
      reason: error?.code ?? error?.message ?? 'skill sync failed',
      recovery: 'pdd setup',
    });
  }

  const skippedSkills = [];
  if (skillsModule && typeof skillsModule.findSkills === 'function') {
    const noRepoCwd = join(resolvedHome || '/nonexistent', '.pdd-upgrade-user-only');
    const failedCanon = new Set(failedSkills.map(item => canonicalDir(item.folder, fs)));
    const seenSkip = new Set();
    try {
      for (const row of skillsModule.findSkills({
        packageRoot: targetPkgRoot,
        cwd: noRepoCwd,
        home: resolvedHome,
        claudeConfigDir: env.CLAUDE_CONFIG_DIR,
        ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}),
      })) {
        if (!row.found || !row.stale) continue;
        const key = canonicalDir(row.found, fs);
        if (failedCanon.has(key) || seenSkip.has(key)) continue;
        seenSkip.add(key);
        skippedSkills.push({
          folder: row.found,
          stale: row.stale,
          details: formatStaleDetails(row.staleSkills),
          recovery: "npx skills add promptdriven/pdd -g --skill '*'",
        });
      }
    } catch { /* User skill inspection is best-effort. */ }

    if (cwd && cwd !== noRepoCwd && (!resolvedHome || canonicalDir(cwd, fs) !== canonicalDir(resolvedHome, fs))) {
      const projectRoots = new Set([join(cwd, '.agents/skills'), join(cwd, '.codex/skills'), join(cwd, '.claude/skills')]);
      try {
        for (const row of skillsModule.findSkills({
          packageRoot: targetPkgRoot,
          cwd,
          home: resolvedHome,
          claudeConfigDir: env.CLAUDE_CONFIG_DIR,
          ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}),
        })) {
          if (!row.found || !row.stale || !projectRoots.has(row.found)) continue;
          const key = canonicalDir(row.found, fs);
          if (failedCanon.has(key) || seenSkip.has(key)) continue;
          seenSkip.add(key);
          skippedSkills.push({
            folder: row.found,
            stale: row.stale,
            details: formatStaleDetails(row.staleSkills),
            recovery: "npx skills add promptdriven/pdd --skill '*'",
          });
        }
      } catch { /* Project skill inspection is best-effort. */ }
    }
  }

  const updatedSkills = [...updatedSet];
  if (cliUpdated) {
    writeLine(stdout, `Upgraded pdd ${currentVersion} -> ${toVersion} (${main ? 'main' : target.ref}).`);
  } else if (!updatedSkills.length && !skippedSkills.length && !failedSkills.length) {
    writeLine(stdout, `pdd ${toVersion} is already up to date. PDD skills are current.`);
  } else {
    writeLine(stdout, `pdd ${toVersion} is already up to date.`);
  }
  if (updatedSkills.length) {
    writeLine(stdout, `Updated PDD skills to ${toVersion} in: ${updatedSkills.join(', ')}.`);
  }
  for (const item of skippedSkills) {
    writeLine(stdout, `Skipped ${item.stale === 'differs' ? 'customized' : 'unmarked'} PDD skills in ${item.folder}${item.details ? ` (${item.details})` : ''} (preserved without overwriting). To update unmarked skills, run: ${item.recovery}`);
  }
  for (const item of failedSkills) {
    writeLine(stderr, `Failed to update PDD skills in ${item.folder} (${item.reason}). To recover, run: ${item.recovery}`);
  }

  return {
    exitCode: failedSkills.length > 0 ? 1 : 0,
    cliUpdated,
    fromVersion: currentVersion,
    toVersion,
    updatedSkills,
    skippedSkills,
    failedSkills,
  };
}
