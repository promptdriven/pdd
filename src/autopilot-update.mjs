// Prompt: prompts/cli/autopilot-update.prompt.md
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join } from 'node:path';
import { isNewerRelease, parseReleaseVersion, pickLatestRelease } from './release-notice.mjs';
import {
  classifyInstallKind,
  detectGlobalInstallPrefix,
  formatNpmInstallCommand,
  hasLegacyUnscopedPdd,
  isLegacyUnscopedPddDir,
  npmCommandForInstall,
  quoteShellArg as quote,
  resolveInstalledBinEntry,
  resolveInstalledRoot,
  scrubVoltaEnv,
} from './shared/install-kind.mjs';

export { classifyInstallKind, detectGlobalInstallPrefix, hasLegacyUnscopedPdd };

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

const LEGACY_SHIM_RE = /(?:^|[\\/])node_modules[\\/]pdd(?:[\\/]|$)/;

function isLegacyNpmShim(src, rel, info, fs) {
  if (info.isDirectory?.()) return false;
  const isLink = Boolean(info.isSymbolicLink?.());
  if (!isLink && !info.isFile?.()) return false;
  const isRootShim = !rel.startsWith('bin/');
  if (isLink) {
    if (typeof fs.readlinkSync !== 'function') return false;
    try {
      const target = String(fs.readlinkSync(src));
      return isRootShim ? LEGACY_SHIM_RE.test(target) : true;
    } catch { return false; }
  }
  if (!isRootShim) return true;
  try {
    if (Number.isFinite(info.size) && info.size > 32768) return false;
    return LEGACY_SHIM_RE.test(String(fs.readFileSync(src, 'utf8')));
  } catch { return false; }
}

function stageLegacyPddBackup(prefix, fs, uid = undefined) {
  const effUid = uid !== undefined ? uid : (typeof process.getuid === 'function' ? process.getuid() : null);
  const backupDir = join(prefix, `.pdd-upgrade-backup-${process.pid}-${Date.now()}`);
  const cleanup = () => {
    try { fs.rmSync(backupDir, { recursive: true, force: true }); } catch { /* Best-effort backup cleanup. */ }
  };
  const lstat = fs.lstatSync ?? fs.statSync;
  const items = [];
  try {
    fs.mkdirSync(backupDir, { recursive: true, mode: 0o700 });
    for (const rel of ['lib/node_modules/pdd', 'node_modules/pdd']) {
      const src = join(prefix, rel);
      if (!isLegacyUnscopedPddDir(src, fs, effUid)) continue;
      const dst = join(backupDir, 'items', rel);
      fs.mkdirSync(dirname(dst), { recursive: true });
      fs.cpSync(src, dst, { recursive: true, verbatimSymlinks: true });
      items.push({ rel, isPkgDir: true, isSymlink: false, linkTarget: null });
    }
    for (const rel of ['bin/pdd', 'bin/pdd.cmd', 'bin/pdd.ps1', 'pdd', 'pdd.cmd', 'pdd.ps1']) {
      const src = join(prefix, rel);
      let info;
      try { info = lstat(src); } catch { continue; }
      if (!isLegacyNpmShim(src, rel, info, fs)) continue;
      const dst = join(backupDir, 'items', rel);
      fs.mkdirSync(dirname(dst), { recursive: true });
      if (info.isSymbolicLink?.() && typeof fs.readlinkSync === 'function' && typeof fs.symlinkSync === 'function') {
        const linkTarget = String(fs.readlinkSync(src));
        fs.symlinkSync(linkTarget, dst);
        items.push({ rel, isPkgDir: false, isSymlink: true, linkTarget });
      } else {
        fs.cpSync(src, dst, { recursive: true, verbatimSymlinks: true });
        items.push({ rel, isPkgDir: false, isSymlink: false, linkTarget: null });
      }
    }
  } catch {
    cleanup();
    return { staged: false, backupDir: null, restore: () => false, cleanup: () => {} };
  }
  if (!items.length) {
    cleanup();
    return { staged: false, backupDir: null, restore: () => false, cleanup: () => {} };
  }
  return {
    staged: true,
    backupDir,
    cleanup,
    restore() {
      try {
        for (const item of items) {
          const dst = join(prefix, item.rel);
          let curInfo = null;
          try { curInfo = lstat(dst); } catch { curInfo = null; }
          if (curInfo) {
            if (!item.isPkgDir && curInfo.isDirectory?.() && !curInfo.isSymbolicLink?.()) return false;
            if (item.isPkgDir && fs.existsSync(join(dst, '.git'))) return false;
            try { fs.rmSync(dst, { recursive: item.isPkgDir, force: true }); } catch { /* Clear partial state before restoring. */ }
          }
          fs.mkdirSync(dirname(dst), { recursive: true });
          if (item.isSymlink) {
            fs.symlinkSync(item.linkTarget, dst);
          } else {
            fs.cpSync(join(backupDir, 'items', item.rel), dst, { recursive: true, verbatimSymlinks: true });
          }
        }
        const ok = hasLegacyUnscopedPdd(prefix, { fs, uid: null });
        if (ok) cleanup();
        return ok;
      } catch {
        return false;
      }
    },
  };
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
  const globalInstall = detectGlobalInstallPrefix(packageRoot, { fs, uid: ports.uid, env, platform: ports.platform });
  if (!globalInstall) {
    writeJson(statusPath, { ...(previous ?? {}), checkedAt: now, channel: mode, action: 'skipped', reason: 'non-global-or-unowned' }, fs);
    return { action: 'skipped', reason: 'non-global-or-unowned' };
  }
  const currentVersion = readJson(join(globalInstall.realPackageRoot, 'package.json'), fs)?.version;
  if (!parseReleaseVersion(currentVersion)) return { action: 'skipped', reason: 'unreadable-version' };
  const execute = ports.execute;
  if (typeof execute !== 'function') return { action: 'skipped', reason: 'missing-executor' };
  const isVolta = globalInstall.kind === 'volta';
  const legacyUnscoped = isVolta
    ? (globalInstall.isLegacyUnscoped || hasLegacyUnscopedPdd(globalInstall, { fs, uid: ports.uid }))
    : hasLegacyUnscopedPdd(globalInstall.prefix, { fs, uid: ports.uid });

  let targetSpec = null, fallbackSpec = null, targetLabel = null, nextSha = null;
  try {
    if (mode === 'release') {
      const payload = ports.fetchLatestRelease
        ? await ports.fetchLatestRelease()
        : await ghApiJson(execute, 'repos/promptdriven/pdd/releases?per_page=10');
      const picked = pickLatestRelease(payload);
      if (!picked) throw Error('Could not find a valid PDD release tag');
      if (!legacyUnscoped && !isNewerRelease(picked.version, currentVersion)) {
        writeJson(statusPath, { ...(previous ?? {}), checkedAt: now, channel: mode, action: 'up-to-date', version: currentVersion, lastError: null }, fs);
        return { action: 'up-to-date', version: currentVersion };
      }
      targetSpec = `@promptdriven/pdd@${picked.version}`;
      fallbackSpec = `github:promptdriven/pdd#${picked.tag}`;
      targetLabel = picked.tag;
    } else {
      const payload = ports.fetchMainHead
        ? await ports.fetchMainHead()
        : await ghApiJson(execute, 'repos/promptdriven/pdd/commits/main');
      const sha = typeof payload?.sha === 'string' && /^[0-9a-f]{40}$/i.test(payload.sha) ? payload.sha : null;
      if (!sha) throw Error('Could not read promptdriven/pdd main head');
      if (!legacyUnscoped && previous?.installedSha === sha) {
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
    let backup = null, uninstalledLegacy = false;
    const needsUninstall = isVolta
      ? (globalInstall.isLegacyUnscoped || hasLegacyUnscopedPdd(globalInstall, { fs, uid: ports.uid }))
      : hasLegacyUnscopedPdd(globalInstall.prefix, { fs, uid: ports.uid });
    if (needsUninstall) {
      if (!isVolta) backup = stageLegacyPddBackup(globalInstall.prefix, fs, ports.uid);
      const u = npmCommandForInstall(globalInstall, 'uninstall', 'pdd', env);
      const uninstall = await execute(u.command, u.args, isVolta ? { timeoutMs: 60000, env: u.env } : { timeoutMs: 60000 });
      if (uninstall.code !== 0) {
        backup?.cleanup();
        throw Error((uninstall.stderr || uninstall.stdout || 'npm uninstall pdd failed').trim().split('\n')[0]);
      }
      uninstalledLegacy = true;
    }
    let installedSpec = targetSpec;
    let ins = npmCommandForInstall(globalInstall, 'install', installedSpec, env);
    let install = await execute(ins.command, ins.args, isVolta ? { timeoutMs: 120000, env: ins.env } : { timeoutMs: 120000 });
    const rawInstallOut = `${install.stderr || ''}\n${install.stdout || ''}`;
    if (install.code !== 0 && !/\bEEXIST\b/.test(rawInstallOut) && fallbackSpec) {
      installedSpec = fallbackSpec;
      ins = npmCommandForInstall(globalInstall, 'install', installedSpec, env);
      install = await execute(ins.command, ins.args, isVolta ? { timeoutMs: 120000, env: ins.env } : { timeoutMs: 120000 });
    }
    if (install.code !== 0) {
      const detail = (install.stderr || install.stdout || 'npm install failed').trim().split('\n')[0];
      if (uninstalledLegacy) {
        if (isVolta) {
          throw Error(`${detail}; unscoped pdd was removed — restore with: ${formatNpmInstallCommand(globalInstall, installedSpec)}`);
        }
        const restored = backup?.restore() ?? false;
        if (!restored) {
          const backupNote = backup?.backupDir ? ` (staged backup preserved at ${quote(backup.backupDir)})` : '';
          throw Error(`${detail}; unscoped pdd was removed and rollback failed${backupNote} — restore with: ${formatNpmInstallCommand(globalInstall, installedSpec)}`);
        }
      }
      throw Error(detail);
    }
    backup?.cleanup();
    const installedRoot = resolveInstalledRoot(globalInstall, globalInstall.realPackageRoot, fs);
    const toVersion = readJson(join(installedRoot, 'package.json'), fs)?.version ?? currentVersion;
    const resolvedHome = env.HOME || (ports.homedir ?? homedir)();
    try {
      if (typeof ports.setupSkills === 'function') {
        ports.setupSkills({
          packageRoot: installedRoot,
          cwd: state?.cwd ?? process.cwd(),
          home: resolvedHome,
          claudeConfigDir: env.CLAUDE_CONFIG_DIR,
          ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}),
          env,
        });
      } else {
        const binEntry = resolveInstalledBinEntry(installedRoot, fs);
        if (binEntry) {
          const childEnv = {
            ...(isVolta ? scrubVoltaEnv(env, globalInstall.voltaHome) : { ...env }),
            ...(resolvedHome ? { HOME: resolvedHome } : {}),
            PDD_NO_UPDATE_CHECK: '1',
          };
          const syncRes = await execute(
            ports.nodePath ?? process.execPath,
            [binEntry, 'setup', '--upgrade'],
            { cwd: state?.cwd ?? process.cwd(), timeoutMs: 60000, env: childEnv },
          );
          if (syncRes && syncRes.code === 2 && /--upgrade/.test(String(syncRes.stderr ?? ''))) {
            const { setupSkills } = await import('./shared/skills-install.mjs');
            setupSkills({
              packageRoot: installedRoot,
              cwd: state?.cwd ?? process.cwd(),
              home: resolvedHome,
              claudeConfigDir: env.CLAUDE_CONFIG_DIR,
              ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}),
              env,
            });
          }
        }
      }
    } catch { /* Skill/MCP refresh never fails a completed binary update. */ }
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
