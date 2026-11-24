// Prompt: prompts/cli/cli-upgrade.prompt.md
import { spawnSync as nativeSpawnSync } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { isNewerRelease, parseReleaseVersion, pickLatestRelease } from '../release-notice.mjs';
import {
  classifyInstallKind,
  detectGlobalInstallPrefix,
  formatNpmInstallCommand,
  formatNpmUninstallCommand,
  hasLegacyUnscopedPdd,
  npmCommandForInstall,
  resolveInstalledBinEntry,
  resolveInstalledRoot,
  scrubVoltaEnv,
} from '../shared/install-kind.mjs';
import { PACKAGE_ROOT } from '../shared/package-root.mjs';
import { resolvePddStateBase } from '../shared/state-dir.mjs';

export { classifyInstallKind, detectGlobalInstallPrefix, hasLegacyUnscopedPdd };

const writeLine = (stream, text) => { if (stream?.write) stream.write(`${text}\n`); };
const canonicalDir = (folder, fs) => { try { return fs.realpathSync(folder); } catch { return folder; } };

function readJson(file, fs) {
  try {
    const parsed = JSON.parse(fs.readFileSync(file, 'utf8'));
    return parsed && typeof parsed === 'object' && !Array.isArray(parsed) ? parsed : null;
  } catch { return null; }
}

const SKIP_LABELS = {
  'git-checkout': 'a Git checkout',
  pypi: 'a Python (PyPI) installation',
  pnpm: 'a pnpm-managed installation',
  npx: 'an ephemeral npx cache',
  'local-project': 'a local project node_modules installation',
  'unowned-prefix': 'a non-user-owned npm prefix',
};

async function queryGitHubJson(endpoint, { fetchImpl, spawnSyncImpl, env = process.env } = {}) {
  const effectiveFetch = typeof fetchImpl === 'function' ? fetchImpl : (!spawnSyncImpl ? globalThis.fetch : null);
  const effectiveSpawn = typeof spawnSyncImpl === 'function' ? spawnSyncImpl : (fetchImpl === undefined ? nativeSpawnSync : null);
  let fetchError = null;
  if (effectiveFetch) {
    try {
      const res = await effectiveFetch(`https://api.github.com/${endpoint}`, {
        headers: { Accept: 'application/vnd.github+json', 'User-Agent': 'pdd-cli' },
        signal: AbortSignal.timeout(10000),
      });
      if (res && typeof res.json === 'function') {
        if (res.ok === false) throw new Error(`HTTP ${res.status}`);
        return await res.json();
      }
      return res;
    } catch (error) {
      fetchError = error;
      if (!effectiveSpawn) throw error;
    }
  }
  if (effectiveSpawn) {
    const reply = effectiveSpawn('gh', ['api', endpoint], { encoding: 'utf8', timeout: 10000, env });
    if (reply?.signal || (reply?.status ?? reply?.code ?? (reply?.error ? 1 : 0)) !== 0) {
      throw new Error((reply?.stderr || reply?.stdout || reply?.error?.message || fetchError?.message || `gh api ${endpoint} failed`).trim().split('\n')[0]);
    }
    return JSON.parse(reply.stdout || 'null');
  }
  throw fetchError ?? new Error(`Could not query GitHub ${endpoint}`);
}

export async function resolveReleaseUpgradeTarget(options = {}) {
  const picked = pickLatestRelease(await queryGitHubJson('repos/promptdriven/pdd/releases?per_page=10', options));
  if (!picked) throw new Error('Could not find a valid PDD release tag');
  return {
    channel: 'release', ref: picked.tag, version: picked.version,
    npmSpec: `@promptdriven/pdd@${picked.version}`, fallbackSpec: `github:promptdriven/pdd#${picked.tag}`,
    spec: `@promptdriven/pdd@${picked.version}`,
  };
}

export async function resolveMainCommitTarget(options = {}) {
  const payload = await queryGitHubJson('repos/promptdriven/pdd/commits/main', options);
  const sha = typeof payload?.sha === 'string' && /^[0-9a-f]{40}$/i.test(payload.sha) ? payload.sha : null;
  if (!sha) throw new Error('Could not read promptdriven/pdd main commit');
  return { channel: 'main', ref: sha, sha, spec: `github:promptdriven/pdd#${sha}` };
}

function runNpmAction(spawnImpl, install, action, spec, env, timeout = 120000) {
  const invocation = npmCommandForInstall(install, action, spec, env);
  const res = spawnImpl(invocation.command, invocation.args, { encoding: 'utf8', timeout, env: invocation.env });
  const ok = (res?.status ?? res?.code ?? ((res?.error || res?.signal) ? 1 : 0)) === 0;
  const sigNote = res?.signal ? `killed by ${res.signal}` : '';
  const raw = `${res?.stderr || ''}\n${res?.stdout || ''}\n${res?.error?.message || sigNote}`;
  const detail = (res?.stderr || res?.stdout || res?.error?.message || sigNote || `npm ${action} failed`).trim().split('\n')[0];
  return { ok, raw, detail };
}

function parseSetupUpgradeOutput(rawStdout) {
  const lines = String(rawStdout ?? '').split(/\r?\n/).map(line => line.trimEnd()).filter(Boolean);
  const updatedSet = new Set();
  const skippedSkills = [];
  const updatedMcp = [];
  for (const line of lines) {
    let match = /^(?:Installed|Updated) \d+ PDD skills? (?:to|in) (.+): /.exec(line);
    if (match?.[1]) { updatedSet.add(match[1]); continue; }
    match = /^Removed retired PDD skills from (.+): /.exec(line);
    if (match?.[1]) { updatedSet.add(match[1]); continue; }
    match = /^PDD skills in (.+?) (are older than|differ from) /.exec(line);
    if (match?.[1]) {
      skippedSkills.push({
        folder: match[1],
        stale: match[2] === 'differ from' ? 'differs' : 'older',
        details: line,
        recovery: 'pdd setup',
      });
      continue;
    }
    match = /^Retired PDD skills remain in (.+?) \(pdd /.exec(line);
    if (match?.[1]) {
      skippedSkills.push({
        folder: match[1],
        stale: 'older',
        details: line,
        recovery: 'pdd setup',
      });
      continue;
    }
    if (/^Updated PDD (?:Simulator )?MCP tools /.test(line)) {
      updatedMcp.push(line);
    }
  }
  return { lines, updatedSkills: [...updatedSet], skippedSkills, updatedMcp };
}

function runFallbackSkillsSync(skillsModule, {
  targetPkgRoot, resolvedHome, env, stateRoot, cwd, fs,
}) {
  const failedSkills = [], updatedSkills = [], skippedSkills = [];
  try {
    const { updated } = skillsModule.syncOwnedUserSkills({
      packageRoot: targetPkgRoot,
      home: resolvedHome,
      claudeConfigDir: env.CLAUDE_CONFIG_DIR,
      codexHome: env.CODEX_HOME,
      stateRoot,
      env,
      force: true,
      onError: (folder, error) => failedSkills.push({ folder, reason: error?.code ?? error?.message ?? 'skill write failed', recovery: 'pdd setup' }),
    });
    updatedSkills.push(...updated);
  } catch (error) {
    failedSkills.push({ folder: resolvedHome || targetPkgRoot, reason: error?.code ?? error?.message ?? 'skill sync failed', recovery: 'pdd setup' });
  }

  if (typeof skillsModule.findSkills === 'function') {
    const failedCanon = new Set(failedSkills.map(item => canonicalDir(item.folder, fs)));
    const seenSkip = new Set();
    try {
      for (const row of skillsModule.findSkills({ packageRoot: targetPkgRoot, cwd, home: resolvedHome, claudeConfigDir: env.CLAUDE_CONFIG_DIR, ...(env.CODEX_HOME ? { codexHome: env.CODEX_HOME } : {}) })) {
        const folder = row.found ?? row.root;
        const hasStale = Boolean(row.found && row.stale);
        const hasRetired = Array.isArray(row.retiredSkills) && row.retiredSkills.length > 0;
        if (!folder || (!hasStale && !hasRetired)) continue;
        const key = canonicalDir(folder, fs);
        if (failedCanon.has(key) || seenSkip.has(key)) continue;
        seenSkip.add(key);
        const staleDetails = (row.staleSkills ?? []).map(({ name, state, version }) => state === 'older' ? `${name} is ${version ?? 'unknown'}` : `${name} differs (version ${version ?? 'unknown'})`);
        const retiredDetails = (row.retiredSkills ?? []).map(({ name, version }) => `retired ${name}${version ? ` (${version})` : ''}`);
        const details = [...staleDetails, ...retiredDetails].join(', ');
        skippedSkills.push({
          folder,
          stale: row.stale ?? 'older',
          details,
          recovery: row.scope === 'project' ? "npx skills add promptdriven/pdd --skill '*'" : (hasRetired && !hasStale ? 'pdd setup' : "npx skills add promptdriven/pdd -g --skill '*'"),
        });
      }
    } catch {}
  }
  return { updatedSkills, skippedSkills, failedSkills };
}

export async function runCliUpgrade({
  env = process.env, stdout = process.stdout, stderr = process.stderr, main = false,
  spawnSyncImpl, fetchImpl, packageRoot = PACKAGE_ROOT, home, cwd = process.cwd(),
} = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const resolvedHome = home ?? env.HOME ?? (ports.homedir ?? homedir)();
  const install = classifyInstallKind(packageRoot, { fs, uid: ports.uid, env, platform: ports.platform });
  const fail = (msg, fromVersion, toVersion) => {
    writeLine(stderr, msg);
    return { exitCode: 1, cliUpdated: false, ...(fromVersion ? { fromVersion, toVersion } : {}), updatedSkills: [], skippedSkills: [], failedSkills: [] };
  };
  if (install.kind !== 'npm-global' && install.kind !== 'volta') {
    return fail(`pdd upgrade skips ${SKIP_LABELS[install.kind] ?? 'this installation'} (${packageRoot}).\n  Invariant: pdd upgrade modifies only a user-owned global npm installation (including Volta) of @promptdriven/pdd.\n  Fix: Run \`${install.hint ?? 'npm install -g @promptdriven/pdd && pdd setup'}\`.\n  Rerun: pdd --version`);
  }
  const currentVersion = readJson(join(install.realPackageRoot, 'package.json'), fs)?.version;
  if (!parseReleaseVersion(currentVersion)) {
    return fail('pdd upgrade could not read the installed pdd version. To reinstall, run: npm install -g @promptdriven/pdd && pdd setup');
  }

  let target;
  try {
    target = main ? await resolveMainCommitTarget({ fetchImpl, spawnSyncImpl, env }) : await resolveReleaseUpgradeTarget({ fetchImpl, spawnSyncImpl, env });
  } catch (error) {
    return fail(`pdd upgrade could not check releases (${error?.message || 'lookup failed'}). To update manually, run: npm install -g @promptdriven/pdd && pdd setup`, currentVersion, currentVersion);
  }

  const spawnImpl = spawnSyncImpl ?? nativeSpawnSync;
  const isVolta = install.kind === 'volta';
  const legacyVoltaUnscoped = isVolta && (install.isLegacyUnscoped || hasLegacyUnscopedPdd(install, { fs, uid: ports.uid }));
  let cliUpdated = false;
  if (main || legacyVoltaUnscoped || isNewerRelease(target.version, currentVersion)) {
    if (legacyVoltaUnscoped) {
      const uninstall = runNpmAction(spawnImpl, install, 'uninstall', 'pdd', env, 60000);
      if (!uninstall.ok) {
        return fail(
          `pdd upgrade failed to remove the unscoped pdd package under Volta (${uninstall.detail}). To migrate manually, run: ${formatNpmUninstallCommand(install)} && ${formatNpmInstallCommand(install, target.spec)} && pdd setup`,
          currentVersion,
          currentVersion,
        );
      }
    }
    let spec = target.spec;
    let attempt = runNpmAction(spawnImpl, install, 'install', spec, env, 120000);
    if (!attempt.ok && !/\bEEXIST\b/.test(attempt.raw) && target.fallbackSpec) {
      spec = target.fallbackSpec;
      attempt = runNpmAction(spawnImpl, install, 'install', spec, env, 120000);
    }
    if (!attempt.ok) {
      const retryInstall = formatNpmInstallCommand(install, spec);
      if (/\bEEXIST\b/.test(attempt.raw)) {
        return fail(`pdd upgrade hit an existing bin/pdd collision at ${join(install.prefix, 'bin/pdd')} (${attempt.detail}).\n  Invariant: global npm refuses to overwrite an unscoped "pdd" or foreign bin/pdd binary.\n  Fix: Run \`npm uninstall -g pdd\` to remove the conflicting package.\n  Rerun: ${retryInstall} && pdd setup`, currentVersion, currentVersion);
      }
      return fail(`pdd upgrade failed to install ${spec} (${attempt.detail}). To retry, run: ${retryInstall} && pdd setup`, currentVersion, currentVersion);
    }
    cliUpdated = true;
  }

  const targetPkgRoot = resolveInstalledRoot(install, install.realPackageRoot, fs);
  const toVersion = readJson(join(targetPkgRoot, 'package.json'), fs)?.version ?? (cliUpdated && target.version ? target.version : currentVersion);
  const stateRoot = ports.stateHome ? join(ports.stateHome, 'pdd') : resolvePddStateBase(env);
  for (const cachePath of new Set([join(stateRoot, 'release-check.json'), join(resolvePddStateBase(env), 'release-check.json')])) {
    try { fs.rmSync(cachePath, { force: true }); } catch {}
  }

  // Delegate post-upgrade skill & stale-MCP sync to the newly installed binary (`pdd setup --upgrade`)
  // so post-upgrade skill layouts never clash with pre-upgrade in-RAM PDD_SKILL_NAMES (#3645).
  const binEntry = ports.skillsInstall ? null : resolveInstalledBinEntry(targetPkgRoot, fs);
  let usedDelegatedSetup = false;
  let updatedSkills = [], skippedSkills = [], failedSkills = [], updatedMcp = [], delegatedLines = [];
  let delegatedErr = '';

  if (binEntry) {
    const baseChildEnv = isVolta ? scrubVoltaEnv(env, install.voltaHome) : { ...env };
    const childEnv = {
      ...baseChildEnv,
      ...(resolvedHome ? { HOME: resolvedHome } : {}),
      ...(ports.stateHome && !baseChildEnv.PDD_STATE_DIR ? { PDD_STATE_DIR: stateRoot } : {}),
      PDD_NO_UPDATE_CHECK: '1',
    };
    const nodeBin = ports.nodePath ?? process.execPath;
    const setupRes = spawnImpl(nodeBin, [binEntry, 'setup', '--upgrade'], {
      cwd,
      env: childEnv,
      encoding: 'utf8',
      timeout: 60000,
    });
    const setupCode = setupRes?.status ?? setupRes?.code ?? ((setupRes?.error || setupRes?.signal) ? 1 : 0);
    const setupOut = String(setupRes?.stdout ?? '');
    const setupErr = String(setupRes?.stderr ?? '');
    const unknownUpgradeFlag = setupCode === 2 && /--upgrade/.test(setupErr);
    if (!unknownUpgradeFlag) {
      usedDelegatedSetup = true;
      const parsed = parseSetupUpgradeOutput(setupOut);
      delegatedLines = parsed.lines;
      updatedSkills = parsed.updatedSkills;
      skippedSkills = parsed.skippedSkills;
      updatedMcp = parsed.updatedMcp;
      delegatedErr = setupErr.trim();
      if (setupCode !== 0) {
        const sigNote = setupRes?.signal ? `killed by ${setupRes.signal}` : '';
        const detail = (delegatedErr || setupRes?.error?.message || sigNote || `pdd setup --upgrade exited ${setupCode}`).split(/\r?\n/)[0];
        failedSkills.push({ folder: resolvedHome || targetPkgRoot, reason: detail, recovery: 'pdd setup' });
      }
    }
  }

  if (!usedDelegatedSetup) {
    const skillsModule = ports.skillsInstall ?? await import('../skills-install.mjs');
    const fallback = runFallbackSkillsSync(skillsModule, {
      targetPkgRoot, resolvedHome, env, stateRoot, cwd, fs,
    });
    updatedSkills = fallback.updatedSkills;
    skippedSkills = fallback.skippedSkills;
    failedSkills = fallback.failedSkills;
  }

  if (cliUpdated) writeLine(stdout, `Upgraded pdd ${currentVersion} -> ${toVersion} (${main ? 'main' : target.ref}).`);
  else if (!updatedSkills.length && !updatedMcp.length && !skippedSkills.length && !failedSkills.length && !delegatedLines.length) {
    writeLine(stdout, `pdd ${toVersion} is already up to date. PDD skills are current.`);
  } else {
    writeLine(stdout, `pdd ${toVersion} is already up to date.`);
  }

  if (usedDelegatedSetup) {
    for (const outLine of delegatedLines) writeLine(stdout, outLine);
    if (delegatedErr) {
      for (const errLine of delegatedErr.split(/\r?\n/).filter(Boolean)) writeLine(stderr, errLine);
    } else if (failedSkills.length) {
      for (const item of failedSkills) writeLine(stderr, `Failed to update PDD skills in ${item.folder} (${item.reason}). To recover, run: ${item.recovery}`);
    }
  } else {
    if (updatedSkills.length) writeLine(stdout, `Updated PDD skills to ${toVersion} in: ${updatedSkills.join(', ')}.`);
    for (const item of skippedSkills) writeLine(stdout, `Skipped ${item.stale === 'differs' ? 'customized' : 'unmarked'} PDD skills in ${item.folder}${item.details ? ` (${item.details})` : ''} (preserved without overwriting). To update unmarked skills, run: ${item.recovery}`);
    for (const item of failedSkills) writeLine(stderr, `Failed to update PDD skills in ${item.folder} (${item.reason}). To recover, run: ${item.recovery}`);
  }

  return { exitCode: failedSkills.length > 0 ? 1 : 0, cliUpdated, fromVersion: currentVersion, toVersion, updatedSkills, skippedSkills, failedSkills };
}
