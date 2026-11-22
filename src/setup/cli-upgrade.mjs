// Prompt: prompts/cli/cli-upgrade.prompt.md
import { spawnSync as nativeSpawnSync } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { isNewerRelease, parseReleaseVersion, pickLatestRelease } from '../release-notice.mjs';
import { PACKAGE_ROOT } from '../shared/package-root.mjs';
import { resolvePddStateBase } from '../shared/state-dir.mjs';
import * as defaultSkillsInstall from '../skills-install.mjs';

const quote = text => `'${String(text).replace(/'/g, "'\\''")}'`;
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

export function classifyInstallKind(packageRoot, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const uid = ports.uid !== undefined ? ports.uid : (typeof process.getuid === 'function' ? process.getuid() : null);
  if (typeof packageRoot !== 'string' || !packageRoot) return { kind: 'invalid' };
  let real, info;
  try {
    real = fs.realpathSync(packageRoot);
    info = fs.statSync(real);
    if (!info.isDirectory()) return { kind: 'invalid' };
  } catch { return { kind: 'invalid' }; }
  const norm = real.replace(/\\/g, '/').replace(/\/+$/, '');
  if (fs.existsSync(join(real, '.git'))) return { kind: 'git-checkout', realPackageRoot: real, hint: 'git pull && npm install' };
  if (/(?:^|\/)(?:site-packages|dist-packages)\/(?:pdd|pdd_cli|pdd-cli)(?:\/|$)/.test(norm)) return { kind: 'pypi', realPackageRoot: real, hint: 'pip install -U pdd-cli' };
  if (/(?:^|\/)\.pnpm(?:\/|$)|\/pnpm\/global(?:\/|$)/.test(norm)) return { kind: 'pnpm', realPackageRoot: real, hint: 'pnpm add -g @promptdriven/pdd@latest' };
  if (/(?:^|\/)_npx(?:\/|$)/.test(norm)) return { kind: 'npx', realPackageRoot: real, hint: 'npm install -g @promptdriven/pdd && pdd setup' };
  const match = /^(.*?)\/(?:lib\/)?node_modules\/(?:@promptdriven\/pdd|pdd)$/.exec(norm);
  if (!match?.[1]) return { kind: 'unknown', realPackageRoot: real, hint: 'npm install -g @promptdriven/pdd && pdd setup' };
  const prefix = match[1];
  // Only classify as local-project when parent holds package.json; never check prefix/.git (Apple Silicon /opt/homebrew/.git is global!).
  if (fs.existsSync(join(prefix, 'package.json'))) {
    return { kind: 'local-project', prefix, realPackageRoot: real, hint: 'npm install @promptdriven/pdd@latest' };
  }
  try {
    const prefixInfo = fs.statSync(prefix);
    if (uid !== null && ((Number.isInteger(info.uid) && info.uid !== uid) || (Number.isInteger(prefixInfo.uid) && prefixInfo.uid !== uid))) {
      return { kind: 'unowned-prefix', prefix, realPackageRoot: real, hint: 'npm install -g @promptdriven/pdd && pdd setup' };
    }
  } catch { return { kind: 'invalid', realPackageRoot: real }; }
  return { kind: 'npm-global', prefix, realPackageRoot: real };
}

export function detectGlobalInstallPrefix(packageRoot, ports = {}) {
  const c = classifyInstallKind(packageRoot, ports);
  return c.kind === 'npm-global' ? { prefix: c.prefix, realPackageRoot: c.realPackageRoot } : null;
}

function resolveInstalledRoot(prefix, fallbackRoot, fs) {
  for (const rel of ['lib/node_modules/@promptdriven/pdd', 'node_modules/@promptdriven/pdd', 'lib/node_modules/pdd', 'node_modules/pdd']) {
    const candidate = join(prefix, rel);
    try { if (fs.statSync(join(candidate, 'package.json')).isFile()) return candidate; } catch {}
  }
  return fallbackRoot;
}

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
    if ((reply?.status ?? reply?.code ?? (reply?.error ? 1 : 0)) !== 0) {
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

function runNpmInstall(spawnImpl, prefix, spec, env) {
  const res = spawnImpl('npm', ['install', '-g', '--prefix', prefix, '--ignore-scripts', '--no-audit', '--no-fund', spec], { encoding: 'utf8', timeout: 120000, env });
  const ok = (res?.status ?? res?.code ?? (res?.error ? 1 : 0)) === 0;
  const raw = `${res?.stderr || ''}\n${res?.stdout || ''}\n${res?.error?.message || ''}`;
  const detail = (res?.stderr || res?.stdout || res?.error?.message || 'npm install failed').trim().split('\n')[0];
  return { ok, raw, detail };
}

export async function runCliUpgrade({
  env = process.env, stdout = process.stdout, stderr = process.stderr, main = false,
  spawnSyncImpl, fetchImpl, packageRoot = PACKAGE_ROOT, home, cwd = process.cwd(),
} = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const resolvedHome = home ?? env.HOME ?? (ports.homedir ?? homedir)();
  const install = classifyInstallKind(packageRoot, { fs, uid: ports.uid });
  const fail = (msg, fromVersion, toVersion) => {
    writeLine(stderr, msg);
    return { exitCode: 1, cliUpdated: false, ...(fromVersion ? { fromVersion, toVersion } : {}), updatedSkills: [], skippedSkills: [], failedSkills: [] };
  };
  if (install.kind !== 'npm-global') {
    return fail(`pdd upgrade skips ${SKIP_LABELS[install.kind] ?? 'this installation'} (${packageRoot}).\n  Invariant: pdd upgrade modifies only a user-owned global npm installation of @promptdriven/pdd.\n  Fix: Run \`${install.hint ?? 'npm install -g @promptdriven/pdd && pdd setup'}\`.\n  Rerun: pdd --version`);
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
  const quotedPrefix = quote(install.prefix);
  let cliUpdated = false;
  if (main || isNewerRelease(target.version, currentVersion)) {
    let spec = target.spec;
    let attempt = runNpmInstall(spawnImpl, install.prefix, spec, env);
    if (!attempt.ok && !/\bEEXIST\b/.test(attempt.raw) && target.fallbackSpec) {
      spec = target.fallbackSpec;
      attempt = runNpmInstall(spawnImpl, install.prefix, spec, env);
    }
    if (!attempt.ok) {
      if (/\bEEXIST\b/.test(attempt.raw)) {
        return fail(`pdd upgrade hit an existing bin/pdd collision at ${join(install.prefix, 'bin/pdd')} (${attempt.detail}).\n  Invariant: global npm refuses to overwrite an unscoped "pdd" or foreign bin/pdd binary.\n  Fix: Run \`npm uninstall -g pdd\` to remove the conflicting package.\n  Rerun: npm install -g --prefix ${quotedPrefix} --ignore-scripts ${spec} && pdd setup`, currentVersion, currentVersion);
      }
      return fail(`pdd upgrade failed to install ${spec} (${attempt.detail}). To retry, run: npm install -g --prefix ${quotedPrefix} --ignore-scripts ${spec} && pdd setup`, currentVersion, currentVersion);
    }
    cliUpdated = true;
  }

  const targetPkgRoot = resolveInstalledRoot(install.prefix, install.realPackageRoot, fs);
  const toVersion = readJson(join(targetPkgRoot, 'package.json'), fs)?.version ?? (cliUpdated && target.version ? target.version : currentVersion);
  const stateRoot = ports.stateHome ? join(ports.stateHome, 'pdd') : resolvePddStateBase(env);
  try { fs.rmSync(join(stateRoot, 'release-check.json'), { force: true }); } catch {}

  const failedSkills = [], updatedSkills = [], skippedSkills = [];
  const skillsModule = ports.skillsInstall ?? defaultSkillsInstall;
  try {
    const { updated } = skillsModule.syncOwnedUserSkills({
      packageRoot: targetPkgRoot, home: resolvedHome, claudeConfigDir: env.CLAUDE_CONFIG_DIR, codexHome: env.CODEX_HOME, stateRoot, force: true,
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
        if (!row.found || !row.stale) continue;
        const key = canonicalDir(row.found, fs);
        if (failedCanon.has(key) || seenSkip.has(key)) continue;
        seenSkip.add(key);
        const details = (row.staleSkills ?? []).map(({ name, state, version }) => state === 'older' ? `${name} is ${version ?? 'unknown'}` : `${name} differs (version ${version ?? 'unknown'})`).join(', ');
        skippedSkills.push({ folder: row.found, stale: row.stale, details, recovery: row.scope === 'project' ? "npx skills add promptdriven/pdd --skill '*'" : "npx skills add promptdriven/pdd -g --skill '*'" });
      }
    } catch {}
  }

  if (cliUpdated) writeLine(stdout, `Upgraded pdd ${currentVersion} -> ${toVersion} (${main ? 'main' : target.ref}).`);
  else if (!updatedSkills.length && !skippedSkills.length && !failedSkills.length) writeLine(stdout, `pdd ${toVersion} is already up to date. PDD skills are current.`);
  else writeLine(stdout, `pdd ${toVersion} is already up to date.`);
  if (updatedSkills.length) writeLine(stdout, `Updated PDD skills to ${toVersion} in: ${updatedSkills.join(', ')}.`);
  for (const item of skippedSkills) writeLine(stdout, `Skipped ${item.stale === 'differs' ? 'customized' : 'unmarked'} PDD skills in ${item.folder}${item.details ? ` (${item.details})` : ''} (preserved without overwriting). To update unmarked skills, run: ${item.recovery}`);
  for (const item of failedSkills) writeLine(stderr, `Failed to update PDD skills in ${item.folder} (${item.reason}). To recover, run: ${item.recovery}`);
  return { exitCode: failedSkills.length > 0 ? 1 : 0, cliUpdated, fromVersion: currentVersion, toVersion, updatedSkills, skippedSkills, failedSkills };
}
