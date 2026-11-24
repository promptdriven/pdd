// Prompt: prompts/cli/path-diagnostic.prompt.md

import { spawnSync as nativeSpawnSync } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { homedir as nativeHomedir } from 'node:os';
import { basename, delimiter, dirname, isAbsolute, join, resolve } from 'node:path';
import { classifyInstallKind, quoteShellArg, resolveInstalledRoot } from './shared/install-kind.mjs';
import { PACKAGE_ROOT } from './shared/package-root.mjs';

const DEFAULT_TIMEOUT_MS = 1500;
const MIN_TIMEOUT_MS = 100;
const MAX_TIMEOUT_MS = 5000;
const MAX_WRAPPER_BYTES = 8192;
const DEFAULT_MAX_VERSION_DIRS = 32;
const DEFAULT_MAX_PROBES = 12;

// Constant probe script — never interpolate paths or user values into shell strings.
// Rejects aliases and shell functions in-shell; emits only paths starting with /, ./, or ../.
const LOGIN_PROBE_CMD = 'p=$(command -v pdd 2>/dev/null) && case "$p" in /*|./*|../*) printf "\\n__PDD_WHICH__=%s\\n" "$p" ;; esac';
const LOGIN_WHICH_PREFIX = '__PDD_WHICH__=';

const clean = text => String(text ?? '').replace(/\x1b\[[0-?]*[ -/]*[@-~]/g, '').replace(/[\x00-\x1f\x7f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 240);
const normPath = (value, platform = process.platform) => {
  const normalized = String(value ?? '').replace(/\\/g, '/').replace(/\/+$/, '');
  return platform === 'win32' ? normalized.toLowerCase() : normalized;
};

function safeQuoteShellPath(targetPath) {
  const str = String(targetPath ?? '');
  if (!/[\x00-\x1f\x7f]/.test(str)) return quoteShellArg(str);
  // POSIX ANSI-C quoting neutralizes raw control chars, newlines, and ANSI escapes safely.
  let out = "$'";
  for (let i = 0; i < str.length; i++) {
    const ch = str[i];
    const code = str.charCodeAt(i);
    if (ch === '\\') out += '\\\\';
    else if (ch === "'") out += "\\'";
    else if (ch === '\n') out += '\\n';
    else if (ch === '\r') out += '\\r';
    else if (ch === '\t') out += '\\t';
    else if (code < 0x20 || code === 0x7f) out += `\\x${code.toString(16).padStart(2, '0')}`;
    else out += ch;
  }
  return `${out}'`;
}

function resolveSafeHome(explicitHome, env, homedirFn = nativeHomedir, platform = process.platform) {
  const isValidAbs = val => {
    if (typeof val !== 'string') return false;
    const trimmed = val.trim();
    if (!trimmed) return false;
    return platform === 'win32' ? /^[A-Za-z]:[\\/]/.test(trimmed) || isAbsolute(trimmed) : isAbsolute(trimmed);
  };
  if (isValidAbs(explicitHome)) return explicitHome.trim();
  if (isValidAbs(env?.HOME)) return env.HOME.trim();
  if (platform === 'win32' && isValidAbs(env?.USERPROFILE)) return env.USERPROFILE.trim();
  try {
    const fallback = homedirFn();
    return isValidAbs(fallback) ? fallback.trim() : '';
  } catch {
    return '';
  }
}

export function shortenHomePath(targetPath, home) {
  if (typeof targetPath !== 'string' || !targetPath) return '';
  if (typeof home !== 'string' || !home) return targetPath;
  const trimmedHome = home.length > 1 ? home.replace(/[\\/]+$/, '') : home;
  if (!trimmedHome || trimmedHome === '/') return targetPath;
  if (targetPath === trimmedHome) return '~';
  if (targetPath.startsWith(`${trimmedHome}/`) || targetPath.startsWith(`${trimmedHome}\\`)) {
    return `~${targetPath.slice(trimmedHome.length)}`;
  }
  return targetPath;
}

function safeRealpath(target, fs = nativeFs) {
  try { return fs.realpathSync(target); } catch { return null; }
}

function isExecutableFile(target, fs = nativeFs) {
  try {
    fs.accessSync(target, fs.constants?.X_OK ?? nativeFs.constants.X_OK);
    return fs.statSync(target).isFile();
  } catch { return false; }
}

function readSmallText(target, maxBytes, fs = nativeFs) {
  try {
    const st = fs.statSync(target);
    if (!st.isFile() || st.size > maxBytes) return null;
    return fs.readFileSync(target, 'utf8');
  } catch { return null; }
}

function readJsonSafe(target, fs = nativeFs) {
  try {
    const parsed = JSON.parse(fs.readFileSync(target, 'utf8'));
    return parsed && typeof parsed === 'object' && !Array.isArray(parsed) ? parsed : null;
  } catch { return null; }
}

function clampTimeout(value) {
  const n = Number(value);
  if (!Number.isFinite(n)) return DEFAULT_TIMEOUT_MS;
  return Math.min(MAX_TIMEOUT_MS, Math.max(MIN_TIMEOUT_MS, Math.round(n)));
}

function pathList(env, cwd, platform) {
  const raw = env?.PATH ?? (platform === 'win32' ? env?.Path : undefined);
  if (typeof raw !== 'string' || !raw) return [];
  const sep = platform === 'win32' ? ';' : delimiter;
  return raw.split(sep).map(entry => {
    const stripped = platform === 'win32' ? entry.trim().replace(/^"(.*)"$/, '$1') : entry;
    return resolve(cwd, stripped || '.');
  });
}

function executableNames(platform) {
  return platform === 'win32' ? ['pdd.cmd', 'pdd.exe', 'pdd'] : ['pdd'];
}

function candidates(cwd, env) {
  const platform = process.platform;
  let listed;
  if (platform !== 'win32') {
    try {
      const reply = nativeSpawnSync('which', ['-a', 'pdd'], { cwd, env, encoding: 'utf8', timeout: 2000, maxBuffer: 65536, stdio: ['ignore', 'pipe', 'pipe'] });
      if (!reply.error && reply.status === 0) listed = reply.stdout.split(/\r?\n/).filter(Boolean).map(p => resolve(cwd, p));
    } catch { /* A missing which still permits local PATH discovery. */ }
  }
  if (!listed) {
    listed = [];
    for (const dir of pathList(env, cwd, platform)) {
      for (const name of executableNames(platform)) listed.push(join(dir, name));
    }
  }
  return [...new Set(listed)].filter(p => isExecutableFile(p, nativeFs));
}

function findUnscopedNpmPdd(cwd, env, paths, fs = nativeFs, platform = process.platform) {
  const dirs = new Set();
  for (const dir of pathList(env, cwd, platform)) {
    dirs.add(resolve(dir, '../lib/node_modules/pdd'));
    dirs.add(resolve(dir, 'node_modules/pdd'));
  }
  for (const p of paths) {
    const real = safeRealpath(p, fs) ?? p;
    const match = /^(.*\/node_modules\/pdd)(?:\/|$)/i.exec(normPath(real, platform));
    if (match) dirs.add(real.slice(0, match[1].length));
  }
  let foreign = null;
  let legacy = null;
  for (const pkgDir of dirs) {
    const metadata = readJsonSafe(join(pkgDir, 'package.json'), fs);
    if (metadata?.name === 'pdd') {
      if (isExecutableFile(join(pkgDir, 'bin/pdd.mjs'), fs)) legacy ??= pkgDir;
      else foreign ??= pkgDir;
    }
  }
  return { foreign, legacy };
}

function compareSemverDesc(a, b) {
  const parts = s => String(s).replace(/^v/i, '').split('.').map(n => parseInt(n, 10) || 0);
  const pa = parts(a);
  const pb = parts(b);
  for (let i = 0; i < 3; i++) {
    if ((pa[i] ?? 0) !== (pb[i] ?? 0)) return (pb[i] ?? 0) - (pa[i] ?? 0);
  }
  return b.localeCompare(a);
}

function boundedSubdirs(parentDir, limit, fs) {
  try {
    const entries = fs.readdirSync(parentDir);
    return entries.filter(name => typeof name === 'string' && name && !name.startsWith('.'))
      .sort(compareSemverDesc)
      .slice(0, limit);
  } catch { return []; }
}

function findEnclosingPddPackage(realBinPath, fs, platform = process.platform) {
  if (typeof realBinPath !== 'string' || !realBinPath) return null;
  const dirs = [dirname(realBinPath), dirname(dirname(realBinPath))];
  for (const dir of dirs) {
    if (!dir || dir === dirname(dir)) continue;
    const pkg = readJsonSafe(join(dir, 'package.json'), fs);
    if (!pkg) continue;
    const binRel = typeof pkg.bin === 'string' ? pkg.bin : pkg.bin?.pdd;
    const matchesBin = typeof binRel === 'string'
      && normPath(safeRealpath(resolve(dir, binRel), fs) ?? resolve(dir, binRel), platform) === normPath(safeRealpath(realBinPath, fs) ?? realBinPath, platform);
    if (pkg.name === '@promptdriven/pdd' || pkg.name === 'pdd' || matchesBin) {
      return { packageRoot: safeRealpath(dir, fs) ?? dir, pkg };
    }
  }
  return null;
}

function resolveVoltaPackageInHome(voltaHome, isShimBinary, fs) {
  const binMeta = readJsonSafe(join(voltaHome, 'tools', 'user', 'bins', 'pdd.json'), fs);
  const pkgNames = [];
  if (typeof binMeta?.package === 'string' && binMeta.package) pkgNames.push(binMeta.package);
  if (isShimBinary && !pkgNames.length) pkgNames.push('@promptdriven/pdd', 'pdd');

  for (const pkgName of pkgNames) {
    const rels = [
      join('tools', 'image', 'packages', pkgName, 'lib', 'node_modules', pkgName),
      join('tools', 'image', 'packages', pkgName, 'node_modules', pkgName),
      join('tools', 'image', 'packages', pkgName),
    ];
    for (const rel of rels) {
      const root = join(voltaHome, rel);
      const targetBin = join(root, 'bin', 'pdd.mjs');
      if (isExecutableFile(targetBin, fs) || readJsonSafe(join(root, 'package.json'), fs)) {
        const canonBin = safeRealpath(targetBin, fs) ?? targetBin;
        const canonRoot = safeRealpath(root, fs) ?? root;
        return { realPath: canonBin, packageRoot: canonRoot, voltaHome, packageName: pkgName, wrapperKind: 'volta' };
      }
    }
  }

  if (isShimBinary) {
    const root = resolveInstalledRoot({ kind: 'volta', voltaHome }, null, fs);
    if (root) {
      const targetBin = join(root, 'bin', 'pdd.mjs');
      return {
        realPath: safeRealpath(targetBin, fs) ?? targetBin,
        packageRoot: safeRealpath(root, fs) ?? root,
        voltaHome,
        packageName: readJsonSafe(join(root, 'package.json'), fs)?.name ?? null,
        wrapperKind: 'volta',
      };
    }
  }
  return null;
}

function resolveVoltaBinTarget(binPath, realPath, { fs, env, home, platform = process.platform }) {
  const normReal = normPath(realPath, platform);
  const isShimBinary = /\/volta-shim(?:\.exe)?$/i.test(normReal) || /\/bin\/volta(?:\.exe)?$/i.test(normReal);
  const binDir = dirname(binPath);
  const parentOfBin = dirname(binDir);
  const envVolta = typeof env?.VOLTA_HOME === 'string' && env.VOLTA_HOME.trim() ? env.VOLTA_HOME.trim().replace(/[\\/]+$/, '') : null;
  const defaultVolta = home ? join(home, '.volta') : null;

  // Build candidate Volta home roots prioritizing binPath's own parent / VOLTA_HOME / ~/.volta
  // BEFORE realPath's parent so `brew install volta` (`~/.volta/bin/pdd -> /opt/homebrew/Cellar/volta/.../volta-shim`)
  // resolves `~/.volta/tools/user/bins/pdd.json` cleanly instead of looking under Cellar.
  const candidatesList = [];
  const seenCanon = new Set();
  const pushHome = candidate => {
    if (typeof candidate !== 'string' || !candidate) return;
    const canon = normPath(safeRealpath(candidate, fs) ?? candidate, platform);
    if (seenCanon.has(canon)) return;
    seenCanon.add(canon);
    candidatesList.push(candidate);
  };

  const parentIsBinParent = basename(binDir).toLowerCase() === 'bin';
  if (parentIsBinParent) {
    const canonParent = normPath(safeRealpath(parentOfBin, fs) ?? parentOfBin, platform);
    const matchesKnown = [envVolta, defaultVolta].filter(Boolean)
      .some(v => normPath(safeRealpath(v, fs) ?? v, platform) === canonParent);
    if (matchesKnown || /(?:^|\/)\.volta$/i.test(normPath(parentOfBin, platform)) || isShimBinary) {
      pushHome(parentOfBin);
    }
  }
  if (isShimBinary) {
    pushHome(envVolta);
    pushHome(defaultVolta);
    if (basename(dirname(realPath)).toLowerCase() === 'bin') pushHome(dirname(dirname(realPath)));
  }

  if (candidatesList.length === 0) return null;

  for (const vh of candidatesList) {
    const resolved = resolveVoltaPackageInHome(vh, isShimBinary, fs);
    if (resolved) return resolved;
  }

  return { realPath, packageRoot: null, voltaHome: candidatesList[0], packageName: null, wrapperKind: 'volta' };
}

function resolvePnpmWrapperTarget(binPath, realPath, fs, platform = process.platform) {
  const normBin = normPath(binPath, platform);
  const normReal = normPath(realPath, platform);
  const looksPnpmPath = /(?:^|\/)(?:library\/pnpm|\.local\/share\/pnpm|pnpm)(?:\/|$)/i.test(normBin)
    || /(?:^|\/)(?:\.pnpm|pnpm\/global)(?:\/|$)/i.test(normReal);
  const text = readSmallText(realPath, MAX_WRAPPER_BYTES, fs);
  if (!text) return looksPnpmPath ? { realPath, packageRoot: null, wrapperKind: 'pnpm' } : null;

  // Match POSIX pnpm wrappers (`$basedir/...` / `${basedir}/...`), Windows cmd-shim (`%dp0%\...`, `%~dp0\...`), and quoted absolute paths.
  const baseDirs = [...new Set([dirname(realPath), dirname(binPath)])];
  const patterns = [
    { re: /["']\$\{?basedir\}?[\\/]([^"'\r\n`]+?[\\/]bin[\\/]pdd\.mjs)["']/i, rel: true },
    { re: /\$\{?basedir\}?[\\/]([^"'\s`]+?[\\/]bin[\\/]pdd\.mjs)/i, rel: true },
    { re: /%(?:~dp0|dp0%)[\\/]([^"'\r\n]+?[\\/]bin[\\/]pdd\.mjs)/i, rel: true },
    { re: /["']((?:\/|[A-Za-z]:[\\/])[^"'\r\n]+?[\\/]bin[\\/]pdd\.mjs)["']/i, rel: false },
  ];
  for (const { re, rel } of patterns) {
    const match = re.exec(text);
    if (!match?.[1]) continue;
    const candidatesToTry = rel
      ? baseDirs.map(baseDir => resolve(baseDir, match[1].replace(/\\/g, '/')))
      : [match[1]];
    for (const candidate of candidatesToTry) {
      try {
        if (fs.statSync(candidate).isFile()) {
          const canon = safeRealpath(candidate, fs) ?? candidate;
          const isPnpm = looksPnpmPath || /(?:^|\/)(?:\.pnpm|pnpm\/global)(?:\/|$)/i.test(normPath(canon, platform));
          return { realPath: canon, packageRoot: null, wrapperKind: isPnpm ? 'pnpm' : null };
        }
      } catch { /* Unresolved target falls back to wrapper itself. */ }
    }
  }
  return looksPnpmPath ? { realPath, packageRoot: null, wrapperKind: 'pnpm' } : null;
}

export function resolveCanonicalPddTarget(binPath, { fs = nativeFs, env = process.env, home, platform = process.platform, homedir = nativeHomedir } = {}) {
  const safeHome = resolveSafeHome(home, env, homedir, platform);
  const realPath = safeRealpath(binPath, fs) ?? binPath;
  const volta = resolveVoltaBinTarget(binPath, realPath, { fs, env, home: safeHome, platform });
  if (volta) return volta;
  const pnpm = resolvePnpmWrapperTarget(binPath, realPath, fs, platform);
  if (pnpm) return pnpm;
  return { realPath, packageRoot: null, voltaHome: null, packageName: null, wrapperKind: null };
}

function isPythonExecutable(binPath, realPath, { fs, env, platform }) {
  const normBin = normPath(binPath, platform);
  const normReal = normPath(realPath, platform);
  const condaPrefix = typeof env?.CONDA_PREFIX === 'string' && env.CONDA_PREFIX.trim() ? normPath(env.CONDA_PREFIX.trim(), platform) : null;
  const virtualEnv = typeof env?.VIRTUAL_ENV === 'string' && env.VIRTUAL_ENV.trim() ? normPath(env.VIRTUAL_ENV.trim(), platform) : null;

  if (condaPrefix && (normBin.startsWith(`${condaPrefix}/`) || normReal.startsWith(`${condaPrefix}/`))) return true;
  if (virtualEnv && (normBin.startsWith(`${virtualEnv}/`) || normReal.startsWith(`${virtualEnv}/`))) return true;
  if (/(?:^|\/)(?:miniconda\d*|anaconda\d*|miniforge\d*|mambaforge\d*|conda|pipx\/venvs|uv\/tools|site-packages|dist-packages|\.venv|venv|virtualenv)(?:\/|$)/i.test(normBin)) return true;
  if (/(?:^|\/)(?:miniconda\d*|anaconda\d*|miniforge\d*|mambaforge\d*|conda|pipx\/venvs|uv\/tools|site-packages|dist-packages|\.venv|venv|virtualenv)(?:\/|$)/i.test(normReal)) return true;

  const head = readSmallText(realPath, 2048, fs);
  if (head) {
    const firstLine = head.split(/\r?\n/, 1)[0] ?? '';
    if (/^#!.*\bpython[0-9.]*\b/i.test(firstLine)) return true;
    if (/(?:from|import)\s+pdd(?:_cli|\b)/.test(head)) return true;
  }
  return false;
}

function extractManagerPrefix(targetPath, platform = process.platform) {
  const norm = normPath(targetPath, platform);
  const rawNorm = String(targetPath ?? '').replace(/\\/g, '/').replace(/\/+$/, '');
  const patterns = [
    /^(.*\/\.nvm\/versions\/node\/[^/]+)\/bin\/[^/]+$/i,
    /^(.*\/fnm\/node-versions\/[^/]+\/installation)\/bin\/[^/]+$/i,
    /^(.*\/fnm\/aliases\/[^/]+)\/bin\/[^/]+$/i,
    /^(.*\/fnm\/current)\/bin\/[^/]+$/i,
    /^(.*\/mise\/installs\/node\/[^/]+)\/bin\/[^/]+$/i,
    /^(.*\/\.?asdf\/installs\/nodejs\/[^/]+)\/bin\/[^/]+$/i,
    /^(.*\/\.npm-global)\/bin\/[^/]+$/i,
    /^(\/opt\/homebrew|\/usr\/local)\/(?:lib\/)?node_modules\/(?:@promptdriven\/pdd|pdd)(?:\/.*)?$/i,
  ];
  for (const re of patterns) {
    const match = re.exec(norm);
    if (match?.[1]) return rawNorm.slice(0, match[1].length);
  }
  return null;
}

function classifyBinaryInstall({ binPath, realPath, resolved, fs, env, uid, platform }) {
  const pkgInfo = resolved.packageRoot
    ? { packageRoot: resolved.packageRoot, pkg: readJsonSafe(join(resolved.packageRoot, 'package.json'), fs) }
    : findEnclosingPddPackage(realPath, fs, platform);

  const pkg = pkgInfo?.pkg ?? null;
  const packageName = pkg?.name ?? resolved.packageName ?? null;
  const packageVersion = typeof pkg?.version === 'string' && pkg.version ? pkg.version : null;

  if (pkgInfo?.packageRoot) {
    const classified = classifyInstallKind(pkgInfo.packageRoot, { fs, uid, env, platform });
    if (classified.kind === 'git-checkout') {
      return { kind: 'git-checkout', prefix: pkgInfo.packageRoot, packageName, version: packageVersion };
    }
    if (classified.kind === 'volta') {
      return {
        kind: packageName === 'pdd' ? 'legacy-unscoped-pdd' : 'volta',
        prefix: classified.voltaHome,
        voltaHome: classified.voltaHome,
        packageName: packageName ?? classified.packageName,
        version: packageVersion,
      };
    }
    if (classified.kind === 'pnpm' || resolved.wrapperKind === 'pnpm') {
      return { kind: 'pnpm', prefix: null, packageName, version: packageVersion };
    }
    if (classified.kind === 'pypi') {
      return { kind: 'pypi', prefix: null, packageName, version: packageVersion };
    }
    if (packageName === 'pdd') {
      return {
        kind: 'legacy-unscoped-pdd',
        prefix: classified.prefix ?? extractManagerPrefix(realPath, platform) ?? extractManagerPrefix(binPath, platform),
        packageName: 'pdd',
        version: packageVersion,
      };
    }
    // Only treat Homebrew Cellar/pdd formulas as Homebrew — never Cellar/node/.../node_modules/@promptdriven/pdd.
    if (/(?:^|\/)(?:cellar|linuxbrew\/cellar)\/pdd(?:\/|$)/i.test(normPath(realPath, platform))) {
      return { kind: 'homebrew', prefix: null, packageName, version: packageVersion };
    }
    if (classified.kind === 'npm-global' || classified.kind === 'unowned-prefix') {
      return { kind: 'npm-global', prefix: classified.prefix ?? null, packageName, version: packageVersion };
    }
    if (classified.kind === 'local-project' || classified.kind === 'npx') {
      return { kind: 'other', prefix: classified.prefix ?? null, packageName, version: packageVersion };
    }
  }

  // Fallback heuristics when no enclosing package.json is present (standalone binaries, Python scripts, shims).
  if (resolved.wrapperKind === 'volta') {
    return { kind: 'volta', prefix: resolved.voltaHome ?? null, voltaHome: resolved.voltaHome ?? null, packageName, version: packageVersion };
  }
  if (resolved.wrapperKind === 'pnpm') {
    return { kind: 'pnpm', prefix: null, packageName, version: packageVersion };
  }
  if (isPythonExecutable(binPath, realPath, { fs, env, platform })) {
    return { kind: 'pypi', prefix: dirname(dirname(binPath)), packageName: 'pdd-cli', version: packageVersion };
  }
  const normBin = normPath(binPath, platform);
  const normReal = normPath(realPath, platform);
  if (/(?:^|\/)(?:opt\/homebrew|usr\/local\/cellar|home\/linuxbrew)(?:\/|$)/i.test(normBin)
    || /(?:^|\/)(?:opt\/homebrew|usr\/local\/cellar|home\/linuxbrew)(?:\/|$)/i.test(normReal)) {
    return { kind: 'homebrew', prefix: null, packageName, version: packageVersion };
  }
  const mgrPrefix = extractManagerPrefix(realPath, platform) ?? extractManagerPrefix(binPath, platform);
  if (mgrPrefix) {
    return { kind: 'npm-global', prefix: mgrPrefix, packageName, version: packageVersion };
  }
  return { kind: 'other', prefix: null, packageName, version: packageVersion };
}

function remediationForInstall(inst, { home, platform = process.platform }) {
  if (inst.isCurrent) return null;
  const normBin = normPath(inst.path, platform);
  const normReal = normPath(inst.realPath, platform);
  switch (inst.kind) {
    case 'volta':
      return inst.packageName === 'pdd' ? 'volta uninstall pdd' : 'volta uninstall @promptdriven/pdd';
    case 'legacy-unscoped-pdd':
      if (inst.voltaHome) return 'volta uninstall pdd';
      return inst.prefix ? `npm uninstall -g pdd --prefix ${safeQuoteShellPath(inst.prefix)}` : 'npm uninstall -g pdd';
    case 'npm-global':
      return inst.prefix ? `npm uninstall -g @promptdriven/pdd --prefix ${safeQuoteShellPath(inst.prefix)}` : 'npm uninstall -g @promptdriven/pdd';
    case 'pnpm':
      return inst.packageName === 'pdd' ? 'pnpm remove -g pdd' : 'pnpm remove -g @promptdriven/pdd';
    case 'homebrew':
      return 'brew uninstall pdd';
    case 'pypi':
      if (/\/uv\/tools\//i.test(normBin) || /\/uv\/tools\//i.test(normReal)) return 'uv tool uninstall pdd-cli';
      if (/\/pipx\/venvs\//i.test(normBin) || /\/pipx\/venvs\//i.test(normReal)) return 'pipx uninstall pdd-cli';
      return 'pip uninstall pdd-cli';
    case 'git-checkout':
      return `Remove ${clean(shortenHomePath(dirname(inst.path), home))} from PATH (Git checkout)`;
    default:
      return `rm -f ${safeQuoteShellPath(inst.path)}`;
  }
}

function probeBinaryVersion(binPath, { cwd, env, spawnImpl, timeout, platform, hasInjectedSpawn }) {
  // Never spawn Windows .cmd/.bat scripts directly without shell (throws EINVAL on Node 22+);
  // never pass shell: true on untrusted paths.
  if (platform === 'win32' && !hasInjectedSpawn && /\.(?:cmd|bat)$/i.test(binPath)) {
    return { version: null, timedOut: false };
  }
  try {
    const reply = spawnImpl(binPath, ['--version'], {
      cwd,
      env: { ...env, PDD_PATH_PROBE: '1', PDD_PATH_DIAG_DONE: '1', PDD_NO_UPDATE_CHECK: '1' },
      encoding: 'utf8',
      timeout,
      maxBuffer: 65536,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    const timedOut = reply?.error?.code === 'ETIMEDOUT' || reply?.signal === 'SIGTERM' || reply?.signal === 'SIGKILL';
    if (timedOut) return { version: null, timedOut: true };
    if (!reply?.error && reply?.status === 0) {
      const raw = (reply.stdout || '').trim() || (reply.stderr || '').trim();
      const firstLine = clean(raw.split(/\r?\n/, 1)[0] ?? '');
      if (firstLine) return { version: firstLine, timedOut: false };
    }
    return { version: null, timedOut: false };
  } catch {
    return { version: null, timedOut: false };
  }
}

function parseLoginProbeStdout(stdout) {
  const lines = String(stdout ?? '').split(/\r?\n/);
  for (let i = lines.length - 1; i >= 0; i--) {
    const trimmed = lines[i].trim();
    if (!trimmed.startsWith(LOGIN_WHICH_PREFIX)) continue;
    const value = trimmed.slice(LOGIN_WHICH_PREFIX.length).trim();
    if (!value || /[\x00-\x1f\x7f]/.test(value)) continue;
    if (/^(?:\/|\.\.?\/|[A-Za-z]:[\\/])/.test(value)) return value;
  }
  return null;
}

function collectCandidatePaths({ cwd, env, home, fs, platform, systemRoots, maxVersionDirs }) {
  const entries = [];
  const seenPath = new Set();
  const add = (candidatePath, source, pathIndex = null) => {
    if (typeof candidatePath !== 'string' || !candidatePath) return;
    const resolvedPath = isAbsolute(candidatePath) ? candidatePath : resolve(cwd, candidatePath);
    const key = normPath(resolvedPath, platform);
    if (seenPath.has(key)) return;
    if (!isExecutableFile(resolvedPath, fs)) return;
    seenPath.add(key);
    entries.push({ path: resolvedPath, source, pathIndex });
  };

  const binNames = executableNames(platform);
  const addDir = (dir, source, pathIndex = null) => {
    if (typeof dir !== 'string' || !dir) return;
    for (const name of binNames) add(join(dir, name), source, pathIndex);
  };

  // 1. Current PATH entries in exact order
  let pathRank = 0;
  for (const dir of pathList(env, cwd, platform)) {
    for (const name of binNames) {
      const full = join(dir, name);
      const key = normPath(full, platform);
      if (!seenPath.has(key) && isExecutableFile(full, fs)) {
        pathRank += 1;
        seenPath.add(key);
        entries.push({ path: full, source: 'path', pathIndex: pathRank });
      }
    }
  }

  // 2. Volta (shims + tools/image/packages)
  const voltaRoots = new Set();
  if (typeof env?.VOLTA_HOME === 'string' && env.VOLTA_HOME.trim()) voltaRoots.add(env.VOLTA_HOME.trim());
  if (home) voltaRoots.add(join(home, '.volta'));
  for (const vh of voltaRoots) {
    addDir(join(vh, 'bin'), 'volta');
    for (const pkgName of ['@promptdriven/pdd', 'pdd']) {
      for (const rel of [
        join('tools', 'image', 'packages', pkgName, 'lib', 'node_modules', pkgName, 'bin', 'pdd.mjs'),
        join('tools', 'image', 'packages', pkgName, 'node_modules', pkgName, 'bin', 'pdd.mjs'),
        join('tools', 'image', 'packages', pkgName, 'bin', 'pdd.mjs'),
      ]) {
        add(join(vh, rel), 'volta');
      }
    }
  }

  // 3. nvm (bounded scan)
  const nvmDirs = new Set();
  if (typeof env?.NVM_DIR === 'string' && env.NVM_DIR.trim()) nvmDirs.add(env.NVM_DIR.trim());
  if (home) nvmDirs.add(join(home, '.nvm'));
  for (const nvmDir of nvmDirs) {
    const versionsRoot = join(nvmDir, 'versions', 'node');
    for (const ver of boundedSubdirs(versionsRoot, maxVersionDirs, fs)) {
      addDir(join(versionsRoot, ver, 'bin'), 'nvm');
    }
  }

  // 4. fnm (bounded scan)
  const fnmDirs = new Set();
  if (typeof env?.FNM_DIR === 'string' && env.FNM_DIR.trim()) fnmDirs.add(env.FNM_DIR.trim());
  if (home) {
    fnmDirs.add(join(home, '.local', 'share', 'fnm'));
    fnmDirs.add(join(home, 'Library', 'Application Support', 'fnm'));
  }
  for (const fnmDir of fnmDirs) {
    addDir(join(fnmDir, 'current', 'bin'), 'fnm');
    const versionsRoot = join(fnmDir, 'node-versions');
    for (const ver of boundedSubdirs(versionsRoot, maxVersionDirs, fs)) {
      addDir(join(versionsRoot, ver, 'installation', 'bin'), 'fnm');
    }
    const aliasesRoot = join(fnmDir, 'aliases');
    for (const alias of boundedSubdirs(aliasesRoot, 8, fs)) {
      addDir(join(aliasesRoot, alias, 'bin'), 'fnm');
    }
  }

  // 5. mise & asdf (shims + bounded installs)
  const miseDirs = new Set();
  if (typeof env?.MISE_DATA_DIR === 'string' && env.MISE_DATA_DIR.trim()) miseDirs.add(env.MISE_DATA_DIR.trim());
  if (home) miseDirs.add(join(home, '.local', 'share', 'mise'));
  for (const miseDir of miseDirs) {
    addDir(join(miseDir, 'shims'), 'mise');
    const installsRoot = join(miseDir, 'installs', 'node');
    for (const ver of boundedSubdirs(installsRoot, maxVersionDirs, fs)) {
      addDir(join(installsRoot, ver, 'bin'), 'mise');
    }
  }

  const asdfDirs = new Set();
  if (typeof env?.ASDF_DATA_DIR === 'string' && env.ASDF_DATA_DIR.trim()) asdfDirs.add(env.ASDF_DATA_DIR.trim());
  if (home) {
    asdfDirs.add(join(home, '.asdf'));
    asdfDirs.add(join(home, '.local', 'share', 'asdf'));
  }
  for (const asdfDir of asdfDirs) {
    addDir(join(asdfDir, 'shims'), 'asdf');
    const installsRoot = join(asdfDir, 'installs', 'nodejs');
    for (const ver of boundedSubdirs(installsRoot, maxVersionDirs, fs)) {
      addDir(join(installsRoot, ver, 'bin'), 'asdf');
    }
  }

  // 6. pnpm
  const pnpmDirs = new Set();
  if (typeof env?.PNPM_HOME === 'string' && env.PNPM_HOME.trim()) pnpmDirs.add(env.PNPM_HOME.trim());
  if (home) {
    pnpmDirs.add(join(home, 'Library', 'pnpm'));
    pnpmDirs.add(join(home, '.local', 'share', 'pnpm'));
  }
  for (const pd of pnpmDirs) addDir(pd, 'pnpm');

  // 7. Global npm / Yarn / user local bin
  const npmPrefix = env?.NPM_CONFIG_PREFIX || env?.npm_config_prefix;
  if (typeof npmPrefix === 'string' && npmPrefix.trim()) addDir(join(npmPrefix.trim(), 'bin'), 'npm-global');
  if (home) {
    addDir(join(home, '.npm-global', 'bin'), 'npm-global');
    addDir(join(home, '.yarn', 'bin'), 'npm-global');
    addDir(join(home, '.config', 'yarn', 'global', 'node_modules', '.bin'), 'npm-global');
    addDir(join(home, '.local', 'bin'), 'local-bin');
  }

  // 8. Python / conda / uv / pipx
  if (typeof env?.CONDA_PREFIX === 'string' && env.CONDA_PREFIX.trim()) addDir(join(env.CONDA_PREFIX.trim(), 'bin'), 'conda');
  if (typeof env?.VIRTUAL_ENV === 'string' && env.VIRTUAL_ENV.trim()) addDir(join(env.VIRTUAL_ENV.trim(), 'bin'), 'python');
  if (home) {
    for (const dir of ['miniconda3', 'anaconda3', 'miniforge3', 'mambaforge']) {
      addDir(join(home, dir, 'bin'), 'conda');
    }
    addDir(join(home, '.local', 'share', 'uv', 'tools', 'pdd-cli', 'bin'), 'uv');
    addDir(join(home, '.local', 'pipx', 'venvs', 'pdd-cli', 'bin'), 'pipx');
  }

  // 9. System / Homebrew roots
  const defaultSystemRoots = platform === 'win32'
    ? []
    : ['/usr/local/bin/pdd', '/opt/homebrew/bin/pdd', '/opt/homebrew/anaconda3/bin/pdd'];
  for (const sysPath of (Array.isArray(systemRoots) ? systemRoots : defaultSystemRoots)) {
    const source = /anaconda|miniconda|conda/i.test(sysPath) ? 'conda'
      : /homebrew/i.test(sysPath) ? 'homebrew' : 'npm-global';
    add(sysPath, source);
  }

  return entries;
}

function maybeMapManagerShimToCurrent(binPath, realPath, currentReal, { fs = nativeFs, env = process.env, platform = process.platform } = {}) {
  if (!currentReal) return null;
  const normBin = normPath(binPath, platform);
  const normCurr = normPath(currentReal, platform);
  const normReal = normPath(realPath, platform);

  const miseRoots = [];
  if (typeof env?.MISE_DATA_DIR === 'string' && env.MISE_DATA_DIR.trim()) {
    miseRoots.push(normPath(safeRealpath(env.MISE_DATA_DIR.trim(), fs) ?? env.MISE_DATA_DIR.trim(), platform));
    miseRoots.push(normPath(env.MISE_DATA_DIR.trim(), platform));
  }
  const miseMatch = /^(.*\/mise)\/shims\/pdd(?:\.(?:cmd|exe))?$/i.exec(normBin);
  if (miseMatch?.[1]) miseRoots.push(miseMatch[1]);
  for (const root of new Set(miseRoots)) {
    if (normBin.startsWith(`${root}/shims/`) && normCurr.startsWith(`${root}/installs/`)) {
      const text = readSmallText(realPath, 4096, fs);
      if (/\/mise(?:\.exe)?$/i.test(normReal) || (text && /\bmise\b/i.test(text))) return currentReal;
    }
  }

  const asdfRoots = [];
  if (typeof env?.ASDF_DATA_DIR === 'string' && env.ASDF_DATA_DIR.trim()) {
    asdfRoots.push(normPath(safeRealpath(env.ASDF_DATA_DIR.trim(), fs) ?? env.ASDF_DATA_DIR.trim(), platform));
    asdfRoots.push(normPath(env.ASDF_DATA_DIR.trim(), platform));
  }
  const asdfMatch = /^(.*\/\.?asdf)\/shims\/pdd(?:\.(?:cmd|exe))?$/i.exec(normBin);
  if (asdfMatch?.[1]) asdfRoots.push(asdfMatch[1]);
  for (const root of new Set(asdfRoots)) {
    if (normBin.startsWith(`${root}/shims/`) && normCurr.startsWith(`${root}/installs/`)) {
      const text = readSmallText(realPath, 4096, fs);
      if (text && /\basdf\b/i.test(text)) return currentReal;
    }
  }
  return null;
}

export function diagnoseHostInstalls(options = {}, ports = {}) {
  const fs = ports.fs ?? options.fs ?? nativeFs;
  const spawnImpl = ports.spawnSync ?? options.spawnSync ?? nativeSpawnSync;
  const hasInjectedSpawn = Boolean(ports.spawnSync ?? options.spawnSync);
  const platform = ports.platform ?? options.platform ?? process.platform;
  const uid = ports.uid ?? options.uid;
  const homedirFn = ports.homedir ?? options.homedir ?? nativeHomedir;

  const env = options.env ?? process.env;
  const cwd = options.cwd ?? process.cwd();
  const home = resolveSafeHome(options.home, env, homedirFn, platform);
  const packageRoot = options.packageRoot ?? PACKAGE_ROOT;
  const currentBin = options.currentBin ?? resolve(packageRoot, 'bin/pdd.mjs');
  const checkLoginShells = (options.checkLoginShells ?? ports.checkLoginShells) !== false;
  const timeout = clampTimeout(options.probeTimeoutMs ?? DEFAULT_TIMEOUT_MS);
  const maxVersionDirs = Number.isInteger(options.maxVersionDirs) && options.maxVersionDirs > 0 ? options.maxVersionDirs : DEFAULT_MAX_VERSION_DIRS;
  const maxProbes = Number.isInteger(options.maxProbes) && options.maxProbes >= 0 ? options.maxProbes : DEFAULT_MAX_PROBES;
  const recursionGuarded = env?.PDD_PATH_DIAG_DONE === '1' || env?.PDD_PATH_PROBE === '1';

  const currentResolved = resolveCanonicalPddTarget(currentBin, { fs, env, home, platform, homedir: homedirFn });
  const currentReal = currentResolved.realPath;
  const currentPkgRoot = safeRealpath(packageRoot, fs) ?? packageRoot;
  const currentPkg = readJsonSafe(join(currentPkgRoot, 'package.json'), fs);
  const currentClass = classifyBinaryInstall({
    binPath: currentBin,
    realPath: currentReal,
    resolved: { ...currentResolved, packageRoot: currentPkg ? currentPkgRoot : currentResolved.packageRoot },
    fs,
    env,
    uid,
    platform,
  });

  const current = {
    path: currentBin,
    realPath: currentReal,
    packageRoot: currentPkgRoot,
    version: (typeof currentPkg?.version === 'string' && currentPkg.version) ? currentPkg.version : currentClass.version,
    kind: currentClass.kind,
    prefix: currentClass.prefix ?? null,
    packageName: currentClass.packageName ?? currentPkg?.name ?? null,
  };

  const rawCandidates = collectCandidatePaths({
    cwd,
    env,
    home,
    fs,
    platform,
    systemRoots: options.systemRoots ?? ports.systemRoots,
    maxVersionDirs,
  });

  let probesUsed = 0;
  const byCanonical = new Map();
  let pathSelected = null;

  const registerCandidate = (binPath, source, pathIndex = null) => {
    const resolved = resolveCanonicalPddTarget(binPath, { fs, env, home, platform, homedir: homedirFn });
    const shimCurrent = maybeMapManagerShimToCurrent(binPath, resolved.realPath, currentReal, { fs, env, platform });
    const canonicalKey = normPath(shimCurrent ?? resolved.realPath, platform);
    const isCurrent = Boolean(currentReal) && canonicalKey === normPath(currentReal, platform);

    let record = byCanonical.get(canonicalKey);
    if (record) {
      if (binPath !== record.path && !record.aliases.includes(binPath)) record.aliases.push(binPath);
      if (pathIndex !== null) {
        record.onPath = true;
        if (record.pathIndex === null || pathIndex < record.pathIndex) {
          record.pathIndex = pathIndex;
          if (record.path !== binPath) {
            record.aliases = [record.path, ...record.aliases.filter(a => a !== binPath)];
            record.path = binPath;
          }
        }
      }
      return record;
    }

    const info = isCurrent
      ? { kind: current.kind, prefix: current.prefix, voltaHome: currentClass.voltaHome ?? null, packageName: current.packageName, version: current.version }
      : classifyBinaryInstall({ binPath, realPath: resolved.realPath, resolved, fs, env, uid, platform });

    let version = info.version;
    let versionTimedOut = false;
    if (!isCurrent && !version && !recursionGuarded && probesUsed < maxProbes) {
      probesUsed += 1;
      const probed = probeBinaryVersion(binPath, { cwd, env, spawnImpl, timeout, platform, hasInjectedSpawn });
      version = probed.version;
      versionTimedOut = probed.timedOut;
    }

    record = {
      path: binPath,
      aliases: [],
      realPath: shimCurrent ?? resolved.realPath,
      version,
      versionTimedOut,
      kind: info.kind,
      prefix: info.prefix ?? null,
      voltaHome: info.voltaHome ?? null,
      packageName: info.packageName ?? null,
      source: isCurrent ? 'current' : source,
      onPath: pathIndex !== null,
      pathIndex,
      isCurrent,
      shadowsCurrent: false,
      remediation: null,
    };
    record.remediation = remediationForInstall(record, { home, platform });
    byCanonical.set(canonicalKey, record);
    return record;
  };

  for (const item of rawCandidates) {
    const rec = registerCandidate(item.path, item.source, item.pathIndex);
    if (item.pathIndex === 1 && !pathSelected) {
      pathSelected = {
        path: item.path,
        realPath: rec.realPath,
        version: rec.version,
        isCurrent: rec.isCurrent,
        kind: rec.kind,
      };
    }
  }

  // Ensure the running `current` install is always represented in `installs`.
  const currentKey = normPath(currentReal, platform);
  if (!byCanonical.has(currentKey)) {
    byCanonical.set(currentKey, {
      path: current.path,
      aliases: [],
      realPath: current.realPath,
      version: current.version,
      versionTimedOut: false,
      kind: current.kind,
      prefix: current.prefix,
      voltaHome: currentClass.voltaHome ?? null,
      packageName: current.packageName,
      source: 'current',
      onPath: false,
      pathIndex: null,
      isCurrent: true,
      shadowsCurrent: false,
      remediation: null,
    });
  }

  // Probe login non-interactive subshells (bounded timeout, zero interpolation).
  const defaultShells = platform === 'win32' ? [] : ['/bin/zsh', '/bin/bash'];
  const configuredShells = Array.isArray(options.loginShells ?? ports.loginShells)
    ? (options.loginShells ?? ports.loginShells)
    : defaultShells;
  const loginShells = [];

  for (const shellPath of configuredShells) {
    const name = basename(shellPath);
    if (!checkLoginShells || recursionGuarded || platform === 'win32') {
      loginShells.push({ shell: shellPath, name, status: 'skipped', resolvedPath: null, realPath: null, version: null, kind: null, remediation: null });
      continue;
    }
    const explicitShellList = Array.isArray(options.loginShells ?? ports.loginShells);
    if (!(hasInjectedSpawn && explicitShellList) && !isExecutableFile(shellPath, fs)) {
      loginShells.push({ shell: shellPath, name, status: 'skipped', resolvedPath: null, realPath: null, version: null, kind: null, remediation: null });
      continue;
    }

    let reply;
    try {
      reply = spawnImpl(shellPath, ['-lc', LOGIN_PROBE_CMD], {
        cwd,
        env: { ...env, PDD_PATH_PROBE: '1', PDD_PATH_DIAG_DONE: '1', PDD_NO_UPDATE_CHECK: '1' },
        encoding: 'utf8',
        timeout,
        maxBuffer: 65536,
        stdio: ['ignore', 'pipe', 'pipe'],
      });
    } catch {
      loginShells.push({ shell: shellPath, name, status: 'skipped', resolvedPath: null, realPath: null, version: null, kind: null, remediation: null });
      continue;
    }

    const timedOut = reply?.error?.code === 'ETIMEDOUT' || reply?.signal === 'SIGTERM' || reply?.signal === 'SIGKILL';
    if (timedOut) {
      loginShells.push({ shell: shellPath, name, status: 'timeout', resolvedPath: null, realPath: null, version: null, kind: null, remediation: null });
      continue;
    }

    if (reply?.error || reply?.status !== 0) {
      loginShells.push({ shell: shellPath, name, status: 'not-found', resolvedPath: null, realPath: null, version: null, kind: null, remediation: null });
      continue;
    }

    const foundPath = parseLoginProbeStdout(reply?.stdout);
    if (!foundPath) {
      loginShells.push({ shell: shellPath, name, status: 'not-found', resolvedPath: null, realPath: null, version: null, kind: null, remediation: null });
      continue;
    }

    const resolvedFound = isAbsolute(foundPath) ? foundPath : resolve(cwd, foundPath);
    if (!hasInjectedSpawn && !isExecutableFile(resolvedFound, fs)) {
      loginShells.push({ shell: shellPath, name, status: 'not-found', resolvedPath: null, realPath: null, version: null, kind: null, remediation: null });
      continue;
    }

    const rec = registerCandidate(resolvedFound, `login-${name}`, null);
    if (rec.isCurrent) {
      loginShells.push({
        shell: shellPath,
        name,
        status: 'match',
        resolvedPath: resolvedFound,
        realPath: rec.realPath,
        version: rec.version,
        kind: rec.kind,
        remediation: null,
      });
    } else {
      loginShells.push({
        shell: shellPath,
        name,
        status: 'mismatch',
        resolvedPath: resolvedFound,
        realPath: rec.realPath,
        version: rec.version,
        kind: rec.kind,
        remediation: rec.remediation,
      });
    }
  }

  const currentRecord = byCanonical.get(currentKey);
  const currentPathIndex = currentRecord?.pathIndex ?? null;
  const shadowedOnPath = Boolean(pathSelected && !pathSelected.isCurrent);

  const installs = [...byCanonical.values()].map(rec => {
    const shadowsCurrent = !rec.isCurrent && rec.onPath && (currentPathIndex === null || rec.pathIndex < currentPathIndex);
    const { voltaHome: _vh, ...publicRec } = rec;
    return { ...publicRec, shadowsCurrent };
  });

  installs.sort((a, b) => {
    if (a.isCurrent !== b.isCurrent) return a.isCurrent ? -1 : 1;
    if (a.onPath !== b.onPath) return a.onPath ? -1 : 1;
    if (a.pathIndex !== null && b.pathIndex !== null && a.pathIndex !== b.pathIndex) return a.pathIndex - b.pathIndex;
    return a.path.localeCompare(b.path);
  });

  const duplicates = installs.filter(inst => !inst.isCurrent);
  const shellSplits = loginShells.filter(sh => sh.status === 'mismatch');

  const pathOnlyPaths = rawCandidates.filter(c => c.pathIndex !== null).map(c => c.path);
  const rawUnscoped = findUnscopedNpmPdd(cwd, env, pathOnlyPaths, fs, platform);
  const legacyBinKey = rawUnscoped.legacy
    ? normPath(safeRealpath(join(rawUnscoped.legacy, 'bin/pdd.mjs'), fs) ?? join(rawUnscoped.legacy, 'bin/pdd.mjs'), platform)
    : null;
  const legacyAlreadyInDuplicates = Boolean(legacyBinKey) && duplicates.some(d => normPath(d.realPath, platform) === legacyBinKey);
  const unscopedLegacy = rawUnscoped.legacy && legacyBinKey !== currentKey && !legacyAlreadyInDuplicates
    ? rawUnscoped.legacy
    : null;
  const unscopedNpm = {
    foreign: rawUnscoped.foreign,
    legacy: unscopedLegacy,
    remediation: (rawUnscoped.foreign || unscopedLegacy) ? 'npm uninstall -g pdd && npm install -g @promptdriven/pdd' : null,
  };

  const hasConflict = shadowedOnPath
    || duplicates.length > 0
    || shellSplits.length > 0
    || Boolean(unscopedNpm.foreign || unscopedNpm.legacy);

  return {
    current,
    installs,
    pathSelected,
    shadowedOnPath,
    duplicates,
    unscopedNpm,
    loginShells,
    shellSplits,
    hasConflict,
  };
}

export function formatDualInstallWarnings(diagnosis, { home } = {}) {
  if (!diagnosis || !diagnosis.hasConflict) return [];
  const fmt = p => clean(shortenHomePath(p, home));
  const lines = ['⚠ Competing pdd installs or shell PATH split detected (run `pdd doctor` for full details):'];
  for (const dup of diagnosis.duplicates ?? []) {
    const ver = dup.version ? clean(dup.version) : (dup.versionTimedOut ? 'version timed out' : 'version unknown');
    const tag = dup.shadowsCurrent ? 'shadows PATH' : (dup.onPath ? 'on PATH' : clean(dup.kind));
    const fix = dup.remediation ? ` — fix: ${clean(dup.remediation)}` : '';
    lines.push(`  • ${fmt(dup.path)} (${ver}, ${tag})${fix}`);
  }
  for (const split of diagnosis.shellSplits ?? []) {
    const ver = split.version ? ` (${clean(split.version)})` : '';
    const currVer = diagnosis.current?.version ? ` (${clean(diagnosis.current.version)})` : '';
    const fix = split.remediation ? ` — fix: ${clean(split.remediation)}` : '';
    lines.push(`  • ${clean(split.name)} -lc resolves ${fmt(split.resolvedPath)}${ver} instead of ${fmt(diagnosis.current?.path ?? 'current pdd')}${currVer}${fix}`);
  }
  if (diagnosis.unscopedNpm?.foreign) {
    lines.push(`  • Unrelated npm package "pdd" at ${fmt(diagnosis.unscopedNpm.foreign)} — fix: ${clean(diagnosis.unscopedNpm.remediation)}`);
  }
  if (diagnosis.unscopedNpm?.legacy) {
    lines.push(`  • Unscoped npm package "pdd" at ${fmt(diagnosis.unscopedNpm.legacy)} — fix: ${clean(diagnosis.unscopedNpm.remediation)}`);
  }
  return lines;
}

export function formatHostInstallWarnings(options = {}, ports = {}) {
  try {
    const env = options.env ?? process.env;
    if (env?.PDD_PATH_DIAG_DONE === '1' || env?.PDD_PATH_PROBE === '1') return [];
    const platform = ports.platform ?? options.platform ?? process.platform;
    const homedirFn = ports.homedir ?? options.homedir ?? nativeHomedir;
    const home = resolveSafeHome(options.home, env, homedirFn, platform);
    const diagnosis = diagnoseHostInstalls({ ...options, home }, ports);
    return formatDualInstallWarnings(diagnosis, { home });
  } catch {
    return [];
  }
}

// Fast PATH diagnostic preserved for `--version`, `setup`, and `workflow` modes.
// Recognizes symlinks, Volta shims, pnpm wrappers, and mise/asdf shims targeting this pdd.
// Only --version probes a shadowed first candidate; recursion guards prevent any probe loop.
export function pathDiagnostic({ packageRoot, cwd, env, mode }) {
  if (env.PDD_PATH_PROBE === '1' || env.PDD_PATH_DIAG_DONE === '1') return [];
  const platform = process.platform;
  const home = resolveSafeHome(undefined, env, nativeHomedir, platform);
  let version;
  let running;
  try {
    version = JSON.parse(nativeFs.readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
    running = resolve(packageRoot, 'bin/pdd.mjs');
    if (typeof version !== 'string' || !version || !isExecutableFile(running, nativeFs)) return [];
  } catch { return []; }
  const paths = candidates(cwd, env);
  const current = safeRealpath(running, nativeFs);
  const currentNorm = current ? normPath(current, platform) : null;
  const selected = paths[0];
  const isAlpha = p => {
    if (!currentNorm) return false;
    const direct = safeRealpath(p, nativeFs);
    if (direct && normPath(direct, platform) === currentNorm) return true;
    const resolved = resolveCanonicalPddTarget(p, { fs: nativeFs, env, home, platform });
    if (normPath(resolved.realPath, platform) === currentNorm) return true;
    const shimMapped = maybeMapManagerShimToCurrent(p, resolved.realPath, current, { fs: nativeFs, env, platform });
    return Boolean(shimMapped && normPath(shimMapped, platform) === currentNorm);
  };
  const shadowed = selected && !isAlpha(selected);
  const { foreign: foreignNpm, legacy: rawLegacyNpm } = findUnscopedNpmPdd(cwd, env, paths, nativeFs, platform);
  const legacyNpm = rawLegacyNpm && (mode === 'setup' || normPath(safeRealpath(join(rawLegacyNpm, 'bin/pdd.mjs'), nativeFs) ?? '', platform) !== currentNorm) ? rawLegacyNpm : null;
  const conflict = shadowed || paths.some(p => !isAlpha(p)) || Boolean(foreignNpm) || Boolean(legacyNpm);
  if ((mode === 'version' && !conflict) || (mode === 'setup' && !conflict && selected) || (mode === 'workflow' && !shadowed)) return [];
  let selectedVersion = `pdd ${version}`;
  if (shadowed) {
    selectedVersion = 'version unavailable';
    try {
      const reply = nativeSpawnSync(selected, ['--version'], {
        cwd,
        env: { ...env, PDD_PATH_PROBE: '1', PDD_PATH_DIAG_DONE: '1', PDD_NO_UPDATE_CHECK: '1' },
        encoding: 'utf8',
        timeout: 2000,
        maxBuffer: 65536,
        stdio: ['ignore', 'pipe', 'pipe'],
      });
      if (!reply.error && reply.status === 0 && clean(reply.stdout)) selectedVersion = clean(reply.stdout);
    } catch { /* Keep the selected path visible when its version cannot be read. */ }
  }
  const absolute = `${safeQuoteShellPath(process.execPath)} ${safeQuoteShellPath(running)}`;
  const selection = selected ? `PATH selects: ${clean(selected)} (${selectedVersion}).` : 'PATH has no executable named pdd.';
  if (mode === 'workflow') return [`${selection} Running pdd ${version}: ${clean(running)}. In workflow chats use "$PDD_BIN"; activate environments before correcting PATH.`];
  const lines = [`Running pdd ${version}: ${clean(running)}.`, ...paths.map((p, i) => `  PATH ${i + 1}: ${clean(p)}`), selection];
  if (conflict || !selected) {
    lines.push('Later environment activation (for example conda) can reorder PATH and shadow this pdd again.', `Use this pdd directly: ${absolute}`);
    const alpha = paths.find(p => /^(?:pdd|pdd\.cmd|pdd\.exe)$/i.test(basename(p)) && isAlpha(p));
    if (alpha) lines.push(`After environment activation, run: export PATH=${safeQuoteShellPath(dirname(alpha))}:"$PATH"; hash -r`);
  }
  if (foreignNpm) lines.push(`Found the unrelated npm package "pdd" at ${clean(foreignNpm)}. Run: npm uninstall -g pdd && npm install -g @promptdriven/pdd`);
  if (legacyNpm) lines.push(`Found unscoped npm package "pdd" at ${clean(legacyNpm)} (blocks @promptdriven/pdd on bin/pdd). Run: npm uninstall -g pdd && npm install -g @promptdriven/pdd`);
  return lines;
}
