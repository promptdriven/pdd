// Prompt: prompts/cli/install-kind.prompt.md
import * as nativeFs from 'node:fs';
import { isAbsolute, join, relative, resolve, win32 as win32Path } from 'node:path';

export const quoteShellArg = text => `'${String(text).replace(/'/g, "'\\''")}'`;

const defaultUid = () => (typeof process.getuid === 'function' ? process.getuid() : null);

function readJson(file, fs) {
  try {
    const parsed = JSON.parse(fs.readFileSync(file, 'utf8'));
    return parsed && typeof parsed === 'object' && !Array.isArray(parsed) ? parsed : null;
  } catch { return null; }
}

const canonicalDir = (folder, fs) => {
  try { return fs.realpathSync(folder); } catch { return folder; }
};

const normPath = value => String(value).replace(/\\/g, '/').replace(/\/+$/, '');

export function resolveVoltaNpmBin(voltaHome, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const platform = ports.platform ?? process.platform;
  if (platform === 'win32') {
    const npmCmd = win32Path.join(voltaHome, 'bin', 'npm.cmd');
    const npmExe = win32Path.join(voltaHome, 'bin', 'npm.exe');
    if (typeof fs.existsSync === 'function') {
      if (fs.existsSync(npmCmd)) return npmCmd;
      if (fs.existsSync(npmExe)) return npmExe;
    }
    return npmCmd;
  }
  return join(voltaHome, 'bin', 'npm');
}

export function scrubVoltaEnv(env = process.env, voltaHome) {
  const cleaned = {};
  if (env && typeof env === 'object') {
    for (const [key, value] of Object.entries(env)) {
      if (key === '_VOLTA_TOOL_RECURSION' || key === 'VOLTA_UNSAFE_GLOBAL') continue;
      if (key.toLowerCase() === 'npm_config_prefix') continue;
      cleaned[key] = value;
    }
  }
  if (typeof voltaHome === 'string' && voltaHome) cleaned.VOLTA_HOME = voltaHome;
  return cleaned;
}

export function classifyInstallKind(packageRoot, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const uid = ports.uid !== undefined ? ports.uid : defaultUid();
  const env = ports.env ?? process.env;
  const platform = ports.platform ?? process.platform;
  if (typeof packageRoot !== 'string' || !packageRoot) return { kind: 'invalid' };
  let real, info;
  try {
    real = fs.realpathSync(packageRoot);
    info = fs.statSync(real);
    if (!info.isDirectory()) return { kind: 'invalid' };
  } catch { return { kind: 'invalid' }; }

  const norm = normPath(real);
  const pathJoin = platform === 'win32' ? win32Path.join : join;
  if (fs.existsSync(pathJoin(real, '.git'))) {
    return { kind: 'git-checkout', realPackageRoot: real, hint: 'git pull && npm install' };
  }
  if (/(?:^|\/)(?:site-packages|dist-packages)\/(?:pdd|pdd_cli|pdd-cli)(?:\/|$)/.test(norm)) {
    return { kind: 'pypi', realPackageRoot: real, hint: 'pip install -U pdd-cli' };
  }
  if (/(?:^|\/)\.pnpm(?:\/|$)|\/pnpm\/global(?:\/|$)/.test(norm)) {
    return { kind: 'pnpm', realPackageRoot: real, hint: 'pnpm add -g @promptdriven/pdd@latest' };
  }
  if (/(?:^|\/)_npx(?:\/|$)/.test(norm)) {
    return { kind: 'npx', realPackageRoot: real, hint: 'npm install -g @promptdriven/pdd && pdd setup' };
  }

  // Detect Volta-managed installs BEFORE generic node_modules matching so we never run `npm --prefix <volta-image-dir>`.
  const voltaMatch = /^(.*?)\/tools\/image\/packages\/(@promptdriven\/pdd|pdd)(?:\/.*)?$/.exec(norm);
  if (voltaMatch?.[1]) {
    const derivedVoltaHome = real.slice(0, voltaMatch[1].length);
    const envVoltaHome = typeof env?.VOLTA_HOME === 'string' && env.VOLTA_HOME.trim()
      ? env.VOLTA_HOME.trim().replace(/[\\/]+$/, '')
      : null;
    const voltaHome = envVoltaHome && normPath(canonicalDir(envVoltaHome, fs)) === normPath(canonicalDir(derivedVoltaHome, fs))
      ? envVoltaHome
      : derivedVoltaHome;
    try {
      const homeInfo = fs.statSync(voltaHome);
      if (uid !== null && ((Number.isInteger(info.uid) && info.uid !== uid) || (Number.isInteger(homeInfo.uid) && homeInfo.uid !== uid))) {
        return { kind: 'unowned-prefix', prefix: voltaHome, realPackageRoot: real, hint: 'npm install -g @promptdriven/pdd && pdd setup' };
      }
    } catch { return { kind: 'invalid', realPackageRoot: real }; }
    const packageName = voltaMatch[2];
    return {
      kind: 'volta',
      prefix: voltaHome,
      voltaHome,
      npmBin: resolveVoltaNpmBin(voltaHome, { fs, platform }),
      packageName,
      isLegacyUnscoped: packageName === 'pdd',
      realPackageRoot: real,
    };
  }

  const match = /^(.*?)\/(?:lib\/)?node_modules\/(?:@promptdriven\/pdd|pdd)$/.exec(norm);
  if (!match?.[1]) return { kind: 'unknown', realPackageRoot: real, hint: 'npm install -g @promptdriven/pdd && pdd setup' };
  const prefix = real.slice(0, match[1].length);
  // Only classify as local-project when parent holds package.json; never check prefix/.git (Apple Silicon /opt/homebrew/.git is global!).
  if (fs.existsSync(pathJoin(prefix, 'package.json'))) {
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
  if (c.kind === 'npm-global') return { prefix: c.prefix, realPackageRoot: c.realPackageRoot };
  if (c.kind === 'volta') {
    return {
      kind: 'volta',
      prefix: c.voltaHome,
      voltaHome: c.voltaHome,
      npmBin: c.npmBin,
      packageName: c.packageName,
      isLegacyUnscoped: c.isLegacyUnscoped,
      realPackageRoot: c.realPackageRoot,
    };
  }
  return null;
}

export function isLegacyUnscopedPddDir(pkgDir, fs = nativeFs, uid = defaultUid()) {
  const lstat = fs.lstatSync ?? fs.statSync;
  try {
    const info = lstat(pkgDir);
    if (info.isSymbolicLink?.() || !info.isDirectory()) return false;
    if (uid !== null && Number.isInteger(info.uid) && info.uid !== uid) return false;
    if (fs.existsSync(join(pkgDir, '.git'))) return false;
    const pkg = readJson(join(pkgDir, 'package.json'), fs);
    if (pkg?.name !== 'pdd') return false;
    const binRel = typeof pkg.bin === 'string' ? pkg.bin : pkg.bin?.pdd;
    if (typeof binRel !== 'string' || binRel.replace(/^\.\//, '') !== 'bin/pdd.mjs') return false;
    const binInfo = lstat(join(pkgDir, 'bin/pdd.mjs'));
    return !binInfo.isSymbolicLink?.() && binInfo.isFile();
  } catch {
    return false;
  }
}

const CLASSIC_LEGACY_RELS = ['lib/node_modules/pdd', 'node_modules/pdd'];
const VOLTA_LEGACY_RELS = [
  'tools/image/packages/pdd/lib/node_modules/pdd',
  'tools/image/packages/pdd/node_modules/pdd',
  'tools/image/packages/pdd',
];

export function hasLegacyUnscopedPdd(prefixOrInstall, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const uid = ports.uid !== undefined ? ports.uid : defaultUid();
  if (prefixOrInstall && typeof prefixOrInstall === 'object') {
    if (prefixOrInstall.kind === 'volta') {
      const base = prefixOrInstall.voltaHome ?? prefixOrInstall.prefix;
      if (typeof base !== 'string' || !base) return false;
      return VOLTA_LEGACY_RELS.some(rel => isLegacyUnscopedPddDir(join(base, rel), fs, uid));
    }
    const prefix = prefixOrInstall.prefix;
    if (typeof prefix !== 'string' || !prefix) return false;
    return CLASSIC_LEGACY_RELS.some(rel => isLegacyUnscopedPddDir(join(prefix, rel), fs, uid));
  }
  if (typeof prefixOrInstall !== 'string' || !prefixOrInstall) return false;
  return [...CLASSIC_LEGACY_RELS, ...VOLTA_LEGACY_RELS].some(rel => isLegacyUnscopedPddDir(join(prefixOrInstall, rel), fs, uid));
}

const CLASSIC_ROOT_RELS = [
  'lib/node_modules/@promptdriven/pdd',
  'node_modules/@promptdriven/pdd',
  'lib/node_modules/pdd',
  'node_modules/pdd',
];

const VOLTA_ROOT_RELS = [
  'tools/image/packages/@promptdriven/pdd/lib/node_modules/@promptdriven/pdd',
  'tools/image/packages/@promptdriven/pdd/node_modules/@promptdriven/pdd',
  'tools/image/packages/@promptdriven/pdd',
  'tools/image/packages/pdd/lib/node_modules/pdd',
  'tools/image/packages/pdd/node_modules/pdd',
  'tools/image/packages/pdd',
];

export function resolveInstalledRoot(installOrPrefix, fallbackRoot, fs = nativeFs) {
  const isObj = installOrPrefix && typeof installOrPrefix === 'object';
  const base = isObj ? (installOrPrefix.voltaHome ?? installOrPrefix.prefix) : installOrPrefix;
  if (typeof base !== 'string' || !base) return fallbackRoot;
  const rels = isObj
    ? (installOrPrefix.kind === 'volta' ? VOLTA_ROOT_RELS : CLASSIC_ROOT_RELS)
    : [...CLASSIC_ROOT_RELS, ...VOLTA_ROOT_RELS];
  for (const rel of rels) {
    const candidate = join(base, rel);
    try { if (fs.statSync(join(candidate, 'package.json')).isFile()) return candidate; } catch { /* Try next layout. */ }
  }
  return fallbackRoot;
}

export function resolveInstalledBinEntry(pkgRoot, fs = nativeFs) {
  if (typeof pkgRoot !== 'string' || !pkgRoot) return null;
  const pkg = readJson(join(pkgRoot, 'package.json'), fs);
  const rawBin = typeof pkg?.bin === 'string' ? pkg.bin : pkg?.bin?.pdd;
  const rel = typeof rawBin === 'string' && rawBin.trim() ? rawBin.trim().replace(/^\.\//, '') : join('bin', 'pdd.mjs');
  if (isAbsolute(rel)) return null;
  const realRoot = canonicalDir(pkgRoot, fs);
  const candidate = resolve(pkgRoot, rel);
  const lexicalRel = relative(resolve(pkgRoot), candidate);
  if (!lexicalRel || lexicalRel.startsWith('..') || isAbsolute(lexicalRel)) return null;
  try {
    const lstat = fs.lstatSync ?? fs.statSync;
    const linfo = lstat(candidate);
    if (linfo.isSymbolicLink?.()) {
      const realCand = canonicalDir(candidate, fs);
      const realRel = relative(realRoot, realCand);
      if (!realRel || realRel.startsWith('..') || isAbsolute(realRel)) return null;
    }
    if (fs.statSync(candidate).isFile()) {
      const realCand = canonicalDir(candidate, fs);
      const realRel = relative(realRoot, realCand);
      if (!realRel || realRel.startsWith('..') || isAbsolute(realRel)) return null;
      return candidate;
    }
  } catch { /* Missing or unreadable bin entry. */ }
  return null;
}

export function npmCommandForInstall(install, action, spec, env = process.env) {
  if (install?.kind === 'volta') {
    return {
      command: install.npmBin,
      args: [action, '-g', '--ignore-scripts', '--no-audit', '--no-fund', spec],
      env: scrubVoltaEnv(env, install.voltaHome),
    };
  }
  return {
    command: 'npm',
    args: [action, '-g', '--prefix', install.prefix, '--ignore-scripts', '--no-audit', '--no-fund', spec],
    env,
  };
}

export function formatNpmInstallCommand(install, spec) {
  if (install?.kind === 'volta') return `npm install -g --ignore-scripts ${spec}`;
  return `npm install -g --prefix ${quoteShellArg(install.prefix)} --ignore-scripts ${spec}`;
}

export function formatNpmUninstallCommand(install) {
  if (install?.kind === 'volta') return 'npm uninstall -g pdd';
  return `npm uninstall -g --prefix ${quoteShellArg(install.prefix)} pdd`;
}
