import { spawnSync } from 'node:child_process';
import {
  accessSync,
  constants,
  cpSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  rmSync,
  statSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { delimiter, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { checkVersionParity, stagePypiBundle } from './sync-pypi-version.mjs';

const DEFAULT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const DEFAULT_REPO = 'promptdriven/pdd';
const DEFAULT_NPM_REGISTRY = 'https://registry.npmjs.org';
const DEFAULT_PYPI_BASE_URL = 'https://pypi.org';
const TAG_PATTERN = /^[A-Za-z0-9._-]+$/;
const REPO_PATTERN = /^[A-Za-z0-9._-]+\/[A-Za-z0-9._-]+$/;

const ISOLATED_HOME_ENV_KEYS = [
  'XDG_CONFIG_HOME',
  'XDG_STATE_HOME',
  'XDG_CACHE_HOME',
  'XDG_DATA_HOME',
  'XDG_RUNTIME_DIR',
  'CODEX_HOME',
  'CLAUDE_CONFIG_DIR',
  'GEMINI_CLI_HOME',
  'AGY_HOME',
  'GH_CONFIG_DIR',
];

const NPM_SCRUB_ENV_KEYS = [
  'npm_config_dry_run',
  'npm_config_prefix',
  'npm_config_userconfig',
  'npm_config_globalconfig',
  'npm_config_registry',
];

const PYTHON_COPY_SKIP = new Set(['_bundled', 'build', 'dist', '__pycache__']);

function defaultRunCommand(cmd, args, options = {}) {
  const res = spawnSync(cmd, args, {
    cwd: options.cwd,
    env: options.env ?? process.env,
    encoding: 'utf8',
    stdio: options.stdio ?? ['ignore', 'pipe', 'pipe'],
    maxBuffer: options.maxBuffer ?? 32 * 1024 * 1024,
  });
  return {
    status: res.status ?? (res.error ? 1 : 0),
    stdout: res.stdout ?? '',
    stderr: res.stderr ?? '',
    error: res.error ?? null,
  };
}

function defaultSleep(ms) {
  return new Promise(resolveSleep => setTimeout(resolveSleep, ms));
}

function formatCommandFailure(label, res) {
  if (res.error) {
    return `${label} failed: ${res.error.message}`;
  }
  const detail = [res.stderr, res.stdout].map(s => String(s || '').trim()).filter(Boolean).join('\n');
  return detail
    ? `${label} failed (exit ${res.status}):\n${detail}`
    : `${label} failed (exit ${res.status}).`;
}

function readFlagValue(argv, index, flag) {
  const arg = argv[index];
  if (arg === flag) {
    const next = argv[index + 1];
    if (next === undefined || next === '' || next.startsWith('-')) {
      throw new Error(`Missing value for ${flag}.`);
    }
    return { matched: true, value: next, advance: 1 };
  }
  const prefix = `${flag}=`;
  if (arg.startsWith(prefix)) {
    const value = arg.slice(prefix.length);
    if (!value) throw new Error(`Missing value for ${flag}.`);
    return { matched: true, value, advance: 0 };
  }
  return { matched: false, value: null, advance: 0 };
}

/**
 * Parse CLI flags for scripts/publish-release.mjs.
 * Also honors npm_config_dry_run=true when invoked via `npm run release:publish --dry-run`
 * (without `--`) so an omitted separator fails safe into dry-run mode.
 */
export function parsePublishArgs(argv, env = {}) {
  let dryRun = String(env.npm_config_dry_run || '').toLowerCase() === 'true';
  let dryRunFromNpmEnv = dryRun;
  let tag = null;
  let npmOnly = false;
  let pypiOnly = false;
  let repo = null;
  let root = DEFAULT_ROOT;
  let pythonBin = null;
  let help = false;

  const valueSetters = [
    ['--tag', val => { tag = val; }],
    ['--repo', val => { repo = val; }],
    ['--root', val => { root = resolve(val); }],
    ['--python', val => { pythonBin = val; }],
  ];

  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--help' || arg === '-h') {
      help = true;
      continue;
    }
    if (arg === '--dry-run') {
      dryRun = true;
      dryRunFromNpmEnv = false;
      continue;
    }
    if (arg === '--npm-only') {
      npmOnly = true;
      continue;
    }
    if (arg === '--pypi-only') {
      pypiOnly = true;
      continue;
    }

    let consumed = false;
    for (const [flag, assign] of valueSetters) {
      const parsed = readFlagValue(argv, i, flag);
      if (parsed.matched) {
        assign(parsed.value);
        i += parsed.advance;
        consumed = true;
        break;
      }
    }
    if (!consumed) {
      throw new Error(`Unknown argument: ${arg}`);
    }
  }

  if (npmOnly && pypiOnly) {
    throw new Error('Cannot combine --npm-only and --pypi-only.');
  }

  if (tag !== null) {
    tag = tag.trim().replace(/^refs\/tags\//, '');
    if (!TAG_PATTERN.test(tag)) {
      throw new Error(`Invalid GitHub Release tag "${tag}".`);
    }
  }

  if (repo !== null) {
    repo = repo.trim();
    if (!REPO_PATTERN.test(repo)) {
      throw new Error(`Invalid GitHub repository "${repo}". Expected OWNER/REPO.`);
    }
  }

  return { dryRun, dryRunFromNpmEnv, tag, npmOnly, pypiOnly, repo, root, pythonBin, help };
}

/**
 * Format concise CLI usage text.
 */
export function usageText() {
  return [
    'Usage: node scripts/publish-release.mjs [options]',
    '       npm run release:publish -- [options]',
    '',
    'Options:',
    '  --dry-run          Verify, build, and smoke-test without publishing',
    '  --tag <tag>        Target GitHub Release tag (default: latest published release)',
    '  --npm-only         Verify, smoke-test, and publish only @promptdriven/pdd on npm',
    '  --pypi-only        Build, verify, and publish only pdd-cli on PyPI',
    '  --repo <owner/org> GitHub repository slug (default: derived from package.json/origin)',
    '  --python <bin>     Python 3 executable to use for build and twine',
    '  --root <dir>       Repository root path (default: current repo)',
    '  -h, --help         Show this help text',
  ].join('\n');
}

/**
 * Select npm dist-tag matching .github/workflows/release.yml.
 */
export function npmDistTagForVersion(version) {
  return String(version).includes('-') ? 'alpha' : 'latest';
}

/**
 * Convert a SemVer version to its PEP 440 PyPI equivalent.
 */
export function toPep440Version(version) {
  const raw = String(version).trim();
  const match = /^(\d+\.\d+\.\d+)-(alpha|a|beta|b|rc)\.?(\d+)$/i.exec(raw);
  if (!match) return raw;
  const [, base, label, num] = match;
  const lower = label.toLowerCase();
  const pepLabel = lower.startsWith('a') ? 'a' : lower.startsWith('b') ? 'b' : 'rc';
  return `${base}${pepLabel}${num}`;
}

/**
 * Read `[project] name = "..."` from python/pyproject.toml.
 */
export function readPyprojectName(pyprojectText) {
  const lines = String(pyprojectText).split(/\r?\n/);
  let inProject = false;
  for (const raw of lines) {
    const line = raw.trim();
    if (!line || line.startsWith('#')) continue;
    if (line.startsWith('[')) {
      inProject = line === '[project]';
      continue;
    }
    if (inProject) {
      const match = /^name\s*=\s*"([^"]+)"\s*(?:#.*)?$/.exec(line);
      if (match) return match[1];
    }
  }
  return null;
}

/**
 * Extract OWNER/REPO from a GitHub git/https URL or slug.
 */
export function normalizeGitHubRepo(raw) {
  if (typeof raw !== 'string') return null;
  const trimmed = raw.trim();
  if (REPO_PATTERN.test(trimmed)) return trimmed;
  const match = /github\.com[:/]([A-Za-z0-9._-]+\/[A-Za-z0-9._-]+?)(?:\.git)?(?:[#?].*)?$/.exec(trimmed);
  return match ? match[1] : null;
}

/**
 * Resolve OWNER/REPO from package.json repository URL or git origin remote.
 */
export function deriveGitHubRepo(root = DEFAULT_ROOT, runCommand = defaultRunCommand) {
  try {
    const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
    const repoField = typeof pkg.repository === 'string' ? pkg.repository : pkg.repository?.url;
    const fromPkg = normalizeGitHubRepo(repoField);
    if (fromPkg) return fromPkg;
  } catch {
    // Fall back to git remote or default.
  }

  const remote = runCommand('git', ['remote', 'get-url', 'origin'], { cwd: root });
  if (remote.status === 0) {
    const fromGit = normalizeGitHubRepo(remote.stdout);
    if (fromGit) return fromGit;
  }

  return DEFAULT_REPO;
}

function hasExecutablePdd(dir) {
  const names = process.platform === 'win32' ? ['pdd.cmd', 'pdd.exe', 'pdd'] : ['pdd'];
  for (const name of names) {
    const candidate = join(dir, name);
    try {
      accessSync(candidate, constants.X_OK);
      if (statSync(candidate).isFile()) return true;
    } catch {
      // Not present or not executable.
    }
  }
  return false;
}

function hasUnscopedNpmPddNear(dir) {
  for (const rel of ['../lib/node_modules/pdd/package.json', 'node_modules/pdd/package.json']) {
    if (existsSync(resolve(dir, rel))) return true;
  }
  return false;
}

/**
 * Build a PATH that exposes installBinDir and nodeBinDir while excluding
 * other directories containing a `pdd` binary that would shadow the smoke-tested install.
 */
export function buildIsolatedPddPath(
  installBinDir,
  currentPath = process.env.PATH ?? '',
  nodeBinDir = dirname(process.execPath),
) {
  const ordered = [];
  const seen = new Set();
  const push = dir => {
    if (!dir) return;
    const normalized = resolve(dir);
    if (seen.has(normalized)) return;
    seen.add(normalized);
    ordered.push(dir);
  };

  push(installBinDir);
  push(nodeBinDir);

  for (const rawDir of String(currentPath).split(delimiter)) {
    const dir = rawDir.trim();
    if (!dir) continue;
    if (hasExecutablePdd(dir) || hasUnscopedNpmPddNear(dir)) continue;
    push(dir);
  }

  return ordered.join(delimiter);
}

function createIsolatedNodeBinDir(smokeDir) {
  const realNodeDir = dirname(process.execPath);
  if (process.platform === 'win32' || (!hasExecutablePdd(realNodeDir) && !hasUnscopedNpmPddNear(realNodeDir))) {
    return realNodeDir;
  }
  const nodeBinDir = join(smokeDir, 'node-bin');
  mkdirSync(nodeBinDir, { recursive: true });
  symlinkSync(process.execPath, join(nodeBinDir, 'node'));
  return nodeBinDir;
}

function buildScrubbedBaseEnv(baseEnv) {
  const next = { ...baseEnv };
  for (const key of [...ISOLATED_HOME_ENV_KEYS, ...NPM_SCRUB_ENV_KEYS]) {
    delete next[key];
  }
  return next;
}

/**
 * Verify that the repository has a clean git working tree.
 */
export function verifyCleanGitStatus({ root = DEFAULT_ROOT, runCommand = defaultRunCommand } = {}) {
  const inside = runCommand('git', ['rev-parse', '--is-inside-work-tree'], { cwd: root });
  if (inside.status !== 0 || inside.stdout.trim() !== 'true') {
    throw new Error(`Not a git working tree: ${root}`);
  }

  const status = runCommand('git', ['status', '--porcelain'], { cwd: root });
  if (status.status !== 0) {
    throw new Error(formatCommandFailure('git status --porcelain', status));
  }

  const dirtyLines = status.stdout.split(/\r?\n/).filter(Boolean);
  if (dirtyLines.length > 0) {
    throw new Error(
      `Git working tree is not clean. Commit or stash changes before publishing:\n${dirtyLines.join('\n')}`,
    );
  }
}

/**
 * Resolve the target release tag (if omitted) and verify that a published (non-draft)
 * GitHub Release exists for it.
 */
export function resolveAndVerifyGitHubRelease({ repo, tag = null, runCommand = defaultRunCommand } = {}) {
  const endpoint = tag
    ? `repos/${repo}/releases/tags/${encodeURIComponent(tag)}`
    : `repos/${repo}/releases`;

  const res = runCommand('gh', ['api', endpoint]);
  if (res.status !== 0) {
    const hint = res.error?.code === 'ENOENT'
      ? 'GitHub CLI (`gh`) was not found on PATH. Install `gh` and run `gh auth login`.'
      : `Could not verify published GitHub Release via \`gh api ${endpoint}\`. Ensure the release is published and \`gh auth status\` is valid.`;
    throw new Error(`${hint}\n${formatCommandFailure(`gh api ${endpoint}`, res)}`);
  }

  let parsed;
  try {
    parsed = JSON.parse(res.stdout);
  } catch (err) {
    throw new Error(`Failed to parse GitHub Release response from \`gh api ${endpoint}\`: ${err.message}`);
  }

  const release = tag
    ? parsed
    : Array.isArray(parsed)
      ? parsed.find(item => item && item.draft === false)
      : null;

  if (!release || typeof release.tag_name !== 'string' || !release.tag_name.trim()) {
    throw new Error(
      tag
        ? `GitHub Release for tag "${tag}" was not found in ${repo}.`
        : `No published GitHub Release found in ${repo}. Publish a release or pass --tag <tag>.`,
    );
  }

  if (release.draft === true) {
    throw new Error(`GitHub Release "${release.tag_name}" is still a draft. Publish it on GitHub first.`);
  }

  const resolvedTag = release.tag_name.trim().replace(/^refs\/tags\//, '');
  if (!TAG_PATTERN.test(resolvedTag)) {
    throw new Error(`Invalid GitHub Release tag "${resolvedTag}".`);
  }

  return {
    tag: resolvedTag,
    url: release.html_url || `https://github.com/${repo}/releases/tag/${resolvedTag}`,
    prerelease: Boolean(release.prerelease),
  };
}

/**
 * Pack the npm tarball, install it into an isolated temp prefix with an empty HOME,
 * and smoke-test `pdd --version` and `pdd --help`.
 */
export function buildAndSmokeTestNpm({
  root = DEFAULT_ROOT,
  scratchDir,
  version,
  packageName,
  npmRegistry = DEFAULT_NPM_REGISTRY,
  offline = false,
  env = process.env,
  runCommand = defaultRunCommand,
  log = console.log,
} = {}) {
  const npmDistDir = join(scratchDir, 'npm-dist');
  const npmPackCache = join(scratchDir, 'npm-pack-cache');
  const smokeDir = join(scratchDir, 'npm-smoke');
  const installHome = join(smokeDir, 'install-home');
  const smokeHome = join(smokeDir, 'home');
  const smokeState = join(smokeDir, 'state');
  const smokeInstall = join(smokeDir, 'install');
  const smokeInstallCache = join(smokeDir, 'install-cache');

  mkdirSync(npmDistDir, { recursive: true });
  mkdirSync(npmPackCache, { recursive: true });
  mkdirSync(installHome, { recursive: true });
  mkdirSync(smokeHome, { recursive: true });
  mkdirSync(smokeState, { recursive: true });
  mkdirSync(smokeInstall, { recursive: true });
  mkdirSync(smokeInstallCache, { recursive: true });

  const baseEnv = buildScrubbedBaseEnv(env);
  const packEnv = {
    ...baseEnv,
    COPYFILE_DISABLE: '1',
    npm_config_cache: npmPackCache,
  };

  const packRes = runCommand('npm', ['pack', '--ignore-scripts', '--json', '--pack-destination', npmDistDir], {
    cwd: root,
    env: packEnv,
  });
  if (packRes.status !== 0) {
    throw new Error(formatCommandFailure('npm pack', packRes));
  }

  let packedList;
  try {
    packedList = JSON.parse(packRes.stdout);
  } catch (err) {
    throw new Error(`Could not parse \`npm pack --json\` output: ${err.message}`);
  }
  const packed = Array.isArray(packedList) ? packedList[0] : null;
  if (!packed?.filename) {
    throw new Error('`npm pack --json` did not report a tarball filename.');
  }
  const tarballPath = join(npmDistDir, packed.filename);
  if (!existsSync(tarballPath)) {
    throw new Error(`Packed npm tarball was not created at ${tarballPath}.`);
  }

  const installArgs = [
    'install',
    '--prefix',
    smokeInstall,
    '--ignore-scripts',
    '--no-audit',
    '--no-fund',
    '--registry',
    npmRegistry,
  ];
  if (offline) installArgs.push('--offline');
  installArgs.push(tarballPath);

  const installEnv = {
    ...baseEnv,
    HOME: installHome,
    USERPROFILE: installHome,
    npm_config_cache: smokeInstallCache,
  };
  const installRes = runCommand('npm', installArgs, { cwd: smokeDir, env: installEnv });
  if (installRes.status !== 0) {
    throw new Error(formatCommandFailure('npm smoke-test install', installRes));
  }

  const installBinDir = join(smokeInstall, 'node_modules', '.bin');
  const binName = process.platform === 'win32' ? 'pdd.cmd' : 'pdd';
  const pddBin = join(installBinDir, binName);
  if (!existsSync(pddBin)) {
    throw new Error(`Smoke-tested npm install did not expose ${binName} at ${pddBin}.`);
  }

  const nodeBinDir = createIsolatedNodeBinDir(smokeDir);
  const cliEnv = {
    ...baseEnv,
    HOME: smokeHome,
    USERPROFILE: smokeHome,
    PDD_STATE_DIR: smokeState,
    PDD_NO_UPDATE_CHECK: '1',
    PATH: buildIsolatedPddPath(installBinDir, baseEnv.PATH, nodeBinDir),
  };

  const versionRes = runCommand(pddBin, ['--version'], { cwd: smokeHome, env: cliEnv });
  if (versionRes.status !== 0) {
    throw new Error(formatCommandFailure('npm smoke-test `pdd --version`', versionRes));
  }
  if (versionRes.stdout.trim() !== version) {
    throw new Error(
      `npm smoke-test \`pdd --version\` printed "${versionRes.stdout.trim()}", expected "${version}".`,
    );
  }
  if (versionRes.stderr.trim() !== '') {
    throw new Error(`npm smoke-test \`pdd --version\` wrote unexpected stderr:\n${versionRes.stderr}`);
  }

  const helpRes = runCommand(pddBin, ['--help'], { cwd: smokeHome, env: cliEnv });
  if (helpRes.status !== 0) {
    throw new Error(formatCommandFailure('npm smoke-test `pdd --help`', helpRes));
  }
  if (!/usage:\s*pdd|\bpdd\b/i.test(helpRes.stdout)) {
    throw new Error('npm smoke-test `pdd --help` did not print expected PDD help output.');
  }

  const distTag = npmDistTagForVersion(version);
  log(`  npm tarball verified: ${packed.filename} (${packageName}@${version}, dist-tag: ${distTag})`);
  return {
    packageName,
    version,
    filename: packed.filename,
    tarballPath,
    distTag,
  };
}

/**
 * Probe available Python 3 interpreters and `build` / `twine` tooling.
 */
export function resolvePythonTools({
  pythonBin = null,
  env = process.env,
  runCommand = defaultRunCommand,
} = {}) {
  const probeScript = [
    'import importlib.util, json, sys',
    'print(json.dumps({',
    '  "executable": sys.executable,',
    '  "major": sys.version_info[0],',
    '  "minor": sys.version_info[1],',
    '  "hasBuild": importlib.util.find_spec("build") is not None,',
    '  "hasTwine": importlib.util.find_spec("twine") is not None,',
    '}))',
  ].join('\n');

  const explicit = pythonBin || String(env.PDD_RELEASE_PYTHON || '').trim() || null;
  const candidates = explicit ? [explicit] : ['python3', 'python'];
  const probeEnv = { ...env, PYTHONDONTWRITEBYTECODE: '1' };
  const found = [];

  for (const cmd of candidates) {
    const res = runCommand(cmd, ['-B', '-c', probeScript], { env: probeEnv });
    if (res.status !== 0) continue;
    try {
      const info = JSON.parse(res.stdout.trim());
      if (info && Number(info.major) >= 3) {
        const entry = {
          cmd,
          executable: info.executable || cmd,
          major: Number(info.major),
          minor: Number(info.minor ?? 0),
          hasBuild: Boolean(info.hasBuild),
          hasTwine: Boolean(info.hasTwine),
        };
        found.push(entry);
        if (entry.hasBuild && entry.hasTwine) break;
      }
    } catch {
      // Ignore non-JSON probe output.
    }
  }

  const selected =
    found.find(item => item.hasBuild && item.hasTwine)
    ?? found.find(item => item.hasBuild)
    ?? found[0]
    ?? null;

  let twineCmd = null;
  if (selected?.hasTwine) {
    twineCmd = { cmd: selected.cmd, argsPrefix: ['-B', '-m', 'twine'] };
  } else {
    const standalone = runCommand('twine', ['--version'], { env: probeEnv });
    if (standalone.status === 0) {
      twineCmd = { cmd: 'twine', argsPrefix: [] };
    }
  }

  return { python: selected, twineCmd };
}

function copyIsolatedPythonSource(root, destDir) {
  const srcDir = join(root, 'python');
  cpSync(srcDir, destDir, {
    recursive: true,
    filter: srcPath => {
      const rel = srcPath.slice(srcDir.length).replace(/^[/\\]+/, '');
      if (!rel) return true;
      const segments = rel.split(/[/\\]/);
      return !segments.some(seg => PYTHON_COPY_SKIP.has(seg) || seg.endsWith('.egg-info'));
    },
  });
}

/**
 * Stage the bundled JS CLI into an isolated copy of `python/`, build sdist and wheel,
 * and run `twine check` when available (failing closed in live mode if missing).
 */
export function buildAndVerifyPypi({
  root = DEFAULT_ROOT,
  scratchDir,
  version,
  pypiName = 'pdd-cli',
  dryRun = false,
  pythonBin = null,
  env = process.env,
  stageBundle = stagePypiBundle,
  runCommand = defaultRunCommand,
  log = console.log,
} = {}) {
  const { python, twineCmd } = resolvePythonTools({ pythonBin, env, runCommand });
  if (!python) {
    throw new Error(
      'Python 3 was not found on PATH. Install Python 3 and run: python3 -m pip install --upgrade build twine',
    );
  }
  if (!python.hasBuild) {
    throw new Error(
      `Python "build" module is missing for ${python.cmd} (${python.executable}). ` +
      `Install build tools with: ${python.cmd} -m pip install --upgrade build twine`,
    );
  }
  if (!dryRun && !twineCmd) {
    throw new Error(
      `Python "twine" is required for live PyPI upload. ` +
      `Install twine with: ${python.cmd} -m pip install --upgrade twine`,
    );
  }

  const pySrcDir = join(scratchDir, 'python-src');
  const pypiDistDir = join(scratchDir, 'pypi-dist');
  mkdirSync(pypiDistDir, { recursive: true });
  copyIsolatedPythonSource(root, pySrcDir);

  stageBundle({
    root,
    bundleDir: join(pySrcDir, 'pdd_cli', '_bundled'),
  });

  const pyEnv = { ...env, PYTHONDONTWRITEBYTECODE: '1' };
  const buildRes = runCommand(python.cmd, ['-B', '-m', 'build', '--outdir', pypiDistDir, pySrcDir], {
    cwd: scratchDir,
    env: pyEnv,
  });
  if (buildRes.status !== 0) {
    throw new Error(formatCommandFailure(`${python.cmd} -m build`, buildRes));
  }

  const pep440Version = toPep440Version(version);
  const builtFiles = readdirSync(pypiDistDir).sort();
  const wheels = builtFiles.filter(name => name.endsWith('.whl') && name.includes(`-${pep440Version}-`));
  const sdists = builtFiles.filter(name => name.endsWith('.tar.gz') && name.includes(`-${pep440Version}.tar.gz`));
  if (wheels.length === 0 || sdists.length === 0) {
    throw new Error(
      `Expected both wheel (.whl) and sdist (.tar.gz) for version ${pep440Version} in ${pypiDistDir}; found: ${builtFiles.join(', ') || '(none)'}`,
    );
  }
  const distFiles = [...sdists, ...wheels].map(name => join(pypiDistDir, name));

  let twineChecked = false;
  if (twineCmd) {
    const checkRes = runCommand(twineCmd.cmd, [...twineCmd.argsPrefix, 'check', ...distFiles], {
      cwd: scratchDir,
      env: pyEnv,
    });
    if (checkRes.status !== 0) {
      throw new Error(formatCommandFailure('twine check', checkRes));
    }
    twineChecked = true;
    log(`  PyPI artifacts built and checked with twine: ${builtFiles.join(', ')}`);
  } else {
    log(
      `  PyPI artifacts built: ${builtFiles.join(', ')}\n` +
      `  Warning: twine is not installed; skipped \`twine check\`. ` +
      `Install with: ${python.cmd} -m pip install --upgrade twine (required before live PyPI publish).`,
    );
  }

  return {
    pypiName,
    version,
    pep440Version,
    python: python.cmd,
    twineCmd,
    twineChecked,
    distFiles,
    filenames: builtFiles,
  };
}

function isNpmNotFound(res) {
  const combined = `${res.stderr}\n${res.stdout}`;
  return /E404|404\b|not found|is not in this registry/i.test(combined);
}

/**
 * Check whether `<packageName>@<version>` is already live on npm.
 */
export function checkNpmVersionPublished({
  packageName,
  version,
  npmRegistry = DEFAULT_NPM_REGISTRY,
  env = process.env,
  runCommand = defaultRunCommand,
} = {}) {
  const res = runCommand(
    'npm',
    ['view', `${packageName}@${version}`, 'version', '--registry', npmRegistry],
    { env: buildScrubbedBaseEnv(env) },
  );
  if (res.status === 0) {
    return res.stdout.trim() === version;
  }
  if (isNpmNotFound(res)) {
    return false;
  }
  throw new Error(formatCommandFailure(`npm view ${packageName}@${version}`, res));
}

/**
 * Publish the verified npm tarball with `--access public` (idempotent if already published).
 */
export function publishNpm({
  packageName,
  version,
  tarballPath,
  distTag = npmDistTagForVersion(version),
  npmRegistry = DEFAULT_NPM_REGISTRY,
  scratchDir,
  env = process.env,
  interactive = false,
  runCommand = defaultRunCommand,
  log = console.log,
} = {}) {
  if (checkNpmVersionPublished({ packageName, version, npmRegistry, env, runCommand })) {
    log(`  ${packageName}@${version} is already published on npm; skipping npm publish.`);
    return { published: false, skipped: true, packageName, version, distTag };
  }

  const npmToken = String(env.NPM_TOKEN || env.NODE_AUTH_TOKEN || '').trim();
  const args = [
    'publish',
    tarballPath,
    '--registry',
    npmRegistry,
    '--ignore-scripts',
    '--access',
    'public',
    '--tag',
    distTag,
  ];

  let userconfigPath = null;
  try {
    if (npmToken) {
      const registryUrl = new URL(npmRegistry);
      const authScope = `//${registryUrl.host}${registryUrl.pathname.replace(/\/+$/, '')}/`;
      userconfigPath = join(scratchDir || tmpdir(), `pdd-npmrc-${process.pid}-${Date.now()}`);
      writeFileSync(userconfigPath, `${authScope}:_authToken=${npmToken}\n`, { mode: 0o600 });
      args.push('--userconfig', userconfigPath);
    }

    const publishEnv = { ...env };
    delete publishEnv.npm_config_dry_run;
    const res = runCommand('npm', args, {
      env: publishEnv,
      stdio: interactive ? 'inherit' : ['ignore', 'pipe', 'pipe'],
    });
    if (res.status !== 0) {
      throw new Error(
        `npm publish failed for ${packageName}@${version}. Run \`npm login\` or set NPM_TOKEN with publish access.\n` +
        formatCommandFailure('npm publish', res),
      );
    }
    log(`  Published ${packageName}@${version} to ${npmRegistry} (tag: ${distTag}).`);
    return { published: true, skipped: false, packageName, version, distTag };
  } finally {
    if (userconfigPath) {
      rmSync(userconfigPath, { force: true });
    }
  }
}

/**
 * Verify that `<packageName>@<version>` is visible on the live npm registry.
 */
export async function verifyNpmLiveVersion({
  packageName,
  version,
  npmRegistry = DEFAULT_NPM_REGISTRY,
  attempts = 5,
  delayMs = 2000,
  env = process.env,
  runCommand = defaultRunCommand,
  sleep = defaultSleep,
} = {}) {
  let lastDetail = '';
  for (let attempt = 1; attempt <= attempts; attempt++) {
    const res = runCommand(
      'npm',
      ['view', `${packageName}@${version}`, 'version', '--registry', npmRegistry],
      { env: buildScrubbedBaseEnv(env) },
    );
    if (res.status === 0 && res.stdout.trim() === version) {
      return { ok: true, version, attempts: attempt };
    }
    lastDetail = [res.stderr, res.stdout].map(s => String(s || '').trim()).filter(Boolean).join(' ')
      || `exit ${res.status}`;
    if (attempt < attempts && delayMs > 0) {
      await sleep(delayMs);
    }
  }
  throw new Error(
    `Live npm verification failed: ${packageName}@${version} was not returned by ${npmRegistry} after ${attempts} attempts (${lastDetail}).`,
  );
}

/**
 * Query PyPI JSON API to check whether a package version is live with uploaded files.
 */
export async function queryPypiRelease({
  pypiName = 'pdd-cli',
  version,
  pypiBaseUrl = DEFAULT_PYPI_BASE_URL,
  fetchImpl = globalThis.fetch,
} = {}) {
  const pep440 = toPep440Version(version);
  const url = `${pypiBaseUrl.replace(/\/+$/, '')}/pypi/${encodeURIComponent(pypiName)}/${encodeURIComponent(pep440)}/json`;
  const res = await fetchImpl(url, { headers: { Accept: 'application/json' } });
  if (res.status === 404) {
    return { exists: false, status: 404, url, version: pep440, fileCount: 0 };
  }
  if (!res.ok) {
    throw new Error(`PyPI lookup failed at ${url} (HTTP ${res.status}).`);
  }
  const data = await res.json();
  const fileCount = Array.isArray(data?.urls) ? data.urls.length : 0;
  const liveVersion = data?.info?.version ?? null;
  return {
    exists: liveVersion === pep440 && fileCount > 0,
    status: res.status,
    url,
    version: liveVersion,
    fileCount,
  };
}

/**
 * Upload the verified sdist and wheel to PyPI via `twine upload` (idempotent if already live).
 */
export async function publishPypi({
  pypiName = 'pdd-cli',
  version,
  distFiles,
  twineCmd,
  pypiBaseUrl = DEFAULT_PYPI_BASE_URL,
  env = process.env,
  interactive = false,
  runCommand = defaultRunCommand,
  fetchImpl = globalThis.fetch,
  log = console.log,
} = {}) {
  const existing = await queryPypiRelease({ pypiName, version, pypiBaseUrl, fetchImpl });
  if (existing.exists) {
    log(`  ${pypiName} ${existing.version} is already published on PyPI; skipping twine upload.`);
    return { published: false, skipped: true, pypiName, version: existing.version };
  }

  if (!twineCmd) {
    throw new Error('twine is required to publish pdd-cli to PyPI. Install with: python3 -m pip install --upgrade twine');
  }

  const uploadEnv = { ...env, PYTHONDONTWRITEBYTECODE: '1' };
  const apiToken = String(env.PYPI_API_TOKEN || '').trim();
  if (apiToken && !String(env.TWINE_PASSWORD || '').trim()) {
    uploadEnv.TWINE_USERNAME = '__token__';
    uploadEnv.TWINE_PASSWORD = apiToken;
  }

  const res = runCommand(
    twineCmd.cmd,
    [...twineCmd.argsPrefix, 'upload', '--skip-existing', ...distFiles],
    {
      env: uploadEnv,
      stdio: interactive ? 'inherit' : ['ignore', 'pipe', 'pipe'],
    },
  );
  if (res.status !== 0) {
    throw new Error(
      `twine upload failed for ${pypiName} ${version}. Set PYPI_API_TOKEN or configure ~/.pypirc with a PyPI token.\n` +
      formatCommandFailure('twine upload', res),
    );
  }
  log(`  Uploaded ${pypiName} ${toPep440Version(version)} to PyPI.`);
  return { published: true, skipped: false, pypiName, version: toPep440Version(version) };
}

/**
 * Verify that `<pypiName> <version>` is live on PyPI after upload.
 */
export async function verifyPypiLiveVersion({
  pypiName = 'pdd-cli',
  version,
  pypiBaseUrl = DEFAULT_PYPI_BASE_URL,
  attempts = 5,
  delayMs = 2000,
  fetchImpl = globalThis.fetch,
  sleep = defaultSleep,
} = {}) {
  const expected = toPep440Version(version);
  let lastStatus = 'unknown';
  for (let attempt = 1; attempt <= attempts; attempt++) {
    try {
      const check = await queryPypiRelease({ pypiName, version: expected, pypiBaseUrl, fetchImpl });
      if (check.exists) {
        return { ok: true, version: check.version, fileCount: check.fileCount, attempts: attempt };
      }
      lastStatus = `HTTP ${check.status} (files: ${check.fileCount})`;
    } catch (err) {
      lastStatus = err?.message || String(err);
    }
    if (attempt < attempts && delayMs > 0) {
      await sleep(delayMs);
    }
  }
  throw new Error(
    `Live PyPI verification failed: ${pypiName} ${expected} was not visible on ${pypiBaseUrl} after ${attempts} attempts (${lastStatus}).`,
  );
}

/**
 * Execute the full maintainer release verification, artifact build, smoke-test,
 * and (when not `--dry-run`) live npm + PyPI publish and registry verification.
 */
export async function publishRelease(options = {}, deps = {}) {
  const {
    dryRun = false,
    dryRunFromNpmEnv = false,
    tag = null,
    npmOnly = false,
    pypiOnly = false,
    repo: explicitRepo = null,
    root = DEFAULT_ROOT,
    pythonBin = null,
    npmRegistry = DEFAULT_NPM_REGISTRY,
    pypiBaseUrl = DEFAULT_PYPI_BASE_URL,
    offlineNpmInstall = false,
    verifyAttempts = 5,
    verifyDelayMs = 2000,
    interactive = false,
  } = options;

  if (npmOnly && pypiOnly) {
    throw new Error('Cannot combine --npm-only and --pypi-only.');
  }

  const runCommand = deps.runCommand ?? defaultRunCommand;
  const fetchImpl = deps.fetchImpl ?? globalThis.fetch;
  const sleep = deps.sleep ?? defaultSleep;
  const stageBundle = deps.stageBundle ?? stagePypiBundle;
  const env = deps.env ?? process.env;
  const log = deps.log ?? console.log;

  const runNpm = !pypiOnly;
  const runPypi = !npmOnly;

  const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  if (typeof pkg.name !== 'string' || !pkg.name.trim()) {
    throw new Error('package.json is missing a valid package name.');
  }
  if (pkg.private === true) {
    throw new Error(`package.json marks ${pkg.name} as private; refusing to publish.`);
  }

  const pyprojectPath = join(root, 'python', 'pyproject.toml');
  const pypiName = existsSync(pyprojectPath)
    ? (readPyprojectName(readFileSync(pyprojectPath, 'utf8')) ?? 'pdd-cli')
    : 'pdd-cli';

  const targetsLabel = [runNpm ? `npm (${pkg.name})` : null, runPypi ? `PyPI (${pypiName})` : null]
    .filter(Boolean)
    .join(' + ');
  log(`Mode: ${dryRun ? 'DRY RUN (no live publish)' : 'LIVE PUBLISH'} | Targets: ${targetsLabel}`);
  if (dryRunFromNpmEnv) {
    log('Note: Detected npm_config_dry_run=true; running in --dry-run mode. Use `npm run release:publish -- --dry-run` to pass flags directly.');
  }

  log('[1/4] Verifying clean git status, published GitHub Release, and version parity...');
  verifyCleanGitStatus({ root, runCommand });
  const repo = explicitRepo || deriveGitHubRepo(root, runCommand);
  const release = resolveAndVerifyGitHubRelease({ repo, tag, runCommand });

  const parity = checkVersionParity({ root, tag: release.tag });
  if (!parity.ok) {
    throw new Error(`Release version parity check failed:\n${parity.problems.join('\n')}`);
  }
  const version = parity.version;
  log(`  Verified clean git tree, GitHub Release ${release.tag} (${release.url}), and version parity (${version}).`);

  const tagCommit = runCommand('git', ['rev-parse', '--verify', `refs/tags/${release.tag}^{commit}`], { cwd: root });
  const headCommit = runCommand('git', ['rev-parse', 'HEAD'], { cwd: root });
  if (tagCommit.status === 0 && headCommit.status === 0 && tagCommit.stdout.trim() !== headCommit.stdout.trim()) {
    log(
      `  Note: HEAD (${headCommit.stdout.trim().slice(0, 8)}) differs from local tag ${release.tag} (${tagCommit.stdout.trim().slice(0, 8)}).`,
    );
  }

  const scratchDir = mkdtempSync(join(tmpdir(), 'pdd-release-publish-'));
  try {
    let npmArtifact = null;
    if (runNpm) {
      log(`[2/4] Packing and smoke-testing ${pkg.name}@${version}...`);
      npmArtifact = buildAndSmokeTestNpm({
        root,
        scratchDir,
        version,
        packageName: pkg.name,
        npmRegistry,
        offline: offlineNpmInstall,
        env,
        runCommand,
        log,
      });
    } else {
      log('[2/4] Skipping npm build and smoke test (--pypi-only).');
    }

    let pypiArtifact = null;
    if (runPypi) {
      log(`[3/4] Staging, building, and verifying ${pypiName} ${version}...`);
      pypiArtifact = buildAndVerifyPypi({
        root,
        scratchDir,
        version,
        pypiName,
        dryRun,
        pythonBin,
        env,
        stageBundle,
        runCommand,
        log,
      });
    } else {
      log('[3/4] Skipping PyPI build and verification (--npm-only).');
    }

    if (dryRun) {
      log('[4/4] Dry run complete. No packages were published to live registries.');
      return {
        dryRun: true,
        repo,
        tag: release.tag,
        releaseUrl: release.url,
        version,
        npm: npmArtifact,
        pypi: pypiArtifact,
        published: { npm: null, pypi: null },
        verified: { npm: null, pypi: null },
      };
    }

    log('[4/4] Publishing artifacts and verifying live registries...');
    const published = { npm: null, pypi: null };
    const verified = { npm: null, pypi: null };

    if (runNpm) {
      published.npm = publishNpm({
        packageName: npmArtifact.packageName,
        version,
        tarballPath: npmArtifact.tarballPath,
        distTag: npmArtifact.distTag,
        npmRegistry,
        scratchDir,
        env,
        interactive,
        runCommand,
        log,
      });
      verified.npm = await verifyNpmLiveVersion({
        packageName: npmArtifact.packageName,
        version,
        npmRegistry,
        attempts: verifyAttempts,
        delayMs: verifyDelayMs,
        env,
        runCommand,
        sleep,
      });
      log(`  Live npm registry verified: ${npmArtifact.packageName}@${verified.npm.version}`);
    }

    if (runPypi) {
      published.pypi = await publishPypi({
        pypiName: pypiArtifact.pypiName,
        version,
        distFiles: pypiArtifact.distFiles,
        twineCmd: pypiArtifact.twineCmd,
        pypiBaseUrl,
        env,
        interactive,
        runCommand,
        fetchImpl,
        log,
      });
      verified.pypi = await verifyPypiLiveVersion({
        pypiName: pypiArtifact.pypiName,
        version,
        pypiBaseUrl,
        attempts: verifyAttempts,
        delayMs: verifyDelayMs,
        fetchImpl,
        sleep,
      });
      log(`  Live PyPI registry verified: ${pypiArtifact.pypiName} ${verified.pypi.version} (${verified.pypi.fileCount} files)`);
    }

    log(`Release publish complete for ${release.tag} (${version}).`);
    return {
      dryRun: false,
      repo,
      tag: release.tag,
      releaseUrl: release.url,
      version,
      npm: npmArtifact,
      pypi: pypiArtifact,
      published,
      verified,
    };
  } finally {
    rmSync(scratchDir, { recursive: true, force: true });
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const parsed = parsePublishArgs(process.argv.slice(2), process.env);
    if (parsed.help) {
      console.log(usageText());
      process.exit(0);
    }
    await publishRelease({
      ...parsed,
      interactive: Boolean(process.stdin.isTTY && process.stdout.isTTY),
    });
  } catch (err) {
    console.error(err?.message || String(err));
    process.exit(1);
  }
}
