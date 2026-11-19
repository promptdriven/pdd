import { execFileSync } from 'node:child_process';
import { chmodSync, cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const DEFAULT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');

export function normalizeReleaseTag(tag) {
  if (typeof tag !== 'string') return null;
  const trimmed = tag.trim().replace(/^refs\/tags\//, '');
  const match = /^(?:alpha-)?v?(\d+\.\d+\.\d+(?:[-+][\w.-]+)?)$/.exec(trimmed);
  return match ? match[1] : null;
}

export function readPyprojectField(pyprojectText, fieldName) {
  const lines = String(pyprojectText).split(/\r?\n/);
  const pattern = new RegExp(`^${fieldName}\\s*=\\s*"([^"]+)"\\s*(?:#.*)?$`);
  let inProject = false;
  for (const raw of lines) {
    const line = raw.trim();
    if (!line || line.startsWith('#')) continue;
    if (line.startsWith('[')) {
      inProject = line === '[project]';
      continue;
    }
    if (inProject) {
      const match = pattern.exec(line);
      if (match) return match[1];
    }
  }
  return null;
}

export function readPyprojectVersion(pyprojectText) {
  return readPyprojectField(pyprojectText, 'version');
}

export function readPythonInitVersion(initText) {
  const match = /^__version__\s*=\s*"([^"]+)"/m.exec(String(initText));
  return match ? match[1] : null;
}

export function checkVersionParity({ root = DEFAULT_ROOT, tag = null } = {}) {
  const pkgPath = join(root, 'package.json');
  const pyprojectPath = join(root, 'python', 'pyproject.toml');
  const pyInitPath = join(root, 'python', 'pdd_cli', '__init__.py');

  const pkg = JSON.parse(readFileSync(pkgPath, 'utf8'));
  const npmVersion = pkg.version;
  const pyprojectVersion = readPyprojectVersion(readFileSync(pyprojectPath, 'utf8'));
  const pyInitVersion = readPythonInitVersion(readFileSync(pyInitPath, 'utf8'));

  const problems = [];
  if (typeof npmVersion !== 'string' || !npmVersion) {
    problems.push('package.json is missing a valid version string.');
  }
  if (pyprojectVersion !== npmVersion) {
    problems.push(`python/pyproject.toml version (${pyprojectVersion ?? 'missing'}) != package.json version (${npmVersion}).`);
  }
  if (pyInitVersion !== npmVersion) {
    problems.push(`python/pdd_cli/__init__.py __version__ (${pyInitVersion ?? 'missing'}) != package.json version (${npmVersion}).`);
  }
  if (tag !== null && tag !== undefined && String(tag).trim() !== '') {
    const tagVersion = normalizeReleaseTag(tag);
    if (!tagVersion) {
      problems.push(`Release tag "${tag}" does not contain a valid semver version.`);
    } else if (tagVersion !== npmVersion) {
      problems.push(`Release tag "${tag}" (${tagVersion}) != package.json version (${npmVersion}).`);
    }
  }

  return {
    ok: problems.length === 0,
    version: npmVersion,
    pyprojectVersion,
    pyInitVersion,
    tagVersion: tag ? normalizeReleaseTag(tag) : null,
    problems,
  };
}

export function syncPypiVersion({ root = DEFAULT_ROOT } = {}) {
  const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  const version = pkg.version;
  if (typeof version !== 'string' || !version) {
    throw new Error('package.json is missing a valid version string.');
  }

  const pyprojectPath = join(root, 'python', 'pyproject.toml');
  const pyprojectText = readFileSync(pyprojectPath, 'utf8');
  let inProject = false;
  let replacedPyproject = false;
  const updatedPyproject = pyprojectText
    .split(/\r?\n/)
    .map(line => {
      const trimmed = line.trim();
      if (trimmed.startsWith('[')) {
        inProject = trimmed === '[project]';
        return line;
      }
      if (inProject && !replacedPyproject && /^version\s*=\s*"[^"]+"/.test(trimmed)) {
        replacedPyproject = true;
        return line.replace(/version\s*=\s*"[^"]+"/, `version = "${version}"`);
      }
      return line;
    })
    .join('\n');
  if (!replacedPyproject) {
    throw new Error('Could not find [project] version = "..." in python/pyproject.toml.');
  }
  writeFileSync(pyprojectPath, updatedPyproject);

  const pyInitPath = join(root, 'python', 'pdd_cli', '__init__.py');
  const pyInitText = readFileSync(pyInitPath, 'utf8');
  if (!/^__version__\s*=\s*"[^"]+"/m.test(pyInitText)) {
    throw new Error('Could not find __version__ = "..." in python/pdd_cli/__init__.py.');
  }
  const updatedInit = pyInitText.replace(/^__version__\s*=\s*"[^"]+"/m, `__version__ = "${version}"`);
  writeFileSync(pyInitPath, updatedInit);

  return version;
}

const STAGE_SCRUB_EXACT_KEYS = new Set([
  'NPM_TOKEN',
  'NODE_AUTH_TOKEN',
  'PYPI_API_TOKEN',
  'TWINE_PASSWORD',
  'TWINE_USERNAME',
]);
const STAGE_SCRUB_CI_KEYS = new Set([
  'npm_config_dry_run',
  'npm_config_tag',
  'npm_config_npm_only',
  'npm_config_pypi_only',
  'npm_config_cache',
]);

export function stagePypiBundle({ root = DEFAULT_ROOT, bundleDir: customBundleDir = null, env: sourceEnv = process.env } = {}) {
  const parity = checkVersionParity({ root });
  if (!parity.ok) {
    throw new Error(`Cannot stage PyPI bundle:\n${parity.problems.join('\n')}`);
  }

  const bundleDir = customBundleDir ?? join(root, 'python', 'pdd_cli', '_bundled');
  rmSync(bundleDir, { recursive: true, force: true });

  const scratch = mkdtempSync(join(tmpdir(), 'pdd-pypi-stage-'));
  try {
    const cacheDir = join(scratch, 'npm-cache');
    mkdirSync(cacheDir, { recursive: true });
    const baseEnv = { ...sourceEnv };
    for (const key of Object.keys(baseEnv)) {
      if (STAGE_SCRUB_EXACT_KEYS.has(key) || STAGE_SCRUB_CI_KEYS.has(key.toLowerCase())) {
        delete baseEnv[key];
      }
    }
    const env = { ...baseEnv, npm_config_cache: cacheDir, COPYFILE_DISABLE: '1' };
    const packOut = execFileSync('npm', ['pack', '--ignore-scripts', '--json', '--pack-destination', scratch], {
      cwd: root,
      env,
      encoding: 'utf8',
      maxBuffer: 16 * 1024 * 1024,
    });
    const packed = JSON.parse(packOut)[0];
    const archivePath = join(scratch, packed.filename);
    const extractDir = join(scratch, 'extract');
    mkdirSync(extractDir, { recursive: true });
    execFileSync('tar', ['-xzf', archivePath, '-C', extractDir], { env });

    const extractedPkg = join(extractDir, 'package');
    const manifest = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
    for (const dep of Object.keys(manifest.dependencies ?? {})) {
      const srcDep = join(root, 'node_modules', dep);
      if (!existsSync(srcDep)) {
        throw new Error(`Missing installed dependency ${dep} at ${srcDep}. Run npm ci first.`);
      }
      const dstDep = join(extractedPkg, 'node_modules', dep);
      mkdirSync(dirname(dstDep), { recursive: true });
      cpSync(srcDep, dstDep, { recursive: true, dereference: true });
    }

    cpSync(extractedPkg, bundleDir, { recursive: true, dereference: true });
    const entryMjs = join(bundleDir, 'bin', 'pdd.mjs');
    chmodSync(entryMjs, 0o755);

    const verifyEnv = {
      ...baseEnv,
      HOME: scratch,
      PDD_STATE_DIR: join(scratch, 'state'),
      PDD_NO_UPDATE_CHECK: '1',
      PDD_PATH_PROBE: '1',
    };
    const printed = execFileSync(process.execPath, [entryMjs, '--version'], {
      cwd: scratch,
      env: verifyEnv,
      encoding: 'utf8',
    }).trim();
    if (printed !== parity.version) {
      throw new Error(`Bundled CLI reported version "${printed}", expected "${parity.version}".`);
    }
    return bundleDir;
  } finally {
    rmSync(scratch, { recursive: true, force: true });
  }
}

function parseCliArgs(argv) {
  let check = false;
  let stageBundle = false;
  let cleanBundle = false;
  let tag = null;
  let root = DEFAULT_ROOT;

  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--check') check = true;
    else if (arg === '--stage-bundle') stageBundle = true;
    else if (arg === '--clean-bundle') cleanBundle = true;
    else if (arg === '--tag') tag = argv[++i] ?? '';
    else if (arg.startsWith('--tag=')) tag = arg.slice('--tag='.length);
    else if (arg === '--root') root = resolve(argv[++i] ?? '.');
    else if (arg.startsWith('--root=')) root = resolve(arg.slice('--root='.length));
    else throw new Error(`Unknown argument: ${arg}`);
  }
  return { check, stageBundle, cleanBundle, tag, root };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const opts = parseCliArgs(process.argv.slice(2));
    if (opts.cleanBundle) {
      rmSync(join(opts.root, 'python', 'pdd_cli', '_bundled'), { recursive: true, force: true });
      console.log('Removed python/pdd_cli/_bundled.');
    } else if (opts.stageBundle) {
      const parity = checkVersionParity({ root: opts.root, tag: opts.tag });
      if (!parity.ok) {
        for (const p of parity.problems) console.error(p);
        process.exit(1);
      }
      const dir = stagePypiBundle({ root: opts.root });
      console.log(`Staged bundled @promptdriven/pdd ${parity.version} into ${dir}.`);
    } else if (opts.check) {
      const parity = checkVersionParity({ root: opts.root, tag: opts.tag });
      if (!parity.ok) {
        for (const p of parity.problems) console.error(p);
        console.error('Run `node scripts/sync-pypi-version.mjs` to sync Python package versions with package.json.');
        process.exit(1);
      }
      const tagSuffix = parity.tagVersion ? ` (release tag: ${opts.tag})` : '';
      console.log(`Version parity verified: ${parity.version}${tagSuffix}`);
    } else {
      const version = syncPypiVersion({ root: opts.root });
      console.log(`Synced Python wrapper version to ${version}.`);
    }
  } catch (err) {
    console.error(err?.message || String(err));
    process.exit(1);
  }
}
