import { spawnSync } from 'node:child_process';
import {
  accessSync, constants, cpSync, existsSync, mkdirSync, mkdtempSync,
  readdirSync, readFileSync, rmSync, statSync, symlinkSync, writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, delimiter, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import { checkVersionParity, readPyprojectField, stagePypiBundle, toPep440Version } from './sync-pypi-version.mjs';

export { toPep440Version };

const DEFAULT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const DEFAULT_REPO = 'promptdriven/pdd';
const DEFAULT_NPM_REGISTRY = 'https://registry.npmjs.org';
const DEFAULT_PYPI_BASE_URL = 'https://pypi.org';
function readRuntimeClientPackageName(root = DEFAULT_ROOT) {
  try {
    const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
    return Object.keys(pkg.dependencies ?? {}).find(name => name.endsWith('/runtime-client')) ?? null;
  } catch {
    return null;
  }
}

export const RUNTIME_CLIENT_PACKAGE = readRuntimeClientPackageName(DEFAULT_ROOT);
const TAG_RE = /^[A-Za-z0-9._-]+$/;
const REPO_RE = /^[A-Za-z0-9._-]+\/[A-Za-z0-9._-]+$/;
const SHA_RE = /^[0-9a-f]{7,64}$/i;
const NPM_NOT_FOUND_RE = /E404|404 Not Found|is not in this registry/i;
const CONTROL_CHAR_RE = /[\x00-\x1f\x7f]/;

const SECRET_ENV_KEYS = ['NPM_TOKEN', 'NODE_AUTH_TOKEN', 'PYPI_API_TOKEN', 'TWINE_PASSWORD'];
const PUBLISH_AUTH_ENV_KEYS = [...SECRET_ENV_KEYS, 'TWINE_USERNAME'];
const ISOLATED_HOME_ENV_KEYS = [
  'XDG_CONFIG_HOME', 'XDG_STATE_HOME', 'XDG_CACHE_HOME', 'XDG_DATA_HOME', 'XDG_RUNTIME_DIR',
  'CODEX_HOME', 'CLAUDE_CONFIG_DIR', 'GEMINI_CLI_HOME', 'AGY_HOME', 'GH_CONFIG_DIR',
];
const NPM_SCRUB_ENV_KEYS = [
  'npm_config_dry_run', 'npm_config_tag', 'npm_config_npm_only', 'npm_config_pypi_only',
  'npm_config_allow_stale_runtime_client',
  'npm_config_cache', 'npm_config_prefix', 'npm_config_userconfig', 'npm_config_globalconfig', 'npm_config_registry',
];
const TWINE_REPO_ENV_KEYS = ['TWINE_REPOSITORY', 'TWINE_REPOSITORY_URL'];
const PYTHON_COPY_SKIP = new Set(['_bundled', 'build', 'dist', '__pycache__']);
const USAGE = `Usage: node scripts/publish-release.mjs [options]
       npm run release:publish -- [options]

Options:
  --dry-run          Verify, build, and smoke-test without publishing
  --tag <tag>        Target GitHub Release tag (default: latest published release)
  --npm-only         Verify, smoke-test, and publish only @promptdriven/pdd on npm
  --pypi-only        Build, verify, and publish only pdd-cli on PyPI
  --repo <owner/org> GitHub repository slug (default: derived from package.json/origin)
  --python <bin>     Python 3 executable to use for build and twine
  --root <dir>       Repository root path (default: current repo)
  --allow-stale-runtime-client  Allow publishing when pinned runtime client lags latest npm version
  -h, --help         Show this help text`;

function defaultRunCommand(cmd, args, opts = {}) {
  const res = spawnSync(cmd, args, { cwd: opts.cwd, env: opts.env ?? process.env, encoding: 'utf8', stdio: opts.stdio ?? ['ignore', 'pipe', 'pipe'], maxBuffer: opts.maxBuffer ?? 32 * 1024 * 1024 });
  return { status: res.status ?? (res.error ? 1 : 0), stdout: res.stdout ?? '', stderr: res.stderr ?? '', error: res.error ?? null };
}

const defaultSleep = ms => new Promise(done => setTimeout(done, ms));

function collectSecrets(env = {}) {
  const vals = new Set();
  for (const key of SECRET_ENV_KEYS) {
    const raw = env?.[key];
    if (typeof raw === 'string') {
      if (raw.length >= 4) vals.add(raw);
      if (raw.trim().length >= 4) vals.add(raw.trim());
    }
  }
  return [...vals].sort((a, b) => b.length - a.length);
}

const redactSecrets = (text, secrets = []) => secrets.reduce((out, s) => (s ? out.split(s).join('[REDACTED]') : out), String(text ?? ''));

function formatCommandFailure(label, res, secrets = []) {
  if (res.error) return redactSecrets(`${label} failed: ${res.error.message}`, secrets);
  const detail = [res.stderr, res.stdout].map(s => String(s || '').trim()).filter(Boolean).join('\n');
  return redactSecrets(detail ? `${label} failed (exit ${res.status}):\n${detail}` : `${label} failed (exit ${res.status}).`, secrets);
}

function runOrThrow(runCommand, label, cmd, args, opts, secrets) {
  const res = runCommand(cmd, args, opts);
  if (res.status !== 0) throw new Error(formatCommandFailure(label, res, secrets));
  return res;
}

function scrubEnv(baseEnv, ...keyLists) {
  const next = { ...baseEnv };
  const exact = new Set();
  const ci = new Set();
  for (const keys of keyLists) {
    for (const k of keys) {
      if (/^npm_config_/i.test(k)) ci.add(k.toLowerCase());
      else exact.add(k);
    }
  }
  for (const key of Object.keys(next)) {
    if (exact.has(key) || ci.has(key.toLowerCase())) delete next[key];
  }
  return next;
}

function findEnvValuesCI(env, key) {
  if (!env) return [];
  const target = key.toLowerCase();
  return Object.entries(env).filter(([k, v]) => k.toLowerCase() === target && v !== undefined).map(([, v]) => v);
}

function isTruthyNpmConfig(env, key) {
  return findEnvValuesCI(env, key).some(v => {
    const normalized = String(v).trim().toLowerCase();
    return normalized !== 'false' && normalized !== '0';
  });
}

function parseJsonOrThrow(raw, label) {
  try { return JSON.parse(raw); } catch (err) { throw new Error(`Failed to parse ${label}: ${err.message}`); }
}

async function pollUntil({ attempts, delayMs, sleep, check, formatFailure }) {
  let lastDetail = 'unknown';
  for (let attempt = 1; attempt <= attempts; attempt++) {
    const result = await check();
    if (result.ok) return { ...result, attempts: attempt };
    lastDetail = result.detail;
    if (attempt < attempts && delayMs > 0) await sleep(delayMs);
  }
  throw new Error(formatFailure(lastDetail));
}

const CLI_OPTIONS = {
  'dry-run': { type: 'boolean', default: false }, 'npm-only': { type: 'boolean', default: false },
  'pypi-only': { type: 'boolean', default: false }, 'allow-stale-runtime-client': { type: 'boolean', default: false },
  tag: { type: 'string' }, repo: { type: 'string' },
  root: { type: 'string' }, python: { type: 'string' }, help: { type: 'boolean', short: 'h', default: false },
};

/** Parse CLI flags via node:util parseArgs and trap flags swallowed by `npm run` when `--` is omitted. */
export function parsePublishArgs(argv, env = {}) {
  const { values } = parseArgs({ args: argv, strict: true, allowPositionals: false, options: CLI_OPTIONS });
  const opt = (flag, val) => {
    if (val === undefined) return null;
    if (val === '' || val.startsWith('-')) throw new Error(`Missing value for ${flag}.`);
    return val;
  };
  const help = Boolean(values.help);
  const npmOnly = Boolean(values['npm-only']);
  const pypiOnly = Boolean(values['pypi-only']);
  const explicitDryRun = Boolean(values['dry-run']);
  const dryRunFromNpmEnv = !explicitDryRun && isTruthyNpmConfig(env, 'npm_config_dry_run');
  let tag = opt('--tag', values.tag);
  let repo = opt('--repo', values.repo);
  const rootArg = opt('--root', values.root);
  const pythonBin = opt('--python', values.python);

  const allowStaleRuntimeClient = Boolean(values['allow-stale-runtime-client']);
  if (!help) {
    for (const [key, flag, present] of [
      ['npm_config_npm_only', '--npm-only', npmOnly],
      ['npm_config_pypi_only', '--pypi-only', pypiOnly],
      ['npm_config_allow_stale_runtime_client', '--allow-stale-runtime-client', allowStaleRuntimeClient],
    ]) {
      if (!present && isTruthyNpmConfig(env, key)) {
        throw new Error(`Detected ${key} without ${flag}. Use \`--\` before flags: npm run release:publish -- ${flag}`);
      }
    }
    const envTag = findEnvValuesCI(env, 'npm_config_tag').map(v => String(v).trim()).find(v => v && v !== 'latest') || '';
    if (tag === null && envTag) {
      throw new Error(`Detected npm_config_tag="${envTag}" without --tag. Use \`--\` before flags: npm run release:publish -- --tag ${envTag}`);
    }
  }
  if (npmOnly && pypiOnly) throw new Error('Cannot combine --npm-only and --pypi-only.');
  if (tag !== null && !TAG_RE.test((tag = tag.trim().replace(/^refs\/tags\//, '')))) throw new Error(`Invalid GitHub Release tag "${tag}".`);
  if (repo !== null && !REPO_RE.test((repo = repo.trim()))) throw new Error(`Invalid GitHub repository "${repo}". Expected OWNER/REPO.`);
  return { dryRun: explicitDryRun || dryRunFromNpmEnv, dryRunFromNpmEnv, tag, npmOnly, pypiOnly, allowStaleRuntimeClient, repo, root: rootArg ? resolve(rootArg) : DEFAULT_ROOT, pythonBin, help };
}

/** Select npm dist-tag matching .github/workflows/release.yml. */
export function npmDistTagForVersion(version) {
  const raw = String(version).trim().toLowerCase();
  if (!raw.includes('-')) return 'latest';
  if (/-rc(?:\.|\d|$)/.test(raw)) return 'next';
  if (/-beta(?:\.|\d|$)/.test(raw)) return 'beta';
  if (/-alpha(?:\.|\d|$)/.test(raw)) return 'alpha';
  return 'alpha';
}

function deriveGitHubRepo(root, env, runCommand) {
  const extract = raw => {
    if (typeof raw !== 'string') return null;
    const trimmed = raw.trim();
    if (REPO_RE.test(trimmed)) return trimmed;
    return /github\.com[:/]([A-Za-z0-9._-]+\/[A-Za-z0-9._-]+?)(?:\.git)?(?:[#?].*)?$/.exec(trimmed)?.[1] ?? null;
  };
  try {
    const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
    const fromPkg = extract(typeof pkg.repository === 'string' ? pkg.repository : pkg.repository?.url);
    if (fromPkg) return fromPkg;
  } catch { /* Fall back to git remote or default. */ }
  const remote = runCommand('git', ['remote', 'get-url', 'origin'], { cwd: root, env });
  return (remote.status === 0 && extract(remote.stdout)) || DEFAULT_REPO;
}

function hasHostPdd(dir) {
  const bins = process.platform === 'win32' ? ['pdd.cmd', 'pdd.exe', 'pdd'] : ['pdd'];
  const hasBin = bins.some(name => {
    try { const p = join(dir, name); accessSync(p, constants.X_OK); return statSync(p).isFile(); } catch { return false; }
  });
  return hasBin || ['../lib/node_modules/pdd/package.json', 'node_modules/pdd/package.json'].some(rel => existsSync(resolve(dir, rel)));
}

/** Build a smoke-test PATH exposing installBinDir + nodeBinDir while excluding host `pdd` copies. */
export function buildIsolatedPddPath(installBinDir, currentPath = process.env.PATH ?? '', nodeBinDir = dirname(process.execPath)) {
  const ordered = [];
  const seen = new Set();
  const push = dir => {
    if (!dir) return;
    const key = resolve(dir);
    if (!seen.has(key)) { seen.add(key); ordered.push(dir); }
  };
  push(installBinDir);
  push(nodeBinDir);
  for (const rawDir of String(currentPath).split(delimiter)) {
    const dir = rawDir.trim();
    if (dir && !hasHostPdd(dir)) push(dir);
  }
  return ordered.join(delimiter);
}

function createIsolatedNodeBinDir(smokeDir) {
  const realNodeDir = dirname(process.execPath);
  if (process.platform === 'win32' || !hasHostPdd(realNodeDir)) return realNodeDir;
  const nodeBinDir = join(smokeDir, 'node-bin');
  mkdirSync(nodeBinDir, { recursive: true });
  symlinkSync(process.execPath, join(nodeBinDir, 'node'));
  return nodeBinDir;
}

/** Verify that the repository has a clean git working tree. */
export function verifyCleanGitStatus({ root = DEFAULT_ROOT, env = process.env, runCommand = defaultRunCommand } = {}) {
  const cleanEnv = scrubEnv(env, PUBLISH_AUTH_ENV_KEYS);
  const secrets = collectSecrets(env);
  const inside = runCommand('git', ['rev-parse', '--is-inside-work-tree'], { cwd: root, env: cleanEnv });
  if (inside.status !== 0 || inside.stdout.trim() !== 'true') throw new Error(`Not a git working tree: ${root}`);
  const status = runOrThrow(runCommand, 'git status --porcelain', 'git', ['status', '--porcelain'], { cwd: root, env: cleanEnv }, secrets);
  const dirtyLines = status.stdout.split(/\r?\n/).filter(Boolean);
  if (dirtyLines.length > 0) {
    throw new Error(`Git working tree is not clean. Commit or stash changes before publishing:\n${dirtyLines.join('\n')}`);
  }
}

/** Resolve the target release tag (if omitted) and verify a published (`draft === false`) GitHub Release. */
export function resolveAndVerifyGitHubRelease({ repo, tag = null, env = process.env, runCommand = defaultRunCommand } = {}) {
  const endpoint = tag ? `repos/${repo}/releases/tags/${encodeURIComponent(tag)}` : `repos/${repo}/releases`;
  const res = runCommand('gh', ['api', endpoint], { env: scrubEnv(env, PUBLISH_AUTH_ENV_KEYS) });
  if (res.status !== 0) {
    const hint = res.error?.code === 'ENOENT'
      ? 'GitHub CLI (`gh`) was not found on PATH. Install `gh` and run `gh auth login`.'
      : `Could not verify published GitHub Release via \`gh api ${endpoint}\`. Ensure the release is published and \`gh auth status\` is valid.`;
    throw new Error(`${hint}\n${formatCommandFailure(`gh api ${endpoint}`, res, collectSecrets(env))}`);
  }

  const parsed = parseJsonOrThrow(res.stdout, `GitHub Release response from \`gh api ${endpoint}\``);
  const release = tag ? parsed : (Array.isArray(parsed) ? parsed.find(item => item && item.draft === false) : null);
  if (!release || typeof release.tag_name !== 'string' || !release.tag_name.trim()) {
    throw new Error(tag ? `GitHub Release for tag "${tag}" was not found in ${repo}.` : `No published GitHub Release found in ${repo}. Publish a release or pass --tag <tag>.`);
  }
  if (release.draft !== false) {
    throw new Error(`GitHub Release "${release.tag_name}" is not published (draft=${String(release.draft)}). Publish it on GitHub first.`);
  }
  const resolvedTag = release.tag_name.trim().replace(/^refs\/tags\//, '');
  if (!TAG_RE.test(resolvedTag)) throw new Error(`Invalid GitHub Release tag "${resolvedTag}".`);
  return { tag: resolvedTag, url: release.html_url || `https://github.com/${repo}/releases/tag/${resolvedTag}`, prerelease: Boolean(release.prerelease) };
}

function resolveRemoteTagCommit({ repo, tag, env, runCommand, secrets }) {
  const refEndpoint = `repos/${repo}/git/ref/tags/${encodeURIComponent(tag)}`;
  const refRes = runOrThrow(runCommand, `gh api ${refEndpoint}`, 'gh', ['api', refEndpoint], { env }, secrets);
  let obj = parseJsonOrThrow(refRes.stdout, `GitHub tag ref for "${tag}"`)?.object;
  for (let hop = 0; hop < 5 && obj?.type === 'tag' && obj?.sha; hop++) {
    const tagEndpoint = `repos/${repo}/git/tags/${encodeURIComponent(obj.sha)}`;
    const tagRes = runOrThrow(runCommand, `gh api ${tagEndpoint}`, 'gh', ['api', tagEndpoint], { env }, secrets);
    obj = parseJsonOrThrow(tagRes.stdout, `annotated GitHub tag "${tag}"`)?.object;
  }
  if (obj?.type !== 'commit' || typeof obj.sha !== 'string' || !SHA_RE.test(obj.sha)) {
    throw new Error(`Remote GitHub tag "${tag}" did not resolve to a commit object.`);
  }
  return obj.sha.toLowerCase();
}

/** Verify HEAD matches local and dereferenced remote GitHub tag commits; fails closed in live mode. */
export function verifyReleaseCommitParity({ root = DEFAULT_ROOT, repo, tag, dryRun = false, env = process.env, runCommand = defaultRunCommand, log = console.log } = {}) {
  const cleanEnv = scrubEnv(env, PUBLISH_AUTH_ENV_KEYS);
  const secrets = collectSecrets(env);
  const headCommit = runOrThrow(runCommand, 'git rev-parse HEAD^{commit}', 'git', ['rev-parse', '--verify', 'HEAD^{commit}'], { cwd: root, env: cleanEnv }, secrets).stdout.trim().toLowerCase();
  const localRes = runCommand('git', ['rev-parse', '--verify', `refs/tags/${tag}^{commit}`], { cwd: root, env: cleanEnv });
  const localTagCommit = localRes.status === 0 ? localRes.stdout.trim().toLowerCase() : null;

  if (dryRun) {
    if (localTagCommit && headCommit !== localTagCommit) {
      log(`  Note: HEAD (${headCommit.slice(0, 8)}) differs from local tag ${tag} (${localTagCommit.slice(0, 8)}); live publish requires an exact match.`);
    }
    return { headCommit, localTagCommit, remoteTagCommit: null };
  }

  if (!localTagCommit) throw new Error(`Refusing live publish: local tag "${tag}" was not found. Fetch tags and check out "${tag}" first.`);
  if (headCommit !== localTagCommit) {
    throw new Error(`Refusing live publish: HEAD (${headCommit}) does not match local tag "${tag}" (${localTagCommit}). Check out "${tag}" first.`);
  }
  const remoteTagCommit = resolveRemoteTagCommit({ repo, tag, env: cleanEnv, runCommand, secrets });
  if (headCommit !== remoteTagCommit) {
    throw new Error(`Refusing live publish: HEAD (${headCommit}) does not match remote GitHub tag "${tag}" (${remoteTagCommit}).`);
  }
  return { headCommit, localTagCommit, remoteTagCommit };
}

function parseSemver(raw) {
  const match = /^v?(\d+)\.(\d+)\.(\d+)(?:-([0-9A-Za-z.-]+))?(?:\+[0-9A-Za-z.-]+)?$/.exec(String(raw ?? '').trim());
  if (!match) return null;
  return {
    major: Number(match[1]),
    minor: Number(match[2]),
    patch: Number(match[3]),
    prerelease: match[4] ? match[4].split('.') : [],
  };
}

function compareSemver(leftRaw, rightRaw) {
  const left = parseSemver(leftRaw);
  const right = parseSemver(rightRaw);
  if (!left || !right) return null;
  for (const field of ['major', 'minor', 'patch']) {
    if (left[field] !== right[field]) return left[field] < right[field] ? -1 : 1;
  }
  if (left.prerelease.length === 0 && right.prerelease.length === 0) return 0;
  if (left.prerelease.length === 0) return 1;
  if (right.prerelease.length === 0) return -1;
  const len = Math.max(left.prerelease.length, right.prerelease.length);
  for (let i = 0; i < len; i++) {
    const a = left.prerelease[i];
    const b = right.prerelease[i];
    if (a === undefined) return -1;
    if (b === undefined) return 1;
    if (a === b) continue;
    const aNum = /^\d+$/.test(a);
    const bNum = /^\d+$/.test(b);
    if (aNum && bNum) return Number(a) < Number(b) ? -1 : 1;
    if (aNum !== bNum) return aNum ? -1 : 1;
    return a < b ? -1 : 1;
  }
  return 0;
}

/** Verify pinned runtime-client dependency in package.json is not behind latest published npm version. */
export function checkRuntimeClientParity({
  root = DEFAULT_ROOT,
  packageName = RUNTIME_CLIENT_PACKAGE,
  npmRegistry = DEFAULT_NPM_REGISTRY,
  allowStale = false,
  dryRun = false,
  env = process.env,
  runCommand = defaultRunCommand,
  log = console.log,
} = {}) {
  const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  const pinnedRaw = pkg.dependencies?.[packageName];
  if (typeof pinnedRaw !== 'string' || !pinnedRaw.trim()) {
    return { ok: true, skipped: true, stale: false, packageName, pinned: null, latest: null };
  }
  const pinned = pinnedRaw.trim();
  const secrets = collectSecrets(env);
  const res = runCommand('npm', ['view', packageName, 'version', '--registry', npmRegistry], {
    cwd: root,
    env: scrubEnv(env, ISOLATED_HOME_ENV_KEYS, NPM_SCRUB_ENV_KEYS, PUBLISH_AUTH_ENV_KEYS),
  });
  const latest = res.status === 0 ? String(res.stdout ?? '').trim().split(/\r?\n/).at(-1)?.trim() ?? '' : '';
  if (res.status !== 0 || !parseSemver(latest)) {
    const detail = res.status !== 0 ? formatCommandFailure(`npm view ${packageName} version`, res, secrets) : `unexpected version output "${latest}"`;
    const warning = `Could not verify latest published ${packageName} version on ${npmRegistry} (pinned ${pinned}): ${detail}`;
    if (dryRun || allowStale) {
      log(`  Warning: ${warning}`);
      return { ok: true, skipped: false, stale: false, warning, packageName, pinned, latest: null };
    }
    throw new Error(`Refusing live publish: ${warning} Pass --allow-stale-runtime-client to override.`);
  }
  const cmp = compareSemver(pinned, latest);
  if (cmp === null) {
    const warning = `${packageName} in package.json uses non-exact version "${pinned}" (latest on ${npmRegistry}: ${latest}).`;
    if (dryRun || allowStale) {
      log(`  Warning: ${warning}`);
      return { ok: true, skipped: false, stale: true, warning, packageName, pinned, latest };
    }
    throw new Error(`Refusing live publish: ${warning} Pin an exact version or pass --allow-stale-runtime-client.`);
  }
  if (cmp < 0) {
    const message = `${packageName} in package.json is pinned to ${pinned}, behind latest published ${latest} on ${npmRegistry}. Update package.json and package-lock.json before releasing (or pass --allow-stale-runtime-client to override).`;
    if (dryRun || allowStale) {
      log(`  Warning: ${message}`);
      return { ok: true, skipped: false, stale: true, warning: message, packageName, pinned, latest };
    }
    throw new Error(`Refusing live publish: ${message}`);
  }
  log(`  Verified ${packageName} parity: pinned ${pinned} (latest on npm: ${latest}).`);
  return { ok: true, skipped: false, stale: false, packageName, pinned, latest };
}

function buildAndSmokeTestNpm({ root, scratchDir, version, packageName, npmRegistry, env, runCommand, log }) {
  const secrets = collectSecrets(env);
  const smoke = join(scratchDir, 'npm-smoke');
  const [dist, packCache, installHome, home, state, install, installCache] = [
    join(scratchDir, 'npm-dist'), join(scratchDir, 'npm-pack-cache'), join(smoke, 'install-home'),
    join(smoke, 'home'), join(smoke, 'state'), join(smoke, 'install'), join(smoke, 'install-cache'),
  ];
  for (const dir of [dist, packCache, installHome, home, state, install, installCache]) mkdirSync(dir, { recursive: true });

  const baseEnv = scrubEnv(env, ISOLATED_HOME_ENV_KEYS, NPM_SCRUB_ENV_KEYS, PUBLISH_AUTH_ENV_KEYS);
  const packRes = runOrThrow(runCommand, 'npm pack', 'npm', ['pack', '--ignore-scripts', '--json', '--pack-destination', dist], {
    cwd: root, env: { ...baseEnv, COPYFILE_DISABLE: '1', npm_config_cache: packCache },
  }, secrets);
  const packed = parseJsonOrThrow(packRes.stdout, '`npm pack --json` output')?.[0];
  if (!packed?.filename) throw new Error('`npm pack --json` did not report a tarball filename.');
  const tarballPath = join(dist, packed.filename);
  if (!existsSync(tarballPath)) throw new Error(`Packed npm tarball was not created at ${tarballPath}.`);

  runOrThrow(runCommand, 'npm smoke-test install', 'npm',
    ['install', '--prefix', install, '--ignore-scripts', '--no-audit', '--no-fund', '--registry', npmRegistry, tarballPath],
    { cwd: smoke, env: { ...baseEnv, HOME: installHome, USERPROFILE: installHome, npm_config_cache: installCache } }, secrets);

  const installBinDir = join(install, 'node_modules', '.bin');
  const pddBin = join(installBinDir, process.platform === 'win32' ? 'pdd.cmd' : 'pdd');
  if (!existsSync(pddBin)) throw new Error(`Smoke-tested npm install did not expose pdd binary at ${pddBin}.`);

  const cliEnv = {
    ...baseEnv, HOME: home, USERPROFILE: home, PDD_STATE_DIR: state, PDD_NO_UPDATE_CHECK: '1',
    PATH: buildIsolatedPddPath(installBinDir, baseEnv.PATH, createIsolatedNodeBinDir(smoke)),
  };
  const versionRes = runOrThrow(runCommand, 'npm smoke-test `pdd --version`', pddBin, ['--version'], { cwd: home, env: cliEnv }, secrets);
  if (versionRes.stdout.trim() !== version) throw new Error(`npm smoke-test \`pdd --version\` printed "${versionRes.stdout.trim()}", expected "${version}".`);
  if (versionRes.stderr.trim() !== '') throw new Error(`npm smoke-test \`pdd --version\` wrote unexpected stderr:\n${redactSecrets(versionRes.stderr, secrets)}`);

  const helpRes = runOrThrow(runCommand, 'npm smoke-test `pdd --help`', pddBin, ['--help'], { cwd: home, env: cliEnv }, secrets);
  if (!/usage:\s*pdd|\bpdd\b/i.test(helpRes.stdout)) throw new Error('npm smoke-test `pdd --help` did not print expected PDD help output.');

  const distTag = npmDistTagForVersion(version);
  log(`  npm tarball verified: ${packed.filename} (${packageName}@${version}, dist-tag: ${distTag})`);
  return { packageName, version, filename: packed.filename, tarballPath, distTag };
}

/** Probe available Python 3 interpreters and `build` / `twine` tooling. */
export function resolvePythonTools({ pythonBin = null, env = process.env, runCommand = defaultRunCommand } = {}) {
  const probeScript = 'import importlib.util, json, sys; print(json.dumps({"executable": sys.executable, "major": sys.version_info[0], "minor": sys.version_info[1], "hasBuild": importlib.util.find_spec("build") is not None, "hasTwine": importlib.util.find_spec("twine") is not None}))';
  const explicit = pythonBin || String(env.PDD_RELEASE_PYTHON || '').trim() || null;
  const probeEnv = { ...scrubEnv(env, PUBLISH_AUTH_ENV_KEYS), PYTHONDONTWRITEBYTECODE: '1' };
  const found = [];

  for (const cmd of (explicit ? [explicit] : ['python3', 'python'])) {
    const res = runCommand(cmd, ['-B', '-c', probeScript], { env: probeEnv });
    if (res.status !== 0) continue;
    try {
      const info = JSON.parse(res.stdout.trim());
      if (info && Number(info.major) >= 3) {
        const entry = { cmd, executable: info.executable || cmd, major: Number(info.major), minor: Number(info.minor ?? 0), hasBuild: Boolean(info.hasBuild), hasTwine: Boolean(info.hasTwine) };
        found.push(entry);
        if (entry.hasBuild && entry.hasTwine) break;
      }
    } catch { /* Ignore non-JSON probe output. */ }
  }

  const selected = found.find(i => i.hasBuild && i.hasTwine) ?? found.find(i => i.hasBuild) ?? found[0] ?? null;
  let twineCmd = null;
  if (selected?.hasTwine) twineCmd = { cmd: selected.cmd, argsPrefix: ['-B', '-m', 'twine'] };
  else if (runCommand('twine', ['--version'], { env: probeEnv }).status === 0) twineCmd = { cmd: 'twine', argsPrefix: [] };
  return { python: selected, twineCmd };
}

function buildAndVerifyPypi({ root, scratchDir, version, pypiName, dryRun, pythonBin, env, stageBundle, runCommand, log }) {
  const secrets = collectSecrets(env);
  const { python, twineCmd } = resolvePythonTools({ pythonBin, env, runCommand });
  if (!python) throw new Error('Python 3 was not found on PATH. Install Python 3 and run: python3 -m pip install --upgrade build twine');
  if (!python.hasBuild) throw new Error(`Python "build" module is missing for ${python.cmd} (${python.executable}). Install with: ${python.cmd} -m pip install --upgrade build twine`);
  if (!dryRun && !twineCmd) throw new Error(`Python "twine" is required for live PyPI upload. Install with: ${python.cmd} -m pip install --upgrade twine`);

  const pySrcDir = join(scratchDir, 'python-src');
  const pypiDistDir = join(scratchDir, 'pypi-dist');
  mkdirSync(pypiDistDir, { recursive: true });
  const srcDir = join(root, 'python');
  cpSync(srcDir, pySrcDir, {
    recursive: true,
    filter: srcPath => {
      const rel = srcPath.slice(srcDir.length).replace(/^[/\\]+/, '');
      return !rel || !rel.split(/[/\\]/).some(seg => PYTHON_COPY_SKIP.has(seg) || seg.endsWith('.egg-info'));
    },
  });

  const cleanEnv = scrubEnv(env, NPM_SCRUB_ENV_KEYS, PUBLISH_AUTH_ENV_KEYS);
  stageBundle({ root, bundleDir: join(pySrcDir, 'pdd_cli', '_bundled'), env: cleanEnv });

  const pyEnv = { ...cleanEnv, PYTHONDONTWRITEBYTECODE: '1' };
  runOrThrow(runCommand, `${python.cmd} -m build`, python.cmd, ['-B', '-m', 'build', '--outdir', pypiDistDir, pySrcDir], { cwd: scratchDir, env: pyEnv }, secrets);

  const pep440Version = toPep440Version(version);
  const builtFiles = readdirSync(pypiDistDir).sort();
  const wheels = builtFiles.filter(name => name.endsWith('.whl') && name.includes(`-${pep440Version}-`));
  const sdists = builtFiles.filter(name => name.endsWith('.tar.gz') && name.includes(`-${pep440Version}.tar.gz`));
  if (wheels.length === 0 || sdists.length === 0) {
    throw new Error(`Expected both wheel (.whl) and sdist (.tar.gz) for version ${pep440Version} in ${pypiDistDir}; found: ${builtFiles.join(', ') || '(none)'}`);
  }
  const selectedFiles = [...sdists, ...wheels];
  const distFiles = selectedFiles.map(name => join(pypiDistDir, name));

  let twineChecked = false;
  if (twineCmd) {
    runOrThrow(runCommand, 'twine check', twineCmd.cmd, [...twineCmd.argsPrefix, 'check', ...distFiles], { cwd: scratchDir, env: pyEnv }, secrets);
    twineChecked = true;
    log(`  PyPI artifacts built and checked with twine: ${selectedFiles.join(', ')}`);
  } else {
    log(`  PyPI artifacts built: ${selectedFiles.join(', ')}\n  Warning: twine is not installed; skipped \`twine check\`. Install with: ${python.cmd} -m pip install --upgrade twine (required before live PyPI publish).`);
  }
  return { pypiName, version, pep440Version, python: python.cmd, twineCmd, twineChecked, distFiles, filenames: selectedFiles };
}

function queryNpmVersion({ packageName, version, npmRegistry, env, runCommand }) {
  const res = runCommand('npm', ['view', `${packageName}@${version}`, 'version', '--registry', npmRegistry], {
    env: scrubEnv(env, ISOLATED_HOME_ENV_KEYS, NPM_SCRUB_ENV_KEYS, PUBLISH_AUTH_ENV_KEYS),
  });
  if (res.status === 0) {
    const out = res.stdout.trim();
    return { published: out === version, notFound: out === '', detail: out || 'empty version', res };
  }
  const detail = [res.stderr, res.stdout].map(s => String(s || '').trim()).filter(Boolean).join(' ') || `exit ${res.status}`;
  return { published: false, notFound: NPM_NOT_FOUND_RE.test(detail), detail, res };
}

/** Publish the verified npm tarball with `--access public` (idempotent if already published). */
export function publishNpm({
  packageName, version, tarballPath, distTag = npmDistTagForVersion(version), npmRegistry = DEFAULT_NPM_REGISTRY,
  root = DEFAULT_ROOT, scratchDir, env = process.env, interactive = false, runCommand = defaultRunCommand, log = console.log,
} = {}) {
  const secrets = collectSecrets(env);
  const existing = queryNpmVersion({ packageName, version, npmRegistry, env, runCommand });
  if (existing.published) {
    log(`  ${packageName}@${version} is already published on npm; skipping npm publish.`);
    return { published: false, skipped: true, packageName, version, distTag };
  }
  if (!existing.notFound) throw new Error(formatCommandFailure(`npm view ${packageName}@${version}`, existing.res, secrets));

  for (const key of ['NPM_TOKEN', 'NODE_AUTH_TOKEN']) {
    if (typeof env[key] === 'string' && CONTROL_CHAR_RE.test(env[key])) {
      throw new Error(`Invalid ${key}: control or newline characters are not allowed.`);
    }
  }
  const npmToken = String(env.NPM_TOKEN || '').trim() || String(env.NODE_AUTH_TOKEN || '').trim();
  const args = ['publish', tarballPath, '--registry', npmRegistry, '--ignore-scripts', '--access', 'public', '--tag', distTag];

  let authDir = null;
  try {
    if (npmToken) {
      const registryUrl = new URL(npmRegistry);
      const authScope = `//${registryUrl.host}${registryUrl.pathname.replace(/\/+$/, '')}/`;
      authDir = mkdtempSync(join(scratchDir || tmpdir(), 'pdd-npm-auth-'));
      const userconfigPath = join(authDir, '.npmrc');
      writeFileSync(userconfigPath, `${authScope}:_authToken=${npmToken}\n`, { mode: 0o600, flag: 'wx' });
      args.push('--userconfig', userconfigPath);
    }

    const res = runCommand('npm', args, {
      cwd: root,
      env: scrubEnv(env, NPM_SCRUB_ENV_KEYS, PUBLISH_AUTH_ENV_KEYS),
      stdio: interactive ? 'inherit' : ['ignore', 'pipe', 'pipe'],
    });
    if (res.status !== 0) {
      throw new Error(`npm publish failed for ${packageName}@${version}. Run \`npm login\` or set NPM_TOKEN with publish access.\n${formatCommandFailure('npm publish', res, secrets)}`);
    }
    log(`  Published ${packageName}@${version} to ${npmRegistry} (tag: ${distTag}).`);
    return { published: true, skipped: false, packageName, version, distTag };
  } finally {
    if (authDir) rmSync(authDir, { recursive: true, force: true });
  }
}

/** Verify that `<packageName>@<version>` is visible on the live npm registry. */
export async function verifyNpmLiveVersion({
  packageName, version, npmRegistry = DEFAULT_NPM_REGISTRY, attempts = 5, delayMs = 2000,
  env = process.env, runCommand = defaultRunCommand, sleep = defaultSleep,
} = {}) {
  const secrets = collectSecrets(env);
  return pollUntil({
    attempts, delayMs, sleep,
    check: () => {
      const res = queryNpmVersion({ packageName, version, npmRegistry, env, runCommand });
      return res.published ? { ok: true, version } : { ok: false, detail: redactSecrets(res.detail, secrets) };
    },
    formatFailure: detail => `Live npm verification failed: ${packageName}@${version} was not returned by ${npmRegistry} after ${attempts} attempts (${detail}).`,
  });
}

function resolveCustomTwineUploadUrl(pypiBaseUrl) {
  const normalized = pypiBaseUrl.replace(/\/+$/, '');
  if (normalized === DEFAULT_PYPI_BASE_URL) return null;
  return normalized.endsWith('/legacy') ? `${normalized}/` : `${normalized}/legacy/`;
}

async function queryPypiRelease({ pypiName, version, expectedFilenames = [], pypiBaseUrl, fetchImpl }) {
  const pep440 = toPep440Version(version);
  const url = `${pypiBaseUrl.replace(/\/+$/, '')}/pypi/${encodeURIComponent(pypiName)}/${encodeURIComponent(pep440)}/json`;
  const res = await fetchImpl(url, { headers: { Accept: 'application/json' } });
  if (res.status === 404) return { allPresent: false, status: 404, version: pep440, filenames: [], fileCount: 0 };
  if (!res.ok) throw new Error(`PyPI lookup failed at ${url} (HTTP ${res.status}).`);

  const data = await res.json();
  const urls = Array.isArray(data?.urls) ? data.urls : [];
  const filenames = urls.map(u => u?.filename).filter(f => typeof f === 'string' && f.length > 0);
  const liveVersion = data?.info?.version ?? null;
  const liveSet = new Set(filenames);
  const allPresent = liveVersion === pep440 && (expectedFilenames.length > 0 ? expectedFilenames.every(n => liveSet.has(n)) : urls.length > 0);
  return { allPresent, status: res.status, version: liveVersion, filenames, fileCount: urls.length };
}

/** Upload verified sdist and wheel to PyPI via `twine upload` (skips only when ALL built files are live). */
export async function publishPypi({
  pypiName = 'pdd-cli', version, distFiles, twineCmd, pypiBaseUrl = DEFAULT_PYPI_BASE_URL,
  env = process.env, interactive = false, runCommand = defaultRunCommand, fetchImpl = globalThis.fetch, log = console.log,
} = {}) {
  if (!Array.isArray(distFiles) || distFiles.length === 0) {
    throw new Error('No PyPI distribution files provided for upload.');
  }
  const expectedFilenames = distFiles.map(file => basename(file));
  const existing = await queryPypiRelease({ pypiName, version, expectedFilenames, pypiBaseUrl, fetchImpl });
  if (existing.allPresent) {
    log(`  ${pypiName} ${existing.version} already has all artifacts on PyPI (${expectedFilenames.join(', ')}); skipping twine upload.`);
    return { published: false, skipped: true, pypiName, version: existing.version };
  }
  if (!twineCmd) throw new Error('twine is required to publish pdd-cli to PyPI. Install with: python3 -m pip install --upgrade twine');

  const secrets = collectSecrets(env);
  const uploadEnv = { ...scrubEnv(env, PUBLISH_AUTH_ENV_KEYS, TWINE_REPO_ENV_KEYS), PYTHONDONTWRITEBYTECODE: '1' };
  const twinePassword = String(env.TWINE_PASSWORD || '').trim();
  const apiToken = String(env.PYPI_API_TOKEN || '').trim();
  if (twinePassword) {
    uploadEnv.TWINE_PASSWORD = twinePassword;
    const twineUsername = String(env.TWINE_USERNAME || '').trim();
    if (twineUsername) uploadEnv.TWINE_USERNAME = twineUsername;
  } else if (apiToken) {
    uploadEnv.TWINE_USERNAME = '__token__';
    uploadEnv.TWINE_PASSWORD = apiToken;
  }

  const customUploadUrl = resolveCustomTwineUploadUrl(pypiBaseUrl);
  const uploadArgs = [...twineCmd.argsPrefix, 'upload', '--skip-existing'];
  if (customUploadUrl) uploadArgs.push('--repository-url', customUploadUrl);
  uploadArgs.push(...distFiles);

  const res = runCommand(twineCmd.cmd, uploadArgs, { env: uploadEnv, stdio: interactive ? 'inherit' : ['ignore', 'pipe', 'pipe'] });
  if (res.status !== 0) {
    throw new Error(`twine upload failed for ${pypiName} ${version}. Set PYPI_API_TOKEN or configure ~/.pypirc with a PyPI token.\n${formatCommandFailure('twine upload', res, secrets)}`);
  }
  log(`  Uploaded ${pypiName} ${toPep440Version(version)} to ${customUploadUrl ?? 'PyPI'}.`);
  return { published: true, skipped: false, pypiName, version: toPep440Version(version), repositoryUrl: customUploadUrl };
}

/** Verify that `<pypiName> <version>` (and all expected built artifacts) are live on PyPI. */
export async function verifyPypiLiveVersion({
  pypiName = 'pdd-cli', version, expectedFilenames = [], pypiBaseUrl = DEFAULT_PYPI_BASE_URL,
  attempts = 5, delayMs = 2000, fetchImpl = globalThis.fetch, sleep = defaultSleep,
} = {}) {
  const expected = toPep440Version(version);
  return pollUntil({
    attempts, delayMs, sleep,
    check: async () => {
      try {
        const res = await queryPypiRelease({ pypiName, version: expected, expectedFilenames, pypiBaseUrl, fetchImpl });
        return res.allPresent
          ? { ok: true, version: res.version, fileCount: res.fileCount, filenames: res.filenames }
          : { ok: false, detail: `HTTP ${res.status} (files: ${res.filenames.join(', ') || res.fileCount})` };
      } catch (err) {
        return { ok: false, detail: err?.message || String(err) };
      }
    },
    formatFailure: detail => `Live PyPI verification failed: ${pypiName} ${expected} did not have all artifacts on ${pypiBaseUrl} after ${attempts} attempts (${detail}).`,
  });
}

/** Execute maintainer release verification, build/smoke-test, and (when not `--dry-run`) live publish. */
export async function publishRelease(options = {}, deps = {}) {
  const {
    dryRun = false, dryRunFromNpmEnv = false, tag = null, npmOnly = false, pypiOnly = false,
    allowStaleRuntimeClient = false,
    repo: explicitRepo = null, root = DEFAULT_ROOT, pythonBin = null,
    npmRegistry = DEFAULT_NPM_REGISTRY, pypiBaseUrl = DEFAULT_PYPI_BASE_URL,
    verifyAttempts = 5, verifyDelayMs = 2000, interactive = false,
  } = options;
  if (npmOnly && pypiOnly) throw new Error('Cannot combine --npm-only and --pypi-only.');

  const { runCommand = defaultRunCommand, fetchImpl = globalThis.fetch, sleep = defaultSleep, stageBundle = stagePypiBundle, env = process.env, log = console.log } = deps;
  const [runNpm, runPypi] = [!pypiOnly, !npmOnly];

  const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  if (typeof pkg.name !== 'string' || !pkg.name.trim()) throw new Error('package.json is missing a valid package name.');
  if (pkg.private === true) throw new Error(`package.json marks ${pkg.name} as private; refusing to publish.`);

  const pyprojectPath = join(root, 'python', 'pyproject.toml');
  const pypiName = existsSync(pyprojectPath) ? (readPyprojectField(readFileSync(pyprojectPath, 'utf8'), 'name') ?? 'pdd-cli') : 'pdd-cli';
  const targets = [runNpm ? `npm (${pkg.name})` : null, runPypi ? `PyPI (${pypiName})` : null].filter(Boolean).join(' + ');
  log(`Mode: ${dryRun ? 'DRY RUN (no live publish)' : 'LIVE PUBLISH'} | Targets: ${targets}`);
  if (dryRunFromNpmEnv) log('Note: Detected npm_config_dry_run; running in --dry-run mode. Use `npm run release:publish -- --dry-run` to pass flags directly.');

  log('[1/4] Verifying clean git status, published GitHub Release, and version parity...');
  verifyCleanGitStatus({ root, env, runCommand });
  const repo = explicitRepo || deriveGitHubRepo(root, scrubEnv(env, PUBLISH_AUTH_ENV_KEYS), runCommand);
  const release = resolveAndVerifyGitHubRelease({ repo, tag, env, runCommand });
  const parity = checkVersionParity({ root, tag: release.tag });
  if (!parity.ok) throw new Error(`Release version parity check failed:\n${parity.problems.join('\n')}`);
  const version = parity.version;
  log(`  Verified clean git tree, GitHub Release ${release.tag} (${release.url}), and version parity (${version}).`);
  verifyReleaseCommitParity({ root, repo, tag: release.tag, dryRun, env, runCommand, log });
  const runtimeClientParity = checkRuntimeClientParity({ root, npmRegistry, allowStale: allowStaleRuntimeClient, dryRun, env, runCommand, log });

  const scratchDir = mkdtempSync(join(tmpdir(), 'pdd-release-publish-'));
  try {
    let npmArtifact = null;
    if (runNpm) {
      log(`[2/4] Packing and smoke-testing ${pkg.name}@${version}...`);
      npmArtifact = buildAndSmokeTestNpm({ root, scratchDir, version, packageName: pkg.name, npmRegistry, env, runCommand, log });
    } else log('[2/4] Skipping npm build and smoke test (--pypi-only).');

    let pypiArtifact = null;
    if (runPypi) {
      log(`[3/4] Staging, building, and verifying ${pypiName} ${version}...`);
      pypiArtifact = buildAndVerifyPypi({ root, scratchDir, version, pypiName, dryRun, pythonBin, env, stageBundle, runCommand, log });
    } else log('[3/4] Skipping PyPI build and verification (--npm-only).');

    if (dryRun) {
      log('[4/4] Dry run complete. No packages were published to live registries.');
      return { dryRun: true, repo, tag: release.tag, releaseUrl: release.url, version, runtimeClientParity, npm: npmArtifact, pypi: pypiArtifact, published: { npm: null, pypi: null }, verified: { npm: null, pypi: null } };
    }

    log('[4/4] Publishing artifacts and verifying live registries...');
    const published = { npm: null, pypi: null };
    const verified = { npm: null, pypi: null };
    if (runNpm) {
      published.npm = publishNpm({ packageName: npmArtifact.packageName, version, tarballPath: npmArtifact.tarballPath, distTag: npmArtifact.distTag, npmRegistry, root, scratchDir, env, interactive, runCommand, log });
      verified.npm = await verifyNpmLiveVersion({ packageName: npmArtifact.packageName, version, npmRegistry, attempts: verifyAttempts, delayMs: verifyDelayMs, env, runCommand, sleep });
      log(`  Live npm registry verified: ${npmArtifact.packageName}@${verified.npm.version}`);
    }
    if (runPypi) {
      published.pypi = await publishPypi({ pypiName: pypiArtifact.pypiName, version, distFiles: pypiArtifact.distFiles, twineCmd: pypiArtifact.twineCmd, pypiBaseUrl, env, interactive, runCommand, fetchImpl, log });
      verified.pypi = await verifyPypiLiveVersion({ pypiName: pypiArtifact.pypiName, version, expectedFilenames: pypiArtifact.filenames, pypiBaseUrl, attempts: verifyAttempts, delayMs: verifyDelayMs, fetchImpl, sleep });
      log(`  Live PyPI registry verified: ${pypiArtifact.pypiName} ${verified.pypi.version} (${verified.pypi.fileCount} files)`);
    }
    log(`Release publish complete for ${release.tag} (${version}).`);
    return { dryRun: false, repo, tag: release.tag, releaseUrl: release.url, version, runtimeClientParity, npm: npmArtifact, pypi: pypiArtifact, published, verified };
  } finally {
    rmSync(scratchDir, { recursive: true, force: true });
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const parsed = parsePublishArgs(process.argv.slice(2), process.env);
    if (parsed.help) { console.log(USAGE); process.exit(0); }
    await publishRelease({ ...parsed, interactive: Boolean(process.stdin.isTTY && process.stdout.isTTY) });
  } catch (err) {
    console.error(redactSecrets(err?.message || String(err), collectSecrets(process.env)));
    process.exit(1);
  }
}
