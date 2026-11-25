// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Thin upstream-linter manifest detector & runner for lean `pdd lint`.
// Never auto-installs missing tools; never regex-parses upstream tool stdout.
import { spawnSync } from 'node:child_process';
import { accessSync, constants, existsSync, readFileSync } from 'node:fs';
import { delimiter, join } from 'node:path';
import { performance } from 'node:perf_hooks';
import { formatTeachingDetail, scrubChildEnv } from './diagnostics.mjs';

const ESLINT_CONFIG_FILES = [
  'eslint.config.js', 'eslint.config.mjs', 'eslint.config.cjs', 'eslint.config.ts',
  '.eslintrc', '.eslintrc.js', '.eslintrc.cjs', '.eslintrc.json', '.eslintrc.yml', '.eslintrc.yaml',
];
const GOLANGCI_CONFIG_FILES = ['.golangci.yml', '.golangci.yaml', '.golangci.toml', '.golangci.json'];
const PINNED_DESLOP_VERSION = '0.1.4';

function isExecutableFile(absPath) {
  try {
    accessSync(absPath, constants.X_OK);
    return true;
  } catch {
    return false;
  }
}

export function locateBinary(name, { root, env = process.env, localDirs = [] } = {}) {
  for (const relDir of localDirs) {
    const candidate = join(root, relDir, name);
    if (isExecutableFile(candidate)) return { found: true, bin: candidate, source: 'repo-local' };
  }
  const pathValue = env?.PATH ?? '';
  for (const dir of pathValue.split(delimiter).filter(Boolean)) {
    const candidate = join(dir, name);
    if (isExecutableFile(candidate)) return { found: true, bin: candidate, source: 'PATH' };
  }
  return { found: false, bin: null, source: null };
}

function readPackageJson(root) {
  const pkgPath = join(root, 'package.json');
  if (!existsSync(pkgPath)) return null;
  try {
    const parsed = JSON.parse(readFileSync(pkgPath, 'utf8'));
    return parsed && typeof parsed === 'object' && !Array.isArray(parsed) ? parsed : {};
  } catch {
    return {};
  }
}

function firstNonEmptyLine(text) {
  for (const line of String(text ?? '').split(/\r?\n/)) {
    const trimmed = line.trim();
    if (trimmed) return trimmed;
  }
  return null;
}

function scriptMentionsTool(scripts, toolName) {
  if (!scripts || typeof scripts !== 'object') return false;
  const re = new RegExp(`(?:^|[\\s;&|()])${toolName}(?:$|[\\s;&|()])`);
  return Object.values(scripts).some(v => typeof v === 'string' && re.test(v));
}

export function detectUpstreamLinters(root, { env = process.env } = {}) {
  const specs = [];

  if (existsSync(join(root, 'Cargo.toml'))) {
    specs.push({
      manifest: 'Cargo.toml',
      tool: 'cargo clippy',
      binName: 'cargo',
      localDirs: [],
      args: ['clippy', '--workspace', '--all-targets', '--', '-D', 'warnings'],
      versionArgs: ['clippy', '--version'],
      displayCommand: 'cargo clippy --workspace --all-targets -- -D warnings',
      pinned: null,
      configured: true,
      optional: false,
      installHint: 'rustup component add clippy',
    });
    const hasAllowFile = existsSync(join(root, '.deslop-please.allow'));
    specs.push({
      manifest: 'Cargo.toml',
      tool: 'deslop-please',
      binName: 'deslop-please',
      localDirs: [],
      args: hasAllowFile ? ['--allow', '.deslop-please.allow'] : [],
      versionArgs: ['--version'],
      displayCommand: hasAllowFile ? 'deslop-please --allow .deslop-please.allow' : 'deslop-please',
      pinned: PINNED_DESLOP_VERSION,
      configured: true,
      optional: true,
      installHint: `cargo install deslop-please --version ${PINNED_DESLOP_VERSION} --locked`,
    });
  }

  if (existsSync(join(root, 'pyproject.toml'))) {
    specs.push({
      manifest: 'pyproject.toml',
      tool: 'ruff',
      binName: 'ruff',
      localDirs: ['.venv/bin', 'venv/bin'],
      args: ['check', '.'],
      versionArgs: ['--version'],
      displayCommand: 'ruff check .',
      pinned: null,
      configured: true,
      optional: false,
      installHint: 'uv tool install ruff  # or: pip install ruff',
    });
  }

  if (existsSync(join(root, 'package.json'))) {
    const pkg = readPackageJson(root) ?? {};
    const allDeps = { ...pkg.dependencies, ...pkg.devDependencies };
    const scripts = pkg.scripts ?? {};
    const hasOxlintConfig = existsSync(join(root, '.oxlintrc.json')) || existsSync(join(root, 'oxlint.json'));
    const hasBiomeConfig = existsSync(join(root, 'biome.json')) || existsSync(join(root, 'biome.jsonc'));
    const hasEslintConfig = ESLINT_CONFIG_FILES.some(f => existsSync(join(root, f)));

    const configuredOxlint = Boolean(allDeps.oxlint || hasOxlintConfig || scriptMentionsTool(scripts, 'oxlint') || isExecutableFile(join(root, 'node_modules', '.bin', 'oxlint')));
    const configuredBiome = Boolean(allDeps['@biomejs/biome'] || hasBiomeConfig || scriptMentionsTool(scripts, 'biome') || isExecutableFile(join(root, 'node_modules', '.bin', 'biome')));
    const configuredEslint = Boolean(allDeps.eslint || hasEslintConfig || scriptMentionsTool(scripts, 'eslint') || isExecutableFile(join(root, 'node_modules', '.bin', 'eslint')));

    if (configuredOxlint) {
      const cfgFile = existsSync(join(root, '.oxlintrc.json')) ? '.oxlintrc.json' : (existsSync(join(root, 'oxlint.json')) ? 'oxlint.json' : null);
      const args = cfgFile ? ['-c', cfgFile] : [];
      specs.push({
        manifest: 'package.json',
        tool: 'oxlint',
        binName: 'oxlint',
        localDirs: ['node_modules/.bin'],
        args,
        versionArgs: ['--version'],
        displayCommand: cfgFile ? `oxlint -c ${cfgFile}` : 'oxlint',
        pinned: typeof allDeps.oxlint === 'string' ? allDeps.oxlint : null,
        configured: true,
        optional: false,
        installHint: 'npm install --save-dev --save-exact oxlint',
      });
    } else if (configuredBiome) {
      specs.push({
        manifest: 'package.json',
        tool: 'biome',
        binName: 'biome',
        localDirs: ['node_modules/.bin'],
        args: ['lint', '.'],
        versionArgs: ['--version'],
        displayCommand: 'biome lint .',
        pinned: typeof allDeps['@biomejs/biome'] === 'string' ? allDeps['@biomejs/biome'] : null,
        configured: true,
        optional: false,
        installHint: 'npm install --save-dev --save-exact @biomejs/biome',
      });
    } else if (configuredEslint) {
      specs.push({
        manifest: 'package.json',
        tool: 'eslint',
        binName: 'eslint',
        localDirs: ['node_modules/.bin'],
        args: ['.'],
        versionArgs: ['--version'],
        displayCommand: 'eslint .',
        pinned: typeof allDeps.eslint === 'string' ? allDeps.eslint : null,
        configured: true,
        optional: false,
        installHint: 'npm install --save-dev --save-exact eslint',
      });
    } else {
      specs.push({
        manifest: 'package.json',
        tool: 'oxlint',
        binName: 'oxlint',
        localDirs: ['node_modules/.bin'],
        args: [],
        versionArgs: ['--version'],
        displayCommand: 'oxlint',
        pinned: null,
        configured: false,
        optional: true,
        installHint: 'npm install --save-dev --save-exact oxlint',
      });
    }
  }

  if (existsSync(join(root, 'go.mod'))) {
    const hasGolangciConfig = GOLANGCI_CONFIG_FILES.some(f => existsSync(join(root, f)));
    const golangciBin = locateBinary('golangci-lint', { root, env });
    if (hasGolangciConfig || golangciBin.found) {
      specs.push({
        manifest: 'go.mod',
        tool: 'golangci-lint',
        binName: 'golangci-lint',
        localDirs: [],
        args: ['run'],
        versionArgs: ['--version'],
        displayCommand: 'golangci-lint run',
        pinned: null,
        configured: true,
        optional: false,
        installHint: 'go install github.com/golangci/golangci-lint/cmd/golangci-lint@latest',
      });
    } else {
      specs.push({
        manifest: 'go.mod',
        tool: 'go vet',
        binName: 'go',
        localDirs: [],
        args: ['vet', './...'],
        versionArgs: ['version'],
        displayCommand: 'go vet ./...',
        pinned: null,
        configured: true,
        optional: false,
        installHint: 'Install Go from https://go.dev/dl/',
      });
    }
  }

  return specs;
}

export function runUpstreamLinters(root, { env = process.env, timeoutMs = 120_000 } = {}, ports = {}) {
  const runner = ports.spawnSync ?? spawnSync;
  const locator = ports.locateBinary ?? locateBinary;
  const specs = ports.detectUpstreamLinters
    ? ports.detectUpstreamLinters(root, { env })
    : detectUpstreamLinters(root, { env });
  if (!specs.length) return { ok: true, results: [], errors: [] };

  const childEnv = scrubChildEnv(env);
  const results = [];
  const errors = [];

  for (const spec of specs) {
    if (spec.configured === false) {
      results.push({
        manifest: spec.manifest,
        tool: spec.tool,
        pinned: spec.pinned,
        version: null,
        command: spec.displayCommand,
        status: 'unconfigured',
        exit_code: null,
        duration_ms: 0,
        note: 'not run: no JS/TS linter configured in package.json (recommended: oxlint)',
        install_hint: spec.installHint,
        stdout: '',
        stderr: '',
      });
      continue;
    }

    const located = locator(spec.binName, { root, env, localDirs: spec.localDirs ?? [] });
    if (!located.found || !located.bin) {
      results.push({
        manifest: spec.manifest,
        tool: spec.tool,
        pinned: spec.pinned,
        version: null,
        command: spec.displayCommand,
        status: 'not_installed',
        exit_code: null,
        duration_ms: 0,
        note: 'not run: not installed',
        install_hint: spec.installHint,
        stdout: '',
        stderr: '',
      });
      continue;
    }

    const verProc = runner(located.bin, spec.versionArgs ?? ['--version'], {
      cwd: root,
      env: childEnv,
      encoding: 'utf8',
      timeout: 15_000,
      maxBuffer: 1024 * 1024,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    if (verProc.error || (spec.tool === 'cargo clippy' && verProc.status !== 0)) {
      results.push({
        manifest: spec.manifest,
        tool: spec.tool,
        pinned: spec.pinned,
        version: null,
        command: spec.displayCommand,
        status: 'not_installed',
        exit_code: null,
        duration_ms: 0,
        note: 'not run: not installed',
        install_hint: spec.installHint,
        stdout: '',
        stderr: '',
      });
      continue;
    }
    const version = firstNonEmptyLine(verProc.stdout || verProc.stderr) ?? 'unknown';

    const t0 = performance.now();
    const proc = runner(located.bin, spec.args ?? [], {
      cwd: root,
      env: childEnv,
      encoding: 'utf8',
      timeout: timeoutMs,
      maxBuffer: 16 * 1024 * 1024,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    const durationMs = Math.round(performance.now() - t0);
    const exitCode = typeof proc.status === 'number' ? proc.status : 1;
    const passed = exitCode === 0 && !proc.error && !proc.signal;
    const rawStdout = typeof proc.stdout === 'string' ? proc.stdout : '';
    const rawStderr = typeof proc.stderr === 'string' ? proc.stderr : (proc.error?.message ? `${proc.error.message}\n` : '');

    results.push({
      manifest: spec.manifest,
      tool: spec.tool,
      pinned: spec.pinned,
      version,
      command: spec.displayCommand,
      status: passed ? 'passed' : 'failed',
      exit_code: exitCode,
      duration_ms: durationMs,
      note: passed ? 'ok' : `exited with code ${exitCode}`,
      install_hint: null,
      stdout: rawStdout,
      stderr: rawStderr,
    });

    if (!passed) {
      const detail = formatTeachingDetail({
        invariant: `Upstream linter "${spec.tool}" (${version}) exited with ${proc.signal ? `signal ${proc.signal}` : `code ${exitCode}`}`,
        fix: `Fix the reported issues from \`${spec.displayCommand}\``,
        rerun: spec.displayCommand,
      });
      const slug = spec.tool.replace(/\s+/g, '-');
      errors.push(`Error: upstream linter: ${spec.manifest}:1 [upstream-linter-failed:${slug}] ${detail}`);
    }
  }

  return { ok: errors.length === 0, results, errors };
}

export function formatUpstreamLinterReport(results = []) {
  const chunks = [];
  for (const r of results) {
    if (r.status === 'not_installed') {
      chunks.push(`Upstream linter [${r.manifest}]: ${r.tool} — ${r.note} (install: ${r.install_hint})\n`);
      continue;
    }
    if (r.status === 'unconfigured') {
      chunks.push(`Upstream linter [${r.manifest}]: ${r.tool} — ${r.note} (recommend: ${r.install_hint})\n`);
      continue;
    }
    const pinSuffix = r.pinned ? `, pinned ${r.pinned}` : '';
    chunks.push(`Upstream linter [${r.manifest}]: ${r.tool} (${r.version}${pinSuffix}) — exit ${r.exit_code} (${r.duration_ms}ms)\n`);
    if (r.stdout) chunks.push(r.stdout.endsWith('\n') ? r.stdout : `${r.stdout}\n`);
    if (r.stderr) chunks.push(r.stderr.endsWith('\n') ? r.stderr : `${r.stderr}\n`);
  }
  return chunks.join('');
}
