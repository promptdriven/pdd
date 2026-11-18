import './helpers/test-home.mjs';
import './helpers/test-net-guard.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import {
  chmodSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { delimiter, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  buildIsolatedPddPath,
  normalizeGitHubRepo,
  npmDistTagForVersion,
  parsePublishArgs,
  publishNpm,
  publishPypi,
  publishRelease,
  readPyprojectName,
  resolveAndVerifyGitHubRelease,
  resolvePythonTools,
  toPep440Version,
  verifyCleanGitStatus,
  verifyNpmLiveVersion,
  verifyPypiLiveVersion,
} from '../scripts/publish-release.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const publishScript = join(root, 'scripts', 'publish-release.mjs');

function createFixtureRepo(t, { version = '0.1.37', tag = `alpha-v${version}`, dirty = false } = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-publish-fixture-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));

  mkdirSync(join(dir, 'bin'), { recursive: true });
  mkdirSync(join(dir, 'python', 'pdd_cli'), { recursive: true });

  writeFileSync(
    join(dir, 'package.json'),
    `${JSON.stringify({
      name: '@promptdriven/pdd',
      version,
      type: 'module',
      repository: { type: 'git', url: 'git+https://github.com/promptdriven/pdd.git' },
      bin: { pdd: 'bin/pdd.mjs' },
      files: ['bin/'],
      dependencies: {},
      publishConfig: { access: 'public' },
    }, null, 2)}\n`,
  );

  const binPath = join(dir, 'bin', 'pdd.mjs');
  writeFileSync(
    binPath,
    [
      '#!/usr/bin/env node',
      'import { existsSync, readdirSync } from "node:fs";',
      'const arg = process.argv[2];',
      'if (arg === "--version") {',
      '  if (!process.env.HOME || !existsSync(process.env.HOME)) {',
      '    process.stderr.write("missing HOME\\n");',
      '    process.exit(2);',
      '  }',
      '  const entries = readdirSync(process.env.HOME);',
      '  if (process.env.PDD_PATH_PROBE !== "1" && entries.length > 0 && !entries.every(e => e.startsWith("."))) {',
      '    process.stderr.write(`non-empty HOME: ${entries.join(",")}\\n`);',
      '    process.exit(3);',
      '  }',
      `  process.stdout.write(${JSON.stringify(`${version}\n`)});`,
      '  process.exit(0);',
      '}',
      'if (arg === "--help") {',
      '  process.stdout.write("Usage: pdd <command> [options]\\n");',
      '  process.exit(0);',
      '}',
      'process.stderr.write(`unexpected arg: ${arg}\\n`);',
      'process.exit(1);',
    ].join('\n') + '\n',
  );
  chmodSync(binPath, 0o755);

  writeFileSync(
    join(dir, 'python', 'pyproject.toml'),
    [
      '[build-system]',
      'requires = ["setuptools>=77", "wheel"]',
      'build-backend = "setuptools.build_meta"',
      '',
      '[project]',
      'name = "pdd-cli"',
      `version = "${version}"`,
      'dependencies = []',
      '',
    ].join('\n'),
  );
  writeFileSync(
    join(dir, 'python', 'pdd_cli', '__init__.py'),
    `"""Test wrapper."""\n\n__version__ = "${version}"\n`,
  );

  const gitEnv = {
    ...process.env,
    GIT_AUTHOR_NAME: 'Test Maintainer',
    GIT_AUTHOR_EMAIL: 'maintainer@example.test',
    GIT_COMMITTER_NAME: 'Test Maintainer',
    GIT_COMMITTER_EMAIL: 'maintainer@example.test',
  };
  execFileSync('git', ['init', '-q'], { cwd: dir, env: gitEnv });
  execFileSync('git', ['add', '.'], { cwd: dir, env: gitEnv });
  execFileSync('git', ['commit', '-q', '-m', `Release ${version}`], { cwd: dir, env: gitEnv });
  if (tag) {
    execFileSync('git', ['tag', tag], { cwd: dir, env: gitEnv });
  }
  if (dirty) {
    writeFileSync(join(dir, 'untracked.txt'), 'dirty\n');
  }

  return dir;
}

function writeExecutable(path, content) {
  writeFileSync(path, content);
  chmodSync(path, 0o755);
}

test('#3533 package.json wires release:publish and parsePublishArgs enforces flags cleanly', () => {
  const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  assert.equal(pkg.scripts?.['release:publish'], 'node scripts/publish-release.mjs');

  assert.deepEqual(
    parsePublishArgs(['--dry-run', '--tag', 'refs/tags/alpha-v0.1.37', '--npm-only', '--repo=promptdriven/pdd']),
    {
      dryRun: true,
      dryRunFromNpmEnv: false,
      tag: 'alpha-v0.1.37',
      npmOnly: true,
      pypiOnly: false,
      repo: 'promptdriven/pdd',
      root,
      pythonBin: null,
      help: false,
    },
  );

  const fromNpmEnv = parsePublishArgs([], { npm_config_dry_run: 'true' });
  assert.equal(fromNpmEnv.dryRun, true);
  assert.equal(fromNpmEnv.dryRunFromNpmEnv, true);

  assert.throws(() => parsePublishArgs(['--npm-only', '--pypi-only']), /Cannot combine --npm-only and --pypi-only/);
  assert.throws(() => parsePublishArgs(['--tag']), /Missing value for --tag/);
  assert.throws(() => parsePublishArgs(['--tag', 'bad tag!']), /Invalid GitHub Release tag/);
  assert.throws(() => parsePublishArgs(['--repo', 'not-a-repo']), /Invalid GitHub repository/);
  assert.throws(() => parsePublishArgs(['--unknown']), /Unknown argument/);

  assert.equal(npmDistTagForVersion('0.1.37'), 'latest');
  assert.equal(npmDistTagForVersion('0.1.38-alpha.1'), 'alpha');
  assert.equal(toPep440Version('0.1.37'), '0.1.37');
  assert.equal(toPep440Version('0.1.38-alpha.1'), '0.1.38a1');
  assert.equal(toPep440Version('0.1.38-rc.2'), '0.1.38rc2');
  assert.equal(normalizeGitHubRepo('git+https://github.com/promptdriven/pdd.git'), 'promptdriven/pdd');
  assert.equal(normalizeGitHubRepo('git@github.com:promptdriven/pdd.git'), 'promptdriven/pdd');
  assert.equal(readPyprojectName('[project]\nname = "pdd-cli"\nversion = "0.1.37"\n'), 'pdd-cli');
});

test('#3533 pre-flight checks fail closed on dirty tree, draft release, or missing gh release', () => {
  assert.throws(
    () =>
      verifyCleanGitStatus({
        root,
        runCommand: (_cmd, args) => {
          if (args[0] === 'rev-parse') return { status: 0, stdout: 'true\n', stderr: '' };
          return { status: 0, stdout: ' M package.json\n?? scratch.txt\n', stderr: '' };
        },
      }),
    /Git working tree is not clean[\s\S]*package\.json/,
  );

  assert.throws(
    () =>
      resolveAndVerifyGitHubRelease({
        repo: 'promptdriven/pdd',
        tag: 'alpha-v0.1.37',
        runCommand: () => ({
          status: 0,
          stdout: JSON.stringify({ tag_name: 'alpha-v0.1.37', draft: true }),
          stderr: '',
        }),
      }),
    /still a draft/,
  );

  assert.throws(
    () =>
      resolveAndVerifyGitHubRelease({
        repo: 'promptdriven/pdd',
        tag: 'alpha-v0.1.37',
        runCommand: () => ({ status: 1, stdout: '', stderr: 'HTTP 404: Not Found' }),
      }),
    /Could not verify published GitHub Release/,
  );

  const latest = resolveAndVerifyGitHubRelease({
    repo: 'promptdriven/pdd',
    runCommand: () => ({
      status: 0,
      stdout: JSON.stringify([
        { tag_name: 'alpha-v0.1.38', draft: true },
        { tag_name: 'alpha-v0.1.37', draft: false, html_url: 'https://github.com/promptdriven/pdd/releases/tag/alpha-v0.1.37' },
      ]),
      stderr: '',
    }),
  });
  assert.equal(latest.tag, 'alpha-v0.1.37');
});

test('#3533 resolvePythonTools prefers Python with build + twine and falls back cleanly', () => {
  const preferred = resolvePythonTools({
    runCommand: cmd => {
      if (cmd === 'python3') {
        return {
          status: 0,
          stdout: JSON.stringify({ executable: '/opt/homebrew/bin/python3', major: 3, minor: 14, hasBuild: false, hasTwine: false }),
          stderr: '',
        };
      }
      if (cmd === 'python') {
        return {
          status: 0,
          stdout: JSON.stringify({ executable: '/opt/anaconda3/bin/python', major: 3, minor: 12, hasBuild: true, hasTwine: true }),
          stderr: '',
        };
      }
      return { status: 1, stdout: '', stderr: '' };
    },
  });
  assert.equal(preferred.python.cmd, 'python');
  assert.deepEqual(preferred.twineCmd, { cmd: 'python', argsPrefix: ['-B', '-m', 'twine'] });

  const standaloneTwine = resolvePythonTools({
    runCommand: cmd => {
      if (cmd === 'python3') {
        return {
          status: 0,
          stdout: JSON.stringify({ executable: '/usr/bin/python3', major: 3, minor: 12, hasBuild: true, hasTwine: false }),
          stderr: '',
        };
      }
      if (cmd === 'twine') return { status: 0, stdout: 'twine version 6.2.0\n', stderr: '' };
      return { status: 1, stdout: '', stderr: '' };
    },
  });
  assert.equal(standaloneTwine.python.cmd, 'python3');
  assert.deepEqual(standaloneTwine.twineCmd, { cmd: 'twine', argsPrefix: [] });
});

test('#3533 live publish is idempotent, passes --access public and --skip-existing, and verifies live registries', async t => {
  const fixtureDir = createFixtureRepo(t, { version: '0.1.37', tag: 'alpha-v0.1.37' });
  const commands = [];
  const logs = [];
  let npmPublishedLive = false;
  let pypiUploadedLive = false;
  let npmVerifyPolls = 0;
  let pypiVerifyPolls = 0;
  let capturedUserconfigContent = null;
  let capturedUserconfigPath = null;
  let capturedTwineEnv = null;

  const runCommand = (cmd, args, opts = {}) => {
    commands.push([cmd, ...args]);

    if (cmd === 'git') {
      if (args[0] === 'rev-parse' && args[1] === '--is-inside-work-tree') return { status: 0, stdout: 'true\n', stderr: '' };
      if (args[0] === 'status') return { status: 0, stdout: '', stderr: '' };
      return { status: 0, stdout: 'deadbeef\n', stderr: '' };
    }
    if (cmd === 'gh') {
      return {
        status: 0,
        stdout: JSON.stringify({ tag_name: 'alpha-v0.1.37', draft: false, html_url: 'https://github.com/promptdriven/pdd/releases/tag/alpha-v0.1.37' }),
        stderr: '',
      };
    }
    if (cmd === 'npm' && args[0] === 'pack') {
      const dest = args[args.indexOf('--pack-destination') + 1];
      const filename = 'promptdriven-pdd-0.1.37.tgz';
      writeFileSync(join(dest, filename), 'fake-tarball');
      return { status: 0, stdout: JSON.stringify([{ filename }]), stderr: '' };
    }
    if (cmd === 'npm' && args[0] === 'install') {
      const prefix = args[args.indexOf('--prefix') + 1];
      const binDir = join(prefix, 'node_modules', '.bin');
      mkdirSync(binDir, { recursive: true });
      writeExecutable(join(binDir, 'pdd'), '#!/bin/sh\necho 0.1.37\n');
      return { status: 0, stdout: '', stderr: '' };
    }
    if (cmd.endsWith('/pdd') || cmd.endsWith('\\pdd.cmd')) {
      if (args[0] === '--version') return { status: 0, stdout: '0.1.37\n', stderr: '' };
      if (args[0] === '--help') return { status: 0, stdout: 'Usage: pdd <command>\n', stderr: '' };
    }
    if (cmd === 'python3' && args[1] === '-c') {
      return {
        status: 0,
        stdout: JSON.stringify({ executable: '/fake/python3', major: 3, minor: 12, hasBuild: true, hasTwine: true }),
        stderr: '',
      };
    }
    if (cmd === 'python3' && args[1] === '-m' && args[2] === 'build') {
      const outdir = args[args.indexOf('--outdir') + 1];
      writeFileSync(join(outdir, 'pdd_cli-0.1.37.tar.gz'), 'fake-sdist');
      writeFileSync(join(outdir, 'pdd_cli-0.1.37-py3-none-any.whl'), 'fake-wheel');
      return { status: 0, stdout: 'Successfully built\n', stderr: '' };
    }
    if (cmd === 'python3' && args[1] === '-m' && args[2] === 'twine' && args[3] === 'check') {
      return { status: 0, stdout: 'PASSED\n', stderr: '' };
    }
    if (cmd === 'npm' && args[0] === 'view') {
      if (!npmPublishedLive) return { status: 1, stdout: '', stderr: 'npm error code E404' };
      npmVerifyPolls++;
      if (npmVerifyPolls === 1) return { status: 1, stdout: '', stderr: 'npm error code E404' };
      return { status: 0, stdout: '0.1.37\n', stderr: '' };
    }
    if (cmd === 'npm' && args[0] === 'publish') {
      const cfgIdx = args.indexOf('--userconfig');
      if (cfgIdx >= 0) {
        capturedUserconfigPath = args[cfgIdx + 1];
        capturedUserconfigContent = readFileSync(capturedUserconfigPath, 'utf8');
      }
      npmPublishedLive = true;
      return { status: 0, stdout: '+ @promptdriven/pdd@0.1.37\n', stderr: '' };
    }
    if (cmd === 'python3' && args[1] === '-m' && args[2] === 'twine' && args[3] === 'upload') {
      capturedTwineEnv = opts.env;
      pypiUploadedLive = true;
      return { status: 0, stdout: 'Uploading distributions to https://upload.pypi.org/legacy/\n', stderr: '' };
    }
    throw new Error(`Unexpected command: ${cmd} ${args.join(' ')}`);
  };

  const fetchImpl = async url => {
    assert.equal(url, 'https://pypi.org/pypi/pdd-cli/0.1.37/json');
    if (!pypiUploadedLive) return { status: 404, ok: false };
    pypiVerifyPolls++;
    if (pypiVerifyPolls === 1) return { status: 404, ok: false };
    return {
      status: 200,
      ok: true,
      json: async () => ({ info: { version: '0.1.37' }, urls: [{ packagetype: 'sdist' }, { packagetype: 'bdist_wheel' }] }),
    };
  };

  const result = await publishRelease(
    {
      dryRun: false,
      tag: 'alpha-v0.1.37',
      root: fixtureDir,
      verifyAttempts: 3,
      verifyDelayMs: 0,
    },
    {
      runCommand,
      fetchImpl,
      sleep: async () => {},
      stageBundle: ({ bundleDir }) => {
        mkdirSync(bundleDir, { recursive: true });
        return bundleDir;
      },
      env: { ...process.env, NPM_TOKEN: 'fake-npm-token', PYPI_API_TOKEN: 'fake-pypi-token' },
      log: msg => logs.push(msg),
    },
  );

  assert.equal(result.dryRun, false);
  assert.equal(result.published.npm.published, true);
  assert.equal(result.published.npm.skipped, false);
  assert.equal(result.verified.npm.ok, true);
  assert.equal(result.verified.npm.attempts, 2);
  assert.equal(result.published.pypi.published, true);
  assert.equal(result.published.pypi.skipped, false);
  assert.equal(result.verified.pypi.ok, true);
  assert.equal(result.verified.pypi.attempts, 2);

  const npmPublishCmd = commands.find(c => c[0] === 'npm' && c[1] === 'publish');
  assert.ok(npmPublishCmd.includes('--access'));
  assert.equal(npmPublishCmd[npmPublishCmd.indexOf('--access') + 1], 'public');
  assert.ok(npmPublishCmd.includes('--tag'));
  assert.equal(npmPublishCmd[npmPublishCmd.indexOf('--tag') + 1], 'latest');
  assert.equal(capturedUserconfigContent, '//registry.npmjs.org/:_authToken=fake-npm-token\n');
  assert.equal(existsSync(capturedUserconfigPath), false, 'temporary npmrc userconfig is deleted after publish');

  const twineUploadCmd = commands.find(c => c[0] === 'python3' && c.includes('upload'));
  assert.ok(twineUploadCmd.includes('--skip-existing'));
  assert.equal(capturedTwineEnv.TWINE_USERNAME, '__token__');
  assert.equal(capturedTwineEnv.TWINE_PASSWORD, 'fake-pypi-token');
  assert.equal(logs.some(line => line.includes('fake-npm-token') || line.includes('fake-pypi-token')), false, 'tokens never logged');

  // Re-running live publish when both registries already have 0.1.37 skips both uploads idempotently.
  const commandsSecondRun = [];
  const secondResult = await publishRelease(
    {
      dryRun: false,
      tag: 'alpha-v0.1.37',
      root: fixtureDir,
      verifyAttempts: 2,
      verifyDelayMs: 0,
    },
    {
      runCommand: (cmd, args, opts) => {
        commandsSecondRun.push([cmd, ...args]);
        return runCommand(cmd, args, opts);
      },
      fetchImpl,
      sleep: async () => {},
      stageBundle: ({ bundleDir }) => {
        mkdirSync(bundleDir, { recursive: true });
        return bundleDir;
      },
      log: () => {},
    },
  );
  assert.equal(secondResult.published.npm.skipped, true);
  assert.equal(secondResult.published.pypi.skipped, true);
  assert.equal(commandsSecondRun.some(c => c[0] === 'npm' && c[1] === 'publish'), false);
  assert.equal(commandsSecondRun.some(c => c.includes('upload')), false);
});

test('#3533 live mode fails closed when twine is missing or post-publish registry verification fails', async t => {
  const fixtureDir = createFixtureRepo(t, { version: '0.1.37', tag: 'alpha-v0.1.37' });
  const logs = [];

  const noTwineRunner = (cmd, args) => {
    if (cmd === 'git') return { status: 0, stdout: args[0] === 'rev-parse' ? 'true\n' : '', stderr: '' };
    if (cmd === 'gh') return { status: 0, stdout: JSON.stringify({ tag_name: 'alpha-v0.1.37', draft: false }), stderr: '' };
    if (cmd === 'python3' && args[1] === '-c') {
      return {
        status: 0,
        stdout: JSON.stringify({ executable: '/fake/python3', major: 3, minor: 12, hasBuild: true, hasTwine: false }),
        stderr: '',
      };
    }
    if (cmd === 'python3' && args[1] === '-m' && args[2] === 'build') {
      const outdir = args[args.indexOf('--outdir') + 1];
      writeFileSync(join(outdir, 'pdd_cli-0.1.37.tar.gz'), 'sdist');
      writeFileSync(join(outdir, 'pdd_cli-0.1.37-py3-none-any.whl'), 'wheel');
      return { status: 0, stdout: '', stderr: '' };
    }
    return { status: 1, stdout: '', stderr: 'not found' };
  };

  // Dry-run without twine succeeds with clear guidance.
  const dryRes = await publishRelease(
    { dryRun: true, pypiOnly: true, tag: 'alpha-v0.1.37', root: fixtureDir },
    {
      runCommand: noTwineRunner,
      stageBundle: ({ bundleDir }) => {
        mkdirSync(bundleDir, { recursive: true });
        return bundleDir;
      },
      log: msg => logs.push(msg),
    },
  );
  assert.equal(dryRes.pypi.twineChecked, false);
  assert.equal(dryRes.npm, null);
  assert.equal(logs.some(line => line.includes('pip install --upgrade twine')), true);

  // Live mode without twine fails closed BEFORE uploading.
  await assert.rejects(
    () =>
      publishRelease(
        { dryRun: false, pypiOnly: true, tag: 'alpha-v0.1.37', root: fixtureDir },
        {
          runCommand: noTwineRunner,
          stageBundle: ({ bundleDir }) => {
            mkdirSync(bundleDir, { recursive: true });
            return bundleDir;
          },
          log: () => {},
        },
      ),
    /twine.*required for live PyPI upload[\s\S]*pip install --upgrade twine/,
  );

  // Live verification failures fail closed.
  await assert.rejects(
    () =>
      verifyNpmLiveVersion({
        packageName: '@promptdriven/pdd',
        version: '0.1.37',
        attempts: 2,
        delayMs: 0,
        runCommand: () => ({ status: 1, stdout: '', stderr: 'E404' }),
        sleep: async () => {},
      }),
    /Live npm verification failed/,
  );

  await assert.rejects(
    () =>
      verifyPypiLiveVersion({
        pypiName: 'pdd-cli',
        version: '0.1.37',
        attempts: 2,
        delayMs: 0,
        fetchImpl: async () => ({ status: 404, ok: false }),
        sleep: async () => {},
      }),
    /Live PyPI verification failed/,
  );

  // Direct publish helpers also guard against already-published/missing-twine.
  const skippedNpm = publishNpm({
    packageName: '@promptdriven/pdd',
    version: '0.1.37',
    tarballPath: '/unused.tgz',
    runCommand: () => ({ status: 0, stdout: '0.1.37\n', stderr: '' }),
    log: () => {},
  });
  assert.equal(skippedNpm.skipped, true);

  await assert.rejects(
    () =>
      publishPypi({
        pypiName: 'pdd-cli',
        version: '0.1.37',
        distFiles: ['/unused.whl'],
        twineCmd: null,
        fetchImpl: async () => ({ status: 404, ok: false }),
        log: () => {},
      }),
    /twine is required/,
  );
});

test('#3533 subprocess --dry-run builds and smoke-tests npm + PyPI in an isolated repo without mutating git tree or publishing', t => {
  const fixtureDir = createFixtureRepo(t, { version: '0.1.37', tag: 'alpha-v0.1.37' });
  const stubDir = mkdtempSync(join(tmpdir(), 'pdd-publish-stubs-'));
  const decoyPddDir = mkdtempSync(join(tmpdir(), 'pdd-decoy-bin-'));
  t.after(() => {
    rmSync(stubDir, { recursive: true, force: true });
    rmSync(decoyPddDir, { recursive: true, force: true });
  });

  const callLog = join(stubDir, 'calls.log');

  // Install a decoy `pdd` on PATH to prove isolated smoke PATH excludes host `pdd` copies.
  writeExecutable(join(decoyPddDir, 'pdd'), '#!/bin/sh\necho "DECOY 0.0.1" >&2\nexit 99\n');

  // Stub `gh` returning published release alpha-v0.1.37.
  writeExecutable(
    join(stubDir, 'gh'),
    [
      '#!/bin/sh',
      `printf 'gh %s\\n' "$*" >> "${callLog}"`,
      'printf \'{"tag_name":"alpha-v0.1.37","draft":false,"prerelease":false,"html_url":"https://github.com/promptdriven/pdd/releases/tag/alpha-v0.1.37"}\\n\'',
    ].join('\n') + '\n',
  );

  // Stub `python3` handling probe (-c), build (-m build), and twine (-m twine check).
  writeExecutable(
    join(stubDir, 'python3'),
    [
      `#!${process.execPath}`,
      'import { appendFileSync, existsSync, writeFileSync } from "node:fs";',
      'import { join } from "node:path";',
      'const args = process.argv.slice(2);',
      `appendFileSync(${JSON.stringify(callLog)}, "python3 " + args.join(" ") + "\\n");`,
      'if (args.includes("-c")) {',
      '  console.log(JSON.stringify({ executable: process.argv[1], major: 3, minor: 12, hasBuild: true, hasTwine: true }));',
      '  process.exit(0);',
      '}',
      'const mIdx = args.indexOf("-m");',
      'if (mIdx >= 0 && args[mIdx + 1] === "build") {',
      '  const outdir = args[args.indexOf("--outdir") + 1];',
      '  const srcDir = args[args.length - 1];',
      '  if (!existsSync(join(srcDir, "pdd_cli", "_bundled", "bin", "pdd.mjs"))) {',
      '    console.error("missing staged _bundled CLI");',
      '    process.exit(1);',
      '  }',
      '  writeFileSync(join(outdir, "pdd_cli-0.1.37.tar.gz"), "sdist");',
      '  writeFileSync(join(outdir, "pdd_cli-0.1.37-py3-none-any.whl"), "wheel");',
      '  process.exit(0);',
      '}',
      'if (mIdx >= 0 && args[mIdx + 1] === "twine" && args[mIdx + 2] === "check") {',
      '  console.log("Checking distributions: PASSED");',
      '  process.exit(0);',
      '}',
      'console.error("unexpected python3 invocation:", args.join(" "));',
      'process.exit(1);',
    ].join('\n') + '\n',
  );

  const subEnv = {
    ...process.env,
    PATH: [stubDir, decoyPddDir, dirname(process.execPath), process.env.PATH].filter(Boolean).join(delimiter),
  };

  // Verify buildIsolatedPddPath strips decoyPddDir.
  const isolatedPath = buildIsolatedPddPath(join(stubDir, 'smoke-bin'), subEnv.PATH);
  assert.equal(isolatedPath.split(delimiter).includes(decoyPddDir), false);

  // Full --dry-run (npm + PyPI)
  const fullDry = spawnSync(
    process.execPath,
    [publishScript, '--dry-run', '--root', fixtureDir, '--tag', 'alpha-v0.1.37'],
    { cwd: fixtureDir, env: subEnv, encoding: 'utf8' },
  );
  assert.equal(fullDry.status, 0, `stdout:\n${fullDry.stdout}\nstderr:\n${fullDry.stderr}`);
  assert.match(fullDry.stdout, /Mode: DRY RUN/);
  assert.match(fullDry.stdout, /npm tarball verified:/);
  assert.match(fullDry.stdout, /PyPI artifacts built and checked with twine:/);
  assert.match(fullDry.stdout, /Dry run complete\. No packages were published/);
  assert.equal(existsSync(join(fixtureDir, 'python', 'pdd_cli', '_bundled')), false, 'repo python/ stays untouched');

  const gitStatusAfter = execFileSync('git', ['status', '--porcelain'], { cwd: fixtureDir, encoding: 'utf8' }).trim();
  assert.equal(gitStatusAfter, '', 'git working tree remains completely clean after dry run');

  const loggedCalls = readFileSync(callLog, 'utf8');
  assert.doesNotMatch(loggedCalls, /\bupload\b/, 'dry run must never invoke twine upload');

  // --dry-run --npm-only skips PyPI completely
  const npmOnlyDry = spawnSync(
    process.execPath,
    [publishScript, '--dry-run', '--npm-only', '--root', fixtureDir, '--tag', 'alpha-v0.1.37'],
    { cwd: fixtureDir, env: subEnv, encoding: 'utf8' },
  );
  assert.equal(npmOnlyDry.status, 0, npmOnlyDry.stderr);
  assert.match(npmOnlyDry.stdout, /Skipping PyPI build and verification \(--npm-only\)/);

  // --dry-run --pypi-only skips npm completely
  const pypiOnlyDry = spawnSync(
    process.execPath,
    [publishScript, '--dry-run', '--pypi-only', '--root', fixtureDir, '--tag', 'alpha-v0.1.37'],
    { cwd: fixtureDir, env: subEnv, encoding: 'utf8' },
  );
  assert.equal(pypiOnlyDry.status, 0, pypiOnlyDry.stderr);
  assert.match(pypiOnlyDry.stdout, /Skipping npm build and smoke test \(--pypi-only\)/);

  // Dirty git tree fails closed in subprocess
  writeFileSync(join(fixtureDir, 'dirty.tmp'), 'dirty\n');
  const dirtyRun = spawnSync(
    process.execPath,
    [publishScript, '--dry-run', '--root', fixtureDir, '--tag', 'alpha-v0.1.37'],
    { cwd: fixtureDir, env: subEnv, encoding: 'utf8' },
  );
  assert.equal(dirtyRun.status, 1);
  assert.match(dirtyRun.stderr, /Git working tree is not clean/);
});
