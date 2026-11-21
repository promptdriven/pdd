import './helpers/test-home.mjs';
import './helpers/test-net-guard.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import {
  chmodSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, statSync, writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { delimiter, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { readPyprojectField } from '../scripts/sync-pypi-version.mjs';
import { version as runtimeClientVersionInfo } from '../src/runtime-seam.mjs';
import {
  buildIsolatedPddPath,
  checkRuntimeClientParity,
  npmDistTagForVersion,
  parsePublishArgs,
  publishNpm,
  publishPypi,
  publishRelease,
  resolveAndVerifyGitHubRelease,
  resolvePythonTools,
  toPep440Version,
  verifyCleanGitStatus,
  verifyNpmLiveVersion,
  verifyPypiLiveVersion,
  verifyReleaseCommitParity,
} from '../scripts/publish-release.mjs';

const RUNTIME_CLIENT_PKG = runtimeClientVersionInfo().package;

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const publishScript = join(root, 'scripts', 'publish-release.mjs');
const PUBLISH_AUTH_KEYS = ['NPM_TOKEN', 'NODE_AUTH_TOKEN', 'PYPI_API_TOKEN', 'TWINE_PASSWORD', 'TWINE_USERNAME'];

function createFixtureRepo(t, { version = '0.1.37', tag = `alpha-v${version}` } = {}) {
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
      '  if (!process.env.HOME || !existsSync(process.env.HOME)) { process.stderr.write("missing HOME\\n"); process.exit(2); }',
      '  const entries = readdirSync(process.env.HOME);',
      '  if (process.env.PDD_PATH_PROBE !== "1" && entries.length > 0 && !entries.every(e => e.startsWith("."))) {',
      '    process.stderr.write(`non-empty HOME: ${entries.join(",")}\\n`); process.exit(3);',
      '  }',
      `  process.stdout.write(${JSON.stringify(`${version}\n`)}); process.exit(0);`,
      '}',
      'if (arg === "--help") { process.stdout.write("Usage: pdd <command> [options]\\n"); process.exit(0); }',
      'process.stderr.write(`unexpected arg: ${arg}\\n`); process.exit(1);',
    ].join('\n') + '\n',
  );
  chmodSync(binPath, 0o755);

  writeFileSync(
    join(dir, 'python', 'pyproject.toml'),
    `[build-system]\nrequires = ["setuptools>=77", "wheel"]\nbuild-backend = "setuptools.build_meta"\n\n[project]\nname = "pdd-cli"\nversion = "${version}"\ndependencies = []\n`,
  );
  writeFileSync(join(dir, 'python', 'pdd_cli', '__init__.py'), `"""Test wrapper."""\n\n__version__ = "${version}"\n`);

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
  if (tag) execFileSync('git', ['tag', tag], { cwd: dir, env: gitEnv });
  return dir;
}

function writeExecutable(path, content) {
  writeFileSync(path, content);
  chmodSync(path, 0o755);
}

test('#3533 package.json wires release:publish, parsePublishArgs uses parseArgs and traps swallowed npm flags', () => {
  const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  assert.equal(pkg.scripts?.['release:publish'], 'node scripts/publish-release.mjs');
  assert.equal(readPyprojectField('[project]\nname = "pdd-cli"\nversion = "0.1.37"\n', 'name'), 'pdd-cli');

  assert.deepEqual(
    parsePublishArgs(['--dry-run', '--tag', 'refs/tags/alpha-v0.1.37', '--npm-only', '--repo=promptdriven/pdd']),
    {
      dryRun: true, dryRunFromNpmEnv: false, tag: 'alpha-v0.1.37',
      npmOnly: true, pypiOnly: false, allowStaleRuntimeClient: false, repo: 'promptdriven/pdd', root, pythonBin: null, help: false,
    },
  );
  assert.equal(parsePublishArgs(['--allow-stale-runtime-client']).allowStaleRuntimeClient, true);

  // npm_config_dry_run treats any value other than false/0/undefined (including '' and '1') as dry-run (case-insensitively).
  for (const truthy of ['true', '1', '', 'yes']) {
    const parsed = parsePublishArgs([], { npm_config_dry_run: truthy });
    assert.equal(parsed.dryRun, true, `expected dryRun=true for npm_config_dry_run=${JSON.stringify(truthy)}`);
    assert.equal(parsed.dryRunFromNpmEnv, true);
    const upper = parsePublishArgs([], { NPM_CONFIG_DRY_RUN: truthy });
    assert.equal(upper.dryRun, true, `expected dryRun=true for NPM_CONFIG_DRY_RUN=${JSON.stringify(truthy)}`);
    assert.equal(upper.dryRunFromNpmEnv, true);
  }
  for (const falsy of ['false', 'FALSE', '0', undefined]) {
    const parsed = parsePublishArgs([], { npm_config_dry_run: falsy });
    assert.equal(parsed.dryRun, false, `expected dryRun=false for npm_config_dry_run=${JSON.stringify(falsy)}`);
    assert.equal(parsePublishArgs([], { NPM_CONFIG_DRY_RUN: falsy }).dryRun, false);
  }

  // Swallowed npm flags fail closed with explicit `use -- before flags` guidance (case-insensitively).
  assert.throws(() => parsePublishArgs([], { npm_config_npm_only: 'true' }), /Use `--` before flags[\s\S]*--npm-only/);
  assert.throws(() => parsePublishArgs([], { npm_config_npm_only: '' }), /Use `--` before flags[\s\S]*--npm-only/);
  assert.throws(() => parsePublishArgs([], { NPM_CONFIG_NPM_ONLY: 'true' }), /Use `--` before flags[\s\S]*--npm-only/);
  assert.throws(() => parsePublishArgs([], { npm_config_pypi_only: '1' }), /Use `--` before flags[\s\S]*--pypi-only/);
  assert.throws(() => parsePublishArgs([], { NPM_CONFIG_PYPI_ONLY: '1' }), /Use `--` before flags[\s\S]*--pypi-only/);
  assert.throws(() => parsePublishArgs([], { npm_config_tag: 'alpha-v0.1.37' }), /Use `--` before flags[\s\S]*--tag alpha-v0\.1\.37/);
  assert.throws(() => parsePublishArgs([], { NPM_CONFIG_TAG: 'alpha-v0.1.37' }), /Use `--` before flags[\s\S]*--tag alpha-v0\.1\.37/);
  assert.equal(parsePublishArgs([], { npm_config_tag: 'latest' }).tag, null, 'default npm_config_tag=latest is allowed');
  assert.equal(parsePublishArgs([], { NPM_CONFIG_TAG: 'latest' }).tag, null, 'default NPM_CONFIG_TAG=latest is allowed');
  assert.equal(parsePublishArgs(['--npm-only'], { npm_config_npm_only: 'true' }).npmOnly, true);

  assert.throws(() => parsePublishArgs(['--npm-only', '--pypi-only']), /Cannot combine --npm-only and --pypi-only/);
  assert.throws(() => parsePublishArgs(['--tag']), /argument missing|Missing value/i);
  assert.throws(() => parsePublishArgs(['--tag=']), /Missing value for --tag/);
  assert.throws(() => parsePublishArgs(['--tag', '--dry-run']), /argument is ambiguous|Missing value/i);
  assert.throws(() => parsePublishArgs(['--tag', 'bad tag!']), /Invalid GitHub Release tag/);
  assert.throws(() => parsePublishArgs(['--repo', 'not-a-repo']), /Invalid GitHub repository/);
  assert.throws(() => parsePublishArgs(['--unknown']), /Unknown option/i);

  assert.equal(npmDistTagForVersion('0.1.37'), 'latest');
  assert.equal(npmDistTagForVersion('0.1.38-alpha.1'), 'alpha');
  assert.equal(toPep440Version('0.1.37'), '0.1.37');
  assert.equal(toPep440Version('0.1.38-alpha.1'), '0.1.38a1');
  assert.equal(toPep440Version('0.1.38-rc.2'), '0.1.38rc2');
});

test('#3533 pre-flight checks fail closed on dirty tree, draft/unknown-draft release, and HEAD != local/remote tag in live mode', () => {
  assert.throws(
    () => verifyCleanGitStatus({
      root,
      runCommand: (_cmd, args) => (args[0] === 'rev-parse'
        ? { status: 0, stdout: 'true\n', stderr: '' }
        : { status: 0, stdout: ' M package.json\n?? scratch.txt\n', stderr: '' }),
    }),
    /Git working tree is not clean[\s\S]*package\.json/,
  );

  for (const draftVal of [true, undefined, null, 'false']) {
    assert.throws(
      () => resolveAndVerifyGitHubRelease({
        repo: 'promptdriven/pdd',
        tag: 'alpha-v0.1.37',
        runCommand: () => ({ status: 0, stdout: JSON.stringify({ tag_name: 'alpha-v0.1.37', draft: draftVal }), stderr: '' }),
      }),
      /is not published/,
    );
  }

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

  // Finding 1: Live mode refuses when HEAD != local tag, local tag missing, or HEAD != remote GitHub tag.
  const headSha = 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa';
  const tagSha = 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb';
  const annotObjSha = 'cccccccccccccccccccccccccccccccccccccccc';

  assert.throws(
    () => verifyReleaseCommitParity({
      root, repo: 'promptdriven/pdd', tag: 'alpha-v0.1.37', dryRun: false,
      runCommand: (_cmd, args) => ({
        status: 0,
        stdout: args[2] === 'HEAD^{commit}' ? `${headSha}\n` : `${tagSha}\n`,
        stderr: '',
      }),
    }),
    /Refusing live publish: HEAD .* does not match local tag/,
  );

  assert.throws(
    () => verifyReleaseCommitParity({
      root, repo: 'promptdriven/pdd', tag: 'alpha-v0.1.37', dryRun: false,
      runCommand: (_cmd, args) => (args[2] === 'HEAD^{commit}'
        ? { status: 0, stdout: `${headSha}\n`, stderr: '' }
        : { status: 128, stdout: '', stderr: 'fatal: Needed a single revision' }),
    }),
    /Refusing live publish: local tag "alpha-v0.1.37" was not found/,
  );

  assert.throws(
    () => verifyReleaseCommitParity({
      root, repo: 'promptdriven/pdd', tag: 'alpha-v0.1.37', dryRun: false,
      runCommand: (cmd, args) => {
        if (cmd === 'git') return { status: 0, stdout: `${headSha}\n`, stderr: '' };
        if (cmd === 'gh' && args[1].includes('/git/ref/tags/')) {
          return { status: 0, stdout: JSON.stringify({ object: { type: 'commit', sha: tagSha } }), stderr: '' };
        }
        throw new Error(`unexpected ${cmd} ${args.join(' ')}`);
      },
    }),
    /Refusing live publish: HEAD .* does not match remote GitHub tag/,
  );

  // Annotated remote tag dereferencing succeeds in live mode when commit SHA matches HEAD.
  const annotatedMatch = verifyReleaseCommitParity({
    root, repo: 'promptdriven/pdd', tag: 'alpha-v0.1.37', dryRun: false,
    runCommand: (cmd, args) => {
      if (cmd === 'git') return { status: 0, stdout: `${headSha}\n`, stderr: '' };
      if (cmd === 'gh' && args[1] === 'repos/promptdriven/pdd/git/ref/tags/alpha-v0.1.37') {
        return { status: 0, stdout: JSON.stringify({ object: { type: 'tag', sha: annotObjSha } }), stderr: '' };
      }
      if (cmd === 'gh' && args[1] === `repos/promptdriven/pdd/git/tags/${annotObjSha}`) {
        return { status: 0, stdout: JSON.stringify({ object: { type: 'commit', sha: headSha } }), stderr: '' };
      }
      throw new Error(`unexpected ${cmd} ${args.join(' ')}`);
    },
  });
  assert.equal(annotatedMatch.remoteTagCommit, headSha);
});

test('#3533 publishRelease refuses live mode when HEAD differs from tag before running build or publish', async t => {
  const fixtureDir = createFixtureRepo(t, { version: '0.1.37', tag: 'alpha-v0.1.37' });
  const invoked = [];
  await assert.rejects(
    () => publishRelease(
      { dryRun: false, tag: 'alpha-v0.1.37', root: fixtureDir },
      {
        runCommand: (cmd, args) => {
          invoked.push([cmd, ...args]);
          if (cmd === 'git' && args[0] === 'rev-parse' && args[1] === '--is-inside-work-tree') return { status: 0, stdout: 'true\n', stderr: '' };
          if (cmd === 'git' && args[0] === 'status') return { status: 0, stdout: '', stderr: '' };
          if (cmd === 'gh' && args[1].includes('/releases/tags/')) {
            return { status: 0, stdout: JSON.stringify({ tag_name: 'alpha-v0.1.37', draft: false }), stderr: '' };
          }
          if (cmd === 'git' && args[2] === 'HEAD^{commit}') return { status: 0, stdout: '1111111111111111111111111111111111111111\n', stderr: '' };
          if (cmd === 'git' && args[2] === 'refs/tags/alpha-v0.1.37^{commit}') return { status: 0, stdout: '2222222222222222222222222222222222222222\n', stderr: '' };
          throw new Error(`unexpected ${cmd} ${args.join(' ')}`);
        },
        log: () => {},
      },
    ),
    /Refusing live publish: HEAD .* does not match local tag/,
  );
  assert.equal(invoked.some(c => c[0] === 'npm' || c[0] === 'python3'), false, 'never builds or publishes on HEAD!=tag');
});

test('#3533 resolvePythonTools prefers Python with build + twine and falls back cleanly', () => {
  const preferred = resolvePythonTools({
    runCommand: cmd => {
      if (cmd === 'python3') return { status: 0, stdout: JSON.stringify({ executable: '/opt/homebrew/bin/python3', major: 3, minor: 14, hasBuild: false, hasTwine: false }), stderr: '' };
      if (cmd === 'python') return { status: 0, stdout: JSON.stringify({ executable: '/opt/anaconda3/bin/python', major: 3, minor: 12, hasBuild: true, hasTwine: true }), stderr: '' };
      return { status: 1, stdout: '', stderr: '' };
    },
  });
  assert.equal(preferred.python.cmd, 'python');
  assert.deepEqual(preferred.twineCmd, { cmd: 'python', argsPrefix: ['-B', '-m', 'twine'] });

  const standaloneTwine = resolvePythonTools({
    runCommand: cmd => {
      if (cmd === 'python3') return { status: 0, stdout: JSON.stringify({ executable: '/usr/bin/python3', major: 3, minor: 12, hasBuild: true, hasTwine: false }), stderr: '' };
      if (cmd === 'twine') return { status: 0, stdout: 'twine version 6.2.0\n', stderr: '' };
      return { status: 1, stdout: '', stderr: '' };
    },
  });
  assert.equal(standaloneTwine.python.cmd, 'python3');
  assert.deepEqual(standaloneTwine.twineCmd, { cmd: 'twine', argsPrefix: [] });
});

test('#3533 live publish enforces HEAD==tag, scrubs secrets across subprocesses, handles partial PyPI retry, and aligns custom twine URL', async t => {
  const fixtureDir = createFixtureRepo(t, { version: '0.1.37', tag: 'alpha-v0.1.37' });
  const headSha = '08eb96975656d2ced9f97b61dac2e07e66a20446';
  const commands = [];
  const logs = [];
  let npmPublishedLive = false;
  let pypiLiveFiles = [];
  let npmVerifyPolls = 0;
  let pypiVerifyPolls = 0;
  let capturedUserconfigPath = null;
  let capturedUserconfigMode = null;
  let capturedUserconfigContent = null;
  let capturedNpmPublishOpts = null;
  let capturedTwineOpts = null;

  const secretEnv = {
    ...process.env,
    NPM_TOKEN: 'secret-npm-tok-9999',
    NODE_AUTH_TOKEN: 'secret-node-auth-8888',
    PYPI_API_TOKEN: 'secret-pypi-tok-7777',
    TWINE_USERNAME: 'stray-twine-user',
    TWINE_REPOSITORY: 'wrong-repo',
    TWINE_REPOSITORY_URL: 'https://wrong.example/legacy/',
    NPM_CONFIG_CACHE: '/tmp/stray-npm-cache',
  };

  const assertNoSecrets = (label, envObj) => {
    for (const key of PUBLISH_AUTH_KEYS) {
      assert.equal(envObj?.[key], undefined, `${label} must not inherit ${key}`);
    }
  };

  const runCommand = (cmd, args, opts = {}) => {
    commands.push([cmd, ...args]);

    if (cmd === 'git') {
      assertNoSecrets(`git ${args[0]}`, opts.env);
      if (args[0] === 'rev-parse' && args[1] === '--is-inside-work-tree') return { status: 0, stdout: 'true\n', stderr: '' };
      if (args[0] === 'status') return { status: 0, stdout: '', stderr: '' };
      return { status: 0, stdout: `${headSha}\n`, stderr: '' };
    }
    if (cmd === 'gh') {
      assertNoSecrets(`gh ${args[1]}`, opts.env);
      if (args[1].includes('/git/ref/tags/')) {
        return { status: 0, stdout: JSON.stringify({ object: { type: 'commit', sha: headSha } }), stderr: '' };
      }
      return { status: 0, stdout: JSON.stringify({ tag_name: 'alpha-v0.1.37', draft: false, html_url: 'https://github.com/promptdriven/pdd/releases/tag/alpha-v0.1.37' }), stderr: '' };
    }
    if (cmd === 'npm' && args[0] === 'pack') {
      assertNoSecrets('npm pack', opts.env);
      const dest = args[args.indexOf('--pack-destination') + 1];
      const filename = 'promptdriven-pdd-0.1.37.tgz';
      writeFileSync(join(dest, filename), 'fake-tarball');
      return { status: 0, stdout: JSON.stringify([{ filename }]), stderr: '' };
    }
    if (cmd === 'npm' && args[0] === 'install') {
      assertNoSecrets('npm install', opts.env);
      const prefix = args[args.indexOf('--prefix') + 1];
      const binDir = join(prefix, 'node_modules', '.bin');
      mkdirSync(binDir, { recursive: true });
      writeExecutable(join(binDir, 'pdd'), '#!/bin/sh\necho 0.1.37\n');
      return { status: 0, stdout: '', stderr: '' };
    }
    if (cmd.endsWith('/pdd') || cmd.endsWith('\\pdd.cmd')) {
      assertNoSecrets('smoke pdd', opts.env);
      if (args[0] === '--version') return { status: 0, stdout: '0.1.37\n', stderr: '' };
      if (args[0] === '--help') return { status: 0, stdout: 'Usage: pdd <command>\n', stderr: '' };
    }
    if (cmd === 'python3' && args[1] === '-c') {
      assertNoSecrets('python probe', opts.env);
      return { status: 0, stdout: JSON.stringify({ executable: '/fake/python3', major: 3, minor: 12, hasBuild: true, hasTwine: true }), stderr: '' };
    }
    if (cmd === 'python3' && args[1] === '-m' && args[2] === 'build') {
      assertNoSecrets('python build', opts.env);
      const outdir = args[args.indexOf('--outdir') + 1];
      writeFileSync(join(outdir, 'pdd_cli-0.1.37.tar.gz'), 'fake-sdist');
      writeFileSync(join(outdir, 'pdd_cli-0.1.37-py3-none-any.whl'), 'fake-wheel');
      return { status: 0, stdout: 'Successfully built\n', stderr: '' };
    }
    if (cmd === 'python3' && args[1] === '-m' && args[2] === 'twine' && args[3] === 'check') {
      assertNoSecrets('twine check', opts.env);
      return { status: 0, stdout: 'PASSED\n', stderr: '' };
    }
    if (cmd === 'npm' && args[0] === 'view') {
      assertNoSecrets('npm view', opts.env);
      if (!npmPublishedLive) return { status: 1, stdout: '', stderr: 'npm error code E404' };
      npmVerifyPolls++;
      if (npmVerifyPolls === 1) return { status: 1, stdout: '', stderr: 'npm error code E404' };
      return { status: 0, stdout: '0.1.37\n', stderr: '' };
    }
    if (cmd === 'npm' && args[0] === 'publish') {
      assertNoSecrets('npm publish env', opts.env);
      capturedNpmPublishOpts = opts;
      const cfgIdx = args.indexOf('--userconfig');
      capturedUserconfigPath = args[cfgIdx + 1];
      capturedUserconfigMode = statSync(capturedUserconfigPath).mode & 0o777;
      capturedUserconfigContent = readFileSync(capturedUserconfigPath, 'utf8');
      npmPublishedLive = true;
      return { status: 0, stdout: '+ @promptdriven/pdd@0.1.37\n', stderr: '' };
    }
    if (cmd === 'python3' && args[1] === '-m' && args[2] === 'twine' && args[3] === 'upload') {
      capturedTwineOpts = opts;
      pypiLiveFiles = ['pdd_cli-0.1.37.tar.gz', 'pdd_cli-0.1.37-py3-none-any.whl'];
      return { status: 0, stdout: 'Uploading distributions\n', stderr: '' };
    }
    throw new Error(`Unexpected command: ${cmd} ${args.join(' ')}`);
  };

  const fetchImpl = async url => {
    assert.equal(url, 'https://pypi.org/pypi/pdd-cli/0.1.37/json');
    if (pypiLiveFiles.length === 0) return { status: 404, ok: false };
    pypiVerifyPolls++;
    if (pypiVerifyPolls === 1) {
      // Simulate partial propagation: only sdist visible on first poll.
      return { status: 200, ok: true, json: async () => ({ info: { version: '0.1.37' }, urls: [{ filename: 'pdd_cli-0.1.37.tar.gz' }] }) };
    }
    return { status: 200, ok: true, json: async () => ({ info: { version: '0.1.37' }, urls: pypiLiveFiles.map(filename => ({ filename })) }) };
  };

  const result = await publishRelease(
    { dryRun: false, tag: 'alpha-v0.1.37', root: fixtureDir, verifyAttempts: 3, verifyDelayMs: 0 },
    {
      runCommand, fetchImpl, sleep: async () => {},
      stageBundle: ({ bundleDir, env }) => {
        assertNoSecrets('stageBundle', env);
        mkdirSync(bundleDir, { recursive: true });
        return bundleDir;
      },
      env: secretEnv, log: msg => logs.push(msg),
    },
  );

  assert.equal(result.published.npm.published, true);
  assert.equal(result.verified.npm.attempts, 2);
  assert.equal(result.published.pypi.published, true);
  assert.equal(result.verified.pypi.attempts, 2);

  // npm publish checks: cwd, --access public, isolated mkdtemp .npmrc 0600, deleted afterward, uppercase NPM_CONFIG_* scrubbed.
  assert.equal(capturedNpmPublishOpts.cwd, fixtureDir);
  assert.equal(capturedNpmPublishOpts.env.NPM_CONFIG_CACHE, undefined);
  assert.match(capturedUserconfigPath, /pdd-npm-auth-[^/\\]+[/\\]\.npmrc$/);
  assert.equal(capturedUserconfigMode, 0o600);
  assert.equal(capturedUserconfigContent, '//registry.npmjs.org/:_authToken=secret-npm-tok-9999\n');
  assert.equal(existsSync(dirname(capturedUserconfigPath)), false, 'temp npm auth dir removed after publish');

  // twine upload checks: scrubbed NPM secrets + scrubbed TWINE_REPOSITORY*, no --repository-url on default pypi.org.
  const twineUploadCmd = commands.find(c => c[0] === 'python3' && c.includes('upload'));
  assert.ok(twineUploadCmd.includes('--skip-existing'));
  assert.equal(twineUploadCmd.includes('--repository-url'), false);
  assert.equal(capturedTwineOpts.env.NPM_TOKEN, undefined);
  assert.equal(capturedTwineOpts.env.NODE_AUTH_TOKEN, undefined);
  assert.equal(capturedTwineOpts.env.PYPI_API_TOKEN, undefined);
  assert.equal(capturedTwineOpts.env.TWINE_REPOSITORY, undefined);
  assert.equal(capturedTwineOpts.env.TWINE_REPOSITORY_URL, undefined);
  assert.equal(capturedTwineOpts.env.TWINE_USERNAME, '__token__');
  assert.equal(capturedTwineOpts.env.TWINE_PASSWORD, 'secret-pypi-tok-7777');
  assert.equal(logs.some(line => line.includes('secret-')), false);

  // Partial PyPI upload (only sdist live, wheel missing) must NOT skip twine upload, and custom pypiBaseUrl sets --repository-url.
  const customUploads = [];
  const partialRes = await publishPypi({
    pypiName: 'pdd-cli', version: '0.1.37',
    distFiles: ['/tmp/pdd_cli-0.1.37.tar.gz', '/tmp/pdd_cli-0.1.37-py3-none-any.whl'],
    twineCmd: { cmd: 'twine', argsPrefix: [] },
    pypiBaseUrl: 'https://test.pypi.org',
    env: secretEnv,
    fetchImpl: async url => {
      assert.equal(url, 'https://test.pypi.org/pypi/pdd-cli/0.1.37/json');
      return { status: 200, ok: true, json: async () => ({ info: { version: '0.1.37' }, urls: [{ filename: 'pdd_cli-0.1.37.tar.gz' }] }) };
    },
    runCommand: (cmd, args, opts) => {
      customUploads.push({ cmd, args, env: opts.env });
      return { status: 0, stdout: '', stderr: '' };
    },
    log: () => {},
  });
  assert.equal(partialRes.published, true);
  assert.equal(partialRes.skipped, false);
  assert.equal(customUploads.length, 1);
  assert.equal(customUploads[0].args[customUploads[0].args.indexOf('--repository-url') + 1], 'https://test.pypi.org/legacy/');
  assert.equal(customUploads[0].env.TWINE_REPOSITORY, undefined);
  assert.equal(customUploads[0].env.TWINE_REPOSITORY_URL, undefined);

  // TWINE_PASSWORD + TWINE_USERNAME restores both; ~/.pypirc fallback leaves both unset (even with stray TWINE_USERNAME).
  const notFoundFetch = async () => ({ status: 404, ok: false });
  let capturedExplicitTwineEnv = null;
  await publishPypi({
    pypiName: 'pdd-cli', version: '0.1.37',
    distFiles: ['/tmp/pdd_cli-0.1.37.tar.gz', '/tmp/pdd_cli-0.1.37-py3-none-any.whl'],
    twineCmd: { cmd: 'twine', argsPrefix: [] },
    env: { TWINE_USERNAME: '  custom-user  ', TWINE_PASSWORD: 'twine-pass-123', NPM_TOKEN: 'leaked-npm' },
    fetchImpl: notFoundFetch,
    runCommand: (_cmd, _args, opts) => { capturedExplicitTwineEnv = opts.env; return { status: 0, stdout: '', stderr: '' }; },
    log: () => {},
  });
  assert.equal(capturedExplicitTwineEnv.TWINE_USERNAME, 'custom-user');
  assert.equal(capturedExplicitTwineEnv.TWINE_PASSWORD, 'twine-pass-123');
  assert.equal(capturedExplicitTwineEnv.NPM_TOKEN, undefined);

  let capturedPypircEnv = null;
  await publishPypi({
    pypiName: 'pdd-cli', version: '0.1.37',
    distFiles: ['/tmp/pdd_cli-0.1.37.tar.gz', '/tmp/pdd_cli-0.1.37-py3-none-any.whl'],
    twineCmd: { cmd: 'twine', argsPrefix: [] },
    env: { TWINE_USERNAME: 'stray-user-without-password' },
    fetchImpl: notFoundFetch,
    runCommand: (_cmd, _args, opts) => { capturedPypircEnv = opts.env; return { status: 0, stdout: '', stderr: '' }; },
    log: () => {},
  });
  assert.equal(capturedPypircEnv.TWINE_USERNAME, undefined);
  assert.equal(capturedPypircEnv.TWINE_PASSWORD, undefined);

  // Empty distFiles fails closed.
  await assert.rejects(
    () => publishPypi({ pypiName: 'pdd-cli', version: '0.1.37', distFiles: [], twineCmd: { cmd: 'twine', argsPrefix: [] }, fetchImpl: notFoundFetch, log: () => {} }),
    /No PyPI distribution files provided/,
  );

  // Whitespace-only NPM_TOKEN falls back to NODE_AUTH_TOKEN.
  let fallbackAuthContent = null;
  publishNpm({
    packageName: '@promptdriven/pdd', version: '0.1.37', tarballPath: '/tmp/a.tgz', root: fixtureDir,
    env: { NPM_TOKEN: '   ', NODE_AUTH_TOKEN: 'node-auth-fallback-tok' },
    runCommand: (_cmd, args) => {
      if (args[0] === 'view') return { status: 1, stdout: '', stderr: 'npm error code E404' };
      fallbackAuthContent = readFileSync(args[args.indexOf('--userconfig') + 1], 'utf8');
      return { status: 0, stdout: '', stderr: '' };
    },
    log: () => {},
  });
  assert.equal(fallbackAuthContent, '//registry.npmjs.org/:_authToken=node-auth-fallback-tok\n');

  // Full idempotency: when BOTH sdist and wheel are already live on PyPI + version is live on npm, both skip.
  const commandsSecondRun = [];
  const secondResult = await publishRelease(
    { dryRun: false, tag: 'alpha-v0.1.37', root: fixtureDir, verifyAttempts: 2, verifyDelayMs: 0 },
    {
      runCommand: (cmd, args, opts) => { commandsSecondRun.push([cmd, ...args]); return runCommand(cmd, args, opts); },
      fetchImpl, sleep: async () => {},
      stageBundle: ({ bundleDir }) => { mkdirSync(bundleDir, { recursive: true }); return bundleDir; },
      log: () => {},
    },
  );
  assert.equal(secondResult.published.npm.skipped, true);
  assert.equal(secondResult.published.pypi.skipped, true);
  assert.equal(commandsSecondRun.some(c => c[0] === 'npm' && c[1] === 'publish'), false);
  assert.equal(commandsSecondRun.some(c => c.includes('upload')), false);
});

test('#3533 secret redaction, control-char token rejection, strict 404 matching, and missing-twine guards fail closed', async t => {
  const fixtureDir = createFixtureRepo(t, { version: '0.1.37', tag: 'alpha-v0.1.37' });

  // Control/newline chars in NPM_TOKEN or NODE_AUTH_TOKEN fail closed without echoing the token.
  for (const badToken of ['tok\n//evil/:_authToken=x', 'tok\r\nbar', 'tok\0null']) {
    assert.throws(
      () => publishNpm({
        packageName: '@promptdriven/pdd', version: '0.1.37', tarballPath: '/tmp/a.tgz',
        env: { NPM_TOKEN: badToken },
        runCommand: () => ({ status: 1, stdout: '', stderr: 'npm error code E404' }),
        log: () => {},
      }),
      err => /control or newline characters/.test(err.message) && !err.message.includes('evil'),
    );
  }

  // Known secrets echoed in failing command stderr are redacted to [REDACTED], while TWINE_USERNAME ('__token__') is not.
  assert.throws(
    () => publishNpm({
      packageName: '@promptdriven/pdd', version: '0.1.37', tarballPath: '/tmp/a.tgz',
      env: { NPM_TOKEN: 'npm_secret_value_12345', TWINE_USERNAME: '__token__' },
      runCommand: (_cmd, args) => (args[0] === 'view'
        ? { status: 1, stdout: '', stderr: 'npm error code E404' }
        : { status: 1, stdout: '', stderr: 'auth failed for __token__ and npm_secret_value_12345' }),
      log: () => {},
    }),
    err => err.message.includes('[REDACTED]') && err.message.includes('__token__') && !err.message.includes('npm_secret_value_12345'),
  );

  // Tightened isNpmNotFound regex must NOT swallow non-404 errors containing a stray "404".
  assert.throws(
    () => publishNpm({
      packageName: '@promptdriven/pdd', version: '0.1.37', tarballPath: '/tmp/a.tgz',
      runCommand: () => ({ status: 1, stdout: '', stderr: 'connect ECONNREFUSED 127.0.0.1:4040' }),
      log: () => {},
    }),
    /npm view @promptdriven\/pdd@0\.1\.37 failed/,
  );

  // Live mode without twine fails closed; dry-run without twine succeeds with install guidance.
  const logs = [];
  const headSha = 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa';
  const noTwineRunner = (cmd, args) => {
    if (cmd === 'git') return { status: 0, stdout: args[0] === 'rev-parse' ? (args[1] === '--is-inside-work-tree' ? 'true\n' : `${headSha}\n`) : '', stderr: '' };
    if (cmd === 'gh') {
      return args[1].includes('/git/ref/tags/')
        ? { status: 0, stdout: JSON.stringify({ object: { type: 'commit', sha: headSha } }), stderr: '' }
        : { status: 0, stdout: JSON.stringify({ tag_name: 'alpha-v0.1.37', draft: false }), stderr: '' };
    }
    if (cmd === 'python3' && args[1] === '-c') {
      return { status: 0, stdout: JSON.stringify({ executable: '/fake/python3', major: 3, minor: 12, hasBuild: true, hasTwine: false }), stderr: '' };
    }
    if (cmd === 'python3' && args[1] === '-m' && args[2] === 'build') {
      const outdir = args[args.indexOf('--outdir') + 1];
      writeFileSync(join(outdir, 'pdd_cli-0.1.37.tar.gz'), 'sdist');
      writeFileSync(join(outdir, 'pdd_cli-0.1.37-py3-none-any.whl'), 'wheel');
      return { status: 0, stdout: '', stderr: '' };
    }
    return { status: 1, stdout: '', stderr: 'not found' };
  };

  const dryRes = await publishRelease(
    { dryRun: true, pypiOnly: true, tag: 'alpha-v0.1.37', root: fixtureDir },
    { runCommand: noTwineRunner, stageBundle: ({ bundleDir }) => { mkdirSync(bundleDir, { recursive: true }); return bundleDir; }, log: m => logs.push(m) },
  );
  assert.equal(dryRes.pypi.twineChecked, false);
  assert.equal(logs.some(line => line.includes('pip install --upgrade twine')), true);

  await assert.rejects(
    () => publishRelease(
      { dryRun: false, pypiOnly: true, tag: 'alpha-v0.1.37', root: fixtureDir },
      { runCommand: noTwineRunner, stageBundle: ({ bundleDir }) => { mkdirSync(bundleDir, { recursive: true }); return bundleDir; }, log: () => {} },
    ),
    /twine.*required for live PyPI upload[\s\S]*pip install --upgrade twine/,
  );

  await assert.rejects(
    () => verifyNpmLiveVersion({ packageName: '@promptdriven/pdd', version: '0.1.37', attempts: 2, delayMs: 0, runCommand: () => ({ status: 1, stdout: '', stderr: 'E404' }), sleep: async () => {} }),
    /Live npm verification failed/,
  );

  // PyPI verification fails closed if only partial files exist.
  await assert.rejects(
    () => verifyPypiLiveVersion({
      pypiName: 'pdd-cli', version: '0.1.37',
      expectedFilenames: ['pdd_cli-0.1.37.tar.gz', 'pdd_cli-0.1.37-py3-none-any.whl'],
      attempts: 2, delayMs: 0,
      fetchImpl: async () => ({ status: 200, ok: true, json: async () => ({ info: { version: '0.1.37' }, urls: [{ filename: 'pdd_cli-0.1.37.tar.gz' }] }) }),
      sleep: async () => {},
    }),
    /Live PyPI verification failed/,
  );
});

test('#3533 subprocess --dry-run and npm_config_dry_run=true build & smoke-test npm + PyPI without mutating git tree', t => {
  const fixtureDir = createFixtureRepo(t, { version: '0.1.37', tag: 'alpha-v0.1.37' });
  const stubDir = mkdtempSync(join(tmpdir(), 'pdd-publish-stubs-'));
  const decoyPddDir = mkdtempSync(join(tmpdir(), 'pdd-decoy-bin-'));
  t.after(() => {
    rmSync(stubDir, { recursive: true, force: true });
    rmSync(decoyPddDir, { recursive: true, force: true });
  });

  const callLog = join(stubDir, 'calls.log');
  writeExecutable(join(decoyPddDir, 'pdd'), '#!/bin/sh\necho "DECOY 0.0.1" >&2\nexit 99\n');
  writeExecutable(
    join(stubDir, 'gh'),
    `#!/bin/sh\nprintf 'gh %s\\n' "$*" >> "${callLog}"\nprintf '{"tag_name":"alpha-v0.1.37","draft":false,"prerelease":false,"html_url":"https://github.com/promptdriven/pdd/releases/tag/alpha-v0.1.37"}\\n'\n`,
  );
  writeExecutable(
    join(stubDir, 'python3'),
    [
      `#!${process.execPath}`,
      'import { appendFileSync, existsSync, writeFileSync } from "node:fs";',
      'import { join } from "node:path";',
      'const args = process.argv.slice(2);',
      `appendFileSync(${JSON.stringify(callLog)}, "python3 " + args.join(" ") + "\\n");`,
      'if (args.includes("-c")) { console.log(JSON.stringify({ executable: process.argv[1], major: 3, minor: 12, hasBuild: true, hasTwine: true })); process.exit(0); }',
      'const mIdx = args.indexOf("-m");',
      'if (mIdx >= 0 && args[mIdx + 1] === "build") {',
      '  const outdir = args[args.indexOf("--outdir") + 1];',
      '  const srcDir = args[args.length - 1];',
      '  if (!existsSync(join(srcDir, "pdd_cli", "_bundled", "bin", "pdd.mjs"))) { console.error("missing staged _bundled CLI"); process.exit(1); }',
      '  writeFileSync(join(outdir, "pdd_cli-0.1.37.tar.gz"), "sdist");',
      '  writeFileSync(join(outdir, "pdd_cli-0.1.37-py3-none-any.whl"), "wheel");',
      '  process.exit(0);',
      '}',
      'if (mIdx >= 0 && args[mIdx + 1] === "twine" && args[mIdx + 2] === "check") { console.log("Checking distributions: PASSED"); process.exit(0); }',
      'console.error("unexpected python3 invocation:", args.join(" ")); process.exit(1);',
    ].join('\n') + '\n',
  );

  const subEnv = {
    ...process.env,
    PATH: [stubDir, decoyPddDir, dirname(process.execPath), process.env.PATH].filter(Boolean).join(delimiter),
  };

  assert.equal(buildIsolatedPddPath(join(stubDir, 'smoke-bin'), subEnv.PATH).split(delimiter).includes(decoyPddDir), false);

  // Full --dry-run (npm + PyPI)
  const fullDry = spawnSync(process.execPath, [publishScript, '--dry-run', '--root', fixtureDir, '--tag', 'alpha-v0.1.37'], { cwd: fixtureDir, env: subEnv, encoding: 'utf8' });
  assert.equal(fullDry.status, 0, `stdout:\n${fullDry.stdout}\nstderr:\n${fullDry.stderr}`);
  assert.match(fullDry.stdout, /Mode: DRY RUN/);
  assert.match(fullDry.stdout, /npm tarball verified:/);
  assert.match(fullDry.stdout, /PyPI artifacts built and checked with twine:/);
  assert.equal(existsSync(join(fixtureDir, 'python', 'pdd_cli', '_bundled')), false);
  assert.equal(execFileSync('git', ['status', '--porcelain'], { cwd: fixtureDir, encoding: 'utf8' }).trim(), '');

  // Finding 2: npm_config_dry_run=true and uppercase NPM_CONFIG_DRY_RUN=true run BOTH npm + PyPI dry-run cleanly.
  for (const dryEnv of [{ npm_config_dry_run: 'true' }, { NPM_CONFIG_DRY_RUN: 'true' }]) {
    const npmEnvDry = spawnSync(
      process.execPath,
      [publishScript, '--root', fixtureDir, '--tag', 'alpha-v0.1.37'],
      { cwd: fixtureDir, env: { ...subEnv, ...dryEnv }, encoding: 'utf8' },
    );
    assert.equal(npmEnvDry.status, 0, `stdout:\n${npmEnvDry.stdout}\nstderr:\n${npmEnvDry.stderr}`);
    assert.match(npmEnvDry.stdout, /Mode: DRY RUN/);
    assert.match(npmEnvDry.stdout, /Detected npm_config_dry_run/);
    assert.match(npmEnvDry.stdout, /PyPI artifacts built and checked with twine:/);
  }

  // Uppercase NPM_CONFIG_NPM_ONLY=true fails closed at the CLI boundary.
  const upperTrap = spawnSync(
    process.execPath,
    [publishScript, '--root', fixtureDir, '--tag', 'alpha-v0.1.37'],
    { cwd: fixtureDir, env: { ...subEnv, NPM_CONFIG_NPM_ONLY: 'true' }, encoding: 'utf8' },
  );
  assert.equal(upperTrap.status, 1);
  assert.match(upperTrap.stderr, /Use `--` before flags[\s\S]*--npm-only/);

  assert.doesNotMatch(readFileSync(callLog, 'utf8'), /\bupload\b/);

  // --npm-only, --pypi-only, and dirty-tree rejection
  const npmOnlyDry = spawnSync(process.execPath, [publishScript, '--dry-run', '--npm-only', '--root', fixtureDir, '--tag', 'alpha-v0.1.37'], { cwd: fixtureDir, env: subEnv, encoding: 'utf8' });
  assert.equal(npmOnlyDry.status, 0, npmOnlyDry.stderr);
  assert.match(npmOnlyDry.stdout, /Skipping PyPI build and verification \(--npm-only\)/);

  const pypiOnlyDry = spawnSync(process.execPath, [publishScript, '--dry-run', '--pypi-only', '--root', fixtureDir, '--tag', 'alpha-v0.1.37'], { cwd: fixtureDir, env: subEnv, encoding: 'utf8' });
  assert.equal(pypiOnlyDry.status, 0, pypiOnlyDry.stderr);
  assert.match(pypiOnlyDry.stdout, /Skipping npm build and smoke test \(--pypi-only\)/);

  writeFileSync(join(fixtureDir, 'dirty.tmp'), 'dirty\n');
  const dirtyRun = spawnSync(process.execPath, [publishScript, '--dry-run', '--root', fixtureDir, '--tag', 'alpha-v0.1.37'], { cwd: fixtureDir, env: subEnv, encoding: 'utf8' });
  assert.equal(dirtyRun.status, 1);
  assert.match(dirtyRun.stderr, /Git working tree is not clean/);
});

test('#3594 checkRuntimeClientParity fails closed in live mode when pinned runtime client lags latest npm release and warns in dry-run/override', async t => {
  const fixtureDir = createFixtureRepo(t, { version: '0.1.41', tag: 'alpha-v0.1.41' });
  const pkgPath = join(fixtureDir, 'package.json');
  const pkg = JSON.parse(readFileSync(pkgPath, 'utf8'));
  pkg.dependencies = { [RUNTIME_CLIENT_PKG]: '1.1.0' };
  writeFileSync(pkgPath, `${JSON.stringify(pkg, null, 2)}\n`);
  execFileSync('git', ['add', 'package.json'], { cwd: fixtureDir });
  execFileSync('git', ['-c', 'user.name=T', '-c', 'user.email=t@e.c', 'commit', '-q', '-m', 'Pin runtime client'], { cwd: fixtureDir });
  execFileSync('git', ['tag', '-f', 'alpha-v0.1.41'], { cwd: fixtureDir });

  const logs = [];
  const log = line => logs.push(line);

  // Matching version succeeds cleanly.
  const matched = checkRuntimeClientParity({
    root: fixtureDir,
    dryRun: false,
    runCommand: (cmd, args) => {
      assert.equal(cmd, 'npm');
      assert.equal(args[0], 'view');
      assert.equal(args[1], RUNTIME_CLIENT_PKG);
      assert.equal(args[2], 'version');
      return { status: 0, stdout: '1.1.0\n', stderr: '' };
    },
    log,
  });
  assert.equal(matched.ok, true);
  assert.equal(matched.stale, false);
  assert.equal(matched.pinned, '1.1.0');
  assert.equal(matched.latest, '1.1.0');

  // Lagging version fails closed in live mode.
  assert.throws(
    () => checkRuntimeClientParity({
      root: fixtureDir,
      dryRun: false,
      runCommand: () => ({ status: 0, stdout: '1.2.0\n', stderr: '' }),
      log,
    }),
    /Refusing live publish:.*pinned to 1\.1\.0, behind latest published 1\.2\.0/,
  );

  // Lagging version warns and continues in --dry-run.
  const dryLogs = [];
  const dryStale = checkRuntimeClientParity({
    root: fixtureDir,
    dryRun: true,
    runCommand: () => ({ status: 0, stdout: '1.2.0\n', stderr: '' }),
    log: line => dryLogs.push(line),
  });
  assert.equal(dryStale.ok, true);
  assert.equal(dryStale.stale, true);
  assert.match(dryLogs.join('\n'), /Warning:.*1\.1\.0.*1\.2\.0/);

  // Explicit --allow-stale-runtime-client override allows live publish with warning.
  const overrideLogs = [];
  const allowed = checkRuntimeClientParity({
    root: fixtureDir,
    dryRun: false,
    allowStale: true,
    runCommand: () => ({ status: 0, stdout: '1.2.0\n', stderr: '' }),
    log: line => overrideLogs.push(line),
  });
  assert.equal(allowed.ok, true);
  assert.equal(allowed.stale, true);
  assert.match(overrideLogs.join('\n'), /Warning:.*1\.1\.0.*1\.2\.0/);

  // Registry lookup failure fails closed in live mode and warns in --dry-run.
  assert.throws(
    () => checkRuntimeClientParity({
      root: fixtureDir,
      dryRun: false,
      runCommand: () => ({ status: 1, stdout: '', stderr: 'EAI_AGAIN' }),
      log,
    }),
    /Refusing live publish: Could not verify latest published/,
  );
  const dryUnreachable = checkRuntimeClientParity({
    root: fixtureDir,
    dryRun: true,
    runCommand: () => ({ status: 1, stdout: '', stderr: 'EAI_AGAIN' }),
    log: () => {},
  });
  assert.equal(dryUnreachable.ok, true);
  assert.equal(dryUnreachable.latest, null);

  // publishRelease enforces runtime-client parity in live mode BEFORE running pack/build/publish.
  const headSha = execFileSync('git', ['rev-parse', 'HEAD^{commit}'], { cwd: fixtureDir, encoding: 'utf8' }).trim();
  const invoked = [];
  await assert.rejects(
    () => publishRelease(
      { dryRun: false, tag: 'alpha-v0.1.41', root: fixtureDir },
      {
        runCommand: (cmd, args) => {
          invoked.push([cmd, ...args]);
          if (cmd === 'git' && args[0] === 'rev-parse' && args[1] === '--is-inside-work-tree') return { status: 0, stdout: 'true\n', stderr: '' };
          if (cmd === 'git' && args[0] === 'status') return { status: 0, stdout: '', stderr: '' };
          if (cmd === 'git' && args[0] === 'rev-parse') return { status: 0, stdout: `${headSha}\n`, stderr: '' };
          if (cmd === 'gh' && args[1].includes('/releases/tags/')) return { status: 0, stdout: JSON.stringify({ tag_name: 'alpha-v0.1.41', draft: false }), stderr: '' };
          if (cmd === 'gh' && args[1].includes('/git/ref/tags/')) return { status: 0, stdout: JSON.stringify({ object: { type: 'commit', sha: headSha } }), stderr: '' };
          if (cmd === 'npm' && args[0] === 'view') return { status: 0, stdout: '1.2.0\n', stderr: '' };
          throw new Error(`unexpected ${cmd} ${args.join(' ')}`);
        },
        log: () => {},
      },
    ),
    /Refusing live publish:.*1\.1\.0.*1\.2\.0/,
  );
  assert.equal(invoked.some(([cmd, arg]) => cmd === 'npm' && (arg === 'pack' || arg === 'publish')), false);
});
