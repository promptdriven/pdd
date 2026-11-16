import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { createServer } from 'node:http';
import { tmpdir } from 'node:os';
import { delimiter, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import { version as runtimeVersion } from '../src/runtime-seam.mjs';

const root = fileURLToPath(new URL('..', import.meta.url));
const installer = join(root, '.github/scripts/ci-install.mjs');
const credentialNames = [
  'RUNTIME_CLIENT_DEPLOY_KEY',
  'PRIVATE_REPO_TOKEN',
  'PDS_TOKEN',
  'PDD_CLOUD_APP_ID',
  'PDD_CLOUD_APP_PRIVATE_KEY',
  'GITHUB_TOKEN',
  'GH_TOKEN',
  'NPM_TOKEN',
  'NODE_AUTH_TOKEN',
];

function fixtureLock(resolved) {
  const lock = JSON.parse(readFileSync(join(root, 'package-lock.json'), 'utf8'));
  const runtimePackage = runtimeVersion().package;
  const runtimeSpec = lock.packages[''].dependencies[runtimePackage];
  const packageKey = `node_modules/${runtimePackage}`;
  return JSON.stringify({
    ...lock,
    packages: {
      '': { ...lock.packages[''], dependencies: { [runtimePackage]: runtimeSpec } },
      [packageKey]: { ...lock.packages[packageKey], version: runtimeSpec, resolved },
    },
  });
}

function run(command, args, options) {
  return new Promise((resolve, reject) => {
    const child = spawn(command, args, { ...options, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '';
    let stderr = '';
    child.stdout.on('data', chunk => { stdout += chunk; });
    child.stderr.on('data', chunk => { stderr += chunk; });
    child.on('error', reject);
    child.on('close', code => resolve({ code, stdout, stderr }));
  });
}

function testEnvironment(bin, npmLog, gitLog, extra = {}) {
  const env = {
    ...process.env,
    ...extra,
    PATH: `${bin}${delimiter}${process.env.PATH}`,
    CI_INSTALL_LOG: npmLog,
    CI_INSTALL_GIT_LOG: gitLog,
  };
  for (const name of credentialNames) {
    if (!(name in extra)) delete env[name];
  }
  return env;
}

function writeCommand(path, source) {
  writeFileSync(path, `#!/usr/bin/env node\n${source}`);
  chmodSync(path, 0o755);
}

function writeCommands(bin) {
  writeCommand(join(bin, 'npm'), `
    const { writeFileSync } = require('node:fs');
    writeFileSync(process.env.CI_INSTALL_LOG, JSON.stringify({
      command: 'npm', args: process.argv.slice(2),
      credentials: Object.fromEntries(${JSON.stringify(credentialNames)}.map(name => [name, process.env[name] || ''])),
      gitConfigCount: process.env.GIT_CONFIG_COUNT || '',
      gitConfigKey0: process.env.GIT_CONFIG_KEY_0 || '',
      gitConfigValue0: process.env.GIT_CONFIG_VALUE_0 || '',
    }));
  `);
  writeCommand(join(bin, 'git'), `
    const { appendFileSync } = require('node:fs');
    appendFileSync(process.env.CI_INSTALL_GIT_LOG, 'git ' + process.argv.slice(2).join(' ') + '\\n');
  `);
}

function readNpmLog(log) {
  assert.equal(existsSync(log), true, 'npm ci should run');
  return JSON.parse(readFileSync(log, 'utf8'));
}

async function startApi() {
  const requests = [];
  const server = createServer((request, response) => {
    requests.push({ url: request.url, authorization: request.headers.authorization || '' });
    response.writeHead(200, { 'Content-Type': 'application/json' });
    response.end('{}');
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const { port } = server.address();
  return { server, requests, base: `http://127.0.0.1:${port}` };
}

test('CI installer uses anonymous npm ci for a public registry runtime package', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-ci-public-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const bin = join(dir, 'bin');
  const log = join(dir, 'npm.json');
  const gitLog = join(dir, 'git.log');
  writeFileSync(join(dir, 'package-lock.json'), fixtureLock('https://registry.npmjs.org/@promptdriven/runtime-client/-/runtime-client-1.0.0.tgz'));
  mkdirSync(bin);
  writeCommands(bin);

  const result = await run(process.execPath, [installer], {
    cwd: dir,
    env: testEnvironment(bin, log, gitLog, {
      RUNTIME_CLIENT_DEPLOY_KEY: 'synthetic-public-deploy-key',
      PRIVATE_REPO_TOKEN: 'synthetic-public-token',
      PDS_TOKEN: 'synthetic-public-pds-token',
      PDD_CLOUD_APP_ID: 'synthetic-public-app-id',
      PDD_CLOUD_APP_PRIVATE_KEY: 'synthetic-public-app-key',
      GITHUB_TOKEN: 'synthetic-public-github-token',
      GH_TOKEN: 'synthetic-public-gh-token',
      NPM_TOKEN: 'synthetic-public-npm-token',
      NODE_AUTH_TOKEN: 'synthetic-public-node-auth-token',
    }),
  });

  assert.equal(result.code, 0, result.stderr);
  assert.deepEqual(readNpmLog(log), {
    command: 'npm',
    args: ['ci', '--ignore-scripts'],
    credentials: Object.fromEntries(credentialNames.map(name => [name, ''])),
    gitConfigCount: '',
    gitConfigKey0: '',
    gitConfigValue0: '',
  });
  assert.doesNotMatch(result.stdout + result.stderr, /Authenticated read access|No configured secret/);
  assert.equal(existsSync(gitLog), false, 'public registry install must not probe Git credentials');
});

test('CI installer retains authenticated Git dependency installation for older locks', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-ci-private-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const bin = join(dir, 'bin');
  const log = join(dir, 'npm.json');
  const gitLog = join(dir, 'git.log');
  writeFileSync(join(dir, 'package-lock.json'), fixtureLock('git+https://github.com/promptdriven/runtime-client.git#0123456789abcdef'));
  mkdirSync(bin);
  writeCommands(bin);
  const api = await startApi();
  t.after(() => api.server.close());

  const result = await run(process.execPath, [installer], {
    cwd: dir,
    env: testEnvironment(bin, log, gitLog, {
      GITHUB_API_URL: api.base,
      PRIVATE_REPO_TOKEN: 'synthetic-private-token',
      GITHUB_TOKEN: 'synthetic-private-github-token',
    }),
  });

  assert.equal(result.code, 0, result.stderr);
  assert.deepEqual(api.requests, [{
    url: '/repos/promptdriven/runtime-client',
    authorization: 'Bearer synthetic-private-token',
  }]);
  const npm = readNpmLog(log);
  assert.deepEqual(npm.args, ['ci', '--ignore-scripts']);
  assert.deepEqual(npm.credentials, Object.fromEntries(credentialNames.map(name => [
    name,
    name === 'GITHUB_TOKEN' ? 'synthetic-private-github-token' : '',
  ])));
  assert.equal(npm.gitConfigCount, '3');
  assert.match(npm.gitConfigKey0, /^url\.https:\/\/x-access-token:synthetic-private-token@github\.com\/promptdriven\/.insteadOf$/);
  assert.equal(npm.gitConfigValue0, 'https://github.com/promptdriven/');
  assert.match(readFileSync(gitLog, 'utf8'), /^git config --local --unset-all http\.https:\/\/github\.com\/.extraheader\n$/);
});
