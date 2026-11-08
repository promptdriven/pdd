import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { createServer as httpsServer } from 'node:https';
import { createServer as httpServer } from 'node:http';
import { connect } from 'node:net';
import { nativeGithubCounter } from '../src/github-calls.mjs';
import { githubAppWorld } from './helpers/github-app-world.mjs';
import { chatLaunch } from '../src/workflow-chat.mjs';

const execute = promisify(execFile);
const url = 'https://github.com/acme/widgets.git';
const scope = `http.${url}.extraheader`;
const personal = 'basic synthetic-personal-header';

// Only loopback is contacted. Real Git sees a GitHub URL through a local CONNECT
// proxy. A deliberate 403 stops the Git protocol after we observe its headers.
async function gitEndpoint(t, w) {
  const key = join(w.dir, 'tls-key.pem'), cert = join(w.dir, 'tls-cert.pem');
  execFileSync('openssl', ['req', '-x509', '-newkey', 'rsa:2048', '-nodes', '-keyout', key,
    '-out', cert, '-days', '1', '-subj', '/CN=github.com'], { stdio: 'ignore' });
  const requests = [], sockets = new Set();
  const track = socket => { sockets.add(socket); socket.on('close', () => sockets.delete(socket)); socket.on('error', () => socket.destroy()); };
  const endpoint = httpsServer({ key: readFileSync(key), cert: readFileSync(cert) }, (req, res) => {
    requests.push({ headers: req.headers, authorizationCount: req.rawHeaders.filter((x, i) => i % 2 === 0 && x.toLowerCase() === 'authorization').length });
    res.writeHead(403); res.end();
  });
  endpoint.on('connection', track);
  const proxy = httpServer();
  proxy.on('connect', (req, socket, head) => {
    track(socket);
    if (req.url !== 'github.com:443') { socket.destroy(); return; }
    const upstream = connect(endpoint.address().port, '127.0.0.1', () => {
      socket.write('HTTP/1.1 200 Connection Established\r\n\r\n');
      if (head.length) upstream.write(head);
      socket.pipe(upstream); upstream.pipe(socket);
    });
    track(upstream);
  });
  t.after(async () => {
    for (const socket of sockets) socket.destroy();
    await Promise.all([endpoint, proxy].map(server => new Promise((resolve, reject) => server.close(error => error ? reject(error) : resolve()))));
  });
  await new Promise(resolve => endpoint.listen(0, '127.0.0.1', resolve));
  await new Promise(resolve => proxy.listen(0, '127.0.0.1', resolve));
  return { requests, env: { ...w.env, https_proxy: `http://127.0.0.1:${proxy.address().port}`,
    HTTPS_PROXY: '', ALL_PROXY: '', all_proxy: '', NO_PROXY: '', no_proxy: '', GIT_SSL_NO_VERIFY: 'true' } };
}

function inheritedConfig(w, source, env) {
  // Preserve a multi-valued non-auth header, another host, and an unrelated option.
  execFileSync('git', ['config', '--add', scope, 'X-Pdd-Test: retained'], { cwd: w.cwd });
  execFileSync('git', ['config', 'http.https://example.invalid/.extraheader', 'X-Other: retained'], { cwd: w.cwd });
  const result = { ...env, GIT_CONFIG_COUNT: '1', GIT_CONFIG_KEY_0: 'fetch.prune', GIT_CONFIG_VALUE_0: 'true' };
  if (source === 'repository') execFileSync('git', ['config', '--add', scope, `AUTHORIZATION: ${personal}`], { cwd: w.cwd });
  else Object.assign(result, { GIT_CONFIG_COUNT: '2', GIT_CONFIG_KEY_1: scope, GIT_CONFIG_VALUE_1: `AUTHORIZATION: ${personal}` });
  return result;
}

for (const source of ['repository', 'environment']) {
  for (const route of ['native Git', 'nested gh', 'worker Git', 'worker gh']) {
    test(`App overrides ${source} URL authorization on the wire through ${route}`, async t => {
      const w = await githubAppWorld(t), endpoint = await gitEndpoint(t, w);
      w.time = Date.now();
      const env = inheritedConfig(w, source, endpoint.env);
      const configFile = join(w.cwd, '.git', 'config'), before = readFileSync(configFile, 'utf8');
      let invoked = false;
      const run = nativeGithubCounter(async (file, args, options) => {
        if (file === 'gh') {
          invoked = true;
          // Model gh's nested push with a real read-only Git HTTPS request.
          return execute('git', ['ls-remote', url], options);
        }
        if (args.includes('ls-remote')) invoked = true;
        return execute(file, args, options);
      }, { env: w.env, stateRoot: w.stateRoot, now: () => w.time, appPorts: w.appPorts });
      if (route.startsWith('worker')) {
        // Seed the private cache, then use the real bundled shell wrapper.
        await nativeGithubCounter(async (file, args, options) => file === 'git' ? execute(file, args, options) : { code: 0, stdout: '', stderr: '' },
          { env: w.env, stateRoot: w.stateRoot, now: () => w.time, appPorts: w.appPorts })('gh', ['auth', 'status'], { cwd: w.cwd, env: w.env });
        const bin = join(w.dir, 'fake-bin'), runDir = join(w.dir, 'run'); mkdirSync(bin); mkdirSync(runDir);
        writeFileSync(join(bin, 'gh'), `#!${process.execPath}
const { spawnSync } = require('node:child_process');
const r = spawnSync('git', ['ls-remote', ${JSON.stringify(url)}], { env:process.env, encoding:'utf8' });
process.stdout.write(r.stdout); process.stderr.write(r.stderr); process.exitCode=r.status;
`, { mode: 0o755 });
        const workerEnv = { ...env, PATH: `${bin}:${env.PATH}` };
        const launch = chatLaunch({ run: { sourceRoot: w.cwd, root: w.cwd, runDir }, agent: 'codex', env: workerEnv });
        const { runAgentProcess } = await import('../src/agent-adapters.mjs');
        const answer = await runAgentProcess(route === 'worker Git' ? 'git' : 'gh',
          route === 'worker Git' ? ['ls-remote', url] : ['pr', 'create', '--repo', w.repository],
          { cwd: w.cwd, env: { ...workerEnv, ...launch.githubEnv } });
        assert.equal(answer.code, 128);
        assert.match(answer.stderr, /403/);
      } else {
        await assert.rejects(run(route === 'native Git' ? 'git' : 'gh',
          route === 'native Git' ? ['ls-remote', url] : ['pr', 'create', '--repo', w.repository],
          { cwd: w.cwd, env, encoding: 'utf8', timeout: 5000 }), error => error.code === 128 && /403/.test(error.stderr));
        assert.equal(invoked, true);
      }
      assert.equal(endpoint.requests.length, 1);
      const request = endpoint.requests[0];
      assert.ok(w.tokens.some(token => request.headers.authorization === `basic ${Buffer.from(`x-access-token:${token}`).toString('base64')}`),
        'Git must send App authorization at the repository URL scope');
      assert.equal(request.authorizationCount, 1);
      assert.equal(request.headers['x-pdd-test'], 'retained');
      assert.equal(readFileSync(configFile, 'utf8'), before);
      assert.equal(env.GIT_CONFIG_VALUE_0, 'true');
      assert.ok(!JSON.stringify(env).includes('fake-installation-token-'));
    });
  }

  test(`personal mode preserves ${source} URL authorization on the wire`, async t => {
    const w = await githubAppWorld(t), endpoint = await gitEndpoint(t, w);
    writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto' } }));
    const env = inheritedConfig(w, source, endpoint.env);
    const run = nativeGithubCounter(execute, { env: w.env, stateRoot: w.stateRoot, appPorts: w.appPorts });
    await assert.rejects(run('git', ['ls-remote', url], { cwd: w.cwd, env, encoding: 'utf8', timeout: 5000 }), error => error.code === 128 && /403/.test(error.stderr));
    assert.equal(endpoint.requests.length, 1);
    assert.ok(endpoint.requests[0].headers.authorization === personal);
    assert.equal(w.tokens.length, 0);
  });
}

for (const source of ['included config', 'Git parameters', 'command options', 'config env option', 'config env equals option']) {
  test(`App overrides ${source} at a user and repository URL scope`, async t => {
    const w = await githubAppWorld(t), endpoint = await gitEndpoint(t, w);
    const name = 'http.https://git@github.com/acme/widgets.git.extraheader';
    const env = { ...endpoint.env, PDD_GITHUB_APP_ROOT: w.cwd };
    let options = [];
    if (source === 'included config') {
      const file = join(w.dir, 'included.conf');
      writeFileSync(file, `[http "https://git@github.com/acme/widgets.git"]\nextraheader = AUTHORIZATION: ${personal}\n`);
      execFileSync('git', ['config', 'include.path', file], { cwd: w.cwd });
      options = ['-C', w.cwd];
    } else if (source === 'Git parameters') env.GIT_CONFIG_PARAMETERS = `'${name}=AUTHORIZATION: ${personal}' 'fetch.prune=true'`;
    else if (source === 'command options') options = ['-C', w.cwd, '-c', `${name}=AUTHORIZATION: ${personal}`];
    else {
      env.SYNTHETIC_HEADER = `AUTHORIZATION: ${personal}`;
      options = source === 'config env option' ? ['--config-env', `${name}=SYNTHETIC_HEADER`] : [`--config-env=${name}=SYNTHETIC_HEADER`];
    }
    const run = nativeGithubCounter(execute, { env: w.env, stateRoot: w.stateRoot, now: () => w.time, appPorts: w.appPorts });
    await assert.rejects(run('git', [...options, 'ls-remote', url.replace('https://', 'https://git@')],
      { cwd: source === 'included config' ? w.dir : w.cwd, env, encoding: 'utf8', timeout: 5000 }), error => error.code === 128 && /403/.test(error.stderr));
    assert.ok(endpoint.requests.length > 0);
    assert.ok(w.tokens.some(token => endpoint.requests[0].headers.authorization === `basic ${Buffer.from(`x-access-token:${token}`).toString('base64')}`),
      'Git must send App authorization at the user and repository URL scope');
    assert.equal(endpoint.requests.length, 1);
    assert.equal(endpoint.requests[0].authorizationCount, 1);
  });
}

test('App config read failure stops before a Git network command and hides its output', async t => {
  const w = await githubAppWorld(t); let network = 0;
  const run = nativeGithubCounter(async (file, args, options) => {
    if (args.includes('--list')) throw Object.assign(Error('synthetic-private-config'), { stderr: 'synthetic-private-config' });
    if (args.includes('ls-remote')) { network++; return { code: 0, stdout: '', stderr: '' }; }
    return execute(file, args, options);
  }, { env: w.env, stateRoot: w.stateRoot, now: () => w.time, appPorts: w.appPorts });
  await assert.rejects(run('git', ['ls-remote', url], { cwd: w.cwd, env: w.env }), error => {
    assert.equal(error.code, 'github_app_invalid');
    assert.ok(!JSON.stringify([error.message, error.stderr]).includes('synthetic-private-config'));
    return true;
  });
  assert.equal(network, 0);
});
