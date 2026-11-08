// Local GitHub App token endpoint, plus the existing fake GitHub/Herdr world.
import { createServer } from 'node:http';
import { generateKeyPairSync, verify } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import assert from 'node:assert/strict';
import { autopilotGithubWorld } from './autopilot-github-world.mjs';

export async function githubAppWorld(t) {
  const w = await autopilotGithubWorld({ issues: 0 });
  t.after(() => w.cleanup());
  const { privateKey, publicKey } = generateKeyPairSync('rsa', { modulusLength: 2048 });
  w.keyFile = join(w.dir, 'app.pem');
  writeFileSync(w.keyFile, privateKey.export({ type: 'pkcs8', format: 'pem' }), { mode: 0o600 });
  w.app = { id: '1234', privateKeyFile: w.keyFile };
  w.permissions = { issues: 'write', pull_requests: 'write', contents: 'write', metadata: 'read', checks: 'read', statuses: 'read', actions: 'read' };
  w.tokens = []; w.http = []; w.installed = true; w.limit = 15000; w.bot = 'pdd-autopilot[bot]'; w.identity = 'app:1234:installation:9876';
  w.github.limit = w.limit; w.github.remaining = w.limit;
  w.env = { HOME: w.home, PATH: process.env.PATH };
  w.configure = app => {
    writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [w.bot], github: { app } } }));
  };
  w.configure(w.app);
  const server = createServer(async (req, res) => {
    const chunks = []; for await (const chunk of req) chunks.push(chunk);
    const body = chunks.length ? JSON.parse(Buffer.concat(chunks).toString()) : undefined;
    const path = req.url, auth = req.headers.authorization?.slice(7);
    w.http.push({ path, method: req.method, body });
    const reply = (status, value) => { res.writeHead(status, { 'Content-Type': 'application/json' }); res.end(JSON.stringify(value)); };
    if (path === '/repos/acme/widgets/installation' || path === '/app/installations/9876/access_tokens') {
      const [head, payload, signature] = String(auth).split('.');
      const claims = JSON.parse(Buffer.from(payload, 'base64url'));
      assert.equal(JSON.parse(Buffer.from(head, 'base64url')).alg, 'RS256');
      assert.equal(claims.iss, '1234');
      assert.equal(claims.iat, Math.floor(w.time / 1000) - 60);
      assert.ok(claims.exp <= Math.floor(w.time / 1000) + 600);
      assert.ok(verify('RSA-SHA256', Buffer.from(`${head}.${payload}`), publicKey, Buffer.from(signature, 'base64url')));
      if (w.authFailure) return reply(w.authFailure, { message: w.remoteError ?? 'authentication refused' });
      if (path.endsWith('/installation')) return reply(w.installed ? 200 : 404, { id: 9876, app_id: w.wrongApp ? 999 : 1234, app_slug: 'pdd-autopilot', permissions: w.permissions });
      assert.deepEqual(body, { repositories: ['widgets'] });
      const token = `fake-installation-token-${w.tokens.length + 1}`; w.tokens.push(token);
      return reply(201, { token: w.badToken ? '' : token, expires_at: w.badExpiry ? 'invalid' : new Date(w.time + 3600000).toISOString(), permissions: w.permissions });
    }
    if (!w.tokens.includes(auth)) return reply(401, { message: 'wrong installation token' });
    if (w.accessFailure) return reply(w.accessFailure, { message: w.remoteError });
    if (path === '/repos/acme/widgets') return reply(200, { full_name: 'acme/widgets' });
    if (path === '/rate_limit') return reply(200, { resources: { core: { limit: w.limit, remaining: w.limit - 10, reset: Math.floor(w.time / 1000) + 3600 } } });
    return reply(404, {});
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  t.after(() => new Promise(resolve => server.close(resolve)));
  w.appPorts = { apiUrl: `http://127.0.0.1:${server.address().port}`, now: () => w.time, env: w.env };
  const originalRun = w.ports.run;
  w.ghOptions = []; w.launches = [];
  w.ports.githubApp = w.appPorts;
  w.ports.run = async (command, args, options = {}) => {
    if (command === 'gh') {
      w.ghOptions.push({ args, env: options.env });
      if (args[0] === 'auth') return { code: 1, stdout: '', stderr: 'No personal login' };
      assert.ok(w.tokens.includes(options.env?.GH_TOKEN), 'gh must use an installation token');
    }
    return originalRun(command, args, options);
  };
  const originalHerdr = w.ports.herdr;
  w.ports.herdr = async args => { if (args[0] === 'pane' && args[1] === 'run') w.launches.push(args.at(-1)); return originalHerdr(args); };
  w.gitExec = async (file, args, options = {}) => {
    if (file !== 'git') throw Error('unexpected command');
    return { code: 0, stdout: execFileSync(file, args, { cwd: options.cwd ?? w.cwd, encoding: 'utf8' }), stderr: '' };
  };
  w.mkdir = path => mkdirSync(path, { recursive: true });
  w.readConfig = () => JSON.parse(readFileSync(join(w.cwd, 'pdd.json')));
  return w;
}
