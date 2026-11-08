// Implements prompts/cli/github-app.prompt.md.
import * as nativeFs from 'node:fs';
import { createHash, createPrivateKey, randomUUID, sign } from 'node:crypto';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { homedir } from 'node:os';
import { dirname, isAbsolute, join, relative, resolve, delimiter } from 'node:path';
import { fileURLToPath } from 'node:url';
import { githubOriginRepository } from './workflow-worktree.mjs';

const nativeExec = promisify(execFile);
const wrapper = fileURLToPath(new URL('../bin/github-app', import.meta.url));
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const fail = reason => { throw Object.assign(Error(`GitHub App: ${reason}`), { code: 'github_app_invalid' }); };
const digest = value => createHash('sha256').update(value).digest('hex');
const required = { issues: 'write', pull_requests: 'write', contents: 'write', metadata: 'read', checks: 'read', statuses: 'read', actions: 'read' };
const permissions = value => Object.entries(required).every(([key, level]) => value?.[key] === level || level === 'read' && value?.[key] === 'write');
const inside = (root, file) => { const path = relative(root, file); return path === '' || !path.startsWith(`..${process.platform === 'win32' ? '\\' : '/'}`) && path !== '..' && !isAbsolute(path); };

export function githubAppSettings({ cwd = process.cwd(), env = process.env, fs = nativeFs } = {}) {
  let root = resolve(env.PDD_GITHUB_APP_ROOT || cwd), config;
  for (;;) {
    try { config = JSON.parse(fs.readFileSync(join(root, 'pdd.json'), 'utf8')); break; }
    catch (error) {
      if (error.code !== 'ENOENT') fail('cannot read pdd.json; fix its JSON and file access.');
      if (env.PDD_GITHUB_APP_ROOT || dirname(root) === root) break;
      root = dirname(root);
    }
  }
  if (!Object.hasOwn(config?.autopilot?.github ?? {}, 'app')) {
    if (env.PDD_GITHUB_APP_ROOT) fail('the bound checkout has no App settings; restore autopilot.github.app.');
    return null;
  }
  const app = config.autopilot.github.app;
  if (!object(app) || !/^[1-9][0-9]*$/.test(String(app.id)) || typeof app.id === 'number' && !Number.isSafeInteger(app.id)) fail('set autopilot.github.app.id to the App ID.');
  if (typeof app.privateKeyFile !== 'string' || !isAbsolute(app.privateKeyFile)) fail('set autopilot.github.app.privateKeyFile to an absolute path outside the repository.');
  let file;
  try { file = fs.realpathSync(app.privateKeyFile); if (!fs.statSync(file).isFile()) throw Error(); }
  catch { fail('cannot read the private key file; check its path and access.'); }
  if (inside(fs.realpathSync(root), file)) fail('keep the private key file outside the repository.');
  return { root, id: String(app.id), privateKeyFile: file };
}

export function githubAppEnvironment({ root, env = process.env }) {
  return { PATH: [wrapper, ...(env.PATH ?? '').split(delimiter).filter(part => resolve(part || '.') !== wrapper)].join(delimiter), PDD_GITHUB_APP_ROOT: root };
}

export function createGithubApp(settings, { fs = nativeFs, fetch = globalThis.fetch, now = Date.now, env = process.env, exec = nativeExec, apiUrl = 'https://api.github.com' } = {}) {
  let saved, pending;
  const request = async (path, token, method = 'GET', body) => {
    let result;
    try { result = await fetch(`${apiUrl}/${path}`, { method, redirect: 'error', signal: AbortSignal.timeout(10000),
      headers: { Accept: 'application/vnd.github+json', Authorization: `Bearer ${token}`, 'X-GitHub-Api-Version': '2022-11-28', ...(body ? { 'Content-Type': 'application/json' } : {}) }, ...(body ? { body: JSON.stringify(body) } : {}) }); }
    catch { fail(`cannot reach GitHub for ${path.includes('access_tokens') ? 'installation authentication' : 'installation access'}; check the network.`); }
    if (!result.ok) fail(`${path.includes('access_tokens') ? 'token creation' : 'installation access'} failed (HTTP ${result.status}); check the App ID, key, permissions and repository installation.`);
    return result;
  };
  const json = async response => { try { return await response.json(); } catch { fail('GitHub sent an invalid installation response.'); } };
  const fresh = entry => object(entry) && typeof entry.token === 'string' && entry.token.length > 0 && !/[\s\x00-\x1f\x7f]/.test(entry.token)
    && Number.isFinite(entry.expiresAt) && entry.expiresAt > now() + 300000 && entry.expiresAt <= now() + 3600000
    && entry.identity?.startsWith(`app:${settings.id}:installation:`) && /^[a-z0-9_.-]+\[bot\]$/i.test(entry.bot ?? '');
  async function load() {
    let pem, key;
    try { pem = fs.readFileSync(settings.privateKeyFile, 'utf8'); key = createPrivateKey(pem); if (key.asymmetricKeyType !== 'rsa') throw Error(); }
    catch { fail('the private key is not a readable RSA private key.'); }
    let repository;
    try { repository = githubOriginRepository((await exec('git', ['remote', 'get-url', 'origin'], { cwd: settings.root, encoding: 'utf8' })).stdout)?.toLowerCase(); }
    catch { /* The reason below does not expose an origin URL or command output. */ }
    if (!repository) fail('origin must name a github.com repository.');
    let folder;
    try { folder = join(fs.realpathSync(env.HOME || homedir()), '.cache', 'pdd', 'github-app'); }
    catch { fail('cannot resolve the credential cache home directory.'); }
    if (inside(fs.realpathSync(settings.root), folder)) fail('keep the credential cache outside the repository.');
    try {
      fs.mkdirSync(folder, { recursive: true, mode: 0o700 });
      const stat = fs.lstatSync(folder);
      if (!stat.isDirectory() || stat.mode & 0o077 || typeof process.getuid === 'function' && stat.uid !== process.getuid()) throw Error();
      if (fs.realpathSync(folder) !== resolve(folder)) throw Error();
    } catch { fail('the credential cache must be a private directory owned by this user (mode 0700).'); }
    const file = join(folder, `${digest(`${settings.id}:${repository}:${pem}`)}.json`);
    let cached;
    try {
      const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW);
      try { const stat = fs.fstatSync(fd); if (stat.isFile() && !(stat.mode & 0o077) && (typeof process.getuid !== 'function' || stat.uid === process.getuid())) cached = JSON.parse(fs.readFileSync(fd, 'utf8')); }
      finally { fs.closeSync(fd); }
    } catch { /* Missing, unsafe or corrupt credentials are never reused. */ }
    if (fresh(cached) && cached.repository === repository) return cached;
    const stamp = Math.floor(now() / 1000), b64 = value => Buffer.from(JSON.stringify(value)).toString('base64url');
    const unsigned = `${b64({ alg: 'RS256', typ: 'JWT' })}.${b64({ iss: settings.id, iat: stamp - 60, exp: stamp + 540 })}`;
    const jwt = `${unsigned}.${sign('RSA-SHA256', Buffer.from(unsigned), key).toString('base64url')}`;
    const installation = await json(await request(`repos/${repository}/installation`, jwt));
    if (!/^[1-9][0-9]*$/.test(String(installation?.id)) || String(installation.app_id) !== settings.id || !/^[a-z0-9_.-]+$/i.test(installation.app_slug ?? '')) fail('the repository installation does not match the configured App.');
    if (!permissions(installation.permissions)) fail('grant Issues, Pull requests and Contents write; Metadata, Checks, Commit statuses and Actions read.');
    const answer = await json(await request(`app/installations/${installation.id}/access_tokens`, jwt, 'POST', { repositories: [repository.split('/')[1]] }));
    const entry = { token: answer.token, expiresAt: Math.min(Date.parse(answer.expires_at), now() + 3600000), repository,
      identity: `app:${settings.id}:installation:${installation.id}`, bot: `${installation.app_slug}[bot]` };
    if (!fresh(entry) || answer.permissions && !permissions(answer.permissions)) fail('GitHub sent an invalid or insufficient installation token.');
    const temp = `${file}.${randomUUID()}.tmp`;
    try { fs.writeFileSync(temp, JSON.stringify(entry), { mode: 0o600, flag: 'wx' }); fs.renameSync(temp, file); }
    catch { fail('cannot save the private credential cache; check file access.'); }
    finally { try { fs.unlinkSync(temp); } catch {} }
    return entry;
  }
  const credentials = async () => {
    if (fresh(saved)) return saved;
    pending ??= load().then(entry => { saved = entry; return entry; }).finally(() => { pending = null; });
    return pending;
  };
  return { credentials, async preflight() {
    const { token, identity, repository, bot } = await credentials();
    await request(`repos/${repository}`, token);
    const response = await request('rate_limit', token), body = await json(response);
    const core = body?.resources?.core;
    if (![core?.limit, core?.remaining, core?.reset].every(Number.isFinite) || core.limit <= 0) fail('GitHub did not report the installation API limit.');
    const rate = `HTTP/2.0 200 OK\r\nX-RateLimit-Limit: ${core.limit}\r\nX-RateLimit-Remaining: ${core.remaining}\r\nX-RateLimit-Reset: ${core.reset}\r\nX-RateLimit-Resource: core\r\n\r\n`;
    return { identity, repository, bot, rate };
  } };
}

export function githubAppRunner(exec, ports = {}) {
  const instances = new Map();
  return async (file, args, options = {}) => {
    if (!['gh', 'git'].includes(file)) return exec(file, args, options);
    const env = options.env ?? ports.env ?? process.env;
    const wrappedPath = (env.PATH ?? '').split(delimiter).some(part => resolve(part || '.') === wrapper);
    const plainOptions = wrappedPath ? { ...options, env: { ...env, PATH: (env.PATH ?? '').split(delimiter).filter(part => resolve(part || '.') !== wrapper).join(delimiter) } } : options;
    const plainEnv = { ...env, PATH: (env.PATH ?? '').split(delimiter).filter(part => resolve(part || '.') !== wrapper).join(delimiter) };
    let command;
    for (let at = 0; at < args.length; at++) {
      if (['-c', '-C', '--git-dir', '--work-tree', '--namespace', '--config-env'].includes(args[at])) { at++; continue; }
      if (!args[at].startsWith('-')) { command = args[at]; break; }
    }
    if (file === 'git' && !['push', 'fetch', 'pull', 'clone', 'ls-remote'].includes(command)) return exec(file, args, plainOptions);
    const settings = githubAppSettings({ cwd: options.cwd, env, fs: ports.fs });
    if (!settings) return exec(file, args, plainOptions);
    if (file === 'gh' && args[0] === 'auth' && args[1] !== 'status') fail('credential commands are unavailable in App mode.');
    const key = JSON.stringify(settings);
    if (!instances.has(key)) instances.set(key, createGithubApp(settings, { ...ports, env, exec }));
    const { token, identity } = await instances.get(key).credentials();
    const basic = Buffer.from(`x-access-token:${token}`).toString('base64');
    const redact = value => typeof value === 'string' ? [token, basic].reduce((text, secret) => text.split(secret).join('[redacted]'), value) : value;
    const childEnv = { ...plainEnv, GH_TOKEN: token, GITHUB_TOKEN: token };
    {
      // gh can invoke Git itself (for example, when creating a PR).
      const extra = [
        ['credential.helper', ''], ['credential.interactive', 'false'],
        ['http.https://github.com/.extraheader', ''], ['http.https://github.com/.extraheader', `AUTHORIZATION: basic ${basic}`],
        ['url.https://github.com/.insteadOf', 'git@github.com:'], ['url.https://github.com/.insteadOf', 'ssh://git@github.com/'],
        ['http.followRedirects', 'false'],
      ];
      const count = Number(childEnv.GIT_CONFIG_COUNT ?? 0);
      if (!Number.isSafeInteger(count) || count < 0 || count > 1000) fail('invalid Git environment configuration.');
      for (let index = 0; index < extra.length; index++) {
        childEnv[`GIT_CONFIG_KEY_${count + index}`] = extra[index][0];
        childEnv[`GIT_CONFIG_VALUE_${count + index}`] = extra[index][1];
      }
      childEnv.GIT_CONFIG_COUNT = String(count + extra.length);
      childEnv.GIT_TERMINAL_PROMPT = '0';
    }
    let result;
    try { result = await exec(file, args, { ...options, env: childEnv }); }
    catch (error) {
      throw Object.assign(Error('GitHub App command failed.'), { code: Number.isInteger(error.code) ? error.code : 'github_app_command_failed',
        stdout: redact(error.stdout ?? ''), stderr: redact(error.stderr ?? ''), githubIdentity: identity });
    }
    return { ...result, stdout: redact(result.stdout), stderr: redact(result.stderr), githubIdentity: identity };
  };
}
