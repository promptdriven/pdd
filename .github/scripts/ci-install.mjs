import { createSign } from 'node:crypto';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const repo = 'promptdriven/runtime-client';
const apiBase = (process.env.GITHUB_API_URL || 'https://api.github.com').replace(/\/+$/, '');
const baseHeaders = {
  Accept: 'application/vnd.github+json',
  'X-GitHub-Api-Version': '2022-11-28',
  'User-Agent': 'pdd-ci',
};

async function checkRepoAccess(token) {
  if (!token) return { ok: false, status: 0 };
  const res = await fetch(`${apiBase}/repos/${repo}`, {
    headers: { ...baseHeaders, Authorization: `Bearer ${token}` },
  });
  return { ok: res.status === 200, status: res.status };
}

function normalizePem(raw) {
  let key = String(raw ?? '').trim();
  if (!key) return '';
  if (!key.includes('BEGIN ')) {
    try { key = Buffer.from(key, 'base64').toString('utf8').trim(); } catch {}
  }
  key = key.replace(/\\n/g, '\n').trim();
  return key ? `${key}\n` : '';
}

function checkDeployKeyAccess(sshCommand) {
  const probe = spawnSync('git', ['ls-remote', `ssh://git@github.com/${repo}.git`, 'HEAD'], {
    env: { ...process.env, GIT_SSH_COMMAND: sshCommand, GIT_TERMINAL_PROMPT: '0' },
    encoding: 'utf8',
    timeout: 20_000,
  });
  return { ok: probe.status === 0, status: probe.status };
}

async function mintAppToken(rawAppId, rawKey) {
  const appId = String(rawAppId ?? '').trim();
  const pem = normalizePem(rawKey);
  if (!appId || !pem) return { token: '', reason: 'unset' };
  const now = Math.floor(Date.now() / 1000);
  const b64 = obj => Buffer.from(JSON.stringify(obj)).toString('base64url');
  const iss = /^\d+$/.test(appId) ? Number(appId) : appId;
  const unsigned = `${b64({ alg: 'RS256', typ: 'JWT' })}.${b64({ iat: now - 60, exp: now + 300, iss })}`;
  const jwt = `${unsigned}.${createSign('RSA-SHA256').update(unsigned).sign(pem, 'base64url')}`;
  const jwtHeaders = { ...baseHeaders, Authorization: `Bearer ${jwt}` };

  let instRes = await fetch(`${apiBase}/repos/${repo}/installation`, { headers: jwtHeaders });
  if (instRes.status !== 200) {
    instRes = await fetch(`${apiBase}/orgs/promptdriven/installation`, { headers: jwtHeaders });
  }
  if (instRes.status !== 200) return { token: '', reason: `installation HTTP ${instRes.status}` };
  const inst = await instRes.json();

  let tokRes = await fetch(`${apiBase}/app/installations/${inst.id}/access_tokens`, {
    method: 'POST',
    headers: { ...jwtHeaders, 'Content-Type': 'application/json' },
    body: JSON.stringify({ repositories: ['runtime-client'], permissions: { contents: 'read' } }),
  });
  if (tokRes.status !== 201) {
    tokRes = await fetch(`${apiBase}/app/installations/${inst.id}/access_tokens`, {
      method: 'POST',
      headers: { ...jwtHeaders, 'Content-Type': 'application/json' },
      body: JSON.stringify({ permissions: { contents: 'read' } }),
    });
  }
  if (tokRes.status !== 201) return { token: '', reason: `access_tokens HTTP ${tokRes.status}` };
  const data = await tokRes.json();
  const token = String(data?.token ?? '').trim();
  if (token) process.stdout.write(`::add-mask::${token}\n`);
  return { token, reason: token ? 'ok' : 'empty token' };
}

const attempts = [];
let selected = null;
let keyDir = '';

try {
  const deployKey = normalizePem(process.env.RUNTIME_CLIENT_DEPLOY_KEY);
  if (!deployKey) {
    attempts.push('RUNTIME_CLIENT_DEPLOY_KEY=unset');
  } else {
    keyDir = mkdtempSync(join(tmpdir(), 'pdd-ci-key-'));
    const keyPath = join(keyDir, 'id_ed25519');
    const knownHostsPath = join(keyDir, 'known_hosts');
    writeFileSync(keyPath, deployKey, { mode: 0o600 });
    const sshCommand = `ssh -i "${keyPath}" -o IdentitiesOnly=yes -o StrictHostKeyChecking=accept-new -o UserKnownHostsFile="${knownHostsPath}" -o BatchMode=yes`;
    const check = checkDeployKeyAccess(sshCommand);
    attempts.push(`RUNTIME_CLIENT_DEPLOY_KEY=exit ${check.status}`);
    if (check.ok) {
      selected = { kind: 'ssh', name: 'RUNTIME_CLIENT_DEPLOY_KEY', sshCommand };
    }
  }

  if (!selected) {
    for (const [name, raw] of [['PRIVATE_REPO_TOKEN', process.env.PRIVATE_REPO_TOKEN], ['PDS_TOKEN', process.env.PDS_TOKEN]]) {
      const token = String(raw ?? '').trim();
      if (!token) { attempts.push(`${name}=unset`); continue; }
      const check = await checkRepoAccess(token);
      attempts.push(`${name}=HTTP ${check.status}`);
      if (check.ok) { selected = { kind: 'https', name, token }; break; }
    }
  }

  if (!selected) {
    const minted = await mintAppToken(process.env.PDD_CLOUD_APP_ID, process.env.PDD_CLOUD_APP_PRIVATE_KEY);
    if (!minted.token) {
      attempts.push(`PDD_CLOUD_APP=${minted.reason}`);
    } else {
      const check = await checkRepoAccess(minted.token);
      attempts.push(`PDD_CLOUD_APP=HTTP ${check.status}`);
      if (check.ok) selected = { kind: 'https', name: 'PDD_CLOUD_APP', token: minted.token };
    }
  }

  if (!selected) {
    console.error(`No configured secret has read access to ${repo} (${attempts.join(', ')}).`);
    process.exit(1);
  }
  console.log(`Authenticated read access to ${repo} via ${selected.name}.`);

  try { execFileSync('git', ['config', '--local', '--unset-all', 'http.https://github.com/.extraheader'], { stdio: 'ignore' }); } catch {}

  const scrubbedEnv = {
    ...process.env,
    RUNTIME_CLIENT_DEPLOY_KEY: '',
    PRIVATE_REPO_TOKEN: '',
    PDS_TOKEN: '',
    PDD_CLOUD_APP_ID: '',
    PDD_CLOUD_APP_PRIVATE_KEY: '',
  };

  let childEnv;
  if (selected.kind === 'ssh') {
    const sshKey = `url.ssh://git@github.com/${repo}.insteadOf`;
    childEnv = {
      ...scrubbedEnv,
      GIT_SSH_COMMAND: selected.sshCommand,
      GIT_CONFIG_COUNT: '2',
      GIT_CONFIG_KEY_0: sshKey,
      GIT_CONFIG_VALUE_0: `https://github.com/${repo}`,
      GIT_CONFIG_KEY_1: sshKey,
      GIT_CONFIG_VALUE_1: `git@github.com:${repo}`,
    };
  } else {
    const httpsKey = `url.https://x-access-token:${selected.token}@github.com/promptdriven/.insteadOf`;
    childEnv = {
      ...scrubbedEnv,
      GIT_CONFIG_COUNT: '3',
      GIT_CONFIG_KEY_0: httpsKey,
      GIT_CONFIG_VALUE_0: 'https://github.com/promptdriven/',
      GIT_CONFIG_KEY_1: httpsKey,
      GIT_CONFIG_VALUE_1: 'ssh://git@github.com/promptdriven/',
      GIT_CONFIG_KEY_2: httpsKey,
      GIT_CONFIG_VALUE_2: 'git@github.com:promptdriven/',
    };
  }

  execFileSync('npm', ['ci', '--ignore-scripts'], { env: childEnv, stdio: 'inherit' });
} finally {
  if (keyDir) {
    try { rmSync(keyDir, { recursive: true, force: true }); } catch {}
  }
}
