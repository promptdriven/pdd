// Generated from prompts/cli/interpreter-version.prompt.md (sha256: c9053d934c43da87d7bf78a11a79aea374ae246d960960ec1e98eda522cc5435).
import { spawnSync } from 'node:child_process';
import { runtimeOrigin } from './runtime-seam.mjs';

const formatList = value => Array.isArray(value) && value.length <= 32
  && value.every(id => typeof id === 'string' && /^prompt-runtime\.[a-z0-9][a-z0-9._-]{0,127}$/.exec(id)?.[0] === id)
  ? value.join(', ') || 'none' : 'unknown';

function resolveOrigin({ env }) {
  try { return { valid: true, origin: runtimeOrigin(env) }; }
  catch { return { valid: false, origin: '' }; }
}

function readToken({ timeoutMs }, env) {
  const result = spawnSync('gh', ['auth', 'token'], {
    env, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], timeout: timeoutMs, killSignal: 'SIGKILL',
  });
  return { token: !result.error && result.status === 0 ? result.stdout.trim() : '' };
}

// One deadline covers connection, response headers and the complete response body.
async function getMetadata({ origin, path, method, token, timeoutMs, redirect }, fetch) {
  const controller = new AbortController();
  let timer;
  try {
    return await Promise.race([
      (async () => {
        const response = await fetch(new URL(path, origin), {
          method, redirect, headers: { Authorization: `Bearer ${token}` }, signal: controller.signal,
        });
        return { status: response.status, body: await response.text() };
      })(),
      new Promise((_, reject) => {
        timer = setTimeout(() => { controller.abort(); reject(new Error('Metadata deadline')); }, timeoutMs);
      }),
    ]);
  } finally { clearTimeout(timer); }
}

export async function runDetailedVersion({ version, env = {} }, ports = {}) {
  const prefix = `PDD CLI: ${version}\n`;
  const unknown = { exit_code: 0, stdout: `${prefix}PDD interpreter: unknown\n`, stderr: '' };
  try {
    const addressEnv = Object.hasOwn(env, 'PDD_RUNTIME_URL') ? { PDD_RUNTIME_URL: env.PDD_RUNTIME_URL } : {};
    const address = await (ports.resolveOrigin ?? resolveOrigin)({ env: addressEnv });
    if (!address?.valid) return unknown;
    const credentials = await (ports.readToken ?? (input => readToken(input, env)))({ timeoutMs: 2000 });
    if (typeof credentials?.token !== 'string' || !credentials.token.trim()) return unknown;
    const answer = await (ports.getMetadata ?? (input => getMetadata(input, ports.fetch ?? globalThis.fetch)))({
      origin: address.origin, path: '/v1/version', method: 'GET', token: credentials.token,
      timeoutMs: 10000, redirect: 'manual',
    });
    if (answer?.status !== 200 || typeof answer.body !== 'string') return unknown;
    const metadata = JSON.parse(answer.body);
    if (!metadata || typeof metadata !== 'object' || Array.isArray(metadata)
      || typeof metadata.engine_sha !== 'string' || metadata.engine_sha.length !== 40 || !/^[a-f0-9]{40}$/i.test(metadata.engine_sha)) return unknown;
    const serviceLine = Object.hasOwn(metadata, 'service_sha')
      ? `PDD service: ${typeof metadata.service_sha === 'string' && /^[a-f0-9]{40}$/i.test(metadata.service_sha) ? metadata.service_sha.toLowerCase() : 'unknown'}\n`
      : '';
    return { exit_code: 0, stderr: '', stdout: `${prefix}PDD interpreter: ${metadata.engine_sha.toLowerCase()}\n`
      + serviceLine
      + `Interface formats: ${formatList(metadata.formats?.interface)}\n`
      + `Test formats: ${formatList(metadata.formats?.test)}\n`
      + `App-map formats: ${formatList(metadata.formats?.app_map)}\n` };
  } catch { return unknown; }
}
