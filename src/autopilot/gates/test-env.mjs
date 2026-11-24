// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: 691dd6196bed4cd3f73c6e54357b81dbbd926f01249066f198c14749055ad53b).
import { execFileSync } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { dirname, isAbsolute, join, resolve } from 'node:path';
import { redactSecrets, rememberSecrets } from '../../secret-redaction.mjs';

const ACCOUNT_NAME_RE = /^[A-Za-z0-9][A-Za-z0-9._-]{0,63}$/;
const ENV_KEY_RE = /^[A-Za-z_][A-Za-z0-9_]{0,127}$/;
const CAPABILITY_KEY_RE = /^[A-Za-z0-9][A-Za-z0-9:._-]{0,79}$/;
const GIT_SHA_RE = /^[0-9a-f]{7,64}$/i;
const MAX_TEST_ENV_BYTES = 65_536;
const MIN_SECRET_LENGTH = 8;

// Strict allowlist for baseEnv copied into post-review sandboxes (mirrors test-suite-queue.mjs clean-v1 policy).
const SAFE_BASE_ENV_KEY_RE = /^(?:PATH|LANG|LANGUAGE|LC_[A-Z_]+|TZ|TERM|CI|SystemRoot|WINDIR|GOPATH|CARGO_HOME|RUSTUP_HOME|VIRTUAL_ENV|HOME|USERPROFILE|TMPDIR|TMP|TEMP|XDG_CONFIG_HOME|XDG_CACHE_HOME)$/;
// Strict blocklist on keys loaded/injected from autopilot-test-env.json so runtime/loader/git/proxy/shell hooks can never be hijacked.
const BLOCKED_INJECT_ENV_RE = /^(?:PATH|HOME|USERPROFILE|SHELL|USER|LOGNAME|TMPDIR|TMP|TEMP|IFS|CDPATH|ENV|BASH_ENV|ZDOTDIR|SHELLOPTS|BASHOPTS|PS4|FPATH|LD_.*|DYLD_.*|NODE_.*|V8_.*|UV_.*|GIT_.*|SSH_.*|NPM_.*|YARN_.*|PNPM_.*|PDD_.*|PYTHON.*|PERL.*|RUBY.*|JAVA_TOOL_OPTIONS|_JAVA_OPTIONS|JDK_JAVA_OPTIONS|CLASSPATH|GOENV|GOFLAGS|RUSTFLAGS|CARGO_.*|HTTP_PROXY|HTTPS_PROXY|ALL_PROXY|NO_PROXY|CURL_.*|SSL_CERT_.*|REQUESTS_CA_BUNDLE|GH_TOKEN|GITHUB_TOKEN)$/i;
const TRIVIAL_NON_SECRET_RE = /^(?:\d+|true|false|yes|no|on|off|pass|fail|passed|failed|proved|none|null|undefined|default|debug|info|warn|error|development|production|test|staging|localhost|127\.0\.0\.1)$/i;
const PROTO_KEYS = new Set(['__proto__', 'constructor', 'prototype']);

const isPlainObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
const isSafeInjectKey = (k) => !PROTO_KEYS.has(k) && ENV_KEY_RE.test(k) && !BLOCKED_INJECT_ENV_RE.test(k);
export const isRegistrableSecret = (v) => typeof v === 'string' && v.trim().length >= MIN_SECRET_LENGTH && !TRIVIAL_NON_SECRET_RE.test(v.trim());

export function defaultTestEnvPath({ homeDir = homedir(), env = process.env } = {}) {
  const xdg = typeof env?.XDG_CONFIG_HOME === 'string' && isAbsolute(env.XDG_CONFIG_HOME)
    ? env.XDG_CONFIG_HOME : join(homeDir, '.config');
  return join(xdg, 'pdd', 'autopilot-test-env.json');
}

const emptyResult = (filePath, ok, reason, error) => ({
  ok, loaded: false, filePath, reason, error, accountNames: [], accounts: {}, envVars: {}, extraCapabilities: [],
});

function collectSecretValues(accounts, envVars) {
  const vals = [];
  for (const map of Object.values(accounts ?? {})) {
    if (!isPlainObj(map)) continue;
    for (const v of Object.values(map)) if (isRegistrableSecret(v)) vals.push(v);
  }
  for (const v of Object.values(envVars ?? {})) if (isRegistrableSecret(v)) vals.push(v);
  return [...new Set(vals)];
}

export function registerTestEnvSecrets(testEnv) {
  if (!isPlainObj(testEnv)) return 0;
  const values = collectSecretValues(testEnv.accounts, testEnv.envVars);
  if (values.length) rememberSecrets(...values);
  return values.length;
}

export const redactTestEnvOutput = (text, extraSecrets = []) =>
  redactSecrets(String(text ?? ''), Array.isArray(extraSecrets) ? extraSecrets.filter(isRegistrableSecret) : []);

/** Sanitized metadata-only view of loaded test-env (ZERO secret values exposed). */
export function summarizeTestEnvMetadata(testEnv) {
  if (!isPlainObj(testEnv)) {
    return { ok: false, loaded: false, filePath: null, reason: 'invalid_test_env', error: null, accountNames: [], extraCapabilities: [] };
  }
  return {
    ok: testEnv.ok === true,
    loaded: testEnv.loaded === true,
    filePath: testEnv.filePath ?? null,
    reason: testEnv.reason ?? null,
    error: testEnv.error ?? null,
    accountNames: Array.isArray(testEnv.accountNames) ? [...testEnv.accountNames] : [],
    extraCapabilities: Array.isArray(testEnv.extraCapabilities) ? [...testEnv.extraCapabilities] : [],
  };
}

function readBoundedFromFd(f, fd, maxBytes) {
  const chunks = [];
  let total = 0;
  const chunkSize = Math.min(8192, maxBytes + 1);
  for (;;) {
    const buf = Buffer.allocUnsafe(chunkSize);
    const n = f.readSync(fd, buf, 0, chunkSize, null);
    if (n <= 0) break;
    total += n;
    if (total > maxBytes) throw Object.assign(new Error(`File exceeds ${maxBytes} bytes.`), { code: 'file_too_large' });
    chunks.push(buf.subarray(0, n));
  }
  return Buffer.concat(chunks, total).toString('utf8');
}

/**
 * Safely load `~/.config/pdd/autopilot-test-env.json` using FD-first TOCTOU-safe open (`O_NOFOLLOW`),
 * `fstatSync(fd)` checks (`0600`, regular file, owner match, bounded size), and parent dir mode check (`& 0o022 === 0`).
 */
export function loadAutopilotTestEnv({
  filePath = null, homeDir = homedir(), env = process.env, fs = nativeFs,
  expectedUid = typeof process.getuid === 'function' ? process.getuid() : null,
} = {}) {
  const f = fs ?? nativeFs;
  const target = resolve(filePath || defaultTestEnvPath({ homeDir, env }));

  // 1. Validate parent directory: real directory, matching owner, and NOT group/world-writable.
  try {
    const pStat = f.lstatSync(dirname(target));
    if (pStat.isSymbolicLink() || !pStat.isDirectory()) {
      return emptyResult(target, false, 'symlink_rejected', 'Parent config directory must be a real directory, not a symlink.');
    }
    if (expectedUid !== null && typeof pStat.uid === 'number' && pStat.uid !== expectedUid) {
      return emptyResult(target, false, 'foreign_owner', 'Parent config directory is owned by another user.');
    }
    if ((pStat.mode & 0o022) !== 0) {
      return emptyResult(target, false, 'insecure_parent_permissions', `Parent config directory is group/world-writable (mode 0${(pStat.mode & 0o777).toString(8)}).`);
    }
  } catch (err) {
    return err?.code === 'ENOENT'
      ? emptyResult(target, true, 'not_found', null)
      : emptyResult(target, false, 'stat_failed', 'Unable to inspect test-env parent directory.');
  }

  // 2. Open target file descriptor FIRST with O_NOFOLLOW | O_NONBLOCK, then verify via fstatSync(fd) (TOCTOU-safe).
  const c = f.constants ?? nativeFs.constants ?? {};
  const openFlags = (c.O_RDONLY ?? 0) | (c.O_NOFOLLOW ?? 0) | (c.O_NONBLOCK ?? 0);
  let fd = null;
  let raw = '';
  try {
    try {
      fd = f.openSync(target, openFlags);
    } catch (err) {
      if (err?.code === 'ENOENT') return emptyResult(target, true, 'not_found', null);
      if (err?.code === 'ELOOP' || err?.code === 'ENOTSUP') return emptyResult(target, false, 'symlink_rejected', 'Refusing symlinked autopilot-test-env.json.');
      return emptyResult(target, false, 'open_failed', 'Unable to open autopilot-test-env.json safely.');
    }
    const st = f.fstatSync(fd);
    if (!st.isFile()) return emptyResult(target, false, 'not_regular_file', 'autopilot-test-env.json must be a regular file.');
    if (expectedUid !== null && typeof st.uid === 'number' && st.uid !== expectedUid) {
      return emptyResult(target, false, 'foreign_owner', 'Refusing autopilot-test-env.json owned by another user.');
    }
    if ((st.mode & 0o177) !== 0) {
      return emptyResult(target, false, 'insecure_permissions', `Refusing autopilot-test-env.json with mode 0${(st.mode & 0o777).toString(8)}; require 0600.`);
    }
    if (typeof st.size === 'number' && st.size > MAX_TEST_ENV_BYTES) {
      return emptyResult(target, false, 'file_too_large', 'autopilot-test-env.json exceeds 64 KiB bound.');
    }
    raw = readBoundedFromFd(f, fd, MAX_TEST_ENV_BYTES);
  } catch (err) {
    const reason = err?.code === 'file_too_large' ? 'file_too_large' : 'read_failed';
    return emptyResult(target, false, reason, 'Failed safe FD-bound read of autopilot-test-env.json.');
  } finally {
    if (fd !== null) try { f.closeSync(fd); } catch { /* ignore */ }
  }

  let parsed;
  try { parsed = JSON.parse(raw); } catch { return emptyResult(target, false, 'invalid_json', 'autopilot-test-env.json is not valid JSON.'); }
  if (!isPlainObj(parsed)) return emptyResult(target, false, 'invalid_schema', 'autopilot-test-env.json must contain a JSON object.');

  const accounts = {};
  if (isPlainObj(parsed.accounts)) {
    for (const [acctName, rawVars] of Object.entries(parsed.accounts)) {
      if (PROTO_KEYS.has(acctName) || !ACCOUNT_NAME_RE.test(acctName) || !isPlainObj(rawVars)) continue;
      const cleanVars = {};
      for (const [k, v] of Object.entries(rawVars)) if (isSafeInjectKey(k) && typeof v === 'string') cleanVars[k] = v;
      accounts[acctName] = cleanVars;
    }
  }
  const envVars = {};
  if (isPlainObj(parsed.env)) {
    for (const [k, v] of Object.entries(parsed.env)) if (isSafeInjectKey(k) && typeof v === 'string') envVars[k] = v;
  }
  const extraCapabilities = Array.isArray(parsed.capabilities)
    ? [...new Set(parsed.capabilities.filter((cap) => typeof cap === 'string' && CAPABILITY_KEY_RE.test(cap.trim())).map((cap) => cap.trim()))].sort()
    : [];

  const result = {
    ok: true, loaded: true, filePath: target, reason: null, error: null,
    accountNames: Object.keys(accounts).sort(), accounts, envVars, extraCapabilities,
  };
  registerTestEnvSecrets(result);
  return result;
}

const defaultWhich = (bin, env = process.env) => {
  try { execFileSync('which', [bin], { env, encoding: 'utf8', timeout: 1500, stdio: ['ignore', 'pipe', 'ignore'] }); return true; }
  catch { return false; }
};
const defaultExecOk = (cmd, args, env = process.env) => {
  try { execFileSync(cmd, args, { env, encoding: 'utf8', timeout: 2500, stdio: ['ignore', 'ignore', 'ignore'] }); return true; }
  catch { return false; }
};

/**
 * Probe host machine capabilities returning open capability keys (`tty`, `browser`, `docker`,
 * `ios-simulator`, and KEY NAMES ONLY `account:<name>` — NEVER secret values).
 */
export function probeMachineCapabilities({
  testEnv = null, env = process.env, platform = process.platform,
  whichFn = (bin) => defaultWhich(bin, env),
  execFn = (cmd, args) => defaultExecOk(cmd, args, env),
  ttyCheck = null,
} = {}) {
  const caps = new Set();
  const hasTty = typeof ttyCheck === 'function' ? Boolean(ttyCheck()) : Boolean(process.stdin?.isTTY && process.stdout?.isTTY);
  if (hasTty) caps.add('tty');
  if ((typeof env?.PLAYWRIGHT_BROWSERS_PATH === 'string' && env.PLAYWRIGHT_BROWSERS_PATH.trim()) || whichFn('chromium') || whichFn('google-chrome') || whichFn('playwright')) {
    caps.add('browser');
  }
  if (whichFn('docker') && execFn('docker', ['info'])) caps.add('docker');
  if (platform === 'darwin' && whichFn('xcrun') && execFn('xcrun', ['simctl', 'list', 'devices'])) caps.add('ios-simulator');

  const accountNames = [];
  if (testEnv?.ok === true && Array.isArray(testEnv.accountNames)) {
    for (const name of testEnv.accountNames) {
      if (typeof name === 'string' && ACCOUNT_NAME_RE.test(name)) { accountNames.push(name); caps.add(`account:${name}`); }
    }
  }
  if (testEnv?.ok === true && Array.isArray(testEnv.extraCapabilities)) {
    for (const cap of testEnv.extraCapabilities) if (typeof cap === 'string' && CAPABILITY_KEY_RE.test(cap)) caps.add(cap);
  }
  return { capabilities: [...caps].sort(), accountNames: accountNames.sort() };
}

/**
 * Post-review-only sandbox environment injection guard.
 * Requires `reviewApproved === true`, valid non-empty matching Git hex SHAs, strict baseEnv allowlist,
 * and strict injected-key safety filtering.
 */
export function buildPostReviewSandboxEnv({
  baseEnv = {}, testEnv = null, reviewApproved = false, approvedHead = '', currentHead = '',
  allowedAccounts = [], allowedEnvKeys = [],
} = {}) {
  if (reviewApproved !== true) {
    throw Object.assign(new Error('Refusing test-env secret injection: reviewApproved must be strictly true.'), { code: 'review_not_approved' });
  }
  const ah = String(approvedHead ?? '').trim(), ch = String(currentHead ?? '').trim();
  if (!GIT_SHA_RE.test(ah) || !GIT_SHA_RE.test(ch)) {
    throw Object.assign(new Error('Refusing test-env secret injection: approvedHead and currentHead must be valid non-empty Git hex SHAs.'), { code: 'invalid_head_sha' });
  }
  if (ah.toLowerCase() !== ch.toLowerCase()) {
    throw Object.assign(new Error('Refusing test-env secret injection: candidate head changed after review approval.'), { code: 'head_mismatch' });
  }
  if (testEnv && testEnv.ok === false) {
    throw Object.assign(new Error(`Refusing test-env secret injection: ${testEnv.reason || 'unsafe test-env'}.`), { code: 'unsafe_test_env' });
  }

  const outEnv = {};
  if (isPlainObj(baseEnv)) {
    for (const [k, v] of Object.entries(baseEnv)) {
      if (typeof v === 'string' && SAFE_BASE_ENV_KEY_RE.test(k)) outEnv[k] = v;
    }
  }

  const injectedKeys = [], injectedSecrets = [];
  const injectPair = (k, v) => {
    if (!isSafeInjectKey(k) || typeof v !== 'string') return;
    outEnv[k] = v;
    injectedKeys.push(k);
    if (isRegistrableSecret(v)) injectedSecrets.push(v);
  };
  if (testEnv?.ok === true) {
    for (const acct of Array.isArray(allowedAccounts) ? allowedAccounts : []) {
      const vars = testEnv.accounts?.[acct];
      if (isPlainObj(vars)) for (const [k, v] of Object.entries(vars)) injectPair(k, v);
    }
    for (const key of Array.isArray(allowedEnvKeys) ? allowedEnvKeys : []) {
      if (Object.hasOwn(testEnv.envVars ?? {}, key)) injectPair(key, testEnv.envVars[key]);
    }
  }
  if (injectedSecrets.length) rememberSecrets(...injectedSecrets);
  return {
    env: outEnv,
    injectedKeys: [...new Set(injectedKeys)].sort(),
    registeredSecretCount: injectedSecrets.length,
    redact: (text) => redactSecrets(String(text ?? ''), injectedSecrets),
  };
}
