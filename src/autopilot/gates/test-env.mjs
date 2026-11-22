// Layer-2 safe 0600 autopilot test-env loader, open machine capability probe, and post-review-only env guard.
import { execFileSync } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { dirname, isAbsolute, join, resolve } from 'node:path';
import { redactSecrets, rememberSecrets } from '../../secret-redaction.mjs';
import { readBoundedUtf8 } from '../../shared/safe-read.mjs';

const ACCOUNT_NAME_RE = /^[A-Za-z0-9][A-Za-z0-9._-]{0,63}$/;
const ENV_KEY_RE = /^[A-Za-z_][A-Za-z0-9_]{0,127}$/;
const CAPABILITY_KEY_RE = /^[A-Za-z0-9][A-Za-z0-9:._-]{0,79}$/;
const DANGEROUS_ENV_KEYS = new Set([
  'LD_PRELOAD', 'LD_LIBRARY_PATH', 'DYLD_INSERT_LIBRARIES', 'DYLD_LIBRARY_PATH',
  'DYLD_FRAMEWORK_PATH', 'NODE_OPTIONS', 'PYTHONPATH', 'PYTHONSTARTUP', 'BASH_ENV', 'ENV', 'SHELLOPTS', 'PS4',
]);
const PROTO_KEYS = new Set(['__proto__', 'constructor', 'prototype']);
const isPlainObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
const isSafeEnvKey = (k) => !PROTO_KEYS.has(k) && ENV_KEY_RE.test(k) && !DANGEROUS_ENV_KEYS.has(k.toUpperCase());

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
    for (const v of Object.values(map)) if (typeof v === 'string' && v) vals.push(v);
  }
  for (const v of Object.values(envVars ?? {})) if (typeof v === 'string' && v) vals.push(v);
  return [...new Set(vals)];
}

export function registerTestEnvSecrets(testEnv) {
  if (!isPlainObj(testEnv)) return 0;
  const values = collectSecretValues(testEnv.accounts, testEnv.envVars);
  if (values.length) rememberSecrets(...values);
  return values.length;
}

export const redactTestEnvOutput = (text, extraSecrets = []) =>
  redactSecrets(String(text ?? ''), Array.isArray(extraSecrets) ? extraSecrets : []);

/**
 * Safely load `~/.config/pdd/autopilot-test-env.json` with strict `0600` & no-symlink enforcement.
 * Registers all secret values for log redaction; never exposes secret values in errors or capabilities.
 */
export function loadAutopilotTestEnv({
  filePath = null, homeDir = homedir(), env = process.env, fs = nativeFs,
  expectedUid = typeof process.getuid === 'function' ? process.getuid() : null,
} = {}) {
  const f = fs ?? nativeFs;
  const target = resolve(filePath || defaultTestEnvPath({ homeDir, env }));

  try {
    const pStat = f.lstatSync(dirname(target));
    if (pStat.isSymbolicLink() || !pStat.isDirectory()) {
      return emptyResult(target, false, 'symlink_rejected', 'Parent config directory must be a real directory, not a symlink.');
    }
    if (expectedUid !== null && typeof pStat.uid === 'number' && pStat.uid !== expectedUid) {
      return emptyResult(target, false, 'foreign_owner', 'Parent config directory is owned by another user.');
    }
  } catch (err) {
    return err?.code === 'ENOENT'
      ? emptyResult(target, true, 'not_found', null)
      : emptyResult(target, false, 'stat_failed', 'Unable to inspect test-env parent directory.');
  }

  let st;
  try {
    st = f.lstatSync(target);
  } catch (err) {
    return err?.code === 'ENOENT'
      ? emptyResult(target, true, 'not_found', null)
      : emptyResult(target, false, 'stat_failed', 'Unable to inspect test-env file.');
  }

  if (st.isSymbolicLink()) return emptyResult(target, false, 'symlink_rejected', 'Refusing symlinked autopilot-test-env.json.');
  if (!st.isFile()) return emptyResult(target, false, 'not_regular_file', 'autopilot-test-env.json must be a regular file.');
  if (expectedUid !== null && typeof st.uid === 'number' && st.uid !== expectedUid) {
    return emptyResult(target, false, 'foreign_owner', 'Refusing autopilot-test-env.json owned by another user.');
  }
  if ((st.mode & 0o177) !== 0) {
    return emptyResult(target, false, 'insecure_permissions', `Refusing autopilot-test-env.json with mode 0${(st.mode & 0o777).toString(8)}; require 0600.`);
  }

  let raw;
  try {
    raw = readBoundedUtf8(target, { maxBytes: 65_536, noFollow: true, fs: f });
    const postSt = f.lstatSync(target);
    if (postSt.isSymbolicLink() || !postSt.isFile() || (postSt.mode & 0o177) !== 0) {
      return emptyResult(target, false, 'insecure_permissions', 'File mode or type changed during read.');
    }
  } catch (err) {
    const reason = err?.code === 'ELOOP' ? 'symlink_rejected' : (err?.code === 'file_too_large' ? 'file_too_large' : 'read_failed');
    return emptyResult(target, false, reason, 'Failed safe bounded read of autopilot-test-env.json.');
  }

  let parsed;
  try { parsed = JSON.parse(raw); } catch { return emptyResult(target, false, 'invalid_json', 'autopilot-test-env.json is not valid JSON.'); }
  if (!isPlainObj(parsed)) return emptyResult(target, false, 'invalid_schema', 'autopilot-test-env.json must contain a JSON object.');

  const accounts = {};
  if (isPlainObj(parsed.accounts)) {
    for (const [acctName, rawVars] of Object.entries(parsed.accounts)) {
      if (PROTO_KEYS.has(acctName) || !ACCOUNT_NAME_RE.test(acctName) || !isPlainObj(rawVars)) continue;
      const cleanVars = {};
      for (const [k, v] of Object.entries(rawVars)) if (isSafeEnvKey(k) && typeof v === 'string') cleanVars[k] = v;
      accounts[acctName] = cleanVars;
    }
  }
  const envVars = {};
  if (isPlainObj(parsed.env)) {
    for (const [k, v] of Object.entries(parsed.env)) if (isSafeEnvKey(k) && typeof v === 'string') envVars[k] = v;
  }
  const extraCapabilities = Array.isArray(parsed.capabilities)
    ? [...new Set(parsed.capabilities.filter((c) => typeof c === 'string' && CAPABILITY_KEY_RE.test(c.trim())).map((c) => c.trim()))].sort()
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
  existsFn = (p) => nativeFs.existsSync(p),
  ttyCheck = null,
} = {}) {
  const caps = new Set();
  if (typeof ttyCheck === 'function' ? Boolean(ttyCheck()) : (Boolean(process.stdout?.isTTY) || existsFn('/dev/tty'))) caps.add('tty');
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
 * Refuses to inject ANY test-env secret unless `reviewApproved === true` and head SHA matches.
 */
export function buildPostReviewSandboxEnv({
  baseEnv = {}, testEnv = null, reviewApproved = false, approvedHead = '', currentHead = '',
  allowedAccounts = [], allowedEnvKeys = [],
} = {}) {
  if (reviewApproved !== true) {
    throw Object.assign(new Error('Refusing test-env secret injection: reviewApproved must be strictly true.'), { code: 'review_not_approved' });
  }
  const ah = String(approvedHead ?? '').trim(), ch = String(currentHead ?? '').trim();
  if ((ah || ch) && ah !== ch) {
    throw Object.assign(new Error('Refusing test-env secret injection: candidate head changed after review approval.'), { code: 'head_mismatch' });
  }
  if (testEnv && testEnv.ok === false) {
    throw Object.assign(new Error(`Refusing test-env secret injection: ${testEnv.reason || 'unsafe test-env'}.`), { code: 'unsafe_test_env' });
  }

  const outEnv = { ...(isPlainObj(baseEnv) ? baseEnv : {}) };
  const injectedKeys = [], injectedSecrets = [];
  const injectPair = (k, v) => {
    if (!isSafeEnvKey(k) || typeof v !== 'string') return;
    outEnv[k] = v;
    injectedKeys.push(k);
    if (v) injectedSecrets.push(v);
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
