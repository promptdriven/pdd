// Generated from prompts/cli/accounts-cli.prompt.md (sha256: 4c4f6470ed343fd1d4be6719948fa7f4ffd0f05c4f4bc6f9d2c15df994399109).
import { spawnSync } from 'node:child_process';
import { createHash, randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { homedir, tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { createInterface } from 'node:readline';
import { runAgentProcess } from './agent-adapters.mjs';
import {
  CloudAccountsError,
  cloudAccountsRequest,
  isCloudAccountsActive,
  leaseCloudAccount,
  listCloudAccounts,
  localClaudePaths,
  localCodexAuthPath,
  localCodexConfigPath,
  localCodexHome,
  materializeLocalClaudeAuth,
  materializeLocalCodexAuth,
  readCloudAccountsState,
  readCodexUsageWindows,
  reportCloudAccountUsage,
  restoreLocalCodexGatewayConfig,
  saveActiveLeaseMetadata,
  writeCloudAccountsState,
} from './login-pool.mjs';
import { knownSecretValues, redactSecrets, rememberSecrets } from './secret-redaction.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const AUTO_BEGIN = '# >>> pdd accounts auto >>>';
const AUTO_END = '# <<< pdd accounts auto <<<';

export function renderAutoSwitchBlock() {
  return [
    AUTO_BEGIN,
    'unalias codex claude 2>/dev/null || true',
    'codex() {',
    '  command -v pdd >/dev/null 2>&1 && pdd accounts sync --provider codex --quiet --timeout-ms 1200 2>/dev/null || true',
    '  command codex "$@"',
    '}',
    'claude() {',
    '  command -v pdd >/dev/null 2>&1 && pdd accounts sync --provider claude --quiet --timeout-ms 1200 2>/dev/null || true',
    '  command claude "$@"',
    '}',
    AUTO_END,
  ].join('\n');
}

const AUTO_BLOCK_RE = /(?:^|\n)# >>> pdd accounts auto >>>[\s\S]*?# <<< pdd accounts auto <<<\n?/g;

export function applyAutoSwitchBlock(existingText = '') {
  const block = `${renderAutoSwitchBlock()}\n`;
  const source = String(existingText ?? '');
  if (source.includes(AUTO_BEGIN) && source.includes(AUTO_END)) {
    return source.replace(/# >>> pdd accounts auto >>>[\s\S]*?# <<< pdd accounts auto <<<\n?/, block);
  }
  if (!source) return block;
  return source.endsWith('\n') ? `${source}\n${block}` : `${source}\n\n${block}`;
}

export function removeAutoSwitchBlock(existingText = '') {
  const source = String(existingText ?? '');
  if (!source.includes(AUTO_BEGIN)) return source;
  let cleaned = source.replace(/\n\n# >>> pdd accounts auto >>>[\s\S]*?# <<< pdd accounts auto <<<\n?/g, '\n');
  cleaned = cleaned.replace(/\n?# >>> pdd accounts auto >>>[\s\S]*?# <<< pdd accounts auto <<<\n?/g, '');
  return cleaned;
}

function shellProfilePaths(env = process.env) {
  const home = env?.HOME || homedir();
  return [join(home, '.zshrc'), join(home, '.bashrc')];
}

function formatShortReset(iso) {
  if (typeof iso !== 'string' || !iso.trim()) return '';
  const ms = Date.parse(iso);
  if (!Number.isFinite(ms)) return iso.slice(0, 19);
  return new Date(ms).toISOString().replace(/:\d{2}(?:\.\d+)?Z$/, 'Z');
}

function formatWindow(pct, resetAt) {
  if (typeof pct !== 'number' || !Number.isFinite(pct)) return '-';
  const rounded = Math.round(pct);
  const reset = formatShortReset(resetAt);
  return reset ? `${rounded}% (${reset})` : `${rounded}%`;
}

function renderAccountsTable(accounts, pendingInvites, activeByProvider) {
  const lines = [];
  if (!accounts.length) {
    lines.push('No Cloud accounts enrolled. Run pdd accounts add or pdd accounts import.');
  } else {
    const rows = accounts.map(acc => {
      const isActive = activeByProvider?.[acc.provider]?.account_id === acc.account_id;
      const isSharedBorrower = typeof acc.is_owner === 'boolean' ? !acc.is_owner : Boolean(acc.shared);
      const access = isSharedBorrower
        ? `shared${acc.owner_login ? ` (${acc.owner_login})` : ''}`
        : `owner${acc.owner_login ? ` (${acc.owner_login})` : ''}`;
      return [
        isActive ? '*' : ' ',
        String(acc.label ?? acc.account_id ?? '-'),
        String(acc.provider ?? '-'),
        access,
        formatWindow(acc.five_hour_used_percent, acc.five_hour_reset_at),
        formatWindow(acc.weekly_used_percent, acc.weekly_reset_at),
        String(acc.state ?? 'ready'),
      ];
    });
    const headers = [' ', 'LABEL', 'PROVIDER', 'ACCESS', '5H', '7D', 'STATE'];
    const widths = headers.map((h, col) => Math.max(h.length, ...rows.map(r => r[col].length)));
    const formatRow = cols => cols.map((val, col) => (col === cols.length - 1 ? val : val.padEnd(widths[col]))).join('  ').trimEnd();
    lines.push(formatRow(headers));
    for (const row of rows) lines.push(formatRow(row));
  }
  if (Array.isArray(pendingInvites) && pendingInvites.length > 0) {
    lines.push('');
    lines.push('Pending share invites:');
    for (const inv of pendingInvites) {
      lines.push(`  ${inv.invite_id}  ${inv.label ?? '-'}  ${inv.provider ?? '-'}  from ${inv.owner_login ?? 'unknown'}  (accept: pdd accounts accept ${inv.invite_id})`);
    }
  }
  return lines.join('\n');
}

function decodeJwtPayload(jwt) {
  if (typeof jwt !== 'string') return null;
  const parts = jwt.split('.');
  if (parts.length < 2) return null;
  try {
    return JSON.parse(Buffer.from(parts[1], 'base64url').toString('utf8'));
  } catch {
    return null;
  }
}

function detectCodexPlan(authJson) {
  const payload = decodeJwtPayload(authJson?.tokens?.id_token) ?? decodeJwtPayload(authJson?.tokens?.access_token);
  const authClaim = payload?.['https://api.openai.com/auth'];
  const plan = authClaim?.chatgpt_plan_type ?? payload?.chatgpt_plan_type ?? authJson?.plan;
  return typeof plan === 'string' && plan.trim() ? plan.trim().toLowerCase() : 'pro';
}

function sanitizeLabel(raw, fallback) {
  const cleaned = String(raw ?? '')
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9._-]+/g, '-')
    .replace(/^-+|-+$/g, '')
    .slice(0, 48);
  return cleaned || fallback;
}

function defaultAccountLabel(provider, authJson = null) {
  if (provider === 'codex') {
    const payload = decodeJwtPayload(authJson?.tokens?.id_token);
    const emailUser = typeof payload?.email === 'string' ? payload.email.split('@')[0] : '';
    if (emailUser) return sanitizeLabel(`codex-${emailUser}`, 'codex-main');
  }
  return `${provider}-main`;
}

async function readStdinString(stdin, { idleTimeoutMs = 50 } = {}) {
  if (typeof stdin === 'string') return stdin;
  if (!stdin || stdin.isTTY || typeof stdin.on !== 'function' || stdin.readableEnded) return '';
  return new Promise(resolve => {
    const chunks = [];
    let gotData = false;
    let timer = null;
    const finish = () => {
      if (timer) clearTimeout(timer);
      stdin.off?.('data', onData);
      stdin.off?.('end', onEnd);
      stdin.off?.('error', onEnd);
      if (stdin === process.stdin && !gotData) stdin.pause?.();
      resolve(Buffer.concat(chunks).toString('utf8'));
    };
    const onData = chunk => {
      gotData = true;
      if (timer) { clearTimeout(timer); timer = null; }
      chunks.push(Buffer.from(chunk));
    };
    const onEnd = () => finish();
    if (stdin === process.stdin && idleTimeoutMs > 0) {
      timer = setTimeout(finish, idleTimeoutMs);
      timer.unref?.();
    }
    stdin.on('data', onData);
    stdin.on('end', onEnd);
    stdin.on('error', onEnd);
    stdin.resume?.();
  });
}

export function readCodexFullAuthBundle(fs, env, explicitAuthPath = null) {
  const authPath = explicitAuthPath || localCodexAuthPath(env);
  let raw;
  try {
    raw = JSON.parse(fs.readFileSync(authPath, 'utf8'));
  } catch {
    throw new CloudAccountsError(`No Codex login found at ${authPath}. Run codex login first.`, { code: 'missing_local_login' });
  }
  rememberSecrets(...knownSecretValues(raw));
  const tokens = raw?.tokens;
  if (!object(tokens)) {
    throw new CloudAccountsError('Local Codex auth.json is missing OAuth tokens (access_token, refresh_token, id_token, account_id). Run codex login first.', { code: 'invalid_local_login' });
  }
  for (const val of Object.values(tokens)) {
    if (typeof val === 'string' && val.length >= 8) rememberSecrets(val);
  }
  const hasAccess = typeof tokens.access_token === 'string' && Boolean(tokens.access_token.trim());
  const hasRefresh = typeof tokens.refresh_token === 'string' && Boolean(tokens.refresh_token.trim());
  if (hasAccess && !hasRefresh) {
    throw new CloudAccountsError('Local Codex auth.json already has a stripped refresh token. Run pdd accounts add --provider codex to sign in fresh.', { code: 'already_stripped' });
  }
  const missing = ['access_token', 'refresh_token', 'id_token', 'account_id'].filter(
    key => typeof tokens[key] !== 'string' || !tokens[key].trim(),
  );
  if (missing.length > 0) {
    throw new CloudAccountsError(
      `Local Codex auth.json is missing required OAuth token field${missing.length > 1 ? 's' : ''}: ${missing.join(', ')}. Run codex login first.`,
      { code: 'invalid_local_login' },
    );
  }
  return {
    authPath,
    authJson: raw,
    bundle: {
      auth_json: {
        OPENAI_API_KEY: raw.OPENAI_API_KEY ?? null,
        tokens: {
          access_token: tokens.access_token.trim(),
          refresh_token: tokens.refresh_token.trim(),
          id_token: tokens.id_token.trim(),
          account_id: tokens.account_id.trim(),
        },
      },
    },
  };
}

function extractClaudeToken(text) {
  const match = /\b(sk-ant-oat[A-Za-z0-9_-]{8,})\b/.exec(String(text ?? ''));
  return match ? match[1] : '';
}

function readLocalClaudeToken(fs, env, extraText = '') {
  const fromExtra = extractClaudeToken(extraText);
  if (fromExtra) { rememberSecrets(fromExtra); return fromExtra; }
  const envTok = typeof env?.CLAUDE_CODE_OAUTH_TOKEN === 'string' ? env.CLAUDE_CODE_OAUTH_TOKEN.trim() : '';
  if (envTok) { rememberSecrets(envTok); return envTok; }
  const { settingsPath } = localClaudePaths(env);
  try {
    const settings = JSON.parse(fs.readFileSync(settingsPath, 'utf8'));
    rememberSecrets(...knownSecretValues(settings));
    const savedTok = typeof settings?.env?.CLAUDE_CODE_OAUTH_TOKEN === 'string' ? settings.env.CLAUDE_CODE_OAUTH_TOKEN.trim() : '';
    if (savedTok) { rememberSecrets(savedTok); return savedTok; }
  } catch {}
  throw new CloudAccountsError('No Claude OAuth token found. Run claude setup-token or pass CLAUDE_CODE_OAUTH_TOKEN.', { code: 'missing_local_login' });
}

function readClaudeTokenFromPath(fs, fromPath) {
  let target = fromPath;
  try {
    if (fs.statSync(fromPath)?.isDirectory()) target = join(fromPath, 'settings.json');
  } catch {}
  let rawText = '';
  try {
    rawText = fs.readFileSync(target, 'utf8');
  } catch {
    throw new CloudAccountsError(`No Claude token file found at ${target}.`, { code: 'missing_local_login' });
  }
  try {
    const parsed = JSON.parse(rawText);
    rememberSecrets(...knownSecretValues(parsed));
    const candidate = parsed?.env?.CLAUDE_CODE_OAUTH_TOKEN ?? parsed?.oauth_token ?? parsed?.claude_oauth_token ?? '';
    if (typeof candidate === 'string' && candidate.trim()) {
      const clean = candidate.trim();
      rememberSecrets(clean);
      return clean;
    }
  } catch {}
  const extracted = extractClaudeToken(rawText) || rawText.trim();
  if (extracted && !/\s/.test(extracted)) {
    rememberSecrets(extracted);
    return extracted;
  }
  throw new CloudAccountsError(`No valid Claude OAuth token found in ${target}.`, { code: 'invalid_local_login' });
}

function resolveCodexImportSource(fs, cwd, env, fromOption) {
  const defaultAuth = localCodexAuthPath(env);
  if (!fromOption) {
    return { authPath: defaultAuth, probeCodexHome: localCodexHome(env), isDefaultLocal: true };
  }
  const resolved = resolve(cwd, String(fromOption).trim());
  let isDir = false;
  try { isDir = Boolean(fs.statSync(resolved)?.isDirectory()); } catch {}
  const authPath = isDir ? join(resolved, 'auth.json') : resolved;
  const isDefaultLocal = resolve(authPath) === resolve(defaultAuth);
  return {
    authPath,
    probeCodexHome: isDir ? resolved : null,
    isDefaultLocal,
  };
}

function detectImportProvider(fs, env, { cwd = process.cwd(), fromOption = null } = {}) {
  if (fromOption) {
    const resolved = resolve(cwd, String(fromOption).trim());
    let candidate = resolved;
    try { if (fs.statSync(resolved)?.isDirectory()) candidate = join(resolved, 'auth.json'); } catch {}
    try {
      const raw = JSON.parse(fs.readFileSync(candidate, 'utf8'));
      if (object(raw?.tokens)) return 'codex';
      if (raw?.env?.CLAUDE_CODE_OAUTH_TOKEN || raw?.oauth_token || raw?.claude_oauth_token) return 'claude';
    } catch {}
    try {
      const txt = fs.readFileSync(resolved, 'utf8');
      if (extractClaudeToken(txt)) return 'claude';
    } catch {}
    return 'codex';
  }
  try {
    const raw = JSON.parse(fs.readFileSync(localCodexAuthPath(env), 'utf8'));
    const t = raw?.tokens;
    if (['access_token', 'refresh_token', 'id_token', 'account_id'].every(k => typeof t?.[k] === 'string' && t[k].trim())) {
      return 'codex';
    }
  } catch {}
  try {
    if (readLocalClaudeToken(fs, env)) return 'claude';
  } catch {}
  return 'codex';
}

function createTempPrivateDir(fs, prefix, tmpRoot) {
  const rootDir = tmpRoot || (fs.existsSync?.('/tmp') !== false ? '/tmp' : tmpdir());
  let dir;
  if (typeof fs.mkdtempSync === 'function') {
    dir = fs.mkdtempSync(join(rootDir, prefix));
  } else if (fs === nativeFs) {
    dir = nativeFs.mkdtempSync(join(rootDir, prefix));
  } else {
    dir = join(rootDir, `${prefix}${randomBytes(8).toString('hex')}`);
    fs.mkdirSync(dir, { recursive: true, mode: 0o700 });
  }
  try { (fs.chmodSync ?? nativeFs.chmodSync)(dir, 0o700); } catch {}
  return dir;
}

function removeTempPrivateDir(fs, dir) {
  if (!dir) return;
  try { (fs.rmSync ?? nativeFs.rmSync)(dir, { recursive: true, force: true }); } catch {}
}

async function runProviderLogin(provider, { cwd, env, deviceAuth = false }, ports = {}) {
  if (typeof ports.runLogin === 'function') {
    return ports.runLogin(provider, { cwd, env, deviceAuth });
  }
  const cmd = provider === 'claude' ? 'claude' : 'codex';
  const args = provider === 'claude'
    ? ['setup-token']
    : ['login', '-c', 'cli_auth_credentials_store="file"', ...(deviceAuth ? ['--device-auth'] : [])];
  if (typeof ports.run === 'function') {
    return ports.run(cmd, args, { cwd, env, input: '', timeoutMs: 120_000, maxBytes: 65_536 });
  }
  if (provider === 'codex' && process.stdin?.isTTY && process.stdout?.isTTY) {
    const res = spawnSync(cmd, args, { cwd, env, stdio: 'inherit' });
    return { code: res.status ?? 1, stdout: '', stderr: '' };
  }
  return runAgentProcess(cmd, args, { cwd, env, input: '', timeoutMs: 120_000, maxBytes: 65_536 });
}

function applyMaterializedLease(leaseReply, { env }, ports = {}) {
  const saved = readCloudAccountsState({ env }, ports);
  const provider = leaseReply?.account?.provider;
  const lease = leaseReply?.lease;
  if (provider === 'codex') {
    const prevCodex = saved.active?.codex;
    const prevManagedGateway = Boolean(prevCodex?.managed_codex_gateway);
    const prevModelProvider = prevCodex?.previous_codex_model_provider ?? null;
    if (lease?.delivery_mode === 'gateway_grant') {
      const mat = materializeLocalCodexAuth(lease, {
        env,
        previousManagedCodexGateway: prevManagedGateway,
        previousCodexModelProvider: prevModelProvider,
      }, ports);
      saveActiveLeaseMetadata(leaseReply, {
        env,
        managedCodexGateway: mat.managedCodexGateway,
        codexGatewayUrl: mat.codexGatewayUrl,
        previousCodexModelProvider: mat.previousCodexModelProvider,
      }, ports);
      return;
    }
    if (object(lease?.codex_auth_json)) {
      materializeLocalCodexAuth(lease.codex_auth_json, {
        env,
        previousManagedCodexGateway: prevManagedGateway,
        previousCodexModelProvider: prevModelProvider,
      }, ports);
      saveActiveLeaseMetadata(leaseReply, {
        env,
        managedCodexGateway: false,
        codexGatewayUrl: null,
        previousCodexModelProvider: null,
      }, ports);
      return;
    }
  }
  if (provider === 'claude') {
    const prevManaged = Boolean(saved.active?.claude?.managed_anthropic_base_url);
    const { managedBaseUrl } = materializeLocalClaudeAuth(lease, { env, previousManagedBaseUrl: prevManaged }, ports);
    saveActiveLeaseMetadata(leaseReply, { env, managedBaseUrl }, ports);
  }
}

async function fetchAccountsList({ cwd, env, refresh = false }, ports = {}) {
  const data = await listCloudAccounts({ refresh, cwd, env }, ports);
  const accounts = Array.isArray(data?.accounts) ? data.accounts : [];
  const pendingInvites = Array.isArray(data?.pending_invites) ? data.pending_invites : [];
  return { accounts, pendingInvites };
}

function isOwnedAccount(acc) {
  if (!acc || acc.revoked) return false;
  if (typeof acc.is_owner === 'boolean') return acc.is_owner === true;
  return acc.shared !== true;
}

const VALID_SLUG_RE = /^[A-Za-z0-9][A-Za-z0-9._-]{0,79}$/;

function parseWithTargets(rawWith) {
  const source = String(rawWith ?? '');
  if (!source.trim()) return { targets: [] };
  const parts = source.split(',');
  const seen = new Set();
  const targets = [];
  for (const rawPart of parts) {
    const item = rawPart.trim();
    if (!item) {
      return { error: 'Share target list contains an empty entry. Pass --with USER|ORG/TEAM[,...].' };
    }
    if (/\s/.test(item)) {
      return { error: `Invalid share target "${item}". Separate multiple targets with commas.` };
    }
    if (item.startsWith('@')) {
      const org = item.slice(1);
      if (!org || org.includes('/') || !VALID_SLUG_RE.test(org)) {
        return { error: `Invalid organization target "${item}". Use @ORG or ORG/TEAM.` };
      }
      const key = `org:${org.toLowerCase()}`;
      if (!seen.has(key)) {
        seen.add(key);
        targets.push({ kind: 'org', raw: item, org });
      }
      continue;
    }
    if (item.includes('/')) {
      const segs = item.split('/');
      const [org, team, extra] = segs;
      if (!org || !team || extra || !VALID_SLUG_RE.test(org) || !VALID_SLUG_RE.test(team)) {
        return { error: 'Use ORG/TEAM for team sharing.' };
      }
      const key = `team:${org.toLowerCase()}/${team.toLowerCase()}`;
      if (!seen.has(key)) {
        seen.add(key);
        targets.push({ kind: 'team', raw: item, org, team });
      }
      continue;
    }
    if (!VALID_SLUG_RE.test(item)) {
      return { error: `Invalid GitHub user target "${item}".` };
    }
    const key = `user:${item.toLowerCase()}`;
    if (!seen.has(key)) {
      seen.add(key);
      targets.push({ kind: 'user', raw: item, login: item });
    }
  }
  return { targets };
}

async function resolveSharePayloads(parsedTargets, { cwd, env }, ports = {}) {
  const payloads = [];
  for (const target of parsedTargets) {
    if (target.kind === 'org') {
      payloads.push({ display: `@${target.org}`, body: { org: target.org } });
    } else if (target.kind === 'team') {
      payloads.push({ display: `${target.org}/${target.team}`, body: { org: target.org, team: target.team } });
    } else {
      const resolved = await resolveGitHubUser(target.login, { cwd, env }, ports);
      const body = { github_login: resolved.login };
      if (Number.isSafeInteger(resolved.id)) body.github_user_id = resolved.id;
      payloads.push({ display: target.raw, body });
    }
  }
  return payloads;
}

async function applySharePayloadsToAccounts(accounts, sharePayloads, { cwd, env }, ports = {}) {
  const notes = [];
  for (const account of accounts) {
    for (const item of sharePayloads) {
      const res = await cloudAccountsRequest(
        'POST',
        `/v1/accounts/${encodeURIComponent(account.account_id)}/share`,
        { body: item.body, cwd, env },
        ports,
      );
      const inviteId = res?.invite?.invite_id ?? res?.invite_id ?? null;
      notes.push({
        label: account.label ?? account.account_id,
        display: item.display,
        inviteId,
      });
    }
  }
  return notes;
}

function buildUnsharePayloads({ userOption, withOption, machineOption }) {
  const seen = new Set();
  const payloads = [];
  const rawUser = typeof userOption === 'string' ? userOption.trim() : '';
  if (rawUser) {
    if (!VALID_SLUG_RE.test(rawUser)) {
      return { error: `Invalid GitHub user "${rawUser}".` };
    }
    const key = `user:${rawUser.toLowerCase()}`;
    seen.add(key);
    payloads.push({ display: rawUser, body: { github_login: rawUser } });
  }
  const rawWith = typeof withOption === 'string' ? withOption : '';
  if (rawWith.trim()) {
    const parsed = parseWithTargets(rawWith);
    if (parsed.error) return { error: parsed.error };
    for (const target of parsed.targets) {
      if (target.kind === 'org') {
        const key = `org:${target.org.toLowerCase()}`;
        if (!seen.has(key)) {
          seen.add(key);
          payloads.push({ display: `@${target.org}`, body: { org: target.org } });
        }
      } else if (target.kind === 'team') {
        const key = `team:${target.org.toLowerCase()}/${target.team.toLowerCase()}`;
        if (!seen.has(key)) {
          seen.add(key);
          payloads.push({ display: `${target.org}/${target.team}`, body: { org: target.org, team: target.team } });
        }
      } else {
        const key = `user:${target.login.toLowerCase()}`;
        if (!seen.has(key)) {
          seen.add(key);
          payloads.push({ display: target.login, body: { github_login: target.login } });
        }
      }
    }
  }
  const rawMachine = typeof machineOption === 'string' ? machineOption.trim() : '';
  if (rawMachine) {
    if (/\s/.test(rawMachine)) {
      return { error: `Invalid machine ID "${rawMachine}".` };
    }
    const key = `machine:${rawMachine}`;
    if (!seen.has(key)) {
      seen.add(key);
      payloads.push({ display: `machine ${rawMachine}`, body: { machine_id: rawMachine } });
    }
  }
  return { payloads };
}

async function probeInitialCodexUsageIfUnpopulated(acc, authJson, probeCodexHome, { fs, cwd, env }, ports = {}) {
  if (!acc?.account_id) return acc;
  const isUnpopulated = (acc.five_hour_used_percent ?? 0) === 0
    && (acc.weekly_used_percent ?? 0) === 0
    && !acc.five_hour_reset_at
    && !acc.weekly_reset_at;
  if (!isUnpopulated) return acc;

  let tempProbeDir = null;
  try {
    let targetHome = probeCodexHome;
    if (!targetHome) {
      tempProbeDir = createTempPrivateDir(fs, 'pdd-cx-probe-', ports.tmpRoot);
      fs.writeFileSync(join(tempProbeDir, 'auth.json'), `${JSON.stringify(authJson, null, 2)}\n`, { mode: 0o600 });
      targetHome = tempProbeDir;
    }
    const probeFn = ports.readCodexUsageWindows ?? readCodexUsageWindows;
    const windows = await probeFn(
      {
        command: 'codex',
        cwd,
        env: { ...env, CODEX_HOME: targetHome },
        weeklyStopPercent: 100,
        timeoutMs: ports.usageProbeTimeoutMs ?? 3000,
      },
      ports.codexLimitPorts,
    );
    const hasFiveH = typeof windows?.five_hour_used_percent === 'number' && Number.isFinite(windows.five_hour_used_percent);
    const hasSevenD = typeof windows?.weekly_used_percent === 'number' && Number.isFinite(windows.weekly_used_percent);
    if (hasFiveH || hasSevenD) {
      const fiveH = hasFiveH ? windows.five_hour_used_percent : 0;
      const sevenD = hasSevenD ? windows.weekly_used_percent : 0;
      const reported = await reportCloudAccountUsage(acc.account_id, {
        five_hour_used_percent: fiveH,
        five_hour_reset_at: windows.five_hour_reset_at ?? null,
        weekly_used_percent: sevenD,
        weekly_reset_at: windows.weekly_reset_at ?? null,
        limit_reached: Boolean(windows.limit_reached || fiveH >= 100 || sevenD >= 100),
      }, { cwd, env, timeoutMs: 3500 }, ports);
      if (object(reported?.account)) return reported.account;
    }
  } catch {} finally {
    removeTempPrivateDir(fs, tempProbeDir);
  }
  return acc;
}

function hashCredentialMaterial(value) {
  return createHash('sha256').update(String(value ?? '')).digest('hex');
}

async function askLoopContinue(question, { stdin, stdout }, ports = {}) {
  const promptFn = ports.prompt ?? ports.confirm ?? null;
  let answer;
  if (typeof promptFn === 'function') {
    try {
      answer = await promptFn(question);
    } catch {
      return false;
    }
  } else {
    const rl = createInterface({ input: stdin, output: stdout });
    try {
      answer = await new Promise(resolveAnswer => {
        let settled = false;
        const finish = val => {
          if (settled) return;
          settled = true;
          resolveAnswer(val);
        };
        rl.once('SIGINT', () => {
          finish(undefined);
          rl.close();
        });
        rl.once('close', () => finish(undefined));
        rl.question(question, val => finish(val));
      });
    } finally {
      rl.close();
    }
  }
  if (answer === undefined || answer === null || answer === false) return false;
  if (answer === true) return true;
  const normalized = String(answer).trim().toLowerCase();
  return normalized === '' || normalized === 'y' || normalized === 'yes';
}

async function resolveAccount(labelOrId, { cwd, env }, ports = {}) {
  const target = String(labelOrId ?? '').trim();
  if (!target) throw new CloudAccountsError('Account label is required.', { code: 'missing_label' });
  const { accounts } = await fetchAccountsList({ cwd, env }, ports);
  const exact = accounts.find(a => a.label === target || a.account_id === target);
  if (exact) return { account: exact, accounts };
  const lower = target.toLowerCase();
  const ciMatches = accounts.filter(a => String(a.label ?? '').toLowerCase() === lower);
  if (ciMatches.length === 1) return { account: ciMatches[0], accounts };
  throw new CloudAccountsError(`Account "${target}" was not found. Run pdd accounts list.`, { code: 'not_found' });
}

async function leaseAndSyncAfterEnroll(provider, acc, fallbackLabel, fallbackAuthJson, fallbackOauthToken, { cwd, env }, ports = {}) {
  try {
    const leased = await leaseCloudAccount({ provider, preferredLabel: acc.label, holderId: 'local-cli' }, { cwd, env }, ports);
    if (leased?.state === 'leased') {
      applyMaterializedLease(leased, { env }, ports);
    } else {
      if (provider === 'codex' && fallbackAuthJson) {
        const saved = readCloudAccountsState({ env }, ports);
        const prevCodex = saved.active?.codex;
        materializeLocalCodexAuth(fallbackAuthJson, {
          env,
          previousManagedCodexGateway: Boolean(prevCodex?.managed_codex_gateway),
          previousCodexModelProvider: prevCodex?.previous_codex_model_provider ?? null,
        }, ports);
      } else if (provider === 'claude' && fallbackOauthToken) {
        materializeLocalClaudeAuth({ delivery_mode: 'direct_oauth', claude_oauth_token: fallbackOauthToken }, { env }, ports);
      }
      const current = readCloudAccountsState({ env }, ports);
      writeCloudAccountsState({
        enrolled: true,
        providers: [...new Set([...current.providers, provider])],
        active: current.active,
        cooling: leased?.state === 'all_cooling'
          ? { ...current.cooling, [provider]: { wake_at: leased.wake_at ?? null } }
          : current.cooling,
      }, { env }, ports);
    }
  } catch {
    if (provider === 'codex' && fallbackAuthJson) {
      const saved = readCloudAccountsState({ env }, ports);
      const prevCodex = saved.active?.codex;
      materializeLocalCodexAuth(fallbackAuthJson, {
        env,
        previousManagedCodexGateway: Boolean(prevCodex?.managed_codex_gateway),
        previousCodexModelProvider: prevCodex?.previous_codex_model_provider ?? null,
      }, ports);
    } else if (provider === 'claude' && fallbackOauthToken) {
      materializeLocalClaudeAuth({ delivery_mode: 'direct_oauth', claude_oauth_token: fallbackOauthToken }, { env }, ports);
    }
    const current = readCloudAccountsState({ env }, ports);
    writeCloudAccountsState({
      enrolled: true,
      providers: [...new Set([...current.providers, provider])],
      active: {
        ...current.active,
        [provider]: {
          account_id: acc.account_id,
          label: acc.label ?? fallbackLabel,
          provider,
          lease_id: null,
          expires_at: new Date(((ports.now ?? Date.now)()) + 45 * 60 * 1000).toISOString(),
          delivery_mode: provider === 'codex' ? 'direct_stripped' : 'direct_oauth',
          five_hour_used_percent: acc.five_hour_used_percent ?? 0,
          five_hour_reset_at: acc.five_hour_reset_at ?? null,
          weekly_used_percent: acc.weekly_used_percent ?? 0,
          weekly_reset_at: acc.weekly_reset_at ?? null,
        },
      },
      cooling: current.cooling,
    }, { env }, ports);
  }
}

async function enrollSingleIteration(mode, {
  provider,
  requestedLabel = null,
  fromOption = null,
  deviceAuth = false,
  sharePayloads = [],
  loopState = null,
  cwd,
  env,
  stdin,
}, ports = {}) {
  const fs = ports.fs ?? nativeFs;

  if (provider === 'codex') {
    let tempLoginDir = null;
    try {
      let authJson;
      let bundle;
      let probeCodexHome = null;
      let shouldStripDefaultLocal = false;

      if (mode === 'add') {
        tempLoginDir = createTempPrivateDir(fs, 'pdd-codex-login-', ports.tmpRoot);
        const loginEnv = { ...env, CODEX_HOME: tempLoginDir };
        const loginRes = await runProviderLogin('codex', { cwd, env: loginEnv, deviceAuth }, ports);
        if (loginRes && Number.isInteger(loginRes.code) && loginRes.code !== 0) {
          return { exitCode: 1, aborted: loginRes.code === 130, message: 'codex login did not complete.' };
        }
        const tempAuthFile = join(tempLoginDir, 'auth.json');
        let hasTempAuth = false;
        try { hasTempAuth = Boolean(fs.statSync(tempAuthFile)?.isFile()); } catch {}
        if (hasTempAuth || typeof ports.runLogin !== 'function') {
          ({ authJson, bundle } = readCodexFullAuthBundle(fs, loginEnv, tempAuthFile));
          probeCodexHome = tempLoginDir;
        } else {
          // Compatibility with unit test runLogin mocks that write directly to HOME/.codex/auth.json.
          ({ authJson, bundle } = readCodexFullAuthBundle(fs, env));
          probeCodexHome = localCodexHome(env);
          shouldStripDefaultLocal = true;
        }
      } else {
        const importSource = resolveCodexImportSource(fs, cwd, env, fromOption);
        ({ authJson, bundle } = readCodexFullAuthBundle(fs, env, importSource.authPath));
        probeCodexHome = importSource.probeCodexHome;
        shouldStripDefaultLocal = importSource.isDefaultLocal;
      }

      const subjectAccountId = bundle.auth_json.tokens.account_id;
      const credHash = hashCredentialMaterial(`${subjectAccountId}:${bundle.auth_json.tokens.refresh_token}`);
      const seenLabel = loopState
        ? (loopState.bySubjectId.get(subjectAccountId) ?? loopState.byFingerprint.get(credHash) ?? null)
        : null;

      let candidateLabel;
      if (loopState) {
        candidateLabel = seenLabel || loopState.peekNextLabel();
      } else {
        candidateLabel = requestedLabel ? sanitizeLabel(requestedLabel, '') : defaultAccountLabel('codex', authJson);
      }
      if (!candidateLabel) return { exitCode: 2, message: 'Provide a valid --label NAME.' };

      const created = await cloudAccountsRequest('POST', '/v1/accounts', {
        body: {
          label: candidateLabel,
          provider: 'codex',
          plan: detectCodexPlan(authJson),
          bundle,
        },
        cwd,
        env,
      }, ports);

      let acc = created?.account ?? { account_id: created?.account_id ?? candidateLabel, label: candidateLabel, provider: 'codex' };
      const isDuplicate = Boolean(
        created?.already_enrolled === true
        || seenLabel
        || (loopState && acc.account_id && loopState.byAccountId.has(acc.account_id)),
      );

      acc = await probeInitialCodexUsageIfUnpopulated(acc, authJson, probeCodexHome, { fs, cwd, env }, ports);

      if (shouldStripDefaultLocal) {
        const saved = readCloudAccountsState({ env }, ports);
        const prevCodex = saved.active?.codex;
        materializeLocalCodexAuth(authJson, {
          env,
          previousManagedCodexGateway: Boolean(prevCodex?.managed_codex_gateway),
          previousCodexModelProvider: prevCodex?.previous_codex_model_provider ?? null,
        }, ports);
      }

      await leaseAndSyncAfterEnroll('codex', acc, candidateLabel, authJson, null, { cwd, env }, ports);

      const finalLabel = acc.label ?? candidateLabel;
      if (loopState) {
        loopState.byFingerprint.set(credHash, finalLabel);
        if (subjectAccountId) loopState.bySubjectId.set(subjectAccountId, finalLabel);
        if (acc.account_id) loopState.byAccountId.set(acc.account_id, finalLabel);
        if (!isDuplicate) loopState.commitCandidateLabel(candidateLabel, finalLabel);
      }

      const shareNotes = sharePayloads.length
        ? await applySharePayloadsToAccounts([acc], sharePayloads, { cwd, env }, ports)
        : [];
      const shareSuffix = shareNotes.length
        ? ` Shared with ${shareNotes.map(n => `${n.display}${n.inviteId ? ` (invite ${n.inviteId})` : ''}`).join(', ')}.`
        : '';

      if (isDuplicate) {
        return {
          exitCode: 0,
          duplicate: true,
          account: acc,
          label: finalLabel,
          shareNotes,
          message: `Already enrolled as ${finalLabel} — refreshed credentials.${shareSuffix}`,
        };
      }
      return {
        exitCode: 0,
        duplicate: false,
        account: acc,
        label: finalLabel,
        shareNotes,
        message: `Enrolled Codex account "${finalLabel}" in PDD Cloud and stripped the local refresh token.${shareSuffix}`,
      };
    } finally {
      removeTempPrivateDir(fs, tempLoginDir);
    }
  }

  // Claude enrollment / import
  let oauthToken = '';
  if (mode === 'add') {
    const piped = !loopState ? await readStdinString(stdin) : '';
    if (piped.trim()) {
      oauthToken = readLocalClaudeToken(fs, env, piped);
    } else {
      const loginRes = await runProviderLogin('claude', { cwd, env, deviceAuth: false }, ports);
      if (loginRes && Number.isInteger(loginRes.code) && loginRes.code !== 0) {
        return { exitCode: 1, aborted: loginRes.code === 130, message: 'claude setup-token did not complete.' };
      }
      const loginOutput = `${loginRes?.stdout ?? ''}\n${loginRes?.stderr ?? ''}`;
      oauthToken = readLocalClaudeToken(fs, env, loginOutput);
    }
  } else if (fromOption) {
    oauthToken = readClaudeTokenFromPath(fs, resolve(cwd, String(fromOption).trim()));
  } else {
    const loginOutput = await readStdinString(stdin);
    oauthToken = readLocalClaudeToken(fs, env, loginOutput);
  }

  const credHash = hashCredentialMaterial(oauthToken);
  const seenLabel = loopState ? (loopState.byFingerprint.get(credHash) ?? null) : null;
  let candidateLabel;
  if (loopState) {
    candidateLabel = seenLabel || loopState.peekNextLabel();
  } else {
    candidateLabel = requestedLabel ? sanitizeLabel(requestedLabel, '') : defaultAccountLabel('claude');
  }
  if (!candidateLabel) return { exitCode: 2, message: 'Provide a valid --label NAME.' };

  const created = await cloudAccountsRequest('POST', '/v1/accounts', {
    body: {
      label: candidateLabel,
      provider: 'claude',
      plan: 'max',
      bundle: { oauth_token: oauthToken },
    },
    cwd,
    env,
  }, ports);
  const acc = created?.account ?? { account_id: created?.account_id ?? candidateLabel, label: candidateLabel, provider: 'claude' };
  const isDuplicate = Boolean(
    created?.already_enrolled === true
    || seenLabel
    || (loopState && acc.account_id && loopState.byAccountId.has(acc.account_id)),
  );

  materializeLocalClaudeAuth({ delivery_mode: 'direct_oauth', claude_oauth_token: oauthToken }, { env }, ports);
  await leaseAndSyncAfterEnroll('claude', acc, candidateLabel, null, oauthToken, { cwd, env }, ports);

  const finalLabel = acc.label ?? candidateLabel;
  if (loopState) {
    loopState.byFingerprint.set(credHash, finalLabel);
    if (acc.account_id) loopState.byAccountId.set(acc.account_id, finalLabel);
    if (!isDuplicate) loopState.commitCandidateLabel(candidateLabel, finalLabel);
  }

  const shareNotes = sharePayloads.length
    ? await applySharePayloadsToAccounts([acc], sharePayloads, { cwd, env }, ports)
    : [];
  const shareSuffix = shareNotes.length
    ? ` Shared with ${shareNotes.map(n => `${n.display}${n.inviteId ? ` (invite ${n.inviteId})` : ''}`).join(', ')}.`
    : '';

  if (isDuplicate) {
    return {
      exitCode: 0,
      duplicate: true,
      account: acc,
      label: finalLabel,
      shareNotes,
      message: `Already enrolled as ${finalLabel} — refreshed credentials.${shareSuffix}`,
    };
  }
  return {
    exitCode: 0,
    duplicate: false,
    account: acc,
    label: finalLabel,
    shareNotes,
    message: `Enrolled Claude account "${finalLabel}" in PDD Cloud.${shareSuffix}`,
  };
}

async function enrollOrImportAccount(mode, {
  provider: requestedProvider,
  label: requestedLabel,
  from: fromOption,
  loop = false,
  deviceAuth = false,
  withTargets: rawWith = '',
  cwd,
  env,
  stdin,
}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const provider = requestedProvider || (mode === 'import' ? detectImportProvider(fs, env, { cwd, fromOption }) : 'codex');

  if (deviceAuth && provider === 'claude') {
    return { exitCode: 2, message: '--device-auth is only supported for Codex accounts.' };
  }

  let sharePayloads = [];
  if (typeof rawWith === 'string' && rawWith.trim()) {
    const parsedWith = parseWithTargets(rawWith);
    if (parsedWith.error) return { exitCode: 2, message: parsedWith.error };
    if (!parsedWith.targets.length) return { exitCode: 2, message: 'Pass at least one target to --with USER|ORG/TEAM[,...].' };
    sharePayloads = await resolveSharePayloads(parsedWith.targets, { cwd, env }, ports);
  }

  if (!loop) {
    const single = await enrollSingleIteration(mode, {
      provider,
      requestedLabel,
      fromOption,
      deviceAuth,
      sharePayloads,
      loopState: null,
      cwd,
      env,
      stdin,
    }, ports);
    return { exitCode: single.exitCode, message: single.message };
  }

  // Interactive --loop enrollment mode
  const promptFn = ports.prompt ?? ports.confirm ?? null;
  const stdout = ports.stdout ?? process.stdout;
  const interactive = Boolean(promptFn) || Boolean(stdin?.isTTY && stdout?.isTTY);
  if (!interactive) {
    return { exitCode: 2, message: 'pdd accounts add --loop requires an interactive terminal.' };
  }
  const prefix = requestedLabel ? sanitizeLabel(requestedLabel, '') : provider;
  if (!prefix) return { exitCode: 2, message: 'Provide a valid --label NAME.' };

  const existingList = await fetchAccountsList({ cwd, env, refresh: false }, ports).catch(() => ({ accounts: [] }));
  const usedLabels = new Set(
    existingList.accounts
      .filter(a => a && !a.revoked)
      .map(a => String(a.label ?? '').toLowerCase())
      .filter(Boolean),
  );
  let counter = 1;
  const loopState = {
    byFingerprint: new Map(),
    bySubjectId: new Map(),
    byAccountId: new Map(),
    peekNextLabel() {
      while (usedLabels.has(`${prefix}-${counter}`.toLowerCase())) counter += 1;
      return `${prefix}-${counter}`;
    },
    commitCandidateLabel(candidate, actual) {
      usedLabels.add(String(candidate).toLowerCase());
      if (actual) usedLabels.add(String(actual).toLowerCase());
      counter += 1;
    },
  };

  const streamedLive = !promptFn && Boolean(stdin?.isTTY && stdout?.isTTY);
  const iterationMessages = [];
  const enrolledLabels = [];
  const refreshedLabels = [];

  for (let iteration = 0; ; iteration += 1) {
    const step = await enrollSingleIteration('add', {
      provider,
      requestedLabel: null,
      fromOption: null,
      deviceAuth,
      sharePayloads,
      loopState,
      cwd,
      env,
      stdin,
    }, ports);

    if (step.exitCode !== 0) {
      if (iteration > 0 && step.aborted) break;
      if (iteration === 0) return { exitCode: step.exitCode, message: step.message };
      iterationMessages.push(step.message);
      break;
    }

    if (step.duplicate) {
      if (!refreshedLabels.includes(step.label) && !enrolledLabels.includes(step.label)) {
        refreshedLabels.push(step.label);
      }
    } else if (!enrolledLabels.includes(step.label)) {
      enrolledLabels.push(step.label);
    }

    if (streamedLive) {
      stdout.write(`${redactSecrets(step.message)}\n`);
    } else {
      iterationMessages.push(step.message);
    }

    const keepGoing = await askLoopContinue(`Enroll another ${provider} account? [Y/n] `, { stdin, stdout }, ports);
    if (!keepGoing) break;
  }

  const shareSummary = sharePayloads.length
    ? `, shared with ${sharePayloads.map(p => p.display).join(', ')}`
    : '';
  const summaryParts = [];
  if (enrolledLabels.length) {
    summaryParts.push(`enrolled ${enrolledLabels.length} ${provider} account${enrolledLabels.length === 1 ? '' : 's'} (${enrolledLabels.join(', ')})`);
  }
  if (refreshedLabels.length) {
    summaryParts.push(`refreshed ${refreshedLabels.length} existing (${refreshedLabels.join(', ')})`);
  }
  const summary = summaryParts.length
    ? `Loop summary: ${summaryParts.join('; ')}${shareSummary}.`
    : `Loop finished with 0 ${provider} accounts enrolled.`;

  const fullOutput = streamedLive ? summary : [...iterationMessages, summary].join('\n');
  return { exitCode: 0, message: redactSecrets(fullOutput) };
}

function hasLocalMaterializedFile(fs, provider, env, cachedEntry = null) {
  try {
    if (provider === 'claude') {
      return Boolean(fs.statSync(localClaudePaths(env).settingsPath)?.isFile());
    }
    const hasAuth = Boolean(fs.statSync(localCodexAuthPath(env))?.isFile());
    if (!hasAuth) return false;
    if (cachedEntry?.managed_codex_gateway === true || cachedEntry?.delivery_mode === 'gateway_grant') {
      return Boolean(fs.statSync(localCodexConfigPath(env))?.isFile());
    }
    return true;
  } catch {
    return false;
  }
}

async function runSyncCommand({ provider: requestedProvider, quiet = false, timeoutMs = 1200, cwd, env }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = (ports.now ?? Date.now)();
  const saved = readCloudAccountsState({ env }, ports);
  let providers = requestedProvider
    ? [requestedProvider]
    : (saved.providers.length ? saved.providers : ['codex']);
  if (quiet) {
    providers = (requestedProvider ? [requestedProvider] : saved.providers)
      .filter(provider => isCloudAccountsActive({ env, provider }, ports));
    if (!providers.length) return { exitCode: 0, message: '' };
  }

  const messages = [];
  for (const provider of providers) {
    const cached = saved.active?.[provider];
    const expiresMs = cached?.expires_at ? Date.parse(cached.expires_at) : NaN;
    const fiveH = cached?.five_hour_used_percent ?? 0;
    const sevenD = cached?.weekly_used_percent ?? 0;
    const validCache = Boolean(
      cached?.account_id
      && Number.isFinite(expiresMs)
      && (expiresMs - now) > 15 * 60 * 1000
      && fiveH < 100
      && sevenD < 100
      && hasLocalMaterializedFile(fs, provider, env, cached),
    );
    if (validCache) {
      if (!quiet) messages.push(`Active ${provider} account "${cached.label}" is fresh.`);
      continue;
    }

    // Fail-open on timeout, offline, or unauthenticated state so plain terminal launches never break.
    try {
      const skip = (fiveH >= 100 || sevenD >= 100) && cached?.account_id ? [cached.account_id] : [];
      const reply = await leaseCloudAccount({
        provider,
        currentAccountId: cached?.account_id ?? null,
        skipAccountIds: skip,
        holderId: 'terminal-sync',
      }, { cwd, env, timeoutMs }, ports);
      if (reply?.state === 'leased') {
        applyMaterializedLease(reply, { env }, ports);
        if (!quiet) messages.push(`Synced ${provider} account "${reply.account?.label ?? reply.account?.account_id}".`);
      } else if (reply?.state === 'all_cooling' && !quiet) {
        messages.push(`All ${provider} accounts are cooling${reply.wake_at ? ` until ${reply.wake_at}` : ''}; keeping current local credentials.`);
      }
    } catch {
      if (!quiet) messages.push(`Cloud sync skipped for ${provider}; keeping current local credentials.`);
    }
  }
  return { exitCode: 0, message: quiet ? '' : messages.join('\n') };
}

function runAutoCommand(mode, { env }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const targets = shellProfilePaths(env);
  if (mode === 'status') {
    const activeFiles = targets.filter(path => {
      try { return fs.readFileSync(path, 'utf8').includes(AUTO_BEGIN); } catch { return false; }
    });
    return {
      exitCode: 0,
      message: activeFiles.length
        ? `Terminal auto-switch: on (${activeFiles.join(', ')}).`
        : 'Terminal auto-switch: off (default).',
    };
  }
  if (mode === 'on') {
    for (const path of targets) {
      let current = '';
      try { current = fs.readFileSync(path, 'utf8'); } catch (err) { if (err?.code !== 'ENOENT') throw err; }
      const updated = applyAutoSwitchBlock(current);
      if (updated !== current) fs.writeFileSync(path, updated, { mode: 0o644 });
    }
    return {
      exitCode: 0,
      message: 'Enabled opt-in terminal auto-switch in ~/.zshrc and ~/.bashrc. Open a new shell or source your profile.',
    };
  }
  if (mode === 'off') {
    for (const path of targets) {
      let current;
      try { current = fs.readFileSync(path, 'utf8'); } catch (err) { if (err?.code === 'ENOENT') continue; throw err; }
      const updated = removeAutoSwitchBlock(current);
      if (updated !== current) fs.writeFileSync(path, updated, { mode: 0o644 });
    }
    return {
      exitCode: 0,
      message: 'Removed terminal auto-switch wrapper from ~/.zshrc and ~/.bashrc.',
    };
  }
  return { exitCode: 2, message: 'Use pdd accounts auto on|off|status.' };
}

async function resolveGitHubUser(login, { cwd, env }, ports = {}) {
  if (typeof ports.resolveGithubUser === 'function') {
    const info = await ports.resolveGithubUser(login, { cwd, env });
    if (info?.type === 'Organization') {
      throw new CloudAccountsError(
        `"${login}" is a GitHub organization. Pass --with ${login}/<team> to share with an organization team.`,
        { code: 'organization_requires_team' },
      );
    }
    if (info?.type && info.type !== 'User') {
      throw new CloudAccountsError(`"${login}" is not a GitHub user account.`, { code: 'invalid_share_target' });
    }
    return { login: info?.login || login, id: Number.isSafeInteger(info?.id) ? info.id : null };
  }
  if (typeof ports.resolveGithubUserId === 'function') {
    const uid = await ports.resolveGithubUserId(login, { cwd, env });
    return { login, id: Number.isSafeInteger(uid) ? uid : null };
  }
  let parsed = null;
  try {
    const runner = ports.run ?? ((c, a, o) => runAgentProcess(c, a, o));
    const ghRes = await runner('gh', ['api', `users/${encodeURIComponent(login)}`], { cwd, env, input: '', timeoutMs: 3000, maxBytes: 65_536 });
    if (ghRes?.code === 0 && ghRes.stdout) {
      parsed = JSON.parse(ghRes.stdout);
    }
  } catch {}
  if (parsed?.type === 'Organization') {
    throw new CloudAccountsError(
      `"${login}" is a GitHub organization. Pass --with ${login}/<team> to share with an organization team.`,
      { code: 'organization_requires_team' },
    );
  }
  if (parsed?.type && parsed.type !== 'User') {
    throw new CloudAccountsError(`"${login}" is not a GitHub user account.`, { code: 'invalid_share_target' });
  }
  return {
    login: typeof parsed?.login === 'string' && parsed.login.trim() ? parsed.login.trim() : login,
    id: Number.isSafeInteger(parsed?.id) ? parsed.id : null,
  };
}

function syncStateAfterAccountRemoval(account, accounts, { env }, ports = {}) {
  const current = readCloudAccountsState({ env }, ports);
  const remaining = accounts.filter(a => a.account_id !== account.account_id && !a.revoked);
  const remainingIds = new Set(remaining.map(a => a.account_id));
  const nextProviders = [...new Set(remaining.map(a => a.provider).filter(Boolean))];
  const nextActive = {};
  for (const [prov, entry] of Object.entries(current.active ?? {})) {
    if (entry?.account_id && entry.account_id !== account.account_id && remainingIds.has(entry.account_id)) {
      nextActive[prov] = entry;
    }
  }
  const prevCodex = current.active?.codex;
  if (prevCodex?.managed_codex_gateway === true && !nextActive.codex?.managed_codex_gateway) {
    restoreLocalCodexGatewayConfig({
      env,
      previousModelProvider: prevCodex.previous_codex_model_provider ?? null,
      removeAuthFile: !nextActive.codex,
    }, ports);
  }
  const nextCooling = Object.fromEntries(
    Object.entries(current.cooling ?? {}).filter(([prov]) => nextProviders.includes(prov)),
  );
  writeCloudAccountsState({
    enrolled: remaining.length > 0,
    providers: nextProviders,
    active: nextActive,
    cooling: nextCooling,
  }, { env }, ports);
}

export async function runAccountsCli({
  commandId = 'accounts',
  operands = [],
  options = {},
  cwd = process.cwd(),
  env = process.env,
  stdin = process.stdin,
} = {}, ports = {}) {
  const sub = commandId === 'accounts' ? 'list' : commandId.slice('accounts.'.length);
  try {
    switch (sub) {
      case 'list': {
        const { accounts, pendingInvites } = await fetchAccountsList({ cwd, env, refresh: true }, ports);
        const current = readCloudAccountsState({ env }, ports);
        const accessible = accounts.filter(a => !a.revoked);
        const validIds = new Set(accessible.map(a => a.account_id).filter(Boolean));
        const nextProviders = [...new Set(accessible.map(a => a.provider).filter(Boolean))];
        const nextActive = {};
        for (const [prov, entry] of Object.entries(current.active ?? {})) {
          if (!validIds.has(entry?.account_id)) continue;
          const acc = accessible.find(a => a.account_id === entry.account_id);
          nextActive[prov] = acc
            ? {
                ...entry,
                label: acc.label ?? acc.account_id,
                five_hour_used_percent: typeof acc.five_hour_used_percent === 'number' ? acc.five_hour_used_percent : entry.five_hour_used_percent,
                five_hour_reset_at: acc.five_hour_reset_at ?? entry.five_hour_reset_at,
                weekly_used_percent: typeof acc.weekly_used_percent === 'number' ? acc.weekly_used_percent : entry.weekly_used_percent,
                weekly_reset_at: acc.weekly_reset_at ?? entry.weekly_reset_at,
              }
            : entry;
        }
        const nextCooling = Object.fromEntries(
          Object.entries(current.cooling ?? {}).filter(([prov]) => nextProviders.includes(prov)),
        );
        const updatedState = writeCloudAccountsState({
          enrolled: accessible.length > 0,
          providers: nextProviders,
          active: nextActive,
          cooling: nextCooling,
        }, { env }, ports);
        if (options['--json'] === true) {
          return {
            exitCode: 0,
            message: redactSecrets(JSON.stringify({ accounts: accessible, pending_invites: pendingInvites, active: updatedState.active }, null, 2)),
          };
        }
        return {
          exitCode: 0,
          message: redactSecrets(renderAccountsTable(accessible, pendingInvites, updatedState.active)),
        };
      }

      case 'add':
        return await enrollOrImportAccount('add', {
          provider: options['--provider'],
          label: options['--label'],
          loop: options['--loop'] === true,
          deviceAuth: options['--device-auth'] === true,
          withTargets: options['--with'] ?? '',
          cwd,
          env,
          stdin,
        }, ports);

      case 'import':
        return await enrollOrImportAccount('import', {
          provider: options['--provider'],
          from: options['--from'] ?? null,
          label: options['--label'],
          withTargets: options['--with'] ?? '',
          cwd,
          env,
          stdin,
        }, ports);

      case 'use': {
        const targetLabel = operands[0];
        const { account, accounts } = await resolveAccount(targetLabel, { cwd, env }, ports);
        const reply = await leaseCloudAccount({
          provider: account.provider,
          preferredLabel: account.label,
          currentAccountId: account.account_id,
          holderId: 'local-cli',
        }, { cwd, env }, ports);
        if (reply?.state === 'all_cooling') {
          return { exitCode: 1, message: `All ${account.provider} accounts are cooling${reply.wake_at ? ` until ${reply.wake_at}` : ''}.` };
        }
        applyMaterializedLease(reply, { env }, ports);
        const synced = readCloudAccountsState({ env }, ports);
        const allProviders = [...new Set(accounts.filter(a => !a.revoked).map(a => a.provider).filter(Boolean))];
        writeCloudAccountsState({
          ...synced,
          enrolled: allProviders.length > 0,
          providers: allProviders,
        }, { env }, ports);
        return { exitCode: 0, message: `Active ${account.provider} account set to "${reply.account?.label ?? account.label}".` };
      }

      case 'next': {
        const saved = readCloudAccountsState({ env }, ports);
        const provider = options['--provider'] || (saved.providers.length === 1 ? saved.providers[0] : 'codex');
        const currentId = saved.active?.[provider]?.account_id ?? null;
        const reply = await leaseCloudAccount({
          provider,
          currentAccountId: currentId,
          skipAccountIds: currentId ? [currentId] : [],
          holderId: 'local-cli',
        }, { cwd, env }, ports);
        if (reply?.state === 'all_cooling') {
          return { exitCode: 1, message: `All ${provider} accounts are cooling${reply.wake_at ? ` until ${reply.wake_at}` : ''}.` };
        }
        applyMaterializedLease(reply, { env }, ports);
        return { exitCode: 0, message: `Switched ${provider} account to "${reply.account?.label ?? reply.account?.account_id}".` };
      }

      case 'sync': {
        const timeoutMs = options['--timeout-ms'] !== undefined ? Number(options['--timeout-ms']) : 1200;
        return await runSyncCommand({
          provider: options['--provider'],
          quiet: options['--quiet'] === true,
          timeoutMs,
          cwd,
          env,
        }, ports);
      }

      case 'auto':
        return runAutoCommand(operands[0], { env }, ports);

      case 'pause': {
        const { account } = await resolveAccount(operands[0], { cwd, env }, ports);
        await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/pause`, { body: {}, cwd, env }, ports);
        return { exitCode: 0, message: `Paused account "${account.label}".` };
      }

      case 'unpause': {
        const { account } = await resolveAccount(operands[0], { cwd, env }, ports);
        await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/unpause`, { body: {}, cwd, env }, ports);
        return { exitCode: 0, message: `Unpaused account "${account.label}".` };
      }

      case 'share': {
        const labelArg = typeof operands[0] === 'string' ? operands[0].trim() : '';
        const allFlag = options['--all'] === true;
        const providerFilter = options['--provider'] || null;
        if (Boolean(labelArg) === allFlag) {
          return { exitCode: 2, message: 'Specify either LABEL or --all on pdd accounts share, not both.' };
        }
        if (!allFlag && providerFilter) {
          return { exitCode: 2, message: '--provider requires --all on pdd accounts share.' };
        }
        const rawWith = typeof options['--with'] === 'string' ? options['--with'] : '';
        const parsedWith = parseWithTargets(rawWith);
        if (parsedWith.error) return { exitCode: 2, message: parsedWith.error };
        if (!parsedWith.targets.length) {
          return { exitCode: 2, message: 'Use pdd accounts share LABEL --with USER|ORG/TEAM[,...] or pdd accounts share --all --with USER|ORG/TEAM[,...].' };
        }
        const sharePayloads = await resolveSharePayloads(parsedWith.targets, { cwd, env }, ports);

        let targetAccounts;
        if (allFlag) {
          const { accounts } = await fetchAccountsList({ cwd, env, refresh: false }, ports);
          targetAccounts = accounts.filter(acc => isOwnedAccount(acc) && (!providerFilter || acc.provider === providerFilter));
          if (!targetAccounts.length) {
            return { exitCode: 1, message: providerFilter ? `No owned ${providerFilter} Cloud accounts found.` : 'No owned Cloud accounts found.' };
          }
        } else {
          const { account } = await resolveAccount(labelArg, { cwd, env }, ports);
          targetAccounts = [account];
        }

        const notes = await applySharePayloadsToAccounts(targetAccounts, sharePayloads, { cwd, env }, ports);
        if (targetAccounts.length === 1 && sharePayloads.length === 1) {
          const inviteNote = notes[0]?.inviteId ? ` (invite ${notes[0].inviteId})` : '';
          return { exitCode: 0, message: `Shared "${targetAccounts[0].label}" with ${notes[0].display}${inviteNote}.` };
        }
        const acctNames = targetAccounts.map(a => `"${a.label}"`).join(', ');
        const targetNames = notes
          .filter((_, idx) => idx < sharePayloads.length)
          .map((n, idx) => {
            const invitesForTarget = notes
              .filter(row => row.display === sharePayloads[idx].display && row.inviteId)
              .map(row => row.inviteId);
            return invitesForTarget.length ? `${n.display} (invite ${invitesForTarget.join(', ')})` : n.display;
          })
          .join(', ');
        return { exitCode: 0, message: `Shared ${acctNames} with ${targetNames}.` };
      }

      case 'accept': {
        const rawInvite = String(operands[0] ?? '').trim();
        let inviteId = rawInvite;
        if (!rawInvite.startsWith('inv_')) {
          const { pendingInvites } = await fetchAccountsList({ cwd, env }, ports);
          const match = pendingInvites.find(inv => inv.invite_id === rawInvite || inv.label === rawInvite || inv.account_id === rawInvite);
          if (match?.invite_id) inviteId = match.invite_id;
        }
        const res = await cloudAccountsRequest('POST', `/v1/accounts/invites/${encodeURIComponent(inviteId)}/accept`, { body: {}, cwd, env }, ports);
        const current = readCloudAccountsState({ env }, ports);
        const acceptedAcc = res?.account ?? null;
        let provider = acceptedAcc?.provider ?? res?.provider ?? null;
        let nextProviders = provider ? [...new Set([...current.providers, provider])] : current.providers;
        if (!provider) {
          const listed = await fetchAccountsList({ cwd, env }, ports).catch(() => null);
          if (listed?.accounts) {
            nextProviders = [...new Set(listed.accounts.filter(a => !a.revoked).map(a => a.provider).filter(Boolean))];
          }
        }
        writeCloudAccountsState({
          ...current,
          enrolled: true,
          providers: nextProviders,
        }, { env }, ports);
        if (provider && !current.active?.[provider]?.account_id) {
          try {
            const leased = await leaseCloudAccount({
              provider,
              preferredLabel: acceptedAcc?.label ?? null,
              currentAccountId: acceptedAcc?.account_id ?? null,
              holderId: 'local-cli',
            }, { cwd, env }, ports);
            if (leased?.state === 'leased') {
              applyMaterializedLease(leased, { env }, ports);
              const refreshed = readCloudAccountsState({ env }, ports);
              writeCloudAccountsState({
                ...refreshed,
                enrolled: true,
                providers: [...new Set([...refreshed.providers, ...nextProviders])],
              }, { env }, ports);
            }
          } catch {}
        }
        return { exitCode: 0, message: `Accepted shared account${acceptedAcc?.label ? ` "${acceptedAcc.label}"` : ` invite ${inviteId}`}.` };
      }

      case 'unshare': {
        const labelArg = typeof operands[0] === 'string' ? operands[0].trim() : '';
        const allFlag = options['--all'] === true;
        const providerFilter = options['--provider'] || null;
        if (Boolean(labelArg) === allFlag) {
          return { exitCode: 2, message: 'Specify either LABEL or --all on pdd accounts unshare, not both.' };
        }
        if (!allFlag && providerFilter) {
          return { exitCode: 2, message: '--provider requires --all on pdd accounts unshare.' };
        }
        const built = buildUnsharePayloads({
          userOption: options['--user'],
          withOption: options['--with'],
          machineOption: options['--machine'],
        });
        if (built.error) return { exitCode: 2, message: built.error };
        if (!built.payloads.length) {
          return { exitCode: 2, message: 'Use pdd accounts unshare LABEL --user USER or pass --with USER|ORG/TEAM[,...] / --machine MACHINE_ID.' };
        }

        let targetAccounts;
        if (allFlag) {
          const { accounts } = await fetchAccountsList({ cwd, env, refresh: false }, ports);
          targetAccounts = accounts.filter(acc => isOwnedAccount(acc) && (!providerFilter || acc.provider === providerFilter));
          if (!targetAccounts.length) {
            return { exitCode: 1, message: providerFilter ? `No owned ${providerFilter} Cloud accounts found.` : 'No owned Cloud accounts found.' };
          }
        } else {
          const { account } = await resolveAccount(labelArg, { cwd, env }, ports);
          targetAccounts = [account];
        }

        for (const account of targetAccounts) {
          for (const item of built.payloads) {
            await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/unshare`, {
              body: item.body,
              cwd,
              env,
            }, ports);
          }
        }

        if (targetAccounts.length === 1 && built.payloads.length === 1) {
          return { exitCode: 0, message: `Revoked "${targetAccounts[0].label}" access for ${built.payloads[0].display}.` };
        }
        const acctNames = targetAccounts.map(a => `"${a.label}"`).join(', ');
        const targetNames = built.payloads.map(p => p.display).join(', ');
        return { exitCode: 0, message: `Revoked ${acctNames} access for ${targetNames}.` };
      }

      case 'leave': {
        const { account, accounts } = await resolveAccount(operands[0], { cwd, env }, ports);
        await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/leave`, { body: {}, cwd, env }, ports);
        syncStateAfterAccountRemoval(account, accounts, { env }, ports);
        return { exitCode: 0, message: `Left shared account "${account.label}".` };
      }

      case 'remove': {
        const { account, accounts } = await resolveAccount(operands[0], { cwd, env }, ports);
        await cloudAccountsRequest('DELETE', `/v1/accounts/${encodeURIComponent(account.account_id)}`, { cwd, env }, ports);
        syncStateAfterAccountRemoval(account, accounts, { env }, ports);
        return { exitCode: 0, message: `Removed account "${account.label}".` };
      }

      case 'log': {
        const { account } = await resolveAccount(operands[0], { cwd, env }, ports);
        const data = await cloudAccountsRequest('GET', `/v1/accounts/${encodeURIComponent(account.account_id)}/log`, { cwd, env }, ports);
        const entries = Array.isArray(data?.entries) ? data.entries : Array.isArray(data?.events) ? data.events : Array.isArray(data?.log) ? data.log : [];
        if (options['--json'] === true) {
          return { exitCode: 0, message: redactSecrets(JSON.stringify({ account_id: account.account_id, label: account.label, entries }, null, 2)) };
        }
        if (!entries.length) return { exitCode: 0, message: `No audit events recorded for "${account.label}".` };
        const lines = entries.map(row => {
          const at = row.created_at ?? row.at ?? row.timestamp ?? '-';
          const event = row.event ?? row.action ?? 'event';
          const actor = row.actor_login ?? row.actor ?? row.machine_label ?? '';
          const detail = row.detail ?? row.note ?? '';
          return `${at}  ${event}${actor ? `  (${actor})` : ''}${detail ? `  ${detail}` : ''}`;
        });
        return { exitCode: 0, message: redactSecrets(lines.join('\n')) };
      }

      default:
        return { exitCode: 2, message: 'Unsupported accounts command. Run pdd accounts --help.' };
    }
  } catch (error) {
    const safeMsg = redactSecrets(error instanceof CloudAccountsError ? error.message : `Accounts command failed: ${error?.message ?? 'unknown error'}`);
    return { exitCode: 1, message: safeMsg };
  }
}
