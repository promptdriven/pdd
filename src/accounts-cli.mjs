// Generated from prompts/cli/accounts-cli.prompt.md (sha256: d3daa9fb0b86d1f7e07fb0a924836f25f961cf67f13245933563f47c2378e6b0).
import { spawnSync } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { runAgentProcess } from './agent-adapters.mjs';
import {
  CloudAccountsError,
  cloudAccountsRequest,
  leaseCloudAccount,
  localClaudePaths,
  localCodexAuthPath,
  materializeLocalClaudeAuth,
  materializeLocalCodexAuth,
  readCloudAccountsState,
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
      const access = acc.shared
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

export function readCodexFullAuthBundle(fs, env) {
  const authPath = localCodexAuthPath(env);
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

function detectImportProvider(fs, env) {
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

async function runProviderLogin(provider, { cwd, env }, ports = {}) {
  if (typeof ports.runLogin === 'function') {
    return ports.runLogin(provider, { cwd, env });
  }
  const cmd = provider === 'claude' ? 'claude' : 'codex';
  const args = provider === 'claude' ? ['setup-token'] : ['login'];
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
  if (provider === 'codex' && object(leaseReply?.lease?.codex_auth_json)) {
    materializeLocalCodexAuth(leaseReply.lease.codex_auth_json, { env }, ports);
    saveActiveLeaseMetadata(leaseReply, { env }, ports);
    return;
  }
  if (provider === 'claude') {
    const prevManaged = Boolean(saved.active?.claude?.managed_anthropic_base_url);
    const { managedBaseUrl } = materializeLocalClaudeAuth(leaseReply.lease, { env, previousManagedBaseUrl: prevManaged }, ports);
    saveActiveLeaseMetadata(leaseReply, { env, managedBaseUrl }, ports);
  }
}

async function fetchAccountsList({ cwd, env }, ports = {}) {
  const data = await cloudAccountsRequest('GET', '/v1/accounts', { cwd, env }, ports);
  const accounts = Array.isArray(data?.accounts) ? data.accounts : [];
  const pendingInvites = Array.isArray(data?.pending_invites) ? data.pending_invites : [];
  return { accounts, pendingInvites };
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

async function enrollOrImportAccount(mode, { provider: requestedProvider, label: requestedLabel, cwd, env, stdin }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const provider = requestedProvider || (mode === 'import' ? detectImportProvider(fs, env) : 'codex');

  if (provider === 'codex') {
    if (mode === 'add') {
      const loginRes = await runProviderLogin('codex', { cwd, env }, ports);
      if (loginRes && Number.isInteger(loginRes.code) && loginRes.code !== 0) {
        return { exitCode: 1, message: 'codex login did not complete.' };
      }
    }
    const { authJson, bundle } = readCodexFullAuthBundle(fs, env);
    const label = requestedLabel ? sanitizeLabel(requestedLabel, '') : defaultAccountLabel('codex', authJson);
    if (!label) return { exitCode: 2, message: 'Provide a valid --label NAME.' };
    const created = await cloudAccountsRequest('POST', '/v1/accounts', {
      body: {
        label,
        provider: 'codex',
        plan: detectCodexPlan(authJson),
        bundle,
      },
      cwd,
      env,
    }, ports);
    const acc = created?.account ?? { account_id: created?.account_id ?? label, label, provider: 'codex' };
    // Strip local refresh_token immediately so only Cloud refreshes.
    materializeLocalCodexAuth(authJson, { env }, ports);
    try {
      const leased = await leaseCloudAccount({ provider: 'codex', preferredLabel: acc.label, holderId: 'local-cli' }, { cwd, env }, ports);
      if (leased?.state === 'leased') applyMaterializedLease(leased, { env }, ports);
    } catch {
      const current = readCloudAccountsState({ env }, ports);
      writeCloudAccountsState({
        enrolled: true,
        providers: [...new Set([...current.providers, 'codex'])],
        active: {
          ...current.active,
          codex: {
            account_id: acc.account_id,
            label: acc.label ?? label,
            provider: 'codex',
            lease_id: null,
            expires_at: new Date(((ports.now ?? Date.now)()) + 45 * 60 * 1000).toISOString(),
            delivery_mode: 'direct_stripped',
            five_hour_used_percent: acc.five_hour_used_percent ?? 0,
            five_hour_reset_at: acc.five_hour_reset_at ?? null,
            weekly_used_percent: acc.weekly_used_percent ?? 0,
            weekly_reset_at: acc.weekly_reset_at ?? null,
          },
        },
        cooling: current.cooling,
      }, { env }, ports);
    }
    return {
      exitCode: 0,
      message: `Enrolled Codex account "${acc.label ?? label}" in PDD Cloud and stripped the local refresh token.`,
    };
  }

  // Claude enrollment / import
  let loginOutput = '';
  if (mode === 'add') {
    const piped = await readStdinString(stdin);
    if (piped.trim()) {
      loginOutput = piped;
    } else {
      const loginRes = await runProviderLogin('claude', { cwd, env }, ports);
      if (loginRes && Number.isInteger(loginRes.code) && loginRes.code !== 0) {
        return { exitCode: 1, message: 'claude setup-token did not complete.' };
      }
      loginOutput = `${loginRes?.stdout ?? ''}\n${loginRes?.stderr ?? ''}`;
    }
  } else {
    loginOutput = await readStdinString(stdin);
  }
  const oauthToken = readLocalClaudeToken(fs, env, loginOutput);
  const label = requestedLabel ? sanitizeLabel(requestedLabel, '') : defaultAccountLabel('claude');
  if (!label) return { exitCode: 2, message: 'Provide a valid --label NAME.' };
  const created = await cloudAccountsRequest('POST', '/v1/accounts', {
    body: {
      label,
      provider: 'claude',
      plan: 'max',
      bundle: { oauth_token: oauthToken },
    },
    cwd,
    env,
  }, ports);
  const acc = created?.account ?? { account_id: created?.account_id ?? label, label, provider: 'claude' };
  materializeLocalClaudeAuth({ delivery_mode: 'direct_oauth', claude_oauth_token: oauthToken }, { env }, ports);
  try {
    const leased = await leaseCloudAccount({ provider: 'claude', preferredLabel: acc.label, holderId: 'local-cli' }, { cwd, env }, ports);
    if (leased?.state === 'leased') applyMaterializedLease(leased, { env }, ports);
  } catch {
    const current = readCloudAccountsState({ env }, ports);
    writeCloudAccountsState({
      enrolled: true,
      providers: [...new Set([...current.providers, 'claude'])],
      active: {
        ...current.active,
        claude: {
          account_id: acc.account_id,
          label: acc.label ?? label,
          provider: 'claude',
          lease_id: null,
          expires_at: new Date(((ports.now ?? Date.now)()) + 45 * 60 * 1000).toISOString(),
          delivery_mode: 'direct_oauth',
          five_hour_used_percent: acc.five_hour_used_percent ?? 0,
          five_hour_reset_at: acc.five_hour_reset_at ?? null,
          weekly_used_percent: acc.weekly_used_percent ?? 0,
          weekly_reset_at: acc.weekly_reset_at ?? null,
        },
      },
      cooling: current.cooling,
    }, { env }, ports);
  }
  return {
    exitCode: 0,
    message: `Enrolled Claude account "${acc.label ?? label}" in PDD Cloud.`,
  };
}

function hasLocalMaterializedFile(fs, provider, env) {
  try {
    const target = provider === 'claude' ? localClaudePaths(env).settingsPath : localCodexAuthPath(env);
    return Boolean(fs.statSync(target)?.isFile());
  } catch {
    return false;
  }
}

async function runSyncCommand({ provider: requestedProvider, quiet = false, timeoutMs = 1200, cwd, env }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = (ports.now ?? Date.now)();
  const saved = readCloudAccountsState({ env }, ports);
  const providers = requestedProvider
    ? [requestedProvider]
    : (saved.providers.length ? saved.providers : ['codex']);

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
      && hasLocalMaterializedFile(fs, provider, env),
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
        const { accounts, pendingInvites } = await fetchAccountsList({ cwd, env }, ports);
        const current = readCloudAccountsState({ env }, ports);
        const nextActive = { ...current.active };
        for (const acc of accounts) {
          if (nextActive[acc.provider]?.account_id === acc.account_id) {
            nextActive[acc.provider] = {
              ...nextActive[acc.provider],
              label: acc.label ?? acc.account_id,
              five_hour_used_percent: typeof acc.five_hour_used_percent === 'number' ? acc.five_hour_used_percent : nextActive[acc.provider].five_hour_used_percent,
              five_hour_reset_at: acc.five_hour_reset_at ?? nextActive[acc.provider].five_hour_reset_at,
              weekly_used_percent: typeof acc.weekly_used_percent === 'number' ? acc.weekly_used_percent : nextActive[acc.provider].weekly_used_percent,
              weekly_reset_at: acc.weekly_reset_at ?? nextActive[acc.provider].weekly_reset_at,
            };
          }
        }
        const updatedState = writeCloudAccountsState({
          enrolled: accounts.length > 0 || current.enrolled,
          providers: [...new Set(accounts.map(a => a.provider).filter(Boolean))],
          active: nextActive,
          cooling: current.cooling,
        }, { env }, ports);
        if (options['--json'] === true) {
          return {
            exitCode: 0,
            message: redactSecrets(JSON.stringify({ accounts, pending_invites: pendingInvites, active: updatedState.active }, null, 2)),
          };
        }
        return {
          exitCode: 0,
          message: redactSecrets(renderAccountsTable(accounts, pendingInvites, updatedState.active)),
        };
      }

      case 'add':
        return await enrollOrImportAccount('add', {
          provider: options['--provider'],
          label: options['--label'],
          cwd,
          env,
          stdin,
        }, ports);

      case 'import':
        return await enrollOrImportAccount('import', {
          provider: options['--provider'],
          label: options['--label'],
          cwd,
          env,
          stdin,
        }, ports);

      case 'use': {
        const targetLabel = operands[0];
        const { account } = await resolveAccount(targetLabel, { cwd, env }, ports);
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
        const withTarget = typeof options['--with'] === 'string' ? options['--with'].trim() : '';
        if (!withTarget) return { exitCode: 2, message: 'Use pdd accounts share LABEL --with USER|ORG/TEAM.' };
        const { account } = await resolveAccount(operands[0], { cwd, env }, ports);
        let body;
        if (withTarget.includes('/')) {
          const [org, team, extra] = withTarget.split('/');
          if (!org || !team || extra) return { exitCode: 2, message: 'Use ORG/TEAM for team sharing.' };
          body = { org, team };
        } else {
          const resolvedUser = await resolveGitHubUser(withTarget, { cwd, env }, ports);
          body = { github_login: resolvedUser.login };
          if (Number.isSafeInteger(resolvedUser.id)) body.github_user_id = resolvedUser.id;
        }
        const res = await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/share`, { body, cwd, env }, ports);
        const inviteId = res?.invite?.invite_id ?? res?.invite_id ?? null;
        const inviteNote = inviteId ? ` (invite ${inviteId})` : '';
        return { exitCode: 0, message: `Shared "${account.label}" with ${withTarget}${inviteNote}.` };
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
        const provider = res?.account?.provider;
        writeCloudAccountsState({
          ...current,
          enrolled: true,
          providers: provider ? [...new Set([...current.providers, provider])] : current.providers,
        }, { env }, ports);
        return { exitCode: 0, message: `Accepted shared account${res?.account?.label ? ` "${res.account.label}"` : ` invite ${inviteId}`}.` };
      }

      case 'unshare': {
        const user = typeof options['--user'] === 'string' ? options['--user'].trim() : '';
        if (!user) return { exitCode: 2, message: 'Use pdd accounts unshare LABEL --user USER.' };
        const { account } = await resolveAccount(operands[0], { cwd, env }, ports);
        await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/unshare`, {
          body: { github_login: user },
          cwd,
          env,
        }, ports);
        return { exitCode: 0, message: `Revoked "${account.label}" access for ${user}.` };
      }

      case 'leave': {
        const { account } = await resolveAccount(operands[0], { cwd, env }, ports);
        await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/leave`, { body: {}, cwd, env }, ports);
        return { exitCode: 0, message: `Left shared account "${account.label}".` };
      }

      case 'remove': {
        const { account, accounts } = await resolveAccount(operands[0], { cwd, env }, ports);
        await cloudAccountsRequest('DELETE', `/v1/accounts/${encodeURIComponent(account.account_id)}`, { cwd, env }, ports);
        const current = readCloudAccountsState({ env }, ports);
        const nextActive = { ...current.active };
        if (nextActive[account.provider]?.account_id === account.account_id) delete nextActive[account.provider];
        const remaining = accounts.filter(a => a.account_id !== account.account_id);
        writeCloudAccountsState({
          enrolled: remaining.length > 0,
          providers: [...new Set(remaining.map(a => a.provider).filter(Boolean))],
          active: nextActive,
          cooling: current.cooling,
        }, { env }, ports);
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
