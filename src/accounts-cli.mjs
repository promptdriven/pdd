// Generated from prompts/cli/accounts-cli.prompt.md (sha256: d317268bc5396e25c3f4780c685f55f9a7880968730938a820b49394ff966212).
import { spawn, spawnSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { homedir, tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { createInterface } from 'node:readline';
import { stripVTControlCharacters } from 'node:util';
import { runAgentProcess } from './agent-adapters.mjs';
import {
  CloudAccountsError,
  cloudAccountsRequest,
  isCloudAccountsActive,
  isLocalReauthUnresolved,
  isReauthRequiredAccount,
  isReauthRequiredFailure,
  leaseCloudAccount,
  listCloudAccounts,
  localClaudePaths,
  localCodexAuthPath,
  localCodexHome,
  managedCodexAuthPath,
  managedCodexConfigPath,
  markLocalAccountReauthRequired,
  materializeLocalClaudeAuth,
  materializeLocalCodexAuth,
  pddManagedCodexHome,
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
const CLAUDE_SETUP_COLUMNS = '500';

export function renderAutoSwitchBlock(shell = 'sh') {
  if (shell === 'fish') {
    return [
      AUTO_BEGIN,
      "functions -e codex claude 2>/dev/null; or true",
      "function codex --wraps codex",
      "  set -l _pdd_mhome \"$HOME/.local/state/pdd/codex-home\"",
      "  if set -q XDG_STATE_HOME; and test -n \"$XDG_STATE_HOME\"",
      "    set _pdd_mhome (string replace -r '/+$' '' -- \"$XDG_STATE_HOME\")\"/pdd/codex-home\"",
      "  end",
      "  if set -q PDD_STATE_DIR; and test -n \"$PDD_STATE_DIR\"",
      "    set _pdd_mhome (string replace -r '/+$' '' -- \"$PDD_STATE_DIR\")\"/codex-home\"",
      "  end",
      "  set _pdd_mhome (string replace -a '/./' '/' -- \"$_pdd_mhome\")",
      "  set -l _pdd_cur_home \"\"",
      "  set -l _pdd_is_mhome 0",
      "  if set -q CODEX_HOME; and test -n \"$CODEX_HOME\"",
      "    set _pdd_cur_home (string replace -a '/./' '/' -- (string replace -r '/+$' '' -- \"$CODEX_HOME\"))",
      "    if test \"$_pdd_cur_home\" = \"$_pdd_mhome\"",
      "      set _pdd_is_mhome 1",
      "    else if test -e \"$_pdd_cur_home\"; and test -e \"$_pdd_mhome\"; and test \"$_pdd_cur_home\" -ef \"$_pdd_mhome\"",
      "      set _pdd_is_mhome 1",
      "    end",
      "  end",
      "  set -l _pdd_sub \"\"",
      "  set -l _pdd_next \"\"",
      "  set -l _pdd_skip 0",
      "  for _pdd_arg in $argv",
      "    if test $_pdd_skip -eq 1",
      "      set _pdd_skip 0",
      "      continue",
      "    end",
      "    if test \"$_pdd_arg\" = \"--\"",
      "      break",
      "    end",
      "    if test -z \"$_pdd_sub\"",
      "      switch \"$_pdd_arg\"",
      "        case -c --config --enable --disable --remote --remote-auth-token-env -i --image -m --model --local-provider -p --profile -s --sandbox -C --cd --add-dir -a --ask-for-approval --color -o --output-last-message",
      "          set _pdd_skip 1",
      "          continue",
      "        case '-*'",
      "          continue",
      "        case logout login",
      "          set _pdd_sub \"$_pdd_arg\"",
      "          continue",
      "        case agents exec e review mcp mcp-server plugin app-server remote-control completion update doctor sandbox debug apply a resume queue archive delete migrate-rollouts unarchive fork cloud exec-server features help",
      "          set _pdd_sub \"$_pdd_arg\"",
      "          break",
      "      end",
      "    else if test -z \"$_pdd_next\"",
      "      switch \"$_pdd_arg\"",
      "        case '-*'",
      "          continue",
      "      end",
      "      set _pdd_next \"$_pdd_arg\"",
      "      break",
      "    end",
      "  end",
      "  if test \"$_pdd_sub\" = \"logout\"; or begin; test \"$_pdd_sub\" = \"login\"; and test \"$_pdd_next\" != \"status\"; end",
      "    if test $_pdd_is_mhome -eq 1",
      "      echo \"pdd accounts: refusing to run 'codex $_pdd_sub' inside PDD-managed CODEX_HOME ($_pdd_mhome) so the Cloud token is not revoked. Use 'pdd accounts pause', 'pdd accounts remove', or 'pdd accounts use' instead (or set -e CODEX_HOME to manage ~/.codex).\" >&2",
      "      return 1",
      "    end",
      "    command codex $argv",
      "    return $status",
      "  end",
      "  if test \"$_pdd_sub\" = \"login\"",
      "    command codex $argv",
      "    return $status",
      "  end",
      "  if test -z \"$_pdd_cur_home\"; or test $_pdd_is_mhome -eq 1",
      "    set -l _pdd_cx_home \"\"",
      "    if command -sq pdd",
      "      set _pdd_cx_home (env PDD_PRINT_CODEX_HOME=1 pdd accounts sync --provider codex --quiet --timeout-ms 1200 2>/dev/null; or true)",
      "    end",
      "    if test -n \"$_pdd_cx_home\"; and test -f \"$_pdd_cx_home/auth.json\"",
      "      CODEX_HOME=\"$_pdd_cx_home\" command codex $argv",
      "      return $status",
      "    end",
      "    if set -q CODEX_HOME",
      "      env -u CODEX_HOME codex $argv",
      "      return $status",
      "    end",
      "  end",
      "  command codex $argv",
      "end",
      "function claude --wraps claude",
      "  command -sq pdd; and pdd accounts sync --provider claude --quiet --timeout-ms 1200 2>/dev/null; or true",
      "  command claude $argv",
      "end",
      AUTO_END,
    ].join('\n');
  }
  return [
    AUTO_BEGIN,
    "unalias codex claude 2>/dev/null || true",
    "codex() {",
    "  local _pdd_mhome=\"$HOME/.local/state/pdd/codex-home\"",
    "  if [ -n \"${XDG_STATE_HOME:-}\" ]; then",
    "    _pdd_mhome=\"${XDG_STATE_HOME%/}/pdd/codex-home\"",
    "  fi",
    "  if [ -n \"${PDD_STATE_DIR:-}\" ]; then",
    "    _pdd_mhome=\"${PDD_STATE_DIR%/}/codex-home\"",
    "  fi",
    "  while [ \"${_pdd_mhome#*/./}\" != \"$_pdd_mhome\" ]; do _pdd_mhome=\"${_pdd_mhome%%/./*}/${_pdd_mhome#*/./}\"; done",
    "  local _pdd_cur_home=\"${CODEX_HOME:-}\" _pdd_is_mhome=0",
    "  while [ -n \"$_pdd_cur_home\" ] && [ \"${_pdd_cur_home%/}\" != \"$_pdd_cur_home\" ]; do _pdd_cur_home=\"${_pdd_cur_home%/}\"; done",
    "  while [ \"${_pdd_cur_home#*/./}\" != \"$_pdd_cur_home\" ]; do _pdd_cur_home=\"${_pdd_cur_home%%/./*}/${_pdd_cur_home#*/./}\"; done",
    "  if [ -n \"$_pdd_cur_home\" ]; then",
    "    if [ \"$_pdd_cur_home\" = \"$_pdd_mhome\" ]; then",
    "      _pdd_is_mhome=1",
    "    elif [ -e \"$_pdd_cur_home\" ] && [ -e \"$_pdd_mhome\" ] && [ \"$_pdd_cur_home\" -ef \"$_pdd_mhome\" ]; then",
    "      _pdd_is_mhome=1",
    "    fi",
    "  fi",
    "  local _pdd_sub=\"\" _pdd_next=\"\" _pdd_skip=0 _pdd_arg",
    "  for _pdd_arg in \"$@\"; do",
    "    if [ \"$_pdd_skip\" -eq 1 ]; then",
    "      _pdd_skip=0",
    "      continue",
    "    fi",
    "    if [ \"$_pdd_arg\" = \"--\" ]; then",
    "      break",
    "    fi",
    "    if [ -z \"$_pdd_sub\" ]; then",
    "      case \"$_pdd_arg\" in",
    "        -c|--config|--enable|--disable|--remote|--remote-auth-token-env|-i|--image|-m|--model|--local-provider|-p|--profile|-s|--sandbox|-C|--cd|--add-dir|-a|--ask-for-approval|--color|-o|--output-last-message)",
    "          _pdd_skip=1",
    "          continue",
    "          ;;",
    "        -*) continue ;;",
    "        logout|login)",
    "          _pdd_sub=\"$_pdd_arg\"",
    "          continue",
    "          ;;",
    "        agents|exec|e|review|mcp|mcp-server|plugin|app-server|remote-control|completion|update|doctor|sandbox|debug|apply|a|resume|queue|archive|delete|migrate-rollouts|unarchive|fork|cloud|exec-server|features|help)",
    "          _pdd_sub=\"$_pdd_arg\"",
    "          break",
    "          ;;",
    "      esac",
    "    elif [ -z \"$_pdd_next\" ]; then",
    "      case \"$_pdd_arg\" in",
    "        -*) continue ;;",
    "      esac",
    "      _pdd_next=\"$_pdd_arg\"",
    "      break",
    "    fi",
    "  done",
    "  if [ \"$_pdd_sub\" = \"logout\" ] || { [ \"$_pdd_sub\" = \"login\" ] && [ \"$_pdd_next\" != \"status\" ]; }; then",
    "    if [ \"$_pdd_is_mhome\" -eq 1 ]; then",
    "      printf '%s\\n' \"pdd accounts: refusing to run 'codex $_pdd_sub' inside PDD-managed CODEX_HOME ($_pdd_mhome) so the Cloud token is not revoked. Use 'pdd accounts pause', 'pdd accounts remove', or 'pdd accounts use' instead (or unset CODEX_HOME to manage ~/.codex).\" >&2",
    "      return 1",
    "    fi",
    "    command codex \"$@\"",
    "    return $?",
    "  fi",
    "  if [ \"$_pdd_sub\" = \"login\" ]; then",
    "    command codex \"$@\"",
    "    return $?",
    "  fi",
    "  if [ -z \"$_pdd_cur_home\" ] || [ \"$_pdd_is_mhome\" -eq 1 ]; then",
    "    local _pdd_cx_home=\"\"",
    "    if command -v pdd >/dev/null 2>&1; then",
    "      _pdd_cx_home=\"$(PDD_PRINT_CODEX_HOME=1 pdd accounts sync --provider codex --quiet --timeout-ms 1200 2>/dev/null || true)\"",
    "    fi",
    "    if [ -n \"$_pdd_cx_home\" ] && [ -f \"$_pdd_cx_home/auth.json\" ]; then",
    "      CODEX_HOME=\"$_pdd_cx_home\" command codex \"$@\"",
    "      return $?",
    "    fi",
    "    if [ -n \"${CODEX_HOME:-}\" ]; then",
    "      (unset CODEX_HOME; command codex \"$@\")",
    "      return $?",
    "    fi",
    "  fi",
    "  command codex \"$@\"",
    "}",
    "claude() {",
    "  command -v pdd >/dev/null 2>&1 && pdd accounts sync --provider claude --quiet --timeout-ms 1200 2>/dev/null || true",
    "  command claude \"$@\"",
    "}",
    AUTO_END,
  ].join('\n');
}

export function applyAutoSwitchBlock(existingText = '', shell = 'sh') {
  const block = `${renderAutoSwitchBlock(shell)}\n`;
  const source = String(existingText ?? '');
  if (source.includes(AUTO_BEGIN) && source.includes(AUTO_END)) {
    return source.replace(/# >>> pdd accounts auto >>>[\s\S]*?# <<< pdd accounts auto <<<\n?/, () => block);
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

function shellProfileEntries(env = process.env) {
  const home = env?.HOME || homedir();
  const xdgConfig = (typeof env?.XDG_CONFIG_HOME === 'string' && env.XDG_CONFIG_HOME.trim())
    ? env.XDG_CONFIG_HOME.trim()
    : join(home, '.config');
  return [
    { path: join(home, '.zshrc'), shell: 'zsh' },
    { path: join(home, '.bashrc'), shell: 'bash' },
    { path: join(xdgConfig, 'fish', 'config.fish'), shell: 'fish' },
  ];
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

function hasUnresolvedLocalReauth(acc, activeEntry = null, localReauth = null) {
  const accId = acc?.account_id;
  if (!accId) return false;
  const refreshedIso = acc?.last_refresh_at ?? acc?.refreshed_at ?? null;
  if (isLocalReauthUnresolved(accId, refreshedIso, localReauth)) return true;
  if (object(localReauth) && object(localReauth[accId])) return false;
  if (activeEntry?.account_id === accId && activeEntry?.state === 'reauth_required') {
    const refreshedMs = refreshedIso ? Date.parse(refreshedIso) : NaN;
    const leasedMs = activeEntry.leased_at ? Date.parse(activeEntry.leased_at) : NaN;
    if (Number.isFinite(refreshedMs) && Number.isFinite(leasedMs) && refreshedMs > leasedMs) {
      return false;
    }
    return true;
  }
  return false;
}

function accountDisplayState(acc, activeEntry = null, localReauth = null) {
  if (isReauthRequiredAccount(acc)) return 'reauth_required';
  const rawState = typeof acc?.state === 'string' && acc.state.trim() ? acc.state.trim() : '';
  if (rawState && rawState !== 'ready') return rawState;
  if (hasUnresolvedLocalReauth(acc, activeEntry, localReauth)) {
    return 'reauth_required';
  }
  return rawState || 'ready';
}

function formatRefreshColumn(acc, activeEntry, nowMs = Date.now()) {
  const state = accountDisplayState(acc, activeEntry);
  if (state === 'reauth_required') return 'reauth required';
  const isSameActive = Boolean(activeEntry?.account_id && activeEntry.account_id === acc?.account_id);
  const lastRefresh = acc?.last_refresh_at
    ?? acc?.refreshed_at
    ?? (isSameActive ? activeEntry?.last_refresh_at : null)
    ?? null;
  const expiresAt = acc?.access_token_expires_at
    ?? (isSameActive ? (activeEntry?.access_token_expires_at ?? activeEntry?.expires_at) : null)
    ?? null;
  const refShort = formatShortReset(lastRefresh);
  const expShort = formatShortReset(expiresAt);
  const expMs = expiresAt ? Date.parse(expiresAt) : NaN;
  const expPart = expShort
    ? (Number.isFinite(expMs) && expMs <= nowMs ? `expired ${expShort}` : `exp ${expShort}`)
    : '';
  if (refShort && expPart) return `refreshed ${refShort} (${expPart})`;
  if (refShort) return `refreshed ${refShort}`;
  if (expPart) return expPart;
  return '-';
}

function renderAccountsTable(accounts, pendingInvites, activeByProvider, nowMs = Date.now()) {
  const lines = [];
  const reauthAccounts = [];
  if (!accounts.length) {
    lines.push('No Cloud accounts enrolled. Run pdd accounts add or pdd accounts import.');
  } else {
    const rows = accounts.map(acc => {
      const activeEntry = activeByProvider?.[acc.provider] ?? null;
      const isActive = activeEntry?.account_id === acc.account_id;
      const isSharedBorrower = typeof acc.is_owner === 'boolean' ? !acc.is_owner : Boolean(acc.shared);
      const access = isSharedBorrower
        ? `shared${acc.owner_login ? ` (${acc.owner_login})` : ''}`
        : `owner${acc.owner_login ? ` (${acc.owner_login})` : ''}`;
      const dispState = accountDisplayState(acc, activeEntry);
      if (dispState === 'reauth_required') reauthAccounts.push(acc);
      return [
        isActive ? '*' : ' ',
        String(acc.label ?? acc.account_id ?? '-'),
        String(acc.provider ?? '-'),
        access,
        formatWindow(acc.five_hour_used_percent, acc.five_hour_reset_at),
        formatWindow(acc.weekly_used_percent, acc.weekly_reset_at),
        dispState,
        formatRefreshColumn(acc, activeEntry, nowMs),
      ];
    });
    const headers = [' ', 'LABEL', 'PROVIDER', 'ACCESS', '5H', '7D', 'STATE', 'REFRESH'];
    const widths = headers.map((h, col) => Math.max(h.length, ...rows.map(r => r[col].length)));
    const formatRow = cols => cols.map((val, col) => (col === cols.length - 1 ? val : val.padEnd(widths[col]))).join('  ').trimEnd();
    lines.push(formatRow(headers));
    for (const row of rows) lines.push(formatRow(row));
    if (reauthAccounts.length > 0) {
      lines.push('');
      for (const acc of reauthAccounts) {
        lines.push(`Re-authentication required for "${acc.label ?? acc.account_id}": run pdd accounts add --provider ${acc.provider ?? 'codex'} --label ${acc.label ?? acc.account_id}`);
      }
    }
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

function formatExpiryRemaining(iso, nowMs) {
  if (typeof iso !== 'string' || !iso.trim()) return 'unknown';
  const expMs = Date.parse(iso);
  if (!Number.isFinite(expMs)) return iso;
  const diffMin = Math.round((expMs - nowMs) / 60_000);
  const short = formatShortReset(iso);
  if (diffMin <= 0) return `expired (${short})`;
  return `valid (${diffMin}m remaining, ${short})`;
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

function extractClaudeSetupToken(stdout) {
  const lines = stripVTControlCharacters(stdout ?? '').split(/\r?\n/).map(line => line.trimEnd());
  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    const match = /\bsk-ant-oat[A-Za-z0-9_-]*/.exec(line);
    if (!match) continue;
    let token = match[0];
    if (match.index + token.length === line.length) {
      let width = line.length;
      for (let next = index + 1; width === 80 || width === Number(CLAUDE_SETUP_COLUMNS); next += 1) {
        const continuation = lines[next]?.trim();
        if (!continuation || !/^[A-Za-z0-9_-]+$/.test(continuation)) break;
        token += continuation;
        width = lines[next].length;
      }
    }
    if (/^sk-ant-oat[A-Za-z0-9_-]{8,}$/.test(token)) return token;
  }
  return '';
}

function rememberCodexPayloadSecrets(raw) {
  if (!object(raw)) return;
  rememberSecrets(...knownSecretValues(raw));
  if (object(raw.tokens)) {
    for (const val of Object.values(raw.tokens)) {
      if (typeof val === 'string' && val.length >= 8) rememberSecrets(val);
    }
  }
}

function rememberClaudePayloadSecrets(parsed) {
  if (!object(parsed)) return;
  rememberSecrets(...knownSecretValues(parsed));
  if (object(parsed.env)) {
    rememberSecrets(...knownSecretValues(parsed.env));
  }
  for (const key of ['oauth_token', 'claude_oauth_token']) {
    if (typeof parsed[key] === 'string' && parsed[key].trim()) {
      rememberSecrets(parsed[key], parsed[key].trim());
    }
  }
  if (object(parsed.claudeAiOauth)) {
    rememberSecrets(...knownSecretValues(parsed.claudeAiOauth));
    for (const [key, val] of Object.entries(parsed.claudeAiOauth)) {
      if (typeof val === 'string' && val.trim() && (/token|secret|key|credential/i.test(key) || val.trim().startsWith('sk-'))) {
        rememberSecrets(val, val.trim());
      }
    }
  }
}

function parseClaudeExpiresAtMs(expiresAt) {
  if (typeof expiresAt === 'number') return expiresAt;
  if (typeof expiresAt === 'string') {
    const trimmed = expiresAt.trim();
    if (!trimmed) return null;
    if (/^-?\d+(?:\.\d+)?$/.test(trimmed)) return Number(trimmed);
    return Date.parse(trimmed);
  }
  return NaN;
}

function parseClaudeTokenText(rawText, target, nowMs, { allowBareToken = true } = {}) {
  let parsed = null;
  let isJson = false;
  try {
    parsed = JSON.parse(rawText);
    isJson = true;
  } catch {}

  if (isJson) {
    rememberClaudePayloadSecrets(parsed);
    if (object(parsed)) {
      const candidate = parsed?.env?.CLAUDE_CODE_OAUTH_TOKEN ?? parsed?.oauth_token ?? parsed?.claude_oauth_token ?? '';
      if (typeof candidate === 'string' && candidate.trim() && !/\s/.test(candidate.trim())) {
        const clean = candidate.trim();
        rememberSecrets(clean);
        return clean;
      }
      if (object(parsed.claudeAiOauth)) {
        const oauth = parsed.claudeAiOauth;
        const rawExpiresAt = oauth.expiresAt;
        const hasExpiresAt = rawExpiresAt !== undefined
          && rawExpiresAt !== null
          && !(typeof rawExpiresAt === 'string' && !rawExpiresAt.trim());
        if (hasExpiresAt) {
          const expMs = parseClaudeExpiresAtMs(rawExpiresAt);
          if (!Number.isFinite(expMs) || expMs <= nowMs + 60_000) {
            throw new CloudAccountsError(
              `${target} contains an expired short-lived Claude OAuth access token. Run pdd accounts add --provider claude or claude setup-token.`,
              { code: 'expired_local_login' },
            );
          }
        }
        const accessToken = typeof oauth.accessToken === 'string' ? oauth.accessToken.trim() : '';
        if (accessToken && !/\s/.test(accessToken)) {
          rememberSecrets(accessToken);
          return accessToken;
        }
        return '';
      }
      const extractedFromJson = extractClaudeToken(rawText);
      if (extractedFromJson) {
        rememberSecrets(extractedFromJson);
        return extractedFromJson;
      }
      return '';
    }
    if (typeof parsed === 'string') {
      const strCandidate = extractClaudeToken(parsed) || (allowBareToken ? parsed.trim() : '');
      if (strCandidate && !/\s/.test(strCandidate)) {
        rememberSecrets(strCandidate);
        return strCandidate;
      }
    }
    return '';
  }

  const extracted = extractClaudeToken(rawText) || (allowBareToken ? rawText.trim() : '');
  if (extracted && !/\s/.test(extracted)) {
    rememberSecrets(extracted);
    return extracted;
  }
  return '';
}

function hasClaudeJsonCredentials(raw) {
  if (!object(raw)) return false;
  if (typeof raw?.env?.CLAUDE_CODE_OAUTH_TOKEN === 'string' && raw.env.CLAUDE_CODE_OAUTH_TOKEN.trim()) return true;
  if (typeof raw?.oauth_token === 'string' && raw.oauth_token.trim()) return true;
  if (typeof raw?.claude_oauth_token === 'string' && raw.claude_oauth_token.trim()) return true;
  if (object(raw?.claudeAiOauth)) {
    const oauth = raw.claudeAiOauth;
    if (
      (typeof oauth.accessToken === 'string' && oauth.accessToken.trim())
      || oauth.expiresAt !== undefined
      || (typeof oauth.refreshToken === 'string' && oauth.refreshToken.trim())
    ) {
      return true;
    }
  }
  return false;
}

export function readLocalClaudeToken(fs, env, extraText = '', options = {}) {
  const nowMs = (typeof options?.now === 'function' ? options.now : Date.now)();
  if (typeof extraText === 'string' && extraText.trim()) {
    const fromExtra = parseClaudeTokenText(extraText, 'stdin', nowMs, { allowBareToken: false });
    if (fromExtra) return fromExtra;
  }
  const envTok = typeof env?.CLAUDE_CODE_OAUTH_TOKEN === 'string' ? env.CLAUDE_CODE_OAUTH_TOKEN.trim() : '';
  if (envTok) { rememberSecrets(envTok); return envTok; }
  const { settingsPath } = localClaudePaths(env);
  try {
    const settingsRaw = fs.readFileSync(settingsPath, 'utf8');
    const savedTok = parseClaudeTokenText(settingsRaw, settingsPath, nowMs, { allowBareToken: false });
    if (savedTok) return savedTok;
  } catch (err) {
    if (err instanceof CloudAccountsError) throw err;
  }
  const credentialsPath = join(dirname(settingsPath), '.credentials.json');
  try {
    const credsRaw = fs.readFileSync(credentialsPath, 'utf8');
    const credsTok = parseClaudeTokenText(credsRaw, credentialsPath, nowMs, { allowBareToken: false });
    if (credsTok) return credsTok;
  } catch (err) {
    if (err instanceof CloudAccountsError) throw err;
  }
  throw new CloudAccountsError('No Claude OAuth token found. Run pdd accounts add --provider claude or claude setup-token, or pass CLAUDE_CODE_OAUTH_TOKEN.', { code: 'missing_local_login' });
}

export function readClaudeTokenFromPath(fs, fromPath, options = {}) {
  const nowMs = (typeof options?.now === 'function' ? options.now : Date.now)();
  let isDir = false;
  try {
    isDir = Boolean(fs.statSync(fromPath)?.isDirectory());
  } catch {}
  if (isDir) {
    const settingsPath = join(fromPath, 'settings.json');
    const credentialsPath = join(fromPath, '.credentials.json');
    let foundAnyFile = false;
    let lastExistingPath = settingsPath;
    try {
      const settingsRaw = fs.readFileSync(settingsPath, 'utf8');
      foundAnyFile = true;
      lastExistingPath = settingsPath;
      const fromSettings = parseClaudeTokenText(settingsRaw, settingsPath, nowMs, { allowBareToken: false });
      if (fromSettings) return fromSettings;
    } catch (err) {
      if (err instanceof CloudAccountsError) throw err;
    }
    try {
      const credsRaw = fs.readFileSync(credentialsPath, 'utf8');
      foundAnyFile = true;
      lastExistingPath = credentialsPath;
      const fromCreds = parseClaudeTokenText(credsRaw, credentialsPath, nowMs, { allowBareToken: false });
      if (fromCreds) return fromCreds;
    } catch (err) {
      if (err instanceof CloudAccountsError) throw err;
    }
    if (!foundAnyFile) {
      throw new CloudAccountsError(`No Claude token file found at ${settingsPath} or ${credentialsPath}.`, { code: 'missing_local_login' });
    }
    throw new CloudAccountsError(`No valid Claude OAuth token found in ${lastExistingPath}.`, { code: 'invalid_local_login' });
  }
  let rawText = '';
  try {
    rawText = fs.readFileSync(fromPath, 'utf8');
  } catch {
    throw new CloudAccountsError(`No Claude token file found at ${fromPath}.`, { code: 'missing_local_login' });
  }
  const token = parseClaudeTokenText(rawText, fromPath, nowMs, { allowBareToken: true });
  if (token) return token;
  throw new CloudAccountsError(`No valid Claude OAuth token found in ${fromPath}.`, { code: 'invalid_local_login' });
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

export function detectImportProvider(fs, env = process.env, options = {}) {
  const cwd = options?.cwd ?? process.cwd();
  const fromOption = options?.fromOption ?? options?.from ?? null;
  const now = typeof options?.now === 'function' ? options.now : Date.now;
  if (fromOption) {
    const resolved = resolve(cwd, String(fromOption).trim());
    let isDir = false;
    try { isDir = Boolean(fs.statSync(resolved)?.isDirectory()); } catch {}
    if (isDir) {
      try {
        const raw = JSON.parse(fs.readFileSync(join(resolved, 'auth.json'), 'utf8'));
        rememberCodexPayloadSecrets(raw);
        if (object(raw?.tokens)) return 'codex';
      } catch {}
      for (const fileName of ['settings.json', '.credentials.json']) {
        try {
          const txt = fs.readFileSync(join(resolved, fileName), 'utf8');
          try {
            const raw = JSON.parse(txt);
            rememberClaudePayloadSecrets(raw);
            if (hasClaudeJsonCredentials(raw)) return 'claude';
          } catch {}
          const extracted = extractClaudeToken(txt);
          if (extracted) {
            rememberSecrets(extracted);
            return 'claude';
          }
        } catch {}
      }
      return 'codex';
    }
    try {
      const txt = fs.readFileSync(resolved, 'utf8');
      try {
        const raw = JSON.parse(txt);
        rememberCodexPayloadSecrets(raw);
        rememberClaudePayloadSecrets(raw);
        if (object(raw?.tokens)) return 'codex';
        if (hasClaudeJsonCredentials(raw)) return 'claude';
      } catch {}
      const extracted = extractClaudeToken(txt);
      if (extracted) {
        rememberSecrets(extracted);
        return 'claude';
      }
    } catch {}
    return 'codex';
  }
  try {
    const raw = JSON.parse(fs.readFileSync(localCodexAuthPath(env), 'utf8'));
    rememberCodexPayloadSecrets(raw);
    const t = raw?.tokens;
    if (['access_token', 'refresh_token', 'id_token', 'account_id'].every(k => typeof t?.[k] === 'string' && t[k].trim())) {
      return 'codex';
    }
  } catch {}
  try {
    if (readLocalClaudeToken(fs, env, '', { now })) return 'claude';
  } catch (err) {
    if (err?.code === 'expired_local_login') return 'claude';
  }
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

function runInteractiveClaudeLogin(cmd, args, { cwd, env, stdin, stdout }) {
  return new Promise((resolve, reject) => {
    const child = spawn(cmd, args, { cwd, env, stdio: [stdin, 'pipe', 'pipe'] });
    let captured = '';
    let interrupted = false;
    const interrupt = () => {
      interrupted = true;
      child.kill('SIGINT');
    };
    process.on('SIGINT', interrupt);
    child.stdout.setEncoding('utf8');
    child.stdout.on('data', chunk => { captured += chunk; });
    child.stdout.pipe(stdout, { end: false });
    child.stderr.pipe(process.stderr.isTTY ? process.stderr : stdout, { end: false });
    child.once('error', reject);
    child.once('close', (code, signal) => {
      process.off('SIGINT', interrupt);
      resolve({ code: interrupted ? 130 : code, signal, stdout: captured });
    });
  });
}

async function runProviderLogin(provider, { cwd, env, stdin, deviceAuth = false }, ports = {}) {
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
    return {
      code: res.signal === 'SIGINT' ? 130 : (res.status ?? 1),
      signal: res.signal ?? null,
      stdout: '',
      stderr: '',
    };
  }
  const stdout = ports.stdout ?? process.stdout;
  if (provider === 'claude' && stdin?.isTTY && stdout?.isTTY) {
    return runInteractiveClaudeLogin(cmd, args, { cwd, env, stdin, stdout });
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
        materializedLocal: true,
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
        materializedLocal: true,
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
    saveActiveLeaseMetadata(leaseReply, { env, materializedLocal: true, managedBaseUrl }, ports);
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

function buildUnsharePayloads({ userOption, withOption }) {
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
  const sanitized = sanitizeLabel(target, '');
  if (sanitized) {
    const sanitizedMatches = accounts.filter(a => {
      const accLabel = String(a.label ?? '');
      return accLabel.toLowerCase() === sanitized || sanitizeLabel(accLabel, '') === sanitized;
    });
    if (sanitizedMatches.length === 1) return { account: sanitizedMatches[0], accounts };
  }
  throw new CloudAccountsError(`Account "${target}" was not found. Run pdd accounts list.`, { code: 'not_found' });
}

async function leaseAndSyncAfterEnroll(provider, acc, fallbackLabel, fallbackAuthJson, fallbackOauthToken, { cwd, env }, ports = {}) {
  const nowMs = (ports.now ?? Date.now)();
  if (acc?.account_id) {
    const preEnrollState = readCloudAccountsState({ env }, ports);
    if (preEnrollState.reauth?.[acc.account_id]) {
      const cleanedReauth = { ...preEnrollState.reauth };
      delete cleanedReauth[acc.account_id];
      writeCloudAccountsState({ ...preEnrollState, reauth: cleanedReauth }, { env }, ports);
    }
  }
  try {
    const leased = await leaseCloudAccount({ provider, preferredLabel: acc.label, holderId: 'local-cli', updateState: false }, { cwd, env }, ports);
    if (leased?.state === 'leased' && !isReauthRequiredAccount(leased.account)) {
      applyMaterializedLease(leased, { env }, ports);
    } else if (leased?.state === 'leased' && isReauthRequiredAccount(leased.account)) {
      markLocalAccountReauthRequired(leased.account?.account_id ?? acc.account_id, { env }, ports);
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
          state: accountDisplayState(acc),
          lease_id: null,
          leased_at: new Date(nowMs).toISOString(),
          expires_at: new Date(nowMs + 45 * 60 * 1000).toISOString(),
          last_refresh_at: acc.last_refresh_at ?? fallbackAuthJson?.last_refresh ?? new Date(nowMs).toISOString(),
          materialized_local: true,
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

      if (mode === 'add') {
        tempLoginDir = createTempPrivateDir(fs, 'pdd-codex-login-', ports.tmpRoot);
        const loginEnv = { ...env, CODEX_HOME: tempLoginDir };
        const loginRes = await runProviderLogin('codex', { cwd, env: loginEnv, deviceAuth }, ports);
        if (!loginRes || loginRes.code !== 0) {
          return {
            exitCode: 1,
            aborted: loginRes?.code === 130 || loginRes?.signal === 'SIGINT',
            message: 'codex login did not complete.',
          };
        }
        const tempAuthFile = join(tempLoginDir, 'auth.json');
        ({ authJson, bundle } = readCodexFullAuthBundle(fs, loginEnv, tempAuthFile));
        probeCodexHome = tempLoginDir;
      } else {
        const importSource = resolveCodexImportSource(fs, cwd, env, fromOption);
        ({ authJson, bundle } = readCodexFullAuthBundle(fs, env, importSource.authPath));
        probeCodexHome = importSource.probeCodexHome;
      }

      const subjectAccountId = bundle.auth_json.tokens.account_id;
      const seenLabel = loopState ? (loopState.bySubjectId.get(subjectAccountId) ?? null) : null;

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
        || (loopState && acc.account_id && loopState.seenAccountIds.has(acc.account_id)),
      );

      acc = await probeInitialCodexUsageIfUnpopulated(acc, authJson, probeCodexHome, { fs, cwd, env }, ports);

      await leaseAndSyncAfterEnroll('codex', acc, candidateLabel, authJson, null, { cwd, env }, ports);

      const finalLabel = acc.label ?? candidateLabel;
      if (loopState) {
        if (subjectAccountId) loopState.bySubjectId.set(subjectAccountId, finalLabel);
        if (acc.account_id) loopState.seenAccountIds.add(acc.account_id);
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
      const importNote = (mode === 'import' && !fromOption)
        ? ' (~/.codex/auth.json was left untouched; prefer "pdd accounts add --provider codex" so Cloud uses an independent OAuth session.)'
        : '';
      return {
        exitCode: 0,
        duplicate: false,
        account: acc,
        label: finalLabel,
        shareNotes,
        message: `Enrolled Codex account "${finalLabel}" in PDD Cloud (materialized in ${pddManagedCodexHome(env)}).${shareSuffix}${importNote}`,
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
      oauthToken = readLocalClaudeToken(fs, env, piped, { now: ports.now });
    } else {
      const tempLoginDir = createTempPrivateDir(fs, 'pdd-claude-login-', ports.tmpRoot);
      const loginEnv = { ...env, CLAUDE_CONFIG_DIR: tempLoginDir, COLUMNS: CLAUDE_SETUP_COLUMNS };
      delete loginEnv.CLAUDE_CODE_OAUTH_TOKEN;
      let loginRes;
      try {
        loginRes = await runProviderLogin('claude', { cwd, env: loginEnv, stdin }, ports);
      } finally {
        removeTempPrivateDir(fs, tempLoginDir);
      }
      if (!loginRes || loginRes.code !== 0) {
        return {
          exitCode: 1,
          aborted: loginRes?.code === 130 || loginRes?.signal === 'SIGINT',
          message: 'claude setup-token did not complete.',
        };
      }
      oauthToken = extractClaudeSetupToken(loginRes.stdout);
      if (!oauthToken) {
        throw new CloudAccountsError('claude setup-token did not print a Claude OAuth token. No account was enrolled.', { code: 'missing_local_login' });
      }
      rememberSecrets(oauthToken);
    }
  } else if (fromOption) {
    oauthToken = readClaudeTokenFromPath(fs, resolve(cwd, String(fromOption).trim()), { now: ports.now });
  } else {
    const loginOutput = await readStdinString(stdin);
    oauthToken = readLocalClaudeToken(fs, env, loginOutput, { now: ports.now });
  }

  let candidateLabel;
  if (loopState) {
    candidateLabel = loopState.peekNextLabel();
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
    || (loopState && acc.account_id && loopState.seenAccountIds.has(acc.account_id)),
  );

  materializeLocalClaudeAuth({ delivery_mode: 'direct_oauth', claude_oauth_token: oauthToken }, { env }, ports);
  await leaseAndSyncAfterEnroll('claude', acc, candidateLabel, null, oauthToken, { cwd, env }, ports);

  const finalLabel = acc.label ?? candidateLabel;
  if (loopState) {
    if (acc.account_id) loopState.seenAccountIds.add(acc.account_id);
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
  const provider = requestedProvider || (mode === 'import' ? detectImportProvider(fs, env, { cwd, fromOption, now: ports.now }) : 'codex');

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

  const promptFn = ports.prompt ?? ports.confirm ?? null;
  const stdout = ports.stdout ?? process.stdout;
  const interactive = Boolean(promptFn) || Boolean(stdin?.isTTY && stdout?.isTTY);
  if (!interactive) {
    return { exitCode: 2, message: '--loop requires an interactive terminal (TTY).' };
  }

  const prefix = sanitizeLabel(requestedLabel || provider, provider);
  const { accounts: initialAccounts } = await fetchAccountsList({ cwd, env, refresh: false }, ports);
  const usedLabels = new Set();
  const seenAccountIds = new Set();
  for (const existing of initialAccounts) {
    if (!existing || existing.revoked) continue;
    if (existing.label) usedLabels.add(String(existing.label).toLowerCase());
    if (existing.account_id) seenAccountIds.add(existing.account_id);
  }

  let counter = 1;
  const loopState = {
    bySubjectId: new Map(),
    seenAccountIds,
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
      if (step.aborted) break;
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

function hasLocalMaterializedFile(fs, provider, env) {
  try {
    if (provider === 'claude') {
      return Boolean(fs.statSync(localClaudePaths(env).settingsPath)?.isFile());
    }
    const hasAuth = Boolean(fs.statSync(managedCodexAuthPath(env))?.isFile());
    if (!hasAuth) return false;
    return Boolean(fs.statSync(managedCodexConfigPath(env))?.isFile());
  } catch {
    return false;
  }
}

async function runSyncCommand({ provider: requestedProvider, quiet = false, printCodexHome = false, timeoutMs = 1200, cwd, env }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = (ports.now ?? Date.now)();
  const saved = readCloudAccountsState({ env }, ports);
  let providers = requestedProvider
    ? [requestedProvider]
    : (saved.providers.length ? saved.providers : ['codex']);
  if (quiet || printCodexHome) {
    providers = (requestedProvider ? [requestedProvider] : saved.providers)
      .filter(provider => isCloudAccountsActive({ env, provider }, ports));
    if (!providers.length) return { exitCode: 0, message: '' };
  }

  const messages = [];
  let codexHealthyHome = '';
  for (const provider of providers) {
    const cached = saved.active?.[provider];
    const expiresMs = cached?.expires_at ? Date.parse(cached.expires_at) : NaN;
    const tokenExpiresMs = cached?.access_token_expires_at ? Date.parse(cached.access_token_expires_at) : NaN;
    const tokenFreshEnough = !Number.isFinite(tokenExpiresMs) || (tokenExpiresMs - now) > 5 * 60 * 1000;
    const fiveH = cached?.five_hour_used_percent ?? 0;
    const sevenD = cached?.weekly_used_percent ?? 0;
    const cachedState = cached?.state ?? 'ready';
    const isRevokedCached = cachedState === 'reauth_required' || Boolean(cached?.account_id && saved.reauth?.[cached.account_id]);
    const isHealthyCachedState = cachedState === 'ready' && !isRevokedCached;
    const isCoolingCached = Boolean(saved.cooling?.[provider]);
    const validCache = Boolean(
      cached?.account_id
      && cached?.materialized_local === true
      && isHealthyCachedState
      && !isCoolingCached
      && Number.isFinite(expiresMs)
      && (expiresMs - now) > 15 * 60 * 1000
      && tokenFreshEnough
      && fiveH < 100
      && sevenD < 100
      && hasLocalMaterializedFile(fs, provider, env),
    );
    if (validCache) {
      if (provider === 'codex') codexHealthyHome = pddManagedCodexHome(env);
      if (!quiet && !printCodexHome) messages.push(`Active ${provider} account "${cached.label}" is fresh.`);
      continue;
    }

    // Fail-open on timeout, offline, or unauthenticated state so plain terminal launches never break.
    try {
      const shouldSkipCached = Boolean((fiveH >= 100 || sevenD >= 100 || isRevokedCached) && cached?.account_id);
      const skip = shouldSkipCached ? [cached.account_id] : [];
      const reply = await leaseCloudAccount({
        provider,
        currentAccountId: shouldSkipCached ? null : (cached?.account_id ?? null),
        skipAccountIds: skip,
        holderId: 'terminal-sync',
        updateState: false,
      }, { cwd, env, timeoutMs, ...(quiet || printCodexHome ? { maxRetries: 0 } : {}) }, ports);
      if (reply?.state === 'leased' && !isReauthRequiredAccount(reply.account)) {
        applyMaterializedLease(reply, { env }, ports);
        if (provider === 'codex' && hasLocalMaterializedFile(fs, 'codex', env)) {
          codexHealthyHome = pddManagedCodexHome(env);
        }
        if (!quiet && !printCodexHome) messages.push(`Synced ${provider} account "${reply.account?.label ?? reply.account?.account_id}".`);
      } else if (reply?.state === 'leased' && isReauthRequiredAccount(reply.account)) {
        markLocalAccountReauthRequired(reply.account?.account_id, { env }, ports);
        if (!quiet && !printCodexHome) messages.push(`Account "${reply.account?.label ?? reply.account?.account_id}" requires re-authentication.`);
      } else if (reply?.state === 'all_cooling') {
        const latestSaved = readCloudAccountsState({ env }, ports);
        if (latestSaved.enrolled && latestSaved.providers.includes(provider)) {
          writeCloudAccountsState({
            ...latestSaved,
            cooling: { ...latestSaved.cooling, [provider]: { wake_at: reply.wake_at ?? null } },
          }, { env }, ports);
        }
        if (!quiet && !printCodexHome) {
          messages.push(`All ${provider} accounts are cooling${reply.wake_at ? ` until ${reply.wake_at}` : ''}; keeping current local credentials.`);
        }
      }
    } catch (error) {
      if (isReauthRequiredFailure(error)) {
        const explicitId = error?.payload?.account_id
          ?? error?.payload?.detail?.account_id
          ?? error?.payload?.account?.account_id
          ?? null;
        if (typeof explicitId === 'string' && explicitId) {
          markLocalAccountReauthRequired(explicitId, { env }, ports);
        }
      }
      if (!quiet && !printCodexHome) messages.push(`Cloud sync skipped for ${provider}; keeping current local credentials.`);
    }
  }
  if (printCodexHome) {
    return { exitCode: 0, message: codexHealthyHome };
  }
  return { exitCode: 0, message: quiet ? '' : messages.join('\n') };
}

function runAutoCommand(mode, { env }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const targets = shellProfileEntries(env);
  if (mode === 'status') {
    const activeFiles = targets
      .filter(entry => {
        try { return fs.readFileSync(entry.path, 'utf8').includes(AUTO_BEGIN); } catch { return false; }
      })
      .map(entry => entry.path);
    return {
      exitCode: 0,
      message: activeFiles.length
        ? `Terminal auto-switch: on (${activeFiles.join(', ')}).`
        : 'Terminal auto-switch: off (default).',
    };
  }
  if (mode === 'on') {
    for (const entry of targets) {
      let current = '';
      try { current = fs.readFileSync(entry.path, 'utf8'); } catch (err) { if (err?.code !== 'ENOENT') throw err; }
      const updated = applyAutoSwitchBlock(current, entry.shell);
      if (updated !== current) {
        fs.mkdirSync(dirname(entry.path), { recursive: true });
        fs.writeFileSync(entry.path, updated, { mode: 0o644 });
      }
    }
    return {
      exitCode: 0,
      message: 'Enabled opt-in terminal auto-switch in ~/.zshrc, ~/.bashrc, and ~/.config/fish/config.fish. Open a new shell or source your profile.',
    };
  }
  if (mode === 'off') {
    for (const entry of targets) {
      let current;
      try { current = fs.readFileSync(entry.path, 'utf8'); } catch (err) { if (err?.code === 'ENOENT') continue; throw err; }
      const updated = removeAutoSwitchBlock(current);
      if (updated !== current) fs.writeFileSync(entry.path, updated, { mode: 0o644 });
    }
    return {
      exitCode: 0,
      message: 'Removed terminal auto-switch wrapper from ~/.zshrc, ~/.bashrc, and ~/.config/fish/config.fish.',
    };
  }
  return { exitCode: 2, message: 'Use pdd accounts auto on|off|status.' };
}

function reconcileListedState(accounts, current, { env }, ports = {}) {
  const nowIso = new Date((ports.now ?? Date.now)()).toISOString();
  const accessible = accounts.filter(a => !a.revoked);
  const validIds = new Set(accessible.map(a => a.account_id).filter(Boolean));
  const nextProviders = [...new Set(accessible.map(a => a.provider).filter(Boolean))];
  const nextReauth = {};
  for (const [accId, meta] of Object.entries(current.reauth ?? {})) {
    if (!validIds.has(accId)) continue;
    const acc = accessible.find(a => a.account_id === accId);
    const refreshedIso = acc?.last_refresh_at ?? acc?.refreshed_at ?? null;
    if (!acc || isReauthRequiredAccount(acc) || isLocalReauthUnresolved(accId, refreshedIso, current.reauth)) {
      nextReauth[accId] = meta;
    }
  }
  for (const acc of accessible) {
    if (acc?.account_id && isReauthRequiredAccount(acc) && !nextReauth[acc.account_id]) {
      nextReauth[acc.account_id] = { marked_at: nowIso };
    }
  }
  const nextActive = {};
  for (const [prov, entry] of Object.entries(current.active ?? {})) {
    if (!validIds.has(entry?.account_id)) continue;
    const acc = accessible.find(a => a.account_id === entry.account_id);
    const wasClearedByNewRefresh = Boolean(current.reauth?.[entry.account_id] && !nextReauth[entry.account_id]);
    const effectiveEntry = wasClearedByNewRefresh && entry.state === 'reauth_required'
      ? { ...entry, state: 'ready' }
      : entry;
    nextActive[prov] = acc
      ? {
          ...entry,
          label: acc.label ?? acc.account_id,
          state: accountDisplayState(acc, effectiveEntry, nextReauth),
          last_refresh_at: acc.last_refresh_at ?? acc.refreshed_at ?? entry.last_refresh_at ?? null,
          access_token_expires_at: entry.access_token_expires_at ?? null,
          materialized_local: wasClearedByNewRefresh ? false : (entry.materialized_local === true),
          five_hour_used_percent: typeof acc.five_hour_used_percent === 'number' ? acc.five_hour_used_percent : entry.five_hour_used_percent,
          five_hour_reset_at: acc.five_hour_reset_at ?? entry.five_hour_reset_at,
          weekly_used_percent: typeof acc.weekly_used_percent === 'number' ? acc.weekly_used_percent : entry.weekly_used_percent,
          weekly_reset_at: acc.weekly_reset_at ?? entry.weekly_reset_at,
        }
      : entry;
  }
  const prevCodex = current.active?.codex;
  if (prevCodex && (!nextActive.codex || (prevCodex.managed_codex_gateway === true && !nextActive.codex?.managed_codex_gateway))) {
    restoreLocalCodexGatewayConfig({
      env,
      previousModelProvider: prevCodex.previous_codex_model_provider ?? null,
      removeAuthFile: !nextActive.codex,
    }, ports);
  }
  const nextCooling = Object.fromEntries(
    Object.entries(current.cooling ?? {}).filter(([prov]) => nextProviders.includes(prov)),
  );
  const updatedState = writeCloudAccountsState({
    enrolled: accessible.length > 0,
    providers: nextProviders,
    active: nextActive,
    cooling: nextCooling,
    reauth: nextReauth,
  }, { env }, ports);
  return { accessible, updatedState };
}

async function runStatusCommand({ json = false, cwd, env }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const nowMs = (ports.now ?? Date.now)();
  let current = readCloudAccountsState({ env }, ports);
  let accessible = [];
  let pendingInvites = [];
  let cloudReachable = false;

  try {
    const listed = await fetchAccountsList({ cwd, env, refresh: true }, ports);
    cloudReachable = true;
    pendingInvites = listed.pendingInvites;
    const reconciled = reconcileListedState(listed.accounts, current, { env }, ports);
    accessible = reconciled.accessible;
    current = reconciled.updatedState;
  } catch {
    cloudReachable = false;
  }

  const codexHomePath = pddManagedCodexHome(env);
  let codexAuthPresent = false;
  let codexConfigPresent = false;
  try { codexAuthPresent = Boolean(fs.statSync(managedCodexAuthPath(env))?.isFile()); } catch {}
  try { codexConfigPresent = Boolean(fs.statSync(managedCodexConfigPath(env))?.isFile()); } catch {}

  const activeAutoProfiles = shellProfileEntries(env)
    .filter(entry => {
      try { return fs.readFileSync(entry.path, 'utf8').includes(AUTO_BEGIN); } catch { return false; }
    })
    .map(entry => entry.path);

  const reauthRequired = accessible
    .filter(a => accountDisplayState(a, current.active?.[a.provider], current.reauth) === 'reauth_required')
    .map(a => ({ account_id: a.account_id, label: a.label ?? a.account_id, provider: a.provider }));
  for (const [prov, entry] of Object.entries(current.active ?? {})) {
    if (entry?.state === 'reauth_required' && !reauthRequired.some(r => r.account_id === entry.account_id)) {
      reauthRequired.push({ account_id: entry.account_id, label: entry.label ?? entry.account_id, provider: prov });
    }
  }

  if (json) {
    return {
      exitCode: 0,
      message: redactSecrets(JSON.stringify({
        enrolled: current.enrolled,
        cloud_reachable: cloudReachable,
        providers: current.providers,
        codex_home: {
          path: codexHomePath,
          materialized: codexAuthPresent && codexConfigPresent,
          auth_present: codexAuthPresent,
          config_present: codexConfigPresent,
        },
        auto_switch: {
          enabled: activeAutoProfiles.length > 0,
          profiles: activeAutoProfiles,
        },
        active: current.active,
        cooling: current.cooling,
        reauth_required: reauthRequired,
        accounts: accessible.map(a => ({ ...a, state: accountDisplayState(a, current.active?.[a.provider], current.reauth) })),
        pending_invites: pendingInvites,
      }, null, 2)),
    };
  }

  const lines = [];
  const countNote = cloudReachable
    ? `${accessible.length} account${accessible.length === 1 ? '' : 's'}`
    : 'offline — showing cached local state';
  lines.push(`Cloud accounts: ${current.enrolled ? 'enrolled' : 'not enrolled'} (${countNote})`);
  lines.push(`Codex isolated home: ${codexHomePath} (${codexAuthPresent && codexConfigPresent ? 'materialized' : 'not materialized'}; ~/.codex/auth.json untouched)`);
  lines.push(activeAutoProfiles.length
    ? `Terminal auto-switch: on (${activeAutoProfiles.join(', ')})`
    : 'Terminal auto-switch: off (default)');

  const activeProviders = Object.keys(current.active ?? {});
  if (activeProviders.length > 0) {
    for (const prov of activeProviders) {
      const entry = current.active[prov];
      const liveAcc = accessible.find(a => a.account_id === entry.account_id) ?? null;
      const dispState = liveAcc ? accountDisplayState(liveAcc, entry) : (entry.state || 'ready');
      const refreshStr = formatShortReset(liveAcc?.last_refresh_at ?? entry.last_refresh_at) || '-';
      const expTarget = liveAcc?.access_token_expires_at ?? entry.access_token_expires_at ?? entry.expires_at;
      const expStr = formatExpiryRemaining(expTarget, nowMs);
      const fiveH = formatWindow(liveAcc?.five_hour_used_percent ?? entry.five_hour_used_percent, liveAcc?.five_hour_reset_at ?? entry.five_hour_reset_at);
      const sevenD = formatWindow(liveAcc?.weekly_used_percent ?? entry.weekly_used_percent, liveAcc?.weekly_reset_at ?? entry.weekly_reset_at);
      lines.push(`Active ${prov}: ${entry.label} [${dispState}] (mode: ${entry.delivery_mode ?? 'default'}, 5h: ${fiveH}, 7d: ${sevenD}, last refresh: ${refreshStr}, lease: ${expStr})`);
    }
  }
  if (reauthRequired.length > 0) {
    for (const item of reauthRequired) {
      lines.push(`Re-authentication required: "${item.label}" — run pdd accounts add --provider ${item.provider ?? 'codex'} --label ${item.label}`);
    }
  }
  return { exitCode: 0, message: redactSecrets(lines.join('\n')) };
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
  if (prevCodex && (!nextActive.codex || (prevCodex.managed_codex_gateway === true && !nextActive.codex?.managed_codex_gateway))) {
    restoreLocalCodexGatewayConfig({
      env,
      previousModelProvider: prevCodex.previous_codex_model_provider ?? null,
      removeAuthFile: !nextActive.codex,
    }, ports);
  }
  const nextCooling = Object.fromEntries(
    Object.entries(current.cooling ?? {}).filter(([prov]) => nextProviders.includes(prov)),
  );
  const nextReauth = Object.fromEntries(
    Object.entries(current.reauth ?? {}).filter(([accId]) => accId !== account.account_id && remainingIds.has(accId)),
  );
  writeCloudAccountsState({
    enrolled: remaining.length > 0,
    providers: nextProviders,
    active: nextActive,
    cooling: nextCooling,
    reauth: nextReauth,
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
        const nowMs = (ports.now ?? Date.now)();
        const { accounts, pendingInvites } = await fetchAccountsList({ cwd, env, refresh: true }, ports);
        const current = readCloudAccountsState({ env }, ports);
        const { accessible, updatedState } = reconcileListedState(accounts, current, { env }, ports);
        const normalizedAccounts = accessible.map(acc => ({
          ...acc,
          state: accountDisplayState(acc, updatedState.active?.[acc.provider], updatedState.reauth),
        }));
        if (options['--json'] === true) {
          return {
            exitCode: 0,
            message: redactSecrets(JSON.stringify({ accounts: normalizedAccounts, pending_invites: pendingInvites, active: updatedState.active }, null, 2)),
          };
        }
        return {
          exitCode: 0,
          message: redactSecrets(renderAccountsTable(normalizedAccounts, pendingInvites, updatedState.active, nowMs)),
        };
      }

      case 'status':
        return await runStatusCommand({ json: options['--json'] === true, cwd, env }, ports);

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
        if (isReauthRequiredAccount(account)) {
          markLocalAccountReauthRequired(account.account_id, { env }, ports);
          return {
            exitCode: 1,
            message: `Account "${account.label}" requires re-authentication (state: reauth_required). Run pdd accounts add --provider ${account.provider} --label ${account.label}.`,
          };
        }
        let reply;
        try {
          reply = await leaseCloudAccount({
            provider: account.provider,
            preferredLabel: account.label,
            currentAccountId: account.account_id,
            holderId: 'local-cli',
            updateState: false,
          }, { cwd, env }, ports);
        } catch (err) {
          const attributedId = err?.payload?.account_id ?? err?.payload?.detail?.account_id ?? err?.payload?.account?.account_id ?? null;
          if (isReauthRequiredFailure(err) && attributedId) {
            markLocalAccountReauthRequired(attributedId, { env }, ports);
            return {
              exitCode: 1,
              message: `Account "${account.label}" requires re-authentication (state: reauth_required). Run pdd accounts add --provider ${account.provider} --label ${account.label}.`,
            };
          }
          throw err;
        }
        if (reply?.state === 'all_cooling') {
          return { exitCode: 1, message: `All ${account.provider} accounts are cooling${reply.wake_at ? ` until ${reply.wake_at}` : ''}.` };
        }
        const currentBeforeUse = readCloudAccountsState({ env }, ports);
        const replyRefreshIso = reply?.account?.last_refresh_at ?? reply?.account?.refreshed_at ?? reply?.lease?.last_refresh_at ?? null;
        if (isReauthRequiredAccount(reply?.account) || isLocalReauthUnresolved(reply?.account?.account_id ?? account.account_id, replyRefreshIso, currentBeforeUse.reauth)) {
          markLocalAccountReauthRequired(account.account_id, { env }, ports);
          return {
            exitCode: 1,
            message: `Account "${account.label}" requires re-authentication (state: reauth_required). Run pdd accounts add --provider ${account.provider} --label ${account.label}.`,
          };
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
        const skipIds = currentId ? [currentId] : [];
        let reply = null;
        for (let attempt = 0; attempt < 8; attempt += 1) {
          try {
            reply = await leaseCloudAccount({
              provider,
              currentAccountId: null,
              skipAccountIds: skipIds,
              holderId: 'local-cli',
              updateState: false,
            }, { cwd, env }, ports);
          } catch (err) {
            if (isReauthRequiredFailure(err)) {
              const failedId = err?.payload?.account_id ?? err?.payload?.detail?.account_id ?? null;
              if (failedId) markLocalAccountReauthRequired(failedId, { env }, ports);
              return { exitCode: 1, message: `All remaining ${provider} accounts require re-authentication (state: reauth_required). Run pdd accounts add --provider ${provider}.` };
            }
            throw err;
          }
          if (reply?.state === 'leased' && isReauthRequiredAccount(reply.account) && reply.account?.account_id && !skipIds.includes(reply.account.account_id)) {
            markLocalAccountReauthRequired(reply.account.account_id, { env }, ports);
            skipIds.push(reply.account.account_id);
            continue;
          }
          break;
        }
        if (reply?.state === 'all_cooling') {
          const latestSaved = readCloudAccountsState({ env }, ports);
          if (latestSaved.enrolled && latestSaved.providers.includes(provider)) {
            writeCloudAccountsState({
              ...latestSaved,
              cooling: { ...latestSaved.cooling, [provider]: { wake_at: reply.wake_at ?? null } },
            }, { env }, ports);
          }
          return { exitCode: 1, message: `All ${provider} accounts are cooling${reply.wake_at ? ` until ${reply.wake_at}` : ''}.` };
        }
        if (!reply || reply.state !== 'leased' || isReauthRequiredAccount(reply.account)) {
          if (reply?.account?.account_id) markLocalAccountReauthRequired(reply.account.account_id, { env }, ports);
          return { exitCode: 1, message: `All remaining ${provider} accounts require re-authentication (state: reauth_required). Run pdd accounts add --provider ${provider}.` };
        }
        applyMaterializedLease(reply, { env }, ports);
        return { exitCode: 0, message: `Switched ${provider} account to "${reply.account?.label ?? reply.account?.account_id}".` };
      }

      case 'sync': {
        const timeoutMs = options['--timeout-ms'] !== undefined ? Number(options['--timeout-ms']) : 1200;
        const printCodexHome = options['--print-codex-home'] === true || env?.PDD_PRINT_CODEX_HOME === '1';
        return await runSyncCommand({
          provider: options['--provider'],
          quiet: options['--quiet'] === true,
          printCodexHome,
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
          const sanitizedInvite = sanitizeLabel(rawInvite, '');
          const match = pendingInvites.find(inv => (
            inv.invite_id === rawInvite
            || inv.label === rawInvite
            || inv.account_id === rawInvite
            || (sanitizedInvite && sanitizeLabel(inv.label, '') === sanitizedInvite)
          ));
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
              updateState: false,
            }, { cwd, env }, ports);
            if (leased?.state === 'leased' && !isReauthRequiredAccount(leased.account)) {
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
        });
        if (built.error) return { exitCode: 2, message: built.error };
        if (!built.payloads.length) {
          return { exitCode: 2, message: 'Use pdd accounts unshare LABEL --user USER or pass --with USER|ORG/TEAM[,...].' };
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
