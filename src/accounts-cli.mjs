// Generated from prompts/cli/accounts-cli.prompt.md (sha256: 0ef5f9b6a59e1bf804b8f020f5ad43888734ddec4b520689319496779c819a4e).
import { spawn, spawnSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join, resolve, sep } from 'node:path';
import { createInterface } from 'node:readline';
import { runAgentProcess } from './shared/agent-process.mjs';
import { writeAtomicPreservingSymlinkAndMode } from './shared/atomic-fs.mjs';
import { resolvePddStateBase } from './shared/state-dir.mjs';
import {
  CloudAccountsError,
  classifyRateLimitFailure,
  cloudAccountsRequest,
  extractRateLimitReport,
  isCloudAccountsActive,
  isLocalReauthUnresolved,
  isReauthRequiredAccount,
  isReauthRequiredFailure,
  leaseCloudAccount,
  listCloudAccounts,
  localClaudePaths,
  localCodexAuthPath,
  localCodexHome,
  managedClaudeSettingsPath,
  managedCodexAuthPath,
  managedCodexConfigPath,
  markLocalAccountReauthRequired,
  materializeLocalClaudeAuth,
  materializeLocalCodexAuth,
  pddManagedCodexHome,
  readCloudAccountsState,
  readCodexUsageWindows,
  reportCloudAccountUsage,
  restoreLocalClaudeGatewayConfig,
  restoreLocalCodexGatewayConfig,
  saveActiveLeaseMetadata,
  stopCodexAppServerDaemon,
  writeCloudAccountsState,
} from './login-pool.mjs';
import { knownSecretValues, redactSecrets, rememberSecrets } from './secret-redaction.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const AUTO_BEGIN = '# >>> pdd accounts auto >>>';
const AUTO_END = '# <<< pdd accounts auto <<<';

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
      "        case agents exec e review mcp mcp-server plugin app-server remote-control app completion update doctor sandbox debug apply a resume queue archive delete migrate-rollouts migrate-nfs-db unarchive fork cloud exec-server features help",
      "          set _pdd_sub \"$_pdd_arg\"",
      "          break",
      "        case '*'",
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
      "  if test -z \"$_pdd_cur_home\"; or test $_pdd_is_mhome -eq 1",
      "    set -l _pdd_cx_home \"\"",
      "    if command -sq pdd",
      "      set _pdd_cx_home (env PDD_PRINT_CODEX_HOME=1 pdd accounts sync --provider codex --quiet --timeout-ms 1200 2>/dev/null; or true)",
      "    end",
      "    if test -n \"$_pdd_cx_home\"; and test -f \"$_pdd_cx_home/auth.json\"",
      "      if isatty stdin; and isatty stdout; and begin; test -z \"$_pdd_sub\"; or test \"$_pdd_sub\" = \"resume\"; or test \"$_pdd_sub\" = \"fork\"; end",
      "        CODEX_HOME=\"$_pdd_cx_home\" pdd accounts codex -- $argv",
      "        return $status",
      "      end",
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
      "  if set -q CLAUDE_CONFIG_DIR; and test -n \"$CLAUDE_CONFIG_DIR\"",
      "    command claude $argv",
      "    return $status",
      "  end",
      "  if test (count $argv) -gt 0",
      "    switch $argv[1]",
      "      case auth login logout setup-token -v --version -h --help",
      "        command claude $argv",
      "        return $status",
      "    end",
      "  end",
      "  if command -sq pdd-claude",
      "    PDD_CLAUDE_AUTO_FAIL_OPEN=1 command pdd-claude $argv",
      "    return $status",
      "  end",
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
    "        agents|exec|e|review|mcp|mcp-server|plugin|app-server|remote-control|app|completion|update|doctor|sandbox|debug|apply|a|resume|queue|archive|delete|migrate-rollouts|migrate-nfs-db|unarchive|fork|cloud|exec-server|features|help)",
    "          _pdd_sub=\"$_pdd_arg\"",
    "          break",
    "          ;;",
    "        *)",
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
    "  if [ -z \"$_pdd_cur_home\" ] || [ \"$_pdd_is_mhome\" -eq 1 ]; then",
    "    local _pdd_cx_home=\"\"",
    "    if command -v pdd >/dev/null 2>&1; then",
    "      _pdd_cx_home=\"$(PDD_PRINT_CODEX_HOME=1 pdd accounts sync --provider codex --quiet --timeout-ms 1200 2>/dev/null || true)\"",
    "    fi",
    "    if [ -n \"$_pdd_cx_home\" ] && [ -f \"$_pdd_cx_home/auth.json\" ]; then",
    "      if [ -t 0 ] && [ -t 1 ] && { [ -z \"$_pdd_sub\" ] || [ \"$_pdd_sub\" = \"resume\" ] || [ \"$_pdd_sub\" = \"fork\" ]; }; then",
    "        CODEX_HOME=\"$_pdd_cx_home\" pdd accounts codex -- \"$@\"",
    "        return $?",
    "      fi",
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
    "  if [ -n \"${CLAUDE_CONFIG_DIR:-}\" ]; then",
    "    command claude \"$@\"",
    "    return $?",
    "  fi",
    "  case \"${1:-}\" in",
    "    auth|login|logout|setup-token|-v|--version|-h|--help)",
    "      command claude \"$@\"",
    "      return $?",
    "      ;;",
    "  esac",
    "  if command -v pdd-claude >/dev/null 2>&1; then",
    "    PDD_CLAUDE_AUTO_FAIL_OPEN=1 command pdd-claude \"$@\"",
    "    return $?",
    "  fi",
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

function shellProfileEntries(env = process.env, { requireExplicitHome = false } = {}) {
  const explicitHome = typeof env?.HOME === 'string' ? env.HOME.trim() : '';
  if (requireExplicitHome && !explicitHome) return [];
  const home = explicitHome || homedir();
  const xdgConfig = (typeof env?.XDG_CONFIG_HOME === 'string' && env.XDG_CONFIG_HOME.trim())
    ? env.XDG_CONFIG_HOME.trim()
    : join(home, '.config');
  return [
    { path: join(home, '.zshrc'), shell: 'zsh' },
    { path: join(home, '.bashrc'), shell: 'bash' },
    { path: join(xdgConfig, 'fish', 'config.fish'), shell: 'fish' },
  ];
}

export function refreshInstalledAutoSwitchBlocks({ env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  if (typeof fs?.readFileSync !== 'function' || typeof fs?.writeFileSync !== 'function') return [];
  const entries = shellProfileEntries(env, { requireExplicitHome: true });
  if (!entries.length) return [];
  const upgraded = [];
  for (const entry of entries) {
    try {
      const existingText = fs.readFileSync(entry.path, 'utf8');
      if (
        typeof existingText !== 'string'
        || !existingText.includes(AUTO_BEGIN)
        || !existingText.includes(AUTO_END)
      ) {
        continue;
      }
      const beginIdx = existingText.indexOf(AUTO_BEGIN);
      const endIdx = existingText.indexOf(AUTO_END, beginIdx + AUTO_BEGIN.length);
      if (beginIdx < 0 || endIdx < 0) continue;
      const nextText = applyAutoSwitchBlock(existingText, entry.shell);
      if (nextText === existingText) continue;
      writeAtomicPreservingSymlinkAndMode(fs, entry.path, nextText, { defaultMode: 0o644 });
      upgraded.push(entry.path);
    } catch {}
  }
  return upgraded;
}

function formatShortReset(iso) {
  if (typeof iso !== 'string' || !iso.trim()) return '';
  const ms = Date.parse(iso);
  if (!Number.isFinite(ms)) return iso.slice(0, 19);
  return new Date(ms).toISOString().replace(/:\d{2}(?:\.\d+)?Z$/, 'Z');
}

function computeLeftPercent(usedPct) {
  if (typeof usedPct !== 'number' || !Number.isFinite(usedPct)) return null;
  return Math.min(100, Math.max(0, Math.round(100 - usedPct)));
}

function formatWindow(pct, resetAt) {
  const left = computeLeftPercent(pct);
  if (left === null) return '-';
  const reset = formatShortReset(resetAt);
  return reset ? `${left}% left (${reset})` : `${left}% left`;
}

function formatAccountQuotaSummary(acc) {
  const fiveH = formatWindow(acc?.five_hour_used_percent, acc?.five_hour_reset_at);
  const sevenD = formatWindow(acc?.weekly_used_percent, acc?.weekly_reset_at);
  if (fiveH === '-' && sevenD === '-') return '';
  return ` (5h: ${fiveH}, 7d: ${sevenD})`;
}

function withLeftPercentFields(entry) {
  if (!object(entry)) return entry;
  return {
    ...entry,
    five_hour_left_percent: computeLeftPercent(entry.five_hour_used_percent),
    weekly_left_percent: computeLeftPercent(entry.weekly_used_percent),
  };
}

function withLeftPercentActiveMap(activeMap) {
  if (!object(activeMap)) return activeMap;
  const out = {};
  for (const [prov, entry] of Object.entries(activeMap)) {
    out[prov] = withLeftPercentFields(entry);
  }
  return out;
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
  const listedIds = new Set(accounts.map(acc => acc?.account_id).filter(Boolean));
  const visiblePendingInvites = Array.isArray(pendingInvites)
    ? pendingInvites.filter(inv => !(inv?.account_id && listedIds.has(inv.account_id)))
    : [];
  if (visiblePendingInvites.length > 0) {
    lines.push('');
    lines.push('Pending share invites:');
    for (const inv of visiblePendingInvites) {
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

function extractCodexEmail(authJson) {
  const payload = decodeJwtPayload(authJson?.tokens?.id_token) ?? decodeJwtPayload(authJson?.tokens?.access_token);
  return typeof payload?.email === 'string' && payload.email.trim() ? payload.email.trim() : '';
}

function deriveEmailBaseLabel(authJson) {
  const email = extractCodexEmail(authJson);
  const emailUser = email ? email.split('@')[0] : '';
  return sanitizeLabel(emailUser, '');
}

function defaultAccountLabel(provider, authJson = null) {
  if (provider === 'codex') {
    const slug = deriveEmailBaseLabel(authJson);
    if (slug) return slug;
  }
  return `${provider}-main`;
}

function nextDisambiguatedLabel(baseLabel, usedLabels, startSuffix = 2) {
  const cleanBase = sanitizeLabel(baseLabel, 'account');
  if (!usedLabels.has(cleanBase.toLowerCase())) return cleanBase;
  let idx = Math.max(2, startSuffix);
  while (usedLabels.has(`${cleanBase}-${idx}`.toLowerCase())) idx += 1;
  return `${cleanBase}-${idx}`;
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

function stripAnsiText(raw) {
  return String(raw ?? '')
    .replace(/\x1b\][^\x07\x1b]*(?:\x07|\x1b\\)/g, '')
    .replace(/\x1b\[[0-?]*[ -/]*[@-~]/g, '')
    .replace(/\x1b[@-Z\\-_]/g, '')
    .replace(/\r\n/g, '\n')
    .replace(/\r/g, '\n');
}

function unwrapClaudeTokenLines(cleanText) {
  const lines = cleanText.split('\n');
  const out = [];
  for (let i = 0; i < lines.length; i += 1) {
    let cur = lines[i];
    const tokenTail = /(sk-ant-oat[A-Za-z0-9_-]{8,})\s*$/.exec(cur);
    if (tokenTail && (cur.trimEnd().length >= 50 || tokenTail[1].length >= 45)) {
      cur = cur.trimEnd();
      let tokLen = tokenTail[1].length;
      while (i + 1 < lines.length) {
        const contMatch = /^\s*([A-Za-z0-9_-]+)\s*$/.exec(lines[i + 1]);
        if (!contMatch) break;
        const frag = contMatch[1];
        if (tokLen >= 95 && !/[0-9_-]/.test(frag)) break;
        cur += frag;
        tokLen += frag.length;
        i += 1;
      }
    }
    out.push(cur);
  }
  return out.join('\n');
}

function extractClaudeToken(text) {
  const cleaned = unwrapClaudeTokenLines(stripAnsiText(text));
  const match = /\b(sk-ant-oat[A-Za-z0-9_-]{8,})\b/.exec(cleaned);
  return match ? match[1] : '';
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
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  let rawSt = null;
  try { rawSt = lstat(resolved); } catch {}
  if (rawSt?.isSymbolicLink()) {
    throw new CloudAccountsError(`Refusing to import symlinked Codex credential path: ${resolved}`, { code: 'symlink_refused' });
  }
  const isDir = Boolean(rawSt?.isDirectory());
  const authPath = isDir ? join(resolved, 'auth.json') : resolved;
  const isDefaultLocal = resolve(authPath) === resolve(defaultAuth);
  return {
    authPath,
    probeCodexHome: isDir ? resolved : null,
    isDefaultLocal,
  };
}

function isPathInsideRoot(candidatePath, rootPath) {
  const normCandidate = resolve(candidatePath);
  const normRoot = resolve(rootPath);
  return normCandidate === normRoot || normCandidate.startsWith(normRoot + sep) || normCandidate.startsWith(`${normRoot}/`);
}

function resolveAllowedImportAuthFile(fs, authPath, env = process.env, { action = 'import' } = {}) {
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  const statFn = fs.statSync ?? nativeFs.statSync;
  const realFn = fs.realpathSync?.native ?? fs.realpathSync ?? nativeFs.realpathSync?.native ?? nativeFs.realpathSync;
  const managedHome = pddManagedCodexHome(env);
  const refuse = msg => { throw new CloudAccountsError(msg, { code: 'symlink_refused' }); };
  if (typeof realFn !== 'function' || typeof statFn !== 'function') {
    refuse(`Refusing to ${action} symlinked Codex credential file: ${authPath}`);
  }
  let realTarget;
  try {
    realTarget = String(realFn.call(fs, authPath));
    const targetStat = statFn.call(fs, realTarget);
    if (!targetStat?.isFile()) {
      refuse(`Refusing to ${action} symlinked Codex credential file: ${authPath}`);
    }
    const targetDirStat = lstat(dirname(realTarget));
    if (!targetDirStat || targetDirStat.isSymbolicLink() || !targetDirStat.isDirectory()) {
      refuse(`Refusing to ${action} symlinked Codex credential file: ${authPath}`);
    }
  } catch (err) {
    if (err instanceof CloudAccountsError) throw err;
    refuse(`Refusing to ${action} symlinked Codex credential file: ${authPath}`);
  }
  if (isPathInsideRoot(realTarget, managedHome)) {
    refuse(`Refusing to ${action} symlinked Codex credential file: ${authPath}`);
  }
  try {
    const realManaged = String(realFn.call(fs, managedHome));
    if (isPathInsideRoot(realTarget, realManaged)) {
      refuse(`Refusing to ${action} symlinked Codex credential file: ${authPath}`);
    }
  } catch (err) {
    if (err instanceof CloudAccountsError) throw err;
  }
  return realTarget;
}

function assertNonSymlinkImportFile(fs, authPath, env = process.env) {
  if (!authPath) return authPath;
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  const parentDir = dirname(authPath);
  let parentSt = null;
  try { parentSt = lstat(parentDir); } catch {}
  if (parentSt?.isSymbolicLink()) {
    throw new CloudAccountsError(`Refusing to import Codex credential file from symlinked directory: ${parentDir}`, { code: 'symlink_refused' });
  }
  let st = null;
  try { st = lstat(authPath); } catch { return authPath; }
  if (st?.isSymbolicLink()) {
    return resolveAllowedImportAuthFile(fs, authPath, env, { action: 'import' });
  }
  return authPath;
}

function scrubImportedCodexSourceRefreshToken(fs, authPath, env = process.env) {
  if (!authPath) return false;
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  const dir = dirname(authPath);
  let dirSt = null;
  try { dirSt = lstat(dir); } catch { return false; }
  if (!dirSt || dirSt.isSymbolicLink() || !dirSt.isDirectory()) {
    if (dirSt?.isSymbolicLink()) {
      throw new CloudAccountsError(`Refusing to rewrite Codex credential file in symlinked directory: ${dir}`, { code: 'symlink_refused' });
    }
    return false;
  }
  let st = null;
  try { st = lstat(authPath); } catch { return false; }
  if (!st) return false;
  let targetFilePath = authPath;
  if (st.isSymbolicLink()) {
    targetFilePath = resolveAllowedImportAuthFile(fs, authPath, env, { action: 'rewrite' });
  } else if (!st.isFile()) {
    return false;
  }
  let parsed = null;
  try {
    parsed = JSON.parse(fs.readFileSync(targetFilePath, 'utf8'));
  } catch {
    return false;
  }
  if (!object(parsed) || !object(parsed.tokens)) return false;
  if (typeof parsed.tokens.refresh_token !== 'string' || parsed.tokens.refresh_token === '') {
    return false;
  }
  rememberCodexPayloadSecrets(parsed);
  const scrubbed = {
    ...parsed,
    tokens: {
      ...parsed.tokens,
      refresh_token: '',
    },
  };
  const targetDir = dirname(targetFilePath);
  const tmpPath = join(targetDir, `.pdd-scrub-${process.pid}-${randomBytes(6).toString('hex')}.tmp`);
  try {
    fs.writeFileSync(tmpPath, `${JSON.stringify(scrubbed, null, 2)}\n`, { mode: 0o600 });
    try { (fs.chmodSync ?? nativeFs.chmodSync)(tmpPath, 0o600); } catch {}
    fs.renameSync(tmpPath, targetFilePath);
    return true;
  } catch (err) {
    try { (fs.rmSync ?? nativeFs.rmSync)(tmpPath, { force: true }); } catch {}
    throw err;
  }
}

export function detectImportProvider(fs, env = process.env, options = {}) {
  const cwd = options?.cwd ?? process.cwd();
  const fromOption = options?.fromOption ?? options?.from ?? null;
  const now = typeof options?.now === 'function' ? options.now : Date.now;
  if (fromOption) {
    const resolved = resolve(cwd, String(fromOption).trim());
    const lstat = fs.lstatSync ?? nativeFs.lstatSync;
    const parentDir = dirname(resolved);
    let parentSt = null;
    try { parentSt = lstat.call(fs, parentDir); } catch {}
    if (parentSt?.isSymbolicLink?.() && parentSt.uid !== 0) {
      throw new CloudAccountsError(
        `Refusing to import credential file from symlinked directory: ${parentDir}. `
        + 'Pass a real non-symlinked credential directory or file to --from, then rerun.',
        { code: 'symlink_refused' },
      );
    }
    let rawSt = null;
    try { rawSt = lstat.call(fs, resolved); } catch {}
    if (rawSt?.isSymbolicLink?.()) {
      throw new CloudAccountsError(
        `Refusing to import symlinked credential path: ${resolved}. `
        + 'Pass the real credential file or directory path to --from (not a symlink), then rerun.',
        { code: 'symlink_refused' },
      );
    }
    const isRegularNonSymlink = candidatePath => {
      let st;
      try {
        st = lstat.call(fs, candidatePath);
      } catch {
        return false;
      }
      if (st?.isSymbolicLink?.()) {
        throw new CloudAccountsError(
          `Refusing to import symlinked credential file: ${candidatePath}. `
          + 'Pass a real non-symlinked credential file to --from, then rerun.',
          { code: 'symlink_refused' },
        );
      }
      return Boolean(st?.isFile?.());
    };
    const isDir = Boolean(rawSt?.isDirectory?.());
    if (isDir) {
      const authCandidate = join(resolved, 'auth.json');
      if (isRegularNonSymlink(authCandidate)) {
        try {
          const raw = JSON.parse(fs.readFileSync(authCandidate, 'utf8'));
          rememberCodexPayloadSecrets(raw);
          if (object(raw?.tokens)) return 'codex';
        } catch {}
      }
      for (const fileName of ['settings.json', '.credentials.json']) {
        const candidate = join(resolved, fileName);
        if (!isRegularNonSymlink(candidate)) continue;
        try {
          const txt = fs.readFileSync(candidate, 'utf8');
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
    if (!rawSt?.isFile?.()) {
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

function createTempPrivateDir(fs, prefix, tmpRoot, env = process.env) {
  const rootDir = tmpRoot
    || (typeof env?.PDD_CODEX_RUNTIME_ROOT === 'string' && env.PDD_CODEX_RUNTIME_ROOT.trim())
    || join(resolvePddStateBase(env), 'codex-runtime');
  fs.mkdirSync(rootDir, { recursive: true, mode: 0o700 });
  try { (fs.chmodSync ?? nativeFs.chmodSync)(rootDir, 0o700); } catch {}
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

function runInteractiveClaudeSetupToken({ cwd, env, stdin, stdout, stderr, timeoutMs = 300_000 }, ports = {}) {
  const spawnImpl = ports.spawnInteractive ?? spawn;
  return new Promise((resolveRun, rejectRun) => {
    let child = null;
    let stdoutBuf = '';
    let stderrBuf = '';
    let settled = false;
    let killTimer = null;
    let interrupted = false;

    const cleanupSigint = () => process.off('SIGINT', onSigint);
    const stopChild = () => {
      if (!child) return;
      try { child.kill('SIGTERM'); } catch {}
      killTimer = setTimeout(() => {
        try { child.kill('SIGKILL'); } catch {}
      }, 500);
      killTimer.unref?.();
    };
    const finish = (err, code, signal) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      if (killTimer) clearTimeout(killTimer);
      cleanupSigint();
      if (err) {
        err.stdout = stdoutBuf;
        err.stderr = stderrBuf;
        rejectRun(err);
        return;
      }
      resolveRun({
        code: interrupted || signal === 'SIGINT' ? 130 : (code ?? 1),
        signal: interrupted ? 'SIGINT' : (signal ?? null),
        stdout: stdoutBuf,
        stderr: stderrBuf,
      });
    };
    const onSigint = () => {
      interrupted = true;
      stopChild();
      finish(null, 130, 'SIGINT');
    };
    const timer = setTimeout(() => {
      stopChild();
      finish(new CloudAccountsError('claude setup-token timed out waiting for browser OAuth completion.', { code: 'timeout' }));
    }, timeoutMs);
    timer.unref?.();

    const childEnv = { ...env, COLUMNS: env?.COLUMNS || '500' };
    const useInheritedStdin = stdin === process.stdin || !stdin || typeof stdin.pipe !== 'function';
    try {
      child = spawnImpl('claude', ['setup-token'], {
        cwd,
        env: childEnv,
        stdio: [useInheritedStdin ? 'inherit' : 'pipe', 'pipe', 'pipe'],
        shell: false,
      });
    } catch (err) {
      finish(err);
      return;
    }

    process.on('SIGINT', onSigint);
    if (!useInheritedStdin && child.stdin) {
      stdin.pipe(child.stdin);
      child.stdin.on('error', () => {});
    }
    child.stdout?.on('data', chunk => {
      const str = String(chunk);
      stdoutBuf += str;
      try { stdout?.write?.(chunk); } catch {}
    });
    child.stderr?.on('data', chunk => {
      const str = String(chunk);
      stderrBuf += str;
      try { stderr?.write?.(chunk); } catch {}
    });
    child.on('error', err => finish(err));
    child.on('close', (code, signal) => finish(null, code, signal));
  });
}

async function runProviderLogin(provider, { cwd, env, deviceAuth = false, stdin = process.stdin }, ports = {}) {
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
  const activeStdin = ports.stdin ?? stdin ?? process.stdin;
  const activeStdout = ports.stdout ?? process.stdout;
  const activeStderr = ports.stderr ?? process.stderr;
  if (provider === 'claude') {
    if (!activeStdin?.isTTY || !activeStdout?.isTTY) {
      throw new CloudAccountsError(
        'claude setup-token requires an interactive terminal (TTY) to paste the OAuth authorization code. Run "pdd accounts add --provider claude" in an interactive terminal, pipe a token to stdin, or run "pdd accounts import --provider claude".',
        { code: 'non_interactive_claude_login', exitCode: 1 },
      );
    }
    return runInteractiveClaudeSetupToken({
      cwd,
      env,
      stdin: activeStdin,
      stdout: activeStdout,
      stderr: activeStderr,
      timeoutMs: ports.claudeLoginTimeoutMs ?? 300_000,
    }, ports);
  }
  if (provider === 'codex' && activeStdin?.isTTY && activeStdout?.isTTY) {
    const res = spawnSync(cmd, args, { cwd, env, stdio: 'inherit' });
    return {
      code: res.signal === 'SIGINT' ? 130 : (res.status ?? 1),
      signal: res.signal ?? null,
      stdout: '',
      stderr: '',
    };
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
      const leasePlanType = lease.plan_type ?? leaseReply?.account?.plan_type ?? leaseReply?.account?.plan;
      const leaseInput = lease.plan_type === undefined && typeof leasePlanType === 'string' && leasePlanType.trim()
        ? { ...lease, plan_type: leasePlanType }
        : lease;
      const mat = materializeLocalCodexAuth(leaseInput, {
        env,
        previousManagedCodexGateway: prevManagedGateway,
        previousCodexModelProvider: prevModelProvider,
      }, ports);
      stopCodexAppServerDaemon(mat.codexHome, {
        env,
        fs: ports.fs ?? nativeFs,
        spawnSync: ports.spawnSync,
      });
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
      const mat = materializeLocalCodexAuth(lease.codex_auth_json, {
        env,
        previousManagedCodexGateway: prevManagedGateway,
        previousCodexModelProvider: prevModelProvider,
      }, ports);
      stopCodexAppServerDaemon(mat.codexHome, {
        env,
        fs: ports.fs ?? nativeFs,
        spawnSync: ports.spawnSync,
      });
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
    const { managedBaseUrl } = materializeLocalClaudeAuth(lease, { env }, ports);
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

function sharePayloadKey(item) {
  const b = item?.body ?? {};
  if (b.team && b.org) return `team:${String(b.org).toLowerCase()}/${String(b.team).toLowerCase()}`;
  if (b.org) return `org:${String(b.org).toLowerCase()}`;
  if (b.github_login) return `user:${String(b.github_login).toLowerCase()}`;
  if (Number.isSafeInteger(b.github_user_id)) return `uid:${b.github_user_id}`;
  return '';
}

function addRawShareEntryKeys(keys, entry) {
  if (!entry) return;
  if (typeof entry === 'string') {
    const trimmed = entry.trim();
    if (!trimmed) return;
    if (trimmed.startsWith('@')) {
      keys.add(`org:${trimmed.slice(1).toLowerCase()}`);
    } else if (trimmed.includes('/')) {
      keys.add(`team:${trimmed.toLowerCase()}`);
    } else {
      keys.add(`user:${trimmed.toLowerCase()}`);
    }
    return;
  }
  if (!object(entry)) return;
  const st = typeof entry.state === 'string' ? entry.state.toLowerCase() : '';
  if (st === 'revoked' || st === 'declined' || st === 'cancelled' || st === 'expired') return;
  if (entry.team && entry.org) {
    keys.add(`team:${String(entry.org).toLowerCase()}/${String(entry.team).toLowerCase()}`);
    return;
  }
  if (typeof entry.team === 'string' && entry.team.includes('/')) {
    keys.add(`team:${entry.team.toLowerCase()}`);
    return;
  }
  if (entry.org) {
    keys.add(`org:${String(entry.org).toLowerCase()}`);
    return;
  }
  const login = entry.github_login ?? entry.recipient_login ?? entry.invited_login ?? entry.login ?? entry.user ?? '';
  if (typeof login === 'string' && login.trim()) {
    keys.add(`user:${login.trim().toLowerCase()}`);
  }
  const uid = entry.github_user_id ?? entry.recipient_github_id ?? entry.user_id ?? null;
  if (Number.isSafeInteger(uid)) {
    keys.add(`uid:${uid}`);
  }
}

function collectExistingShareKeys(account, pendingInvites = [], sessionSharedKeys = null) {
  const keys = new Set();
  if (!object(account)) return keys;
  const accId = account.account_id;
  for (const field of ['shares', 'shared_with', 'active_shares', 'pending_shares', 'pending_invites', 'invites', 'accepted_users', 'accepted_logins']) {
    if (Array.isArray(account[field])) {
      for (const entry of account[field]) addRawShareEntryKeys(keys, entry);
    }
  }
  if (Array.isArray(account.org_shares)) {
    for (const org of account.org_shares) {
      if (typeof org === 'string' && org.trim()) keys.add(`org:${org.trim().replace(/^@/, '').toLowerCase()}`);
    }
  }
  if (Array.isArray(account.team_shares)) {
    for (const team of account.team_shares) {
      if (typeof team === 'string' && team.trim()) keys.add(`team:${team.trim().toLowerCase()}`);
    }
  }
  if (Array.isArray(account.accepted_user_ids)) {
    for (const uid of account.accepted_user_ids) {
      if (Number.isSafeInteger(uid)) keys.add(`uid:${uid}`);
    }
  }
  if (accId && Array.isArray(pendingInvites)) {
    for (const inv of pendingInvites) {
      if (inv?.account_id === accId) addRawShareEntryKeys(keys, inv);
    }
  }
  if (accId && sessionSharedKeys instanceof Set) {
    const prefix = `${accId}:`;
    for (const sk of sessionSharedKeys) {
      if (sk.startsWith(prefix)) keys.add(sk.slice(prefix.length));
    }
  }
  return keys;
}

function extractSharePayloadsFromAccount(account, pendingInvites = []) {
  const existing = [];
  if (!object(account)) return existing;
  const loginToUid = new Map();
  const coveredUids = new Set();
  const inspectRawEntry = entry => {
    if (!object(entry)) return;
    const st = typeof entry.state === 'string' ? entry.state.toLowerCase() : '';
    if (st === 'revoked' || st === 'declined' || st === 'cancelled' || st === 'expired') return;
    if (entry.team || entry.org) return;
    const rawLogin = entry.github_login ?? entry.recipient_login ?? entry.invited_login ?? entry.login ?? entry.user ?? '';
    const login = typeof rawLogin === 'string' ? rawLogin.trim().toLowerCase() : '';
    const uid = entry.github_user_id ?? entry.recipient_github_id ?? entry.user_id ?? null;
    if (login && Number.isSafeInteger(uid)) {
      loginToUid.set(login, uid);
      coveredUids.add(uid);
    }
  };
  for (const field of ['shares', 'shared_with', 'active_shares', 'pending_shares', 'pending_invites', 'invites', 'accepted_users', 'accepted_logins']) {
    if (Array.isArray(account[field])) {
      for (const entry of account[field]) inspectRawEntry(entry);
    }
  }
  if (account.account_id && Array.isArray(pendingInvites)) {
    for (const inv of pendingInvites) {
      if (inv?.account_id === account.account_id) inspectRawEntry(inv);
    }
  }

  const keys = collectExistingShareKeys(account, pendingInvites);
  for (const k of keys) {
    if (k.startsWith('org:')) {
      const org = k.slice(4);
      existing.push({ display: `@${org}`, body: { org } });
    } else if (k.startsWith('team:')) {
      const [org, team] = k.slice(5).split('/');
      if (org && team) existing.push({ display: `${org}/${team}`, body: { org, team } });
    } else if (k.startsWith('user:')) {
      const login = k.slice(5);
      const body = { github_login: login };
      if (loginToUid.has(login)) body.github_user_id = loginToUid.get(login);
      existing.push({ display: login, body });
    } else if (k.startsWith('uid:')) {
      const uid = Number(k.slice(4));
      if (Number.isSafeInteger(uid) && !coveredUids.has(uid)) {
        existing.push({ display: `github_user_id:${uid}`, body: { github_user_id: uid } });
      }
    }
  }
  return existing;
}

function mergeSharePayloads(basePayloads, extraPayloads) {
  const seenKeys = new Set();
  const uidIndex = new Map();
  const merged = [];
  for (const item of [...basePayloads, ...extraPayloads]) {
    const key = sharePayloadKey(item);
    if (!key) continue;
    const uid = Number.isSafeInteger(item?.body?.github_user_id) ? item.body.github_user_id : null;
    if (uid !== null && uidIndex.has(uid)) {
      const prevIdx = uidIndex.get(uid);
      if (!merged[prevIdx]?.body?.github_login && item?.body?.github_login) {
        merged[prevIdx] = item;
        seenKeys.add(key);
      }
      continue;
    }
    if (seenKeys.has(key)) continue;
    seenKeys.add(key);
    if (uid !== null) uidIndex.set(uid, merged.length);
    merged.push(item);
  }
  return merged;
}

async function applySharePayloadsToAccounts(accounts, sharePayloads, { cwd, env, pendingInvites = [], sessionSharedKeys = null }, ports = {}) {
  const notes = [];
  for (const account of accounts) {
    const existingKeys = collectExistingShareKeys(account, pendingInvites, sessionSharedKeys);
    for (const item of sharePayloads) {
      const key = sharePayloadKey(item);
      const uidKey = Number.isSafeInteger(item?.body?.github_user_id) ? `uid:${item.body.github_user_id}` : '';
      if ((key && existingKeys.has(key)) || (uidKey && existingKeys.has(uidKey))) {
        notes.push({
          label: account.label ?? account.account_id,
          display: item.display,
          inviteId: null,
          alreadyShared: true,
        });
        continue;
      }
      let res = null;
      try {
        res = await cloudAccountsRequest(
          'POST',
          `/v1/accounts/${encodeURIComponent(account.account_id)}/share`,
          { body: item.body, cwd, env },
          ports,
        );
      } catch (err) {
        if (err instanceof CloudAccountsError && err.status === 409) {
          notes.push({
            label: account.label ?? account.account_id,
            display: item.display,
            inviteId: null,
            alreadyShared: true,
          });
          continue;
        }
        throw err;
      }
      if (key) {
        existingKeys.add(key);
        if (account.account_id && sessionSharedKeys instanceof Set) {
          sessionSharedKeys.add(`${account.account_id}:${key}`);
        }
      }
      if (uidKey) existingKeys.add(uidKey);
      const serverAlreadyShared = Boolean(
        res?.already_shared === true
        || (
          (item?.body?.github_login || item?.body?.github_user_id)
          && res?.already_shared !== false
          && !res?.invite
          && !res?.invite_id
        ),
      );
      const inviteId = serverAlreadyShared ? null : (res?.invite?.invite_id ?? res?.invite_id ?? null);
      notes.push({
        label: account.label ?? account.account_id,
        display: item.display,
        inviteId,
        alreadyShared: serverAlreadyShared,
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

async function probeInitialCodexUsageIfUnpopulated(acc, authJson, _probeCodexHome, { fs, cwd, env }, ports = {}) {
  if (!acc?.account_id) return acc;
  const isUnpopulated = (acc.five_hour_used_percent ?? 0) === 0
    && (acc.weekly_used_percent ?? 0) === 0
    && !acc.five_hour_reset_at
    && !acc.weekly_reset_at;
  if (!isUnpopulated) return acc;

  let tempProbeDir = null;
  try {
    // Always probe inside a disposable 0700 temp directory whose auth.json copy has
    // tokens.refresh_token cleared ("") so local `codex app-server` uses only access_token
    // and can never consume/invalidate the single-use refresh_token uploaded to Cloud.
    tempProbeDir = createTempPrivateDir(fs, 'pdd-cx-probe-', ports.tmpRoot, env);
    const probeAuthJson = object(authJson) && object(authJson.tokens)
      ? {
          ...authJson,
          tokens: {
            ...authJson.tokens,
            refresh_token: '',
          },
        }
      : authJson;
    fs.writeFileSync(join(tempProbeDir, 'auth.json'), `${JSON.stringify(probeAuthJson, null, 2)}\n`, { mode: 0o600 });
    const probeFn = ports.readCodexUsageWindows ?? readCodexUsageWindows;
    const windows = await probeFn(
      {
        command: 'codex',
        cwd,
        env: { ...env, CODEX_HOME: tempProbeDir },
        weeklyStopPercent: 100,
        timeoutMs: ports.usageProbeTimeoutMs ?? 3000,
      },
      ports.codexLimitPorts,
    );
    removeTempPrivateDir(fs, tempProbeDir);
    tempProbeDir = null;
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

async function askPromptRaw(question, { stdin, stdout }, ports = {}) {
  const promptFn = ports.prompt ?? ports.confirm ?? null;
  if (typeof promptFn === 'function') {
    try {
      return await promptFn(question);
    } catch {
      return undefined;
    }
  }
  const rl = createInterface({ input: stdin, output: stdout });
  try {
    return await new Promise(resolveAnswer => {
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

async function askLoopContinue(question, { stdin, stdout }, ports = {}) {
  const answer = await askPromptRaw(question, { stdin, stdout }, ports);
  if (answer === undefined || answer === null || answer === false) return false;
  if (answer === true) return true;
  const normalized = String(answer).trim().toLowerCase();
  return normalized === '' || normalized === 'y' || normalized === 'yes';
}

async function resolveAccount(labelOrId, { cwd, env, provider = null }, ports = {}) {
  const target = String(labelOrId ?? '').trim();
  if (!target) throw new CloudAccountsError('Account label is required.', { code: 'missing_label', exitCode: 2 });
  const { accounts, pendingInvites } = await fetchAccountsList({ cwd, env }, ports);
  const activePool = accounts.filter(a => !a.revoked);
  const candidates = provider ? activePool.filter(a => a.provider === provider) : activePool;

  const pickTier = matches => {
    if (matches.length === 1) return { account: matches[0], accounts, pendingInvites };
    if (matches.length > 1) {
      const providers = [...new Set(matches.map(a => a.provider).filter(Boolean))];
      if (!provider && providers.length > 1) {
        const flags = providers.map(p => `--provider ${p}`).join(' or ');
        throw new CloudAccountsError(
          `Account label "${target}" exists for multiple providers (${providers.join(', ')}). Pass ${flags}.`,
          { code: 'ambiguous_provider', exitCode: 2 },
        );
      }
      return { account: matches[0], accounts, pendingInvites };
    }
    return null;
  };

  const byId = pickTier(candidates.filter(a => a.account_id === target));
  if (byId) return byId;

  const byExact = pickTier(candidates.filter(a => a.label === target));
  if (byExact) return byExact;

  const lower = target.toLowerCase();
  const byCi = pickTier(candidates.filter(a => String(a.label ?? '').toLowerCase() === lower));
  if (byCi) return byCi;

  const sanitized = sanitizeLabel(target, '');
  if (sanitized) {
    const bySanitized = pickTier(candidates.filter(a => {
      const accLabel = String(a.label ?? '');
      return accLabel.toLowerCase() === sanitized || sanitizeLabel(accLabel, '') === sanitized;
    }));
    if (bySanitized) return bySanitized;
  }

  const suffix = provider ? ` for provider "${provider}"` : '';
  throw new CloudAccountsError(`Account "${target}"${suffix} was not found. Run pdd accounts list.`, { code: 'not_found' });
}

async function leaseAndSyncAfterEnroll(provider, acc, fallbackLabel, _fallbackAuthJson, _fallbackOauthToken, { cwd, env }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
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
      return { materialized: Boolean(hasLocalMaterializedFile(fs, provider, env)) };
    }
    if (leased?.state === 'leased' && isReauthRequiredAccount(leased.account)) {
      markLocalAccountReauthRequired(leased.account?.account_id ?? acc.account_id, { env }, ports);
      return { materialized: false };
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
    return { materialized: false };
  } catch {
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
          expires_at: new Date(nowMs + 5 * 60 * 1000).toISOString(),
          last_refresh_at: acc.last_refresh_at ?? new Date(nowMs).toISOString(),
          materialized_local: false,
          delivery_mode: 'gateway_grant',
          five_hour_used_percent: acc.five_hour_used_percent ?? null,
          five_hour_reset_at: acc.five_hour_reset_at ?? null,
          weekly_used_percent: acc.weekly_used_percent ?? null,
          weekly_reset_at: acc.weekly_reset_at ?? null,
        },
      },
      cooling: current.cooling,
    }, { env }, ports);
    return { materialized: false };
  }
}

function extractIsolatedClaudeSetupToken(fs, tempClaudeDir, loginOutput, nowFn) {
  const nowMs = (typeof nowFn === 'function' ? nowFn : Date.now)();
  if (typeof loginOutput === 'string' && loginOutput.trim()) {
    const fromOutput = parseClaudeTokenText(loginOutput, 'claude setup-token output', nowMs, { allowBareToken: false });
    if (fromOutput) return fromOutput;
  }
  if (tempClaudeDir) {
    try {
      const fromTempDir = readClaudeTokenFromPath(fs, tempClaudeDir, { now: nowFn });
      if (fromTempDir) return fromTempDir;
    } catch (err) {
      if (err instanceof CloudAccountsError && err.code === 'expired_local_login') throw err;
    }
  }
  throw new CloudAccountsError(
    'No Claude OAuth token found in claude setup-token output. Run "pdd accounts add --provider claude" in an interactive terminal and complete the browser sign-in.',
    { code: 'missing_local_login' },
  );
}

function isDuplicateLabelConflictError(err) {
  if (!(err instanceof CloudAccountsError)) return false;
  if (err.status === 409) return true;
  return /duplicate[_ ]label|label.*already exists|already exists.*label/i.test(`${err.code ?? ''} ${err.message ?? ''}`);
}

function isTransientUploadError(err) {
  if (!(err instanceof CloudAccountsError)) return false;
  return err.code === 'timeout' || err.code === 'network_error' || err.status === 429 || err.status >= 500;
}

function assertValidUploadBundle(provider, bundle) {
  if (provider === 'codex') {
    const tokens = bundle?.auth_json?.tokens;
    for (const key of ['access_token', 'refresh_token', 'id_token', 'account_id']) {
      if (typeof tokens?.[key] !== 'string' || !tokens[key].trim()) {
        throw new CloudAccountsError(`Invalid local Codex credential bundle: missing ${key}.`, { code: 'invalid_local_login' });
      }
    }
    return;
  }
  if (typeof bundle?.oauth_token !== 'string' || !bundle.oauth_token.trim()) {
    throw new CloudAccountsError('Invalid local Claude OAuth token.', { code: 'invalid_local_login' });
  }
}

function formatDeletedAccountRecoverySummary(backup, provider, sourceHint = null) {
  if (!backup) return '';
  const shareNote = backup.shares.length
    ? ` (preserved shares: --with ${backup.shares.join(',')})`
    : '';
  const sourceNote = sourceHint ? ` Local credential file "${sourceHint}" was left unscrubbed.` : '';
  return ` Previous ${provider} account "${backup.label}" (${backup.account_id}) was removed before the replacement upload failed${shareNote}.${sourceNote} Re-run enroll/import to restore "${backup.label}".`;
}

async function uploadAccountWithConflictAndRetry({
  provider,
  initialLabel,
  baseLabel,
  labelWasExplicit,
  replace = false,
  plan,
  bundle,
  sharePayloads,
  sourceHint = null,
  knownAccounts = null,
  knownPendingInvites = [],
  usedLabels = null,
  interactive = false,
  cwd,
  env,
  stdin,
  stdout,
}, ports = {}) {
  assertValidUploadBundle(provider, bundle);
  let candidateLabel = initialLabel;
  let cachedAccounts = Array.isArray(knownAccounts) ? knownAccounts : null;
  let cachedInvites = Array.isArray(knownPendingInvites) ? knownPendingInvites : [];
  const labelSet = usedLabels instanceof Set ? usedLabels : new Set();
  let inheritedShares = [];
  let deletedExistingId = null;
  let deletedBackup = null;

  const ensureAccountsLoaded = async () => {
    if (!cachedAccounts) {
      try {
        const fetched = await fetchAccountsList({ cwd, env, refresh: false }, ports);
        cachedAccounts = fetched.accounts;
        cachedInvites = fetched.pendingInvites;
      } catch {
        cachedAccounts = [];
      }
    }
    for (const item of cachedAccounts) {
      if (item && !item.revoked && item.provider === provider && item.label) {
        labelSet.add(String(item.label).toLowerCase());
      }
    }
    return cachedAccounts;
  };

  const findExistingOwnedSameLabel = label => (cachedAccounts ?? []).find(
    a => isOwnedAccount(a) && a.provider === provider && String(a.label ?? '').toLowerCase() === String(label).toLowerCase(),
  );

  const deleteConfirmedExisting = async existingOwned => {
    inheritedShares = mergeSharePayloads(inheritedShares, extractSharePayloadsFromAccount(existingOwned, cachedInvites));
    await cloudAccountsRequest('DELETE', `/v1/accounts/${encodeURIComponent(existingOwned.account_id)}`, { cwd, env }, ports);
    deletedExistingId = existingOwned.account_id;
    deletedBackup = {
      account_id: existingOwned.account_id,
      label: existingOwned.label ?? candidateLabel,
      shares: inheritedShares.map(s => s.display),
    };
    cachedAccounts = (cachedAccounts ?? []).filter(a => a.account_id !== existingOwned.account_id);
  };

  if (replace && Array.isArray(cachedAccounts)) {
    const prior = findExistingOwnedSameLabel(candidateLabel);
    if (prior) inheritedShares = extractSharePayloadsFromAccount(prior, cachedInvites);
  }

  for (let attempt = 0; attempt < 12; attempt += 1) {
    try {
      const created = await cloudAccountsRequest('POST', '/v1/accounts', {
        body: {
          label: candidateLabel,
          provider,
          plan,
          bundle,
        },
        cwd,
        env,
      }, ports);
      deletedBackup = null;

      if (replace && created?.already_enrolled !== true) {
        await ensureAccountsLoaded();
        const prior = findExistingOwnedSameLabel(candidateLabel);
        const createdId = created?.account?.account_id ?? created?.account_id ?? null;
        if (prior && prior.account_id && prior.account_id !== deletedExistingId && prior.account_id !== createdId) {
          inheritedShares = mergeSharePayloads(inheritedShares, extractSharePayloadsFromAccount(prior, cachedInvites));
          await cloudAccountsRequest('DELETE', `/v1/accounts/${encodeURIComponent(prior.account_id)}`, { cwd, env }, ports).catch(() => {});
          deletedExistingId = prior.account_id;
          cachedAccounts = (cachedAccounts ?? []).filter(a => a.account_id !== prior.account_id);
        }
      }

      return {
        skipped: false,
        created,
        candidateLabel,
        effectiveSharePayloads: mergeSharePayloads(inheritedShares, sharePayloads),
        pendingInvites: cachedInvites,
      };
    } catch (err) {
      if (isDuplicateLabelConflictError(err)) {
        await ensureAccountsLoaded();
        labelSet.add(candidateLabel.toLowerCase());
        const existingOwned = findExistingOwnedSameLabel(candidateLabel);

        if (replace && existingOwned && existingOwned.account_id !== deletedExistingId) {
          await deleteConfirmedExisting(existingOwned);
          continue;
        }

        if (!labelWasExplicit) {
          candidateLabel = nextDisambiguatedLabel(baseLabel || candidateLabel, labelSet);
          continue;
        }

        if (interactive) {
          const disambiguated = nextDisambiguatedLabel(baseLabel || candidateLabel, labelSet);
          const choice = await askPromptRaw(
            `Account label "${candidateLabel}" already exists for ${provider}. [r]eplace existing, save as "${disambiguated}", or [s]kip? [r/2/s] `,
            { stdin, stdout },
            ports,
          );
          const norm = choice === undefined || choice === null ? 's' : String(choice).trim().toLowerCase();
          if ((norm === 'r' || norm === 'replace') && existingOwned && existingOwned.account_id !== deletedExistingId) {
            await deleteConfirmedExisting(existingOwned);
            continue;
          }
          if (norm === '2' || norm === 'd' || norm === 'n' || norm === 'new' || norm === 'y' || norm === 'yes' || norm === '') {
            candidateLabel = disambiguated;
            continue;
          }
          if (norm === 's' || norm === 'skip' || choice === false) {
            return {
              skipped: true,
              candidateLabel,
              message: `Skipped enrolling ${provider} account "${candidateLabel}".`,
            };
          }
          const customLabel = sanitizeLabel(norm, '');
          if (customLabel && !labelSet.has(customLabel.toLowerCase())) {
            candidateLabel = customLabel;
            continue;
          }
          candidateLabel = disambiguated;
          continue;
        }

        const hint = /--replace/.test(err.message) ? '' : ' Pass --replace to replace the existing account.';
        throw new CloudAccountsError(`${err.message}${hint}`, {
          status: err.status || 409,
          code: err.code || 'duplicate_label',
          payload: err.payload,
        });
      }

      if (interactive && isTransientUploadError(err)) {
        const retryAns = await askPromptRaw(
          `Upload failed (${err.message}). [R]etry upload without signing in again, or [s]kip? [R/s] `,
          { stdin, stdout },
          ports,
        );
        if (retryAns === false || retryAns === undefined || retryAns === null) {
          return {
            skipped: true,
            candidateLabel,
            message: `Skipped ${provider} account "${candidateLabel}" after upload failure.${formatDeletedAccountRecoverySummary(deletedBackup, provider, sourceHint)}`,
          };
        }
        const normRetry = String(retryAns).trim().toLowerCase();
        if (normRetry === 's' || normRetry === 'skip' || normRetry === 'n' || normRetry === 'no') {
          return {
            skipped: true,
            candidateLabel,
            message: `Skipped ${provider} account "${candidateLabel}" after upload failure.${formatDeletedAccountRecoverySummary(deletedBackup, provider, sourceHint)}`,
          };
        }
        continue;
      }

      if (deletedBackup) {
        throw new CloudAccountsError(
          `${err.message}${formatDeletedAccountRecoverySummary(deletedBackup, provider, sourceHint)}`,
          { status: err.status, code: err.code, payload: err.payload, exitCode: err.exitCode },
        );
      }
      throw err;
    }
  }
  throw new CloudAccountsError(
    `Unable to enroll ${provider} account "${candidateLabel}" after multiple attempts.${formatDeletedAccountRecoverySummary(deletedBackup, provider, sourceHint)}`,
    { code: 'enroll_failed' },
  );
}

function formatShareSuffix(shareNotes) {
  if (!shareNotes.length) return '';
  const formatted = shareNotes.map(n => {
    if (n.inviteId) return `${n.display} (invite ${n.inviteId})`;
    if (n.alreadyShared) return `${n.display} (already shared)`;
    return n.display;
  });
  return ` Shared with ${formatted.join(', ')}.`;
}

async function enrollSingleIteration(mode, {
  provider,
  requestedLabel = null,
  replace = false,
  fromOption = null,
  deviceAuth = false,
  sharePayloads = [],
  loopState = null,
  cwd,
  env,
  stdin,
}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const stdout = ports.stdout ?? process.stdout;
  const promptFn = ports.prompt ?? ports.confirm ?? null;
  const interactive = Boolean(loopState) || Boolean(promptFn) || Boolean(stdin?.isTTY && stdout?.isTTY);

  if (provider === 'codex') {
    let tempLoginDir = null;
    try {
      let authJson;
      let bundle;
      let probeCodexHome = null;
      let importSourcePath = null;

      if (mode === 'add') {
        tempLoginDir = createTempPrivateDir(fs, 'pdd-codex-login-', ports.tmpRoot, env);
        const loginEnv = { ...env, CODEX_HOME: tempLoginDir };
        const loginRes = await runProviderLogin('codex', { cwd, env: loginEnv, deviceAuth, stdin }, ports);
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
        const resolvedImportAuth = assertNonSymlinkImportFile(fs, importSource.authPath, env);
        ({ authJson, bundle } = readCodexFullAuthBundle(fs, env, resolvedImportAuth));
        probeCodexHome = importSource.probeCodexHome;
        importSourcePath = importSource.authPath;
      }

      const email = extractCodexEmail(authJson);
      const emailBase = deriveEmailBaseLabel(authJson);
      const subjectAccountId = bundle.auth_json.tokens.account_id;
      const seenLabel = loopState ? (loopState.bySubjectId.get(subjectAccountId) ?? null) : null;
      const labelWasExplicit = Boolean(requestedLabel && String(requestedLabel).trim()) || Boolean(loopState?.hasExplicitPrefix);

      let knownAccounts = loopState?.knownAccounts ?? null;
      let knownPendingInvites = loopState?.knownPendingInvites ?? [];
      const usedLabels = loopState ? loopState.usedLabels : new Set();

      let baseLabel;
      let candidateLabel;
      if (loopState) {
        if (seenLabel) {
          baseLabel = seenLabel;
          candidateLabel = seenLabel;
        } else if (loopState.hasExplicitPrefix) {
          candidateLabel = loopState.peekNextNumberedLabel();
          baseLabel = candidateLabel;
        } else if (emailBase) {
          baseLabel = emailBase;
          candidateLabel = replace
            ? nextDisambiguatedLabel(emailBase, loopState.sessionEnrolledLabels)
            : nextDisambiguatedLabel(emailBase, usedLabels);
        } else {
          candidateLabel = loopState.peekNextNumberedLabel();
          baseLabel = candidateLabel;
        }
      } else if (requestedLabel && String(requestedLabel).trim()) {
        baseLabel = sanitizeLabel(requestedLabel, '');
        candidateLabel = baseLabel;
      } else {
        baseLabel = defaultAccountLabel('codex', authJson);
        if (!replace && emailBase) {
          try {
            const listed = await fetchAccountsList({ cwd, env, refresh: false }, ports);
            knownAccounts = listed.accounts;
            knownPendingInvites = listed.pendingInvites;
            for (const item of knownAccounts) {
              if (item && !item.revoked && item.provider === 'codex' && item.label) {
                usedLabels.add(String(item.label).toLowerCase());
              }
            }
            candidateLabel = nextDisambiguatedLabel(emailBase, usedLabels);
          } catch {
            candidateLabel = baseLabel;
          }
        } else {
          candidateLabel = baseLabel;
        }
      }
      if (!candidateLabel) return { exitCode: 2, message: 'Provide a valid --label NAME.' };

      const upload = await uploadAccountWithConflictAndRetry({
        provider: 'codex',
        initialLabel: candidateLabel,
        baseLabel,
        labelWasExplicit,
        replace,
        plan: detectCodexPlan(authJson),
        bundle,
        sharePayloads,
        sourceHint: importSourcePath,
        knownAccounts,
        knownPendingInvites,
        usedLabels,
        interactive,
        cwd,
        env,
        stdin,
        stdout,
      }, ports);

      if (upload.skipped) {
        return { exitCode: 0, skipped: true, label: upload.candidateLabel, message: upload.message };
      }

      const { created, effectiveSharePayloads, pendingInvites: uploadInvites } = upload;
      candidateLabel = upload.candidateLabel;
      let acc = created?.account ?? { account_id: created?.account_id ?? candidateLabel, label: candidateLabel, provider: 'codex' };
      const isDuplicate = Boolean(
        created?.already_enrolled === true
        || seenLabel
        || (loopState && acc.account_id && loopState.seenAccountIds.has(acc.account_id)),
      );

      acc = await probeInitialCodexUsageIfUnpopulated(acc, authJson, probeCodexHome, { fs, cwd, env }, ports);

      // Zero-plaintext guarantee (#3497): wipe temporary plaintext OAuth login directory immediately after Cloud upload + usage probe.
      if (tempLoginDir) {
        removeTempPrivateDir(fs, tempLoginDir);
        tempLoginDir = null;
      }

      const leaseResult = await leaseAndSyncAfterEnroll('codex', acc, candidateLabel, null, null, { cwd, env }, ports);
      const leaseMaterialized = leaseResult?.materialized === true;

      // P0 single-use OpenAI refresh_token collision guard: scrub tokens.refresh_token from
      // the imported local source file ONLY when local lease materialization succeeded.
      const scrubbedSource = mode === 'import' && importSourcePath && leaseMaterialized
        ? scrubImportedCodexSourceRefreshToken(fs, importSourcePath, env)
        : false;
      if (scrubbedSource) {
        const sourceCodexHome = dirname(importSourcePath);
        const managedHome = pddManagedCodexHome(env);
        let sameHome = resolve(sourceCodexHome) === resolve(managedHome);
        if (!sameHome) {
          try {
            const realFn = fs.realpathSync?.native ?? fs.realpathSync;
            if (typeof realFn === 'function') {
              sameHome = realFn.call(fs, sourceCodexHome) === realFn.call(fs, managedHome);
            }
          } catch {}
        }
        if (!sameHome) {
          stopCodexAppServerDaemon(sourceCodexHome, { env, fs, spawnSync: ports.spawnSync });
        }
      }

      const finalLabel = acc.label ?? candidateLabel;
      if (loopState) {
        if (subjectAccountId) loopState.bySubjectId.set(subjectAccountId, finalLabel);
        if (acc.account_id) loopState.seenAccountIds.add(acc.account_id);
        if (!isDuplicate) {
          loopState.commitCandidateLabel(candidateLabel, finalLabel, Boolean(loopState.hasExplicitPrefix || !emailBase));
        }
      }

      const shareNotes = effectiveSharePayloads.length
        ? await applySharePayloadsToAccounts([acc], effectiveSharePayloads, {
            cwd,
            env,
            pendingInvites: uploadInvites,
            sessionSharedKeys: loopState?.sharedKeys ?? null,
          }, ports)
        : [];
      const shareSuffix = formatShareSuffix(shareNotes);

      if (isDuplicate) {
        return {
          exitCode: 0,
          duplicate: true,
          account: acc,
          label: finalLabel,
          email,
          shareNotes,
          message: `Already enrolled as ${finalLabel} — refreshed credentials. Existing shares remain active.${shareSuffix}`,
        };
      }
      const identityNote = email ? `${email} -> "${finalLabel}", ` : '';
      const materializationNote = leaseMaterialized
        ? `materialized in ${pddManagedCodexHome(env)}`
        : `lease pending for ${pddManagedCodexHome(env)}`;
      const importNote = scrubbedSource
        ? ` (scrubbed single-use refresh_token from ${importSourcePath} so local codex cannot invalidate Cloud refresh.)`
        : (mode === 'import' && importSourcePath && !leaseMaterialized
          ? ` (left ${importSourcePath} unscrubbed because local lease materialization did not complete.)`
          : '');
      return {
        exitCode: 0,
        duplicate: false,
        account: acc,
        label: finalLabel,
        email,
        shareNotes,
        message: `Enrolled Codex account "${finalLabel}" in PDD Cloud (${identityNote}${materializationNote}).${shareSuffix}${importNote}`,
      };
    } finally {
      removeTempPrivateDir(fs, tempLoginDir);
    }
  }

  // Claude enrollment / import
  let oauthToken = '';
  let tempClaudeDir = null;
  try {
    if (mode === 'add') {
      const piped = !loopState ? await readStdinString(stdin) : '';
      if (piped.trim()) {
        oauthToken = extractIsolatedClaudeSetupToken(fs, null, piped, ports.now);
      } else {
        tempClaudeDir = createTempPrivateDir(fs, 'pdd-claude-login-', ports.tmpRoot, env);
        const claudeLoginEnv = { ...env, CLAUDE_CONFIG_DIR: tempClaudeDir, COLUMNS: env?.COLUMNS || '500' };
        delete claudeLoginEnv.CLAUDE_CODE_OAUTH_TOKEN;
        const loginRes = await runProviderLogin('claude', { cwd, env: claudeLoginEnv, deviceAuth: false, stdin }, ports);
        if (!loginRes || loginRes.code !== 0) {
          return {
            exitCode: 1,
            aborted: loginRes?.code === 130 || loginRes?.signal === 'SIGINT',
            message: 'claude setup-token did not complete.',
          };
        }
        const loginOutput = `${loginRes?.stdout ?? ''}\n${loginRes?.stderr ?? ''}`;
        oauthToken = extractIsolatedClaudeSetupToken(fs, tempClaudeDir, loginOutput, ports.now);
        removeTempPrivateDir(fs, tempClaudeDir);
        tempClaudeDir = null;
      }
    } else if (fromOption) {
      oauthToken = readClaudeTokenFromPath(fs, resolve(cwd, String(fromOption).trim()), { now: ports.now });
    } else {
      const loginOutput = await readStdinString(stdin);
      oauthToken = readLocalClaudeToken(fs, env, loginOutput, { now: ports.now });
    }
  } finally {
    removeTempPrivateDir(fs, tempClaudeDir);
  }

  const labelWasExplicit = Boolean(requestedLabel && String(requestedLabel).trim()) || Boolean(loopState?.hasExplicitPrefix);
  let baseLabel;
  let candidateLabel;
  if (loopState) {
    candidateLabel = loopState.peekNextNumberedLabel();
    baseLabel = candidateLabel;
  } else {
    baseLabel = requestedLabel ? sanitizeLabel(requestedLabel, '') : defaultAccountLabel('claude');
    candidateLabel = baseLabel;
  }
  if (!candidateLabel) return { exitCode: 2, message: 'Provide a valid --label NAME.' };

  const upload = await uploadAccountWithConflictAndRetry({
    provider: 'claude',
    initialLabel: candidateLabel,
    baseLabel,
    labelWasExplicit,
    replace,
    plan: 'max',
    bundle: { oauth_token: oauthToken },
    sharePayloads,
    knownAccounts: loopState?.knownAccounts ?? null,
    knownPendingInvites: loopState?.knownPendingInvites ?? [],
    usedLabels: loopState?.usedLabels ?? null,
    interactive,
    cwd,
    env,
    stdin,
    stdout,
  }, ports);

  if (upload.skipped) {
    return { exitCode: 0, skipped: true, label: upload.candidateLabel, message: upload.message };
  }

  const { created, effectiveSharePayloads, pendingInvites: uploadInvites } = upload;
  candidateLabel = upload.candidateLabel;
  const acc = created?.account ?? { account_id: created?.account_id ?? candidateLabel, label: candidateLabel, provider: 'claude' };
  const isDuplicate = Boolean(
    created?.already_enrolled === true
    || (loopState && acc.account_id && loopState.seenAccountIds.has(acc.account_id)),
  );

  await leaseAndSyncAfterEnroll('claude', acc, candidateLabel, null, null, { cwd, env }, ports);

  const finalLabel = acc.label ?? candidateLabel;
  if (loopState) {
    if (acc.account_id) loopState.seenAccountIds.add(acc.account_id);
    if (!isDuplicate) loopState.commitCandidateLabel(candidateLabel, finalLabel, true);
  }

  const shareNotes = effectiveSharePayloads.length
    ? await applySharePayloadsToAccounts([acc], effectiveSharePayloads, {
        cwd,
        env,
        pendingInvites: uploadInvites,
        sessionSharedKeys: loopState?.sharedKeys ?? null,
      }, ports)
    : [];
  const shareSuffix = formatShareSuffix(shareNotes);

  if (isDuplicate) {
    return {
      exitCode: 0,
      duplicate: true,
      account: acc,
      label: finalLabel,
      shareNotes,
      message: `Already enrolled as ${finalLabel} — refreshed credentials. Existing shares remain active.${shareSuffix}`,
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
  replace = false,
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
      replace,
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

  const hasExplicitPrefix = Boolean(requestedLabel && String(requestedLabel).trim());
  const prefix = sanitizeLabel(requestedLabel || provider, provider);
  const { accounts: initialAccounts, pendingInvites: initialInvites } = await fetchAccountsList({ cwd, env, refresh: false }, ports);
  const usedLabels = new Set();
  const seenAccountIds = new Set();
  for (const existing of initialAccounts) {
    if (!existing || existing.revoked) continue;
    if (existing.provider === provider && existing.label) {
      usedLabels.add(String(existing.label).toLowerCase());
    }
    if (existing.account_id) seenAccountIds.add(existing.account_id);
  }

  let counter = 1;
  const loopState = {
    hasExplicitPrefix,
    knownAccounts: initialAccounts,
    knownPendingInvites: initialInvites,
    usedLabels,
    sessionEnrolledLabels: new Set(),
    bySubjectId: new Map(),
    seenAccountIds,
    sharedKeys: new Set(),
    peekNextNumberedLabel() {
      while (!replace && usedLabels.has(`${prefix}-${counter}`.toLowerCase())) counter += 1;
      return `${prefix}-${counter}`;
    },
    commitCandidateLabel(candidate, actual, advanceCounter = true) {
      const candLower = String(candidate).toLowerCase();
      usedLabels.add(candLower);
      this.sessionEnrolledLabels.add(candLower);
      if (actual) {
        const actLower = String(actual).toLowerCase();
        usedLabels.add(actLower);
        this.sessionEnrolledLabels.add(actLower);
      }
      if (advanceCounter) counter += 1;
    },
  };

  const streamedLive = !promptFn && Boolean(stdin?.isTTY && stdout?.isTTY);
  const iterationMessages = [];
  const enrolledLabels = [];
  const refreshedLabels = [];

  for (let iteration = 0; ; iteration += 1) {
    const labelHint = hasExplicitPrefix ? `prefix "${prefix}"` : 'auto-label from account';
    const banner = `--- Account #${iteration + 1} (${provider}, ${labelHint}, ${enrolledLabels.length} enrolled so far) ---`;
    if (streamedLive) {
      stdout.write(`\n${banner}\n`);
    }

    const step = await enrollSingleIteration('add', {
      provider,
      requestedLabel: null,
      replace,
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
      iterationMessages.push(banner, step.message);
      break;
    }

    if (!step.skipped) {
      if (step.duplicate) {
        if (!refreshedLabels.includes(step.label) && !enrolledLabels.includes(step.label)) {
          refreshedLabels.push(step.label);
        }
      } else if (!enrolledLabels.includes(step.label)) {
        enrolledLabels.push(step.label);
      }
    }

    if (streamedLive) {
      stdout.write(`${redactSecrets(step.message)}\n`);
    } else {
      iterationMessages.push(banner, step.message);
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
      return Boolean(fs.statSync(managedClaudeSettingsPath(env))?.isFile());
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
      let cachedMarkedReauth = false;
      if (isReauthRequiredFailure(error)) {
        const explicitId = error?.payload?.account_id
          ?? error?.payload?.detail?.account_id
          ?? error?.payload?.account?.account_id
          ?? null;
        if (typeof explicitId === 'string' && explicitId) {
          markLocalAccountReauthRequired(explicitId, { env }, ports);
          if (explicitId === cached?.account_id) cachedMarkedReauth = true;
        }
      }
      if (
        provider === 'codex'
        && !codexHealthyHome
        && cached?.account_id
        && !isRevokedCached
        && !cachedMarkedReauth
        && !isReauthRequiredFailure(error)
        && Number.isFinite(expiresMs)
        && expiresMs > now
      ) {
        try {
          if (fs.statSync(managedCodexAuthPath(env))?.isFile()) {
            codexHealthyHome = pddManagedCodexHome(env);
          }
        } catch {}
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
        writeAtomicPreservingSymlinkAndMode(fs, entry.path, updated, { defaultMode: 0o644 });
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
      if (updated !== current) {
        writeAtomicPreservingSymlinkAndMode(fs, entry.path, updated, { defaultMode: 0o644 });
      }
    }
    restoreLocalClaudeGatewayConfig({ env }, ports);
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
  if (!nextActive.claude) {
    restoreLocalClaudeGatewayConfig({ env }, ports);
  } else {
    restoreLocalClaudeGatewayConfig({ env, removeManagedFile: false }, ports);
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
        active: withLeftPercentActiveMap(current.active),
        cooling: current.cooling,
        reauth_required: reauthRequired,
        accounts: accessible.map(a => withLeftPercentFields({
          ...a,
          state: accountDisplayState(a, current.active?.[a.provider], current.reauth),
        })),
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
  if (!nextActive.claude) {
    restoreLocalClaudeGatewayConfig({ env }, ports);
  } else {
    restoreLocalClaudeGatewayConfig({ env, removeManagedFile: false }, ports);
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

const CODEX_VALUE_OPTIONS = new Set([
  '-c', '--config', '--enable', '--disable', '--remote', '--remote-auth-token-env',
  '-i', '--image', '-m', '--model', '--local-provider', '-p', '--profile',
  '-s', '--sandbox', '-C', '--cd', '--add-dir', '-a', '--ask-for-approval',
  '--color', '-o', '--output-last-message',
]);

const CODEX_PRESERVED_VALUE_OPTIONS = new Set([
  '-c', '--config', '--enable', '--disable', '--remote', '--remote-auth-token-env',
  '-i', '--image', '-m', '--model', '--local-provider', '-p', '--profile',
  '-s', '--sandbox', '-C', '--cd', '--add-dir', '-a', '--ask-for-approval',
]);

const CODEX_PRESERVED_FLAG_OPTIONS = new Set([
  '--oss', '--strict-config', '--approve-for-me',
  '--dangerously-bypass-approvals-and-sandbox', '--yolo', '--dangerously-bypass-hook-trust',
  '--worktree', '--search', '--no-alt-screen', '--no-daemon', '--include-non-interactive',
]);

const CODEX_NON_INTERACTIVE_SUBCOMMANDS = new Set([
  'agents', 'exec', 'e', 'review', 'login', 'logout', 'mcp', 'mcp-server',
  'plugin', 'app-server', 'remote-control', 'app', 'completion', 'update',
  'doctor', 'sandbox', 'debug', 'apply', 'a', 'queue', 'archive', 'delete',
  'migrate-rollouts', 'migrate-nfs-db', 'unarchive', 'cloud', 'exec-server',
  'features', 'help',
]);

const CODEX_INTERACTIVE_SUBCOMMANDS = new Set(['resume', 'fork']);
const UUID_TOKEN_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
const OUTPUT_SESSION_ID_RE = /(?:session[_\s-]*id|thread[_\s-]*id|conversation[_\s-]*id)["'\s:=]+([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})/i;
const ROLLOUT_FILE_RE = /^rollout-.*\.jsonl$/i;
const ROLLOUT_UUID_FILE_RE = /([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})\.jsonl$/i;
const QUOTA_ERROR_CODES = new Set([
  'usage_limit_exceeded',
  'usage_limit_reached',
  'insufficient_quota',
  'quota_exceeded',
  'out_of_credits',
  'billing_hard_limit_reached',
]);

const PYTHON_PTY_SUPERVISOR_SCRIPT = [
  'import errno, fcntl, os, pty, select, signal, struct, sys, termios, time',
  'initial_ppid = os.getppid()',
  'rows = int(os.environ.get("PDD_PTY_ROWS", "24") or "24")',
  'cols = int(os.environ.get("PDD_PTY_COLS", "80") or "80")',
  'master_fd, slave_fd = pty.openpty()',
  'try:',
  '    fcntl.ioctl(slave_fd, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, 0, 0))',
  'except Exception:',
  '    pass',
  'pid = os.fork()',
  'if pid == 0:',
  '    os.close(master_fd)',
  '    try:',
  '        os.close(3)',
  '    except Exception:',
  '        pass',
  '    os.setsid()',
  '    try:',
  '        fcntl.ioctl(slave_fd, termios.TIOCSCTTY, 0)',
  '    except Exception:',
  '        pass',
  '    os.dup2(slave_fd, 0)',
  '    os.dup2(slave_fd, 1)',
  '    os.dup2(slave_fd, 2)',
  '    if slave_fd > 2:',
  '        os.close(slave_fd)',
  '    os.execvp(sys.argv[1], sys.argv[1:])',
  'os.close(slave_fd)',
  'ctrl_open = True',
  'try:',
  '    fcntl.fcntl(3, fcntl.F_GETFD)',
  'except OSError:',
  '    ctrl_open = False',
  'def _killpg_safe(sig):',
  '    try:',
  '        os.killpg(pid, sig)',
  '        return True',
  '    except ProcessLookupError:',
  '        return False',
  '    except Exception:',
  '        try:',
  '            os.kill(pid, sig)',
  '            return True',
  '        except ProcessLookupError:',
  '            return False',
  '        except Exception:',
  '            return False',
  'stop_requested = False',
  'def _fwd(signum, _frame):',
  '    global stop_requested',
  '    _killpg_safe(signum)',
  '    if signum in (signal.SIGTERM, signal.SIGHUP):',
  '        stop_requested = True',
  'for _s in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):',
  '    signal.signal(_s, _fwd)',
  'reaped_status = None',
  'def _terminate_child_group():',
  '    global reaped_status',
  '    if reaped_status is not None:',
  '        return',
  '    if not _killpg_safe(signal.SIGTERM):',
  '        return',
  '    deadline = time.monotonic() + 0.5',
  '    while time.monotonic() < deadline:',
  '        try:',
  '            wpid, st = os.waitpid(pid, os.WNOHANG)',
  '            if wpid == pid:',
  '                reaped_status = st',
  '                return',
  '        except ChildProcessError:',
  '            reaped_status = 0',
  '            return',
  '        time.sleep(0.02)',
  '    _killpg_safe(signal.SIGKILL)',
  'def _drain_master_nonblocking():',
  '    while True:',
  '        try:',
  '            rdy, _, _ = select.select([master_fd], [], [], 0)',
  '            if not rdy:',
  '                break',
  '            chunk = os.read(master_fd, 16384)',
  '            if not chunk:',
  '                break',
  '            os.write(1, chunk)',
  '        except Exception:',
  '            break',
  'stdin_open = True',
  'ctrl_buf = b""',
  'while True:',
  '    if stop_requested or os.getppid() == 1 or os.getppid() != initial_ppid:',
  '        _terminate_child_group()',
  '        break',
  '    watch = [master_fd] + ([0] if stdin_open else []) + ([3] if ctrl_open else [])',
  '    try:',
  '        rlist, _, _ = select.select(watch, [], [], 0.2)',
  '    except InterruptedError:',
  '        continue',
  '    except Exception:',
  '        _terminate_child_group()',
  '        break',
  '    if master_fd in rlist:',
  '        try:',
  '            data = os.read(master_fd, 16384)',
  '        except OSError as exc:',
  '            if exc.errno == errno.EIO:',
  '                break',
  '            raise',
  '        if not data:',
  '            break',
  '        os.write(1, data)',
  '    if ctrl_open and 3 in rlist:',
  '        try:',
  '            cdata = os.read(3, 4096)',
  '        except OSError:',
  '            cdata = b""',
  '        if not cdata:',
  '            ctrl_open = False',
  '            _terminate_child_group()',
  '            break',
  '        ctrl_buf += cdata',
  '        while b"\\n" in ctrl_buf:',
  '            line, ctrl_buf = ctrl_buf.split(b"\\n", 1)',
  '            parts = line.strip().split()',
  '            if len(parts) == 2:',
  '                try:',
  '                    r_val, c_val = int(parts[0]), int(parts[1])',
  '                    if r_val > 0 and c_val > 0:',
  '                        fcntl.ioctl(master_fd, termios.TIOCSWINSZ, struct.pack("HHHH", r_val, c_val, 0, 0))',
  '                        _killpg_safe(signal.SIGWINCH)',
  '                except Exception:',
  '                    pass',
  '    if stdin_open and 0 in rlist:',
  '        try:',
  '            inp = os.read(0, 16384)',
  '        except OSError:',
  '            inp = b""',
  '        if not inp:',
  '            stdin_open = False',
  '            _terminate_child_group()',
  '            break',
  '        else:',
  '            try:',
  '                os.write(master_fd, inp)',
  '            except OSError:',
  '                break',
  '_drain_master_nonblocking()',
  'try:',
  '    os.close(master_fd)',
  'except Exception:',
  '    pass',
  'if ctrl_open:',
  '    try:',
  '        os.close(3)',
  '    except Exception:',
  '        pass',
  'if reaped_status is None:',
  '    try:',
  '        _, reaped_status = os.waitpid(pid, 0)',
  '    except ChildProcessError:',
  '        reaped_status = 0',
  'if os.WIFSIGNALED(reaped_status):',
  '    sys.exit(128 + os.WTERMSIG(reaped_status))',
  'sys.exit(os.WEXITSTATUS(reaped_status))',
].join('\n');

function inspectCodexInvocation(args, baseCwd = process.cwd()) {
  let subcommand = '';
  let hasHelpOrVersion = false;
  let explicitSessionId = null;
  let afterSubcommand = false;
  let cdOverride = null;

  for (let i = 0; i < args.length; i += 1) {
    const word = String(args[i] ?? '');
    if (word === '--') break;
    if (word === '-h' || word === '--help' || word === '-V' || word === '--version') {
      hasHelpOrVersion = true;
      continue;
    }
    const eqIdx = word.indexOf('=');
    if (eqIdx > 0 && CODEX_VALUE_OPTIONS.has(word.slice(0, eqIdx))) {
      const flagName = word.slice(0, eqIdx);
      if (flagName === '-C' || flagName === '--cd') cdOverride = word.slice(eqIdx + 1);
      continue;
    }
    if (CODEX_VALUE_OPTIONS.has(word)) {
      if ((word === '-C' || word === '--cd') && i + 1 < args.length) {
        cdOverride = String(args[i + 1] ?? '');
      }
      i += 1;
      continue;
    }
    if (word.startsWith('-')) continue;
    if (!afterSubcommand) {
      if (CODEX_INTERACTIVE_SUBCOMMANDS.has(word) || CODEX_NON_INTERACTIVE_SUBCOMMANDS.has(word)) {
        subcommand = word;
        afterSubcommand = true;
        continue;
      }
      break;
    }
    if ((subcommand === 'resume' || subcommand === 'fork') && !explicitSessionId && UUID_TOKEN_RE.test(word)) {
      explicitSessionId = word;
      break;
    }
  }

  const effectiveCwd = cdOverride
    ? resolve(baseCwd || process.cwd(), cdOverride)
    : resolve(baseCwd || process.cwd());

  return {
    subcommand,
    isResume: subcommand === 'resume',
    isFork: subcommand === 'fork',
    interactive: !hasHelpOrVersion && (subcommand === '' || CODEX_INTERACTIVE_SUBCOMMANDS.has(subcommand)),
    explicitSessionId,
    effectiveCwd,
  };
}

function buildCodexResumeArgs(initialArgs, sessionId) {
  const preserved = [];
  for (let i = 0; i < initialArgs.length; i += 1) {
    const word = String(initialArgs[i] ?? '');
    if (word === '--') break;
    if (CODEX_PRESERVED_VALUE_OPTIONS.has(word)) {
      if (i + 1 < initialArgs.length) {
        preserved.push(word, String(initialArgs[i + 1]));
        i += 1;
      }
      continue;
    }
    const eqIdx = word.indexOf('=');
    if (eqIdx > 0 && CODEX_PRESERVED_VALUE_OPTIONS.has(word.slice(0, eqIdx))) {
      preserved.push(word);
      continue;
    }
    if (eqIdx > 0 && CODEX_VALUE_OPTIONS.has(word.slice(0, eqIdx))) {
      continue;
    }
    if (CODEX_VALUE_OPTIONS.has(word)) {
      i += 1;
      continue;
    }
    if (CODEX_PRESERVED_FLAG_OPTIONS.has(word)) {
      preserved.push(word);
    }
  }
  return sessionId
    ? ['resume', ...preserved, sessionId]
    : ['resume', ...preserved, '--last'];
}

function canonicalPathSafe(fs, targetPath) {
  if (!targetPath) return '';
  try {
    const realpath = fs.realpathSync ?? nativeFs.realpathSync;
    return realpath(targetPath);
  } catch {
    return resolve(targetPath);
  }
}

function pathsMatchCwd(fs, candidateCwd, expectedCwd) {
  if (!candidateCwd || !expectedCwd) return false;
  if (resolve(candidateCwd) === resolve(expectedCwd)) return true;
  return canonicalPathSafe(fs, candidateCwd) === canonicalPathSafe(fs, expectedCwd);
}

function safeFileSize(fs, filePath) {
  if (!filePath) return 0;
  try {
    const st = fs.statSync(filePath);
    return st?.isFile() ? st.size : 0;
  } catch {
    return 0;
  }
}

const MAX_ROLLOUT_HEADER_BYTES = 4 * 1024 * 1024;
const MAX_ROLLOUT_SLICE_BYTES = 2 * 1024 * 1024;

function readFirstJsonLine(fs, filePath) {
  let fd;
  try {
    if (typeof fs.openSync === 'function' && typeof fs.readSync === 'function' && typeof fs.closeSync === 'function') {
      fd = fs.openSync(filePath, 'r');
      const chunkBuf = Buffer.allocUnsafe(65_536);
      const parts = [];
      let offset = 0;
      let foundNewline = false;
      while (offset < MAX_ROLLOUT_HEADER_BYTES) {
        const toRead = Math.min(chunkBuf.length, MAX_ROLLOUT_HEADER_BYTES - offset);
        const bytesRead = fs.readSync(fd, chunkBuf, 0, toRead, offset);
        if (bytesRead <= 0) break;
        const slice = chunkBuf.subarray(0, bytesRead);
        const nlIdx = slice.indexOf(0x0a);
        if (nlIdx >= 0) {
          if (nlIdx > 0) parts.push(Buffer.from(slice.subarray(0, nlIdx)));
          foundNewline = true;
          break;
        }
        parts.push(Buffer.from(slice));
        offset += bytesRead;
      }
      if (!foundNewline) return null;
      const firstLine = (parts.length === 1 ? parts[0] : (parts.length === 0 ? Buffer.alloc(0) : Buffer.concat(parts)))
        .toString('utf8')
        .trim();
      if (!firstLine) return null;
      const parsed = JSON.parse(firstLine);
      return object(parsed) ? parsed : null;
    }
    const raw = fs.readFileSync(filePath, 'utf8');
    const nl = raw.indexOf('\n');
    if (nl < 0) return null;
    const firstLine = raw.slice(0, nl);
    if (Buffer.byteLength(firstLine, 'utf8') > MAX_ROLLOUT_HEADER_BYTES) return null;
    const trimmed = firstLine.trim();
    if (!trimmed) return null;
    const parsed = JSON.parse(trimmed);
    return object(parsed) ? parsed : null;
  } catch {
    return null;
  } finally {
    if (fd !== undefined) {
      try { fs.closeSync(fd); } catch {}
    }
  }
}

function readRolloutChunkFromOffset(fs, filePath, startOffset) {
  let fd;
  try {
    if (typeof fs.openSync === 'function' && typeof fs.fstatSync === 'function' && typeof fs.readSync === 'function' && typeof fs.closeSync === 'function') {
      fd = fs.openSync(filePath, 'r');
      const size = fs.fstatSync(fd).size;
      if (size <= startOffset) {
        return { status: 'empty', text: '', nextOffset: startOffset, eofSize: size };
      }
      const len = Math.min(size - startOffset, MAX_ROLLOUT_SLICE_BYTES);
      const buf = Buffer.allocUnsafe(len);
      let readTotal = 0;
      while (readTotal < len) {
        const n = fs.readSync(fd, buf, readTotal, len - readTotal, startOffset + readTotal);
        if (n <= 0) break;
        readTotal += n;
      }
      const validBuf = buf.subarray(0, readTotal);
      const lastNl = validBuf.lastIndexOf(0x0a);
      if (lastNl >= 0) {
        const completeBuf = validBuf.subarray(0, lastNl + 1);
        return {
          status: 'lines',
          text: completeBuf.toString('utf8'),
          nextOffset: startOffset + completeBuf.length,
          eofSize: size,
        };
      }
      if (size - startOffset <= MAX_ROLLOUT_SLICE_BYTES) {
        return { status: 'partial', text: '', nextOffset: startOffset, eofSize: size };
      }
      // Single JSONL line exceeds 2 MiB with no newline in the 2 MiB slice:
      // scan forward in 64 KiB chunks until the next newline so rolloutOffset never wedges.
      const scanBuf = Buffer.allocUnsafe(65_536);
      let pos = startOffset + readTotal;
      while (pos < size) {
        const n = fs.readSync(fd, scanBuf, 0, Math.min(scanBuf.length, size - pos), pos);
        if (n <= 0) break;
        const nl = scanBuf.subarray(0, n).indexOf(0x0a);
        if (nl >= 0) {
          return {
            status: 'skipped_oversized',
            text: '',
            nextOffset: pos + nl + 1,
            eofSize: size,
          };
        }
        pos += n;
      }
      return { status: 'partial', text: '', nextOffset: startOffset, eofSize: size };
    }
    const raw = Buffer.from(fs.readFileSync(filePath, 'utf8'), 'utf8');
    if (raw.length <= startOffset) {
      return { status: 'empty', text: '', nextOffset: startOffset, eofSize: raw.length };
    }
    const windowBuf = raw.subarray(startOffset, Math.min(raw.length, startOffset + MAX_ROLLOUT_SLICE_BYTES));
    const lastNl = windowBuf.lastIndexOf(0x0a);
    if (lastNl >= 0) {
      const completeBuf = windowBuf.subarray(0, lastNl + 1);
      return {
        status: 'lines',
        text: completeBuf.toString('utf8'),
        nextOffset: startOffset + completeBuf.length,
        eofSize: raw.length,
      };
    }
    if (raw.length - startOffset <= MAX_ROLLOUT_SLICE_BYTES) {
      return { status: 'partial', text: '', nextOffset: startOffset, eofSize: raw.length };
    }
    const nextNl = raw.indexOf(0x0a, startOffset + windowBuf.length);
    if (nextNl >= 0) {
      return {
        status: 'skipped_oversized',
        text: '',
        nextOffset: nextNl + 1,
        eofSize: raw.length,
      };
    }
    return { status: 'partial', text: '', nextOffset: startOffset, eofSize: raw.length };
  } catch {
    return { status: 'empty', text: '', nextOffset: startOffset, eofSize: startOffset };
  } finally {
    if (fd !== undefined) {
      try { fs.closeSync(fd); } catch {}
    }
  }
}

function collectRolloutFiles(fs, codexHomes, { minMtimeMs = null } = {}) {
  const homes = [...new Set(codexHomes.filter(Boolean))];
  const visitedDirs = new Set();
  const seenFiles = new Set();
  const files = [];

  const walkSessions = (dir, depth) => {
    if (depth > 4) return;
    const canonDir = canonicalPathSafe(fs, dir);
    if (!canonDir || visitedDirs.has(canonDir)) return;
    visitedDirs.add(canonDir);
    let entries = [];
    try { entries = fs.readdirSync(dir, { withFileTypes: true }); } catch { return; }
    for (const ent of entries) {
      const full = join(dir, ent.name);
      if (ent.isDirectory()) {
        walkSessions(full, depth + 1);
      } else if (ent.isFile() && ROLLOUT_FILE_RE.test(ent.name)) {
        try {
          const st = fs.statSync(full);
          if (typeof minMtimeMs === 'number' && Number.isFinite(minMtimeMs) && st.mtimeMs < minMtimeMs) {
            continue;
          }
          const canonFile = canonicalPathSafe(fs, full);
          if (seenFiles.has(canonFile)) continue;
          seenFiles.add(canonFile);
          const uuidMatch = ROLLOUT_UUID_FILE_RE.exec(ent.name);
          files.push({
            path: full,
            canonicalPath: canonFile,
            uuid: uuidMatch ? uuidMatch[1] : null,
            mtimeMs: st.mtimeMs,
          });
        } catch {}
      }
    }
  };

  for (const home of homes) {
    walkSessions(join(home, 'sessions'), 0);
  }
  return files;
}

function isSubagentSessionMeta(meta) {
  if (!object(meta)) return false;
  if (meta.thread_source === 'subagent') return true;
  return Boolean(meta.parent_thread_id || (meta.source && typeof meta.source === 'object' && meta.source.subagent));
}

function readSessionIndexIds(fs, codexHomes) {
  const ids = new Set();
  const seenIdx = new Set();
  for (const home of new Set(codexHomes.filter(Boolean))) {
    const idxPath = join(home, 'session_index.jsonl');
    const canonIdx = canonicalPathSafe(fs, idxPath);
    if (seenIdx.has(canonIdx)) continue;
    seenIdx.add(canonIdx);
    try {
      const lines = fs.readFileSync(idxPath, 'utf8').split('\n');
      for (const line of lines) {
        if (!line.trim()) continue;
        try {
          const row = JSON.parse(line);
          if (typeof row?.id === 'string' && UUID_TOKEN_RE.test(row.id)) ids.add(row.id);
        } catch {}
      }
    } catch {}
  }
  return ids;
}

function snapshotPreSpawnCodexSessions(fs, codexHomes) {
  const files = collectRolloutFiles(fs, codexHomes);
  return {
    rolloutPaths: new Set(files.map(f => f.canonicalPath)),
    sessionIds: readSessionIndexIds(fs, codexHomes),
  };
}

function findRolloutPathBySessionId(fs, codexHomes, targetSessionId) {
  if (!targetSessionId) return null;
  const targetLower = targetSessionId.toLowerCase();
  const candidates = [];
  for (const item of collectRolloutFiles(fs, codexHomes)) {
    if (item.uuid && item.uuid.toLowerCase() === targetLower) {
      candidates.push(item);
      continue;
    }
    const header = readFirstJsonLine(fs, item.path);
    const meta = object(header?.payload) ? header.payload : header;
    const id = String(meta?.id ?? meta?.session_id ?? '').toLowerCase();
    if (id === targetLower) candidates.push(item);
  }
  candidates.sort((a, b) => b.mtimeMs - a.mtimeMs);
  return candidates[0]?.path ?? null;
}

function discoverPinnedCodexRollout(fs, codexHomes, {
  preSpawnSnapshot,
  expectedCwd,
  turnStartedMs,
  explicitSessionId = null,
  excludedSessionId = null,
}) {
  if (explicitSessionId) {
    return {
      sessionId: explicitSessionId,
      rolloutPath: findRolloutPathBySessionId(fs, codexHomes, explicitSessionId),
    };
  }
  const matches = [];
  for (const item of collectRolloutFiles(fs, codexHomes, { minMtimeMs: turnStartedMs - 2000 })) {
    if (preSpawnSnapshot?.rolloutPaths?.has(item.canonicalPath)) continue;
    const header = readFirstJsonLine(fs, item.path);
    if (header?.type !== 'session_meta') continue;
    const meta = object(header.payload) ? header.payload : header;
    if (isSubagentSessionMeta(meta)) continue;
    const sid = [meta?.id, meta?.session_id, item.uuid].find(v => typeof v === 'string' && UUID_TOKEN_RE.test(v)) ?? null;
    if (!sid || preSpawnSnapshot?.sessionIds?.has(sid) || (excludedSessionId && sid.toLowerCase() === excludedSessionId.toLowerCase())) continue;
    const metaCwd = typeof meta?.cwd === 'string' && meta.cwd.trim() ? meta.cwd.trim() : null;
    if (!metaCwd || !pathsMatchCwd(fs, metaCwd, expectedCwd)) continue;
    const parsedTs = Date.parse(meta?.timestamp ?? header.timestamp ?? '');
    const sortTime = Number.isFinite(parsedTs) ? parsedTs : item.mtimeMs;
    if (sortTime < turnStartedMs - 2000) continue;
    matches.push({ sessionId: sid, rolloutPath: item.path, sortTime });
  }
  matches.sort((a, b) => a.sortTime - b.sortTime);
  return matches[0] ? { sessionId: matches[0].sessionId, rolloutPath: matches[0].rolloutPath } : null;
}

function hasStructuredHttpStatus(value, statusCode, depth = 0) {
  if (depth > 4 || !object(value)) return false;
  for (const [k, v] of Object.entries(value)) {
    if ((k === 'status' || k === 'http_status' || k === 'status_code' || k === 'http_status_code') && Number(v) === statusCode) {
      return true;
    }
    if (object(v) && hasStructuredHttpStatus(v, statusCode, depth + 1)) return true;
  }
  return false;
}

function inspectRolloutQuotaError(fs, rolloutPath, fromByteOffset, turnStartedMs) {
  if (!rolloutPath) return { nextOffset: fromByteOffset, quotaError: null };
  let curOffset = fromByteOffset;

  for (let pass = 0; pass < 16; pass += 1) {
    const chunk = readRolloutChunkFromOffset(fs, rolloutPath, curOffset);
    if (chunk.status === 'empty' || chunk.status === 'partial') {
      return { nextOffset: chunk.nextOffset, quotaError: null };
    }
    curOffset = chunk.nextOffset;
    if (chunk.status === 'skipped_oversized') {
      if (curOffset >= chunk.eofSize) break;
      continue;
    }

    for (const rawLine of chunk.text.split('\n')) {
      const trimmed = rawLine.trim();
      if (!trimmed) continue;
      let row = null;
      try { row = JSON.parse(trimmed); } catch { continue; }
      if (!object(row)) continue;

      if (typeof row.timestamp === 'string') {
        const rowMs = Date.parse(row.timestamp);
        if (Number.isFinite(rowMs) && rowMs < turnStartedMs - 2000) continue;
      }

      let errObj = null;
      let isTerminalTurnError = false;
      if (row.type === 'event_msg' && object(row.payload)) {
        if (row.payload.type === 'task_complete' && object(row.payload.error)) {
          errObj = row.payload.error;
          isTerminalTurnError = true;
        } else if (row.payload.type === 'error' || row.payload.type === 'turn_failed') {
          errObj = object(row.payload.error) ? row.payload.error : row.payload;
          isTerminalTurnError = row.payload.type === 'turn_failed';
        }
      } else if (row.type === 'error' || row.type === 'turn.failed' || row.type === 'response.failed') {
        errObj = object(row.error)
          ? row.error
          : (object(row.payload?.error) ? row.payload.error : (object(row.payload) ? row.payload : row));
        isTerminalTurnError = true;
      }

      if (!object(errObj)) continue;

      const info = errObj.codex_error_info;
      const infoCode = typeof info === 'string' ? info.trim().toLowerCase() : '';
      const errCode = String(
        errObj.code
        ?? errObj.error_code
        ?? (typeof errObj.type === 'string' && errObj.type !== 'error' && errObj.type !== 'turn_failed' ? errObj.type : ''),
      ).trim().toLowerCase();
      const message = String(errObj.message ?? row.payload?.message ?? row.message ?? '').trim();
      const isHttp429 = hasStructuredHttpStatus(errObj, 429) || hasStructuredHttpStatus(row, 429);

      const isStructuredQuota = QUOTA_ERROR_CODES.has(infoCode)
        || QUOTA_ERROR_CODES.has(errCode)
        || ((isHttp429 || errCode === 'rate_limit_exceeded') && (!message || classifyRateLimitFailure(message) === 'quota_exhausted'))
        || (isTerminalTurnError && message && classifyRateLimitFailure(message) === 'quota_exhausted');

      if (isStructuredQuota) {
        return {
          nextOffset: curOffset,
          quotaError: {
            message: message || errCode || infoCode || 'usage_limit_reached',
          },
        };
      }
    }

    if (curOffset >= chunk.eofSize) break;
  }

  return { nextOffset: curOffset, quotaError: null };
}

function isCloudAccountStructurallyExhausted(acc) {
  if (!object(acc)) return false;
  if (acc.limit_reached === true) return true;
  if (typeof acc.five_hour_used_percent === 'number' && acc.five_hour_used_percent >= 100) return true;
  if (typeof acc.weekly_used_percent === 'number' && acc.weekly_used_percent >= 100) return true;
  return false;
}

async function checkCloudAccountQuotaExhausted(accountId, { cwd, env }, ports = {}) {
  if (!accountId) return null;
  try {
    const listed = await fetchAccountsList({ cwd, env, refresh: false }, ports);
    const acc = listed.accounts.find(a => a?.account_id === accountId) ?? null;
    if (isCloudAccountStructurallyExhausted(acc)) return acc;
  } catch {}
  return null;
}

function buildCodexExecutionEnv(baseEnv, managedHome) {
  const out = {};
  for (const [k, v] of Object.entries(baseEnv ?? {})) {
    if (typeof v === 'string') out[k] = v;
  }
  if (managedHome) {
    out.CODEX_HOME = managedHome;
    delete out.OPENAI_API_KEY;
    delete out.CODEX_API_KEY;
    delete out.CODEX_ACCESS_TOKEN;
    delete out.OPENAI_BASE_URL;
  }
  return out;
}

async function runSingleSupervisedCodexTurn({
  fs,
  args,
  cwd,
  env,
  stdin,
  stdout,
  stderr,
  turn,
  turnStartedMs,
  activeEntry,
  codexHomes,
  preSpawnSnapshot,
  expectedCwd,
  sessionState,
  excludedSessionId = null,
  initialRolloutOffset = 0,
}, ports = {}) {
  let rollingPlain = '';
  let capturedSessionId = null;
  let quotaExhausted = false;
  let quotaReasonText = '';
  let exhaustedAccountSnapshot = null;
  let rolloutOffset = initialRolloutOffset;
  let abortedByParentSignal = null;
  const abortController = new AbortController();
  const settleMs = ports.quotaSettleMs ?? 60;
  const rolloutPollMs = ports.rolloutPollIntervalMs ?? 200;
  const cloudPollMs = ports.cloudQuotaPollIntervalMs ?? 0;

  const inspectChunk = rawChunk => {
    const clean = stripAnsiText(String(rawChunk ?? ''));
    if (!clean) return;
    const sidMatch = OUTPUT_SESSION_ID_RE.exec(clean);
    if (sidMatch?.[1]) capturedSessionId = sidMatch[1];
    rollingPlain = `${rollingPlain}${clean}`.slice(-16_384);
  };

  const triggerStructuredQuotaAbort = (reasonText, cloudAccount = null) => {
    if (quotaExhausted) return;
    quotaExhausted = true;
    quotaReasonText = String(reasonText || 'usage_limit_reached');
    if (cloudAccount) exhaustedAccountSnapshot = cloudAccount;
    abortController.abort();
  };

  const pollRolloutOnce = () => {
    if (!sessionState.rolloutPath) {
      if (sessionState.sessionId) {
        const foundPath = findRolloutPathBySessionId(fs, codexHomes, sessionState.sessionId);
        if (foundPath) {
          sessionState.rolloutPath = foundPath;
          rolloutOffset = 0;
        }
      } else {
        const discovered = discoverPinnedCodexRollout(fs, codexHomes, {
          preSpawnSnapshot,
          expectedCwd,
          turnStartedMs,
          explicitSessionId: null,
          excludedSessionId,
        });
        if (discovered) {
          sessionState.sessionId = discovered.sessionId;
          sessionState.rolloutPath = discovered.rolloutPath;
          rolloutOffset = 0;
        }
      }
    }
    if (sessionState.rolloutPath && !quotaExhausted) {
      const checked = inspectRolloutQuotaError(fs, sessionState.rolloutPath, rolloutOffset, turnStartedMs);
      rolloutOffset = checked.nextOffset;
      if (checked.quotaError) {
        triggerStructuredQuotaAbort(checked.quotaError.message);
      }
    }
  };

  let rolloutInterval = null;
  let cloudInterval = null;
  let cloudCheckInFlight = false;

  const startStructuredMonitors = () => {
    if (rolloutPollMs > 0) {
      rolloutInterval = setInterval(pollRolloutOnce, rolloutPollMs);
      rolloutInterval.unref?.();
    }
    if (cloudPollMs > 0 && activeEntry?.account_id) {
      cloudInterval = setInterval(() => {
        if (quotaExhausted || cloudCheckInFlight) return;
        cloudCheckInFlight = true;
        checkCloudAccountQuotaExhausted(activeEntry.account_id, { cwd, env }, ports)
          .then(acc => {
            if (acc) triggerStructuredQuotaAbort('usage_limit_reached', acc);
          })
          .finally(() => {
            cloudCheckInFlight = false;
          });
      }, cloudPollMs);
      cloudInterval.unref?.();
    }
  };

  const stopStructuredMonitors = () => {
    if (rolloutInterval) {
      clearInterval(rolloutInterval);
      rolloutInterval = null;
    }
    if (cloudInterval) {
      clearInterval(cloudInterval);
      cloudInterval = null;
    }
  };

  if (typeof ports.spawnCodexPty === 'function') {
    startStructuredMonitors();
    let res;
    try {
      res = await ports.spawnCodexPty({
        command: 'codex',
        args,
        cwd,
        env,
        turn,
        signal: abortController.signal,
        onOutput(chunk) {
          try { stdout?.write?.(chunk); } catch {}
          inspectChunk(chunk);
        },
      });
    } finally {
      stopStructuredMonitors();
    }
    if (res?.stdout) inspectChunk(res.stdout);
    if (res?.stderr) inspectChunk(res.stderr);
    if (typeof res?.sessionId === 'string' && UUID_TOKEN_RE.test(res.sessionId)) {
      capturedSessionId = res.sessionId;
    }
    pollRolloutOnce();
    if (!sessionState.sessionId && capturedSessionId && (!excludedSessionId || capturedSessionId.toLowerCase() !== excludedSessionId.toLowerCase())) {
      sessionState.sessionId = capturedSessionId;
    }
    return {
      code: res?.code ?? 0,
      signal: res?.signal ?? null,
      quotaExhausted,
      quotaReasonText,
      exhaustedAccountSnapshot,
      abortedByParentSignal,
      rollingPlain,
      capturedSessionId,
    };
  }

  const spawnImpl = ports.spawnInteractive ?? spawn;
  const usePythonPty = ports.usePythonPty !== false && Boolean(stdin?.isTTY && stdout?.isTTY);

  const runWithChild = tryPython => new Promise((resolveTurn, rejectTurn) => {
    let settled = false;
    let ttyRestored = false;
    let settleTimer = null;
    let killTimer = null;
    let wasRaw = false;
    let rawEnabled = false;
    let onStdinData = null;
    let onStdinEnd = null;
    let onResize = null;

    const childEnv = tryPython
      ? {
          ...env,
          PDD_PTY_ROWS: String(stdout?.rows || 24),
          PDD_PTY_COLS: String(stdout?.columns || 80),
        }
      : env;

    let child;
    try {
      child = tryPython
        ? spawnImpl('python3', ['-u', '-c', PYTHON_PTY_SUPERVISOR_SCRIPT, 'codex', ...args], {
            cwd,
            env: childEnv,
            stdio: ['pipe', 'pipe', 'pipe', 'pipe'],
            shell: false,
          })
        : spawnImpl('codex', args, {
            cwd,
            env: childEnv,
            stdio: [stdin === process.stdin || !stdin ? 'inherit' : 'pipe', 'pipe', 'pipe'],
            shell: false,
          });
    } catch (err) {
      rejectTurn(err);
      return;
    }

    const resizePipe = tryPython ? (child.stdio?.[3] ?? null) : null;
    resizePipe?.on?.('error', () => {});

    const removeStreamListener = (stream, eventName, handler) => {
      if (!stream || !handler) return;
      if (typeof stream.off === 'function') {
        try { stream.off(eventName, handler); return; } catch {}
      }
      if (typeof stream.removeListener === 'function') {
        try { stream.removeListener(eventName, handler); } catch {}
      }
    };

    const restoreTty = () => {
      if (ttyRestored) return;
      ttyRestored = true;
      removeStreamListener(stdin, 'data', onStdinData);
      removeStreamListener(stdin, 'end', onStdinEnd);
      removeStreamListener(stdin, 'close', onStdinEnd);
      removeStreamListener(stdout, 'resize', onResize);
      if (rawEnabled && typeof stdin?.setRawMode === 'function') {
        try { stdin.setRawMode(wasRaw); } catch {}
      }
      if (rawEnabled && typeof stdin?.pause === 'function') {
        try { stdin.pause(); } catch {}
      }
    };

    const terminateChild = () => {
      try { resizePipe?.end?.(); } catch {}
      try { child.stdin?.end?.(); } catch {}
      try { child.kill('SIGTERM'); } catch {}
      if (!killTimer) {
        killTimer = setTimeout(() => {
          try { child.kill('SIGKILL'); } catch {}
        }, 600);
        killTimer.unref?.();
      }
    };

    const onProcessExit = () => {
      restoreTty();
      try { resizePipe?.destroy?.(); } catch {}
      try { child.kill('SIGTERM'); } catch {}
    };
    const onSigterm = () => {
      abortedByParentSignal = 'SIGTERM';
      restoreTty();
      terminateChild();
    };
    const onSighup = () => {
      abortedByParentSignal = 'SIGHUP';
      restoreTty();
      terminateChild();
    };
    const onSigint = () => {
      if (tryPython) {
        try { child.kill('SIGINT'); } catch {}
      }
    };

    process.on('exit', onProcessExit);
    process.on('SIGTERM', onSigterm);
    process.on('SIGHUP', onSighup);
    process.on('SIGINT', onSigint);

    const onAbort = () => {
      if (settleMs <= 0) {
        terminateChild();
      } else {
        settleTimer = setTimeout(terminateChild, settleMs);
        settleTimer.unref?.();
      }
    };
    abortController.signal.addEventListener('abort', onAbort, { once: true });
    startStructuredMonitors();

    const finish = (err, code, signal) => {
      if (settled) return;
      settled = true;
      stopStructuredMonitors();
      if (settleTimer) clearTimeout(settleTimer);
      if (killTimer) clearTimeout(killTimer);
      abortController.signal.removeEventListener('abort', onAbort);
      process.off('exit', onProcessExit);
      process.off('SIGTERM', onSigterm);
      process.off('SIGHUP', onSighup);
      process.off('SIGINT', onSigint);
      try { resizePipe?.end?.(); } catch {}
      restoreTty();
      if (err) {
        rejectTurn(err);
        return;
      }
      pollRolloutOnce();
      if (!sessionState.sessionId && capturedSessionId && (!excludedSessionId || capturedSessionId.toLowerCase() !== excludedSessionId.toLowerCase())) {
        sessionState.sessionId = capturedSessionId;
      }
      const effectiveSignal = abortedByParentSignal ?? signal ?? null;
      const effectiveCode = effectiveSignal === 'SIGINT'
        ? 130
        : (abortedByParentSignal === 'SIGTERM' ? 143 : (abortedByParentSignal === 'SIGHUP' ? 129 : (code ?? 0)));
      resolveTurn({
        code: effectiveCode,
        signal: effectiveSignal,
        quotaExhausted,
        quotaReasonText,
        exhaustedAccountSnapshot,
        abortedByParentSignal,
        rollingPlain,
        capturedSessionId,
      });
    };

    if (tryPython && resizePipe && typeof stdout?.on === 'function') {
      onResize = () => {
        const nextRows = Number(stdout?.rows) || 24;
        const nextCols = Number(stdout?.columns) || 80;
        if (nextRows > 0 && nextCols > 0) {
          try { resizePipe.write(`${nextRows} ${nextCols}\n`); } catch {}
        }
      };
      stdout.on('resize', onResize);
    }

    if (tryPython && stdin && child.stdin) {
      if (stdin.isTTY && typeof stdin.setRawMode === 'function') {
        wasRaw = Boolean(stdin.isRaw);
        try {
          stdin.setRawMode(true);
          rawEnabled = true;
        } catch {}
      }
      onStdinData = chunk => {
        try { child.stdin.write(chunk); } catch {}
      };
      onStdinEnd = () => {
        try { child.stdin.end(); } catch {}
        try { resizePipe?.end?.(); } catch {}
      };
      stdin.on?.('data', onStdinData);
      stdin.once?.('end', onStdinEnd);
      stdin.once?.('close', onStdinEnd);
      stdin.resume?.();
      child.stdin.on('error', () => {});
    } else if (!tryPython && stdin && stdin !== process.stdin && typeof stdin.pipe === 'function' && child.stdin) {
      stdin.pipe(child.stdin);
      child.stdin.on('error', () => {});
    }

    child.stdout?.on('data', chunk => {
      try { stdout?.write?.(chunk); } catch {}
      inspectChunk(chunk);
    });
    child.stderr?.on('data', chunk => {
      try { stderr?.write?.(chunk); } catch {}
      inspectChunk(chunk);
    });
    child.on('error', err => finish(err));
    child.on('close', (code, signal) => finish(null, code, signal));
  });

  if (usePythonPty) {
    try {
      return await runWithChild(true);
    } catch (err) {
      if (err?.code !== 'ENOENT') throw err;
    }
  }
  return runWithChild(false);
}

function exitCodeFromSignalOrStatus(code, signal) {
  if (signal === 'SIGINT') return 130;
  if (signal === 'SIGTERM') return 143;
  if (signal === 'SIGHUP') return 129;
  if (signal) return 1;
  return typeof code === 'number' ? code : 1;
}

function writeStreamChunk(stream, chunk) {
  if (chunk == null) return;
  if (typeof chunk === 'string' && chunk.length === 0) return;
  if (chunk instanceof Uint8Array && chunk.byteLength === 0) return;
  try {
    stream?.write?.(chunk);
  } catch {}
}

async function runPlainCodexOnce(args, { cwd, env, stdin, stdout, stderr }, ports = {}) {
  if (typeof ports.spawnCodexPty === 'function') {
    const res = await ports.spawnCodexPty({
      command: 'codex',
      args,
      cwd,
      env,
      turn: 0,
      signal: new AbortController().signal,
      onOutput(chunk) {
        writeStreamChunk(stdout, chunk);
      },
    });
    const exitCode = res?.signal
      ? exitCodeFromSignalOrStatus(null, res.signal)
      : (res?.code ?? 0);
    return { exitCode, message: '' };
  }
  if (typeof ports.run === 'function') {
    const res = await ports.run('codex', args, { cwd, env, input: '', timeoutMs: 300_000, maxBytes: 1_048_576 });
    writeStreamChunk(stdout, res?.stdout);
    writeStreamChunk(stderr, res?.stderr);
    return { exitCode: exitCodeFromSignalOrStatus(res?.code, res?.signal), message: '' };
  }
  const inheritStdin = stdin == null || stdin === process.stdin;
  const inheritStdout = !stdout || stdout === process.stdout;
  const inheritStderr = !stderr || stderr === process.stderr;
  const stdio = inheritStdin && inheritStdout && inheritStderr
    ? 'inherit'
    : [
      inheritStdin ? 'inherit' : 'pipe',
      inheritStdout ? 'inherit' : 'pipe',
      inheritStderr ? 'inherit' : 'pipe',
    ];
  return new Promise(resolveExit => {
    let settled = false;
    const child = (ports.spawn ?? spawn)('codex', args, { cwd, env, stdio });
    const forward = sig => {
      try { child.kill(sig); } catch {}
    };
    const onSigInt = () => forward('SIGINT');
    const onSigTerm = () => forward('SIGTERM');
    const onSigHup = () => forward('SIGHUP');
    process.on('SIGINT', onSigInt);
    process.on('SIGTERM', onSigTerm);
    process.on('SIGHUP', onSigHup);

    const finish = result => {
      if (settled) return;
      settled = true;
      process.off('SIGINT', onSigInt);
      process.off('SIGTERM', onSigTerm);
      process.off('SIGHUP', onSigHup);
      if (child.stdin && stdin && typeof stdin.unpipe === 'function') {
        try { stdin.unpipe(child.stdin); } catch {}
      }
      resolveExit(result);
    };

    if (child.stdin) {
      child.stdin.on('error', () => {});
      if (typeof stdin === 'string' || stdin instanceof Uint8Array) {
        try { child.stdin.end(stdin); } catch {}
      } else if (stdin && typeof stdin.pipe === 'function') {
        stdin.pipe(child.stdin);
      } else {
        try { child.stdin.end(); } catch {}
      }
    }
    if (child.stdout) {
      child.stdout.on('data', chunk => writeStreamChunk(stdout, chunk));
    }
    if (child.stderr) {
      child.stderr.on('data', chunk => writeStreamChunk(stderr, chunk));
    }

    child.on('error', err => {
      const message = err?.code === 'ENOENT'
        ? 'codex CLI not found on PATH.'
        : redactSecrets(`Failed to run codex: ${err?.message ?? 'spawn error'}`);
      finish({ exitCode: 1, message });
    });
    child.on('close', (code, signal) => {
      finish({ exitCode: exitCodeFromSignalOrStatus(code, signal), message: '' });
    });
  });
}

async function leaseNextHealthyCodexForRotation(skipAccountIds, { cwd, env }, ports = {}) {
  const skipIds = [...new Set(skipAccountIds.filter(Boolean))];
  for (let attempt = 0; attempt < 8; attempt += 1) {
    let reply = null;
    try {
      reply = await leaseCloudAccount({
        provider: 'codex',
        currentAccountId: null,
        skipAccountIds: skipIds,
        holderId: 'codex-pty',
        updateState: false,
      }, { cwd, env, timeoutMs: ports.leaseTimeoutMs ?? 8000 }, ports);
    } catch (err) {
      if (isReauthRequiredFailure(err)) {
        const failedId = err?.payload?.account_id ?? err?.payload?.detail?.account_id ?? null;
        if (failedId && !skipIds.includes(failedId)) {
          markLocalAccountReauthRequired(failedId, { env }, ports);
          skipIds.push(failedId);
          continue;
        }
        return { state: 'reauth_required', reply: null };
      }
      return { state: 'error', error: err, reply: null };
    }

    if (reply?.state === 'all_cooling') {
      const latestSaved = readCloudAccountsState({ env }, ports);
      if (latestSaved.enrolled && latestSaved.providers.includes('codex')) {
        writeCloudAccountsState({
          ...latestSaved,
          cooling: { ...latestSaved.cooling, codex: { wake_at: reply.wake_at ?? null } },
        }, { env }, ports);
      }
      return { state: 'all_cooling', reply };
    }

    if (!reply || reply.state !== 'leased' || !object(reply.account) || !object(reply.lease)) {
      return { state: 'unavailable', reply };
    }

    const acc = reply.account;
    if (isReauthRequiredAccount(acc) && acc.account_id && !skipIds.includes(acc.account_id)) {
      markLocalAccountReauthRequired(acc.account_id, { env }, ports);
      skipIds.push(acc.account_id);
      continue;
    }
    if (((typeof acc.five_hour_used_percent === 'number' && acc.five_hour_used_percent >= 100)
      || (typeof acc.weekly_used_percent === 'number' && acc.weekly_used_percent >= 100))
      && acc.account_id && !skipIds.includes(acc.account_id)) {
      skipIds.push(acc.account_id);
      continue;
    }
    return { state: 'leased', reply };
  }
  return { state: 'unavailable', reply: null };
}

async function runInteractiveCodexWithAutoRotate({ args = [], cwd, env, stdin }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const activeStdin = ports.stdin ?? stdin ?? process.stdin;
  const activeStdout = ports.stdout ?? process.stdout;
  const activeStderr = ports.stderr ?? process.stderr;
  const initialArgs = [...args];
  const invocation = inspectCodexInvocation(initialArgs, cwd);

  let managedHome = '';
  const expectedManagedHome = pddManagedCodexHome(env);
  if (isCloudAccountsActive({ env, provider: 'codex' }, ports)) {
    const synced = await runSyncCommand({
      provider: 'codex',
      quiet: true,
      printCodexHome: true,
      timeoutMs: ports.syncTimeoutMs ?? 2000,
      cwd,
      env,
    }, ports);
    managedHome = synced.message.trim();
    if (!managedHome && hasLocalMaterializedFile(fs, 'codex', env)) {
      const curState = readCloudAccountsState({ env }, ports);
      if (curState.active?.codex?.state === 'ready') managedHome = expectedManagedHome;
    }
  }

  if (!managedHome) {
    const fallbackEnv = { ...env };
    if (fallbackEnv.CODEX_HOME && resolve(fallbackEnv.CODEX_HOME) === resolve(expectedManagedHome)) {
      delete fallbackEnv.CODEX_HOME;
    }
    return runPlainCodexOnce(initialArgs, { cwd, env: fallbackEnv, stdin: activeStdin, stdout: activeStdout, stderr: activeStderr }, ports);
  }

  if (!invocation.interactive) {
    const execEnv = buildCodexExecutionEnv(env, managedHome);
    return runPlainCodexOnce(initialArgs, { cwd, env: execEnv, stdin: activeStdin, stdout: activeStdout, stderr: activeStderr }, ports);
  }

  const userCodexHome = localCodexHome({ ...env, CODEX_HOME: '' });
  const codexHomes = [managedHome, userCodexHome];
  const preSpawnSnapshot = snapshotPreSpawnCodexSessions(fs, codexHomes);
  const initialResumeSessionId = invocation.isResume ? (invocation.explicitSessionId ?? null) : null;
  const excludedForkSessionId = invocation.isFork ? (invocation.explicitSessionId ?? null) : null;
  const sessionState = {
    sessionId: initialResumeSessionId,
    rolloutPath: initialResumeSessionId
      ? findRolloutPathBySessionId(fs, codexHomes, initialResumeSessionId)
      : null,
  };

  let currentArgs = initialArgs;
  const triedAccountIds = new Set();
  const maxRotations = 8;

  for (let turn = 0; turn <= maxRotations; turn += 1) {
    const turnStartedMs = (ports.now ?? Date.now)();
    const stateBefore = readCloudAccountsState({ env }, ports);
    const activeBefore = stateBefore.active?.codex ?? null;
    const childEnv = buildCodexExecutionEnv(env, managedHome);
    const initialRolloutOffset = sessionState.rolloutPath ? safeFileSize(fs, sessionState.rolloutPath) : 0;

    const turnRes = await runSingleSupervisedCodexTurn({
      fs,
      args: currentArgs,
      cwd,
      env: childEnv,
      stdin: activeStdin,
      stdout: activeStdout,
      stderr: activeStderr,
      turn,
      turnStartedMs,
      activeEntry: activeBefore,
      codexHomes,
      preSpawnSnapshot,
      expectedCwd: invocation.effectiveCwd,
      sessionState,
      excludedSessionId: excludedForkSessionId,
      initialRolloutOffset,
    }, ports);

    if (turnRes.abortedByParentSignal) {
      return { exitCode: turnRes.code ?? 1, message: '' };
    }

    let hitQuota = turnRes.quotaExhausted;
    let cloudExhaustedAcc = turnRes.exhaustedAccountSnapshot;

    if (!hitQuota && turnRes.code !== 0 && turnRes.code !== 130 && turnRes.signal !== 'SIGINT') {
      if (activeBefore?.account_id) {
        cloudExhaustedAcc = await checkCloudAccountQuotaExhausted(activeBefore.account_id, { cwd, env }, ports);
        if (cloudExhaustedAcc) hitQuota = true;
      }
      // Early startup failure fallback ONLY when codex exited non-zero on its own before creating a session rollout file.
      if (!hitQuota && !sessionState.rolloutPath && classifyRateLimitFailure(turnRes.rollingPlain, activeBefore) === 'quota_exhausted') {
        hitQuota = true;
      }
    }

    if (!hitQuota) {
      return { exitCode: turnRes.code ?? 0, message: '' };
    }

    const latestState = readCloudAccountsState({ env }, ports);
    const exhaustedEntry = latestState.active?.codex ?? activeBefore;
    const exhaustedId = exhaustedEntry?.account_id ?? null;
    if (exhaustedId) {
      triedAccountIds.add(exhaustedId);
      const reportSourceText = turnRes.quotaReasonText || (!sessionState.rolloutPath ? turnRes.rollingPlain : 'usage_limit_reached');
      const report = extractRateLimitReport(reportSourceText, cloudExhaustedAcc ?? exhaustedEntry, (ports.now ?? Date.now)());
      await reportCloudAccountUsage(exhaustedId, report, { cwd, env, timeoutMs: 3500 }, ports).catch(() => {});
    }

    if (turn >= maxRotations) {
      return {
        exitCode: 1,
        message: 'Reached maximum automatic Codex account rotations for this session.',
      };
    }

    const nextLease = await leaseNextHealthyCodexForRotation([...triedAccountIds], { cwd, env }, ports);
    if (nextLease.state !== 'leased' || !nextLease.reply) {
      const wakeAt = nextLease.reply?.wake_at;
      const msg = nextLease.state === 'all_cooling'
        ? `All codex accounts are cooling${wakeAt ? ` until ${wakeAt}` : ''}.`
        : 'No additional ready Codex Cloud accounts are available to resume this session.';
      return { exitCode: 1, message: msg };
    }

    applyMaterializedLease(nextLease.reply, { env }, ports);
    const prevLabel = exhaustedEntry?.label ?? exhaustedId ?? 'previous';
    const nextLabel = nextLease.reply.account?.label ?? nextLease.reply.account?.account_id ?? 'next';
    const quotaInfo = formatAccountQuotaSummary(nextLease.reply.account);
    const keepInitialPromptArgs = !sessionState.sessionId && !invocation.isResume;
    const resumeDesc = sessionState.sessionId
      ? `session ${sessionState.sessionId}`
      : (keepInitialPromptArgs ? 'initial arguments' : '--last');
    try {
      activeStderr?.write?.(
        redactSecrets(`\n[pdd accounts] Quota reached on "${prevLabel}"; switched active Codex account to "${nextLabel}"${quotaInfo} and resuming (${resumeDesc}).\n`),
      );
    } catch {}
    currentArgs = keepInitialPromptArgs
      ? [...initialArgs]
      : buildCodexResumeArgs(initialArgs, sessionState.sessionId);
  }

  return { exitCode: 1, message: 'No additional ready Codex Cloud accounts are available.' };
}

const AUTO_REFRESH_SUBCOMMANDS = new Set([
  'list',
  'status',
  'add',
  'import',
  'use',
  'next',
  'codex',
  'sync',
  'accept',
]);

export async function runAccountsCli({
  commandId = 'accounts',
  operands = [],
  options = {},
  cwd = process.cwd(),
  env = process.env,
  stdin = process.stdin,
} = {}, ports = {}) {
  const sub = commandId === 'accounts' ? 'list' : commandId.slice('accounts.'.length);
  if (AUTO_REFRESH_SUBCOMMANDS.has(sub)) {
    refreshInstalledAutoSwitchBlocks({ env }, ports);
  }
  try {
    switch (sub) {
      case 'list': {
        const nowMs = (ports.now ?? Date.now)();
        const { accounts, pendingInvites } = await fetchAccountsList({ cwd, env, refresh: true }, ports);
        const current = readCloudAccountsState({ env }, ports);
        const { accessible, updatedState } = reconcileListedState(accounts, current, { env }, ports);
        const normalizedAccounts = accessible.map(acc => withLeftPercentFields({
          ...acc,
          state: accountDisplayState(acc, updatedState.active?.[acc.provider], updatedState.reauth),
        }));
        if (options['--json'] === true) {
          return {
            exitCode: 0,
            message: redactSecrets(JSON.stringify({
              accounts: normalizedAccounts,
              pending_invites: pendingInvites,
              active: withLeftPercentActiveMap(updatedState.active),
            }, null, 2)),
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
          replace: options['--replace'] === true,
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
          replace: options['--replace'] === true,
          withTargets: options['--with'] ?? '',
          cwd,
          env,
          stdin,
        }, ports);

      case 'use': {
        const targetLabel = operands[0];
        const { account, accounts } = await resolveAccount(targetLabel, { cwd, env, provider: options['--provider'] || null }, ports);
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
        const useQuota = formatAccountQuotaSummary(reply.account ?? account);
        return { exitCode: 0, message: `Active ${account.provider} account set to "${reply.account?.label ?? account.label}"${useQuota}.` };
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
        const nextQuota = formatAccountQuotaSummary(reply.account);
        return { exitCode: 0, message: `Switched ${provider} account to "${reply.account?.label ?? reply.account?.account_id}"${nextQuota}.` };
      }

      case 'codex':
        return await runInteractiveCodexWithAutoRotate({ args: operands, cwd, env, stdin }, ports);

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
        const { account } = await resolveAccount(operands[0], { cwd, env, provider: options['--provider'] || null }, ports);
        await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/pause`, { body: {}, cwd, env }, ports);
        const saved = readCloudAccountsState({ env }, ports);
        const prov = account.provider;
        if (prov && saved.active?.[prov]?.account_id === account.account_id) {
          const prevEntry = saved.active[prov];
          const nextActive = { ...saved.active };
          delete nextActive[prov];
          writeCloudAccountsState({
            ...saved,
            active: nextActive,
          }, { env }, ports);
          if (prov === 'claude') {
            restoreLocalClaudeGatewayConfig({ env }, ports);
          } else if (prov === 'codex') {
            restoreLocalCodexGatewayConfig({
              env,
              previousModelProvider: prevEntry.previous_codex_model_provider ?? null,
              removeAuthFile: true,
            }, ports);
          }
        } else if (prov === 'claude') {
          restoreLocalClaudeGatewayConfig({ env, removeManagedFile: false }, ports);
        }
        return { exitCode: 0, message: `Paused account "${account.label}".` };
      }

      case 'unpause': {
        const { account } = await resolveAccount(operands[0], { cwd, env, provider: options['--provider'] || null }, ports);
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
        const rawWith = typeof options['--with'] === 'string' ? options['--with'] : '';
        const parsedWith = parseWithTargets(rawWith);
        if (parsedWith.error) return { exitCode: 2, message: parsedWith.error };
        if (!parsedWith.targets.length) {
          return { exitCode: 2, message: 'Use pdd accounts share LABEL --with USER|ORG/TEAM[,...] or pdd accounts share --all --with USER|ORG/TEAM[,...].' };
        }
        const sharePayloads = await resolveSharePayloads(parsedWith.targets, { cwd, env }, ports);

        let targetAccounts;
        let pendingInvites = [];
        if (allFlag) {
          const listed = await fetchAccountsList({ cwd, env, refresh: false }, ports);
          pendingInvites = listed.pendingInvites;
          targetAccounts = listed.accounts.filter(acc => isOwnedAccount(acc) && (!providerFilter || acc.provider === providerFilter));
          if (!targetAccounts.length) {
            return { exitCode: 1, message: providerFilter ? `No owned ${providerFilter} Cloud accounts found.` : 'No owned Cloud accounts found.' };
          }
        } else {
          const resolved = await resolveAccount(labelArg, { cwd, env, provider: providerFilter }, ports);
          targetAccounts = [resolved.account];
          pendingInvites = resolved.pendingInvites ?? [];
        }

        const notes = await applySharePayloadsToAccounts(targetAccounts, sharePayloads, { cwd, env, pendingInvites }, ports);
        if (targetAccounts.length === 1 && sharePayloads.length === 1) {
          if (notes[0]?.alreadyShared) {
            return { exitCode: 0, message: `Account "${targetAccounts[0].label}" is already shared with ${notes[0].display}.` };
          }
          const inviteNote = notes[0]?.inviteId ? ` (invite ${notes[0].inviteId})` : '';
          return { exitCode: 0, message: `Shared "${targetAccounts[0].label}" with ${notes[0].display}${inviteNote}.` };
        }
        const acctNames = targetAccounts.map(a => `"${a.label}"`).join(', ');
        const targetNames = sharePayloads
          .map(payload => {
            const matching = notes.filter(row => row.display === payload.display);
            const invitesForTarget = matching.filter(row => row.inviteId).map(row => row.inviteId);
            if (invitesForTarget.length) return `${payload.display} (invite ${invitesForTarget.join(', ')})`;
            if (matching.length && matching.every(row => row.alreadyShared)) return `${payload.display} (already shared)`;
            return payload.display;
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
        const fs = ports.fs ?? nativeFs;
        const nowMs = (ports.now ?? Date.now)();
        const existingActive = provider ? current.active?.[provider] : null;
        const existingExpMs = existingActive?.expires_at ? Date.parse(existingActive.expires_at) : NaN;
        const needsActivation = Boolean(
          provider && (
            !existingActive?.account_id
            || existingActive.state === 'reauth_required'
            || Boolean(current.reauth?.[existingActive.account_id])
            || !Number.isFinite(existingExpMs)
            || existingExpMs <= nowMs
            || !hasLocalMaterializedFile(fs, provider, env)
          ),
        );
        let syncWarning = '';
        if (needsActivation) {
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
            } else if (leased?.state === 'leased' && isReauthRequiredAccount(leased.account)) {
              markLocalAccountReauthRequired(leased.account?.account_id, { env }, ports);
              syncWarning = ' Warning: account requires re-authentication before local sync.';
            } else if (leased?.state === 'all_cooling') {
              syncWarning = ` Warning: all ${provider} accounts are currently cooling${leased.wake_at ? ` until ${leased.wake_at}` : ''}; run pdd accounts sync once quota resets.`;
            }
          } catch (err) {
            const reason = redactSecrets(String(err?.message ?? 'lease failed')).trim();
            const useHint = acceptedAcc?.label ? `pdd accounts use ${acceptedAcc.label}` : 'pdd accounts sync';
            syncWarning = ` Warning: initial local sync failed (${reason}) — run ${useHint}.`;
          }
        }
        return {
          exitCode: 0,
          message: redactSecrets(`Accepted shared account${acceptedAcc?.label ? ` "${acceptedAcc.label}"` : ` invite ${inviteId}`}.${syncWarning}`),
        };
      }

      case 'unshare': {
        const labelArg = typeof operands[0] === 'string' ? operands[0].trim() : '';
        const allFlag = options['--all'] === true;
        const providerFilter = options['--provider'] || null;
        if (Boolean(labelArg) === allFlag) {
          return { exitCode: 2, message: 'Specify either LABEL or --all on pdd accounts unshare, not both.' };
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
          const { account } = await resolveAccount(labelArg, { cwd, env, provider: providerFilter }, ports);
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
        const { account, accounts } = await resolveAccount(operands[0], { cwd, env, provider: options['--provider'] || null }, ports);
        await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/leave`, { body: {}, cwd, env }, ports);
        syncStateAfterAccountRemoval(account, accounts, { env }, ports);
        return { exitCode: 0, message: `Left shared account "${account.label}".` };
      }

      case 'remove': {
        const { account, accounts } = await resolveAccount(operands[0], { cwd, env, provider: options['--provider'] || null }, ports);
        await cloudAccountsRequest('DELETE', `/v1/accounts/${encodeURIComponent(account.account_id)}`, { cwd, env }, ports);
        syncStateAfterAccountRemoval(account, accounts, { env }, ports);
        return { exitCode: 0, message: `Removed account "${account.label}".` };
      }

      case 'log': {
        const { account } = await resolveAccount(operands[0], { cwd, env, provider: options['--provider'] || null }, ports);
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
    const exitCode = (error instanceof CloudAccountsError && Number.isInteger(error.exitCode)) ? error.exitCode : 1;
    const safeMsg = redactSecrets(error instanceof CloudAccountsError ? error.message : `Accounts command failed: ${error?.message ?? 'unknown error'}`);
    return { exitCode, message: safeMsg };
  }
}
