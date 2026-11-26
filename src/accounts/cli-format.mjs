// Generated from prompts/cli/accounts-cli.prompt.md.
// Quota/table formatting, account display state, JWT decoding, and label derivation helpers.
import { isLocalReauthUnresolved, isReauthRequiredAccount } from './cloud-client.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);

export function formatShortReset(iso) {
  if (typeof iso !== 'string' || !iso.trim()) return '';
  const ms = Date.parse(iso);
  if (!Number.isFinite(ms)) return iso.slice(0, 19);
  return new Date(ms).toISOString().replace(/:\d{2}(?:\.\d+)?Z$/, 'Z');
}

export function computeLeftPercent(usedPct) {
  if (typeof usedPct !== 'number' || !Number.isFinite(usedPct)) return null;
  return Math.min(100, Math.max(0, Math.round(100 - usedPct)));
}

export function formatWindow(pct, resetAt) {
  const left = computeLeftPercent(pct);
  if (left === null) return '-';
  const reset = formatShortReset(resetAt);
  return reset ? `${left}% left (${reset})` : `${left}% left`;
}

export function formatAccountQuotaSummary(acc) {
  const fiveH = formatWindow(acc?.five_hour_used_percent, acc?.five_hour_reset_at);
  const sevenD = formatWindow(acc?.weekly_used_percent, acc?.weekly_reset_at);
  return fiveH === '-' && sevenD === '-' ? '' : ` (5h: ${fiveH}, 7d: ${sevenD})`;
}

export function withLeftPercentFields(entry) {
  if (!object(entry)) return entry;
  return {
    ...entry,
    five_hour_left_percent: computeLeftPercent(entry.five_hour_used_percent),
    weekly_left_percent: computeLeftPercent(entry.weekly_used_percent),
  };
}

export function withLeftPercentActiveMap(activeMap) {
  if (!object(activeMap)) return activeMap;
  const out = {};
  for (const [prov, entry] of Object.entries(activeMap)) out[prov] = withLeftPercentFields(entry);
  return out;
}

export function hasUnresolvedLocalReauth(acc, activeEntry = null, localReauth = null) {
  const accId = acc?.account_id;
  if (!accId) return false;
  const refreshedIso = acc?.last_refresh_at ?? acc?.refreshed_at ?? null;
  if (isLocalReauthUnresolved(accId, refreshedIso, localReauth)) return true;
  if (object(localReauth) && object(localReauth[accId])) return false;
  if (activeEntry?.account_id === accId && activeEntry?.state === 'reauth_required') {
    const refreshedMs = refreshedIso ? Date.parse(refreshedIso) : NaN;
    const leasedMs = activeEntry.leased_at ? Date.parse(activeEntry.leased_at) : NaN;
    return !(Number.isFinite(refreshedMs) && Number.isFinite(leasedMs) && refreshedMs > leasedMs);
  }
  return false;
}

export function accountDisplayState(acc, activeEntry = null, localReauth = null) {
  if (isReauthRequiredAccount(acc)) return 'reauth_required';
  const rawState = typeof acc?.state === 'string' && acc.state.trim() ? acc.state.trim() : '';
  if (rawState && rawState !== 'ready') return rawState;
  if (hasUnresolvedLocalReauth(acc, activeEntry, localReauth)) return 'reauth_required';
  return rawState || 'ready';
}

export function formatRefreshColumn(acc, activeEntry, nowMs = Date.now()) {
  const state = accountDisplayState(acc, activeEntry);
  if (state === 'reauth_required') return 'reauth required';
  const isSameActive = Boolean(activeEntry?.account_id && activeEntry.account_id === acc?.account_id);
  const lastRefresh = acc?.last_refresh_at ?? acc?.refreshed_at ?? (isSameActive ? activeEntry?.last_refresh_at : null) ?? null;
  const expiresAt = acc?.access_token_expires_at ?? (isSameActive ? (activeEntry?.access_token_expires_at ?? activeEntry?.expires_at) : null) ?? null;
  const refShort = formatShortReset(lastRefresh);
  const expShort = formatShortReset(expiresAt);
  const expMs = expiresAt ? Date.parse(expiresAt) : NaN;
  const expPart = expShort ? (Number.isFinite(expMs) && expMs <= nowMs ? `expired ${expShort}` : `exp ${expShort}`) : '';
  if (refShort && expPart) return `refreshed ${refShort} (${expPart})`;
  if (refShort) return `refreshed ${refShort}`;
  return expPart || '-';
}

export function renderAccountsTable(accounts, pendingInvites, activeByProvider, nowMs = Date.now()) {
  const lines = [], reauthAccounts = [];
  if (!accounts.length) {
    lines.push('No Cloud accounts enrolled. Run pdd accounts add or pdd accounts import.');
  } else {
    const rows = accounts.map(acc => {
      const activeEntry = activeByProvider?.[acc.provider] ?? null;
      const isActive = activeEntry?.account_id === acc.account_id;
      const isSharedBorrower = typeof acc.is_owner === 'boolean' ? !acc.is_owner : Boolean(acc.shared);
      const access = isSharedBorrower ? `shared${acc.owner_login ? ` (${acc.owner_login})` : ''}` : `owner${acc.owner_login ? ` (${acc.owner_login})` : ''}`;
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
    lines.push('', 'Pending share invites:');
    for (const inv of visiblePendingInvites) {
      lines.push(`  ${inv.invite_id}  ${inv.label ?? '-'}  ${inv.provider ?? '-'}  from ${inv.owner_login ?? 'unknown'}  (accept: pdd accounts accept ${inv.invite_id})`);
    }
  }
  return lines.join('\n');
}

export function shortenHomePath(filePath, env = {}) {
  if (typeof filePath !== 'string' || !filePath) return String(filePath ?? '');
  const rawHome = typeof env?.HOME === 'string' ? env.HOME.trim() : '';
  const home = rawHome.replace(/[\\/]+$/, '');
  if (!home || /^[A-Za-z]:$/.test(home)) return filePath;
  if (filePath === home) return '~';
  if (filePath.startsWith(`${home}/`) || filePath.startsWith(`${home}\\`)) {
    return `~${filePath.slice(home.length)}`;
  }
  return filePath;
}

export function sanitizeStatusText(value) {
  if (typeof value !== 'string') return '';
  let out = '';
  for (let i = 0; i < value.length; i += 1) {
    const code = value.charCodeAt(i);
    if (code === 0x1b && value.charCodeAt(i + 1) === 0x5b) {
      i += 2;
      while (i < value.length) {
        const c = value.charCodeAt(i);
        if (c >= 0x40 && c <= 0x7e) break;
        i += 1;
      }
      continue;
    }
    if (code < 0x20 || code === 0x7f) {
      out += ' ';
      continue;
    }
    out += value[i];
  }
  return out.replace(/\s+/g, ' ').trim();
}

export function formatUtcTimestamp(iso) {
  if (typeof iso !== 'string' || !iso.trim()) return '';
  const ms = Date.parse(iso);
  if (!Number.isFinite(ms)) return sanitizeStatusText(iso).slice(0, 19).trimEnd();
  return new Date(ms).toISOString().replace('T', ' ').replace(/:\d{2}(?:\.\d+)?Z$/, ' UTC');
}

export function formatHumanDuration(ms) {
  if (typeof ms !== 'number' || !Number.isFinite(ms) || ms <= 0) return '<1m';
  if (ms < 60_000) return '<1m';
  const totalMinutes = Math.round(ms / 60_000);
  if (totalMinutes < 60) return `${totalMinutes}m`;
  if (totalMinutes < 24 * 60) {
    const hours = Math.floor(totalMinutes / 60);
    const mins = totalMinutes % 60;
    return mins > 0 ? `${hours}h ${mins}m` : `${hours}h`;
  }
  const totalHours = Math.round(ms / 3_600_000);
  const days = Math.floor(totalHours / 24);
  const hours = totalHours % 24;
  return hours > 0 ? `${days}d ${hours}h` : `${days}d`;
}

function formatStatusWindow(pct, resetAt) {
  const left = computeLeftPercent(pct);
  if (left === null) return null;
  const reset = formatUtcTimestamp(resetAt);
  return reset ? `${left}% left (resets ${reset})` : `${left}% left`;
}

export function formatStatusQuota(fiveHourUsed, fiveHourResetAt, weeklyUsed, weeklyResetAt) {
  const fiveH = formatStatusWindow(fiveHourUsed, fiveHourResetAt);
  const sevenD = formatStatusWindow(weeklyUsed, weeklyResetAt);
  if (fiveH === null && sevenD === null) return '-';
  return `5h ${fiveH ?? '-'} | 7d ${sevenD ?? '-'}`;
}

export function formatSeatAccess(source) {
  if (!object(source)) return '';
  const ownerLogin = sanitizeStatusText(source.owner_login);
  if (typeof source.is_owner === 'boolean') {
    const kind = source.is_owner ? 'owner' : 'shared';
    return ownerLogin ? `${kind} (${ownerLogin})` : kind;
  }
  if (typeof source.shared === 'boolean') {
    const kind = source.shared ? 'shared' : 'owner';
    return ownerLogin ? `${kind} (${ownerLogin})` : kind;
  }
  return '';
}

export function formatExpiryRemaining(iso, nowMs) {
  if (typeof iso !== 'string' || !iso.trim()) return 'unknown';
  const expMs = Date.parse(iso);
  if (!Number.isFinite(expMs)) return sanitizeStatusText(iso) || 'unknown';
  const utc = formatUtcTimestamp(iso);
  const remainingMs = expMs - nowMs;
  return remainingMs <= 0
    ? `expired (${utc})`
    : `valid (${formatHumanDuration(remainingMs)} left, exp ${utc})`;
}

export function decodeJwtPayload(jwt) {
  if (typeof jwt !== 'string') return null;
  const parts = jwt.split('.');
  if (parts.length < 2) return null;
  try { return JSON.parse(Buffer.from(parts[1], 'base64url').toString('utf8')); } catch { return null; }
}

export function detectCodexPlan(authJson) {
  const payload = decodeJwtPayload(authJson?.tokens?.id_token) ?? decodeJwtPayload(authJson?.tokens?.access_token);
  const plan = payload?.['https://api.openai.com/auth']?.chatgpt_plan_type ?? payload?.chatgpt_plan_type ?? authJson?.plan;
  return typeof plan === 'string' && plan.trim() ? plan.trim().toLowerCase() : 'pro';
}

export function sanitizeLabel(raw, fallback) {
  const cleaned = String(raw ?? '').trim().toLowerCase().replace(/[^a-z0-9._-]+/g, '-').replace(/^-+|-+$/g, '').slice(0, 48);
  return cleaned || fallback;
}

export function extractCodexEmail(authJson) {
  const payload = decodeJwtPayload(authJson?.tokens?.id_token) ?? decodeJwtPayload(authJson?.tokens?.access_token);
  return typeof payload?.email === 'string' && payload.email.trim() ? payload.email.trim() : '';
}

export function deriveEmailBaseLabel(authJson) {
  const email = extractCodexEmail(authJson);
  return sanitizeLabel(email ? email.split('@')[0] : '', '');
}

export function defaultAccountLabel(provider, authJson = null) {
  if (provider === 'codex') {
    const slug = deriveEmailBaseLabel(authJson);
    if (slug) return slug;
  }
  return `${provider}-main`;
}

export function nextDisambiguatedLabel(baseLabel, usedLabels, startSuffix = 2) {
  const cleanBase = sanitizeLabel(baseLabel, 'account');
  if (!usedLabels.has(cleanBase.toLowerCase())) return cleanBase;
  let idx = Math.max(2, startSuffix);
  while (usedLabels.has(`${cleanBase}-${idx}`.toLowerCase())) idx += 1;
  return `${cleanBase}-${idx}`;
}
