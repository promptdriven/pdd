// Prompt: prompts/cli/codex-seat-visibility.prompt.md

const GLOBAL_VALUE_FLAGS = new Set([
  '-c', '--config',
  '--enable', '--disable',
  '--remote', '--remote-auth-token-env',
  '-i', '--image',
  '-m', '--model',
  '--local-provider',
  '-p', '--profile',
  '-s', '--sandbox',
  '-C', '--cd',
  '--add-dir',
  '-a', '--ask-for-approval',
  '--color',
]);

const MACHINE_BOOL_FLAGS = new Set([
  '--json',
  '--experimental-json',
  '--quiet',
  '-q',
]);

const MACHINE_VALUE_FLAGS = new Set([
  '-o',
  '--output-last-message',
  '--output-schema',
]);

const FORMAT_VALUE_FLAGS = new Set([
  '--format',
  '--output-format',
]);

const NON_INTERACTIVE_SUBCOMMANDS = new Set([
  'exec',
  'e',
  'review',
  'app-server',
  'mcp-server',
  'exec-server',
  'login',
  'logout',
  'mcp',
  'features',
  'apply',
  'a',
  'archive',
  'unarchive',
  'delete',
  'migrate-rollouts',
  'migrate-nfs-db',
  'completion',
  'help',
  'cloud',
  'doctor',
  'update',
  'sandbox',
  'debug',
  'queue',
]);

const isPlainObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);

function sanitizeInlineText(value) {
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

function trimmedOrNull(value) {
  if (typeof value !== 'string') return null;
  const clean = value.trim();
  return clean || null;
}

function resolveAccessType(source) {
  if (!isPlainObject(source)) return 'unknown';
  const explicit = source.accessType ?? source.access_type;
  if (explicit === 'owner' || explicit === 'shared') return explicit;
  const isOwner = source.isOwner !== undefined ? source.isOwner : source.is_owner;
  if (typeof isOwner === 'boolean') return isOwner ? 'owner' : 'shared';
  if (typeof source.shared === 'boolean') return source.shared ? 'shared' : 'owner';
  return 'unknown';
}

function inspectCodexNoticeArgs(codexArgs = []) {
  const args = Array.isArray(codexArgs) ? codexArgs.map(String) : [];
  let firstPositional = null;
  let hasMachineFlag = false;

  for (let i = 0; i < args.length; i += 1) {
    const token = args[i];
    if (token === '--') break;

    if (token.startsWith('-') && token.includes('=')) {
      const eq = token.indexOf('=');
      const flag = token.slice(0, eq);
      const val = token.slice(eq + 1);
      if (MACHINE_VALUE_FLAGS.has(flag)) {
        hasMachineFlag = true;
      } else if (FORMAT_VALUE_FLAGS.has(flag) && val.trim().toLowerCase() === 'json') {
        hasMachineFlag = true;
      }
      continue;
    }

    if (MACHINE_BOOL_FLAGS.has(token)) {
      hasMachineFlag = true;
      continue;
    }
    if (MACHINE_VALUE_FLAGS.has(token)) {
      hasMachineFlag = true;
      i += 1;
      continue;
    }
    if (FORMAT_VALUE_FLAGS.has(token)) {
      const nextVal = args[i + 1];
      if (typeof nextVal === 'string' && nextVal.trim().toLowerCase() === 'json') {
        hasMachineFlag = true;
      }
      i += 1;
      continue;
    }
    if (GLOBAL_VALUE_FLAGS.has(token)) {
      i += 1;
      continue;
    }
    if (token.startsWith('-')) {
      continue;
    }
    if (firstPositional === null) {
      firstPositional = token;
    }
  }

  return { firstPositional, hasMachineFlag };
}

function formatSeatNoticeLine(seat) {
  const src = isPlainObject(seat) ? seat : {};
  const seatLabel = sanitizeInlineText(src.label) || sanitizeInlineText(src.accountId) || 'unknown';
  const pinned = src.pinned === true;
  const autoRotate = typeof src.autoRotate === 'boolean' ? src.autoRotate : !pinned;
  const accessType = resolveAccessType(src);
  const ownerLogin = sanitizeInlineText(src.ownerLogin) || null;

  let accessPart = null;
  if (accessType === 'owner') {
    accessPart = 'owner';
  } else if (accessType === 'shared') {
    accessPart = ownerLogin ? `shared by ${ownerLogin}` : 'shared';
  }

  const rotatePart = autoRotate ? 'auto-rotate on' : 'auto-rotate off';
  const details = accessPart ? `${accessPart}, ${rotatePart}` : rotatePart;
  return pinned
    ? `pdd-codex: pinned to "${seatLabel}" (${details})`
    : `pdd-codex: using PDD Cloud seat "${seatLabel}" (${details})`;
}

export function resolveCodexSeatNotice({
  codexArgs = [],
  isInteractiveTty = false,
  seat = null,
} = {}) {
  if (isInteractiveTty !== true) {
    return { shouldPrint: false, reason: 'non_interactive_tty', notice: null };
  }
  const { firstPositional, hasMachineFlag } = inspectCodexNoticeArgs(codexArgs);
  if (firstPositional !== null && NON_INTERACTIVE_SUBCOMMANDS.has(firstPositional)) {
    return { shouldPrint: false, reason: 'non_interactive_subcommand', notice: null };
  }
  if (hasMachineFlag) {
    return { shouldPrint: false, reason: 'machine_output_flag', notice: null };
  }
  return {
    shouldPrint: true,
    reason: 'interactive',
    notice: formatSeatNoticeLine(seat),
  };
}

function findMatchingAccount(entry, codexAccounts) {
  const entryAccountId = trimmedOrNull(entry.account_id);
  if (entryAccountId) {
    const byId = codexAccounts.find(acc => trimmedOrNull(acc?.account_id) === entryAccountId);
    if (byId) return byId;
  }
  const entryLabel = trimmedOrNull(entry.label);
  if (entryLabel) {
    const byLabel = codexAccounts.find(acc => {
      if (trimmedOrNull(acc?.label) !== entryLabel) return false;
      const accId = trimmedOrNull(acc?.account_id);
      return !entryAccountId || !accId || accId === entryAccountId;
    });
    if (byLabel) return byLabel;
  }
  return null;
}

function formatRuntimeStatusLine(lease) {
  const prefix = lease.pinned ? 'Active pdd-codex (pinned)' : 'Active pdd-codex';
  let accessDisplay = 'access: unknown';
  if (lease.access_type === 'owner') {
    accessDisplay = lease.owner_login ? `owner (${lease.owner_login})` : 'owner';
  } else if (lease.access_type === 'shared') {
    accessDisplay = lease.owner_login ? `shared (${lease.owner_login})` : 'shared';
  }
  const rotateDisplay = lease.auto_rotate ? 'auto-rotate: on' : 'auto-rotate: off';
  const sessionsDisplay = lease.live_sessions === 1
    ? '1 live session'
    : `${lease.live_sessions} live sessions`;
  return `${prefix}: ${lease.label} (${accessDisplay}, ${rotateDisplay}, ${sessionsDisplay})`;
}

export function summarizeCodexRuntimeStatus({
  runtimeLeases = [],
  accounts = [],
  cachedActiveCodex = null,
} = {}) {
  const rawList = Array.isArray(runtimeLeases) ? runtimeLeases : [];
  const codexAccounts = (Array.isArray(accounts) ? accounts : []).filter(
    acc => isPlainObject(acc) && (acc.provider === undefined || acc.provider === null || acc.provider === 'codex'),
  );
  const cached = isPlainObject(cachedActiveCodex) ? cachedActiveCodex : null;
  const cachedAccountId = cached ? trimmedOrNull(cached.account_id) : null;

  const normalized = [];
  for (const entry of rawList) {
    if (!isPlainObject(entry)) continue;
    const liveSessions = entry.live_sessions;
    if (typeof liveSessions !== 'number' || !Number.isInteger(liveSessions) || liveSessions < 1) {
      continue;
    }

    const rawLeaseId = trimmedOrNull(entry.lease_id);
    const rawAccountId = trimmedOrNull(entry.account_id);
    const rawLabel = sanitizeInlineText(entry.label);
    if (!rawLeaseId && !rawAccountId && !rawLabel) continue;

    const matchedAccount = findMatchingAccount(entry, codexAccounts);
    const accountId = rawAccountId || trimmedOrNull(matchedAccount?.account_id) || null;
    const cachedMatch = (accountId && cachedAccountId && accountId === cachedAccountId) ? cached : null;

    const pinned = entry.pinned === true || entry.mode === 'pinned';
    const mode = pinned ? 'pinned' : 'shared';
    const autoRotate = typeof entry.auto_rotate === 'boolean' ? entry.auto_rotate : !pinned;
    const label = rawLabel
      || sanitizeInlineText(matchedAccount?.label)
      || sanitizeInlineText(cachedMatch?.label)
      || sanitizeInlineText(accountId)
      || 'unknown';

    let accessType = resolveAccessType(entry);
    if (accessType === 'unknown' && matchedAccount) accessType = resolveAccessType(matchedAccount);
    if (accessType === 'unknown' && cachedMatch) accessType = resolveAccessType(cachedMatch);

    const ownerLogin = sanitizeInlineText(entry.owner_login)
      || sanitizeInlineText(matchedAccount?.owner_login)
      || sanitizeInlineText(cachedMatch?.owner_login)
      || null;

    const expiresAt = trimmedOrNull(entry.expires_at);

    normalized.push({
      mode,
      lease_id: rawLeaseId,
      account_id: accountId,
      label,
      access_type: accessType,
      owner_login: ownerLogin,
      auto_rotate: autoRotate,
      pinned,
      live_sessions: liveSessions,
      expires_at: expiresAt,
    });
  }

  normalized.sort((a, b) => {
    if (a.mode !== b.mode) return a.mode === 'shared' ? -1 : 1;
    const labelCmp = a.label.toLowerCase().localeCompare(b.label.toLowerCase());
    if (labelCmp !== 0) return labelCmp;
    const accCmp = (a.account_id ?? '').localeCompare(b.account_id ?? '');
    if (accCmp !== 0) return accCmp;
    return (a.lease_id ?? '').localeCompare(b.lease_id ?? '');
  });

  if (normalized.length === 0) {
    return {
      codex_runtime: {
        active: false,
        live_sessions: 0,
        label: null,
        account_id: null,
        access_type: null,
        owner_login: null,
        auto_rotate: null,
        pinned: null,
        expires_at: null,
        leases: [],
      },
      lines: [],
    };
  }

  const totalSessions = normalized.reduce((sum, item) => sum + item.live_sessions, 0);
  const primary = normalized[0];
  return {
    codex_runtime: {
      active: true,
      live_sessions: totalSessions,
      label: primary.label,
      account_id: primary.account_id,
      access_type: primary.access_type,
      owner_login: primary.owner_login,
      auto_rotate: primary.auto_rotate,
      pinned: primary.pinned,
      expires_at: primary.expires_at,
      leases: normalized,
    },
    lines: normalized.map(formatRuntimeStatusLine),
  };
}
