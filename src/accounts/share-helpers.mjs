// Generated from prompts/cli/accounts-cli.prompt.md.
// Account lookup, GitHub user resolution, and share/unshare payload helpers.
import { runAgentProcess } from '../shared/agent-process.mjs';
import { sanitizeLabel } from './cli-format.mjs';
import { cloudAccountsRequest, listCloudAccounts } from './cloud-client.mjs';
import { CloudAccountsError } from './cloud-error.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const VALID_SLUG_RE = /^[A-Za-z0-9][A-Za-z0-9._-]{0,79}$/;
const SHARE_ARRAY_FIELDS = ['shares', 'shared_with', 'active_shares', 'pending_shares', 'pending_invites', 'invites', 'accepted_users', 'accepted_logins'];

export async function fetchAccountsList({ cwd, env, refresh = false }, ports = {}) {
  const data = await listCloudAccounts({ refresh, cwd, env }, ports);
  return {
    accounts: Array.isArray(data?.accounts) ? data.accounts : [],
    pendingInvites: Array.isArray(data?.pending_invites) ? data.pending_invites : [],
  };
}

export function isOwnedAccount(acc) {
  if (!acc || acc.revoked) return false;
  return typeof acc.is_owner === 'boolean' ? acc.is_owner === true : acc.shared !== true;
}

export async function resolveGitHubUser(login, { cwd, env }, ports = {}) {
  if (typeof ports.resolveGithubUser === 'function') {
    const info = await ports.resolveGithubUser(login, { cwd, env });
    if (info?.type === 'Organization') {
      throw new CloudAccountsError(`"${login}" is a GitHub organization. Pass --with ${login}/<team> to share with an organization team.`, { code: 'organization_requires_team' });
    }
    if (info?.type && info.type !== 'User') throw new CloudAccountsError(`"${login}" is not a GitHub user account.`, { code: 'invalid_share_target' });
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
    if (ghRes?.code === 0 && ghRes.stdout) parsed = JSON.parse(ghRes.stdout);
  } catch {}
  if (parsed?.type === 'Organization') {
    throw new CloudAccountsError(`"${login}" is a GitHub organization. Pass --with ${login}/<team> to share with an organization team.`, { code: 'organization_requires_team' });
  }
  if (parsed?.type && parsed.type !== 'User') throw new CloudAccountsError(`"${login}" is not a GitHub user account.`, { code: 'invalid_share_target' });
  return {
    login: typeof parsed?.login === 'string' && parsed.login.trim() ? parsed.login.trim() : login,
    id: Number.isSafeInteger(parsed?.id) ? parsed.id : null,
  };
}

export function parseWithTargets(rawWith) {
  const source = String(rawWith ?? '');
  if (!source.trim()) return { targets: [] };
  const seen = new Set(), targets = [];
  for (const rawPart of source.split(',')) {
    const item = rawPart.trim();
    if (!item) return { error: 'Share target list contains an empty entry. Pass --with USER|ORG/TEAM[,...].' };
    if (/\s/.test(item)) return { error: `Invalid share target "${item}". Separate multiple targets with commas.` };
    if (item.startsWith('@')) {
      const org = item.slice(1);
      if (!org || org.includes('/') || !VALID_SLUG_RE.test(org)) return { error: `Invalid organization target "${item}". Use @ORG or ORG/TEAM.` };
      const key = `org:${org.toLowerCase()}`;
      if (!seen.has(key)) { seen.add(key); targets.push({ kind: 'org', raw: item, org }); }
      continue;
    }
    if (item.includes('/')) {
      const [org, team, extra] = item.split('/');
      if (!org || !team || extra || !VALID_SLUG_RE.test(org) || !VALID_SLUG_RE.test(team)) return { error: 'Use ORG/TEAM for team sharing.' };
      const key = `team:${org.toLowerCase()}/${team.toLowerCase()}`;
      if (!seen.has(key)) { seen.add(key); targets.push({ kind: 'team', raw: item, org, team }); }
      continue;
    }
    if (!VALID_SLUG_RE.test(item)) return { error: `Invalid GitHub user target "${item}".` };
    const key = `user:${item.toLowerCase()}`;
    if (!seen.has(key)) { seen.add(key); targets.push({ kind: 'user', raw: item, login: item }); }
  }
  return { targets };
}

export async function resolveSharePayloads(parsedTargets, { cwd, env }, ports = {}) {
  const payloads = [];
  for (const target of parsedTargets) {
    if (target.kind === 'org') payloads.push({ display: `@${target.org}`, body: { org: target.org } });
    else if (target.kind === 'team') payloads.push({ display: `${target.org}/${target.team}`, body: { org: target.org, team: target.team } });
    else {
      const resolved = await resolveGitHubUser(target.login, { cwd, env }, ports);
      const body = { github_login: resolved.login, ...(Number.isSafeInteger(resolved.id) ? { github_user_id: resolved.id } : {}) };
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
  return Number.isSafeInteger(b.github_user_id) ? `uid:${b.github_user_id}` : '';
}

function addRawShareEntryKeys(keys, entry) {
  if (!entry) return;
  if (typeof entry === 'string') {
    const trimmed = entry.trim();
    if (!trimmed) return;
    if (trimmed.startsWith('@')) keys.add(`org:${trimmed.slice(1).toLowerCase()}`);
    else if (trimmed.includes('/')) keys.add(`team:${trimmed.toLowerCase()}`);
    else keys.add(`user:${trimmed.toLowerCase()}`);
    return;
  }
  if (!object(entry)) return;
  const st = typeof entry.state === 'string' ? entry.state.toLowerCase() : '';
  if (['revoked', 'declined', 'cancelled', 'expired'].includes(st)) return;
  if (entry.team && entry.org) { keys.add(`team:${String(entry.org).toLowerCase()}/${String(entry.team).toLowerCase()}`); return; }
  if (typeof entry.team === 'string' && entry.team.includes('/')) { keys.add(`team:${entry.team.toLowerCase()}`); return; }
  if (entry.org) { keys.add(`org:${String(entry.org).toLowerCase()}`); return; }
  const login = entry.github_login ?? entry.recipient_login ?? entry.invited_login ?? entry.login ?? entry.user ?? '';
  if (typeof login === 'string' && login.trim()) keys.add(`user:${login.trim().toLowerCase()}`);
  const uid = entry.github_user_id ?? entry.recipient_github_id ?? entry.user_id ?? null;
  if (Number.isSafeInteger(uid)) keys.add(`uid:${uid}`);
}

export function collectExistingShareKeys(account, pendingInvites = [], sessionSharedKeys = null) {
  const keys = new Set();
  if (!object(account)) return keys;
  const accId = account.account_id;
  for (const field of SHARE_ARRAY_FIELDS) if (Array.isArray(account[field])) for (const entry of account[field]) addRawShareEntryKeys(keys, entry);
  for (const org of Array.isArray(account.org_shares) ? account.org_shares : []) if (typeof org === 'string' && org.trim()) keys.add(`org:${org.trim().replace(/^@/, '').toLowerCase()}`);
  for (const team of Array.isArray(account.team_shares) ? account.team_shares : []) if (typeof team === 'string' && team.trim()) keys.add(`team:${team.trim().toLowerCase()}`);
  for (const uid of Array.isArray(account.accepted_user_ids) ? account.accepted_user_ids : []) if (Number.isSafeInteger(uid)) keys.add(`uid:${uid}`);
  if (accId && Array.isArray(pendingInvites)) for (const inv of pendingInvites) if (inv?.account_id === accId) addRawShareEntryKeys(keys, inv);
  if (accId && sessionSharedKeys instanceof Set) {
    const prefix = `${accId}:`;
    for (const sk of sessionSharedKeys) if (sk.startsWith(prefix)) keys.add(sk.slice(prefix.length));
  }
  return keys;
}

export function extractSharePayloadsFromAccount(account, pendingInvites = []) {
  const existing = [];
  if (!object(account)) return existing;
  const loginToUid = new Map(), coveredUids = new Set();
  const inspectRawEntry = entry => {
    if (!object(entry) || ['revoked', 'declined', 'cancelled', 'expired'].includes(String(entry.state ?? '').toLowerCase()) || entry.team || entry.org) return;
    const rawLogin = entry.github_login ?? entry.recipient_login ?? entry.invited_login ?? entry.login ?? entry.user ?? '';
    const login = typeof rawLogin === 'string' ? rawLogin.trim().toLowerCase() : '';
    const uid = entry.github_user_id ?? entry.recipient_github_id ?? entry.user_id ?? null;
    if (login && Number.isSafeInteger(uid)) { loginToUid.set(login, uid); coveredUids.add(uid); }
  };
  for (const field of SHARE_ARRAY_FIELDS) if (Array.isArray(account[field])) for (const entry of account[field]) inspectRawEntry(entry);
  if (account.account_id && Array.isArray(pendingInvites)) for (const inv of pendingInvites) if (inv?.account_id === account.account_id) inspectRawEntry(inv);
  for (const k of collectExistingShareKeys(account, pendingInvites)) {
    if (k.startsWith('org:')) { const org = k.slice(4); existing.push({ display: `@${org}`, body: { org } }); }
    else if (k.startsWith('team:')) { const [org, team] = k.slice(5).split('/'); if (org && team) existing.push({ display: `${org}/${team}`, body: { org, team } }); }
    else if (k.startsWith('user:')) {
      const login = k.slice(5);
      existing.push({ display: login, body: { github_login: login, ...(loginToUid.has(login) ? { github_user_id: loginToUid.get(login) } : {}) } });
    } else if (k.startsWith('uid:')) {
      const uid = Number(k.slice(4));
      if (Number.isSafeInteger(uid) && !coveredUids.has(uid)) existing.push({ display: `github_user_id:${uid}`, body: { github_user_id: uid } });
    }
  }
  return existing;
}

export function mergeSharePayloads(basePayloads, extraPayloads) {
  const seenKeys = new Set(), uidIndex = new Map(), merged = [];
  for (const item of [...basePayloads, ...extraPayloads]) {
    const key = sharePayloadKey(item);
    if (!key) continue;
    const uid = Number.isSafeInteger(item?.body?.github_user_id) ? item.body.github_user_id : null;
    if (uid !== null && uidIndex.has(uid)) {
      const prevIdx = uidIndex.get(uid);
      if (!merged[prevIdx]?.body?.github_login && item?.body?.github_login) { merged[prevIdx] = item; seenKeys.add(key); }
      continue;
    }
    if (seenKeys.has(key)) continue;
    seenKeys.add(key);
    if (uid !== null) uidIndex.set(uid, merged.length);
    merged.push(item);
  }
  return merged;
}

export async function applySharePayloadsToAccounts(accounts, sharePayloads, { cwd, env, pendingInvites = [], sessionSharedKeys = null }, ports = {}) {
  const notes = [];
  for (const account of accounts) {
    const existingKeys = collectExistingShareKeys(account, pendingInvites, sessionSharedKeys);
    for (const item of sharePayloads) {
      const key = sharePayloadKey(item);
      const uidKey = Number.isSafeInteger(item?.body?.github_user_id) ? `uid:${item.body.github_user_id}` : '';
      if ((key && existingKeys.has(key)) || (uidKey && existingKeys.has(uidKey))) {
        notes.push({ label: account.label ?? account.account_id, display: item.display, inviteId: null, alreadyShared: true });
        continue;
      }
      let res = null;
      try {
        res = await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/share`, { body: item.body, cwd, env }, ports);
      } catch (err) {
        if (err instanceof CloudAccountsError && err.status === 409) {
          notes.push({ label: account.label ?? account.account_id, display: item.display, inviteId: null, alreadyShared: true });
          continue;
        }
        throw err;
      }
      if (key) { existingKeys.add(key); if (account.account_id && sessionSharedKeys instanceof Set) sessionSharedKeys.add(`${account.account_id}:${key}`); }
      if (uidKey) existingKeys.add(uidKey);
      const serverAlreadyShared = Boolean(res?.already_shared === true || ((item?.body?.github_login || item?.body?.github_user_id) && res?.already_shared !== false && !res?.invite && !res?.invite_id));
      notes.push({ label: account.label ?? account.account_id, display: item.display, inviteId: serverAlreadyShared ? null : (res?.invite?.invite_id ?? res?.invite_id ?? null), alreadyShared: serverAlreadyShared });
    }
  }
  return notes;
}

export function buildUnsharePayloads({ userOption, withOption }) {
  const seen = new Set(), payloads = [];
  const rawUser = typeof userOption === 'string' ? userOption.trim() : '';
  if (rawUser) {
    if (!VALID_SLUG_RE.test(rawUser)) return { error: `Invalid GitHub user "${rawUser}".` };
    seen.add(`user:${rawUser.toLowerCase()}`);
    payloads.push({ display: rawUser, body: { github_login: rawUser } });
  }
  const rawWith = typeof withOption === 'string' ? withOption : '';
  if (rawWith.trim()) {
    const parsed = parseWithTargets(rawWith);
    if (parsed.error) return { error: parsed.error };
    for (const target of parsed.targets) {
      if (target.kind === 'org') {
        const key = `org:${target.org.toLowerCase()}`;
        if (!seen.has(key)) { seen.add(key); payloads.push({ display: `@${target.org}`, body: { org: target.org } }); }
      } else if (target.kind === 'team') {
        const key = `team:${target.org.toLowerCase()}/${target.team.toLowerCase()}`;
        if (!seen.has(key)) { seen.add(key); payloads.push({ display: `${target.org}/${target.team}`, body: { org: target.org, team: target.team } }); }
      } else {
        const key = `user:${target.login.toLowerCase()}`;
        if (!seen.has(key)) { seen.add(key); payloads.push({ display: target.login, body: { github_login: target.login } }); }
      }
    }
  }
  return { payloads };
}

export function formatShareSuffix(shareNotes) {
  if (!shareNotes.length) return '';
  return ` Shared with ${shareNotes.map(n => (n.inviteId ? `${n.display} (invite ${n.inviteId})` : n.alreadyShared ? `${n.display} (already shared)` : n.display)).join(', ')}.`;
}

export async function resolveAccount(labelOrId, { cwd, env, provider = null }, ports = {}) {
  const target = String(labelOrId ?? '').trim();
  if (!target) throw new CloudAccountsError('Account label is required.', { code: 'missing_label', exitCode: 2 });
  const { accounts, pendingInvites } = await fetchAccountsList({ cwd, env }, ports);
  const candidates = (provider ? accounts.filter(a => !a.revoked && a.provider === provider) : accounts.filter(a => !a.revoked));
  const pickTier = matches => {
    if (matches.length === 1) return { account: matches[0], accounts, pendingInvites };
    if (matches.length > 1) {
      const providers = [...new Set(matches.map(a => a.provider).filter(Boolean))];
      if (!provider && providers.length > 1) {
        throw new CloudAccountsError(`Account label "${target}" exists for multiple providers (${providers.join(', ')}). Pass ${providers.map(p => `--provider ${p}`).join(' or ')}.`, { code: 'ambiguous_provider', exitCode: 2 });
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
    const bySanitized = pickTier(candidates.filter(a => { const l = String(a.label ?? ''); return l.toLowerCase() === sanitized || sanitizeLabel(l, '') === sanitized; }));
    if (bySanitized) return bySanitized;
  }
  throw new CloudAccountsError(`Account "${target}"${provider ? ` for provider "${provider}"` : ''} was not found. Run pdd accounts list.`, { code: 'not_found' });
}
