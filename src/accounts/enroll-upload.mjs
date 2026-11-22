// Generated from prompts/cli/accounts-cli.prompt.md.
// Account upload conflict/retry resolution and single/loop enrollment orchestration.
import * as nativeFs from 'node:fs';
import { CloudAccountsError, cloudAccountsRequest } from '../login-pool.mjs';
import { redactSecrets } from '../secret-redaction.mjs';
import { nextDisambiguatedLabel, sanitizeLabel } from './cli-format.mjs';
import { askLoopContinue, askPromptRaw } from './enroll-login.mjs';
import { detectImportProvider } from './import-auth.mjs';
import {
  extractSharePayloadsFromAccount,
  fetchAccountsList,
  isOwnedAccount,
  mergeSharePayloads,
  parseWithTargets,
  resolveSharePayloads,
} from './share-helpers.mjs';

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
  const shareNote = backup.shares.length ? ` (preserved shares: --with ${backup.shares.join(',')})` : '';
  const sourceNote = sourceHint ? ` Local credential file "${sourceHint}" was left unscrubbed.` : '';
  return ` Previous ${provider} account "${backup.label}" (${backup.account_id}) was removed before the replacement upload failed${shareNote}.${sourceNote} Re-run enroll/import to restore "${backup.label}".`;
}

export async function uploadAccountWithConflictAndRetry({
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
  let inheritedShares = [], deletedExistingId = null, deletedBackup = null;

  const ensureAccountsLoaded = async () => {
    if (!cachedAccounts) {
      try {
        const fetched = await fetchAccountsList({ cwd, env, refresh: false }, ports);
        cachedAccounts = fetched.accounts; cachedInvites = fetched.pendingInvites;
      } catch { cachedAccounts = []; }
    }
    for (const item of cachedAccounts) {
      if (item && !item.revoked && item.provider === provider && item.label) labelSet.add(String(item.label).toLowerCase());
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
    deletedBackup = { account_id: existingOwned.account_id, label: existingOwned.label ?? candidateLabel, shares: inheritedShares.map(s => s.display) };
    cachedAccounts = (cachedAccounts ?? []).filter(a => a.account_id !== existingOwned.account_id);
  };

  if (replace && Array.isArray(cachedAccounts)) {
    const prior = findExistingOwnedSameLabel(candidateLabel);
    if (prior) inheritedShares = extractSharePayloadsFromAccount(prior, cachedInvites);
  }

  for (let attempt = 0; attempt < 12; attempt += 1) {
    try {
      const created = await cloudAccountsRequest('POST', '/v1/accounts', { body: { label: candidateLabel, provider, plan, bundle }, cwd, env }, ports);
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
      return { skipped: false, created, candidateLabel, effectiveSharePayloads: mergeSharePayloads(inheritedShares, sharePayloads), pendingInvites: cachedInvites };
    } catch (err) {
      if (isDuplicateLabelConflictError(err)) {
        await ensureAccountsLoaded();
        labelSet.add(candidateLabel.toLowerCase());
        const existingOwned = findExistingOwnedSameLabel(candidateLabel);
        if (replace && existingOwned && existingOwned.account_id !== deletedExistingId) { await deleteConfirmedExisting(existingOwned); continue; }
        if (!labelWasExplicit) { candidateLabel = nextDisambiguatedLabel(baseLabel || candidateLabel, labelSet); continue; }
        if (interactive) {
          const disambiguated = nextDisambiguatedLabel(baseLabel || candidateLabel, labelSet);
          const choice = await askPromptRaw(`Account label "${candidateLabel}" already exists for ${provider}. [r]eplace existing, save as "${disambiguated}", or [s]kip? [r/2/s] `, { stdin, stdout }, ports);
          const norm = choice === undefined || choice === null ? 's' : String(choice).trim().toLowerCase();
          if ((norm === 'r' || norm === 'replace') && existingOwned && existingOwned.account_id !== deletedExistingId) { await deleteConfirmedExisting(existingOwned); continue; }
          if (['2', 'd', 'n', 'new', 'y', 'yes', ''].includes(norm)) { candidateLabel = disambiguated; continue; }
          if (norm === 's' || norm === 'skip' || choice === false) return { skipped: true, candidateLabel, message: `Skipped enrolling ${provider} account "${candidateLabel}".` };
          const customLabel = sanitizeLabel(norm, '');
          candidateLabel = (customLabel && !labelSet.has(customLabel.toLowerCase())) ? customLabel : disambiguated;
          continue;
        }
        const hint = /--replace/.test(err.message) ? '' : ' Pass --replace to replace the existing account.';
        throw new CloudAccountsError(`${err.message}${hint}`, { status: err.status || 409, code: err.code || 'duplicate_label', payload: err.payload });
      }
      if (interactive && isTransientUploadError(err)) {
        const retryAns = await askPromptRaw(`Upload failed (${err.message}). [R]etry upload without signing in again, or [s]kip? [R/s] `, { stdin, stdout }, ports);
        const normRetry = retryAns === false || retryAns === undefined || retryAns === null ? 's' : String(retryAns).trim().toLowerCase();
        if (['s', 'skip', 'n', 'no'].includes(normRetry)) {
          return { skipped: true, candidateLabel, message: `Skipped ${provider} account "${candidateLabel}" after upload failure.${formatDeletedAccountRecoverySummary(deletedBackup, provider, sourceHint)}` };
        }
        continue;
      }
      if (deletedBackup) {
        throw new CloudAccountsError(`${err.message}${formatDeletedAccountRecoverySummary(deletedBackup, provider, sourceHint)}`, { status: err.status, code: err.code, payload: err.payload, exitCode: err.exitCode });
      }
      throw err;
    }
  }
  throw new CloudAccountsError(`Unable to enroll ${provider} account "${candidateLabel}" after multiple attempts.${formatDeletedAccountRecoverySummary(deletedBackup, provider, sourceHint)}`, { code: 'enroll_failed' });
}

export async function runEnrollLoop(enrollSingleIterationFn, mode, {
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
  if (deviceAuth && provider === 'claude') return { exitCode: 2, message: '--device-auth is only supported for Codex accounts.' };

  let sharePayloads = [];
  if (typeof rawWith === 'string' && rawWith.trim()) {
    const parsedWith = parseWithTargets(rawWith);
    if (parsedWith.error) return { exitCode: 2, message: parsedWith.error };
    if (!parsedWith.targets.length) return { exitCode: 2, message: 'Pass at least one target to --with USER|ORG/TEAM[,...].' };
    sharePayloads = await resolveSharePayloads(parsedWith.targets, { cwd, env }, ports);
  }

  if (!loop) {
    const single = await enrollSingleIterationFn(mode, {
      provider, requestedLabel, replace, fromOption, deviceAuth, sharePayloads, loopState: null, cwd, env, stdin,
    }, ports);
    return { exitCode: single.exitCode, message: single.message };
  }

  const promptFn = ports.prompt ?? ports.confirm ?? null;
  const stdout = ports.stdout ?? process.stdout;
  if (!(Boolean(promptFn) || Boolean(stdin?.isTTY && stdout?.isTTY))) {
    return { exitCode: 2, message: '--loop requires an interactive terminal (TTY).' };
  }

  const hasExplicitPrefix = Boolean(requestedLabel && String(requestedLabel).trim());
  const prefix = sanitizeLabel(requestedLabel || provider, provider);
  const { accounts: initialAccounts, pendingInvites: initialInvites } = await fetchAccountsList({ cwd, env, refresh: false }, ports);
  const usedLabels = new Set(), seenAccountIds = new Set();
  for (const existing of initialAccounts) {
    if (!existing || existing.revoked) continue;
    if (existing.provider === provider && existing.label) usedLabels.add(String(existing.label).toLowerCase());
    if (existing.account_id) seenAccountIds.add(existing.account_id);
  }

  let counter = 1;
  const loopState = {
    hasExplicitPrefix, knownAccounts: initialAccounts, knownPendingInvites: initialInvites,
    usedLabels, sessionEnrolledLabels: new Set(), bySubjectId: new Map(), seenAccountIds, sharedKeys: new Set(),
    peekNextNumberedLabel() { while (!replace && usedLabels.has(`${prefix}-${counter}`.toLowerCase())) counter += 1; return `${prefix}-${counter}`; },
    commitCandidateLabel(candidate, actual, advanceCounter = true) {
      usedLabels.add(String(candidate).toLowerCase()); this.sessionEnrolledLabels.add(String(candidate).toLowerCase());
      if (actual) { usedLabels.add(String(actual).toLowerCase()); this.sessionEnrolledLabels.add(String(actual).toLowerCase()); }
      if (advanceCounter) counter += 1;
    },
  };

  const streamedLive = !promptFn && Boolean(stdin?.isTTY && stdout?.isTTY);
  const iterationMessages = [], enrolledLabels = [], refreshedLabels = [];
  for (let iteration = 0; ; iteration += 1) {
    const banner = `--- Account #${iteration + 1} (${provider}, ${hasExplicitPrefix ? `prefix "${prefix}"` : 'auto-label from account'}, ${enrolledLabels.length} enrolled so far) ---`;
    if (streamedLive) stdout.write(`\n${banner}\n`);
    const step = await enrollSingleIterationFn('add', {
      provider, requestedLabel: null, replace, fromOption: null, deviceAuth, sharePayloads, loopState, cwd, env, stdin,
    }, ports);
    if (step.exitCode !== 0) {
      if (step.aborted) break;
      if (iteration === 0) return { exitCode: step.exitCode, message: step.message };
      iterationMessages.push(banner, step.message);
      break;
    }
    if (!step.skipped) {
      if (step.duplicate) { if (!refreshedLabels.includes(step.label) && !enrolledLabels.includes(step.label)) refreshedLabels.push(step.label); }
      else if (!enrolledLabels.includes(step.label)) enrolledLabels.push(step.label);
    }
    if (streamedLive) stdout.write(`${redactSecrets(step.message)}\n`);
    else iterationMessages.push(banner, step.message);
    if (!(await askLoopContinue(`Enroll another ${provider} account? [Y/n] `, { stdin, stdout }, ports))) break;
  }

  const shareSummary = sharePayloads.length ? `, shared with ${sharePayloads.map(p => p.display).join(', ')}` : '';
  const summaryParts = [];
  if (enrolledLabels.length) summaryParts.push(`enrolled ${enrolledLabels.length} ${provider} account${enrolledLabels.length === 1 ? '' : 's'} (${enrolledLabels.join(', ')})`);
  if (refreshedLabels.length) summaryParts.push(`refreshed ${refreshedLabels.length} existing (${refreshedLabels.join(', ')})`);
  const summary = summaryParts.length ? `Loop summary: ${summaryParts.join('; ')}${shareSummary}.` : `Loop finished with 0 ${provider} accounts enrolled.`;
  return { exitCode: 0, message: redactSecrets(streamedLive ? summary : [...iterationMessages, summary].join('\n')) };
}
