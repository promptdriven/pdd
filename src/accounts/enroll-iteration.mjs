// Generated from prompts/cli/accounts-cli.prompt.md.
// Single Codex or Claude enrollment/import iteration.
import * as nativeFs from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { pddManagedCodexHome, stopCodexAppServerDaemon } from '../login-pool.mjs';
import {
  defaultAccountLabel,
  deriveEmailBaseLabel,
  detectCodexPlan,
  extractCodexEmail,
  nextDisambiguatedLabel,
  sanitizeLabel,
} from './cli-format.mjs';
import {
  createTempPrivateDir,
  extractIsolatedClaudeSetupToken,
  leaseAndSyncAfterEnroll,
  probeInitialCodexUsageIfUnpopulated,
  removeTempPrivateDir,
  runProviderLogin,
} from './enroll-login.mjs';
import { runEnrollLoop, uploadAccountWithConflictAndRetry } from './enroll-upload.mjs';
import {
  assertNonSymlinkImportFile,
  readClaudeTokenFromPath,
  readCodexFullAuthBundle,
  readLocalClaudeToken,
  readStdinString,
  resolveCodexImportSource,
  scrubImportedCodexSourceRefreshToken,
} from './import-auth.mjs';
import { applySharePayloadsToAccounts, fetchAccountsList, formatShareSuffix } from './share-helpers.mjs';

export async function enrollSingleIteration(mode, {
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
      let authJson, bundle, probeCodexHome = null, importSourcePath = null;
      if (mode === 'add') {
        tempLoginDir = createTempPrivateDir(fs, 'pdd-codex-login-', ports.tmpRoot, env);
        const loginEnv = { ...env, CODEX_HOME: tempLoginDir };
        const loginRes = await runProviderLogin('codex', { cwd, env: loginEnv, deviceAuth, stdin }, ports);
        if (!loginRes || loginRes.code !== 0) {
          return { exitCode: 1, aborted: loginRes?.code === 130 || loginRes?.signal === 'SIGINT', message: 'codex login did not complete.' };
        }
        ({ authJson, bundle } = readCodexFullAuthBundle(fs, loginEnv, join(tempLoginDir, 'auth.json')));
        probeCodexHome = tempLoginDir;
      } else {
        const importSource = resolveCodexImportSource(fs, cwd, env, fromOption);
        ({ authJson, bundle } = readCodexFullAuthBundle(fs, env, assertNonSymlinkImportFile(fs, importSource.authPath, env)));
        probeCodexHome = importSource.probeCodexHome;
        importSourcePath = importSource.authPath;
      }

      const email = extractCodexEmail(authJson), emailBase = deriveEmailBaseLabel(authJson);
      const subjectAccountId = bundle.auth_json.tokens.account_id;
      const seenLabel = loopState ? (loopState.bySubjectId.get(subjectAccountId) ?? null) : null;
      const labelWasExplicit = Boolean(requestedLabel && String(requestedLabel).trim()) || Boolean(loopState?.hasExplicitPrefix);
      let knownAccounts = loopState?.knownAccounts ?? null, knownPendingInvites = loopState?.knownPendingInvites ?? [];
      const usedLabels = loopState ? loopState.usedLabels : new Set();

      let baseLabel, candidateLabel;
      if (loopState) {
        if (seenLabel) { baseLabel = seenLabel; candidateLabel = seenLabel; }
        else if (loopState.hasExplicitPrefix) { candidateLabel = loopState.peekNextNumberedLabel(); baseLabel = candidateLabel; }
        else if (emailBase) {
          baseLabel = emailBase;
          candidateLabel = replace ? nextDisambiguatedLabel(emailBase, loopState.sessionEnrolledLabels) : nextDisambiguatedLabel(emailBase, usedLabels);
        } else { candidateLabel = loopState.peekNextNumberedLabel(); baseLabel = candidateLabel; }
      } else if (requestedLabel && String(requestedLabel).trim()) {
        baseLabel = sanitizeLabel(requestedLabel, ''); candidateLabel = baseLabel;
      } else {
        baseLabel = defaultAccountLabel('codex', authJson);
        if (!replace && emailBase) {
          try {
            const listed = await fetchAccountsList({ cwd, env, refresh: false }, ports);
            knownAccounts = listed.accounts; knownPendingInvites = listed.pendingInvites;
            for (const item of knownAccounts) if (item && !item.revoked && item.provider === 'codex' && item.label) usedLabels.add(String(item.label).toLowerCase());
            candidateLabel = nextDisambiguatedLabel(emailBase, usedLabels);
          } catch { candidateLabel = baseLabel; }
        } else { candidateLabel = baseLabel; }
      }
      if (!candidateLabel) return { exitCode: 2, message: 'Provide a valid --label NAME.' };

      const upload = await uploadAccountWithConflictAndRetry({
        provider: 'codex', initialLabel: candidateLabel, baseLabel, labelWasExplicit, replace,
        plan: detectCodexPlan(authJson), bundle, sharePayloads, sourceHint: importSourcePath,
        knownAccounts, knownPendingInvites, usedLabels, interactive, cwd, env, stdin, stdout,
      }, ports);
      if (upload.skipped) return { exitCode: 0, skipped: true, label: upload.candidateLabel, message: upload.message };

      const { created, effectiveSharePayloads, pendingInvites: uploadInvites } = upload;
      candidateLabel = upload.candidateLabel;
      let acc = created?.account ?? { account_id: created?.account_id ?? candidateLabel, label: candidateLabel, provider: 'codex' };
      const isDuplicate = Boolean(created?.already_enrolled === true || seenLabel || (loopState && acc.account_id && loopState.seenAccountIds.has(acc.account_id)));
      acc = await probeInitialCodexUsageIfUnpopulated(acc, authJson, probeCodexHome, { fs, cwd, env }, ports);
      if (tempLoginDir) { removeTempPrivateDir(fs, tempLoginDir); tempLoginDir = null; }

      const leaseResult = await leaseAndSyncAfterEnroll('codex', acc, candidateLabel, null, null, { cwd, env }, ports);
      const leaseMaterialized = leaseResult?.materialized === true;
      const scrubbedSource = mode === 'import' && importSourcePath && leaseMaterialized ? scrubImportedCodexSourceRefreshToken(fs, importSourcePath, env) : false;
      if (scrubbedSource) {
        const sourceCodexHome = dirname(importSourcePath), managedHome = pddManagedCodexHome(env);
        let sameHome = resolve(sourceCodexHome) === resolve(managedHome);
        if (!sameHome) {
          try { const realFn = fs.realpathSync?.native ?? fs.realpathSync; if (typeof realFn === 'function') sameHome = realFn.call(fs, sourceCodexHome) === realFn.call(fs, managedHome); } catch {}
        }
        if (!sameHome) stopCodexAppServerDaemon(sourceCodexHome, { env, fs, spawnSync: ports.spawnSync });
      }

      const finalLabel = acc.label ?? candidateLabel;
      if (loopState) {
        if (subjectAccountId) loopState.bySubjectId.set(subjectAccountId, finalLabel);
        if (acc.account_id) loopState.seenAccountIds.add(acc.account_id);
        if (!isDuplicate) loopState.commitCandidateLabel(candidateLabel, finalLabel, Boolean(loopState.hasExplicitPrefix || !emailBase));
      }
      const shareNotes = effectiveSharePayloads.length
        ? await applySharePayloadsToAccounts([acc], effectiveSharePayloads, { cwd, env, pendingInvites: uploadInvites, sessionSharedKeys: loopState?.sharedKeys ?? null }, ports)
        : [];
      const shareSuffix = formatShareSuffix(shareNotes);
      if (isDuplicate) {
        return { exitCode: 0, duplicate: true, account: acc, label: finalLabel, email, shareNotes, message: `Already enrolled as ${finalLabel} — refreshed credentials. Existing shares remain active.${shareSuffix}` };
      }
      const identityNote = email ? `${email} -> "${finalLabel}", ` : '';
      const materializationNote = leaseMaterialized ? `materialized in ${pddManagedCodexHome(env)}` : `lease pending for ${pddManagedCodexHome(env)}`;
      const importNote = scrubbedSource
        ? ` (scrubbed single-use refresh_token from ${importSourcePath} so local codex cannot invalidate Cloud refresh.)`
        : (mode === 'import' && importSourcePath && !leaseMaterialized ? ` (left ${importSourcePath} unscrubbed because local lease materialization did not complete.)` : '');
      return { exitCode: 0, duplicate: false, account: acc, label: finalLabel, email, shareNotes, message: `Enrolled Codex account "${finalLabel}" in PDD Cloud (${identityNote}${materializationNote}).${shareSuffix}${importNote}` };
    } finally { removeTempPrivateDir(fs, tempLoginDir); }
  }

  let oauthToken = '', tempClaudeDir = null;
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
          return { exitCode: 1, aborted: loginRes?.code === 130 || loginRes?.signal === 'SIGINT', message: 'claude setup-token did not complete.' };
        }
        oauthToken = extractIsolatedClaudeSetupToken(fs, tempClaudeDir, `${loginRes?.stdout ?? ''}\n${loginRes?.stderr ?? ''}`, ports.now);
        removeTempPrivateDir(fs, tempClaudeDir); tempClaudeDir = null;
      }
    } else if (fromOption) {
      oauthToken = readClaudeTokenFromPath(fs, resolve(cwd, String(fromOption).trim()), { now: ports.now });
    } else {
      oauthToken = readLocalClaudeToken(fs, env, await readStdinString(stdin), { now: ports.now });
    }
  } finally { removeTempPrivateDir(fs, tempClaudeDir); }

  const labelWasExplicit = Boolean(requestedLabel && String(requestedLabel).trim()) || Boolean(loopState?.hasExplicitPrefix);
  const candidateLabel = loopState ? loopState.peekNextNumberedLabel() : (requestedLabel ? sanitizeLabel(requestedLabel, '') : defaultAccountLabel('claude'));
  if (!candidateLabel) return { exitCode: 2, message: 'Provide a valid --label NAME.' };

  const upload = await uploadAccountWithConflictAndRetry({
    provider: 'claude', initialLabel: candidateLabel, baseLabel: candidateLabel, labelWasExplicit, replace,
    plan: 'max', bundle: { oauth_token: oauthToken }, sharePayloads,
    knownAccounts: loopState?.knownAccounts ?? null, knownPendingInvites: loopState?.knownPendingInvites ?? [],
    usedLabels: loopState?.usedLabels ?? null, interactive, cwd, env, stdin, stdout,
  }, ports);
  if (upload.skipped) return { exitCode: 0, skipped: true, label: upload.candidateLabel, message: upload.message };

  const { created, effectiveSharePayloads, pendingInvites: uploadInvites } = upload;
  const resolvedLabel = upload.candidateLabel;
  const acc = created?.account ?? { account_id: created?.account_id ?? resolvedLabel, label: resolvedLabel, provider: 'claude' };
  const isDuplicate = Boolean(created?.already_enrolled === true || (loopState && acc.account_id && loopState.seenAccountIds.has(acc.account_id)));
  await leaseAndSyncAfterEnroll('claude', acc, resolvedLabel, null, null, { cwd, env }, ports);
  const finalLabel = acc.label ?? resolvedLabel;
  if (loopState) {
    if (acc.account_id) loopState.seenAccountIds.add(acc.account_id);
    if (!isDuplicate) loopState.commitCandidateLabel(resolvedLabel, finalLabel, true);
  }
  const shareNotes = effectiveSharePayloads.length
    ? await applySharePayloadsToAccounts([acc], effectiveSharePayloads, { cwd, env, pendingInvites: uploadInvites, sessionSharedKeys: loopState?.sharedKeys ?? null }, ports)
    : [];
  const shareSuffix = formatShareSuffix(shareNotes);
  return {
    exitCode: 0, duplicate: isDuplicate, account: acc, label: finalLabel, shareNotes,
    message: isDuplicate
      ? `Already enrolled as ${finalLabel} — refreshed credentials. Existing shares remain active.${shareSuffix}`
      : `Enrolled Claude account "${finalLabel}" in PDD Cloud.${shareSuffix}`,
  };
}

export function enrollOrImportAccount(mode, opts, ports = {}) {
  return runEnrollLoop(enrollSingleIteration, mode, opts, ports);
}
