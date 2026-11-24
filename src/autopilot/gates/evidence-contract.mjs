// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: 75fde4547979ce8f760b5cb49996fe40b92c8567837622ceac4c2dd1c41f41ce).
// ZERO LLM numeric confidence scores, ZERO hardcoded model names, ZERO hardcoded capability names.
import { createHash } from 'node:crypto';
import { posix } from 'node:path';

export const GAP_CHECK_FLAGS = Object.freeze(['UNMAPPED_CHANGE', 'INSUFFICIENT_SCOPE']);
export const FORMAL_PROOF_TIERS = Object.freeze(['proved_solver_code', 'proved_spec_model']);
export const HOLD_REASONS = Object.freeze([
  'malformed_output', 'abstention', 'stale_evidence', 'missing_capability',
  'protected_path', 'unmapped_change', 'insufficient_scope', 'service_failure',
]);
export const RECEIPT_OUTCOMES = Object.freeze(['proved', 'failed', 'missing_capability', 'service_failure']);
export const REQUIRED_RECEIPT_FIELDS = Object.freeze([
  'repo', 'acRevision', 'targetTip', 'candidateHead', 'integratedTree',
  'trustedPolicyDigest', 'recipeDigest', 'testProfile', 'command',
  'toolchain', 'capability', 'outcome', 'artifactDigest',
]);
export const RECEIPT_BINDING_FIELDS = Object.freeze([
  'repo', 'acRevision', 'targetTip', 'candidateHead', 'integratedTree', 'trustedPolicyDigest', 'recipeDigest',
]);

const GAP_ALLOWED_KEYS = new Set(['missingPathIds', 'unprovedAcIds', 'flags']);
const GAP_FLAG_SET = new Set(GAP_CHECK_FLAGS);
const FORMAL_TIER_SET = new Set(FORMAL_PROOF_TIERS);
const RECEIPT_OUTCOME_SET = new Set(RECEIPT_OUTCOMES);
const DEFAULT_PROTECTED_BASENAMES = new Set(['pdd.json', 'pdd-workspace.json', 'pdd-bindings.json', 'package.json', 'codeowners']);
const DEFAULT_PROTECTED_EXACT = new Set(['src/autopilot-core.mjs', 'src/autopilot-validator.mjs']);
const DEFAULT_PROTECTED_PREFIXES = ['.github/workflows/', '.github/actions/', 'rules/lint/', 'src/autopilot/core/', 'src/autopilot/gates/', 'src/autopilot/validator/', '.venv/', 'venv/'];
const DEFAULT_PROTECTED_SCRIPT_RE = /^scripts\/(?:.*\/)?(?:check-[^/]+|verify-[^/]+|[^/]*gate[^/]*)\.(?:[cm]?js|ts|sh|py|rb)$/i;
const TEST_FILE_PATH_RE = /(?:(?:^|\/)(?:test|tests|__tests__|spec)\/|\.(?:test|spec)\.[a-z0-9]+$|_test\.(?:go|rs|py)$|(?:^|\/)test_[^/]+\.py$)/i;
const NON_PRODUCTION_PROOF_PATH_RE = /(?:^(?:prompts|docs|user_stories|specs?|models?)\/|\.prompt\.md$|\.mdx?$|^(?:test|tests|__tests__|spec)\/|\.(?:test|spec)\.[a-z0-9]+$|_test\.(?:go|rs|py)$|(?:^|\/)test_[^/]+\.py$)/i;
const HOLD_PRIORITY = ['protected_path', 'malformed_output', 'stale_evidence', 'service_failure', 'abstention', 'missing_capability', 'unmapped_change', 'insufficient_scope'];

const isPlainObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
const nonEmptyStr = (v) => typeof v === 'string' && v.trim().length > 0;

function canonicalizeRepoPath(rawPath) {
  if (typeof rawPath !== 'string') return { path: '', invalid: true };
  const trimmed = rawPath.trim();
  if (!trimmed || trimmed.includes('\0')) return { path: trimmed, invalid: true };
  const slashed = trimmed.replace(/\\/g, '/');
  if (slashed.startsWith('/') || /^[A-Za-z]:\//.test(slashed)) return { path: slashed, invalid: true };
  const normalized = posix.normalize(slashed).replace(/^(?:\.\/)+/, '');
  if (!normalized || normalized === '.' || normalized === '..' || normalized.startsWith('../')) return { path: normalized || trimmed, invalid: true };
  return { path: normalized, invalid: false };
}

function canonicalize(value) {
  if (Array.isArray(value)) return value.map(canonicalize);
  if (!isPlainObj(value)) return value;
  const out = {};
  for (const key of Object.keys(value).sort()) out[key] = canonicalize(value[key]);
  return out;
}

export const computeCanonicalDigest = (payload) =>
  createHash('sha256').update(JSON.stringify(canonicalize(payload))).digest('hex');

function compileGlob(pattern) {
  const norm = String(pattern ?? '').trim().replace(/\\/g, '/').replace(/\/+/g, '/').replace(/^(?:\.\/)+/, '');
  if (!norm) return null;
  let re = '^';
  for (let i = 0; i < norm.length; i += 1) {
    if (norm[i] === '*' && norm[i + 1] === '*') {
      if (norm[i + 2] === '/') { re += '(?:.+/)?'; i += 2; } else { re += '.*'; i += 1; }
    } else if (norm[i] === '*') re += '[^/]*';
    else if (norm[i] === '?') re += '[^/]';
    else if (/[.+^${}()|[\]\\]/.test(norm[i])) re += `\\${norm[i]}`;
    else re += norm[i];
  }
  return new RegExp(`${re}$`, 'i');
}

function matchGlobPattern(path, pattern) {
  if (pattern instanceof RegExp) return new RegExp(pattern.source, pattern.flags.replace(/[gy]/g, '')).test(path);
  const re = compileGlob(pattern);
  return re ? re.test(path) : false;
}

export function isProtectedPath(rawPath, extraPatterns = []) {
  const { path, invalid } = canonicalizeRepoPath(rawPath);
  if (invalid) return true;
  const lower = path.toLowerCase();
  return DEFAULT_PROTECTED_BASENAMES.has(posix.basename(lower))
    || DEFAULT_PROTECTED_EXACT.has(lower)
    || DEFAULT_PROTECTED_PREFIXES.some((prefix) => lower.startsWith(prefix))
    || DEFAULT_PROTECTED_SCRIPT_RE.test(path)
    || (Array.isArray(extraPatterns) && extraPatterns.some((pat) => matchGlobPattern(path, pat)));
}

/** Check 4: Zero protected paths touched without explicit human approval. */
export function checkProtectedPaths({ changedFiles = [], humanApprovedPaths = [], protectedPatterns = [] } = {}) {
  if (!Array.isArray(changedFiles)) return { ok: false, unapprovedProtectedPaths: [], holdReason: 'malformed_output', details: 'changedFiles must be an array.' };
  if (!Array.isArray(humanApprovedPaths)) return { ok: false, unapprovedProtectedPaths: [], holdReason: 'malformed_output', details: 'humanApprovedPaths must be an array.' };
  const approved = new Set();
  for (const raw of humanApprovedPaths) { const c = canonicalizeRepoPath(raw); if (!c.invalid) approved.add(c.path.toLowerCase()); }
  const unapproved = new Set();
  for (const raw of changedFiles) {
    const c = canonicalizeRepoPath(raw);
    if (c.invalid) unapproved.add(`invalid:${String(raw ?? '')}`);
    else if (isProtectedPath(c.path, protectedPatterns) && !approved.has(c.path.toLowerCase())) unapproved.add(c.path);
  }
  const list = [...unapproved].sort();
  return {
    ok: list.length === 0, unapprovedProtectedPaths: list, holdReason: list.length ? 'protected_path' : null,
    details: list.length ? `Protected path(s) modified without explicit human approval: ${list.join(', ')}` : 'No unapproved protected paths touched.',
  };
}

function normalizeProductionProofModules(list) {
  const out = new Set();
  for (const raw of Array.isArray(list) ? list : []) {
    const c = canonicalizeRepoPath(raw);
    if (!c.invalid && !NON_PRODUCTION_PROOF_PATH_RE.test(c.path)) out.add(c.path);
  }
  return [...out].sort();
}

function hasFailingProductionMutationControl(mc) {
  if (typeof mc === 'string') return mc.trim().toLowerCase() === 'failed-on-mutation';
  if (!isPlainObj(mc)) return false;
  return mc.executed === true && mc.failedOnMutation === true && mc.mutatedProductionCode !== false && mc.passedOnMutation !== true;
}

/**
 * #3151 code-bound formal proof classifier:
 * distinguishes `proved_solver_code` vs `proved_spec_model`.
 * A formal/solver proof satisfies code verification ONLY when it imports/executes production modules
 * (covering all `targetModules` if supplied) AND passes a failing production-code mutation control.
 */
export function classifyFormalProofTier(proof, { targetModules = [] } = {}) {
  if (!isPlainObj(proof)) {
    return {
      tier: 'proved_spec_model',
      satisfiesCodeVerification: false,
      holdReason: 'insufficient_scope',
      importedProductionModules: [],
      executedProductionModules: [],
      mutationControlPassed: false,
      reason: 'Formal proof record is missing or malformed; cannot satisfy code verification (proved_spec_model).',
    };
  }
  const importedProductionModules = normalizeProductionProofModules([
    ...(Array.isArray(proof.importedProductionModules) ? proof.importedProductionModules : []),
    ...(Array.isArray(proof.productionModules) ? proof.productionModules : []),
  ]);
  const executedProductionModules = normalizeProductionProofModules([
    ...(Array.isArray(proof.executedProductionModules) ? proof.executedProductionModules : []),
    ...(Array.isArray(proof.productionModules) ? proof.productionModules : []),
  ]);
  const coveredModules = new Set([...importedProductionModules, ...executedProductionModules]);
  const normalizedTargets = normalizeProductionProofModules(
    Array.isArray(targetModules) && targetModules.length
      ? targetModules
      : (Array.isArray(proof.targetModules) ? proof.targetModules : (nonEmptyStr(proof.targetModule) ? [proof.targetModule] : [])),
  );
  const coversTargets = normalizedTargets.length === 0
    ? coveredModules.size > 0
    : normalizedTargets.every((m) => coveredModules.has(m));
  const mutationControlPassed = hasFailingProductionMutationControl(proof.mutationControl);
  const isCodeBound = coveredModules.size > 0 && coversTargets && mutationControlPassed;

  if (isCodeBound) {
    return {
      tier: 'proved_solver_code',
      satisfiesCodeVerification: true,
      holdReason: null,
      importedProductionModules,
      executedProductionModules,
      mutationControlPassed: true,
      reason: 'Formal proof imported/executed production module(s) and verified a failing production-code mutation control (proved_solver_code).',
    };
  }
  const gaps = [];
  if (coveredModules.size === 0) gaps.push('did not import or execute production modules');
  else if (!coversTargets) gaps.push(`missing production module coverage for [${normalizedTargets.filter((m) => !coveredModules.has(m)).join(', ')}]`);
  if (!mutationControlPassed) gaps.push('missing failing production-code mutation control');
  return {
    tier: 'proved_spec_model',
    satisfiesCodeVerification: false,
    holdReason: 'insufficient_scope',
    importedProductionModules,
    executedProductionModules,
    mutationControlPassed,
    reason: `Formal proof classified as proved_spec_model (${gaps.join('; ')}); cannot satisfy code verification.`,
  };
}

/** Check #3151 code-bound formal proof rule across formal proof records. */
export function checkFormalProofBinding({ formalProofs = [], targetModules = [], requireCodeVerification = false } = {}) {
  if (!Array.isArray(formalProofs)) {
    return { ok: false, tier: null, provedCodeProofs: [], specModelOnlyProofs: [], holdReason: 'malformed_output', details: 'formalProofs must be an array.' };
  }
  const provedCodeProofs = [];
  const specModelOnlyProofs = [];
  let rejectedClaim = false;
  for (const proof of formalProofs) {
    const classified = classifyFormalProofTier(proof, { targetModules });
    if (classified.tier === 'proved_solver_code') {
      provedCodeProofs.push({ ...classified, id: isPlainObj(proof) && nonEmptyStr(proof.id) ? proof.id.trim() : null });
    } else {
      const claimedCode = isPlainObj(proof) && (
        proof.satisfiesCode === true
        || proof.forCodeVerification === true
        || proof.tier === 'proved_solver_code'
        || proof.proofTier === 'proved_solver_code'
      );
      if (claimedCode) rejectedClaim = true;
      specModelOnlyProofs.push({ ...classified, id: isPlainObj(proof) && nonEmptyStr(proof.id) ? proof.id.trim() : null, claimedCode });
    }
  }
  if (rejectedClaim || (requireCodeVerification && provedCodeProofs.length === 0)) {
    const reason = specModelOnlyProofs[0]?.reason
      || 'Code-bound formal proof (proved_solver_code) is required to satisfy code verification.';
    return {
      ok: false,
      tier: specModelOnlyProofs.length > 0 ? 'proved_spec_model' : null,
      provedCodeProofs,
      specModelOnlyProofs,
      holdReason: 'insufficient_scope',
      details: reason,
    };
  }
  return {
    ok: true,
    tier: provedCodeProofs.length > 0 ? 'proved_solver_code' : (specModelOnlyProofs.length > 0 ? 'proved_spec_model' : null),
    provedCodeProofs,
    specModelOnlyProofs,
    holdReason: null,
    details: provedCodeProofs.length > 0
      ? `${provedCodeProofs.length} code-bound formal proof(s) verified (proved_solver_code).`
      : 'No code-bound formal proof required.',
  };
}

/** Check 2: Every touched user path has a green harness-written receipt bound to all 13 contract fields. */
export function checkPathReceipts({
  touchedPaths = [], receipts = [], expectedBinding = null, availableCapabilities = null, requiredCapabilitiesByPath = {},
} = {}) {
  if (!Array.isArray(touchedPaths) || !Array.isArray(receipts)) {
    return { ok: false, provedPathIds: [], missingPathIds: [], stalePathIds: [], failedPathIds: [], missingCapabilities: [], holdReason: 'malformed_output', details: 'touchedPaths and receipts must be arrays.' };
  }
  const paths = [...new Set(touchedPaths.map((p) => String(p ?? '').trim()).filter(Boolean))].sort();
  const capSet = availableCapabilities instanceof Set ? availableCapabilities
    : (Array.isArray(availableCapabilities) ? new Set(availableCapabilities.map((c) => String(c ?? '').trim()).filter(Boolean)) : null);
  const bindingValid = isPlainObj(expectedBinding) && RECEIPT_BINDING_FIELDS.every((f) => nonEmptyStr(expectedBinding[f]));

  if ((paths.length > 0 || receipts.length > 0) && !bindingValid) {
    return {
      ok: false, provedPathIds: [], missingPathIds: paths, stalePathIds: paths.length ? paths : ['binding:missing'],
      failedPathIds: [], missingCapabilities: [], holdReason: 'stale_evidence',
      details: 'Expected receipt binding context missing required repo/revision/tip/tree/digest fields.',
    };
  }

  const provedCurrentPaths = new Set(), failedCurrentPaths = new Set(), hardStalePathIds = new Set(), oldHeadPathIds = new Set();
  const missingCapabilities = new Set(), malformedReasons = [], formalSpecModelReasons = [];
  let sawBoundServiceFailure = false;

  for (const r of receipts) {
    if (!isPlainObj(r)) { malformedReasons.push('non-object receipt'); continue; }
    if (r.writtenBy !== 'harness') { malformedReasons.push('receipt writtenBy must be strictly "harness"'); continue; }
    const missingField = REQUIRED_RECEIPT_FIELDS.find((f) => !Object.hasOwn(r, f) || (f === 'capability' ? (r.capability !== null && !nonEmptyStr(r.capability)) : !nonEmptyStr(r[f])));
    if (missingField) { malformedReasons.push(`receipt missing or empty field "${missingField}"`); continue; }
    if (!RECEIPT_OUTCOME_SET.has(r.outcome)) { malformedReasons.push(`receipt has invalid outcome "${String(r.outcome)}"`); continue; }

    const receiptPaths = [...new Set([...(nonEmptyStr(r.pathId) ? [r.pathId.trim()] : []), ...(Array.isArray(r.pathIds) ? r.pathIds.filter(nonEmptyStr).map((p) => p.trim()) : [])])];
    const mismatchedFields = bindingValid ? RECEIPT_BINDING_FIELDS.filter((f) => r[f] !== expectedBinding[f]) : [];
    if (mismatchedFields.length > 0) {
      // Stale/mismatched receipts NEVER earn service_failure free retries and NEVER prove paths.
      const isOldHead = r.candidateHead !== expectedBinding.candidateHead || r.integratedTree !== expectedBinding.integratedTree;
      const targetSet = isOldHead && receiptPaths.length > 0 ? oldHeadPathIds : hardStalePathIds;
      if (receiptPaths.length) for (const p of receiptPaths) targetSet.add(p);
      else hardStalePathIds.add(`mismatch:${mismatchedFields[0]}`);
      continue;
    }
    if (r.outcome === 'service_failure') { sawBoundServiceFailure = true; continue; }
    if (r.outcome === 'missing_capability') { missingCapabilities.add(nonEmptyStr(r.capability) && r.capability !== 'none' ? r.capability.trim() : 'unknown'); continue; }
    if (r.outcome === 'failed') { if (receiptPaths.length) for (const p of receiptPaths) failedCurrentPaths.add(p); else failedCurrentPaths.add('receipt:failed'); continue; }
    if (capSet && nonEmptyStr(r.capability) && r.capability !== 'none' && !capSet.has(r.capability.trim())) { missingCapabilities.add(r.capability.trim()); continue; }
    // #3151: A formal/solver receipt cannot prove code verification unless classified as `proved_solver_code`.
    const isFormalReceipt = isPlainObj(r.formalProof) || r.proofKind === 'formal' || (nonEmptyStr(r.proofTier) && FORMAL_TIER_SET.has(r.proofTier.trim()));
    if (isFormalReceipt) {
      const classified = classifyFormalProofTier(isPlainObj(r.formalProof) ? r.formalProof : r, {
        targetModules: Array.isArray(r.targetModules) ? r.targetModules : [],
      });
      if (!classified.satisfiesCodeVerification) {
        formalSpecModelReasons.push(classified.reason);
        if (receiptPaths.length) for (const p of receiptPaths) failedCurrentPaths.add(p);
        else failedCurrentPaths.add('receipt:proved_spec_model');
        continue;
      }
    }
    for (const p of receiptPaths) provedCurrentPaths.add(p);
  }

  for (const p of failedCurrentPaths) provedCurrentPaths.delete(p);
  const stalePathIds = new Set(hardStalePathIds);
  for (const p of oldHeadPathIds) if (!provedCurrentPaths.has(p) || failedCurrentPaths.has(p)) stalePathIds.add(p);

  const missingPathIds = [];
  for (const pathId of paths) {
    if (provedCurrentPaths.has(pathId)) continue;
    missingPathIds.push(pathId);
    const reqCaps = requiredCapabilitiesByPath?.[pathId];
    if (capSet && Array.isArray(reqCaps)) for (const c of reqCaps) if (nonEmptyStr(c) && !capSet.has(c.trim())) missingCapabilities.add(c.trim());
  }

  const stale = [...stalePathIds].sort(), failed = [...failedCurrentPaths].sort(), missingCaps = [...missingCapabilities].sort();
  const ok = !malformedReasons.length && !stale.length && !sawBoundServiceFailure && !missingCaps.length && !failed.length && !missingPathIds.length;
  const holdReason = ok ? null : malformedReasons.length ? 'malformed_output' : stale.length ? 'stale_evidence' : sawBoundServiceFailure ? 'service_failure' : missingCaps.length ? 'missing_capability' : 'insufficient_scope';
  return {
    ok, provedPathIds: [...provedCurrentPaths].sort(), missingPathIds, stalePathIds: stale, failedPathIds: failed, missingCapabilities: missingCaps, holdReason,
    details: ok ? `All ${paths.length} touched path(s) have valid bound harness receipts.`
      : (malformedReasons[0] || (stale.length ? `Stale/mismatched receipt binding for: ${stale.join(', ')}` : sawBoundServiceFailure ? 'Harness reported bound service_failure during verification.' : missingCaps.length ? `Missing capability: ${missingCaps.join(', ')}` : formalSpecModelReasons[0] || (failed.length ? `Current-head receipt failed for: ${failed.join(', ')}` : `Missing proved receipt(s) for path(s): ${missingPathIds.join(', ')}`))),
  };
}

/** Check 1: Every frozen numbered AC maps to ALL its harness-required passing test IDs and proved user paths. */
export function checkAcCoverage({ frozenAcs = [], testResults = [], provedPathIds = [], acMapping = {}, requireFrozenAcs = true } = {}) {
  if (!Array.isArray(frozenAcs) || !Array.isArray(testResults) || !Array.isArray(provedPathIds)) {
    return { ok: false, unprovedAcIds: [], holdReason: 'malformed_output', details: 'frozenAcs, testResults, and provedPathIds must be arrays.' };
  }
  if (requireFrozenAcs && frozenAcs.length === 0) return { ok: false, unprovedAcIds: [], holdReason: 'insufficient_scope', details: 'No frozen acceptance criteria supplied.' };

  // Strict provenance allowlist: ONLY harness-emitted passing test results count; never trust test-declared acIds.
  const passingTests = new Set();
  for (const t of testResults) if (isPlainObj(t) && nonEmptyStr(t.id) && t.source === 'harness' && t.proseOnly !== true && t.status === 'pass') passingTests.add(t.id.trim());
  const provedPaths = new Set(provedPathIds.filter(nonEmptyStr).map((p) => p.trim()));
  const unprovedAcIds = [];

  for (const rawAc of frozenAcs) {
    const id = typeof rawAc === 'string' ? rawAc.trim() : (isPlainObj(rawAc) && nonEmptyStr(rawAc.id) ? rawAc.id.trim() : '');
    if (!id) return { ok: false, unprovedAcIds: [], holdReason: 'malformed_output', details: 'Frozen AC entry missing id.' };
    const mapped = isPlainObj(acMapping?.[id]) ? acMapping[id] : {};
    const reqTestIds = [...new Set([...(isPlainObj(rawAc) && Array.isArray(rawAc.requiredTestIds) ? rawAc.requiredTestIds : []), ...(isPlainObj(rawAc) && Array.isArray(rawAc.testIds) ? rawAc.testIds : []), ...(Array.isArray(mapped.testIds) ? mapped.testIds : [])].filter(nonEmptyStr).map((x) => x.trim()))];
    const reqPathIds = [...new Set([...(isPlainObj(rawAc) && Array.isArray(rawAc.requiredPathIds) ? rawAc.requiredPathIds : []), ...(isPlainObj(rawAc) && Array.isArray(rawAc.pathIds) ? rawAc.pathIds : []), ...(Array.isArray(mapped.pathIds) ? mapped.pathIds : [])].filter(nonEmptyStr).map((x) => x.trim()))];
    if ((!reqTestIds.length && !reqPathIds.length) || !reqTestIds.every((tid) => passingTests.has(tid)) || !reqPathIds.every((pid) => provedPaths.has(pid))) unprovedAcIds.push(id);
  }
  return {
    ok: unprovedAcIds.length === 0, unprovedAcIds, holdReason: unprovedAcIds.length ? 'insufficient_scope' : null,
    details: unprovedAcIds.length ? `Frozen AC(s) lack complete harness-verified test/path coverage (prose & agent self-attestation excluded): ${unprovedAcIds.join(', ')}` : `All ${frozenAcs.length} frozen AC(s) verified by harness results.`,
  };
}

/** Check 3: Zero unapproved missing/skipped/unknown test IDs AND strict allowlist base-owned edited-test oracle. */
export function checkTestOracle({
  testResults = [], expectedTestIds = [], approvedSkippedIds = [], baseOracle = null,
  editedTestFiles = null, changedFiles = [], requireBaseOracle = true,
  reportDiffVerdict = null, reportReadErrors = [],
} = {}) {
  const failMalformed = (details) => ({ ok: false, badTestIds: [], unlistedOracleFailures: [], oracleUnknowns: [], holdReason: 'malformed_output', details });
  if (!Array.isArray(testResults) || !Array.isArray(expectedTestIds) || !Array.isArray(approvedSkippedIds)) return failMalformed('testResults, expectedTestIds, and approvedSkippedIds must be arrays.');
  if (editedTestFiles !== null && !Array.isArray(editedTestFiles)) return failMalformed('editedTestFiles must be an array.');
  if (!Array.isArray(reportReadErrors)) return failMalformed('reportReadErrors must be an array.');

  const approved = new Set(approvedSkippedIds.filter(nonEmptyStr).map((x) => x.trim()));
  const seenIds = new Set(), badTestIds = [];
  for (const t of testResults) {
    if (!isPlainObj(t) || !nonEmptyStr(t.id)) return failMalformed('Malformed test result entry.');
    const id = t.id.trim();
    if (t.source !== 'harness') { badTestIds.push(`${id}:untrusted-source`); continue; }
    seenIds.add(id);
    if (t.status === 'pass') continue;
    if ((t.status === 'skip' || t.status === 'skipped' || t.status === 'missing') && approved.has(id)) continue;
    badTestIds.push(`${id}:${String(t.status ?? 'unknown')}`);
  }
  for (const exp of expectedTestIds) if (nonEmptyStr(exp) && !seenIds.has(exp.trim()) && !approved.has(exp.trim())) badTestIds.push(`${exp.trim()}:missing`);

  const effectiveEditedTests = Array.isArray(editedTestFiles) ? editedTestFiles.filter(nonEmptyStr) : (Array.isArray(changedFiles) ? changedFiles.filter((f) => nonEmptyStr(f) && TEST_FILE_PATH_RE.test(f)) : []);
  const unlistedOracleFailures = [], oracleUnknowns = [];
  let sawServiceFailure = false, oracleMalformed = null;

  // Un-spoofable harness report comparator veto and report-read errors (completely independent of testResults IDs).
  for (const err of reportReadErrors) {
    if (nonEmptyStr(err)) oracleUnknowns.push(err.trim());
  }
  if (reportDiffVerdict !== null && reportDiffVerdict !== undefined) {
    if (!isPlainObj(reportDiffVerdict)) oracleMalformed = 'Malformed reportDiffVerdict object.';
    else if (reportDiffVerdict.verdict !== 'ALLOW' || reportDiffVerdict.status !== 'pass') {
      const status = nonEmptyStr(reportDiffVerdict.status) ? reportDiffVerdict.status.trim() : 'hold';
      const reason = nonEmptyStr(reportDiffVerdict.reason) ? `:${reportDiffVerdict.reason.trim()}` : '';
      oracleUnknowns.push(`report-diff:${status}${reason}`);
    }
  }

  if (baseOracle === null || baseOracle === undefined) {
    if (requireBaseOracle !== false || effectiveEditedTests.length > 0) oracleUnknowns.push('oracle:missing');
  } else if (!isPlainObj(baseOracle)) oracleMalformed = 'Malformed baseOracle object.';
  else if (!nonEmptyStr(baseOracle.status)) oracleMalformed = 'baseOracle missing required status field.';
  else {
    const status = baseOracle.status.trim();
    if (status === 'service_failure') sawServiceFailure = true;
    else if (status === 'not-applicable') { if (effectiveEditedTests.length > 0) oracleUnknowns.push('oracle:not-applicable-with-edited-tests'); }
    else if (status !== 'passed') oracleUnknowns.push(`oracle:${status}`);
    if (baseOracle.results !== undefined && !Array.isArray(baseOracle.results)) oracleMalformed = 'baseOracle.results must be an array.';
    else {
      const expectedFails = new Set((Array.isArray(baseOracle.expectedFailIds) ? baseOracle.expectedFailIds : []).filter(nonEmptyStr).map((x) => x.trim()));
      for (const r of Array.isArray(baseOracle.results) ? baseOracle.results : []) {
        if (!isPlainObj(r) || !nonEmptyStr(r.id) || !nonEmptyStr(r.status)) { oracleUnknowns.push('oracle:malformed-row'); continue; }
        const id = r.id.trim(), st = r.status.trim();
        if (st === 'pass' || (st === 'fail' && expectedFails.has(id))) continue;
        if (st === 'fail' || st === 'failed') unlistedOracleFailures.push(id);
        else oracleUnknowns.push(`${id}:${st}`);
      }
    }
    if (baseOracle.unlistedFailures !== undefined && !Array.isArray(baseOracle.unlistedFailures)) oracleMalformed = 'baseOracle.unlistedFailures must be an array.';
    else for (const id of baseOracle.unlistedFailures ?? []) if (nonEmptyStr(id)) unlistedOracleFailures.push(id.trim());
    if (baseOracle.unknowns !== undefined && !Array.isArray(baseOracle.unknowns)) oracleMalformed = 'baseOracle.unknowns must be an array.';
    else for (const id of baseOracle.unknowns ?? []) if (nonEmptyStr(id)) oracleUnknowns.push(id.trim());
  }

  if (oracleMalformed) return { ok: false, badTestIds: [...new Set(badTestIds)].sort(), unlistedOracleFailures: [...new Set(unlistedOracleFailures)].sort(), oracleUnknowns: [...new Set(oracleUnknowns)].sort(), holdReason: 'malformed_output', details: oracleMalformed };
  const ok = !sawServiceFailure && !badTestIds.length && !unlistedOracleFailures.length && !oracleUnknowns.length;
  return {
    ok, badTestIds: [...new Set(badTestIds)].sort(), unlistedOracleFailures: [...new Set(unlistedOracleFailures)].sort(), oracleUnknowns: [...new Set(oracleUnknowns)].sort(),
    holdReason: ok ? null : (sawServiceFailure ? 'service_failure' : 'insufficient_scope'),
    details: ok ? 'Zero unapproved skipped/missing/unknown tests and base-owned edited-test oracle passed.' : `Test oracle violation(s): bad=${badTestIds.length}, unlistedOracleFailures=${unlistedOracleFailures.length}, oracleUnknowns=${oracleUnknowns.length}.`,
  };
}

/** Build prompt-injection-safe gap-check input (ZERO PR title, PR body, comments, or commit prose). */
export function buildGapCheckInput({ diffStat = '', changedFiles = [], frozenAcs = [], touchedPaths = [], provedPathIds = [], testSummary = {} } = {}) {
  return {
    diffStat: String(diffStat ?? '').slice(0, 8000),
    changedFiles: (Array.isArray(changedFiles) ? changedFiles : []).map((f) => canonicalizeRepoPath(f)).filter((c) => !c.invalid).map((c) => c.path).sort(),
    frozenAcs: (Array.isArray(frozenAcs) ? frozenAcs : []).map((ac) => (typeof ac === 'string' ? { id: ac.trim() } : { id: String(ac?.id ?? '').trim(), text: String(ac?.text ?? '').trim() })).filter((ac) => ac.id),
    touchedPaths: (Array.isArray(touchedPaths) ? touchedPaths : []).filter(nonEmptyStr).map((p) => p.trim()).sort(),
    provedPathIds: (Array.isArray(provedPathIds) ? provedPathIds : []).filter(nonEmptyStr).map((p) => p.trim()).sort(),
    testSummary: isPlainObj(testSummary) ? { passed: Number(testSummary.passed ?? 0), failed: Number(testSummary.failed ?? 0), skipped: Number(testSummary.skipped ?? 0) } : { passed: 0, failed: 0, skipped: 0 },
  };
}

/** Validate narrow closed-set cross-family gap-check output (ZERO numeric confidence/score fields allowed). */
export function validateGapCheckOutput(raw) {
  const fail = (details) => ({ ok: false, holdReason: 'malformed_output', missingPathIds: [], unprovedAcIds: [], flags: [], details });
  if (!isPlainObj(raw)) return fail('Gap check output must be a JSON object.');
  for (const k of Object.keys(raw)) if (!GAP_ALLOWED_KEYS.has(k)) return fail(`Forbidden/unknown key "${k}" in gap-check output (no scores or extra fields allowed).`);
  for (const req of GAP_ALLOWED_KEYS) if (!Array.isArray(raw[req])) return fail(`Gap check field "${req}" must be an array.`);
  if (!raw.missingPathIds.every(nonEmptyStr) || !raw.unprovedAcIds.every(nonEmptyStr)) return fail('missingPathIds and unprovedAcIds must contain non-empty strings.');
  if (!raw.flags.every((f) => typeof f === 'string' && GAP_FLAG_SET.has(f))) return fail(`flags may only contain closed-set values: ${GAP_CHECK_FLAGS.join(', ')}.`);
  const missingPathIds = [...new Set(raw.missingPathIds.map((s) => s.trim()))].sort();
  const unprovedAcIds = [...new Set(raw.unprovedAcIds.map((s) => s.trim()))].sort();
  const flags = [...new Set(raw.flags)].sort();
  const hasGap = missingPathIds.length > 0 || unprovedAcIds.length > 0 || flags.length > 0;
  const holdReason = !hasGap ? null : (flags.includes('UNMAPPED_CHANGE') ? 'unmapped_change' : 'insufficient_scope');
  return { ok: !hasGap, holdReason, missingPathIds, unprovedAcIds, flags, details: !hasGap ? 'Cross-family gap check found no unmapped changes or unproved ACs.' : `Gap check flagged: ${holdReason}.` };
}

/** Evaluate the full 4-Check Non-Compensatory Mechanical Evidence Contract + #3151 formal proof binding + cross-family gap check. */
export function evaluateEvidenceContract({
  changedFiles = [], humanApprovedPaths = [], protectedPatterns = [], frozenAcs = [], acMapping = {}, requireFrozenAcs = true,
  touchedPaths = [], receipts = [], expectedBinding = null, availableCapabilities = null, requiredCapabilitiesByPath = {},
  testResults = [], expectedTestIds = [], approvedSkippedIds = [], baseOracle = null, editedTestFiles = null, requireBaseOracle = true,
  reportDiffVerdict = null, reportReadErrors = [],
  formalProofs = [], formalTargetModules = [], requireCodeBoundFormal = false,
  gapCheck = null, requireGapCheck = true, serviceFailure = null, abstained = false,
} = {}) {
  const protectedPaths = checkProtectedPaths({ changedFiles, humanApprovedPaths, protectedPatterns });
  const pathReceipts = checkPathReceipts({ touchedPaths, receipts, expectedBinding, availableCapabilities, requiredCapabilitiesByPath });
  const acCoverage = checkAcCoverage({ frozenAcs, testResults, provedPathIds: pathReceipts.provedPathIds, acMapping, requireFrozenAcs });
  const testOracle = checkTestOracle({ testResults, expectedTestIds, approvedSkippedIds, baseOracle, editedTestFiles, changedFiles, requireBaseOracle, reportDiffVerdict, reportReadErrors });
  const formalProofBinding = checkFormalProofBinding({ formalProofs, targetModules: formalTargetModules, requireCodeVerification: requireCodeBoundFormal });

  let gapResult;
  if (serviceFailure) gapResult = { ok: false, skipped: false, holdReason: 'service_failure', missingPathIds: [], unprovedAcIds: [], flags: [], details: String(serviceFailure) };
  else if (abstained === true) gapResult = { ok: false, skipped: false, holdReason: 'abstention', missingPathIds: [], unprovedAcIds: [], flags: [], details: 'Cross-family gap checker abstained.' };
  else if (gapCheck === null || gapCheck === undefined) {
    gapResult = requireGapCheck === false
      ? { ok: true, skipped: true, holdReason: null, missingPathIds: [], unprovedAcIds: [], flags: [], details: 'Gap check explicitly optional.' }
      : { ok: false, skipped: false, holdReason: 'abstention', missingPathIds: [], unprovedAcIds: [], flags: [], details: 'Cross-family gap check output is required.' };
  } else gapResult = { ...validateGapCheckOutput(gapCheck), skipped: false };

  const reasons = [];
  for (const c of [protectedPaths, pathReceipts, acCoverage, testOracle, formalProofBinding, gapResult]) if (!c.ok && c.holdReason && !reasons.includes(c.holdReason)) reasons.push(c.holdReason);
  if (serviceFailure && !reasons.includes('service_failure')) reasons.push('service_failure');

  const holdReason = HOLD_PRIORITY.find((r) => reasons.includes(r)) ?? null;
  const ok = holdReason === null && protectedPaths.ok && pathReceipts.ok && acCoverage.ok && testOracle.ok && formalProofBinding.ok && gapResult.ok;
  return {
    decision: ok ? 'MERGE' : 'HOLD', ok, holdReason, holdReasons: reasons,
    burnRepairStrike: !ok && holdReason !== 'service_failure',
    checks: { acCoverage, pathReceipts, testOracle, protectedPaths, formalProofBinding, gapCheck: gapResult },
    summary: ok ? 'All 4 non-compensatory mechanical evidence checks and gap check passed.'
      : `HOLD (${holdReason}): ${[protectedPaths, pathReceipts, acCoverage, testOracle, formalProofBinding, gapResult].filter((c) => !c.ok).map((c) => c.details).join(' | ')}`,
  };
}
