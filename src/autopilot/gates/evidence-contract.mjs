// Layer-2 2026 4-Check Non-Compensatory Mechanical Evidence Contract + closed-set cross-family gap check.
// ZERO LLM numeric confidence scores, ZERO hardcoded model names, ZERO hardcoded capability names.
import { createHash } from 'node:crypto';

export const GAP_CHECK_FLAGS = Object.freeze(['UNMAPPED_CHANGE', 'INSUFFICIENT_SCOPE']);
export const HOLD_REASONS = Object.freeze([
  'malformed_output', 'abstention', 'stale_evidence', 'missing_capability',
  'protected_path', 'unmapped_change', 'insufficient_scope', 'service_failure',
]);
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
const DEFAULT_PROTECTED_EXACT = new Set(['pdd.json', 'pdd-workspace.json', 'pdd-bindings.json', 'codeowners', '.github/codeowners', 'docs/codeowners']);
const DEFAULT_PROTECTED_PREFIXES = ['.github/workflows/', '.github/actions/', 'rules/lint/', 'src/autopilot/gates/', 'src/autopilot/validator/'];
const DEFAULT_PROTECTED_SCRIPT_RE = /^scripts\/(?:check-[^/]+|[^/]*gate[^/]*)\.(?:[cm]?js|ts|sh|py)$/i;
const HOLD_PRIORITY = ['service_failure', 'protected_path', 'malformed_output', 'abstention', 'stale_evidence', 'missing_capability', 'unmapped_change', 'insufficient_scope'];

const isPlainObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
const nonEmptyStr = (v) => typeof v === 'string' && v.trim().length > 0;
const normPath = (p) => String(p ?? '').trim().replace(/\\/g, '/').replace(/\/+/g, '/').replace(/^\.\//, '');

function canonicalize(value) {
  if (Array.isArray(value)) return value.map(canonicalize);
  if (!isPlainObj(value)) return value;
  const out = {};
  for (const key of Object.keys(value).sort()) out[key] = canonicalize(value[key]);
  return out;
}

export const computeCanonicalDigest = (payload) =>
  createHash('sha256').update(JSON.stringify(canonicalize(payload))).digest('hex');

function matchGlobPattern(path, pattern) {
  if (pattern instanceof RegExp) return pattern.test(path);
  const normPat = normPath(pattern);
  if (!normPat) return false;
  if (normPat.endsWith('/**')) return path.startsWith(normPat.slice(0, -2));
  if (!normPat.includes('*')) return path === normPat || path.toLowerCase() === normPat.toLowerCase();
  return new RegExp(`^${normPat.replace(/[.+?^${}()|[\]\\]/g, '\\$&').replace(/\*\*/g, '.*').replace(/\*/g, '[^/]*')}$`, 'i').test(path);
}

export function isProtectedPath(rawPath, extraPatterns = []) {
  const path = normPath(rawPath);
  if (!path) return false;
  const lower = path.toLowerCase();
  return DEFAULT_PROTECTED_EXACT.has(lower) || lower.endsWith('/codeowners')
    || DEFAULT_PROTECTED_PREFIXES.some((prefix) => lower.startsWith(prefix))
    || DEFAULT_PROTECTED_SCRIPT_RE.test(path)
    || (Array.isArray(extraPatterns) && extraPatterns.some((pat) => matchGlobPattern(path, pat)));
}

/** Check 4: Zero protected paths touched without explicit human approval. */
export function checkProtectedPaths({ changedFiles = [], humanApprovedPaths = [], protectedPatterns = [] } = {}) {
  const approved = new Set((Array.isArray(humanApprovedPaths) ? humanApprovedPaths : []).map(normPath).filter(Boolean));
  const unapproved = [...new Set((Array.isArray(changedFiles) ? changedFiles : []).map(normPath).filter((f) => f && isProtectedPath(f, protectedPatterns) && !approved.has(f)))].sort();
  return {
    ok: unapproved.length === 0,
    unapprovedProtectedPaths: unapproved,
    holdReason: unapproved.length ? 'protected_path' : null,
    details: unapproved.length ? `Protected path(s) modified without explicit human approval: ${unapproved.join(', ')}` : 'No unapproved protected paths touched.',
  };
}

/** Check 2: Every touched user path has a green harness-written receipt bound to all 13 contract fields. */
export function checkPathReceipts({
  touchedPaths = [], receipts = [], expectedBinding = null, availableCapabilities = null, requiredCapabilitiesByPath = {},
} = {}) {
  const paths = [...new Set((Array.isArray(touchedPaths) ? touchedPaths : []).map((p) => String(p ?? '').trim()).filter(Boolean))].sort();
  const capSet = availableCapabilities instanceof Set ? availableCapabilities
    : (Array.isArray(availableCapabilities) ? new Set(availableCapabilities.map((c) => String(c ?? '').trim()).filter(Boolean)) : null);
  const bindingValid = isPlainObj(expectedBinding) && RECEIPT_BINDING_FIELDS.every((f) => nonEmptyStr(expectedBinding[f]));

  if (paths.length > 0 && !bindingValid) {
    return {
      ok: false, provedPathIds: [], missingPathIds: paths, stalePathIds: paths, missingCapabilities: [],
      holdReason: 'stale_evidence', details: 'Expected receipt binding context missing required repo/revision/tip/tree/digest fields.',
    };
  }

  const provedPathIds = new Set(), stalePathIds = new Set(), missingCapabilities = new Set(), malformedReasons = [];
  let sawServiceFailure = false;

  for (const r of Array.isArray(receipts) ? receipts : []) {
    if (!isPlainObj(r)) { malformedReasons.push('non-object receipt'); continue; }
    if (r.writtenBy === 'agent' || r.writtenBy === 'prose') { malformedReasons.push('receipt must be harness-written, not agent/prose attested'); continue; }
    const receiptPaths = [...(nonEmptyStr(r.pathId) ? [r.pathId.trim()] : []), ...(Array.isArray(r.pathIds) ? r.pathIds.filter(nonEmptyStr).map((p) => p.trim()) : [])];
    const missingField = REQUIRED_RECEIPT_FIELDS.find((f) => !Object.hasOwn(r, f) || (f === 'capability' ? (r.capability !== null && !nonEmptyStr(r.capability)) : !nonEmptyStr(r[f])));
    if (missingField) { malformedReasons.push(`receipt missing or empty field "${missingField}"`); continue; }
    if (r.outcome === 'service_failure') { sawServiceFailure = true; continue; }
    if (r.outcome === 'missing_capability') { if (nonEmptyStr(r.capability) && r.capability !== 'none') missingCapabilities.add(r.capability.trim()); continue; }
    if (bindingValid) {
      const mismatch = RECEIPT_BINDING_FIELDS.find((f) => r[f] !== expectedBinding[f]);
      if (mismatch) { for (const p of receiptPaths) stalePathIds.add(p); if (!receiptPaths.length) stalePathIds.add(`mismatch:${mismatch}`); continue; }
    }
    if (capSet && nonEmptyStr(r.capability) && r.capability !== 'none' && !capSet.has(r.capability.trim())) { missingCapabilities.add(r.capability.trim()); continue; }
    if (r.outcome === 'proved') for (const p of receiptPaths) provedPathIds.add(p);
  }

  const missingPathIds = [];
  for (const pathId of paths) {
    if (provedPathIds.has(pathId)) continue;
    missingPathIds.push(pathId);
    const reqCaps = requiredCapabilitiesByPath?.[pathId];
    if (capSet && Array.isArray(reqCaps)) for (const c of reqCaps) if (nonEmptyStr(c) && !capSet.has(c.trim())) missingCapabilities.add(c.trim());
  }

  const stale = [...stalePathIds].sort(), missingCaps = [...missingCapabilities].sort();
  const ok = !sawServiceFailure && !malformedReasons.length && !stale.length && !missingCaps.length && !missingPathIds.length;
  const holdReason = ok ? null : sawServiceFailure ? 'service_failure' : malformedReasons.length ? 'malformed_output' : stale.length ? 'stale_evidence' : missingCaps.length ? 'missing_capability' : 'insufficient_scope';
  return {
    ok, provedPathIds: [...provedPathIds].sort(), missingPathIds, stalePathIds: stale, missingCapabilities: missingCaps, holdReason,
    details: ok ? `All ${paths.length} touched path(s) have valid bound harness receipts.`
      : (malformedReasons[0] || (stale.length ? `Stale/mismatched receipt binding for: ${stale.join(', ')}` : missingCaps.length ? `Missing capability: ${missingCaps.join(', ')}` : `Missing proved receipt(s) for path(s): ${missingPathIds.join(', ')}`)),
  };
}

/** Check 1: Every frozen numbered AC maps to a verified passing test ID or proved user path (prose is NEVER evidence). */
export function checkAcCoverage({ frozenAcs = [], testResults = [], provedPathIds = [], acMapping = {}, requireFrozenAcs = true } = {}) {
  if (!Array.isArray(frozenAcs)) return { ok: false, unprovedAcIds: [], holdReason: 'malformed_output', details: 'frozenAcs must be an array.' };
  if (requireFrozenAcs && frozenAcs.length === 0) return { ok: false, unprovedAcIds: [], holdReason: 'insufficient_scope', details: 'No frozen acceptance criteria supplied.' };

  const passingTests = new Set(), testsByAc = new Map();
  for (const t of Array.isArray(testResults) ? testResults : []) {
    if (!isPlainObj(t) || !nonEmptyStr(t.id) || t.source === 'prose' || t.proseOnly === true || t.status !== 'pass') continue;
    const id = t.id.trim();
    passingTests.add(id);
    for (const acId of Array.isArray(t.acIds) ? t.acIds : []) {
      if (!nonEmptyStr(acId)) continue;
      if (!testsByAc.has(acId.trim())) testsByAc.set(acId.trim(), new Set());
      testsByAc.get(acId.trim()).add(id);
    }
  }
  const provedPaths = new Set((Array.isArray(provedPathIds) ? provedPathIds : []).filter(nonEmptyStr).map((p) => p.trim()));
  const unprovedAcIds = [];

  for (const rawAc of frozenAcs) {
    const id = typeof rawAc === 'string' ? rawAc.trim() : (isPlainObj(rawAc) && nonEmptyStr(rawAc.id) ? rawAc.id.trim() : '');
    if (!id) return { ok: false, unprovedAcIds: [], holdReason: 'malformed_output', details: 'Frozen AC entry missing id.' };
    const mapped = isPlainObj(acMapping?.[id]) ? acMapping[id] : {};
    const testIds = [
      ...(isPlainObj(rawAc) && Array.isArray(rawAc.requiredTestIds) ? rawAc.requiredTestIds : []),
      ...(isPlainObj(rawAc) && Array.isArray(rawAc.testIds) ? rawAc.testIds : []),
      ...(Array.isArray(mapped.testIds) ? mapped.testIds : []),
      ...(testsByAc.get(id) ?? []),
    ].filter(nonEmptyStr).map((x) => x.trim());
    const pathIds = [
      ...(isPlainObj(rawAc) && Array.isArray(rawAc.requiredPathIds) ? rawAc.requiredPathIds : []),
      ...(isPlainObj(rawAc) && Array.isArray(rawAc.pathIds) ? rawAc.pathIds : []),
      ...(Array.isArray(mapped.pathIds) ? mapped.pathIds : []),
    ].filter(nonEmptyStr).map((x) => x.trim());
    if (!testIds.some((tid) => passingTests.has(tid)) && !pathIds.some((pid) => provedPaths.has(pid))) unprovedAcIds.push(id);
  }
  return {
    ok: unprovedAcIds.length === 0, unprovedAcIds,
    holdReason: unprovedAcIds.length ? 'insufficient_scope' : null,
    details: unprovedAcIds.length ? `Frozen AC(s) lack verified passing test ID or proved user path (prose excluded): ${unprovedAcIds.join(', ')}` : `All ${frozenAcs.length} frozen AC(s) verified by harness results.`,
  };
}

/** Check 3: Zero unapproved missing/skipped/unknown test IDs AND base-owned edited-test oracle clean. */
export function checkTestOracle({ testResults = [], expectedTestIds = [], approvedSkippedIds = [], baseOracle = null } = {}) {
  const approved = new Set((Array.isArray(approvedSkippedIds) ? approvedSkippedIds : []).filter(nonEmptyStr).map((x) => x.trim()));
  const seenIds = new Set(), badTestIds = [];
  for (const t of Array.isArray(testResults) ? testResults : []) {
    if (!isPlainObj(t) || !nonEmptyStr(t.id)) return { ok: false, badTestIds: [], unlistedOracleFailures: [], oracleUnknowns: [], holdReason: 'malformed_output', details: 'Malformed test result entry.' };
    const id = t.id.trim(); seenIds.add(id);
    if (t.status === 'pass') continue;
    if ((t.status === 'skip' || t.status === 'skipped' || t.status === 'missing') && approved.has(id)) continue;
    badTestIds.push(`${id}:${String(t.status ?? 'unknown')}`);
  }
  for (const exp of Array.isArray(expectedTestIds) ? expectedTestIds : []) {
    if (nonEmptyStr(exp) && !seenIds.has(exp.trim()) && !approved.has(exp.trim())) badTestIds.push(`${exp.trim()}:missing`);
  }

  const unlistedOracleFailures = [], oracleUnknowns = [];
  let sawServiceFailure = false;
  if (baseOracle !== null && baseOracle !== undefined) {
    if (!isPlainObj(baseOracle)) return { ok: false, badTestIds, unlistedOracleFailures, oracleUnknowns, holdReason: 'malformed_output', details: 'Malformed baseOracle object.' };
    if (baseOracle.status === 'service_failure') sawServiceFailure = true;
    else if (baseOracle.status === 'unknown' || baseOracle.status === 'error') oracleUnknowns.push(`oracle:${baseOracle.status}`);
    const expectedFails = new Set((Array.isArray(baseOracle.expectedFailIds) ? baseOracle.expectedFailIds : []).filter(nonEmptyStr).map((x) => x.trim()));
    for (const r of Array.isArray(baseOracle.results) ? baseOracle.results : []) {
      if (!isPlainObj(r) || !nonEmptyStr(r.id)) { oracleUnknowns.push('oracle:malformed-row'); continue; }
      const id = r.id.trim();
      if (r.status === 'fail' && !expectedFails.has(id)) unlistedOracleFailures.push(id);
      else if (r.status === 'unknown' || r.status === 'missing' || r.status === 'error') oracleUnknowns.push(`${id}:${r.status}`);
    }
    for (const id of Array.isArray(baseOracle.unlistedFailures) ? baseOracle.unlistedFailures : []) if (nonEmptyStr(id)) unlistedOracleFailures.push(id.trim());
    for (const id of Array.isArray(baseOracle.unknowns) ? baseOracle.unknowns : []) if (nonEmptyStr(id)) oracleUnknowns.push(id.trim());
  }

  const ok = !sawServiceFailure && !badTestIds.length && !unlistedOracleFailures.length && !oracleUnknowns.length;
  return {
    ok, badTestIds: [...new Set(badTestIds)].sort(),
    unlistedOracleFailures: [...new Set(unlistedOracleFailures)].sort(),
    oracleUnknowns: [...new Set(oracleUnknowns)].sort(),
    holdReason: ok ? null : (sawServiceFailure ? 'service_failure' : 'insufficient_scope'),
    details: ok ? 'Zero unapproved skipped/missing/unknown tests and base-owned edited-test oracle is clean.' : `Test oracle violation(s): bad=${badTestIds.length}, unlistedOracleFailures=${unlistedOracleFailures.length}, oracleUnknowns=${oracleUnknowns.length}.`,
  };
}

/** Build prompt-injection-safe gap-check input (ZERO PR title, PR body, comments, or commit prose). */
export function buildGapCheckInput({ diffStat = '', changedFiles = [], frozenAcs = [], touchedPaths = [], provedPathIds = [], testSummary = {} } = {}) {
  return {
    diffStat: String(diffStat ?? '').slice(0, 8000),
    changedFiles: (Array.isArray(changedFiles) ? changedFiles : []).map(normPath).filter(Boolean).sort(),
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

/** Evaluate the full 4-Check Non-Compensatory Mechanical Evidence Contract + optional cross-family gap check. */
export function evaluateEvidenceContract({
  changedFiles = [], humanApprovedPaths = [], protectedPatterns = [], frozenAcs = [], acMapping = {}, requireFrozenAcs = true,
  touchedPaths = [], receipts = [], expectedBinding = null, availableCapabilities = null, requiredCapabilitiesByPath = {},
  testResults = [], expectedTestIds = [], approvedSkippedIds = [], baseOracle = null,
  gapCheck = null, serviceFailure = null, abstained = false,
} = {}) {
  const protectedPaths = checkProtectedPaths({ changedFiles, humanApprovedPaths, protectedPatterns });
  const pathReceipts = checkPathReceipts({ touchedPaths, receipts, expectedBinding, availableCapabilities, requiredCapabilitiesByPath });
  const acCoverage = checkAcCoverage({ frozenAcs, testResults, provedPathIds: pathReceipts.provedPathIds, acMapping, requireFrozenAcs });
  const testOracle = checkTestOracle({ testResults, expectedTestIds, approvedSkippedIds, baseOracle });

  let gapResult = { ok: true, skipped: true, holdReason: null, missingPathIds: [], unprovedAcIds: [], flags: [], details: 'Gap check not provided.' };
  if (serviceFailure) gapResult = { ok: false, skipped: false, holdReason: 'service_failure', missingPathIds: [], unprovedAcIds: [], flags: [], details: String(serviceFailure) };
  else if (abstained === true) gapResult = { ok: false, skipped: false, holdReason: 'abstention', missingPathIds: [], unprovedAcIds: [], flags: [], details: 'Cross-family gap checker abstained.' };
  else if (gapCheck !== null && gapCheck !== undefined) gapResult = { ...validateGapCheckOutput(gapCheck), skipped: false };

  const reasons = [];
  if (serviceFailure || pathReceipts.holdReason === 'service_failure' || testOracle.holdReason === 'service_failure') reasons.push('service_failure');
  for (const c of [protectedPaths, pathReceipts, acCoverage, testOracle, gapResult]) {
    if (!c.ok && c.holdReason && !reasons.includes(c.holdReason)) reasons.push(c.holdReason);
  }

  const holdReason = HOLD_PRIORITY.find((r) => reasons.includes(r)) ?? null;
  const ok = holdReason === null && protectedPaths.ok && pathReceipts.ok && acCoverage.ok && testOracle.ok && gapResult.ok;
  return {
    decision: ok ? 'MERGE' : 'HOLD',
    ok,
    holdReason,
    holdReasons: reasons,
    burnRepairStrike: !ok && holdReason !== 'service_failure',
    checks: { acCoverage, pathReceipts, testOracle, protectedPaths, gapCheck: gapResult },
    summary: ok
      ? 'All 4 non-compensatory mechanical evidence checks and gap check passed.'
      : `HOLD (${holdReason}): ${[protectedPaths, pathReceipts, acCoverage, testOracle, gapResult].filter((c) => !c.ok).map((c) => c.details).join(' | ')}`,
  };
}
