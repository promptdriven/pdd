// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: 691dd6196bed4cd3f73c6e54357b81dbbd926f01249066f198c14749055ad53b).
import {
  ADVERSARIAL_BOUNDARY_SURFACES,
  ADVERSARIAL_SURFACE_CHECKLISTS,
  MIN_REALISTIC_PAYLOAD_BYTES,
  REAL_E2E_KINDS,
  REAL_HOST_CLASS_LABELS,
  REAL_HOST_CLASS_SET,
  classifyNativeOnlySurfaces,
  cleanText,
  cleanTool,
  detectChangedSurfaces,
  detectNativeOnlyModules,
  normalizePath,
} from './surfaces.mjs';

export const MAX_VALIDATION_REPAIRS = 3;

const HUMAN_INTERACTION_RE = /\b(?:browser\s+oauth|oauth\s+click|2fa|mfa|captcha|live\s+payment|physical\s+hardware)\b/i;
const emptyProof = () => ({ surfaces: [], commands: [], exitCodes: [] });

const BUCKET2_DIAGNOSTIC_RULES = [
  {
    patterns: ['reauthentication required', 'gcloud auth login', 'invalid_grant', 'do not currently have an active account'],
    resolve: () => ({ cooldownTool: 'gcloud', checkCommand: "gcloud auth list --filter=status:ACTIVE --format='value(account)'" }),
  },
  {
    patterns: ['token has expired', 'expiredtoken', 'unable to locate credentials', 'sso session', 'aws sso login'],
    resolve: () => ({ cooldownTool: 'aws', checkCommand: 'aws sts get-caller-identity' }),
  },
  {
    patterns: ['cannot connect to the docker daemon', 'docker daemon is not running', 'is the docker daemon running'],
    resolve: () => ({ cooldownTool: 'docker', checkCommand: 'docker info' }),
  },
  {
    patterns: ['401 unauthorized', 'invalid api key', 'expired api key', 'missing env', 'secret not set', 'credentials not configured'],
    resolve: ({ joinedLower, toolHint, verifyCommand }) => ({
      cooldownTool: cleanTool(toolHint) || (joinedLower.includes('stripe') ? 'stripe' : 'auth'),
      checkCommand: cleanText(verifyCommand) || 'env | grep -i token',
    }),
  },
  {
    patterns: ['connection refused', 'econnrefused'],
    resolve: ({ joinedLower, toolHint, verifyCommand }) => {
      const tool = cleanTool(toolHint) || (joinedLower.includes('postgres') || joinedLower.includes('5432') ? 'postgres' : 'service');
      return { cooldownTool: tool, checkCommand: cleanText(verifyCommand) || (tool === 'postgres' ? 'pg_isready' : 'curl -sf http://127.0.0.1') };
    },
  },
  {
    patterns: ['real-binding-unavailable'],
    resolve: ({ toolHint, verifyCommand }) => ({
      cooldownTool: cleanTool(toolHint) || 'runtime-binding',
      checkCommand: cleanText(verifyCommand) || 'pdd test --files',
    }),
  },
];

const makeOutcome = (overrides) => ({
  bucket: 1,
  decision: 'needs-person',
  waitKind: 'none',
  eligible: false,
  freeSlot: false,
  keepPr: true,
  repairRoundsToSpend: 0,
  repairAttemptsNext: 0,
  cooldownTool: null,
  resumeMode: 'none',
  checkCommand: null,
  message: '',
  proof: emptyProof(),
  humanVerificationCard: [],
  ...overrides,
});

/**
 * Format the exact 3-line Human Verification Card for Bucket 3 stops.
 */
export function formatHumanVerificationCard({ offlineSummary, unverifiedBoundary, verifyCommand } = {}) {
  return [
    `Passed offline: ${cleanText(offlineSummary) || 'none'}`,
    `Unverified boundary: ${cleanText(unverifiedBoundary) || 'runtime boundary'}`,
    `Verify command: ${cleanText(verifyCommand) || 'npm test'}`,
  ];
}

/**
 * Open-key machine capability check (zero hardcoded capability names).
 */
export function checkCapabilityRequirements({ requiredCapabilities = [], availableCapabilities = [] } = {}) {
  const required = [...new Set((Array.isArray(requiredCapabilities) ? requiredCapabilities : []).map(cleanText).filter(Boolean))].sort();
  const available = new Set((Array.isArray(availableCapabilities) ? availableCapabilities : []).map(cleanText).filter(Boolean));
  const missing = required.filter((cap) => !available.has(cap));
  return { ok: missing.length === 0, required, missing };
}

function detectBucket2Blocker({ realBindingUnavailable, diagnostics, toolHint, verifyCommand }) {
  const joinedLower = diagnostics.join('\n').toLowerCase();
  for (const rule of BUCKET2_DIAGNOSTIC_RULES) {
    if (rule.patterns.some((p) => joinedLower.includes(p))) return rule.resolve({ joinedLower, toolHint, verifyCommand });
  }
  if (realBindingUnavailable === true) {
    return { cooldownTool: cleanTool(toolHint) || 'runtime-binding', checkCommand: cleanText(verifyCommand) || 'pdd test --files' };
  }
  return null;
}

function isRealHostBoundaryCheck(check, { hasOsBoundary = false } = {}) {
  if (!check || typeof check !== 'object' || check.executed !== true || check.mockOnly === true) return false;
  if (!REAL_E2E_KINDS.has(check.kind)) return false;
  if (check.strictKind === true) return check.kind === 'real-host-smoke';
  const isLiveLocal = check.liveLocal === true || /--live-local\b/i.test(cleanText(check.command));
  if (hasOsBoundary) return check.kind === 'real-host-smoke' || check.kind === 'subprocess-cli' || isLiveLocal;
  return check.kind === 'real-execution' ? isLiveLocal : true;
}

const isPassingRealE2eCheck = (c) => Boolean(
  c && typeof c === 'object' && c.executed === true && c.mockOnly !== true && REAL_E2E_KINDS.has(c.kind)
  && Number.isInteger(c.exitCode) && c.exitCode === 0
  && Number.isInteger(c.passed) && c.passed > 0
  && Number.isInteger(c.failed) && c.failed === 0
  && Number.isInteger(c.skipped) && c.skipped === 0,
);

const hasSubprocessRealHostEvidence = (c) => Boolean(
  c && typeof c === 'object' && c.kind === 'real-host-smoke' && (
    (Number.isInteger(c.turns) && c.turns >= 1)
    || c.liveLocal === true || /--live-local\b/i.test(cleanText(c.command))
    || (Array.isArray(c.realHostClasses) && c.realHostClasses.some((x) => x === 'nested-sandbox' || x === 'multi-turn-cli-state'))
  ),
);

function coversRequiredProofKinds(requiredProofKinds, passingChecks, { hasOsBoundary = false } = {}) {
  const passedKinds = new Set(passingChecks.map((c) => c.kind));
  const hasRealHost = passingChecks.some((c) => isRealHostBoundaryCheck(c, { hasOsBoundary }));
  const hasSubRealHost = passingChecks.some((c) => c.strictKind !== true && hasSubprocessRealHostEvidence(c));
  return requiredProofKinds.every((req) => (
    passedKinds.has(req)
    || (req === 'real-host-smoke' && hasRealHost)
    || (req === 'subprocess-cli' && hasSubRealHost)
    || (req === 'real-execution' && passedKinds.size > 0)
  ));
}

function findMissingRealHostClasses({ requiredClasses, executedRealHostChecks }) {
  return requiredClasses.filter((cls) => !executedRealHostChecks.some((c) => {
    const checkClasses = Array.isArray(c.realHostClasses) ? c.realHostClasses : null;
    if (cls === 'multi-turn-cli-state') {
      if (Number.isInteger(c.turns) && c.turns < 2) return false;
      return checkClasses ? checkClasses.includes(cls) : (Number.isInteger(c.turns) && c.turns >= 2);
    }
    if (cls === 'full-size-payload') {
      if (Number.isFinite(c.payloadBytes) && c.payloadBytes <= MIN_REALISTIC_PAYLOAD_BYTES) return false;
      return checkClasses ? checkClasses.includes(cls) : (Number.isFinite(c.payloadBytes) && c.payloadBytes > MIN_REALISTIC_PAYLOAD_BYTES);
    }
    return checkClasses !== null && checkClasses.includes(cls);
  }));
}

function evidencedRealHostClasses(executedRealHostChecks) {
  const classes = new Set();
  for (const c of executedRealHostChecks) {
    if (!isPassingRealE2eCheck(c)) continue;
    for (const cls of Array.isArray(c.realHostClasses) ? c.realHostClasses : []) {
      if (cls === 'multi-turn-cli-state' && Number.isInteger(c.turns) && c.turns < 2) continue;
      if (cls === 'full-size-payload' && Number.isFinite(c.payloadBytes) && c.payloadBytes <= MIN_REALISTIC_PAYLOAD_BYTES) continue;
      if (typeof cls === 'string' && cls.trim()) classes.add(cls.trim());
    }
    if (Number.isInteger(c.turns) && c.turns >= 2) classes.add('multi-turn-cli-state');
    if (Number.isFinite(c.payloadBytes) && c.payloadBytes > MIN_REALISTIC_PAYLOAD_BYTES) classes.add('full-size-payload');
  }
  return [...classes].sort();
}

function describeRealHostGap({ nativeOnlyFiles, runtimeSurfaces, missingClasses, missingAdvSurfaces = [], happyPathOnlyDetected = false, mockOnlyDetected }) {
  const parts = [];
  if (nativeOnlyFiles.length) parts.push(`native-only module(s): ${nativeOnlyFiles.join(', ')}`);
  const nonNative = runtimeSurfaces.filter((s) => s !== 'native-only');
  if (nonNative.length) parts.push(`surface(s): ${nonNative.join(', ')}`);
  if (missingClasses.length) parts.push(`unexercised real-host class(es): ${missingClasses.map((c) => REAL_HOST_CLASS_LABELS[c] || c).join('; ')}`);
  if (missingAdvSurfaces.length) parts.push(`missing adversarial boundary surface(s): ${missingAdvSurfaces.map((s) => `${s} (${ADVERSARIAL_SURFACE_CHECKLISTS[s] || s})`).join('; ')}`);
  if (happyPathOnlyDetected) parts.push('only happy-path real-host smoke detected (zero adversarial negative/rejection probes)');
  if (mockOnlyDetected) parts.push('only mocked/stubbed or in-process unit checks detected');
  return parts.join('; ') || 'native-only / OS boundary real-host smoke';
}

const bucket1Failure = ({ repairAttempts, message }) => (repairAttempts < MAX_VALIDATION_REPAIRS
  ? makeOutcome({ bucket: 1, decision: 'repair', repairRoundsToSpend: 1, repairAttemptsNext: repairAttempts + 1, message })
  : makeOutcome({ bucket: 1, decision: 'needs-person', waitKind: 'repair-exhausted', freeSlot: true, repairAttemptsNext: repairAttempts, message: `Validation failed after ${MAX_VALIDATION_REPAIRS} repair attempts; human review required.` }));

const bucket3Stop = ({ waitKind, repairAttempts, offlineSummary, unverifiedBoundary, verifyCommand, message }) => makeOutcome({
  bucket: 3, decision: 'needs-person', waitKind, freeSlot: true, repairAttemptsNext: repairAttempts, message,
  humanVerificationCard: formatHumanVerificationCard({ offlineSummary, unverifiedBoundary, verifyCommand }),
});

/**
 * Evaluate candidate validation evidence across Buckets 1, 2, and 3 (fail-closed in auto and observe modes).
 */
export function evaluateValidationOutcome({
  mode = 'auto', changedFiles = [], nativeOnlyFiles = [], promptFiles = null, bindings = null, fileHeads = null,
  realHostClasses = [], requiredAdversarialSurfaces = [], requiredCapabilities = [], availableCapabilities = [], isBugFix = false,
  offlinePassed = false, offlineSummary = '', e2eChecks = [], bugFixBaseControl = 'not-applicable',
  diagnostics = [], realBindingUnavailable = false, needsHumanInteraction = false, humanBoundaryDetail = '',
  verifyCommand = '', toolHint = '', lintBlockingCodes = [], repairAttempts = 0,
} = {}) {
  const attempts = Number.isInteger(repairAttempts) && repairAttempts >= 0 ? repairAttempts : 0;
  const diagLines = Array.isArray(diagnostics) ? diagnostics.map((d) => String(d ?? '')) : [];
  const lintErrors = Array.isArray(lintBlockingCodes) ? lintBlockingCodes.map(cleanText).filter(Boolean) : [];
  const normalizedFiles = Array.isArray(changedFiles) ? changedFiles.map(normalizePath).filter(Boolean) : [];
  const detectedNative = (promptFiles || bindings || fileHeads)
    ? detectNativeOnlyModules({ changedFiles: normalizedFiles, promptFiles, bindings, fileHeads })
    : { nativeOnlyModules: [], matches: [] };
  const resolvedNative = [...new Set([
    ...(Array.isArray(nativeOnlyFiles) ? nativeOnlyFiles.map(normalizePath).filter(Boolean) : []),
    ...detectedNative.nativeOnlyModules,
  ])].sort();
  const explicitAdvSurfaces = Array.isArray(requiredAdversarialSurfaces) ? [...new Set(requiredAdversarialSurfaces.map(cleanTool).filter(Boolean))].sort() : [];
  const promptTextByPath = new Map((Array.isArray(promptFiles) ? promptFiles : []).filter((p) => p?.path && typeof p.content === 'string').map((p) => [normalizePath(p.path).toLowerCase(), p.content]));
  const headTextByPath = new Map((Array.isArray(fileHeads) ? fileHeads : []).filter((h) => h?.path && typeof h.content === 'string').map((h) => [normalizePath(h.path).toLowerCase(), h.content]));
  const concreteAdvSet = new Set(ADVERSARIAL_BOUNDARY_SURFACES);
  const inferredAdvSurfaces = resolvedNative.length ? [...new Set(resolvedNative.flatMap((mod) => { const m = (detectedNative.matches ?? []).find((x) => x.module === mod); const surfs = classifyNativeOnlySurfaces({ modulePath: mod, promptText: m ? (promptTextByPath.get(normalizePath(m.prompt).toLowerCase()) ?? '') : '', moduleSource: headTextByPath.get(mod.toLowerCase()) ?? '' }); return (promptFiles || fileHeads) ? surfs : surfs.filter((s) => concreteAdvSet.has(s)); }))].sort() : [];
  const requiredAdvSurfaces = [...new Set([...explicitAdvSurfaces, ...inferredAdvSurfaces])].sort();
  const explicitClasses = Array.isArray(realHostClasses)
    ? [...new Set(realHostClasses.map(cleanTool).filter((c) => REAL_HOST_CLASS_SET.has(c)))].sort()
    : [];
  const surfaceInfo = detectChangedSurfaces({ changedFiles: normalizedFiles, nativeOnlyFiles: resolvedNative });
  const requiredClasses = [...new Set([...explicitClasses, ...surfaceInfo.realHostBoundaryClasses])].sort();
  const needsRealHostSmoke = surfaceInfo.requiredProofKinds.includes('real-host-smoke') || explicitClasses.length > 0 || requiredAdvSurfaces.length > 0;
  const humanBlocker = needsHumanInteraction === true || diagLines.some((d) => HUMAN_INTERACTION_RE.test(d));
  const bucket2 = detectBucket2Blocker({ realBindingUnavailable, diagnostics: diagLines, toolHint, verifyCommand });
  const capCheck = checkCapabilityRequirements({ requiredCapabilities, availableCapabilities });
  const allowDecision = mode === 'observe' ? 'allow-would-merge' : 'allow-merge';

  if (surfaceInfo.docsOnly && !needsRealHostSmoke && !humanBlocker && !bucket2 && capCheck.ok) {
    return (offlinePassed === true && lintErrors.length === 0)
      ? makeOutcome({ bucket: 1, decision: allowDecision, eligible: true, keepPr: false, repairAttemptsNext: attempts, message: 'Documentation-only change passed offline checks.' })
      : bucket1Failure({ repairAttempts: attempts, message: 'Documentation-only change failed offline or lint checks.' });
  }
  if (humanBlocker) {
    return bucket3Stop({
      waitKind: 'human-boundary', repairAttempts: attempts, offlineSummary, verifyCommand,
      unverifiedBoundary: cleanText(humanBoundaryDetail) || surfaceInfo.runtimeSurfaces.join(', ') || 'human interaction boundary',
      message: 'Human interaction is required to verify this boundary before merge.',
    });
  }
  if (bucket2) {
    return makeOutcome({
      bucket: 2, decision: 'park-auth-wait', waitKind: 'auth-environment', freeSlot: true, repairAttemptsNext: attempts,
      cooldownTool: bucket2.cooldownTool, resumeMode: 'validate-only-same-head', checkCommand: bucket2.checkCommand,
      message: `Environment/auth wait on ${bucket2.cooldownTool}; refresh login or service and verify with: ${bucket2.checkCommand}`,
    });
  }

  const defaultVerifyCmd = cleanText(verifyCommand) || (needsRealHostSmoke ? 'npm run test:smoke -- --live-local' : 'npm run test:e2e');
  if (!capCheck.ok) {
    return bucket3Stop({
      waitKind: 'missing-capability', repairAttempts: attempts, offlineSummary, verifyCommand: defaultVerifyCmd,
      unverifiedBoundary: cleanText(humanBoundaryDetail) || `missing host capability: ${capCheck.missing.join(', ')}`,
      message: `Required machine capability missing (${capCheck.missing.join(', ')}); cannot prove boundary on this host.`,
    });
  }
  if (normalizedFiles.length === 0) {
    return bucket3Stop({
      waitKind: 'missing-e2e', repairAttempts: attempts, offlineSummary, verifyCommand: defaultVerifyCmd,
      unverifiedBoundary: cleanText(humanBoundaryDetail) || 'unknown changed files (diff unavailable)',
      message: 'Changed files list is empty or unavailable; cannot verify validation surfaces.',
    });
  }

  const checks = Array.isArray(e2eChecks) ? e2eChecks : [];
  const hasOsBoundary = surfaceInfo.runtimeSurfaces.includes('os-boundary');
  const executedRealChecks = checks.filter((c) => c && typeof c === 'object' && c.executed === true && c.mockOnly !== true && REAL_E2E_KINDS.has(c.kind));
  const executedRealHostChecks = checks.filter((c) => isRealHostBoundaryCheck(c, { hasOsBoundary }));
  const executedClassChecks = checks.filter((c) => (
    isRealHostBoundaryCheck(c, { hasOsBoundary })
    || (c && typeof c === 'object' && c.strictKind === true && c.executed === true && c.mockOnly !== true && c.kind === 'subprocess-cli')
  ));
  const hasExecutedFailure = checks.some((c) => (
    c && typeof c === 'object' && c.executed === true
    && ((Number.isInteger(c.exitCode) && c.exitCode !== 0) || (Number.isInteger(c.failed) && c.failed > 0))
  ));
  const mockOnlyDetected = lintErrors.includes('boundary-mock-only-test')
    || checks.some((c) => c && typeof c === 'object' && (c.kind === 'unit-mock' || c.mockOnly === true))
    || (executedRealChecks.length > 0 && executedRealHostChecks.length === 0 && !executedRealChecks.some((c) => c.strictKind === true));

  if (offlinePassed === false && hasExecutedFailure) {
    return bucket1Failure({ repairAttempts: attempts, message: 'Executed validation or offline suite failed; repair before retrying real-host verification.' });
  }
  if (needsRealHostSmoke && executedRealHostChecks.length === 0) {
    const gap = describeRealHostGap({ nativeOnlyFiles: surfaceInfo.nativeOnlyFiles, runtimeSurfaces: surfaceInfo.runtimeSurfaces, missingClasses: requiredClasses, mockOnlyDetected });
    return bucket3Stop({
      waitKind: 'needs-real-host-smoke', repairAttempts: attempts, offlineSummary, verifyCommand: defaultVerifyCmd,
      unverifiedBoundary: cleanText(humanBoundaryDetail) || gap,
      message: `Real-host non-mocked smoke verification is required before merge (${gap}).`,
    });
  }
  if (needsRealHostSmoke && !executedClassChecks.some((c) => !isPassingRealE2eCheck(c))) {
    const missingClasses = findMissingRealHostClasses({ requiredClasses, executedRealHostChecks: executedClassChecks });
    if (missingClasses.length > 0) {
      const gap = describeRealHostGap({ nativeOnlyFiles: surfaceInfo.nativeOnlyFiles, runtimeSurfaces: surfaceInfo.runtimeSurfaces, missingClasses, mockOnlyDetected });
      return bucket3Stop({
        waitKind: 'needs-real-host-smoke', repairAttempts: attempts, offlineSummary, verifyCommand: defaultVerifyCmd,
        unverifiedBoundary: cleanText(humanBoundaryDetail) || gap,
        message: `Real-host boundary verification missed required host failure class(es) (${gap}).`,
      });
    }
    const evidencedAdvSurfaces = [...new Set(executedClassChecks.flatMap((c) => [...(Array.isArray(c.adversarialSurfaces) ? c.adversarialSurfaces : []), ...(Array.isArray(c.realHostClasses) && c.realHostClasses.includes('multi-turn-cli-state') && (!Number.isInteger(c.turns) || c.turns >= 2) ? ['cli-day0'] : [])]))].sort();
    const evidencedAdvProbes = [...new Set(executedClassChecks.flatMap((c) => (Array.isArray(c.adversarialProbes) ? c.adversarialProbes : [])))].sort();
    const missingAdvSurfaces = requiredAdvSurfaces.filter((s) => !evidencedAdvSurfaces.includes(s));
    const happyPathOnlyNative = surfaceInfo.nativeOnlyFiles.length > 0 && executedClassChecks.some((c) => c.happyPathOnly === true || Array.isArray(c.adversarialProbes) || Array.isArray(c.adversarialSurfaces)) && evidencedAdvProbes.length === 0;
    const advChecks = executedClassChecks.filter((c) => (Array.isArray(c.adversarialProbes) && c.adversarialProbes.length > 0) || (Array.isArray(c.adversarialSurfaces) && c.adversarialSurfaces.length > 0));
    const explicitCoveredMods = new Set(advChecks.flatMap((c) => (Array.isArray(c.coveredModules) ? c.coveredModules.map(normalizePath) : [])));
    const uncoveredNativeMods = surfaceInfo.nativeOnlyFiles.length >= 2 && (explicitCoveredMods.size ? surfaceInfo.nativeOnlyFiles.filter((m) => !explicitCoveredMods.has(m)) : (advChecks.length < surfaceInfo.nativeOnlyFiles.length && !advChecks.some((c) => c.coversAllNativeModules === true) ? surfaceInfo.nativeOnlyFiles : []));
    if (missingAdvSurfaces.length || happyPathOnlyNative || uncoveredNativeMods.length) {
      const gap = describeRealHostGap({ nativeOnlyFiles: uncoveredNativeMods.length ? uncoveredNativeMods : surfaceInfo.nativeOnlyFiles, runtimeSurfaces: surfaceInfo.runtimeSurfaces, missingClasses: [], missingAdvSurfaces, happyPathOnlyDetected: happyPathOnlyNative, mockOnlyDetected });
      return bucket3Stop({ waitKind: 'needs-real-host-smoke', repairAttempts: attempts, offlineSummary, verifyCommand: defaultVerifyCmd, unverifiedBoundary: cleanText(humanBoundaryDetail) || gap, message: `Adversarial real-host boundary verification required for native-only boundary (${gap}).` });
    }
  }
  if (surfaceInfo.requiresRealE2e && executedRealChecks.length === 0) {
    return bucket3Stop({
      waitKind: 'missing-e2e', repairAttempts: attempts, offlineSummary, verifyCommand: defaultVerifyCmd,
      unverifiedBoundary: cleanText(humanBoundaryDetail) || surfaceInfo.runtimeSurfaces.join(', '),
      message: 'No runnable real end-to-end check executed for the changed runtime surfaces.',
    });
  }
  if (isBugFix === true && (bugFixBaseControl === 'not-run' || bugFixBaseControl === 'not-applicable')) {
    return bucket3Stop({
      waitKind: 'missing-e2e', repairAttempts: attempts, offlineSummary, verifyCommand: defaultVerifyCmd,
      unverifiedBoundary: cleanText(humanBoundaryDetail) || 'bug-fix base regression control',
      message: 'Bug-fix base regression control did not run.',
    });
  }

  const allRealPassed = executedRealChecks.every(isPassingRealE2eCheck);
  const coveredSurfaces = coversRequiredProofKinds(surfaceInfo.requiredProofKinds, executedRealChecks.filter(isPassingRealE2eCheck), { hasOsBoundary });
  const bugFixControlOk = isBugFix !== true || bugFixBaseControl === 'ran-and-failed-on-base';

  if (offlinePassed === true && lintErrors.length === 0 && allRealPassed && coveredSurfaces && bugFixControlOk) {
    const advSurfaces = [...new Set(executedClassChecks.flatMap((c) => (Array.isArray(c.adversarialSurfaces) ? c.adversarialSurfaces : [])))].sort();
    const advProbes = [...new Set(executedClassChecks.flatMap((c) => (Array.isArray(c.adversarialProbes) ? c.adversarialProbes : [])))].sort();
    return makeOutcome({
      bucket: 1, decision: allowDecision, eligible: true, keepPr: false, repairAttemptsNext: attempts,
      message: 'All offline, lint, and real end-to-end checks passed 100%.',
      proof: {
        surfaces: [...surfaceInfo.runtimeSurfaces],
        commands: executedRealChecks.map((c) => cleanText(c.command)),
        exitCodes: executedRealChecks.map((c) => c.exitCode),
        ...(needsRealHostSmoke ? { realHostClasses: evidencedRealHostClasses(executedClassChecks) } : {}),
        ...(surfaceInfo.nativeOnlyFiles.length > 0 || requiredAdvSurfaces.length > 0
          ? { evidenceSplit: { simulated_vectors: { executesNativeOnlyBoundaries: false }, adversarial_real_host: { surfaces: advSurfaces, probes: advProbes } } }
          : {}),
      },
    });
  }

  return bucket1Failure({
    repairAttempts: attempts,
    message: !bugFixControlOk ? 'Bug-fix regression check passed on base; repair test or fix.'
      : lintErrors.length > 0 ? `Blocking validation lint findings: ${lintErrors.join(', ')}.`
        : !coveredSurfaces ? `Missing required real end-to-end proof kinds: ${surfaceInfo.requiredProofKinds.join(', ')}.`
          : 'Real end-to-end or offline validation check failed.',
  });
}

export function shouldClaimWithCooldowns({ issueRequiredTools = [], toolCooldowns = {} } = {}) {
  const active = new Set();
  if (toolCooldowns && typeof toolCooldowns === 'object') {
    for (const [k, entry] of Object.entries(toolCooldowns)) {
      const norm = cleanTool(k);
      if (norm && entry?.active === true) active.add(norm);
    }
  }
  for (const rawTool of Array.isArray(issueRequiredTools) ? issueRequiredTools : []) {
    const tool = cleanTool(rawTool);
    if (tool && active.has(tool)) return { claimable: false, blockedByTool: tool, reason: 'tool-cooldown' };
  }
  return { claimable: true, blockedByTool: null, reason: null };
}

export function planValidationResume({ pr, headSha, currentPrHeadSha, cooldownTool, preflightExitCode, userResumed = false } = {}) {
  const targetTool = cleanTool(cooldownTool) || null;
  if (cleanText(currentPrHeadSha) !== cleanText(headSha)) {
    return { action: 'head-changed-abort', pr, headSha, rebuildCode: false, runValidationOnly: false, clearCooldown: false, targetTool };
  }
  if (preflightExitCode === 0 || userResumed === true) {
    return { action: 'resume-validate-only', pr, headSha, rebuildCode: false, runValidationOnly: true, clearCooldown: true, targetTool };
  }
  return { action: 'stay-parked', pr, headSha, rebuildCode: false, runValidationOnly: false, clearCooldown: false, targetTool };
}
