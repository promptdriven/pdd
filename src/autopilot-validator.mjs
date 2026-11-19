// Generated from prompts/cli/autopilot-validator.prompt.md

export const MAX_VALIDATION_REPAIRS = 3;

const REAL_E2E_KINDS = new Set([
  'subprocess-cli',
  'local-server-or-db',
  'browser-playwright',
  'live-binding',
  'real-execution',
]);

const RUNTIME_CODE_EXT_RE = /\.(?:js|mjs|cjs|ts|mts|cts|py|go|rs|rb|java|kt|cs|php|swift|c|cpp)$/i;
const NON_PRODUCTION_DIR_RE = /^(?:test|tests|__tests__|spec|fixtures|examples|prompts|user_stories|docs)\//i;
const DOC_FILE_RE = /(?:^docs\/|\.(?:txt|rst)$|(?:^|\/)(?:license|changelog)[^/]*$)/i;
const HUMAN_INTERACTION_RE = /\b(?:browser\s+oauth|oauth\s+click|2fa|mfa|captcha|live\s+payment|physical\s+hardware)\b/i;

const SURFACE_MATCHERS = [
  {
    surface: 'cli',
    test: (norm, base) => /^(?:bin|cli|cmd|scripts)\//i.test(norm) || /\.sh$/i.test(norm) || base.includes('cli'),
  },
  {
    surface: 'api-server',
    test: (norm, base) => /^(?:api|server|routes|handlers|controllers)\//i.test(norm)
      || /(?:server|router|api|http|websocket|graphql|grpc|\bws\b|[-_.]ws[-_.])/i.test(base),
  },
  {
    surface: 'database',
    test: (norm, base) => /^(?:db|database|migrations|prisma|sql)\//i.test(norm)
      || /\.sql$/i.test(norm)
      || /(?:postgres|mysql|sqlite|mongo|redis|\bdb\b|[-_.]db[-_.])/i.test(base),
  },
  {
    surface: 'web-ui',
    test: (norm) => /^(?:web|ui|frontend|pages|components|views|app)\//i.test(norm)
      || /\.(?:jsx|tsx|vue|svelte|html|css)$/i.test(norm)
      || /\.ui\.svg$/i.test(norm),
  },
  {
    surface: 'external-tool',
    test: (norm, base) => base === 'dockerfile'
      || base.startsWith('docker-compose')
      || /(?:gcloud|gcp|aws|azure|stripe|docker|kubernetes|k8s|oauth|auth|webhook|terraform)/i.test(norm),
  },
];

const SURFACE_TO_PROOF_KIND = {
  cli: 'subprocess-cli',
  'api-server': 'local-server-or-db',
  database: 'local-server-or-db',
  'web-ui': 'browser-playwright',
  'external-tool': 'live-binding',
};

const BUCKET2_DIAGNOSTIC_RULES = [
  {
    patterns: ['reauthentication required', 'gcloud auth login', 'invalid_grant', 'do not currently have an active account'],
    resolve: () => ({
      cooldownTool: 'gcloud',
      checkCommand: "gcloud auth list --filter=status:ACTIVE --format='value(account)'",
    }),
  },
  {
    patterns: ['token has expired', 'expiredtoken', 'unable to locate credentials', 'sso session', 'aws sso login'],
    resolve: () => ({
      cooldownTool: 'aws',
      checkCommand: 'aws sts get-caller-identity',
    }),
  },
  {
    patterns: ['cannot connect to the docker daemon', 'docker daemon is not running', 'is the docker daemon running'],
    resolve: () => ({
      cooldownTool: 'docker',
      checkCommand: 'docker info',
    }),
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
      const tool = cleanTool(toolHint)
        || (joinedLower.includes('postgres') || joinedLower.includes('5432') ? 'postgres' : 'service');
      return {
        cooldownTool: tool,
        checkCommand: cleanText(verifyCommand) || (tool === 'postgres' ? 'pg_isready' : 'curl -sf http://127.0.0.1'),
      };
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

const MOCK_USAGE_RE = /\b(?:mock\.|vi\.mock|jest\.mock|sinon\.stub|fakeClient|fakeServer|fakeTransport)\b|stub(?:bed)?Handler/i;
const REAL_EXEC_RE = /\b(?:spawn|spawnSync|execFile|execFileSync|createServer|playwright)\b|listen\(|fetch\(|http\.request|chromium\.launch|page\.goto/i;
const BOUNDARY_IMPORT_RE = /(?:from|require\s*\()\s*['"`]([^'"`]+)['"`]/g;
const SILENT_SKIP_LINE_PATTERNS = [
  {
    re: /\blocalSkipRow\b|\bstoryLocalSkipOk\b|\blocalSkipOnly\b/i,
    detail: 'silent validation local-skip helper bypasses real validation',
  },
  {
    re: /not a defect or needs-person blocker/i,
    detail: 'rewrites real-binding-unavailable as a non-blocker',
  },
  {
    re: /real-binding-unavailable.*local\s*skip|local\s*skip.*real-binding-unavailable/i,
    detail: 'treats missing live binding as an excused skip',
  },
  {
    re: /\.filter\([^)]*!==\s*['"`]real-binding-unavailable['"`]/i,
    detail: 'filters real-binding-unavailable out of blocking refusals',
  },
  {
    re: /\b(?:test|it|t)\.skip\s*\([^)]*(?:e2e|validation|validator|real-binding)/i,
    detail: 'unconditionally skips an E2E or validation test',
  },
];

const cleanText = (value) => (typeof value === 'string' ? value.trim() : '');
const cleanTool = (value) => cleanText(value).toLowerCase();
const normalizePath = (value) => cleanText(value).replace(/\\/g, '/').replace(/^\.\//, '');
const emptyProof = () => ({ surfaces: [], commands: [], exitCodes: [] });

function isDocPath(norm) {
  if (/\.prompt\.md$/i.test(norm)) return false;
  return /\.md$/i.test(norm) || DOC_FILE_RE.test(norm);
}

function classifyFileSurfaces(rawPath) {
  const norm = normalizePath(rawPath);
  if (!norm) return [];
  const lower = norm.toLowerCase();
  if (isDocPath(lower)) return ['docs'];
  const base = lower.split('/').pop() || lower;
  const matched = [];
  for (const { surface, test } of SURFACE_MATCHERS) {
    if (test(lower, base)) matched.push(surface);
  }
  if (!matched.length && RUNTIME_CODE_EXT_RE.test(lower) && !NON_PRODUCTION_DIR_RE.test(lower)) {
    matched.push('runtime-code');
  }
  return matched;
}

/**
 * Classify changed repository paths into validation surfaces and required E2E proof kinds.
 */
export function detectChangedSurfaces({ changedFiles = [] } = {}) {
  const files = Array.isArray(changedFiles) ? changedFiles.map(normalizePath).filter(Boolean) : [];
  const surfaceSet = new Set();
  let allDocs = files.length > 0;

  for (const file of files) {
    const fileSurfaces = classifyFileSurfaces(file);
    if (!fileSurfaces.length || fileSurfaces.some((s) => s !== 'docs')) allDocs = false;
    for (const s of fileSurfaces) surfaceSet.add(s);
  }

  const surfaces = [...surfaceSet].sort();
  const runtimeSurfaces = surfaces.filter((s) => s !== 'docs');
  const docsOnly = allDocs && runtimeSurfaces.length === 0;
  const requiresRealE2e = runtimeSurfaces.length > 0;

  const proofKindSet = new Set();
  for (const surface of runtimeSurfaces) {
    if (SURFACE_TO_PROOF_KIND[surface]) proofKindSet.add(SURFACE_TO_PROOF_KIND[surface]);
  }
  if (!proofKindSet.size && runtimeSurfaces.includes('runtime-code')) {
    proofKindSet.add('real-execution');
  }

  return {
    surfaces,
    runtimeSurfaces,
    docsOnly,
    requiresRealE2e,
    requiredProofKinds: [...proofKindSet].sort(),
  };
}

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

function detectBucket2Blocker({ realBindingUnavailable, diagnostics, toolHint, verifyCommand }) {
  const joinedLower = diagnostics.join('\n').toLowerCase();
  for (const rule of BUCKET2_DIAGNOSTIC_RULES) {
    if (rule.patterns.some((p) => joinedLower.includes(p))) {
      return rule.resolve({ joinedLower, toolHint, verifyCommand });
    }
  }
  if (realBindingUnavailable === true) {
    return {
      cooldownTool: cleanTool(toolHint) || 'runtime-binding',
      checkCommand: cleanText(verifyCommand) || 'pdd test --files',
    };
  }
  return null;
}

function isPassingRealE2eCheck(check) {
  return Boolean(
    check
    && typeof check === 'object'
    && check.executed === true
    && REAL_E2E_KINDS.has(check.kind)
    && Number.isInteger(check.exitCode)
    && check.exitCode === 0
    && Number.isInteger(check.passed)
    && check.passed > 0
    && Number.isInteger(check.failed)
    && check.failed === 0
    && Number.isInteger(check.skipped)
    && check.skipped === 0,
  );
}

function coversRequiredProofKinds(requiredProofKinds, passingChecks) {
  const passedKinds = new Set(passingChecks.map((c) => c.kind));
  return requiredProofKinds.every((required) => (
    passedKinds.has(required)
    || (required === 'real-execution' && passedKinds.size > 0)
  ));
}

function bucket1FailureOutcome({ repairAttempts, message }) {
  if (repairAttempts < MAX_VALIDATION_REPAIRS) {
    return {
      bucket: 1,
      decision: 'repair',
      waitKind: 'none',
      eligible: false,
      freeSlot: false,
      keepPr: true,
      repairRoundsToSpend: 1,
      repairAttemptsNext: repairAttempts + 1,
      cooldownTool: null,
      resumeMode: 'none',
      checkCommand: null,
      message,
      proof: emptyProof(),
      humanVerificationCard: [],
    };
  }
  return {
    bucket: 1,
    decision: 'needs-person',
    waitKind: 'repair-exhausted',
    eligible: false,
    freeSlot: true,
    keepPr: true,
    repairRoundsToSpend: 0,
    repairAttemptsNext: repairAttempts,
    cooldownTool: null,
    resumeMode: 'none',
    checkCommand: null,
    message: `Validation failed after ${MAX_VALIDATION_REPAIRS} repair attempts; human review required.`,
    proof: emptyProof(),
    humanVerificationCard: [],
  };
}

function bucket3Outcome({ waitKind, repairAttempts, offlineSummary, unverifiedBoundary, verifyCommand, message }) {
  return {
    bucket: 3,
    decision: 'needs-person',
    waitKind,
    eligible: false,
    freeSlot: true,
    keepPr: true,
    repairRoundsToSpend: 0,
    repairAttemptsNext: repairAttempts,
    cooldownTool: null,
    resumeMode: 'none',
    checkCommand: null,
    message,
    proof: emptyProof(),
    humanVerificationCard: formatHumanVerificationCard({
      offlineSummary,
      unverifiedBoundary,
      verifyCommand,
    }),
  };
}

/**
 * Evaluate candidate validation evidence across Buckets 1, 2, and 3 (fail-closed in auto and observe modes).
 */
export function evaluateValidationOutcome({
  mode = 'auto',
  changedFiles = [],
  isBugFix = false,
  offlinePassed = false,
  offlineSummary = '',
  e2eChecks = [],
  bugFixBaseControl = 'not-applicable',
  diagnostics = [],
  realBindingUnavailable = false,
  needsHumanInteraction = false,
  humanBoundaryDetail = '',
  verifyCommand = '',
  toolHint = '',
  lintBlockingCodes = [],
  repairAttempts = 0,
} = {}) {
  const attempts = Number.isInteger(repairAttempts) && repairAttempts >= 0 ? repairAttempts : 0;
  const diagLines = Array.isArray(diagnostics) ? diagnostics.map((d) => String(d ?? '')) : [];
  const lintErrors = Array.isArray(lintBlockingCodes) ? lintBlockingCodes.map(cleanText).filter(Boolean) : [];
  const surfaceInfo = detectChangedSurfaces({ changedFiles });
  const humanBlocker = needsHumanInteraction === true || diagLines.some((d) => HUMAN_INTERACTION_RE.test(d));
  const bucket2 = detectBucket2Blocker({ realBindingUnavailable, diagnostics: diagLines, toolHint, verifyCommand });

  if (surfaceInfo.docsOnly && !humanBlocker && !bucket2) {
    if (offlinePassed === true && lintErrors.length === 0) {
      return {
        bucket: 1,
        decision: mode === 'observe' ? 'allow-would-merge' : 'allow-merge',
        waitKind: 'none',
        eligible: true,
        freeSlot: false,
        keepPr: false,
        repairRoundsToSpend: 0,
        repairAttemptsNext: attempts,
        cooldownTool: null,
        resumeMode: 'none',
        checkCommand: null,
        message: 'Documentation-only change passed offline checks.',
        proof: emptyProof(),
        humanVerificationCard: [],
      };
    }
    return bucket1FailureOutcome({
      repairAttempts: attempts,
      message: 'Documentation-only change failed offline or lint checks.',
    });
  }

  if (humanBlocker) {
    return bucket3Outcome({
      waitKind: 'human-boundary',
      repairAttempts: attempts,
      offlineSummary,
      unverifiedBoundary: cleanText(humanBoundaryDetail) || surfaceInfo.runtimeSurfaces.join(', ') || 'human interaction boundary',
      verifyCommand,
      message: 'Human interaction is required to verify this boundary before merge.',
    });
  }

  if (bucket2) {
    return {
      bucket: 2,
      decision: 'park-auth-wait',
      waitKind: 'auth-environment',
      eligible: false,
      freeSlot: true,
      keepPr: true,
      repairRoundsToSpend: 0,
      repairAttemptsNext: attempts,
      cooldownTool: bucket2.cooldownTool,
      resumeMode: 'validate-only-same-head',
      checkCommand: bucket2.checkCommand,
      message: `Environment/auth wait on ${bucket2.cooldownTool}; refresh login or service and verify with: ${bucket2.checkCommand}`,
      proof: emptyProof(),
      humanVerificationCard: [],
    };
  }

  const checks = Array.isArray(e2eChecks) ? e2eChecks : [];
  const executedRealChecks = checks.filter((c) => c && typeof c === 'object' && c.executed === true && REAL_E2E_KINDS.has(c.kind));
  const defaultVerifyCmd = cleanText(verifyCommand) || 'npm run test:e2e';

  if (surfaceInfo.requiresRealE2e && executedRealChecks.length === 0) {
    return bucket3Outcome({
      waitKind: 'missing-e2e',
      repairAttempts: attempts,
      offlineSummary,
      unverifiedBoundary: cleanText(humanBoundaryDetail) || surfaceInfo.runtimeSurfaces.join(', '),
      verifyCommand: defaultVerifyCmd,
      message: 'No runnable real end-to-end check executed for the changed runtime surfaces.',
    });
  }

  if (isBugFix === true && bugFixBaseControl === 'not-run') {
    return bucket3Outcome({
      waitKind: 'missing-e2e',
      repairAttempts: attempts,
      offlineSummary,
      unverifiedBoundary: cleanText(humanBoundaryDetail) || 'bug-fix base regression control',
      verifyCommand: defaultVerifyCmd,
      message: 'Bug-fix base regression control did not run.',
    });
  }

  const allRealPassed = executedRealChecks.every(isPassingRealE2eCheck);
  const coveredSurfaces = coversRequiredProofKinds(surfaceInfo.requiredProofKinds, executedRealChecks.filter(isPassingRealE2eCheck));
  const bugFixControlOk = isBugFix !== true || bugFixBaseControl === 'ran-and-failed-on-base';

  if (offlinePassed === true && lintErrors.length === 0 && allRealPassed && coveredSurfaces && bugFixControlOk) {
    return {
      bucket: 1,
      decision: mode === 'observe' ? 'allow-would-merge' : 'allow-merge',
      waitKind: 'none',
      eligible: true,
      freeSlot: false,
      keepPr: false,
      repairRoundsToSpend: 0,
      repairAttemptsNext: attempts,
      cooldownTool: null,
      resumeMode: 'none',
      checkCommand: null,
      message: 'All offline, lint, and real end-to-end checks passed 100%.',
      proof: {
        surfaces: [...surfaceInfo.runtimeSurfaces],
        commands: executedRealChecks.map((c) => cleanText(c.command)),
        exitCodes: executedRealChecks.map((c) => c.exitCode),
      },
      humanVerificationCard: [],
    };
  }

  return bucket1FailureOutcome({
    repairAttempts: attempts,
    message: !bugFixControlOk
      ? 'Bug-fix regression check passed on base; repair test or fix.'
      : lintErrors.length > 0
        ? `Blocking validation lint findings: ${lintErrors.join(', ')}.`
        : 'Real end-to-end or offline validation check failed.',
  });
}

/**
 * Skip claiming issues that depend on a tool currently on active cooldown so workers pick up unrelated work.
 */
export function shouldClaimWithCooldowns({ issueRequiredTools = [], toolCooldowns = {} } = {}) {
  const normalizedCooldowns = new Map();
  if (toolCooldowns && typeof toolCooldowns === 'object') {
    for (const [key, entry] of Object.entries(toolCooldowns)) {
      const normKey = cleanTool(key);
      if (normKey && entry && entry.active === true) normalizedCooldowns.set(normKey, entry);
    }
  }
  const required = Array.isArray(issueRequiredTools) ? issueRequiredTools : [];
  for (const rawTool of required) {
    const tool = cleanTool(rawTool);
    if (tool && normalizedCooldowns.has(tool)) {
      return { claimable: false, blockedByTool: tool, reason: 'tool-cooldown' };
    }
  }
  return { claimable: true, blockedByTool: null, reason: null };
}

/**
 * Decide whether a parked PR can resume validate-only at its exact saved commit head with zero code rebuilds.
 */
export function planValidationResume({
  pr,
  headSha,
  currentPrHeadSha,
  cooldownTool,
  preflightExitCode,
  userResumed = false,
} = {}) {
  const targetTool = cleanTool(cooldownTool) || null;
  if (cleanText(currentPrHeadSha) !== cleanText(headSha)) {
    return {
      action: 'head-changed-abort',
      pr,
      headSha,
      rebuildCode: false,
      runValidationOnly: false,
      clearCooldown: false,
      targetTool,
    };
  }
  if (preflightExitCode === 0 || userResumed === true) {
    return {
      action: 'resume-validate-only',
      pr,
      headSha,
      rebuildCode: false,
      runValidationOnly: true,
      clearCooldown: true,
      targetTool,
    };
  }
  return {
    action: 'stay-parked',
    pr,
    headSha,
    rebuildCode: false,
    runValidationOnly: false,
    clearCooldown: false,
    targetTool,
  };
}

function testTargetsBoundarySurface(path, text) {
  const candidatePaths = [normalizePath(path)];
  for (const match of text.matchAll(BOUNDARY_IMPORT_RE)) {
    const spec = normalizePath(match[1].replace(/^(?:\.\.\/)+/, ''));
    if (spec) candidatePaths.push(spec);
  }
  const detected = detectChangedSurfaces({ changedFiles: candidatePaths });
  return detected.runtimeSurfaces.some((s) => s !== 'runtime-code');
}

/**
 * Deterministic backside validation lint for silent validation skips and mock-only boundary tests.
 */
export function lintValidationCode({ path = '', kind = 'test', text = '', hasRealE2eCoverage = false } = {}) {
  const filePath = normalizePath(path) || 'unknown';
  const source = String(text ?? '');
  const lines = source.split(/\r?\n/);
  const codeSet = new Set();
  const warnings = [];

  if (kind === 'code' || kind === 'test') {
    for (let i = 0; i < lines.length; i += 1) {
      const line = lines[i];
      if (/^\s*(?:re|pattern)\s*:\s*\//.test(line)) continue;
      for (const { re, detail } of SILENT_SKIP_LINE_PATTERNS) {
        if (re.test(line)) {
          codeSet.add('silent-validation-skip');
          warnings.push(`Warning: validation lint: ${filePath}:${i + 1} [silent-validation-skip] ${detail}`);
          break;
        }
      }
    }
  }

  if (kind === 'test' && hasRealE2eCoverage !== true && testTargetsBoundarySurface(filePath, source)) {
    const mockLineIndex = lines.findIndex((line) => MOCK_USAGE_RE.test(line));
    if (mockLineIndex >= 0 && !REAL_EXEC_RE.test(source)) {
      codeSet.add('boundary-mock-only-test');
      warnings.push(
        `Warning: validation lint: ${filePath}:${mockLineIndex + 1} [boundary-mock-only-test] mock-only test covers a runtime boundary with no real E2E coverage`,
      );
    }
  }

  const codes = [...codeSet].sort();
  return { ok: codes.length === 0, codes, warnings };
}
