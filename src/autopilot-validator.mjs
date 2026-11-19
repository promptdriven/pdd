// Generated from prompts/cli/autopilot-validator.prompt.md

export const MAX_VALIDATION_REPAIRS = 3;

const REAL_E2E_KINDS = new Set([
  'subprocess-cli',
  'local-server-or-db',
  'browser-playwright',
  'live-binding',
  'real-execution',
]);

const RUNTIME_CODE_EXT_RE = /\.(?:js|mjs|cjs|ts|mts|cts|py|go|rs|rb|java|kt|cs|php|swift|c|cpp|h|hpp|m|mm|ex|exs|dart|zig|lua|graphql|gql|proto|scala|clj|erl|hs|r|jl|pl|groovy|wasm|tf|hcl)$/i;
const NON_PRODUCTION_DIR_RE = /^(?:test|tests|__tests__|spec|fixtures|examples|prompts|user_stories|docs)\//i;
const DOC_FILE_RE = /(?:^docs\/|\.(?:txt|rst)$|(?:^|\/)(?:license|changelog)[^/]*$)/i;
const HUMAN_INTERACTION_RE = /\b(?:browser\s+oauth|oauth\s+click|2fa|mfa|captcha|live\s+payment|physical\s+hardware)\b/i;

const tokenMatch = (pattern) => new RegExp(`(?:^|[^a-z0-9])(?:${pattern})(?:$|[^a-z0-9])`, 'i');
const CLI_TOKEN_RE = tokenMatch('cli');
const API_TOKEN_RE = tokenMatch('server|router|api|http|https|ws|websocket|graphql|grpc');
const DB_TOKEN_RE = tokenMatch('postgres|postgresql|mysql|sqlite|mongo|mongodb|redis|db');
const EXTERNAL_TOKEN_RE = tokenMatch('gcloud|gcp|aws|azure|stripe|docker|kubernetes|k8s|oauth|auth|webhook|terraform');

const SURFACE_MATCHERS = [
  {
    surface: 'cli',
    test: (norm, base) => /^(?:bin|cli|cmd|scripts)\//i.test(norm) || /\.sh$/i.test(norm) || CLI_TOKEN_RE.test(base),
  },
  {
    surface: 'api-server',
    test: (norm, base) => /^(?:api|server|routes|handlers|controllers)\//i.test(norm) || API_TOKEN_RE.test(base),
  },
  {
    surface: 'database',
    test: (norm, base) => /^(?:db|database|migrations|prisma|sql)\//i.test(norm) || /\.sql$/i.test(norm) || DB_TOKEN_RE.test(base),
  },
  {
    surface: 'web-ui',
    test: (norm) => /^(?:web|ui|frontend|pages|components|views|app)\//i.test(norm)
      || /\.(?:jsx|tsx|vue|svelte|html|css)$/i.test(norm)
      || /\.ui\.svg$/i.test(norm),
  },
  {
    surface: 'external-tool',
    test: (norm, base) => /^dockerfile(?:\.|$)/i.test(base)
      || base.startsWith('docker-compose')
      || EXTERNAL_TOKEN_RE.test(norm),
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

export const MOCK_USAGE_RE = /\b(?:mock\.|vi\.mock|jest\.mock|sinon\.stub|fakeClient|fakeServer|fakeTransport)\b|stub(?:bed)?Handler/i;
export const REAL_E2E_EXEC_RE = /\b(?:spawn|spawnSync|execFile|execFileSync|execSync|createServer|playwright|puppeteer|supertest|DatabaseSync)\b|\.\s*listen\s*\(|\bfetch\s*\(|\bhttps?\.request\s*\(|\b(?:chromium|firefox|webkit)\.launch\s*\(|\bpage\.goto\s*\(/i;
const BROWSER_EXEC_RE = /\b(?:playwright|puppeteer)\b|\b(?:chromium|firefox|webkit)\.launch\s*\(|\bpage\.goto\s*\(/i;
const SERVER_OR_DB_EXEC_RE = /\b(?:createServer|supertest|DatabaseSync)\b|\.\s*listen\s*\(|\bfetch\s*\(|\bhttps?\.request\s*\(|\bnew\s+(?:Pool|Client)\s*\(/i;
const DB_DRIVER_IMPORT_RE = /(?:from|require\s*\()\s*['"`](?:pg|mysql2?|better-sqlite3|node:sqlite|sqlite3?|mongodb|redis|ioredis|@prisma\/client)['"`]/i;
const SUBPROCESS_EXEC_RE = /\b(?:spawn|spawnSync|execFile|execFileSync|execSync)\s*\(/;
const BOUNDARY_IMPORT_RE = /(?:from|require\s*\()\s*['"`]([^'"`]+)['"`]/g;
const PROD_PATH_LITERAL_RE = /['"`]((?:\.\.\/|\.\/)?(?:bin|cli|cmd|scripts|api|server|routes|handlers|controllers|db|database|migrations|prisma|sql|web|ui|frontend|pages|components|views|app|src)\/[A-Za-z0-9._/-]+)['"`]/g;

const SKIP_KEYWORD_RE = /(?:e2e|validation|validator|real-binding)/i;
const LOCAL_SKIP_HELPER_RE = /\blocalSkipRow\b|\bstoryLocalSkipOk\b|\blocalSkipOnly\b/i;
const FILTER_CODE_SHAPE_RE = /\.filter\s*\([^)]*!==\s*""/;
const FILTER_REAL_BINDING_RE = /\.filter\s*\([^)]*!==\s*['"`]real-binding-unavailable['"`]/i;
const CALL_DOT_SKIP_RE = /\b(?:test|it|t)\.skip\s*\(/;
const CALL_DOT_SKIP_E2E_RE = /\b(?:test|it|t)\.skip\s*\([^)]*(?:e2e|validation|validator|real-binding)/i;
const NODE_TEST_OPT_SKIP_RE = /\b(?:test|it|t)\s*\([^)]*,\s*\{[^}]*\bskip\s*:\s*(?:true|""|!)/;
const RETURN_PASS_OR_SKIP_RE = /\breturn\b[^;\n]*(?:\bok\s*:\s*true|\bpass\s*:\s*true|\bskipped\s*:\s*true|\bskip\s*:\s*true)/i;
const PROSE_EXCUSE_PATTERNS = [
  {
    re: /not a defect or needs-person blocker/i,
    detail: 'rewrites real-binding-unavailable as a non-blocker',
  },
  {
    re: /real-binding-unavailable.*local\s*skip|local\s*skip.*real-binding-unavailable/i,
    detail: 'treats missing live binding as an excused skip',
  },
];

const cleanText = (value) => (typeof value === 'string' ? value.trim() : '');
const cleanTool = (value) => cleanText(value).toLowerCase();
const normalizePath = (value) => cleanText(value).replace(/\\/g, '/').replace(/^\.\//, '');
const emptyProof = () => ({ surfaces: [], commands: [], exitCodes: [] });

function isRegexStartContext(prevToken) {
  if (!prevToken) return true;
  if ('([{:;,=!?&|+-*%^~<>'.includes(prevToken)) return true;
  return /^(?:return|case|throw|in|of|typeof|void|delete|new|else|do|yield|await)$/.test(prevToken);
}

/**
 * Strip JS/TS comments and separately mask string literal contents while keeping exact line numbers.
 */
export function scanJsPreserveLines(source) {
  const text = String(source ?? '');
  const noComments = [];
  const noStrings = [];
  let i = 0;
  let lastToken = '';

  const readPrevWord = () => {
    let j = noComments.length - 1;
    while (j >= 0 && /\s/.test(noComments[j])) j -= 1;
    if (j < 0) return '';
    const ch = noComments[j];
    if (!/[A-Za-z0-9_$]/.test(ch)) return ch;
    let end = j;
    while (j >= 0 && /[A-Za-z0-9_$]/.test(noComments[j])) j -= 1;
    return noComments.slice(j + 1, end + 1).join('');
  };

  while (i < text.length) {
    const ch = text[i];
    const next = text[i + 1];

    // Single-line comment
    if (ch === '/' && next === '/') {
      while (i < text.length && text[i] !== '\n') {
        noComments.push(' ');
        noStrings.push(' ');
        i += 1;
      }
      continue;
    }

    // Block comment
    if (ch === '/' && next === '*') {
      noComments.push(' ', ' ');
      noStrings.push(' ', ' ');
      i += 2;
      while (i < text.length) {
        if (text[i] === '*' && text[i + 1] === '/') {
          noComments.push(' ', ' ');
          noStrings.push(' ', ' ');
          i += 2;
          break;
        }
        const keep = text[i] === '\n' ? '\n' : ' ';
        noComments.push(keep);
        noStrings.push(keep);
        i += 1;
      }
      continue;
    }

    // String or template literal
    if (ch === '\'' || ch === '"' || ch === '`') {
      const quote = ch;
      noComments.push(ch);
      noStrings.push('"');
      i += 1;
      while (i < text.length) {
        const c = text[i];
        if (c === '\\' && i + 1 < text.length) {
          noComments.push(c, text[i + 1]);
          if (text[i + 1] === '\n') noStrings.push('\n');
          i += 2;
          continue;
        }
        if (c === quote) {
          noComments.push(c);
          noStrings.push('"');
          i += 1;
          break;
        }
        if (c === '\n' && quote !== '`') {
          noComments.push('\n');
          noStrings.push('"', '\n');
          i += 1;
          break;
        }
        noComments.push(c);
        if (c === '\n') noStrings.push('\n');
        i += 1;
      }
      lastToken = '""';
      continue;
    }

    // Regex literal (avoid mis-parsing quotes inside /.../)
    if (ch === '/' && next !== '/' && next !== '*' && isRegexStartContext(lastToken || readPrevWord())) {
      noComments.push(ch);
      noStrings.push(ch);
      i += 1;
      let inClass = false;
      while (i < text.length) {
        const c = text[i];
        if (c === '\\' && i + 1 < text.length) {
          noComments.push(c, text[i + 1]);
          noStrings.push(c, text[i + 1]);
          i += 2;
          continue;
        }
        if (c === '\n') {
          noComments.push('\n');
          noStrings.push('\n');
          i += 1;
          break;
        }
        if (c === '[') inClass = true;
        else if (c === ']') inClass = false;
        noComments.push(c);
        noStrings.push(c);
        i += 1;
        if (c === '/' && !inClass) break;
      }
      lastToken = '/re/';
      continue;
    }

    noComments.push(ch);
    noStrings.push(ch);
    if (!/\s/.test(ch)) lastToken = /[A-Za-z0-9_$]/.test(ch) ? '' : ch;
    i += 1;
  }

  return {
    codeNoComments: noComments.join(''),
    codeNoStrings: noStrings.join(''),
  };
}

export function stripCommentsPreserveLines(source) {
  return scanJsPreserveLines(source).codeNoComments;
}

export function maskStringsPreserveLines(source) {
  return scanJsPreserveLines(source).codeNoStrings;
}

function isDocPath(norm) {
  if (/\.prompt\.md$/i.test(norm) || /^user_stories\//i.test(norm)) return false;
  return /\.md$/i.test(norm) || DOC_FILE_RE.test(norm);
}

function classifyProductionPathSurfaces(rawPath) {
  const norm = normalizePath(rawPath);
  if (!norm) return [];
  const lower = norm.toLowerCase();
  if (isDocPath(lower)) return ['docs'];
  if (NON_PRODUCTION_DIR_RE.test(lower)) return [];
  const base = lower.split('/').pop() || lower;
  const matched = [];
  for (const { surface, test } of SURFACE_MATCHERS) {
    if (test(lower, base)) matched.push(surface);
  }
  if (!matched.length && RUNTIME_CODE_EXT_RE.test(lower)) {
    matched.push('runtime-code');
  }
  return matched;
}

/**
 * Canonical module stem for matching production targets across imports and tests (e.g., api/orders.mjs -> api/orders).
 */
export function canonicalTargetPath(rawPath) {
  const norm = normalizePath(rawPath).toLowerCase();
  if (!norm) return '';
  return norm.replace(/\.(?:[cm]?[jt]sx?|py|go|rs|rb|java|kt|cs|php|swift|sh|sql|vue|svelte|html|css)$/i, '');
}

function resolveRelativeTarget(fromPath, spec) {
  const cleanSpec = normalizePath(spec);
  if (!cleanSpec) return '';
  if (!spec.startsWith('.')) {
    return cleanSpec;
  }
  const fromDir = normalizePath(fromPath).split('/').slice(0, -1);
  const parts = spec.replace(/\\/g, '/').split('/');
  const resolved = [...fromDir];
  for (const part of parts) {
    if (!part || part === '.') continue;
    if (part === '..') resolved.pop();
    else resolved.push(part);
  }
  return normalizePath(resolved.join('/'));
}

/**
 * Extract production boundary targets and surfaces referenced by a test file (via imports or direct path references).
 */
export function inspectTestBoundaryTargets(testPath, text) {
  const normTest = normalizePath(testPath);
  const code = stripCommentsPreserveLines(text);
  const targetSet = new Set();
  const boundaryTargetSet = new Set();
  const surfaceSet = new Set();

  const consider = (rawTarget) => {
    const resolved = resolveRelativeTarget(normTest, rawTarget);
    if (!resolved || NON_PRODUCTION_DIR_RE.test(resolved.toLowerCase())) return;
    const surfaces = classifyProductionPathSurfaces(resolved);
    if (!surfaces.length) return;
    const canonical = canonicalTargetPath(resolved);
    if (!canonical) return;
    targetSet.add(canonical);
    const boundary = surfaces.filter((s) => s !== 'docs' && s !== 'runtime-code');
    if (boundary.length) {
      boundaryTargetSet.add(canonical);
      for (const s of boundary) surfaceSet.add(s);
    }
  };

  for (const match of code.matchAll(BOUNDARY_IMPORT_RE)) {
    const spec = match[1];
    if (spec.startsWith('.') || /^(?:bin|cli|cmd|scripts|api|server|routes|handlers|controllers|db|database|migrations|prisma|sql|web|ui|frontend|pages|components|views|app|src)\//i.test(spec)) {
      consider(spec);
    }
  }
  for (const match of code.matchAll(PROD_PATH_LITERAL_RE)) {
    consider(match[1]);
  }

  // Fallback to the test file's own stripped stem when it has no direct boundary production imports
  if (!boundaryTargetSet.size) {
    const stripped = normTest
      .replace(/^(?:test|tests|__tests__|spec)\//i, '')
      .replace(/\.(?:test|spec|vectors\.test|e2e\.test)\.[a-z0-9]+$/i, '.mjs');
    const ownSurfaces = classifyProductionPathSurfaces(stripped).filter((s) => s !== 'docs' && s !== 'runtime-code');
    if (ownSurfaces.length) {
      for (const s of ownSurfaces) surfaceSet.add(s);
      boundaryTargetSet.add(`test-stem:${canonicalTargetPath(stripped)}`);
    }
  }

  return {
    allTargets: [...targetSet].sort(),
    boundaryTargets: [...boundaryTargetSet].sort(),
    boundarySurfaces: [...surfaceSet].sort(),
  };
}

/**
 * Detect which real E2E proof kinds a test file genuinely executes (comments/strings and skipped tests excluded).
 */
export function detectRealE2eKindsInTest(testPath, text) {
  const lint = lintValidationCode({ path: testPath, kind: 'test', text, hasRealE2eCoverage: true });
  if (lint.codes.includes('silent-validation-skip')) return [];

  const { codeNoComments, codeNoStrings } = scanJsPreserveLines(text);
  const kinds = new Set();

  const hasBrowser = BROWSER_EXEC_RE.test(codeNoStrings)
    || (/\b(?:playwright|puppeteer)\b/i.test(codeNoComments) && /\.(?:launch|goto|newPage)\s*\(/i.test(codeNoStrings));
  const hasServerOrDb = SERVER_OR_DB_EXEC_RE.test(codeNoStrings)
    || (DB_DRIVER_IMPORT_RE.test(codeNoComments) && !MOCK_USAGE_RE.test(codeNoStrings));
  const hasSubprocess = SUBPROCESS_EXEC_RE.test(codeNoStrings);
  const hasAnyRealExec = hasBrowser || hasServerOrDb || hasSubprocess || REAL_E2E_EXEC_RE.test(codeNoStrings);

  if (hasBrowser) kinds.add('browser-playwright');
  if (hasServerOrDb) kinds.add('local-server-or-db');
  if (hasSubprocess) kinds.add('subprocess-cli');
  if (hasAnyRealExec) kinds.add('live-binding');
  if (hasAnyRealExec || !MOCK_USAGE_RE.test(codeNoStrings)) kinds.add('real-execution');

  return [...kinds].sort();
}

/**
 * Classify changed repository paths into validation surfaces and required E2E proof kinds.
 */
export function detectChangedSurfaces({ changedFiles = [] } = {}) {
  const files = Array.isArray(changedFiles) ? changedFiles.map(normalizePath).filter(Boolean) : [];
  const surfaceSet = new Set();
  let allDocs = files.length > 0;

  for (const file of files) {
    const fileSurfaces = classifyProductionPathSurfaces(file);
    if (!fileSurfaces.length || fileSurfaces.some((s) => s !== 'docs')) allDocs = false;
    for (const s of fileSurfaces) surfaceSet.add(s);
  }

  const surfaces = [...surfaceSet].sort();
  const runtimeSurfaces = surfaces.filter((s) => s !== 'docs');
  const emptyChangedFiles = files.length === 0;
  const docsOnly = allDocs && runtimeSurfaces.length === 0;
  const requiresRealE2e = runtimeSurfaces.length > 0 || emptyChangedFiles;

  const proofKindSet = new Set();
  for (const surface of runtimeSurfaces) {
    if (SURFACE_TO_PROOF_KIND[surface]) proofKindSet.add(SURFACE_TO_PROOF_KIND[surface]);
  }
  if (emptyChangedFiles || (!proofKindSet.size && runtimeSurfaces.includes('runtime-code'))) {
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
  const normalizedFiles = Array.isArray(changedFiles) ? changedFiles.map(normalizePath).filter(Boolean) : [];
  const surfaceInfo = detectChangedSurfaces({ changedFiles: normalizedFiles });
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

  const defaultVerifyCmd = cleanText(verifyCommand) || 'npm run test:e2e';
  if (normalizedFiles.length === 0) {
    return bucket3Outcome({
      waitKind: 'missing-e2e',
      repairAttempts: attempts,
      offlineSummary,
      unverifiedBoundary: cleanText(humanBoundaryDetail) || 'unknown changed files (diff unavailable)',
      verifyCommand: defaultVerifyCmd,
      message: 'Changed files list is empty or unavailable; cannot verify validation surfaces.',
    });
  }

  const checks = Array.isArray(e2eChecks) ? e2eChecks : [];
  const executedRealChecks = checks.filter((c) => c && typeof c === 'object' && c.executed === true && REAL_E2E_KINDS.has(c.kind));

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

  if (isBugFix === true && (bugFixBaseControl === 'not-run' || bugFixBaseControl === 'not-applicable')) {
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
        : !coveredSurfaces
          ? `Missing required real end-to-end proof kinds: ${surfaceInfo.requiredProofKinds.join(', ')}.`
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

function matchSilentSkipLine(codeLine, maskedLine, kind) {
  if (/^\s*(?:re|pattern)\s*:\s*\//.test(codeLine)) return null;
  if (LOCAL_SKIP_HELPER_RE.test(maskedLine)) {
    return 'silent validation local-skip helper bypasses real validation';
  }
  if (FILTER_CODE_SHAPE_RE.test(maskedLine) && FILTER_REAL_BINDING_RE.test(codeLine)) {
    return 'filters real-binding-unavailable out of blocking refusals';
  }
  if (CALL_DOT_SKIP_RE.test(maskedLine) && CALL_DOT_SKIP_E2E_RE.test(codeLine)) {
    return 'unconditionally skips an E2E or validation test';
  }
  if (NODE_TEST_OPT_SKIP_RE.test(maskedLine) && SKIP_KEYWORD_RE.test(codeLine)) {
    return 'unconditionally skips an E2E or validation test via test options';
  }
  if (kind === 'code') {
    if (RETURN_PASS_OR_SKIP_RE.test(maskedLine) && /\breal-binding-unavailable\b/i.test(codeLine)) {
      return 'treats real-binding-unavailable as an inline pass or silent skip';
    }
    for (const { re, detail } of PROSE_EXCUSE_PATTERNS) {
      if (re.test(codeLine)) return detail;
    }
  }
  return null;
}

/**
 * Deterministic backside validation lint for silent validation skips and mock-only boundary tests.
 */
export function lintValidationCode({ path = '', kind = 'test', text = '', hasRealE2eCoverage = false } = {}) {
  const filePath = normalizePath(path) || 'unknown';
  const source = String(text ?? '');
  const { codeNoComments, codeNoStrings } = scanJsPreserveLines(source);
  const codeLines = codeNoComments.split(/\r?\n/);
  const maskedLines = codeNoStrings.split(/\r?\n/);
  const codeSet = new Set();
  const warnings = [];

  if (kind === 'code' || kind === 'test') {
    for (let i = 0; i < codeLines.length; i += 1) {
      const detail = matchSilentSkipLine(codeLines[i], maskedLines[i] ?? '', kind);
      if (detail) {
        codeSet.add('silent-validation-skip');
        warnings.push(`Warning: validation lint: ${filePath}:${i + 1} [silent-validation-skip] ${detail}`);
      }
    }
  }

  if (kind === 'test' && hasRealE2eCoverage !== true) {
    const { boundarySurfaces } = inspectTestBoundaryTargets(filePath, source);
    if (boundarySurfaces.length > 0) {
      const mockLineIndex = maskedLines.findIndex((line) => MOCK_USAGE_RE.test(line));
      if (mockLineIndex >= 0 && !REAL_E2E_EXEC_RE.test(codeNoStrings)) {
        codeSet.add('boundary-mock-only-test');
        warnings.push(
          `Warning: validation lint: ${filePath}:${mockLineIndex + 1} [boundary-mock-only-test] mock-only test covers a runtime boundary with no real E2E coverage`,
        );
      }
    }
  }

  const codes = [...codeSet].sort();
  return { ok: codes.length === 0, codes, warnings };
}
