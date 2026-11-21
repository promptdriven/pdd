// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: fe50a41112b31cf1d3d55fd5c6cbdb5ca7a332d5914b742a208ccf07fd29e607).

export const MAX_VALIDATION_REPAIRS = 3;
export const MIN_REALISTIC_PAYLOAD_BYTES = 4096;
export const REAL_HOST_FAILURE_CLASSES = Object.freeze([
  'nested-sandbox',
  'host-tty-ownership',
  'multi-turn-cli-state',
  'full-size-payload',
]);

const REAL_HOST_CLASS_SET = new Set(REAL_HOST_FAILURE_CLASSES);
const REAL_HOST_CLASS_LABELS = Object.freeze({
  'nested-sandbox': 'nested OS sandbox execution (real child process inside sandbox, not mocked argv-prefix test)',
  'host-tty-ownership': 'real host device/TTY ownership (/dev/tty UID/permissions on host kernel, not mocked TTY helper)',
  'multi-turn-cli-state': 'multi-turn real CLI state side effects (Turn 1 -> Turn 2 state/containment check, not single-turn stub)',
  'full-size-payload': `full-size realistic payload handling (> ${MIN_REALISTIC_PAYLOAD_BYTES} bytes un-truncated payload, not tiny synthetic fixture)`,
});

const REAL_E2E_KINDS = new Set([
  'subprocess-cli',
  'local-server-or-db',
  'browser-playwright',
  'live-binding',
  'real-host-smoke',
  'real-execution',
]);

const NON_PRODUCTION_DIR_RE = /^(?:test|tests|__tests__|spec|fixtures|examples|prompts|user_stories|docs)\//i;
const DOC_FILE_RE = /(?:^docs\/|\.(?:txt|rst)$|(?:^|\/)(?:license|changelog)[^/]*$)/i;
const HUMAN_INTERACTION_RE = /\b(?:browser\s+oauth|oauth\s+click|2fa|mfa|captcha|live\s+payment|physical\s+hardware)\b/i;

const tokenMatch = (pattern) => new RegExp(`(?:^|[^a-z0-9])(?:${pattern})(?:$|[^a-z0-9])`, 'i');
const CLI_TOKEN_RE = tokenMatch('cli');
const API_TOKEN_RE = tokenMatch('server|router|api|http|https|ws|websocket|graphql|grpc');
const DB_TOKEN_RE = tokenMatch('postgres|postgresql|mysql|sqlite|mongo|mongodb|redis|db');
const EXTERNAL_TOKEN_RE = tokenMatch('gcloud|gcp|aws|azure|stripe|docker|kubernetes|k8s|oauth|auth|webhook|terraform');
const OS_BOUNDARY_TOKEN_RE = tokenMatch('sandbox|seatbelt|seccomp|landlock|bwrap|bubblewrap|chroot|cgroup|tty|pty|termios|ioctl|subprocess|child[-_]?process|spawn|posix|syscall|kernel|daemon|ipc|unix[-_]?socket|os[-_]?signal');
const REAL_HOST_CLASS_PATH_RULES = [
  { id: 'nested-sandbox', re: tokenMatch('sandbox|seatbelt|seccomp|landlock|bwrap|bubblewrap|chroot|cgroup') },
  { id: 'host-tty-ownership', re: tokenMatch('tty|pty|termios|ioctl') },
  { id: 'multi-turn-cli-state', re: tokenMatch('cli[-_]?session|cli[-_]?wrapper|session[-_]?state|containment') },
  { id: 'full-size-payload', re: tokenMatch('payload|preview|truncat(?:e|ed|es|ing|ion)|framing|wire[-_]?frame|stream[-_]?buffer') },
];

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
  {
    surface: 'os-boundary',
    test: (norm, base) => /^(?:os|sandbox|tty|pty|subprocess)\//i.test(norm)
      || OS_BOUNDARY_TOKEN_RE.test(base),
  },
];

const SURFACE_TO_PROOF_KIND = {
  cli: 'subprocess-cli',
  'api-server': 'local-server-or-db',
  database: 'local-server-or-db',
  'web-ui': 'browser-playwright',
  'external-tool': 'live-binding',
  'os-boundary': 'real-host-smoke',
  'native-only': 'real-host-smoke',
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

export const MOCK_USAGE_RE = /\b(?:mock\.|vi\.mock|vi\.doMock|vi\.fn|vi\.spyOn|vi\.stubGlobal|jest\.mock|jest\.doMock|jest\.fn|jest\.spyOn|sinon\.stub|MagicMock|unittest\.mock|fakeClient|fakeServer|fakeTransport|fakeSandbox|mockSandbox|stubSandbox|fakeTty|mockTty|stubTty|fakeDb|mockDb|fakeDriver|mockDriver|mockSpawn|fakeSpawn|fakeSubprocess|fakeCli|stubCli)\b|stub(?:bed)?(?:Handler|Wrapper)/i;
export const REAL_E2E_EXEC_RE = /\b(?:spawn|spawnSync|execFile|execFileSync|execSync|createServer|playwright|puppeteer|supertest|DatabaseSync)\b|\.\s*listen\s*\(|\bfetch\s*\(|\bhttps?\.request\s*\(|\b(?:chromium|firefox|webkit)\.launch\s*\(|\bpage\.goto\s*\(/i;
const REAL_DEVICE_PATH_RE = /\/dev\/(?:tty|ptmx|pts\/)/;
const SANDBOX_EXEC_RE = /\b(?:sandbox-exec|sandbox_apply|bwrap|bubblewrap|seatbelt|seccomp|landlock|unshare|chroot|firejail)\b/i;
const LOOP_START_ALL_RE = /\b(for|while)[ \t]*\(|\.[ \t]*(forEach|map)[ \t]*\(/g;
const SUBPROCESS_EXEC_RE = /\b(?:spawn|spawnSync|execFile|execFileSync|execSync)\s*\(/;
const SUBPROCESS_CALL_START_RE = /([A-Za-z_$][A-Za-z0-9_$]*[ \t]*\.[ \t]*)?\b(spawn|spawnSync|execFile|execFileSync|execSync)[ \t]*\(/g;
const TRIVIAL_SUBPROCESS_BIN_RE = /^(?:echo|printf|true|false|pwd|uname|whoami|id|date|sleep|cat|ls|test|\[|:)(?:\s|$)/i;
const EXTERNAL_TOOL_EXEC_RE = /\b(?:gcloud|gsutil|bq|aws|az|stripe|docker|docker-compose|kubectl|helm|terraform|gh|pdd|curl|wget|psql|mysql|redis-cli|mongosh|ssh|scp|vault|npm|npx|git)\b/i;
const BOUNDARY_IMPORT_RE = /(?:from|require\s*\()\s*['"`]([^'"`]+)['"`]/g;
const PROD_PATH_LITERAL_RE = /['"`]((?:\.\.\/|\.\/)?(?:bin|cli|cmd|scripts|api|server|routes|handlers|controllers|db|database|migrations|prisma|sql|web|ui|frontend|pages|components|views|app|os|sandbox|tty|pty|subprocess|src)\/[A-Za-z0-9._/-]+)['"`]/g;

const SKIP_KEYWORD_RE = /(?:e2e|validation|validator|real-binding)/i;
const LOCAL_SKIP_HELPER_RE = /\blocalSkipRow\b|\bstoryLocalSkipOk\b|\blocalSkipOnly\b/i;
const FILTER_CODE_SHAPE_RE = /\.filter\s*\([^)]*!==\s*""/;
const FILTER_REAL_BINDING_RE = /\.filter\s*\([^)]*!==\s*['"`]real-binding-unavailable['"`]/i;
const CALL_DOT_SKIP_RE = /\b(?:test|it|t)\.skip\s*\(/;
const CALL_DOT_SKIP_E2E_RE = /\b(?:test|it|t)\.skip\s*\([^)]*(?:e2e|validation|validator|real-binding)/i;
const MULTILINE_CALL_DOT_SKIP_RE = /\b(?:test|it|t)\.skip\s*\(\s*[^,()]{1,200}/gs;
const NODE_TEST_OPT_SKIP_RE = /\b(?:test|it|t)\s*\([^)]*,\s*\{[^}]*\bskip\s*:\s*(?:true|""|!)/;
const MULTILINE_NODE_TEST_OPT_SKIP_RE = /\b(?:test|it|t)\s*\(\s*[^,()]{1,200},\s*\{[^}]{0,400}\bskip\s*:\s*(?:true|""|!)/gs;
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
const normalizePath = (value) => {
  const raw = cleanText(value).replace(/\\/g, '/').replace(/\/+/g, '/');
  if (!raw) return '';
  const isAbs = raw.startsWith('/');
  const parts = raw.split('/');
  const out = [];
  for (const part of parts) {
    if (!part || part === '.') continue;
    if (part === '..') {
      if (out.length && out[out.length - 1] !== '..') out.pop();
      else if (!isAbs) out.push('..');
    } else {
      out.push(part);
    }
  }
  const joined = out.join('/');
  return isAbs ? `/${joined}` : joined;
};
const isCanonicalRepoPath = (value) => typeof value === 'string'
  && value.length > 0
  && value.length <= 1000
  && !value.startsWith('/')
  && !/^[A-Za-z]:/.test(value)
  && !/[\\\x00-\x1f\x7f]/.test(value)
  && !value.split('/').some((part) => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');
const emptyProof = () => ({ surfaces: [], commands: [], exitCodes: [] });

function isRegexStartContext(prevToken) {
  if (!prevToken) return true;
  if ('([{:;,=!?&|+-*%^~<>}'.includes(prevToken)) return true;
  return /^(?:return|case|throw|in|of|typeof|void|delete|new|else|do|yield|await)$/.test(prevToken);
}

/**
 * Strip JS/TS comments and separately mask string literal contents while keeping exact line numbers,
 * plus exact inline string literal lengths, unit lengths preceding `.repeat(...)`, and decoded string
 * literal contents indexed by each opening `"` offset in `codeNoStrings`.
 */
function scanJsWithMetrics(source) {
  const text = String(source ?? '');
  const noComments = [];
  const noStrings = [];
  const templateBraceDepths = [];
  let maxInlineStringBytes = 0;
  const repeatLiteralUnits = new Map(); // endIndexInNoStrings -> literal unit char length
  const stringLiteralsByOpenPos = new Map(); // openIndexInNoStrings -> decoded literal content
  let i = 0;
  let lastToken = '';
  let noStringsLen = 0;

  const decodeEscape = (ch) => (ch === 'n' ? '\n' : ch === 'r' ? '\r' : ch === 't' ? '\t' : ch);

  const pushNoStrings = (...parts) => {
    for (const part of parts) {
      noStrings.push(part);
      noStringsLen += part.length;
    }
  };

  const recordLiteralLen = (len, nextPos) => {
    if (len > maxInlineStringBytes) maxInlineStringBytes = len;
    if (len >= 0) {
      let k = nextPos;
      while (k < text.length && (text[k] === ' ' || text[k] === '\t' || text[k] === '\r' || text[k] === '\n')) k += 1;
      if (text[k] === '.') {
        k += 1;
        while (k < text.length && (text[k] === ' ' || text[k] === '\t')) k += 1;
        if (text.startsWith('repeat', k)) {
          repeatLiteralUnits.set(noStringsLen - 1, len);
        }
      }
    }
  };

  const scanTemplatePart = (isStart, openIdx) => {
    let chunkLen = 0;
    let contentStart = i;
    let parts = null;
    const finalizeLiteral = (endPos) => {
      const lit = parts
        ? (parts.push(text.slice(contentStart, endPos)), parts.join(''))
        : text.slice(contentStart, endPos);
      stringLiteralsByOpenPos.set(openIdx, lit);
    };
    while (i < text.length) {
      const c = text[i];
      if (c === '\\' && i + 1 < text.length) {
        if (!parts) parts = [];
        if (i > contentStart) parts.push(text.slice(contentStart, i));
        const esc = text[i + 1];
        noComments.push(c, esc);
        if (esc === '\n') pushNoStrings('\n');
        else parts.push(decodeEscape(esc));
        chunkLen += 1;
        i += 2;
        contentStart = i;
        continue;
      }
      if (c === '$' && text[i + 1] === '{') {
        finalizeLiteral(i);
        if (chunkLen > maxInlineStringBytes) maxInlineStringBytes = chunkLen;
        noComments.push('$', '{');
        pushNoStrings('"+(');
        i += 2;
        templateBraceDepths.push(1);
        lastToken = '(';
        return;
      }
      if (c === '`') {
        finalizeLiteral(i);
        noComments.push(c);
        pushNoStrings('"');
        i += 1;
        if (isStart) recordLiteralLen(chunkLen, i);
        else if (chunkLen > maxInlineStringBytes) maxInlineStringBytes = chunkLen;
        lastToken = '""';
        return;
      }
      noComments.push(c);
      if (c === '\n') pushNoStrings('\n');
      chunkLen += 1;
      i += 1;
    }
    finalizeLiteral(i);
    if (chunkLen > maxInlineStringBytes) maxInlineStringBytes = chunkLen;
    lastToken = '""';
  };

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
        pushNoStrings(' ');
        i += 1;
      }
      continue;
    }

    // Block comment
    if (ch === '/' && next === '*') {
      noComments.push(' ', ' ');
      pushNoStrings(' ', ' ');
      i += 2;
      while (i < text.length) {
        if (text[i] === '*' && text[i + 1] === '/') {
          noComments.push(' ', ' ');
          pushNoStrings(' ', ' ');
          i += 2;
          break;
        }
        const keep = text[i] === '\n' ? '\n' : ' ';
        noComments.push(keep);
        pushNoStrings(keep);
        i += 1;
      }
      continue;
    }

    // Template literal (scan ${...} expressions as code while masking static text)
    if (ch === '`') {
      const openIdx = noStringsLen;
      noComments.push(ch);
      pushNoStrings('"');
      i += 1;
      scanTemplatePart(true, openIdx);
      continue;
    }

    // Track braces inside active template ${...} expressions
    if (templateBraceDepths.length > 0) {
      if (ch === '{') {
        templateBraceDepths[templateBraceDepths.length - 1] += 1;
      } else if (ch === '}') {
        templateBraceDepths[templateBraceDepths.length - 1] -= 1;
        if (templateBraceDepths[templateBraceDepths.length - 1] === 0) {
          templateBraceDepths.pop();
          noComments.push('}');
          pushNoStrings(')+');
          const nextOpenIdx = noStringsLen;
          pushNoStrings('"');
          i += 1;
          scanTemplatePart(false, nextOpenIdx);
          continue;
        }
      }
    }

    // Single- or double-quoted string literal
    if (ch === '\'' || ch === '"') {
      const quote = ch;
      const openIdx = noStringsLen;
      noComments.push(ch);
      pushNoStrings('"');
      i += 1;
      let contentStart = i;
      let parts = null;
      let litLen = 0;
      let closed = false;
      while (i < text.length) {
        const c = text[i];
        if (c === '\\' && i + 1 < text.length) {
          if (!parts) parts = [];
          if (i > contentStart) parts.push(text.slice(contentStart, i));
          const esc = text[i + 1];
          noComments.push(c, esc);
          if (esc === '\n') pushNoStrings('\n');
          else parts.push(decodeEscape(esc));
          litLen += 1;
          i += 2;
          contentStart = i;
          continue;
        }
        if (c === quote) {
          const lit = parts
            ? (parts.push(text.slice(contentStart, i)), parts.join(''))
            : text.slice(contentStart, i);
          stringLiteralsByOpenPos.set(openIdx, lit);
          noComments.push(c);
          pushNoStrings('"');
          i += 1;
          recordLiteralLen(litLen, i);
          closed = true;
          break;
        }
        if (c === '\n') {
          const lit = parts
            ? (parts.push(text.slice(contentStart, i)), parts.join(''))
            : text.slice(contentStart, i);
          stringLiteralsByOpenPos.set(openIdx, lit);
          noComments.push('\n');
          pushNoStrings('"', '\n');
          i += 1;
          closed = true;
          break;
        }
        noComments.push(c);
        litLen += 1;
        i += 1;
      }
      if (!closed) {
        const lit = parts
          ? (parts.push(text.slice(contentStart, i)), parts.join(''))
          : text.slice(contentStart, i);
        stringLiteralsByOpenPos.set(openIdx, lit);
      }
      lastToken = '""';
      continue;
    }

    // Regex literal (mask body in codeNoStrings so /playwright/ or /localSkipRow/ never false-match)
    if (ch === '/' && next !== '/' && next !== '*' && isRegexStartContext(lastToken || readPrevWord())) {
      noComments.push(ch);
      pushNoStrings('/');
      i += 1;
      let inClass = false;
      while (i < text.length) {
        const c = text[i];
        if (c === '\\' && i + 1 < text.length) {
          noComments.push(c, text[i + 1]);
          i += 2;
          continue;
        }
        if (c === '\n') {
          noComments.push('\n');
          pushNoStrings('\n');
          i += 1;
          break;
        }
        if (c === '[') inClass = true;
        else if (c === ']') inClass = false;
        noComments.push(c);
        i += 1;
        if (c === '/' && !inClass) {
          pushNoStrings(' /');
          break;
        }
      }
      lastToken = '/re/';
      continue;
    }

    noComments.push(ch);
    pushNoStrings(ch);
    if (!/\s/.test(ch)) lastToken = /[A-Za-z0-9_$]/.test(ch) ? '' : ch;
    i += 1;
  }

  return {
    codeNoComments: noComments.join(''),
    codeNoStrings: noStrings.join(''),
    maxInlineStringBytes,
    repeatLiteralUnits,
    stringLiteralsByOpenPos,
  };
}

/**
 * Strip JS/TS comments and separately mask string literal contents while keeping exact line numbers.
 */
export function scanJsPreserveLines(source) {
  const { codeNoComments, codeNoStrings } = scanJsWithMetrics(source);
  return { codeNoComments, codeNoStrings };
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
  if (!matched.length) {
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

const FM_NATIVE_KIND_LINE_RE = /^[ \t]*kind[ \t]*:[ \t]*(?:['"])?native-only(?:['"])?[ \t]*(?:#[^\r\n]*)?$/i;
const FM_REASON_LINE_RE = /^[ \t]*reason[ \t]*:[ \t]*(.+)$/i;

function isTagNameBoundary(ch) {
  return ch === '>' || ch === '/' || ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r';
}

function findRuntimeInterfaceBodies(text) {
  if (!text) return [];
  const lower = text.toLowerCase();
  const detailsSpans = [];

  let pos = 0;
  while (pos < lower.length) {
    const detOpen = lower.indexOf('<details', pos);
    if (detOpen < 0) break;
    const afterDet = detOpen + 8;
    if (afterDet >= lower.length || !isTagNameBoundary(lower[afterDet])) {
      pos = afterDet;
      continue;
    }
    const detTagEnd = lower.indexOf('>', afterDet);
    if (detTagEnd < 0) break;
    let sumStart = detTagEnd + 1;
    while (sumStart < lower.length && (lower[sumStart] === ' ' || lower[sumStart] === '\t' || lower[sumStart] === '\n' || lower[sumStart] === '\r')) {
      sumStart += 1;
    }
    if (!lower.startsWith('<summary', sumStart) || sumStart + 8 >= lower.length || !isTagNameBoundary(lower[sumStart + 8])) {
      pos = detTagEnd + 1;
      continue;
    }
    const sumTagEnd = lower.indexOf('>', sumStart + 8);
    if (sumTagEnd < 0) break;
    const sumClose = lower.indexOf('</summary>', sumTagEnd + 1);
    if (sumClose < 0) break;
    const sumInner = text.slice(sumTagEnd + 1, sumClose);
    if (/[\r\n]/.test(sumInner) || !/runtime[ \t]+interface/i.test(sumInner)) {
      pos = sumClose + 10;
      continue;
    }
    const detClose = lower.indexOf('</details>', sumClose + 10);
    if (detClose < 0) break;
    detailsSpans.push({ start: detOpen, end: detClose + 10, bodyStart: sumClose + 10, bodyEnd: detClose });
    pos = detClose + 10;
  }

  const headingSpans = [];
  let detIdx = 0;
  let lineStart = 0;
  let activeFence = null;
  let openHeading = null;
  while (lineStart <= text.length) {
    const nl = text.indexOf('\n', lineStart);
    const lineEnd = nl < 0 ? text.length : nl;
    const nextStart = nl < 0 ? text.length + 1 : nl + 1;
    const line = text.slice(lineStart, lineEnd).replace(/\r$/, '');

    while (detIdx < detailsSpans.length && detailsSpans[detIdx].end <= lineStart) detIdx += 1;
    if (detIdx < detailsSpans.length && lineStart >= detailsSpans[detIdx].start) {
      if (openHeading) {
        headingSpans.push({ ...openHeading, end: lineStart, bodyEnd: lineStart });
        openHeading = null;
      }
      activeFence = null;
      lineStart = nextStart;
      continue;
    }

    if (activeFence) {
      const closeMatch = /^ {0,3}(`{3,}|~{3,})[ \t]*$/.exec(line);
      if (closeMatch && closeMatch[1][0] === activeFence.char && closeMatch[1].length >= activeFence.len) {
        activeFence = null;
      }
      lineStart = nextStart;
      continue;
    }

    const fenceOpen = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(line);
    if (fenceOpen && !(fenceOpen[1][0] === '`' && fenceOpen[2].includes('`'))) {
      activeFence = { char: fenceOpen[1][0], len: fenceOpen[1].length };
      lineStart = nextStart;
      continue;
    }

    if (openHeading) {
      if (/^#{1,6}[ \t]+\S/.test(line)) {
        headingSpans.push({ ...openHeading, end: lineStart, bodyEnd: lineStart });
        openHeading = null;
        if (/^#{2,6}[ \t]+runtime[ \t]+interface[ \t]*$/i.test(line)) {
          openHeading = { start: lineStart, bodyStart: nl < 0 ? text.length : nl + 1 };
        }
      }
    } else if (/^#{2,6}[ \t]+runtime[ \t]+interface[ \t]*$/i.test(line)) {
      openHeading = { start: lineStart, bodyStart: nl < 0 ? text.length : nl + 1 };
    }
    lineStart = nextStart;
  }
  if (openHeading) {
    headingSpans.push({ ...openHeading, end: text.length, bodyEnd: text.length });
  }

  return [...detailsSpans, ...headingSpans]
    .sort((a, b) => a.start - b.start || a.end - b.end)
    .map((span) => text.slice(span.bodyStart, span.bodyEnd));
}

function scanJsonFencesInMarkdown(chunk) {
  const lines = String(chunk ?? '').split(/\r?\n/);
  const blocks = [];
  let active = null;
  for (const line of lines) {
    if (active) {
      const close = /^ {0,3}(`{3,}|~{3,})[ \t]*$/.exec(line);
      if (close && close[1][0] === active.char && close[1].length >= active.len) {
        blocks.push({ lang: active.lang, body: active.bodyLines.join('\n') });
        active = null;
      } else {
        active.bodyLines.push(line);
      }
      continue;
    }
    const open = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(line);
    if (open && !(open[1][0] === '`' && open[2].includes('`'))) {
      const info = open[2].trim();
      const lang = (info.split(/[\s{`~]/)[0] ?? '').toLowerCase();
      active = { char: open[1][0], len: open[1].length, lang, bodyLines: [] };
    }
  }
  return blocks;
}

function parseNativeOnlyPromptMeta(raw) {
  const text = String(raw ?? '');
  if (!text) return null;
  let bodyStart = -1;
  let fmEndOffset = 0;
  if (text.startsWith('---\n')) bodyStart = 4;
  else if (text.startsWith('---\r\n')) bodyStart = 5;
  if (bodyStart > 0) {
    let pos = bodyStart;
    let isNativeKind = false;
    let reason = '';
    while (pos <= text.length) {
      const nl = text.indexOf('\n', pos);
      const lineEnd = nl < 0 ? text.length : nl;
      const line = text.slice(pos, lineEnd).replace(/\r$/, '');
      if (line === '---') {
        fmEndOffset = nl < 0 ? text.length : nl + 1;
        if (isNativeKind) {
          return { nativeOnly: true, reason, bodyOffset: fmEndOffset };
        }
        break;
      }
      if (!isNativeKind && FM_NATIVE_KIND_LINE_RE.test(line)) {
        isNativeKind = true;
      } else if (!reason) {
        const reasonMatch = FM_REASON_LINE_RE.exec(line);
        if (reasonMatch) reason = reasonMatch[1].trim().replace(/^['"]|['"]$/g, '');
      }
      if (nl < 0) break;
      pos = nl + 1;
    }
  }

  for (const body of findRuntimeInterfaceBodies(text)) {
    for (const fence of scanJsonFencesInMarkdown(body)) {
      if (fence.lang !== 'json' && fence.lang !== '') continue;
      try {
        const parsed = JSON.parse(fence.body);
        if (parsed && typeof parsed === 'object' && !Array.isArray(parsed) && parsed.kind === 'native-only') {
          return { nativeOnly: true, reason: cleanText(parsed.reason), bodyOffset: fmEndOffset };
        }
      } catch {}
    }
  }
  return null;
}

const HEADER_COMMENT_OPENER_RE = /^(?:\/\/+|#+|--|;+|\/\*+|\*+|<!--|"""|''')/;
const HEADER_TAIL_OK_RE = /^(?:(?:\(sha256: [a-f0-9]{64}\)|sha256=[a-f0-9]{64})?\.?[ \t]*(?:\*\/|-->|"""|''')?)?$/;

function extractHeaderPromptRefs(rawContent) {
  if (!rawContent) return [];
  const buf = Buffer.isBuffer(rawContent) ? rawContent : Buffer.from(String(rawContent), 'utf8');
  const lines = buf.subarray(0, 4096).toString('utf8').split(/\r?\n/);
  if (buf.length > 4096) lines.pop();
  const refs = [];
  const seen = new Set();
  for (const rawLine of lines) {
    if (rawLine.length > 1100) continue;
    let rest = rawLine.trim();
    if (!rest) continue;
    let hasOpener = false;
    const opener = HEADER_COMMENT_OPENER_RE.exec(rest);
    if (opener) {
      hasOpener = true;
      rest = rest.slice(opener[0].length).replace(/^[ \t]+/, '');
    }
    let afterLabel = null;
    if (rest.startsWith('Generated from ')) {
      afterLabel = rest.slice('Generated from '.length);
    } else if (hasOpener && rest.startsWith('Prompt: ')) {
      afterLabel = rest.slice('Prompt: '.length);
    }
    if (!afterLabel) continue;
    const sp = afterLabel.search(/[ \t]/);
    let rawToken = sp < 0 ? afterLabel : afterLabel.slice(0, sp);
    const tail = sp < 0 ? '' : afterLabel.slice(sp).trim();
    if (!tail) rawToken = rawToken.replace(/(?:\*\/|-->|"""|''')$/, '');
    if (rawToken.endsWith('.')) rawToken = rawToken.slice(0, -1);
    if (!rawToken.endsWith('.prompt.md')) continue;
    if (tail && !HEADER_TAIL_OK_RE.test(tail)) continue;
    if (!isCanonicalRepoPath(rawToken)) continue;
    const promptPath = normalizePath(rawToken);
    const key = promptPath.toLowerCase();
    if (promptPath && !seen.has(key)) {
      seen.add(key);
      refs.push(promptPath);
    }
  }
  return refs;
}

function extractOpeningSentenceClaims(promptPath, rawPrompt, bodyOffset = 0) {
  const raw = String(rawPrompt ?? '').slice(bodyOffset, bodyOffset + 65536);
  const lines = raw.split(/\r?\n/);
  let at = 0;
  const skipBlanks = () => { while (at < lines.length && !lines[at].trim()) at += 1; };
  skipBlanks();
  if (/^# /.test(lines[at] ?? '')) { at += 1; skipBlanks(); }
  const stopLine = (line) => !line.trim() || /^[ \t]*#/.test(line) || /^[ \t]*(?:```|~~~)/.test(line);
  const paraLines = [];
  while (at < lines.length && !stopLine(lines[at])) {
    paraLines.push(lines[at].trim());
    at += 1;
  }
  if (!paraLines.length) return [];
  const joined = paraLines.join(' ');
  let inTicks = false;
  let sentenceEnd = joined.length;
  for (let i = 0; i < joined.length; i += 1) {
    const ch = joined[i];
    if (ch === '`') { inTicks = !inTicks; continue; }
    if (!inTicks && (ch === '.' || ch === '!' || ch === '?') && (i + 1 === joined.length || /\s/.test(joined[i + 1]))) {
      sentenceEnd = i + 1;
      break;
    }
  }
  let sentence = joined.slice(0, sentenceEnd);
  const normPrompt = normalizePath(promptPath);
  const lastSlash = normPrompt.lastIndexOf('/');
  const folder = lastSlash > 0 ? normPrompt.slice(0, lastSlash) : '';
  const resolveNear = (target) => normalizePath(folder ? `${folder}/${target}` : target);
  const claims = new Set();

  sentence = sentence.replace(/\]\(([^)\s]+)\)/g, (_, target) => {
    const file = target.split('#')[0];
    if (file && !/^[a-z][a-z0-9+.-]*:/i.test(file)) {
      const resolved = resolveNear(file);
      if (isCanonicalRepoPath(resolved) && !resolved.endsWith('.prompt.md')) claims.add(resolved);
    }
    return ']';
  });

  for (const match of sentence.matchAll(/[A-Za-z0-9_@+~./-]+/g)) {
    const run = match[0].replace(/\.+$/, '');
    if (!run || (!run.includes('/') && !run.includes('.'))) continue;
    const resolved = /^\.\.?\//.test(run) ? resolveNear(run) : normalizePath(run);
    if (isCanonicalRepoPath(resolved) && !resolved.endsWith('.prompt.md')) {
      claims.add(resolved);
    }
  }
  return [...claims].sort();
}

/**
 * Resolve which changed production modules are owned by `kind: native-only` prompts
 * via `pdd-bindings.json`, `Generated from` / `Prompt:` headers, or opening-sentence prose claims.
 */
export function detectNativeOnlyModules({
  changedFiles = [],
  promptFiles = [],
  bindings = null,
  fileHeads = [],
} = {}) {
  const nativePromptsByKey = new Map(); // lowerPath -> { path, reason, claims }
  const rawPrompts = Array.isArray(promptFiles)
    ? promptFiles
    : (promptFiles && typeof promptFiles === 'object'
      ? Object.entries(promptFiles).map(([path, content]) => ({ path, content }))
      : []);
  for (const item of rawPrompts) {
    if (!item || typeof item !== 'object') continue;
    const p = normalizePath(item.path);
    if (!p || !p.endsWith('.prompt.md')) continue;
    const meta = parseNativeOnlyPromptMeta(item.content);
    if (!meta?.nativeOnly) continue;
    nativePromptsByKey.set(p.toLowerCase(), {
      path: p,
      reason: meta.reason,
      claims: new Set(extractOpeningSentenceClaims(p, item.content, meta.bodyOffset).map((c) => c.toLowerCase())),
    });
  }

  const bindingMap = new Map(); // lowerModulePath -> promptEntry
  if (bindings) {
    let parsed = null;
    if (typeof bindings === 'string') {
      try { parsed = JSON.parse(bindings); } catch { parsed = null; }
    } else if (typeof bindings === 'object') {
      parsed = bindings;
    }
    if (parsed && Array.isArray(parsed.modules)) {
      for (const entry of parsed.modules) {
        if (!entry || typeof entry !== 'object') continue;
        const mod = normalizePath(entry.module).toLowerCase();
        const prmKey = normalizePath(entry.prompt).toLowerCase();
        if (mod && prmKey && nativePromptsByKey.has(prmKey)) {
          bindingMap.set(mod, nativePromptsByKey.get(prmKey));
        }
      }
    }
  }

  const headMap = new Map(); // lowerModulePath -> headContent
  if (Array.isArray(fileHeads)) {
    for (const entry of fileHeads) {
      if (!entry || typeof entry !== 'object') continue;
      const p = normalizePath(entry.path).toLowerCase();
      if (p && typeof entry.content === 'string') headMap.set(p, entry.content);
    }
  } else if (fileHeads instanceof Map) {
    for (const [k, v] of fileHeads.entries()) {
      const p = normalizePath(k).toLowerCase();
      if (p && typeof v === 'string') headMap.set(p, v);
    }
  } else if (fileHeads && typeof fileHeads === 'object') {
    for (const [k, v] of Object.entries(fileHeads)) {
      const p = normalizePath(k).toLowerCase();
      if (p && typeof v === 'string') headMap.set(p, v);
    }
  }

  const proseClaimsByModule = new Map(); // lowerModulePath -> promptEntry
  for (const entry of nativePromptsByKey.values()) {
    for (const claimKey of entry.claims) {
      if (!proseClaimsByModule.has(claimKey)) proseClaimsByModule.set(claimKey, entry);
    }
  }

  const matches = [];
  const moduleSet = new Set();
  const changedList = Array.isArray(changedFiles) ? [...new Set(changedFiles.map(normalizePath).filter(Boolean))].sort() : [];
  for (const file of changedList) {
    const lower = file.toLowerCase();
    if (isDocPath(lower) || NON_PRODUCTION_DIR_RE.test(lower)) continue;
    let promptEntry = null;
    let source = null;
    if (bindingMap.has(lower)) {
      promptEntry = bindingMap.get(lower);
      source = 'binding';
    } else if (headMap.has(lower)) {
      const refs = extractHeaderPromptRefs(headMap.get(lower));
      const matchedKey = refs.map((r) => r.toLowerCase()).find((k) => nativePromptsByKey.has(k));
      if (matchedKey) {
        promptEntry = nativePromptsByKey.get(matchedKey);
        source = 'header';
      }
    }
    if (!promptEntry && proseClaimsByModule.has(lower)) {
      promptEntry = proseClaimsByModule.get(lower);
      source = 'prose';
    }
    if (promptEntry) {
      moduleSet.add(file);
      matches.push({
        module: file,
        prompt: promptEntry.path,
        source,
        reason: promptEntry.reason,
      });
    }
  }

  return {
    nativeOnlyPrompts: [...nativePromptsByKey.values()].map((e) => e.path).sort(),
    nativeOnlyModules: [...moduleSet].sort(),
    matches,
  };
}

/**
 * Extract production boundary targets and surfaces referenced by a test file (via imports or direct path references).
 */
export function inspectTestBoundaryTargets(testPath, text, { nativeOnlyTargets } = {}) {
  const normTest = normalizePath(testPath);
  const code = stripCommentsPreserveLines(text);
  const targetSet = new Set();
  const boundaryTargetSet = new Set();
  const surfaceSet = new Set();
  const nativeTargetSet = nativeOnlyTargets instanceof Set
    ? nativeOnlyTargets
    : new Set(Array.isArray(nativeOnlyTargets) ? nativeOnlyTargets.map(canonicalTargetPath).filter(Boolean) : []);

  const consider = (rawTarget) => {
    const resolved = resolveRelativeTarget(normTest, rawTarget);
    if (!resolved || NON_PRODUCTION_DIR_RE.test(resolved.toLowerCase())) return;
    const surfaces = classifyProductionPathSurfaces(resolved);
    if (!surfaces.length) return;
    const canonical = canonicalTargetPath(resolved);
    if (!canonical) return;
    targetSet.add(canonical);
    const boundary = surfaces.filter((s) => s !== 'docs' && s !== 'runtime-code');
    if (nativeTargetSet.has(canonical)) boundary.push('native-only');
    if (boundary.length) {
      boundaryTargetSet.add(canonical);
      for (const s of boundary) surfaceSet.add(s);
    }
  };

  for (const match of code.matchAll(BOUNDARY_IMPORT_RE)) {
    const spec = match[1];
    if (spec.startsWith('.') || /^(?:bin|cli|cmd|scripts|api|server|routes|handlers|controllers|db|database|migrations|prisma|sql|web|ui|frontend|pages|components|views|app|os|sandbox|tty|pty|subprocess|src)\//i.test(spec)) {
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

function parseSimpleByteExpr(rawExpr) {
  const clean = String(rawExpr ?? '').replace(/_/g, '').trim();
  if (!clean || clean.length > 40 || !/^[0-9\s*+]+$/.test(clean)) return null;
  let total = 0;
  for (const addPart of clean.split('+')) {
    const factors = addPart.split('*').map((s) => s.trim());
    if (!factors.length || factors.some((f) => !/^\d+$/.test(f))) return null;
    let prod = 1;
    for (const f of factors) {
      prod *= Number(f);
      if (!Number.isSafeInteger(prod)) return null;
    }
    total += prod;
    if (!Number.isSafeInteger(total)) return null;
  }
  return total;
}

function detectMaxPayloadBytes(codeNoStrings, { maxInlineStringBytes = 0, repeatLiteralUnits = null } = {}) {
  const text = String(codeNoStrings ?? '');
  let maxBytes = maxInlineStringBytes > 0 ? maxInlineStringBytes : null;
  const record = (n) => {
    if (Number.isInteger(n) && n > 0 && (maxBytes === null || n > maxBytes)) maxBytes = n;
  };

  for (const m of text.matchAll(/"\s*\.\s*repeat\s*\(([0-9_*\s+]{1,40})\)/g)) {
    const count = parseSimpleByteExpr(m[1]);
    const unitLen = repeatLiteralUnits instanceof Map ? (repeatLiteralUnits.get(m.index) ?? 1) : 1;
    if (count !== null) record(unitLen * count);
  }
  for (const m of text.matchAll(/\.\s*repeat\s*\(([0-9_*\s+]{1,40})\)/g)) {
    let prev = (m.index ?? 0) - 1;
    while (prev >= 0 && (text[prev] === ' ' || text[prev] === '\t' || text[prev] === '\r' || text[prev] === '\n')) prev -= 1;
    if (prev >= 0 && text[prev] === '"') continue;
    const count = parseSimpleByteExpr(m[1]);
    if (count !== null) record(count);
  }
  for (const m of text.matchAll(/\b(?:Buffer\s*\.\s*alloc(?:Unsafe)?|new\s+(?:Uint8Array|Array|Buffer))\s*\(([0-9_*\s+]{1,40})\)/g)) {
    const size = parseSimpleByteExpr(m[1]);
    if (size !== null) record(size);
  }

  return maxBytes;
}

/**
 * Extract the balanced argument slice strictly inside `(...)` starting at `openParenIdx`,
 * stopping at the matching closing `)` (or `maxLen` chars). Quote-aware and strictly O(maxLen).
 */
function extractCallArgsSlice(text, openParenIdx, maxLen = 240) {
  if (typeof text !== 'string' || openParenIdx < 0 || text[openParenIdx] !== '(') {
    return { slice: '', startIdx: openParenIdx + 1, endIdx: openParenIdx + 1, closed: false };
  }
  const startIdx = openParenIdx + 1;
  const limit = Math.min(text.length, startIdx + maxLen);
  let depth = 1;
  let quote = '';
  let i = startIdx;
  while (i < limit) {
    const ch = text[i];
    if (quote) {
      if (ch === '\\' && i + 1 < limit) {
        i += 2;
        continue;
      }
      if (ch === quote) quote = '';
      i += 1;
      continue;
    }
    if (ch === '"' || ch === '\'' || ch === '`') {
      quote = ch;
      i += 1;
      continue;
    }
    if (ch === '(') {
      depth += 1;
    } else if (ch === ')') {
      depth -= 1;
      if (depth === 0) {
        return { slice: text.slice(startIdx, i), startIdx, endIdx: i, closed: true };
      }
    }
    i += 1;
  }
  return { slice: text.slice(startIdx, limit), startIdx, endIdx: limit, closed: false };
}

function collectLiteralsInMaskedSlice(slice, sliceStartIdx, stringLiteralsByOpenPos) {
  const literals = [];
  if (!(stringLiteralsByOpenPos instanceof Map) || !slice) return literals;
  let k = 0;
  while (k < slice.length) {
    if (slice[k] === '"') {
      const openIdx = sliceStartIdx + k;
      const lit = stringLiteralsByOpenPos.get(openIdx);
      if (lit !== undefined) literals.push({ value: lit, sliceStart: k });
      k += 1;
      while (k < slice.length && slice[k] !== '"') k += 1;
      if (k < slice.length) k += 1;
      continue;
    }
    k += 1;
  }
  return literals;
}

function splitLinesWithOffsets(text) {
  const out = [];
  let start = 0;
  while (start <= text.length) {
    const nl = text.indexOf('\n', start);
    if (nl < 0) {
      const line = text.endsWith('\r') && start < text.length ? text.slice(start, -1) : text.slice(start);
      out.push({ line, offset: start });
      break;
    }
    const end = nl > start && text[nl - 1] === '\r' ? nl - 1 : nl;
    out.push({ line: text.slice(start, end), offset: start });
    start = nl + 1;
  }
  return out;
}

function isSameLineLoopEnclosing(maskedLine, targetIdx) {
  for (const m of maskedLine.matchAll(LOOP_START_ALL_RE)) {
    const openParenIdx = (m.index ?? 0) + m[0].length - 1;
    if (openParenIdx >= targetIdx) break;
    const isMethodLoop = Boolean(m[2]); // .forEach( or .map(
    let parenDepth = 1;
    let braceDepth = 0;
    let headerClosedAt = -1;
    let bodyHasBlock = false;
    let sawBodyToken = false;
    let bodyClosed = false;
    let nestedDepth = 0;
    for (let k = openParenIdx + 1; k < targetIdx; k += 1) {
      const ch = maskedLine[k];
      if (isMethodLoop) {
        if (ch === '(') parenDepth += 1;
        else if (ch === ')') {
          parenDepth -= 1;
          if (parenDepth === 0) {
            bodyClosed = true;
            break;
          }
        }
        continue;
      }
      if (headerClosedAt < 0) {
        if (ch === '(') parenDepth += 1;
        else if (ch === ')') {
          parenDepth -= 1;
          if (parenDepth === 0) headerClosedAt = k;
        }
        continue;
      }
      if (!bodyHasBlock && !sawBodyToken) {
        if (ch === ' ' || ch === '\t') continue;
        if (ch === '{') {
          bodyHasBlock = true;
          braceDepth = 1;
          continue;
        }
        if (ch === ';') {
          bodyClosed = true;
          break;
        }
        sawBodyToken = true;
        if (ch === '(' || ch === '[') nestedDepth += 1;
        continue;
      }
      if (bodyHasBlock) {
        if (ch === '{') braceDepth += 1;
        else if (ch === '}') {
          braceDepth -= 1;
          if (braceDepth === 0) {
            bodyClosed = true;
            break;
          }
        }
      } else {
        if (ch === '(' || ch === '{' || ch === '[') nestedDepth += 1;
        else if (ch === ')' || ch === '}' || ch === ']') nestedDepth = Math.max(0, nestedDepth - 1);
        else if (ch === ';' && nestedDepth === 0) {
          bodyClosed = true;
          break;
        }
      }
    }
    if (isMethodLoop) {
      if (!bodyClosed && parenDepth > 0) return true;
    } else if (headerClosedAt >= 0 && !bodyClosed) {
      if (bodyHasBlock ? braceDepth > 0 : true) return true;
    }
  }
  return false;
}

function classifyImportedModule(spec) {
  const s = String(spec ?? '').trim().toLowerCase();
  if (!s) return null;
  if (s === 'child_process' || s === 'node:child_process') return 'child_process';
  if (s === 'fs' || s === 'node:fs' || s === 'fs/promises' || s === 'node:fs/promises') return 'fs';
  if (s === 'http' || s === 'node:http' || s === 'https' || s === 'node:https' || s === 'http2' || s === 'node:http2' || s === 'net' || s === 'node:net' || s === 'supertest' || s === 'express' || s === 'fastify' || s === 'koa' || s === 'hono') return 'http';
  if (s === 'tty' || s === 'node:tty' || s === 'node-pty') return 'tty';
  if (/^(?:node:sqlite|pg|mysql2?|better-sqlite3|sqlite3?|mongodb|redis|ioredis|@prisma\/client)$/.test(s)) return 'db';
  if (/^(?:@playwright\/test|playwright(?:-core|-chromium|-firefox|-webkit)?|puppeteer(?:-core)?)$/.test(s)) return 'browser';
  if (/^(?:@google-cloud\/.+|@aws-sdk\/.+|aws-sdk|stripe|dockerode|@kubernetes\/client-node|@octokit\/.+|googleapis)$/.test(s)) return 'external-sdk';
  return null;
}

function extractBindingNamesFromClause(clause) {
  const namespaces = [];
  const named = new Map(); // localName -> originalName
  const trimmed = String(clause ?? '').trim();
  if (!trimmed) return { namespaces, named };

  const nsMatch = /\*\s+as\s+([A-Za-z_$][A-Za-z0-9_$]*)/.exec(trimmed);
  if (nsMatch) namespaces.push(nsMatch[1]);

  const braceStart = trimmed.indexOf('{');
  const braceEnd = trimmed.lastIndexOf('}');
  if (braceStart >= 0 && braceEnd > braceStart) {
    const before = trimmed.slice(0, braceStart).replace(/,\s*$/, '').trim();
    if (before && /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(before)) namespaces.push(before);
    for (const part of trimmed.slice(braceStart + 1, braceEnd).split(',')) {
      const piece = part.trim();
      if (!piece) continue;
      const alias = /^([A-Za-z_$][A-Za-z0-9_$]*)(?:\s+as\s+|\s*:\s*)([A-Za-z_$][A-Za-z0-9_$]*)$/.exec(piece);
      if (alias) named.set(alias[2], alias[1]);
      else if (/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(piece)) named.set(piece, piece);
    }
  } else if (!nsMatch && /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(trimmed)) {
    namespaces.push(trimmed);
  }
  return { namespaces, named };
}

function splitTopLevelDeclarators(listText) {
  const out = [];
  let start = 0;
  let depth = 0;
  for (let idx = 0; idx < listText.length; idx += 1) {
    const ch = listText[idx];
    if (ch === '(' || ch === '{' || ch === '[') depth += 1;
    else if (ch === ')' || ch === '}' || ch === ']') depth = Math.max(0, depth - 1);
    else if (ch === ',' && depth === 0) {
      out.push(listText.slice(start, idx));
      start = idx + 1;
    }
  }
  out.push(listText.slice(start));
  return out;
}

const MODULE_MOCK_CALL_RE = /\b(?:(?:vi|jest)\.(?:mock|doMock)|mock\.module)[ \t]*\(\s*("")/g;
const ESM_IMPORT_RE = /(?<!\.)\bimport\s+([A-Za-z_$*{][A-Za-z0-9_$,*{}\s]{0,1000})\bfrom\s*("")/g;
const CJS_REQUIRE_RE = /\b(?:const|let|var)[ \t]+([A-Za-z_${][A-Za-z0-9_$,:{}\s]{0,300})=[ \t]*require[ \t]*\(\s*("")\s*\)(?:\s*\.\s*([A-Za-z_$][A-Za-z0-9_$]*))?/g;
const SHADOW_VAR_RE = /\b(?:const|let|var)[ \t]+(spawn|spawnSync|execFile|execFileSync|execSync|createServer|fetch|DatabaseSync|openSync|open|statSync|stat|fstatSync|fstat|lstatSync|lstat|accessSync|access|createReadStream|createWriteStream|isatty|ReadStream|WriteStream)[ \t]*=/g;
const SHADOW_UNINIT_DECL_RE = /\b(?:let|var)[ \t]+([^;\n]{1,300})/g;
const SHADOW_DESTRUCTURE_RE = /\b(?:const|let|var)[ \t]*\{([^}\r\n]{1,200})\}[ \t]*=([^;\n]{0,200})/g;
const SHADOW_FN_RE = /\bfunction[ \t]+(spawn|spawnSync|execFile|execFileSync|execSync|createServer|fetch|DatabaseSync|openSync|open|statSync|stat|fstatSync|fstat|lstatSync|lstat|accessSync|access|createReadStream|createWriteStream|isatty|ReadStream|WriteStream)[ \t]*\(/g;
const SHADOW_CLASS_RE = /\bclass[ \t]+(DatabaseSync|ReadStream|WriteStream)\b/g;
const SHADOW_GLOBAL_FETCH_ASSIGN_RE = /\b(?:globalThis|global|window|self)[ \t]*\.[ \t]*fetch[ \t]*=(?!=)|(?<![.\w$])fetch[ \t]*=(?!=)/;
const STUB_GLOBAL_CALL_RE = /\bvi\.stubGlobal[ \t]*\(\s*("")/g;
const DEFINE_PROP_GLOBAL_RE = /\bObject\.defineProperty[ \t]*\(\s*(?:globalThis|global|window|self)\s*,\s*("")/g;
const METHOD_STUB_RE = /\b(?:mock\.method|vi\.spyOn|jest\.spyOn|sinon\.stub)[ \t]*\(\s*([^,\n)]{1,120}),\s*("")/g;
const BROWSER_ORIGIN_RHS_RE = /\b([A-Za-z_$][A-Za-z0-9_$]*)[ \t]*\.[ \t]*(?:launch|launchPersistentContext|newPage|newContext|connect|connectOverCDP|pages)[ \t]*\(/;
const LOCAL_VAR_DECL_RE = /\b(?:const|let|var)[ \t]+([A-Za-z_$][A-Za-z0-9_$]*)(?:[ \t]*=([^;\n]{1,200})|[ \t]*(?:;|,|$))/g;
const BROWSER_WELL_KNOWN_VARS = new Set(['page', 'browser', 'context', 'chromium', 'firefox', 'webkit']);
const PRIMITIVE_SHADOW_NAMES = new Set([
  'spawn', 'spawnSync', 'execFile', 'execFileSync', 'execSync',
  'createServer', 'fetch', 'DatabaseSync',
  'openSync', 'open', 'statSync', 'stat', 'fstatSync', 'fstat',
  'lstatSync', 'lstat', 'accessSync', 'access', 'createReadStream', 'createWriteStream',
  'isatty', 'ReadStream', 'WriteStream',
]);
const METHOD_STUB_NAMES = new Set([
  ...PRIMITIVE_SHADOW_NAMES,
  'request', 'listen', 'launch', 'goto', 'newPage', 'newContext', 'connect',
]);

function analyzePrimitiveAuthenticity(codeNoStrings, stringLiteralsByOpenPos) {
  const litAtMatch = (m) => {
    if (!(stringLiteralsByOpenPos instanceof Map)) return '';
    const rel = m[0].lastIndexOf('""');
    if (rel < 0) return '';
    return stringLiteralsByOpenPos.get((m.index ?? 0) + rel) ?? '';
  };

  const mockedModules = new Set();
  for (const m of codeNoStrings.matchAll(MODULE_MOCK_CALL_RE)) {
    const cat = classifyImportedModule(litAtMatch(m));
    if (cat) mockedModules.add(cat);
  }

  const importedModules = new Set();
  const namespaceBindings = new Map(); // category -> Set<ident>
  const namedBindings = new Map(); // category -> Map<localIdent, origIdent>
  const shadowedPrimitives = new Set();
  let hasNodePtyImport = false;
  let hasNonSqliteDbImport = false;
  const addImport = (spec, clause, propAccess = '') => {
    const trimmedClause = String(clause ?? '').trim();
    if (!trimmedClause || /^type\s+/.test(trimmedClause)) return;
    const { namespaces, named } = extractBindingNamesFromClause(trimmedClause);
    if (propAccess && namespaces.length === 1 && named.size === 0) {
      named.set(namespaces[0], propAccess);
      namespaces.length = 0;
    }
    const lowerSpec = String(spec ?? '').trim().toLowerCase();
    // Mark `fetch` shadowed whenever an import/require binds local identifier `fetch` from any non-native module.
    if ((namespaces.includes('fetch') || named.has('fetch')) && !lowerSpec.startsWith('node:')) {
      shadowedPrimitives.add('fetch');
    }
    const cat = classifyImportedModule(spec);
    if (!cat || mockedModules.has(cat)) return;
    if (lowerSpec === 'node-pty') hasNodePtyImport = true;
    if (cat === 'db' && lowerSpec !== 'node:sqlite') hasNonSqliteDbImport = true;
    importedModules.add(cat);
    let nsSet = namespaceBindings.get(cat);
    if (!nsSet) { nsSet = new Set(); namespaceBindings.set(cat, nsSet); }
    for (const n of namespaces) nsSet.add(n);
    let namedMap = namedBindings.get(cat);
    if (!namedMap) { namedMap = new Map(); namedBindings.set(cat, namedMap); }
    for (const [local, orig] of named.entries()) namedMap.set(local, orig);
  };

  for (const m of codeNoStrings.matchAll(ESM_IMPORT_RE)) addImport(litAtMatch(m), m[1]);
  for (const m of codeNoStrings.matchAll(CJS_REQUIRE_RE)) addImport(litAtMatch(m), m[1], m[3] ?? '');

  const shadowedBrowserVars = new Set();
  const isCleanBrowserRhs = (rhs) => {
    const trimmed = String(rhs ?? '').trim();
    if (!trimmed || trimmed.startsWith('{') || /\b(?:fake|mock|stub)/i.test(trimmed)) return false;
    const origin = BROWSER_ORIGIN_RHS_RE.exec(trimmed);
    if (!origin) return false;
    const originReceiver = origin[1];
    if (/^(?:fake|mock|stub)/i.test(originReceiver) || shadowedBrowserVars.has(originReceiver)) return false;
    return true;
  };

  const maskedLines = codeNoStrings.split(/\r?\n/);
  for (const line of maskedLines) {
    if (!/\brequire\s*\(/.test(line)) {
      for (const m of line.matchAll(SHADOW_VAR_RE)) shadowedPrimitives.add(m[1]);
      for (const m of line.matchAll(SHADOW_UNINIT_DECL_RE)) {
        for (const decl of splitTopLevelDeclarators(m[1])) {
          const piece = decl.trim();
          const idMatch = /^([A-Za-z_$][A-Za-z0-9_$]*)\b/.exec(piece);
          if (idMatch && PRIMITIVE_SHADOW_NAMES.has(idMatch[1])) shadowedPrimitives.add(idMatch[1]);
          if (idMatch && !piece.includes('=')) shadowedBrowserVars.add(idMatch[1]);
        }
      }
      for (const m of line.matchAll(SHADOW_DESTRUCTURE_RE)) {
        const rhsCleanBrowser = isCleanBrowserRhs(m[2]);
        for (const part of m[1].split(',')) {
          const piece = part.trim();
          const alias = /^[A-Za-z_$][A-Za-z0-9_$]*\s*:\s*([A-Za-z_$][A-Za-z0-9_$]*)/.exec(piece);
          const local = alias ? alias[1] : piece.split('=')[0].trim();
          if (PRIMITIVE_SHADOW_NAMES.has(local)) shadowedPrimitives.add(local);
          if (!rhsCleanBrowser && BROWSER_WELL_KNOWN_VARS.has(local)) shadowedBrowserVars.add(local);
        }
      }
      for (const m of line.matchAll(LOCAL_VAR_DECL_RE)) {
        const ident = m[1];
        const rhs = m[2] ?? '';
        if (!isCleanBrowserRhs(rhs)) shadowedBrowserVars.add(ident);
      }
    }
    for (const m of line.matchAll(SHADOW_FN_RE)) shadowedPrimitives.add(m[1]);
    for (const m of line.matchAll(SHADOW_CLASS_RE)) shadowedPrimitives.add(m[1]);
    for (const m of line.matchAll(/\bfunction[ \t]+(page|browser|context|chromium|firefox|webkit)[ \t]*\(/g)) {
      shadowedBrowserVars.add(m[1]);
    }
  }
  if (SHADOW_GLOBAL_FETCH_ASSIGN_RE.test(codeNoStrings)) shadowedPrimitives.add('fetch');
  for (const m of codeNoStrings.matchAll(STUB_GLOBAL_CALL_RE)) {
    const target = litAtMatch(m);
    if (target === 'fetch' || PRIMITIVE_SHADOW_NAMES.has(target)) shadowedPrimitives.add(target);
  }
  for (const m of codeNoStrings.matchAll(DEFINE_PROP_GLOBAL_RE)) {
    const target = litAtMatch(m);
    if (target === 'fetch' || PRIMITIVE_SHADOW_NAMES.has(target)) shadowedPrimitives.add(target);
  }
  for (const m of codeNoStrings.matchAll(METHOD_STUB_RE)) {
    const target = litAtMatch(m);
    if (METHOD_STUB_NAMES.has(target)) shadowedPrimitives.add(target);
  }

  return {
    mockedModules,
    importedModules,
    namespaceBindings,
    namedBindings,
    shadowedPrimitives,
    shadowedBrowserVars,
    hasNodePtyImport,
    hasNonSqliteDbImport,
  };
}

function isAuthenticCategoryCall(auth, category, fnName, rawReceiver) {
  if (auth.mockedModules.has(category)) return false;
  if (auth.shadowedPrimitives.has(fnName)) return false;
  if (!auth.importedModules.has(category)) return false;
  const receiver = rawReceiver ? rawReceiver.replace(/\.$/, '').trim() : '';
  if (receiver) {
    return auth.namespaceBindings.get(category)?.has(receiver) === true;
  }
  const namedMap = auth.namedBindings.get(category);
  return Boolean(namedMap && namedMap.has(fnName));
}

const HELPER_DEF_RE = /\b(?:function\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*\(|(?:const|let|var)\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*(?:async\s+)?(?:\([^)]*\)|[A-Za-z_$][A-Za-z0-9_$]*)\s*=>)/;

/**
 * Single linear O(N) token scan counting non-declaration calls for all helperNames at once.
 */
function countHelperCallsBatch(codeNoStrings, helperNames) {
  const counts = new Map();
  if (!helperNames.size) return counts;
  const text = String(codeNoStrings ?? '');
  let i = 0;
  let prevWord = '';
  let prevNonSpace = '';
  while (i < text.length) {
    const ch = text[i];
    if (/[A-Za-z_$]/.test(ch)) {
      let j = i + 1;
      while (j < text.length && /[A-Za-z0-9_$]/.test(text[j])) j += 1;
      const word = text.slice(i, j);
      if (helperNames.has(word) && prevNonSpace !== '.' && prevWord !== 'function') {
        let k = j;
        while (k < text.length && (text[k] === ' ' || text[k] === '\t')) k += 1;
        if (text[k] === '(') {
          counts.set(word, (counts.get(word) ?? 0) + 1);
        }
      }
      prevWord = word;
      prevNonSpace = word[word.length - 1];
      i = j;
      continue;
    }
    if (!/\s/.test(ch)) {
      prevNonSpace = ch;
      if (ch !== '(' && ch !== ')' && ch !== ',') prevWord = '';
    }
    i += 1;
  }
  return counts;
}

function analyzeSubprocessCalls(codeNoStrings, auth, stringLiteralsByOpenPos) {
  let hasRealSubprocess = false;
  let hasExternalToolSubprocess = false;
  let hasLiveLocalSubprocess = false;
  let hasSandboxSubprocess = false;
  let subprocessCallCount = 0;
  let hasLoopedSubprocess = false;
  if (!SUBPROCESS_EXEC_RE.test(codeNoStrings) || auth.mockedModules.has('child_process') || !auth.importedModules.has('child_process')) {
    return {
      hasRealSubprocess,
      hasExternalToolSubprocess,
      hasLiveLocalSubprocess,
      hasSandboxSubprocess,
      subprocessCallCount,
      hasLoopedSubprocess,
    };
  }
  const maskedLineEntries = splitLinesWithOffsets(codeNoStrings);
  const helperNames = new Set();
  const scopeStack = []; // { kind: 'fn' | 'loop', name: string | null, depth: number }
  let braceDepth = 0;

  for (let i = 0; i < maskedLineEntries.length; i += 1) {
    const { line: maskedLine, offset: lineOffset } = maskedLineEntries[i];
    const lineStartDepth = braceDepth;

    // Pop scopes closed before this line's body if line starts with '}'
    let leadingCloses = 0;
    let scanIdx = 0;
    while (scanIdx < maskedLine.length && (maskedLine[scanIdx] === ' ' || maskedLine[scanIdx] === '\t')) scanIdx += 1;
    while (scanIdx < maskedLine.length && maskedLine[scanIdx] === '}') {
      leadingCloses += 1;
      scanIdx += 1;
    }
    let effectiveDepth = Math.max(0, lineStartDepth - leadingCloses);
    while (scopeStack.length && scopeStack[scopeStack.length - 1].depth > effectiveDepth) scopeStack.pop();

    const defMatch = HELPER_DEF_RE.exec(maskedLine);
    const defName = defMatch?.[1] ?? defMatch?.[2] ?? null;
    const isHelperDef = Boolean(defName && defName !== 'test' && defName !== 'it' && defName !== 'describe');

    if (SUBPROCESS_EXEC_RE.test(maskedLine)) {
      const firstSubIdx = maskedLine.search(SUBPROCESS_EXEC_RE);
      const sameLineHelper = isHelperDef && defMatch.index < firstSubIdx ? defName : null;
      const inOuterLoop = scopeStack.some((s) => s.kind === 'loop');
      let matchedNonTrivial = false;

      for (const match of maskedLine.matchAll(SUBPROCESS_CALL_START_RE)) {
        const receiver = match[1] ?? '';
        const fnName = match[2];
        if (!isAuthenticCategoryCall(auth, 'child_process', fnName, receiver)) continue;
        const callCol = match.index ?? 0;
        const openParenIdx = lineOffset + callCol + match[0].length - 1;
        const { slice, startIdx } = extractCallArgsSlice(codeNoStrings, openParenIdx, 240);
        const trimmedSlice = slice.trim();
        if (!trimmedSlice) continue;

        const argLiterals = collectLiteralsInMaskedSlice(slice, startIdx, stringLiteralsByOpenPos);
        const combinedArgs = argLiterals.length > 0
          ? `${slice} ${argLiterals.map((item) => item.value).join(' ')}`
          : slice;
        const inLoop = inOuterLoop || isSameLineLoopEnclosing(maskedLine, callCol);

        const leadingLiteral = trimmedSlice[0] === '"'
          && argLiterals.length > 0
          && slice.slice(0, argLiterals[0].sliceStart).trim() === ''
          ? argLiterals[0]
          : null;
        if (leadingLiteral) {
          const closePos = trimmedSlice.indexOf('"', 1);
          const afterFirst = closePos >= 0 ? trimmedSlice.slice(closePos + 1).trimStart() : '';
          const rawCmd = leadingLiteral.value.trim();
          if (!rawCmd) {
            if (!afterFirst.startsWith('+')) continue;
          } else {
            const firstWord = rawCmd.split(/\s+/)[0] ?? '';
            const baseBin = firstWord.split(/[\\/]/).pop() ?? '';
            if (!baseBin || TRIVIAL_SUBPROCESS_BIN_RE.test(baseBin)) continue;
            hasRealSubprocess = true;
            matchedNonTrivial = true;
            subprocessCallCount += 1;
            if (inLoop) hasLoopedSubprocess = true;
            if (/--live-local\b/i.test(combinedArgs)) hasLiveLocalSubprocess = true;
            if (SANDBOX_EXEC_RE.test(rawCmd) || SANDBOX_EXEC_RE.test(combinedArgs)) hasSandboxSubprocess = true;
            const isShellOrRuntime = /^(?:sh|bash|zsh|dash|fish|cmd|cmd\.exe|powershell|pwsh|node|nodejs|python|python3|ruby|deno|bun|tsx|ts-node)$/i.test(baseBin);
            if (EXTERNAL_TOOL_EXEC_RE.test(rawCmd) || (isShellOrRuntime && EXTERNAL_TOOL_EXEC_RE.test(combinedArgs))) {
              hasExternalToolSubprocess = true;
            }
            continue;
          }
        }

        hasRealSubprocess = true;
        matchedNonTrivial = true;
        subprocessCallCount += 1;
        if (inLoop) hasLoopedSubprocess = true;
        if (/--live-local\b/i.test(combinedArgs)) hasLiveLocalSubprocess = true;
        if (SANDBOX_EXEC_RE.test(combinedArgs)) hasSandboxSubprocess = true;
        if (EXTERNAL_TOOL_EXEC_RE.test(combinedArgs)) {
          hasExternalToolSubprocess = true;
        }
      }
      if (matchedNonTrivial) {
        if (sameLineHelper) {
          helperNames.add(sameLineHelper);
        } else {
          for (let s = scopeStack.length - 1; s >= 0; s -= 1) {
            if (scopeStack[s].kind === 'fn' && scopeStack[s].name) {
              helperNames.add(scopeStack[s].name);
              break;
            }
          }
        }
      }
    }

    // Update brace depth across the line and push multi-line scopes that remain open at end of line.
    let netDelta = 0;
    let openedDepth = null;
    for (let k = 0; k < maskedLine.length; k += 1) {
      if (maskedLine[k] === '{') {
        braceDepth += 1;
        netDelta += 1;
        if (openedDepth === null) openedDepth = braceDepth;
      } else if (maskedLine[k] === '}') {
        braceDepth = Math.max(0, braceDepth - 1);
        netDelta -= 1;
      }
    }
    while (scopeStack.length && scopeStack[scopeStack.length - 1].depth > braceDepth) scopeStack.pop();
    const openLoopAtEol = isSameLineLoopEnclosing(maskedLine, maskedLine.length);
    if (openedDepth !== null && braceDepth >= openedDepth) {
      if (openLoopAtEol) scopeStack.push({ kind: 'loop', name: null, depth: openedDepth });
      else if (isHelperDef) scopeStack.push({ kind: 'fn', name: defName, depth: openedDepth });
    } else if (netDelta > 0 && isHelperDef) {
      scopeStack.push({ kind: 'fn', name: defName, depth: braceDepth });
    }
  }

  if (helperNames.size > 0) {
    const counts = countHelperCallsBatch(codeNoStrings, helperNames);
    for (const calls of counts.values()) {
      if (calls > subprocessCallCount) subprocessCallCount = calls;
    }
  }
  return {
    hasRealSubprocess,
    hasExternalToolSubprocess,
    hasLiveLocalSubprocess,
    hasSandboxSubprocess,
    subprocessCallCount,
    hasLoopedSubprocess,
  };
}

function detectRealDeviceOrTtyProbe(codeNoStrings, auth, stringLiteralsByOpenPos) {
  if (!auth.mockedModules.has('tty') && auth.importedModules.has('tty')) {
    for (const m of codeNoStrings.matchAll(/\bnew[ \t]+([A-Za-z_$][A-Za-z0-9_$]*[ \t]*\.[ \t]*)?(ReadStream|WriteStream)[ \t]*\(/g)) {
      if (isAuthenticCategoryCall(auth, 'tty', m[2], m[1] ?? '')) return true;
    }
    for (const m of codeNoStrings.matchAll(/([A-Za-z_$][A-Za-z0-9_$]*[ \t]*\.[ \t]*)?\b(isatty)[ \t]*\(/g)) {
      if (isAuthenticCategoryCall(auth, 'tty', m[2], m[1] ?? '')) return true;
    }
    if (auth.hasNodePtyImport) {
      for (const m of codeNoStrings.matchAll(/([A-Za-z_$][A-Za-z0-9_$]*[ \t]*\.[ \t]*)?\b(spawn)[ \t]*\(/g)) {
        if (isAuthenticCategoryCall(auth, 'tty', m[2], m[1] ?? '')) return true;
      }
    }
  }
  if (auth.mockedModules.has('fs') || !auth.importedModules.has('fs')) return false;

  // Track simple local path variables assigned a /dev/tty, /dev/ptmx, or /dev/pts/... string literal.
  const devicePathVars = new Set();
  if (stringLiteralsByOpenPos instanceof Map) {
    for (const m of codeNoStrings.matchAll(/\b(?:const|let|var)[ \t]+([A-Za-z_$][A-Za-z0-9_$]*)[ \t]*=[ \t]*("")/g)) {
      const openQuoteIdx = (m.index ?? 0) + m[0].lastIndexOf('""');
      const lit = stringLiteralsByOpenPos.get(openQuoteIdx) ?? '';
      if (REAL_DEVICE_PATH_RE.test(lit)) devicePathVars.add(m[1]);
    }
  }

  for (const m of codeNoStrings.matchAll(/([A-Za-z_$][A-Za-z0-9_$]*[ \t]*\.[ \t]*)?\b(openSync|open|statSync|stat|fstatSync|fstat|lstatSync|lstat|accessSync|access|createReadStream|createWriteStream)[ \t]*\(/g)) {
    const receiver = m[1] ?? '';
    const fnName = m[2];
    if (!isAuthenticCategoryCall(auth, 'fs', fnName, receiver)) continue;
    const openParenIdx = (m.index ?? 0) + m[0].length - 1;
    const { slice, startIdx } = extractCallArgsSlice(codeNoStrings, openParenIdx, 240);
    if (!slice) continue;
    const argLiterals = collectLiteralsInMaskedSlice(slice, startIdx, stringLiteralsByOpenPos);
    if (argLiterals.some((item) => REAL_DEVICE_PATH_RE.test(item.value))) return true;
    if (devicePathVars.size > 0) {
      for (const idMatch of slice.matchAll(/\b[A-Za-z_$][A-Za-z0-9_$]*\b/g)) {
        const idx = idMatch.index ?? 0;
        if (idx > 0 && slice[idx - 1] === '.') continue;
        if (devicePathVars.has(idMatch[0])) return true;
      }
    }
  }
  return false;
}

function detectAuthenticServerOrDb(codeNoStrings, auth) {
  // 1. Bare unshadowed global fetch(...)
  if (!auth.shadowedPrimitives.has('fetch')) {
    for (const m of codeNoStrings.matchAll(/(?<![A-Za-z0-9_$.])\bfetch\s*\(/g)) {
      if (m) return true;
    }
  }
  // 2. Authentic HTTP/server primitives when http/net/server module is genuinely imported and unmocked
  if (!auth.mockedModules.has('http') && auth.importedModules.has('http')) {
    for (const m of codeNoStrings.matchAll(/([A-Za-z_$][A-Za-z0-9_$]*\s*\.\s*)?\b(createServer|request)\s*\(/g)) {
      if (isAuthenticCategoryCall(auth, 'http', m[2], m[1] ?? '')) return true;
    }
    if (!auth.shadowedPrimitives.has('listen') && /\.\s*listen\s*\(/.test(codeNoStrings) && !/\b(?:fake|mock|stub)[A-Za-z0-9_$]*\s*\.\s*listen\s*\(/i.test(codeNoStrings)) {
      return true;
    }
    if (/\bsupertest\s*\(/.test(codeNoStrings)) return true;
  }
  // 3. Authentic DB driver / new DatabaseSync(...) when DB module is genuinely imported and unmocked
  if (!auth.mockedModules.has('db') && auth.importedModules.has('db')) {
    for (const m of codeNoStrings.matchAll(/\bnew[ \t]+([A-Za-z_$][A-Za-z0-9_$]*[ \t]*\.[ \t]*)?(DatabaseSync)[ \t]*\(/g)) {
      if (isAuthenticCategoryCall(auth, 'db', m[2], m[1] ?? '')) return true;
    }
    if (/\bnew\s+(?:Pool|Client)\s*\(/.test(codeNoStrings)) return true;
    if (auth.hasNonSqliteDbImport && !MOCK_USAGE_RE.test(codeNoStrings)) return true;
  }
  return false;
}

function detectAuthenticBrowser(codeNoStrings, auth) {
  if (auth.mockedModules.has('browser') || !auth.importedModules.has('browser')) return false;
  for (const m of codeNoStrings.matchAll(/(?:([A-Za-z_$][A-Za-z0-9_$]*)[ \t]*\.[ \t]*)?([A-Za-z_$][A-Za-z0-9_$]*)[ \t]*\.[ \t]*(launch|goto|newPage|newContext|connect)[ \t]*\(/g)) {
    const outerReceiver = m[1] ?? '';
    const receiver = m[2];
    const method = m[3];
    if (auth.shadowedPrimitives.has(method)) continue;
    if (outerReceiver && (/^(?:fake|mock|stub)/i.test(outerReceiver) || auth.shadowedBrowserVars.has(outerReceiver))) continue;
    if (/^(?:fake|mock|stub)/i.test(receiver) || auth.shadowedBrowserVars.has(receiver)) continue;
    return true;
  }
  return false;
}

function detectAuthenticFsState(codeNoStrings, auth) {
  if (auth.mockedModules.has('fs') || !auth.importedModules.has('fs')) return false;
  for (const m of codeNoStrings.matchAll(/([A-Za-z_$][A-Za-z0-9_$]*\s*\.\s*)?\b(mkdtempSync|mkdtemp|readdirSync|readdir|existsSync|readFileSync|readFile|statSync|stat|lstatSync|lstat|accessSync)\s*\(/g)) {
    if (isAuthenticCategoryCall(auth, 'fs', m[2], m[1] ?? '')) return true;
  }
  return false;
}

function detectRealExecutionSignals(codeNoStrings, stringLiteralsByOpenPos) {
  const auth = analyzePrimitiveAuthenticity(codeNoStrings, stringLiteralsByOpenPos);
  const {
    hasRealSubprocess,
    hasExternalToolSubprocess,
    hasLiveLocalSubprocess,
    hasSandboxSubprocess,
    subprocessCallCount,
    hasLoopedSubprocess,
  } = analyzeSubprocessCalls(codeNoStrings, auth, stringLiteralsByOpenPos);
  const hasMock = MOCK_USAGE_RE.test(codeNoStrings);
  const hasBrowser = detectAuthenticBrowser(codeNoStrings, auth);
  const hasServerOrDb = detectAuthenticServerOrDb(codeNoStrings, auth);
  const hasExternalSdk = auth.importedModules.has('external-sdk') && !auth.mockedModules.has('external-sdk') && !hasMock;
  const hasRealDeviceOrTtyProbe = detectRealDeviceOrTtyProbe(codeNoStrings, auth, stringLiteralsByOpenPos);
  const hasRealFsState = detectAuthenticFsState(codeNoStrings, auth);
  const hasLiveLocal = hasLiveLocalSubprocess;
  const hasLiveBinding = hasBrowser || hasServerOrDb || hasExternalToolSubprocess || hasExternalSdk;
  const hasRealHostSmoke = hasLiveBinding || hasRealSubprocess || hasRealDeviceOrTtyProbe || hasLiveLocal;
  const hasAnyRealExec = hasRealHostSmoke;
  return {
    hasBrowser,
    hasServerOrDb,
    hasRealSubprocess,
    hasLiveBinding,
    hasRealDeviceOrTtyProbe,
    hasRealFsState,
    hasLiveLocal,
    hasSandboxSubprocess,
    subprocessCallCount,
    hasLoopedSubprocess,
    hasRealHostSmoke,
    hasAnyRealExec,
  };
}

/**
 * Inspect a test file for executable, non-mocked real-host boundary probes across the 4 OS/CLI failure classes.
 */
export function detectRealHostProbesInTest(testPath, text) {
  const lint = lintValidationCode({ path: testPath, kind: 'test', text, hasRealE2eCoverage: true });
  if (lint.codes.includes('silent-validation-skip')) {
    return {
      hasRealHostSmoke: false,
      mockOnly: false,
      classes: [],
      maxDetectedPayloadBytes: null,
      detectedTurns: 0,
      liveLocal: false,
    };
  }
  const { codeNoStrings, maxInlineStringBytes, repeatLiteralUnits, stringLiteralsByOpenPos } = scanJsWithMetrics(text);
  const signals = detectRealExecutionSignals(codeNoStrings, stringLiteralsByOpenPos);
  const hasMock = MOCK_USAGE_RE.test(codeNoStrings);
  const mockOnly = hasMock && !signals.hasRealHostSmoke;
  const maxDetectedPayloadBytes = detectMaxPayloadBytes(codeNoStrings, { maxInlineStringBytes, repeatLiteralUnits });
  const detectedTurns = !signals.hasRealSubprocess
    ? 0
    : (signals.hasLoopedSubprocess ? Math.max(2, signals.subprocessCallCount) : signals.subprocessCallCount);

  const classes = new Set();
  if (signals.hasRealSubprocess && signals.hasSandboxSubprocess) {
    classes.add('nested-sandbox');
  }
  if (signals.hasRealDeviceOrTtyProbe) {
    classes.add('host-tty-ownership');
  }
  if (signals.hasRealSubprocess && detectedTurns >= 2 && signals.hasRealFsState) {
    classes.add('multi-turn-cli-state');
  }
  if (signals.hasRealHostSmoke && maxDetectedPayloadBytes !== null && maxDetectedPayloadBytes > MIN_REALISTIC_PAYLOAD_BYTES) {
    classes.add('full-size-payload');
  }

  return {
    hasRealHostSmoke: signals.hasRealHostSmoke,
    mockOnly,
    classes: [...classes].sort(),
    maxDetectedPayloadBytes,
    detectedTurns,
    liveLocal: signals.hasLiveLocal,
  };
}

/**
 * Detect which real E2E proof kinds a test file genuinely executes (comments/strings and skipped tests excluded).
 */
export function detectRealE2eKindsInTest(testPath, text) {
  const lint = lintValidationCode({ path: testPath, kind: 'test', text, hasRealE2eCoverage: true });
  if (lint.codes.includes('silent-validation-skip')) return [];

  const { codeNoStrings, stringLiteralsByOpenPos } = scanJsWithMetrics(text);
  const kinds = new Set();
  const {
    hasBrowser,
    hasServerOrDb,
    hasRealSubprocess,
    hasLiveBinding,
    hasRealHostSmoke,
    hasAnyRealExec,
  } = detectRealExecutionSignals(codeNoStrings, stringLiteralsByOpenPos);

  if (hasBrowser) kinds.add('browser-playwright');
  if (hasServerOrDb) kinds.add('local-server-or-db');
  if (hasRealSubprocess) kinds.add('subprocess-cli');
  if (hasLiveBinding) kinds.add('live-binding');
  if (hasRealHostSmoke) kinds.add('real-host-smoke');
  if (hasAnyRealExec || !MOCK_USAGE_RE.test(codeNoStrings)) kinds.add('real-execution');

  return [...kinds].sort();
}

/**
 * Classify changed repository paths into validation surfaces and required E2E proof kinds.
 */
export function detectChangedSurfaces({ changedFiles = [], nativeOnlyFiles = [] } = {}) {
  const files = Array.isArray(changedFiles) ? changedFiles.map(normalizePath).filter(Boolean) : [];
  const nativeSet = new Set(Array.isArray(nativeOnlyFiles) ? nativeOnlyFiles.map((f) => normalizePath(f).toLowerCase()).filter(Boolean) : []);
  const surfaceSet = new Set();
  const matchedNativeFiles = new Set();
  const realHostClassSet = new Set();
  let allDocs = files.length > 0;

  for (const file of files) {
    const lower = file.toLowerCase();
    const fileSurfaces = classifyProductionPathSurfaces(file);
    const isNativeOnlyFile = nativeSet.has(lower) && !isDocPath(lower) && !NON_PRODUCTION_DIR_RE.test(lower);
    if (isNativeOnlyFile) {
      matchedNativeFiles.add(file);
      if (!fileSurfaces.includes('native-only')) fileSurfaces.push('native-only');
    }
    if (!fileSurfaces.length || fileSurfaces.some((s) => s !== 'docs')) allDocs = false;
    for (const s of fileSurfaces) surfaceSet.add(s);
    const isRealHostEligible = fileSurfaces.includes('os-boundary')
      || fileSurfaces.includes('native-only')
      || fileSurfaces.includes('cli');
    if (isRealHostEligible) {
      for (const rule of REAL_HOST_CLASS_PATH_RULES) {
        if (rule.re.test(lower)) realHostClassSet.add(rule.id);
      }
    }
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
    nativeOnlyFiles: [...matchedNativeFiles].sort(),
    realHostBoundaryClasses: [...realHostClassSet].sort(),
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

function isRealHostBoundaryCheck(check, { hasOsBoundary = false } = {}) {
  if (!check || typeof check !== 'object' || check.executed !== true || check.mockOnly === true) return false;
  if (!REAL_E2E_KINDS.has(check.kind)) return false;
  const isLiveLocal = check.liveLocal === true || /--live-local\b/i.test(cleanText(check.command));
  if (hasOsBoundary) {
    return check.kind === 'real-host-smoke' || check.kind === 'subprocess-cli' || isLiveLocal;
  }
  if (check.kind === 'real-execution') {
    return isLiveLocal;
  }
  return true;
}

function isPassingRealE2eCheck(check) {
  return Boolean(
    check
    && typeof check === 'object'
    && check.executed === true
    && check.mockOnly !== true
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

function hasSubprocessRealHostEvidence(check) {
  if (!check || typeof check !== 'object' || check.kind !== 'real-host-smoke') return false;
  if (Number.isInteger(check.turns) && check.turns >= 1) return true;
  if (check.liveLocal === true || /--live-local\b/i.test(cleanText(check.command))) return true;
  if (Array.isArray(check.realHostClasses) && check.realHostClasses.some((c) => c === 'nested-sandbox' || c === 'multi-turn-cli-state')) {
    return true;
  }
  return false;
}

function coversRequiredProofKinds(requiredProofKinds, passingChecks, { hasOsBoundary = false } = {}) {
  const passedKinds = new Set(passingChecks.map((c) => c.kind));
  const hasRealHost = passingChecks.some((c) => isRealHostBoundaryCheck(c, { hasOsBoundary }));
  const hasSubprocessRealHost = passingChecks.some(hasSubprocessRealHostEvidence);
  return requiredProofKinds.every((required) => (
    passedKinds.has(required)
    || (required === 'real-host-smoke' && hasRealHost)
    || (required === 'subprocess-cli' && hasSubprocessRealHost)
    || (required === 'real-execution' && passedKinds.size > 0)
  ));
}

function findMissingRealHostClasses({ requiredClasses, explicitClasses, executedRealHostChecks }) {
  if (!requiredClasses.length) return [];
  const hasExplicitRequirement = explicitClasses.length > 0;
  const anyCheckReportsClassMeta = executedRealHostChecks.some((c) => (
    Array.isArray(c.realHostClasses)
    || Number.isInteger(c.turns)
    || Number.isFinite(c.payloadBytes)
  ));
  if (!hasExplicitRequirement && !anyCheckReportsClassMeta) return [];

  const missing = [];
  for (const cls of requiredClasses) {
    const satisfied = executedRealHostChecks.some((c) => {
      const checkClasses = Array.isArray(c.realHostClasses) ? c.realHostClasses : null;
      if (cls === 'multi-turn-cli-state') {
        if (Number.isInteger(c.turns) && c.turns < 2) return false;
        if (checkClasses) return checkClasses.includes(cls);
        return Number.isInteger(c.turns) && c.turns >= 2;
      }
      if (cls === 'full-size-payload') {
        if (Number.isFinite(c.payloadBytes) && c.payloadBytes <= MIN_REALISTIC_PAYLOAD_BYTES) return false;
        if (checkClasses) return checkClasses.includes(cls);
        return Number.isFinite(c.payloadBytes) && c.payloadBytes > MIN_REALISTIC_PAYLOAD_BYTES;
      }
      return checkClasses !== null && checkClasses.includes(cls);
    });
    if (!satisfied) missing.push(cls);
  }
  return missing;
}

function describeRealHostGap({ nativeOnlyFiles, runtimeSurfaces, missingClasses, mockOnlyDetected }) {
  const parts = [];
  if (nativeOnlyFiles.length) parts.push(`native-only module(s): ${nativeOnlyFiles.join(', ')}`);
  const nonNativeSurfaces = runtimeSurfaces.filter((s) => s !== 'native-only');
  if (nonNativeSurfaces.length) parts.push(`surface(s): ${nonNativeSurfaces.join(', ')}`);
  if (missingClasses.length) {
    parts.push(`unexercised real-host class(es): ${missingClasses.map((c) => REAL_HOST_CLASS_LABELS[c] || c).join('; ')}`);
  }
  if (mockOnlyDetected) {
    parts.push('only mocked/stubbed or in-process unit checks detected');
  }
  return parts.join('; ') || 'native-only / OS boundary real-host smoke';
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
  nativeOnlyFiles = [],
  promptFiles = null,
  bindings = null,
  fileHeads = null,
  realHostClasses = [],
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
  const detectedNative = (promptFiles || bindings || fileHeads)
    ? detectNativeOnlyModules({ changedFiles: normalizedFiles, promptFiles, bindings, fileHeads })
    : { nativeOnlyPrompts: [], nativeOnlyModules: [], matches: [] };
  const resolvedNativeOnlyFiles = [...new Set([
    ...(Array.isArray(nativeOnlyFiles) ? nativeOnlyFiles.map(normalizePath).filter(Boolean) : []),
    ...detectedNative.nativeOnlyModules,
  ])].sort();
  const explicitClasses = Array.isArray(realHostClasses)
    ? [...new Set(realHostClasses.map(cleanTool).filter((c) => REAL_HOST_CLASS_SET.has(c)))].sort()
    : [];
  const surfaceInfo = detectChangedSurfaces({
    changedFiles: normalizedFiles,
    nativeOnlyFiles: resolvedNativeOnlyFiles,
  });
  const requiredClasses = [...new Set([...explicitClasses, ...surfaceInfo.realHostBoundaryClasses])].sort();
  const needsRealHostSmoke = surfaceInfo.requiredProofKinds.includes('real-host-smoke') || explicitClasses.length > 0;
  const humanBlocker = needsHumanInteraction === true || diagLines.some((d) => HUMAN_INTERACTION_RE.test(d));
  const bucket2 = detectBucket2Blocker({ realBindingUnavailable, diagnostics: diagLines, toolHint, verifyCommand });

  if (surfaceInfo.docsOnly && !needsRealHostSmoke && !humanBlocker && !bucket2) {
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

  const defaultVerifyCmd = cleanText(verifyCommand) || (needsRealHostSmoke ? 'npm run test:smoke -- --live-local' : 'npm run test:e2e');
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
  const hasOsBoundary = surfaceInfo.runtimeSurfaces.includes('os-boundary');
  const executedRealChecks = checks.filter((c) => c && typeof c === 'object' && c.executed === true && c.mockOnly !== true && REAL_E2E_KINDS.has(c.kind));
  const executedRealHostChecks = checks.filter((c) => isRealHostBoundaryCheck(c, { hasOsBoundary }));
  const hasExecutedFailure = checks.some((c) => (
    c && typeof c === 'object' && c.executed === true
    && ((Number.isInteger(c.exitCode) && c.exitCode !== 0) || (Number.isInteger(c.failed) && c.failed > 0))
  ));
  const mockOnlyDetected = lintErrors.includes('boundary-mock-only-test')
    || checks.some((c) => c && typeof c === 'object' && (c.kind === 'unit-mock' || c.mockOnly === true))
    || (executedRealChecks.length > 0 && executedRealHostChecks.length === 0);

  if (offlinePassed === false && hasExecutedFailure) {
    return bucket1FailureOutcome({
      repairAttempts: attempts,
      message: 'Executed validation or offline suite failed; repair before retrying real-host verification.',
    });
  }

  if (needsRealHostSmoke && executedRealHostChecks.length === 0) {
    const gap = describeRealHostGap({
      nativeOnlyFiles: surfaceInfo.nativeOnlyFiles,
      runtimeSurfaces: surfaceInfo.runtimeSurfaces,
      missingClasses: requiredClasses,
      mockOnlyDetected,
    });
    return bucket3Outcome({
      waitKind: 'needs-real-host-smoke',
      repairAttempts: attempts,
      offlineSummary,
      unverifiedBoundary: cleanText(humanBoundaryDetail) || gap,
      verifyCommand: defaultVerifyCmd,
      message: `Real-host non-mocked smoke verification is required before merge (${gap}).`,
    });
  }

  if (needsRealHostSmoke && !executedRealHostChecks.some((c) => !isPassingRealE2eCheck(c))) {
    const missingClasses = findMissingRealHostClasses({
      requiredClasses,
      explicitClasses,
      executedRealHostChecks,
    });
    if (missingClasses.length > 0) {
      const gap = describeRealHostGap({
        nativeOnlyFiles: surfaceInfo.nativeOnlyFiles,
        runtimeSurfaces: surfaceInfo.runtimeSurfaces,
        missingClasses,
        mockOnlyDetected,
      });
      return bucket3Outcome({
        waitKind: 'needs-real-host-smoke',
        repairAttempts: attempts,
        offlineSummary,
        unverifiedBoundary: cleanText(humanBoundaryDetail) || gap,
        verifyCommand: defaultVerifyCmd,
        message: `Real-host boundary verification missed required host failure class(es) (${gap}).`,
      });
    }
  }

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
  const coveredSurfaces = coversRequiredProofKinds(
    surfaceInfo.requiredProofKinds,
    executedRealChecks.filter(isPassingRealE2eCheck),
    { hasOsBoundary },
  );
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

function matchSilentSkipLine(codeLine, maskedLine, kind, isValFile = false) {
  if (/^\s*(?:re|pattern)\s*:\s*\//.test(codeLine)) return null;
  if (LOCAL_SKIP_HELPER_RE.test(maskedLine)) {
    return 'silent validation local-skip helper bypasses real validation';
  }
  if (FILTER_CODE_SHAPE_RE.test(maskedLine) && FILTER_REAL_BINDING_RE.test(codeLine)) {
    return 'filters real-binding-unavailable out of blocking refusals';
  }
  if (CALL_DOT_SKIP_RE.test(maskedLine) && (isValFile || CALL_DOT_SKIP_E2E_RE.test(codeLine))) {
    return 'unconditionally skips an E2E or validation test';
  }
  if (NODE_TEST_OPT_SKIP_RE.test(maskedLine) && (isValFile || SKIP_KEYWORD_RE.test(codeLine))) {
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
export function lintValidationCode({ path = '', kind = 'test', text = '', hasRealE2eCoverage = false, nativeOnlyTargets } = {}) {
  const filePath = normalizePath(path) || 'unknown';
  const source = String(text ?? '');
  const { codeNoComments, codeNoStrings, stringLiteralsByOpenPos } = scanJsWithMetrics(source);
  const codeLines = codeNoComments.split(/\r?\n/);
  const maskedLines = codeNoStrings.split(/\r?\n/);
  const codeSet = new Set();
  const warnings = [];

  const isValFile = SKIP_KEYWORD_RE.test(filePath);
  const reportedSkipLines = new Set();
  if (kind === 'code' || kind === 'test') {
    for (let i = 0; i < codeLines.length; i += 1) {
      const detail = matchSilentSkipLine(codeLines[i], maskedLines[i] ?? '', kind, isValFile);
      if (detail) {
        reportedSkipLines.add(i + 1);
        codeSet.add('silent-validation-skip');
        warnings.push(`Warning: validation lint: ${filePath}:${i + 1} [silent-validation-skip] ${detail}`);
      }
    }
    const multilineRules = [
      { re: MULTILINE_NODE_TEST_OPT_SKIP_RE, detail: 'unconditionally skips an E2E or validation test via test options' },
      { re: MULTILINE_CALL_DOT_SKIP_RE, detail: 'unconditionally skips an E2E or validation test' },
    ];
    for (const { re, detail } of multilineRules) {
      for (const match of codeNoStrings.matchAll(re)) {
        const startLine = codeNoStrings.slice(0, match.index ?? 0).split(/\r?\n/).length;
        const endLine = startLine + match[0].split(/\r?\n/).length - 1;
        let alreadyReported = false;
        for (let ln = startLine; ln <= endLine; ln += 1) {
          if (reportedSkipLines.has(ln)) { alreadyReported = true; break; }
        }
        if (alreadyReported) continue;
        const rawSpan = codeLines.slice(startLine - 1, endLine).join('\n');
        if (!isValFile && !SKIP_KEYWORD_RE.test(rawSpan)) continue;
        reportedSkipLines.add(startLine);
        codeSet.add('silent-validation-skip');
        warnings.push(`Warning: validation lint: ${filePath}:${startLine} [silent-validation-skip] ${detail}`);
      }
    }
  }

  if (kind === 'test' && hasRealE2eCoverage !== true) {
    const { boundarySurfaces } = inspectTestBoundaryTargets(filePath, source, { nativeOnlyTargets });
    if (boundarySurfaces.length > 0) {
      const mockLineIndex = maskedLines.findIndex((line) => MOCK_USAGE_RE.test(line));
      const { hasAnyRealExec } = detectRealExecutionSignals(codeNoStrings, stringLiteralsByOpenPos);
      if (mockLineIndex >= 0 && !hasAnyRealExec) {
        codeSet.add('boundary-mock-only-test');
        const isNativeOrOs = boundarySurfaces.includes('native-only') || boundarySurfaces.includes('os-boundary');
        const detail = isNativeOrOs
          ? `mock-only test covers a ${boundarySurfaces.join('/')} boundary with no real-host smoke or --live-local execution`
          : 'mock-only test covers a runtime boundary with no real E2E coverage';
        warnings.push(
          `Warning: validation lint: ${filePath}:${mockLineIndex + 1} [boundary-mock-only-test] ${detail}`,
        );
      }
    }
  }

  const codes = [...codeSet].sort();
  return { ok: codes.length === 0, codes, warnings };
}
