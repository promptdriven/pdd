// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: 9466aa29fd1003fb631a75c3cf3148d244e24e4f7b6c392b4c74d6a88bce4fe9).

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
const OS_BOUNDARY_TOKEN_RE = tokenMatch('sandbox|tty|pty|subprocess|spawn|exec|child[-_]?process|seatbelt|seccomp|landlock|bwrap|bubblewrap|chroot|cgroup|namespace|signal|daemon|ipc|socket|fd|ioctl|termios|posix|syscall|kernel');
const REAL_HOST_CLASS_PATH_RULES = [
  { id: 'nested-sandbox', re: tokenMatch('sandbox|seatbelt|seccomp|landlock|bwrap|bubblewrap|chroot|cgroup') },
  { id: 'host-tty-ownership', re: tokenMatch('tty|pty|termios|ioctl') },
  { id: 'multi-turn-cli-state', re: tokenMatch('cli[-_]?session|cli[-_]?wrapper|session[-_]?state|containment') },
  { id: 'full-size-payload', re: tokenMatch('payload|preview|truncat|framing|wire[-_]?frame|stream[-_]?buffer') },
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
    test: (norm, base) => /^(?:os|sandbox|tty|pty|process|subprocess|native)\//i.test(norm)
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

export const MOCK_USAGE_RE = /\b(?:mock\.|vi\.mock|vi\.fn|jest\.mock|jest\.fn|sinon\.stub|MagicMock|unittest\.mock|fakeClient|fakeServer|fakeTransport|fakeSandbox|mockSandbox|stubSandbox|fakeTty|mockTty|stubTty|fakeDb|mockDb|fakeDriver|mockDriver|mockSpawn|fakeSpawn|fakeSubprocess|fakeCli|stubCli)\b|stub(?:bed)?(?:Handler|Wrapper)/i;
export const REAL_E2E_EXEC_RE = /\b(?:spawn|spawnSync|execFile|execFileSync|execSync|createServer|playwright|puppeteer|supertest|DatabaseSync)\b|\.\s*listen\s*\(|\bfetch\s*\(|\bhttps?\.request\s*\(|\b(?:chromium|firefox|webkit)\.launch\s*\(|\bpage\.goto\s*\(/i;
const BROWSER_EXEC_RE = /\b(?:playwright|puppeteer)\b|\b(?:chromium|firefox|webkit)\.launch\s*\(|\bpage\.goto\s*\(/i;
const BROWSER_IMPORT_RE = /(?:from|require\s*\()\s*['"`](?:@playwright\/test|playwright(?:-core|-chromium|-firefox|-webkit)?|puppeteer(?:-core)?)['"`]/i;
const SERVER_OR_DB_EXEC_RE = /\b(?:createServer|supertest|DatabaseSync)\b|\.\s*listen\s*\(|\bfetch\s*\(|\bhttps?\.request\s*\(|\bnew\s+(?:Pool|Client)\s*\(/i;
const DB_DRIVER_IMPORT_RE = /(?:from|require\s*\()\s*['"`](?:pg|mysql2?|better-sqlite3|node:sqlite|sqlite3?|mongodb|redis|ioredis|@prisma\/client)['"`]/i;
const EXTERNAL_SDK_IMPORT_RE = /(?:from|require\s*\()\s*['"`](?:@google-cloud\/[^'"`]+|@aws-sdk\/[^'"`]+|aws-sdk|stripe|dockerode|@kubernetes\/client-node|@octokit\/[^'"`]+|googleapis)['"`]/i;
const TTY_IMPORT_RE = /(?:from|require\s*\()\s*['"`](?:node:tty|tty|node-pty)['"`]/i;
const REAL_DEVICE_PATH_RE = /\/dev\/(?:tty|ptmx|pts\/)/;
const REAL_DEVICE_OP_RE = /\b(?:openSync|open|statSync|stat|fstatSync|fstat|lstatSync|lstat|accessSync|access|createReadStream|createWriteStream|ReadStream|WriteStream|isatty|getuid|spawn|spawnSync|execFile|execFileSync|execSync)\b/;
const SANDBOX_EXEC_RE = /\b(?:sandbox-exec|sandbox_apply|bwrap|bubblewrap|seatbelt|seccomp|landlock|unshare|chroot)\b/i;
const MULTI_TURN_STATE_RE = /\b(?:mkdtempSync|mkdtemp|readdirSync|readdir|existsSync|readFileSync|readFile|statSync|stat|HOME|containment)\b/;
const LOOP_LINE_RE = /\b(?:for|while)\s*\(|\.\s*(?:forEach|map)\s*\(/;
const SUBPROCESS_EXEC_RE = /\b(?:spawn|spawnSync|execFile|execFileSync|execSync)\s*\(/;
const SUBPROCESS_CALL_RE = /\b(?:spawn|spawnSync|execFile|execFileSync|execSync)\s*\(\s*([^;\n]{1,240})/g;
const TRIVIAL_SUBPROCESS_BIN_RE = /^(?:echo|printf|true|false|pwd|uname|whoami|id|date|sleep|cat|ls|test|\[|:)(?:\s|$)/i;
const EXTERNAL_TOOL_EXEC_RE = /\b(?:gcloud|gsutil|bq|aws|az|stripe|docker|docker-compose|kubectl|helm|terraform|gh|pdd|curl|wget|psql|mysql|redis-cli|mongosh|ssh|scp|vault|npm|npx|git)\b/i;
const BOUNDARY_IMPORT_RE = /(?:from|require\s*\()\s*['"`]([^'"`]+)['"`]/g;
const PROD_PATH_LITERAL_RE = /['"`]((?:\.\.\/|\.\/)?(?:bin|cli|cmd|scripts|api|server|routes|handlers|controllers|db|database|migrations|prisma|sql|web|ui|frontend|pages|components|views|app|os|sandbox|tty|pty|process|subprocess|native|src)\/[A-Za-z0-9._/-]+)['"`]/g;

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
const normalizePath = (value) => cleanText(value).replace(/\\/g, '/').replace(/^\.\//, '');
const emptyProof = () => ({ surfaces: [], commands: [], exitCodes: [] });

function isRegexStartContext(prevToken) {
  if (!prevToken) return true;
  if ('([{:;,=!?&|+-*%^~<>}'.includes(prevToken)) return true;
  return /^(?:return|case|throw|in|of|typeof|void|delete|new|else|do|yield|await)$/.test(prevToken);
}

/**
 * Strip JS/TS comments and separately mask string literal contents while keeping exact line numbers.
 */
export function scanJsPreserveLines(source) {
  const text = String(source ?? '');
  const noComments = [];
  const noStrings = [];
  const templateBraceDepths = [];
  let i = 0;
  let lastToken = '';

  const scanTemplatePart = () => {
    while (i < text.length) {
      const c = text[i];
      if (c === '\\' && i + 1 < text.length) {
        noComments.push(c, text[i + 1]);
        if (text[i + 1] === '\n') noStrings.push('\n');
        i += 2;
        continue;
      }
      if (c === '$' && text[i + 1] === '{') {
        noComments.push('$', '{');
        noStrings.push('"+(');
        i += 2;
        templateBraceDepths.push(1);
        lastToken = '(';
        return;
      }
      if (c === '`') {
        noComments.push(c);
        noStrings.push('"');
        i += 1;
        lastToken = '""';
        return;
      }
      noComments.push(c);
      if (c === '\n') noStrings.push('\n');
      i += 1;
    }
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

    // Template literal (scan ${...} expressions as code while masking static text)
    if (ch === '`') {
      noComments.push(ch);
      noStrings.push('"');
      i += 1;
      scanTemplatePart();
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
          noStrings.push(')+"');
          i += 1;
          scanTemplatePart();
          continue;
        }
      }
    }

    // Single- or double-quoted string literal
    if (ch === '\'' || ch === '"') {
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
        if (c === '\n') {
          noComments.push('\n');
          noStrings.push('"', '\n');
          i += 1;
          break;
        }
        noComments.push(c);
        i += 1;
      }
      lastToken = '""';
      continue;
    }

    // Regex literal (mask body in codeNoStrings so /playwright/ or /localSkipRow/ never false-match)
    if (ch === '/' && next !== '/' && next !== '*' && isRegexStartContext(lastToken || readPrevWord())) {
      noComments.push(ch);
      noStrings.push('/');
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
          noStrings.push('\n');
          i += 1;
          break;
        }
        if (c === '[') inClass = true;
        else if (c === ']') inClass = false;
        noComments.push(c);
        i += 1;
        if (c === '/' && !inClass) {
          noStrings.push(' /');
          break;
        }
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

function parseNativeOnlyPromptMeta(raw) {
  const text = String(raw ?? '');
  if (!text) return null;
  let bodyStart = -1;
  if (text.startsWith('---\n')) bodyStart = 4;
  else if (text.startsWith('---\r\n')) bodyStart = 5;
  if (bodyStart > 0) {
    let pos = bodyStart;
    while (pos <= text.length) {
      const nl = text.indexOf('\n', pos);
      const lineEnd = nl < 0 ? text.length : nl;
      const line = text.slice(pos, lineEnd).replace(/\r$/, '');
      if (line === '---') {
        const fm = text.slice(bodyStart, pos);
        if (/^\s*kind\s*:\s*(?:['"])?native-only(?:['"])?\s*(?:#.*)?$/im.test(fm)) {
          const reasonMatch = /^\s*reason\s*:\s*(.+)$/im.exec(fm);
          const reason = reasonMatch ? reasonMatch[1].trim().replace(/^['"]|['"]$/g, '') : '';
          return { nativeOnly: true, reason, bodyOffset: nl < 0 ? text.length : nl + 1 };
        }
        break;
      }
      if (nl < 0) break;
      pos = nl + 1;
    }
  }
  const lower = text.toLowerCase();
  if (lower.includes('native-only') && lower.includes('runtime interface')) {
    let pos = 0;
    while (pos < text.length) {
      const openFence = text.indexOf('```', pos);
      if (openFence < 0) break;
      const nl = text.indexOf('\n', openFence + 3);
      if (nl < 0) break;
      const closeFence = text.indexOf('\n```', nl + 1);
      if (closeFence < 0) break;
      const lang = text.slice(openFence + 3, nl).trim().toLowerCase();
      if (lang === 'json' || lang === '') {
        try {
          const parsed = JSON.parse(text.slice(nl + 1, closeFence));
          if (parsed && typeof parsed === 'object' && !Array.isArray(parsed) && parsed.kind === 'native-only') {
            return { nativeOnly: true, reason: cleanText(parsed.reason), bodyOffset: 0 };
          }
        } catch {}
      }
      pos = closeFence + 4;
    }
  }
  return null;
}

function extractHeaderPromptRefs(rawContent) {
  const head = String(rawContent ?? '').slice(0, 4096);
  const refs = [];
  const seen = new Set();
  for (const rawLine of head.split(/\r?\n/)) {
    const line = rawLine.trim();
    const m = /^(?:\/\/|#|<!--|\*|"""|''')\s*(?:Generated from|Prompt:)\s+(\S+)/i.exec(line);
    if (!m) continue;
    const rawToken = m[1].replace(/[.,;:]+$/, '');
    if (!rawToken.endsWith('.prompt.md')) continue;
    const promptPath = normalizePath(rawToken);
    if (promptPath && !promptPath.startsWith('..') && !promptPath.includes('/../') && !seen.has(promptPath)) {
      seen.add(promptPath);
      refs.push(promptPath);
    }
  }
  return refs;
}

function extractOpeningSentenceClaims(rawPrompt, bodyOffset = 0) {
  const lines = String(rawPrompt ?? '').slice(bodyOffset).split(/\r?\n/);
  let sawTitle = false;
  const paraLines = [];
  for (const rawLine of lines) {
    const line = rawLine.trim();
    if (!sawTitle) {
      if (!line) continue;
      if (/^#\s+\S/.test(line)) sawTitle = true;
      continue;
    }
    if (!line) {
      if (paraLines.length > 0) break;
      continue;
    }
    if (/^#{1,6}\s+/.test(line)) break;
    paraLines.push(line);
  }
  if (!paraLines.length) return [];
  const para = paraLines.join(' ');
  // Extract first sentence without breaking inside backticks.
  let inTicks = false;
  let sentenceEnd = para.length;
  for (let i = 0; i < para.length; i += 1) {
    const ch = para[i];
    if (ch === '`') { inTicks = !inTicks; continue; }
    if (!inTicks && ch === '.' && (i + 1 === para.length || /\s/.test(para[i + 1]))) {
      sentenceEnd = i + 1;
      break;
    }
  }
  const sentence = para.slice(0, sentenceEnd);
  const claims = new Set();
  let i = 0;
  while (i < sentence.length) {
    const start = sentence.indexOf('`', i);
    if (start < 0) break;
    const end = sentence.indexOf('`', start + 1);
    if (end < 0) break;
    const token = normalizePath(sentence.slice(start + 1, end));
    if (token && token.includes('/') && !token.endsWith('.prompt.md') && !token.startsWith('..') && !token.includes('/../')) {
      claims.add(token);
    }
    i = end + 1;
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
  const nativePrompts = new Map(); // promptPath -> { reason, claims }
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
    nativePrompts.set(p, {
      reason: meta.reason,
      claims: new Set(extractOpeningSentenceClaims(item.content, meta.bodyOffset)),
    });
  }

  const bindingMap = new Map(); // modulePath -> promptPath
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
        const mod = normalizePath(entry.module);
        const prm = normalizePath(entry.prompt);
        if (mod && prm && nativePrompts.has(prm)) bindingMap.set(mod, prm);
      }
    }
  }

  const headMap = new Map(); // modulePath -> headContent
  if (Array.isArray(fileHeads)) {
    for (const entry of fileHeads) {
      if (!entry || typeof entry !== 'object') continue;
      const p = normalizePath(entry.path);
      if (p && typeof entry.content === 'string') headMap.set(p, entry.content);
    }
  } else if (fileHeads instanceof Map) {
    for (const [k, v] of fileHeads.entries()) {
      const p = normalizePath(k);
      if (p && typeof v === 'string') headMap.set(p, v);
    }
  } else if (fileHeads && typeof fileHeads === 'object') {
    for (const [k, v] of Object.entries(fileHeads)) {
      const p = normalizePath(k);
      if (p && typeof v === 'string') headMap.set(p, v);
    }
  }

  const proseClaimsByModule = new Map(); // modulePath -> promptPath
  for (const [promptPath, meta] of nativePrompts.entries()) {
    for (const claim of meta.claims) {
      if (!proseClaimsByModule.has(claim)) proseClaimsByModule.set(claim, promptPath);
    }
  }

  const matches = [];
  const moduleSet = new Set();
  const changedList = Array.isArray(changedFiles) ? [...new Set(changedFiles.map(normalizePath).filter(Boolean))].sort() : [];
  for (const file of changedList) {
    const lower = file.toLowerCase();
    if (isDocPath(lower) || NON_PRODUCTION_DIR_RE.test(lower)) continue;
    let promptPath = null;
    let source = null;
    if (bindingMap.has(file)) {
      promptPath = bindingMap.get(file);
      source = 'binding';
    } else if (headMap.has(file)) {
      const refs = extractHeaderPromptRefs(headMap.get(file));
      const matchedPrompt = refs.find((r) => nativePrompts.has(r));
      if (matchedPrompt) {
        promptPath = matchedPrompt;
        source = 'header';
      }
    }
    if (!promptPath && proseClaimsByModule.has(file)) {
      promptPath = proseClaimsByModule.get(file);
      source = 'prose';
    }
    if (promptPath) {
      moduleSet.add(file);
      matches.push({
        module: file,
        prompt: promptPath,
        source,
        reason: nativePrompts.get(promptPath)?.reason ?? '',
      });
    }
  }

  return {
    nativeOnlyPrompts: [...nativePrompts.keys()].sort(),
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
    if (spec.startsWith('.') || /^(?:bin|cli|cmd|scripts|api|server|routes|handlers|controllers|db|database|migrations|prisma|sql|web|ui|frontend|pages|components|views|app|os|sandbox|tty|pty|process|subprocess|native|src)\//i.test(spec)) {
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

function detectMaxPayloadBytes(codeNoComments) {
  const text = String(codeNoComments ?? '');
  let maxBytes = null;
  const record = (n) => {
    if (Number.isInteger(n) && n > 0 && (maxBytes === null || n > maxBytes)) maxBytes = n;
  };

  for (const m of text.matchAll(/(?:'([^'\r\n]{1,64})'|"([^"\r\n]{1,64})"|`([^`\r\n]{1,64})`)\s*\.\s*repeat\s*\(([0-9_*\s+]{1,40})\)/g)) {
    const unit = m[1] ?? m[2] ?? m[3] ?? '';
    const count = parseSimpleByteExpr(m[4]);
    if (count !== null && unit.length > 0) record(unit.length * count);
  }
  for (const m of text.matchAll(/\.\s*repeat\s*\(([0-9_*\s+]{1,40})\)/g)) {
    const count = parseSimpleByteExpr(m[1]);
    if (count !== null) record(count);
  }
  for (const m of text.matchAll(/\b(?:Buffer\s*\.\s*alloc(?:Unsafe)?|new\s+(?:Uint8Array|Array|Buffer))\s*\(([0-9_*\s+]{1,40})\)/g)) {
    const size = parseSimpleByteExpr(m[1]);
    if (size !== null) record(size);
  }

  // Linear scan for large inline string literals (> 4 KiB) without regex backtracking.
  let i = 0;
  while (i < text.length) {
    const ch = text[i];
    if (ch === '\'' || ch === '"' || ch === '`') {
      const start = i + 1;
      i += 1;
      while (i < text.length) {
        const c = text[i];
        if (c === '\\') { i += 2; continue; }
        if (c === ch) {
          const len = i - start;
          if (len > MIN_REALISTIC_PAYLOAD_BYTES) record(len);
          i += 1;
          break;
        }
        if (c === '\n' && ch !== '`') { i += 1; break; }
        i += 1;
      }
      continue;
    }
    i += 1;
  }

  return maxBytes;
}

const HELPER_DEF_RE = /\b(?:function\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*\(|(?:const|let|var)\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*(?:async\s+)?(?:\([^)]*\)|[A-Za-z_$][A-Za-z0-9_$]*)\s*=>)/;

function countIdentifierCalls(codeNoStrings, name) {
  let count = 0;
  let pos = 0;
  while (pos < codeNoStrings.length) {
    const idx = codeNoStrings.indexOf(name, pos);
    if (idx < 0) break;
    const before = idx > 0 ? codeNoStrings[idx - 1] : '';
    const afterIdx = idx + name.length;
    if (!before || !/[A-Za-z0-9_$.]/.test(before)) {
      let j = afterIdx;
      while (j < codeNoStrings.length && (codeNoStrings[j] === ' ' || codeNoStrings[j] === '\t')) j += 1;
      if (codeNoStrings[j] === '(') {
        const lineStart = codeNoStrings.lastIndexOf('\n', idx) + 1;
        const prefix = codeNoStrings.slice(lineStart, idx);
        if (!/\bfunction\s+$/.test(prefix)) count += 1;
      }
    }
    pos = afterIdx;
  }
  return count;
}

function analyzeSubprocessCalls(codeNoComments, codeNoStrings) {
  let hasRealSubprocess = false;
  let hasExternalToolSubprocess = false;
  let hasLiveLocalSubprocess = false;
  let hasSandboxSubprocess = false;
  let subprocessCallCount = 0;
  let hasLoopedSubprocess = false;
  if (!SUBPROCESS_EXEC_RE.test(codeNoStrings)) {
    return {
      hasRealSubprocess,
      hasExternalToolSubprocess,
      hasLiveLocalSubprocess,
      hasSandboxSubprocess,
      subprocessCallCount,
      hasLoopedSubprocess,
    };
  }
  const codeLines = codeNoComments.split(/\r?\n/);
  const maskedLines = codeNoStrings.split(/\r?\n/);
  const helperNames = new Set();
  for (let i = 0; i < maskedLines.length; i += 1) {
    if (!SUBPROCESS_EXEC_RE.test(maskedLines[i])) continue;
    const lineLen = (codeLines[i] ?? '').length;
    const windowText = codeLines.slice(i, i + 4).join(' ');
    const lookbackStart = Math.max(0, i - 4);
    const prevContext = maskedLines.slice(lookbackStart, i + 1).join('\n');
    const inLoop = LOOP_LINE_RE.test(prevContext);
    let matchedNonTrivial = false;
    for (const match of windowText.matchAll(SUBPROCESS_CALL_RE)) {
      if ((match.index ?? 0) > lineLen) break;
      const argText = (match[1] ?? '').trim();
      if (!argText) continue;
      const literalFirst = /^(['"`])([^'"`]*)\1/.exec(argText);
      if (literalFirst) {
        const rawCmd = literalFirst[2].trim();
        if (!rawCmd) continue;
        const firstWord = rawCmd.split(/\s+/)[0] ?? '';
        const baseBin = firstWord.split(/[\\/]/).pop() ?? '';
        if (!baseBin || TRIVIAL_SUBPROCESS_BIN_RE.test(baseBin)) continue;
        hasRealSubprocess = true;
        matchedNonTrivial = true;
        subprocessCallCount += 1;
        if (inLoop) hasLoopedSubprocess = true;
        if (/--live-local\b/i.test(argText)) hasLiveLocalSubprocess = true;
        if (SANDBOX_EXEC_RE.test(rawCmd) || SANDBOX_EXEC_RE.test(argText)) hasSandboxSubprocess = true;
        const isShellOrRuntime = /^(?:sh|bash|zsh|dash|fish|cmd|cmd\.exe|powershell|pwsh|node|nodejs|python|python3|ruby|deno|bun|tsx|ts-node)$/i.test(baseBin);
        if (EXTERNAL_TOOL_EXEC_RE.test(rawCmd) || (isShellOrRuntime && EXTERNAL_TOOL_EXEC_RE.test(argText))) {
          hasExternalToolSubprocess = true;
        }
        continue;
      }
      hasRealSubprocess = true;
      matchedNonTrivial = true;
      subprocessCallCount += 1;
      if (inLoop) hasLoopedSubprocess = true;
      if (/--live-local\b/i.test(argText)) hasLiveLocalSubprocess = true;
      if (SANDBOX_EXEC_RE.test(argText)) hasSandboxSubprocess = true;
      if (EXTERNAL_TOOL_EXEC_RE.test(argText)) {
        hasExternalToolSubprocess = true;
      }
    }
    if (matchedNonTrivial) {
      for (let back = i; back >= lookbackStart; back -= 1) {
        const def = HELPER_DEF_RE.exec(maskedLines[back] ?? '');
        const helper = def?.[1] ?? def?.[2];
        if (helper && helper !== 'test' && helper !== 'it' && helper !== 'describe') {
          helperNames.add(helper);
          break;
        }
      }
    }
  }
  for (const helper of helperNames) {
    const calls = countIdentifierCalls(codeNoStrings, helper);
    if (calls > subprocessCallCount) subprocessCallCount = calls;
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

function detectRealExecutionSignals(codeNoComments, codeNoStrings) {
  const {
    hasRealSubprocess,
    hasExternalToolSubprocess,
    hasLiveLocalSubprocess,
    hasSandboxSubprocess,
    subprocessCallCount,
    hasLoopedSubprocess,
  } = analyzeSubprocessCalls(codeNoComments, codeNoStrings);
  const hasMock = MOCK_USAGE_RE.test(codeNoStrings);
  const hasBrowser = BROWSER_EXEC_RE.test(codeNoStrings)
    || (BROWSER_IMPORT_RE.test(codeNoComments) && /\.(?:launch|goto|newPage)\s*\(/i.test(codeNoStrings));
  const hasServerOrDb = SERVER_OR_DB_EXEC_RE.test(codeNoStrings)
    || (DB_DRIVER_IMPORT_RE.test(codeNoComments) && !hasMock);
  const hasExternalSdk = EXTERNAL_SDK_IMPORT_RE.test(codeNoComments) && !hasMock;
  const hasRealDeviceOrTtyProbe = !hasMock && (
    (REAL_DEVICE_PATH_RE.test(codeNoComments) && REAL_DEVICE_OP_RE.test(codeNoStrings))
    || (TTY_IMPORT_RE.test(codeNoComments) && REAL_DEVICE_OP_RE.test(codeNoStrings))
  );
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
  const { codeNoComments, codeNoStrings } = scanJsPreserveLines(text);
  const signals = detectRealExecutionSignals(codeNoComments, codeNoStrings);
  const hasMock = MOCK_USAGE_RE.test(codeNoStrings);
  const mockOnly = hasMock && !signals.hasRealHostSmoke;
  const maxDetectedPayloadBytes = detectMaxPayloadBytes(codeNoComments);
  const detectedTurns = !signals.hasRealSubprocess
    ? 0
    : (signals.hasLoopedSubprocess ? Math.max(2, signals.subprocessCallCount) : signals.subprocessCallCount);

  const classes = new Set();
  if (signals.hasRealSubprocess && !mockOnly && (
    signals.hasSandboxSubprocess
    || /\b(?:sandbox|seatbelt|seccomp|landlock|bwrap|bubblewrap)\b/i.test(String(testPath ?? ''))
    || SANDBOX_EXEC_RE.test(codeNoComments)
  )) {
    classes.add('nested-sandbox');
  }
  if (signals.hasRealDeviceOrTtyProbe && !mockOnly) {
    classes.add('host-tty-ownership');
  }
  if (signals.hasRealSubprocess && !mockOnly && detectedTurns >= 2 && MULTI_TURN_STATE_RE.test(codeNoComments)) {
    classes.add('multi-turn-cli-state');
  }
  if (signals.hasRealHostSmoke && !mockOnly && maxDetectedPayloadBytes !== null && maxDetectedPayloadBytes > MIN_REALISTIC_PAYLOAD_BYTES) {
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

  const { codeNoComments, codeNoStrings } = scanJsPreserveLines(text);
  const kinds = new Set();
  const {
    hasBrowser,
    hasServerOrDb,
    hasRealSubprocess,
    hasLiveBinding,
    hasRealHostSmoke,
    hasAnyRealExec,
  } = detectRealExecutionSignals(codeNoComments, codeNoStrings);

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
  const nativeSet = new Set(Array.isArray(nativeOnlyFiles) ? nativeOnlyFiles.map(normalizePath).filter(Boolean) : []);
  const surfaceSet = new Set();
  const matchedNativeFiles = new Set();
  const realHostClassSet = new Set();
  let allDocs = files.length > 0;

  for (const file of files) {
    const fileSurfaces = classifyProductionPathSurfaces(file);
    const isNativeOnlyFile = nativeSet.has(file) && !isDocPath(file.toLowerCase()) && !NON_PRODUCTION_DIR_RE.test(file.toLowerCase());
    if (isNativeOnlyFile) {
      matchedNativeFiles.add(file);
      if (!fileSurfaces.includes('native-only')) fileSurfaces.push('native-only');
    }
    if (!fileSurfaces.length || fileSurfaces.some((s) => s !== 'docs')) allDocs = false;
    for (const s of fileSurfaces) surfaceSet.add(s);
    if (!isDocPath(file.toLowerCase()) && !NON_PRODUCTION_DIR_RE.test(file.toLowerCase())) {
      const lower = file.toLowerCase();
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

function isRealHostBoundaryCheck(check) {
  if (!check || typeof check !== 'object' || check.executed !== true || check.mockOnly === true) return false;
  if (!REAL_E2E_KINDS.has(check.kind)) return false;
  if (check.kind === 'real-execution') {
    return check.liveLocal === true || /--live-local\b/i.test(cleanText(check.command));
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

function coversRequiredProofKinds(requiredProofKinds, passingChecks) {
  const passedKinds = new Set(passingChecks.map((c) => c.kind));
  const hasRealHost = passingChecks.some(isRealHostBoundaryCheck);
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
        if (Number.isInteger(c.turns)) return c.turns >= 2;
        return !hasExplicitRequirement;
      }
      if (cls === 'full-size-payload') {
        if (Number.isFinite(c.payloadBytes) && c.payloadBytes <= MIN_REALISTIC_PAYLOAD_BYTES) return false;
        if (checkClasses) return checkClasses.includes(cls);
        if (Number.isFinite(c.payloadBytes)) return c.payloadBytes > MIN_REALISTIC_PAYLOAD_BYTES;
        return !hasExplicitRequirement;
      }
      if (checkClasses) return checkClasses.includes(cls);
      return !hasExplicitRequirement;
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
  const executedRealChecks = checks.filter((c) => c && typeof c === 'object' && c.executed === true && c.mockOnly !== true && REAL_E2E_KINDS.has(c.kind));
  const executedRealHostChecks = checks.filter(isRealHostBoundaryCheck);
  const mockOnlyDetected = lintErrors.includes('boundary-mock-only-test')
    || checks.some((c) => c && typeof c === 'object' && (c.kind === 'unit-mock' || c.mockOnly === true))
    || (executedRealChecks.length > 0 && executedRealHostChecks.length === 0);

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

  if (needsRealHostSmoke) {
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
  const { codeNoComments, codeNoStrings } = scanJsPreserveLines(source);
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
      const { hasAnyRealExec } = detectRealExecutionSignals(codeNoComments, codeNoStrings);
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
