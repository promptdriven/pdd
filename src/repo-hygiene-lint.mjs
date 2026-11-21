// Generated from prompts/cli/repo-hygiene-lint.prompt.md (sha256: e105deb7d1fc2a2cd136c5287e2796f233baeee703912561e53906d614278f61).
import { closeSync, constants, fstatSync, lstatSync, openSync, readdirSync, readSync, realpathSync } from 'node:fs';
import { isAbsolute, join, posix } from 'node:path';
import { canonicalTargetPath, detectRealE2eKindsInTest, inspectTestBoundaryTargets, lintValidationCode } from './autopilot-validator.mjs';
import { isTestOwnedPath, resolveOwners } from './file-owner.mjs';
import { auditProductPlan } from './product-documents.mjs';
import { isLintableStoryPath, lintStory } from './story-lint.mjs';
import { gitFiles, isSecretPath, workspace } from './runtime-seam.mjs';

const MAX_FILE_BYTES = 2 * 1024 * 1024;
const HEAD_BYTES = 4096;
const PROMPT_FENCE_LINE_LIMIT = 15;
const PROMPT_FENCE_TOTAL_LIMIT = 30;
const DIAGRAM_MIN_PROSE_LINES = 18;
const DIAGRAM_MIN_BRANCH_LINES = 5;
const CODE_FILE_EXT = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift|c|cc|cpp|h|hpp|php|scala|lua|sh)$/i;
const TEST_CODE_EXT = /\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift)$/i;
const SRC_CODE_PATH = /^src\/.+\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|cs|swift)$/i;
const SEAM_TEST_FILE = /(?:^|\/)[^/]*seam\.test\.[A-Za-z0-9]+$/i;
const SKIP_TEST_SUBDIR = /(?:^|\/)(?:fixtures|helpers)\//i;
const FIXTURE_DIR = /(?:^|\/)fixtures(?:\/|$)/i;
const EXAMPLE_DIR = /(?:^|\/)examples(?:\/|$)/i;
const NON_CODE_DIR = /^(?:user_stories|docs?|\.github)\//i;
const RULE_ID_RE = /^[A-Za-z0-9][A-Za-z0-9_.-]{0,63}$/;
const PRIVATE_MODULE_SEGMENT_RE = /(?:^|\/|\.)(?:internal|_internal|private|_private|impl|_impl)(?:\/|\.|$)/i;
const PRIVATE_MODULE_BASENAME_RE = /(?:^|\/)_[A-Za-z0-9][\w.-]*$/;
const DUNDER_BASENAME_RE = /(?:^|\/)__[A-Za-z0-9_]+__(?:\.[A-Za-z0-9]+)?$/;
const PRIVATE_SYMBOL_RE = /^_[A-Za-z0-9][\w$]*$/;

const IMPERATIVE_PATTERNS = [
  /(?<![\w$-])(?:export|const|let|def|impl)\s+/,
  /(?<![\w$-])function(?:\s+[A-Za-z_$]|\s*\(|\*)/,
  /(?<![\w$-])(?:if|for|while)\s*\(/,
  /(?<![\w$-])return(?:\s+|;|$)/,
  /(?<![\w$-])try\s*\{/,
  /=>/,
];

const TEST_FRAMEWORK_PACKAGES = new Set([
  'vitest', 'jest', '@jest/globals', 'mocha', 'chai', 'sinon', 'ava', 'tap', 'uvu',
  'playwright', '@playwright/test', 'pytest', 'unittest',
]);

const DECLARATIVE_SCHEMA_FENCE_LANGS = new Set([
  'sql', 'ddl', 'sqlite', 'postgres', 'postgresql', 'mysql',
  'openapi', 'yaml', 'yml', 'json', 'jsonc', 'jsonschema', 'json-schema',
  'protobuf', 'proto', 'graphql', 'gql', 'http', 'idl', 'schema',
  'avro', 'avsc', 'thrift', 'toml', 'xml', 'xsd', 'prisma',
]);
const SQL_FENCE_LANGS = new Set(['sql', 'ddl', 'sqlite', 'postgres', 'postgresql', 'mysql']);
const SQL_TABLE_CONSTRAINT_KEYWORDS = new Set([
  'primary', 'foreign', 'unique', 'check', 'constraint', 'index', 'key',
  'create', 'alter', 'insert', 'select', 'references', 'exclude', 'like',
]);
const NON_PORT_FILE_EXTENSIONS = new Set([
  'mjs', 'cjs', 'js', 'jsx', 'ts', 'tsx', 'mts', 'cts', 'py', 'pyi',
  'go', 'rs', 'rb', 'java', 'kt', 'cs', 'cc', 'cpp', 'hpp', 'swift', 'php', 'lua',
  'sh', 'bash', 'zsh', 'ps1', 'bat',
  'json', 'jsonc', 'jsonl', 'ndjson', 'yaml', 'yml', 'toml', 'ini', 'cfg', 'conf', 'env',
  'xml', 'xsd', 'html', 'htm', 'css', 'scss', 'less', 'svg', 'png', 'jpg', 'jpeg', 'gif', 'webp', 'ico',
  'pdf', 'csv', 'tsv', 'txt', 'md', 'mdx', 'rst', 'log',
  'sql', 'ddl', 'db', 'sqlite', 'sqlite3', 'wal', 'shm', 'proto', 'graphql', 'gql', 'prisma', 'avsc', 'avro', 'thrift',
  'wasm', 'gz', 'tar', 'zip', 'pem', 'crt', 'cert', 'key', 'pid', 'sock', 'socket',
  'service', 'timer', 'example', 'sample', 'tmp', 'bak', 'orig', 'git', 'lockb', 'map',
]);
const NON_PORT_EXACT_FILENAMES = new Set([
  'yarn.lock', 'bun.lock', 'cargo.lock', 'poetry.lock', 'gemfile.lock',
  'composer.lock', 'uv.lock', 'flake.lock', 'podfile.lock', 'packages.lock',
  'merge-queue.lock',
]);
const NON_PORT_TLDS = new Set([
  'com', 'org', 'net', 'io', 'dev', 'app', 'ai', 'gov', 'edu', 'localhost', 'arpa', 'local',
]);
const NON_PORT_PREFIXES = new Set([
  'env', 'process', 'console', 'window', 'document', 'global', 'globalthis',
  'module', 'exports', 'import', 'this', 'self', 'super', 'args', 'argv',
  'stdin', 'stdout', 'stderr', 'ports', 'options', 'opts', 'req', 'res',
  'request', 'response', 'err', 'error', 'headers', 'params', 'query', 'body', 'cookies',
  'ctx', 'app', 'router', 'server', 'db', 'pool', 'conn', 'tx', 'config', 'excluded',
  'sqlite3', 'uvicorn', 'asyncio', 'json', 'sqlalchemy', 'httpx', 'requests',
  'fastapi', 'flask', 'express', 'fastify', 'koa', 'django', 'pydantic', 'aiohttp',
  'psycopg', 'psycopg2', 'pg', 'prisma', 'drizzle', 'knex', 'redis', 'ioredis', 'boto3',
  'logging', 'logger', 'pathlib', 'subprocess', 'threading', 'multiprocessing',
  'datetime', 'time', 'math', 'random', 'hashlib', 'base64', 'urllib', 'socket', 'ssl',
  'node', 'bun', 'deno', 'sys', 'os', 'path', 'posix', 'fs', 'url', 'util',
  'crypto', 'stream', 'events', 'timers', 'zlib', 'net', 'tls', 'dns',
  'http', 'https', 'http2', 'child_process', 'worker_threads', 'readline', 'std', 'fmt',
]);
const NON_PORT_JS_MEMBERS = new Set([
  'length', 'prototype', 'constructor', 'toString', 'valueOf', 'hasOwnProperty',
  'startsWith', 'endsWith', 'forEach', 'flatMap', 'indexOf', 'lastIndexOf',
  'toLowerCase', 'toUpperCase', 'charAt', 'substring', 'substr',
]);
const VERSION_TOKEN_RE = /^v?\d+$/i;
const SIMPLE_IDENT_RE = /^[a-z][a-zA-Z0-9_-]*$/;
const BARE_PORT_OP_RE = /^([a-z][a-zA-Z0-9_-]*)\.([a-z][a-zA-Z0-9_-]*)$/;
const CALL_PORT_OP_RE = /^([a-z][a-zA-Z0-9_-]*)\.([a-z][a-zA-Z0-9_-]*)\s*\(/;
const BRACE_PORT_OP_RE = /^([a-z][a-zA-Z0-9_-]*)\.\{\s*([a-z][a-zA-Z0-9_-]*(?:\s*,\s*[a-z][a-zA-Z0-9_-]*)+)\s*\}$/;
const INLINE_BRACE_PORT_SCAN_RE = /(?<![A-Za-z0-9_./:@-])([a-z][a-zA-Z0-9_-]*)\.\{\s*([a-z][a-zA-Z0-9_-]*(?:\s*,\s*[a-z][a-zA-Z0-9_-]*)+)\s*\}/g;
const NETWORK_PORT_HEADING_RE = /\b(?:tcp|udp|http|https|grpc|listen(?:ing)?|network|socket|server|tls|ssl|firewall|docker|container|kubernetes|k8s|ingress|expos(?:e|ed))\b/i;
const DOMAIN_PORT_HEADING_RE = /\b(?:port\s+wiring|port\s+bindings?|bound\s+ports?|wired\s+ports?|injected\s+ports?|external\s+ports?|port\s+adapters?|port\s+map(?:ping)?|port\s+interface|port\s+contract|dependency\s+wiring|ports?)\b/i;
const DEP_PORTS_HEADING_RE = /\b(?:injected\s+ports?|external\s+ports?|domain\s+ports?|port\s+interface|port\s+contract|ports?|resources?)\b/i;
const PORT_TABLE_COL_PORT_RE = /\b(?:port|ports|bound\s+port|wired\s+port|injected\s+port|port\s+op(?:eration)?)\b/i;
const PORT_TABLE_COL_IN_SECTION_RE = /\b(?:operation|operations|binding|bindings)\b/i;
const PORT_TABLE_COL_EXCLUDE_RE = /\b(?:tcp|udp|http|https|listen|network|socket|file|path|table|column|field|type|route|endpoint|url|sql|env|variable|header|status|code|metric|flag|option|description|notes?)\b/i;
const DEP_TABLE_PORT_NAME_COL_RE = /\b(?:port|resource|service|adapter|interface|namespace)\b/i;
const DEP_TABLE_OP_COL_RE = /\b(?:operation|operations|op|ops|method|methods|action|actions)\b/i;
const DOMAIN_PORT_CUE_RE = /\b(?:wire|wires|wired|wiring|port|ports|bind|binds|bound|binding|bindings)\b/i;
const DOMAIN_PORT_DIRECT_CUE_RE = /\b(?:wire|wires|wired|wiring|ports?)\b/i;
const DOMAIN_PORT_BIND_WORD_RE = /\b(?:bind|binds|bound|binding|bindings)\b/i;
const DOMAIN_PORT_BIND_CONTEXT_RE = /\b(?:ports?|adapters?|domain)\b/i;
const DIRECT_BIND_PORT_OP_RE = /\bbind(?:s|ing)?\s+`?[a-z][a-zA-Z0-9_-]*\.[a-z][a-zA-Z0-9_-]*`?/i;
const NON_PORT_IDIOM_PATTERNS = [
  /\b(?:tcp|udp|http|https|grpc|ws|wss|listen(?:ing)?|server|socket|host|local|remote|network|container|service)\s+ports?\b/gi,
  /\b(?:on|to|at|from)\s+port(?:\s+`?\d+`?|\s+`?[A-Z0-9_]+`?)?\b/gi,
  /\bports?\s+`?\d+`?\b/gi,
  /\bports?\s+(?:number|numbers|env|variable|variables|range)\b/gi,
  /\bbind(?:s|ing)?\s+(?:the\s+)?(?:(?:http|https|tcp|udp|server|listener|socket|address|host|interface|localhost)\b|`localhost`|`?(?:\d{1,3}\.){3}\d{1,3}`?(?![A-Za-z0-9_.-])|`?\[?::(?:1)?\]?`?(?![A-Za-z0-9_.-]))/gi,
  /\bport\s+binding\s+(?:on|to|for)\s+(?:(?:tcp|udp|http|https|server|socket|localhost)\b|`localhost`|`?(?:\d{1,3}\.){3}\d{1,3}`?(?![A-Za-z0-9_.-])|`?\[?::(?:1)?\]?`?(?![A-Za-z0-9_.-]))/gi,
  /\b(?:upper|lower|time|size|memory|cpu|io|rate|retry|retries|error|timeout|latency|cost|call|step|depth|length|line|byte|buffer|queue|batch|window|hard|soft|strict)\s+bounds?\b/gi,
  /\bbounds?\s+(?:on|of|for)\b/gi,
  /\bwire\s+(?:format|formats|protocol|protocols|encoding|encodings|type|types|frame|frames|bytes|payload|payloads|schema|schemas|representation|level|compatible|compatibility)\b/gi,
  /\b(?:on|over)\s+the\s+wire\b/gi,
  /\bbind(?:s|ing)?\s+(?:(?:sql|query|statement|prepared|positional|named|input|output|request|response|form|body|route|path|header|env|template|data|event|key|signal)\s+)*(?:param|params|parameter|parameters|value|values|column|columns|variable|variables|arg|args|argument|arguments|placeholder|placeholders|field|fields|handler|handlers|listener|listeners|event|events|key|keys)\b/gi,
  /\b(?:sql|query|statement|param|parameter|value|column|variable|data|event|key)\s+bindings?\b/gi,
];
const BULLET_LINE_RE = /^([ \t]*)(?:[-*+]|\d+[.)])\s+(.+)$/;
const EMPTY_STRING_SET = new Set();

const canonicalRepoPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');

function readSafeUtf8(realRoot, relPath, maxBytes = MAX_FILE_BYTES) {
  if (!canonicalRepoPath(relPath)) return null;
  const parts = relPath.split('/');
  let cur = realRoot;
  try {
    for (let i = 0; i < parts.length; i++) {
      cur = join(cur, parts[i]);
      const st = lstatSync(cur);
      if (st.isSymbolicLink()) return null;
      if (i < parts.length - 1 && !st.isDirectory()) return null;
      if (i === parts.length - 1 && (!st.isFile() || st.size > maxBytes)) return null;
    }
  } catch {
    return null;
  }
  let fd;
  try {
    fd = openSync(cur, constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0));
    const fst = fstatSync(fd);
    if (!fst.isFile() || fst.size > maxBytes) return null;
    const buf = Buffer.alloc(fst.size);
    let offset = 0;
    while (offset < buf.length) {
      const n = readSync(fd, buf, offset, buf.length - offset, offset);
      if (!n) break;
      offset += n;
    }
    return buf.subarray(0, offset).toString('utf8');
  } catch {
    return null;
  } finally {
    if (fd !== undefined) {
      try { closeSync(fd); } catch {}
    }
  }
}

const blankPreservingLines = segment => segment.replace(/[^\r\n]/g, ' ');

function findFrontmatterRange(raw) {
  const text = String(raw ?? '');
  let bodyStart;
  if (text.startsWith('---\n')) bodyStart = 4;
  else if (text.startsWith('---\r\n')) bodyStart = 5;
  else return null;
  let pos = bodyStart;
  while (pos <= text.length) {
    const nl = text.indexOf('\n', pos);
    const lineEnd = nl < 0 ? text.length : nl;
    const line = text.slice(pos, lineEnd).replace(/\r$/, '');
    if (line === '---') {
      const end = nl < 0 ? text.length : nl + 1;
      return { start: 0, end, bodyStart, bodyEnd: pos };
    }
    if (nl < 0) break;
    pos = nl + 1;
  }
  return null;
}

function isTagNameBoundary(ch) {
  return ch === '>' || ch === '/' || ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r';
}

function findRuntimeInterfaceSpans(raw) {
  const text = String(raw ?? '');
  if (!text) return [];
  const lower = text.toLowerCase();
  const detailsSpans = [];

  // 1. Linear indexOf scan for <details ...><summary ...>...runtime interface...</summary>...</details>.
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
      sumStart++;
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
    if (/[\r\n]/.test(sumInner) || !/runtime\s+interface/i.test(sumInner)) {
      pos = sumClose + 10;
      continue;
    }
    const detClose = lower.indexOf('</details>', sumClose + 10);
    if (detClose < 0) break;
    detailsSpans.push({ start: detOpen, end: detClose + 10, bodyStart: sumClose + 10, bodyEnd: detClose });
    pos = detClose + 10;
  }

  // 2. Linear line-based scan for `## Runtime interface` headings through next heading or EOF,
  // tracking sorted detailsSpans with a monotonic pointer for strict O(N) runtime.
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

    while (detIdx < detailsSpans.length && detailsSpans[detIdx].end <= lineStart) detIdx++;
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
      const closeMatch = /^ {0,3}(`{3,}|~{3,})\s*$/.exec(line);
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

  const spans = [...detailsSpans, ...headingSpans].sort((a, b) => a.start - b.start || a.end - b.end);
  const merged = [];
  for (const span of spans) {
    if (!merged.length || span.start >= merged.at(-1).end) merged.push(span);
  }
  return merged;
}

function hasRuntimeInterfaceMetadata(raw) {
  return findRuntimeInterfaceSpans(raw).length > 0;
}

const NATIVE_ONLY_KIND_LINE_RE = /^[ \t]*kind[ \t]*:[ \t]*(?:['"])?native-only(?:['"])?[ \t]*(?:#[^\r\n]*)?$/i;

function hasNativeOnlyFrontmatter(raw) {
  const fm = findFrontmatterRange(raw);
  if (!fm) return false;
  const body = String(raw ?? '').slice(fm.bodyStart, fm.bodyEnd);
  for (const line of body.split(/\r?\n/)) {
    if (NATIVE_ONLY_KIND_LINE_RE.test(line)) return true;
  }
  return false;
}

function extractRuntimeInterfaceObjects(raw) {
  const text = String(raw ?? '');
  const spans = findRuntimeInterfaceSpans(text);
  if (!spans.length) return [];
  const objects = [];
  for (const span of spans) {
    const { fences } = scanMarkdownLinesAndFences(text.slice(span.bodyStart, span.bodyEnd));
    for (const fence of fences) {
      if (fence.lang !== 'json' && fence.lang !== '') continue;
      try {
        const parsed = JSON.parse(fence.bodyLines.map(item => item.text).join('\n'));
        if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) objects.push(parsed);
      } catch {}
    }
  }
  return objects;
}

function isNativeOnlyPrompt(raw) {
  if (hasNativeOnlyFrontmatter(raw)) return true;
  return extractRuntimeInterfaceObjects(raw).some(obj => obj.kind === 'native-only');
}

function stripMetadataSpans(raw, preserveLines) {
  const text = String(raw ?? '');
  const ranges = [];
  const fm = findFrontmatterRange(text);
  if (fm) ranges.push({ start: fm.start, end: fm.end });
  for (const span of findRuntimeInterfaceSpans(text)) {
    ranges.push({ start: span.start, end: span.end });
  }
  if (!ranges.length) return text;
  ranges.sort((a, b) => a.start - b.start || a.end - b.end);
  let out = '';
  let cursor = 0;
  for (const range of ranges) {
    const start = Math.max(range.start, cursor);
    if (range.end <= start) continue;
    out += text.slice(cursor, start);
    if (preserveLines) out += blankPreservingLines(text.slice(start, range.end));
    cursor = range.end;
  }
  out += text.slice(cursor);
  return out;
}

function stripPromptMetadataPreservingLines(raw) {
  return stripMetadataSpans(raw, true);
}

export function stripPromptMetadata(raw) {
  return stripMetadataSpans(raw, false);
}

function countPromptProseLines(raw) {
  const cleaned = stripPromptMetadata(raw).replace(/\s+$/, '');
  return cleaned ? cleaned.split(/\r?\n/).length : 0;
}

function countFileLines(raw) {
  const text = String(raw ?? '').replace(/\r?\n$/, '');
  return text ? text.split(/\r?\n/).length : 0;
}

function isDeclarativeJson(lang, bodyText) {
  const trimmed = bodyText.trim();
  if (!trimmed) return true;
  if (lang !== 'json' && lang !== 'jsonc' && !trimmed.startsWith('{') && !trimmed.startsWith('[')) return false;
  try {
    const parsed = JSON.parse(trimmed);
    return typeof parsed === 'object' && parsed !== null;
  } catch {
    return false;
  }
}

function findImperativeToken(lineText) {
  for (const pattern of IMPERATIVE_PATTERNS) {
    const match = pattern.exec(lineText);
    if (match) return match[0].trim();
  }
  return null;
}

function scanMarkdownLinesAndFences(cleanedText) {
  const lines = cleanedText.split(/\r?\n/);
  const fences = [];
  const proseLines = [];
  let inComment = false;
  let activeFence = null;

  for (let i = 0; i < lines.length; i++) {
    let line = lines[i];
    const lineNo = i + 1;

    if (activeFence) {
      const closeMatch = line.match(/^ {0,3}(`{3,}|~{3,})\s*$/);
      if (closeMatch && closeMatch[1][0] === activeFence.char && closeMatch[1].length >= activeFence.len) {
        fences.push(activeFence);
        activeFence = null;
      } else {
        activeFence.bodyLines.push({ lineNo, text: line });
      }
      continue;
    }

    if (inComment) {
      const endIdx = line.indexOf('-->');
      if (endIdx < 0) continue;
      inComment = false;
      line = ' '.repeat(endIdx + 3) + line.slice(endIdx + 3);
    }

    while (true) {
      const openIdx = line.indexOf('<!--');
      if (openIdx < 0) break;
      const closeIdx = line.indexOf('-->', openIdx + 4);
      if (closeIdx < 0) {
        line = line.slice(0, openIdx);
        inComment = true;
        break;
      }
      line = line.slice(0, openIdx) + ' '.repeat(closeIdx + 3 - openIdx) + line.slice(closeIdx + 3);
    }

    const openMatch = line.match(/^ {0,3}(`{3,}|~{3,})(.*)$/);
    if (openMatch && !(openMatch[1][0] === '`' && openMatch[2].includes('`'))) {
      const info = openMatch[2].trim();
      const lang = (info.split(/[\s{`~]/)[0] ?? '').toLowerCase();
      activeFence = {
        openLine: lineNo,
        char: openMatch[1][0],
        len: openMatch[1].length,
        lang,
        bodyLines: [],
      };
      continue;
    }

    proseLines.push({ lineNo, text: line });
  }
  if (activeFence) fences.push(activeFence);
  return { fences, proseLines };
}

function collectPromptCodeBlockFindings(text, { path = 'prompts/module.prompt.md' } = {}) {
  const isNativeOnly = hasNativeOnlyFrontmatter(text);
  const cleaned = stripPromptMetadataPreservingLines(text);
  const { fences } = scanMarkdownLinesAndFences(cleaned);
  const nonMermaid = fences.filter(f => f.lang !== 'mermaid' && f.lang !== 'pdd-boundary');
  if (!nonMermaid.length) return [];

  const records = [];
  const countedFences = [];
  let totalBodyLines = 0;

  for (const fence of nonMermaid) {
    if (isNativeOnly && DECLARATIVE_SCHEMA_FENCE_LANGS.has(fence.lang)) continue;
    countedFences.push(fence);
    const count = fence.bodyLines.length;
    totalBodyLines += count;
    if (count > PROMPT_FENCE_LINE_LIMIT) {
      records.push({
        line: fence.openLine,
        order: 1,
        code: 'prompt-code-fence-length',
        category: 'prompt code block',
        detail: `Non-mermaid code fence spans ${count} lines (recommended <= ${PROMPT_FENCE_LINE_LIMIT}). Replace long code or schema blocks with plain-English rules, a Markdown table, or a mermaid diagram.`,
      });
    }
    const rawBody = fence.bodyLines.map(item => item.text).join('\n');
    if (!isDeclarativeJson(fence.lang, rawBody)) {
      for (const item of fence.bodyLines) {
        const token = findImperativeToken(item.text);
        if (token) {
          records.push({
            line: item.lineNo,
            order: 2,
            code: 'prompt-imperative-code',
            category: 'prompt code block',
            detail: `Fenced block contains imperative code ("${token}"). Describe observable inputs, outputs and failure rules in prose instead of embedding code in prompts.`,
          });
          break;
        }
      }
    }
  }

  if (totalBodyLines > PROMPT_FENCE_TOTAL_LIMIT && countedFences.length > 0) {
    const firstLine = countedFences[0].openLine;
    records.push({
      line: firstLine,
      order: 0,
      code: 'prompt-code-fence-total',
      category: 'prompt code block',
      detail: `Prompt contains ${totalBodyLines} non-mermaid fenced lines across ${countedFences.length} blocks (recommended <= ${PROMPT_FENCE_TOTAL_LIMIT} total). Move implementation details to tests or summarize contracts in prose and tables.`,
    });
  }

  records.sort((a, b) => a.line - b.line || a.order - b.order);
  return records.map(r => ({
    ...r,
    filePath: path,
    warning: `Warning: ${r.category}: ${path}:${r.line} [${r.code}] ${r.detail}`,
  }));
}

export function lintPromptCodeBlocks(text, { path = 'prompts/module.prompt.md' } = {}) {
  return collectPromptCodeBlockFindings(text, { path }).map(r => r.warning);
}

function isSingleCallSpan(span, openIdx) {
  if (openIdx < 0 || !span.endsWith(')')) return false;
  let depth = 0;
  let quote = null;
  for (let i = openIdx; i < span.length; i++) {
    const ch = span[i];
    if (quote) {
      if (ch === '\\') { i++; continue; }
      if (ch === quote) quote = null;
      continue;
    }
    if (ch === '\'' || ch === '"' || ch === '`') {
      quote = ch;
      continue;
    }
    if (ch === '(') depth++;
    else if (ch === ')') {
      depth--;
      if (depth === 0) return i === span.length - 1;
      if (depth < 0) return false;
    }
  }
  return false;
}

function isValidPortCandidate(port, op, sqlSchemaColumns = EMPTY_STRING_SET, declaredPortPrefixes = EMPTY_STRING_SET) {
  if (port.length < 2 || op.length < 2) return false;
  if (VERSION_TOKEN_RE.test(port) || VERSION_TOKEN_RE.test(op)) return false;
  const portLower = port.toLowerCase();
  const opLower = op.toLowerCase();
  const fullLower = `${portLower}.${opLower}`;
  if (NON_PORT_FILE_EXTENSIONS.has(opLower)) return false;
  if (NON_PORT_EXACT_FILENAMES.has(fullLower)) return false;
  if (NON_PORT_TLDS.has(opLower)) return false;
  if (NON_PORT_PREFIXES.has(portLower) && !declaredPortPrefixes.has(port)) return false;
  if (NON_PORT_JS_MEMBERS.has(op)) return false;
  if (sqlSchemaColumns.has(fullLower)) return false;
  return true;
}

function stripUrlsAndMarkdownLinks(line) {
  let out = String(line ?? '');
  if (out.includes('://')) {
    const parts = [];
    let pos = 0;
    while (pos < out.length) {
      const idx = out.indexOf('://', pos);
      if (idx < 0) {
        parts.push(out.slice(pos));
        break;
      }
      let schemeStart = idx;
      const minStart = Math.max(pos, idx - 33);
      while (schemeStart > minStart && /[A-Za-z0-9+.-]/.test(out[schemeStart - 1])) schemeStart--;
      const hasPriorSchemeChar = schemeStart > pos && /[A-Za-z0-9+.-]/.test(out[schemeStart - 1]);
      const scheme = out.slice(schemeStart, idx);
      if (!hasPriorSchemeChar && /^[a-z][a-z0-9+.-]{0,31}$/i.test(scheme)) {
        parts.push(out.slice(pos, schemeStart), ' ');
        let urlEnd = idx + 3;
        while (urlEnd < out.length && !/\s/.test(out[urlEnd])) urlEnd++;
        pos = urlEnd;
      } else {
        parts.push(out.slice(pos, idx + 3));
        pos = idx + 3;
      }
    }
    out = parts.join('');
  }
  if (out.includes('](')) {
    out = out.replace(/\[([^\[\]\r\n]*)\]\(([^()\r\n]*)\)/g, (_m, label) => ` ${label} `);
  }
  return out;
}

function extractInlineBacktickSpans(line) {
  if (!line.includes('`')) return { spans: [], outside: line };
  const spans = [];
  const outsideParts = [];
  let i = 0;
  while (i < line.length) {
    const tickPos = line.indexOf('`', i);
    if (tickPos < 0) {
      outsideParts.push(line.slice(i));
      break;
    }
    if (tickPos > i) outsideParts.push(line.slice(i, tickPos));
    let ticks = 0;
    while (tickPos + ticks < line.length && line[tickPos + ticks] === '`') ticks++;
    const delim = '`'.repeat(ticks);
    const closeIdx = line.indexOf(delim, tickPos + ticks);
    if (closeIdx < 0) {
      outsideParts.push(line.slice(tickPos));
      break;
    }
    spans.push(line.slice(tickPos + ticks, closeIdx));
    outsideParts.push(' ');
    i = closeIdx + ticks;
  }
  return { spans, outside: outsideParts.join('') };
}

function scanDottedPortTokens(text, onPair) {
  if (!text.includes('.')) return;
  if (text.includes('.{')) {
    for (const m of text.matchAll(INLINE_BRACE_PORT_SCAN_RE)) {
      for (const op of m[2].split(',').map(s => s.trim()).filter(Boolean)) {
        onPair(m[1], op);
      }
    }
  }
  const tokenRe = /[A-Za-z0-9_./:@-]+/g;
  let m;
  while ((m = tokenRe.exec(text)) !== null) {
    let tok = m[0];
    while (tok.endsWith('.')) tok = tok.slice(0, -1);
    const dot = tok.indexOf('.');
    if (dot <= 0 || dot !== tok.lastIndexOf('.')) continue;
    if (tok.includes('/') || tok.includes(':') || tok.includes('@')) continue;
    const port = tok.slice(0, dot);
    const op = tok.slice(dot + 1);
    if (SIMPLE_IDENT_RE.test(port) && SIMPLE_IDENT_RE.test(op)) {
      onPair(port, op);
    }
  }
}

function splitMarkdownTableRow(line) {
  let trimmed = line.trim();
  if (!trimmed.includes('|')) return null;
  if (trimmed.startsWith('|')) trimmed = trimmed.slice(1);
  if (trimmed.endsWith('|')) trimmed = trimmed.slice(0, -1);
  return trimmed.split('|').map(cell => cell.trim());
}

function isMarkdownTableSeparator(line) {
  if (!line.includes('|') || !line.includes('--')) return false;
  return /^\|?\s*:?-{2,}:?\s*(?:\|\s*:?-{2,}:?\s*)+\|?$/.test(line.trim());
}

function buildSqlParenMap(sql) {
  const parenMap = new Map();
  const stack = [];
  let quote = null;
  for (let i = 0; i < sql.length; i++) {
    const ch = sql[i];
    const next = sql[i + 1];
    if (quote) {
      if (ch === quote && next === quote) { i++; continue; }
      if (ch === quote) quote = null;
      continue;
    }
    if (ch === '-' && next === '-') {
      const nl = sql.indexOf('\n', i + 2);
      i = nl < 0 ? sql.length : nl;
      continue;
    }
    if (ch === '/' && next === '*') {
      const end = sql.indexOf('*/', i + 2);
      i = end < 0 ? sql.length : end + 1;
      continue;
    }
    if (ch === '\'' || ch === '"') {
      quote = ch;
      continue;
    }
    if (ch === '(') {
      stack.push({ openIdx: i, commas: [] });
    } else if (ch === ',') {
      if (stack.length > 0) stack.at(-1).commas.push(i);
    } else if (ch === ')') {
      if (stack.length > 0) {
        const frame = stack.pop();
        parenMap.set(frame.openIdx, { closeIdx: i, commas: frame.commas });
      }
    } else if (ch === ';') {
      stack.length = 0;
    }
  }
  return parenMap;
}

function extractSqlSchemaColumns(fences) {
  const cols = new Set();
  const createRe = /\bCREATE\s+(?:(?:TEMP(?:ORARY)?|UNLOGGED|VIRTUAL)\s+)*(?:TABLE|VIEW)\s+(?:IF\s+NOT\s+EXISTS\s+)?(?:["`\[]?[A-Za-z_][A-Za-z0-9_]*["`\]]?\.)?["`\[]?([A-Za-z_][A-Za-z0-9_]*)["`\]]?(?:\s+USING\s+[A-Za-z_][A-Za-z0-9_]*)?\s*\(/gi;
  const alterAddRe = /\bALTER\s+TABLE\s+(?:IF\s+EXISTS\s+)?(?:["`\[]?[A-Za-z_][A-Za-z0-9_]*["`\]]?\.)?["`\[]?([A-Za-z_][A-Za-z0-9_]*)["`\]]?\s+ADD\s+(?:COLUMN\s+)?(?:IF\s+NOT\s+EXISTS\s+)?["`\[]?([A-Za-z_][A-Za-z0-9_]*)["`\]]?/gi;

  for (const fence of fences) {
    if (!SQL_FENCE_LANGS.has(fence.lang)) continue;
    const rawSql = fence.bodyLines.map(item => item.text).join('\n');
    const parenMap = rawSql.includes('(') && rawSql.includes(')') ? buildSqlParenMap(rawSql) : null;
    let m;
    if (parenMap && parenMap.size > 0) {
      createRe.lastIndex = 0;
      while ((m = createRe.exec(rawSql)) !== null) {
        const table = m[1].toLowerCase();
        const openIdx = createRe.lastIndex - 1;
        const entry = parenMap.get(openIdx);
        if (!entry) continue;
        let segStart = openIdx + 1;
        const boundaries = [...entry.commas, entry.closeIdx];
        for (const boundary of boundaries) {
          const cleanedSeg = rawSql
            .slice(segStart, boundary)
            .replace(/--[^\r\n]*/g, ' ')
            .replace(/\/\*[\s\S]*?\*\//g, ' ')
            .trim();
          segStart = boundary + 1;
          const colMatch = /^["`\[]?([A-Za-z_][A-Za-z0-9_]*)["`\]]?(?:\s+|$)/.exec(cleanedSeg);
          if (!colMatch) continue;
          const col = colMatch[1].toLowerCase();
          if (!SQL_TABLE_CONSTRAINT_KEYWORDS.has(col)) cols.add(`${table}.${col}`);
        }
        createRe.lastIndex = entry.closeIdx + 1;
      }
    }
    alterAddRe.lastIndex = 0;
    while ((m = alterAddRe.exec(rawSql)) !== null) {
      const table = m[1].toLowerCase();
      const col = m[2].toLowerCase();
      if (!SQL_TABLE_CONSTRAINT_KEYWORDS.has(col)) cols.add(`${table}.${col}`);
    }
  }
  return cols;
}

function extractDependencyLinkTargets(raw, promptPath) {
  const cleaned = stripPromptMetadataPreservingLines(raw);
  const { proseLines } = scanMarkdownLinesAndFences(cleaned);
  let inDeps = false;
  const targets = new Set();
  const baseDir = posix.dirname(promptPath);
  const linkRe = /\[[^\[\]\r\n]*\]\(\s*<?([^()\s<>#\r\n]+)(?:#[^()\s<>#\r\n]*)?>?\s*\)/g;

  for (const { text: line } of proseLines) {
    const h2 = /^ {0,3}##\s+(.+)$/.exec(line);
    if (h2) {
      inDeps = /^dependencies\b/i.test(h2[1].trim());
      continue;
    }
    if (!inDeps) continue;
    let m;
    while ((m = linkRe.exec(line)) !== null) {
      const rawTarget = m[1].trim();
      if (!rawTarget || /^[a-z][a-z0-9+.-]*:/i.test(rawTarget)) continue;
      const resolved = posix.normalize(baseDir === '.' ? rawTarget : posix.join(baseDir, rawTarget));
      if (canonicalRepoPath(resolved) && resolved !== promptPath) targets.add(resolved);
    }
  }
  return [...targets].sort();
}

function cleanSingleIdentifier(raw, { allowCallArgs = false } = {}) {
  let s = String(raw ?? '').trim();
  s = s.replace(/^\*\*|\*\*$/g, '').replace(/^`|`$/g, '').trim();
  if (allowCallArgs) {
    const paren = s.indexOf('(');
    if (paren > 0 && isSingleCallSpan(s, paren)) s = s.slice(0, paren).trim();
  }
  if (s.length < 2 || VERSION_TOKEN_RE.test(s) || !SIMPLE_IDENT_RE.test(s)) return null;
  return s;
}

function extractLeadingSimpleIdentifier(rest, { allowCallArgs = false } = {}) {
  const trimmed = String(rest ?? '').trim();
  if (!trimmed) return null;
  const backtick = /^`([^`\r\n]+)`/.exec(trimmed);
  if (backtick) {
    const inner = backtick[1].trim();
    if (inner.includes('.')) return null;
    return cleanSingleIdentifier(inner, { allowCallArgs });
  }
  const bold = /^\*\*([^*\r\n]+)\*\*/.exec(trimmed);
  if (bold) {
    const inner = bold[1].trim();
    if (inner.includes('.')) return null;
    return cleanSingleIdentifier(inner, { allowCallArgs });
  }
  const bare = /^([a-z][a-zA-Z0-9_-]*)(?:\s*(\([^()\r\n]*\)))?(?=\s*(?::|—|–|->|=>|-\s|$))/.exec(trimmed);
  if (!bare) return null;
  if (bare[2] && !allowCallArgs) return null;
  return cleanSingleIdentifier(bare[1], { allowCallArgs: false });
}

function extractOpsFromTableCell(cell) {
  const ops = [];
  const trimmed = String(cell ?? '').trim();
  if (!trimmed) return ops;
  const parts = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < trimmed.length; i++) {
    const ch = trimmed[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth = Math.max(0, depth - 1);
    else if (depth === 0 && (ch === ',' || ch === '/' || ch === ';')) {
      parts.push(trimmed.slice(start, i));
      start = i + 1;
    }
  }
  parts.push(trimmed.slice(start));
  for (const part of parts) {
    const ident = cleanSingleIdentifier(part, { allowCallArgs: true });
    if (ident) ops.push(ident);
  }
  return ops;
}

function classifyDependencyTable(headers, subheadingPort = null) {
  let portNameCol = -1;
  let opCol = -1;
  for (let c = 0; c < headers.length; c++) {
    const h = headers[c];
    if (PORT_TABLE_COL_EXCLUDE_RE.test(h) && !DEP_TABLE_PORT_NAME_COL_RE.test(h) && !DEP_TABLE_OP_COL_RE.test(h)) continue;
    if (opCol < 0 && DEP_TABLE_OP_COL_RE.test(h) && !DEP_TABLE_PORT_NAME_COL_RE.test(h)) {
      opCol = c;
    } else if (portNameCol < 0 && DEP_TABLE_PORT_NAME_COL_RE.test(h) && !DEP_TABLE_OP_COL_RE.test(h) && !PORT_TABLE_COL_EXCLUDE_RE.test(h)) {
      portNameCol = c;
    }
  }
  if (portNameCol >= 0 && opCol >= 0) return { portNameCol, opCol, subheadingPort: null };
  if (subheadingPort && opCol >= 0) return { portNameCol: -1, opCol, subheadingPort };
  return null;
}

function extractDeclaredPortsFromDependency(raw, { isPrompt = true } = {}) {
  const mentioned = new Set();
  const display = new Set();
  const addDeclaredPair = (port, op) => {
    if (port.length < 2 || op.length < 2) return;
    if (VERSION_TOKEN_RE.test(port) || VERSION_TOKEN_RE.test(op)) return;
    const opLower = op.toLowerCase();
    const fullLower = `${port.toLowerCase()}.${opLower}`;
    if (NON_PORT_FILE_EXTENSIONS.has(opLower) || NON_PORT_EXACT_FILENAMES.has(fullLower) || NON_PORT_TLDS.has(opLower)) return;
    const full = `${port}.${op}`;
    mentioned.add(full);
    display.add(full);
  };

  if (isPrompt) {
    for (const iface of extractRuntimeInterfaceObjects(raw)) {
      if (!Array.isArray(iface.resources)) continue;
      for (const res of iface.resources) {
        if (typeof res?.name !== 'string' || !res.name.trim()) continue;
        for (const op of (Array.isArray(res.operations) ? res.operations : [])) {
          if (typeof op?.name === 'string' && op.name.trim()) {
            const pair = `${res.name.trim()}.${op.name.trim()}`;
            mentioned.add(pair);
            display.add(pair);
          }
        }
      }
    }
  }

  const cleaned = stripPromptMetadata(raw);
  const { proseLines, fences } = scanMarkdownLinesAndFences(cleaned);

  // 1. Structural declarations in proseLines: split-column tables, nested bullets under ## Ports, and subheadings under ## Ports.
  let inPortsSection = false;
  let portsSectionDepth = 0;
  let subheadingPort = null;
  let subheadingDepth = 0;
  let bulletPort = null;
  let bulletIndent = -1;
  let inTable = false;
  let tableSpec = null;

  for (let idx = 0; idx < proseLines.length; idx++) {
    const line = proseLines[idx].text;
    const headingMatch = /^ {0,3}(#{2,6})\s+(.+)$/.exec(line);
    if (headingMatch) {
      const depth = headingMatch[1].length;
      const title = headingMatch[2].trim();
      inTable = false;
      tableSpec = null;
      bulletPort = null;
      bulletIndent = -1;
      if (inPortsSection && depth > portsSectionDepth) {
        const cleanedTitle = title.replace(/\b(?:port|resource|adapter|interface)\b/gi, '').trim();
        const ident = cleanSingleIdentifier(cleanedTitle, { allowCallArgs: false });
        if (ident) {
          subheadingPort = ident;
          subheadingDepth = depth;
        } else if (depth <= subheadingDepth) {
          subheadingPort = null;
          subheadingDepth = 0;
        }
      } else if (!NETWORK_PORT_HEADING_RE.test(title) && DEP_PORTS_HEADING_RE.test(title)) {
        inPortsSection = true;
        portsSectionDepth = depth;
        subheadingPort = null;
        subheadingDepth = 0;
      } else if (depth <= portsSectionDepth) {
        inPortsSection = false;
        portsSectionDepth = 0;
        subheadingPort = null;
        subheadingDepth = 0;
      }
      continue;
    }

    if (line.includes('|') && idx + 1 < proseLines.length && isMarkdownTableSeparator(proseLines[idx + 1].text)) {
      const headers = splitMarkdownTableRow(line) ?? [];
      inTable = true;
      tableSpec = classifyDependencyTable(headers, subheadingPort);
      bulletPort = null;
      bulletIndent = -1;
      continue;
    }
    if (inTable) {
      if (isMarkdownTableSeparator(line)) continue;
      if (!line.includes('|')) {
        inTable = false;
        tableSpec = null;
      } else {
        if (tableSpec) {
          const cells = splitMarkdownTableRow(line) ?? [];
          const portName = tableSpec.portNameCol >= 0
            ? cleanSingleIdentifier(cells[tableSpec.portNameCol], { allowCallArgs: false })
            : tableSpec.subheadingPort;
          if (portName && tableSpec.opCol < cells.length) {
            for (const op of extractOpsFromTableCell(cells[tableSpec.opCol])) {
              addDeclaredPair(portName, op);
            }
          }
        }
        continue;
      }
    }

    if (inPortsSection) {
      const bm = BULLET_LINE_RE.exec(line);
      if (bm) {
        const indent = bm[1].replace(/\t/g, '  ').length;
        const rest = bm[2].trim();
        if (subheadingPort) {
          const op = extractLeadingSimpleIdentifier(rest, { allowCallArgs: true });
          if (op) addDeclaredPair(subheadingPort, op);
        } else if (bulletPort && indent > bulletIndent) {
          const op = extractLeadingSimpleIdentifier(rest, { allowCallArgs: true });
          if (op) addDeclaredPair(bulletPort, op);
        } else {
          const parentIdent = extractLeadingSimpleIdentifier(rest, { allowCallArgs: false });
          if (parentIdent) {
            bulletPort = parentIdent;
            bulletIndent = indent;
          } else {
            bulletPort = null;
            bulletIndent = -1;
          }
        }
      } else if (line.trim()) {
        bulletPort = null;
        bulletIndent = -1;
      }
    }
  }

  // 2. Inline dotted `<port>.<op>` and `<port>.{op1, op2}` declarations across prose and schema fences.
  const scanLines = proseLines.map(item => item.text);
  for (const fence of fences) {
    if (!isPrompt || DECLARATIVE_SCHEMA_FENCE_LANGS.has(fence.lang)) {
      for (const item of fence.bodyLines) scanLines.push(item.text);
    }
  }

  for (const line of scanLines) {
    if (!line.includes('.')) continue;
    const stripped = stripUrlsAndMarkdownLinks(line);
    scanDottedPortTokens(stripped, (port, op) => {
      if (port.length < 2 || op.length < 2) return;
      if (VERSION_TOKEN_RE.test(port) || VERSION_TOKEN_RE.test(op)) return;
      const opLower = op.toLowerCase();
      const fullLower = `${port.toLowerCase()}.${opLower}`;
      if (NON_PORT_FILE_EXTENSIONS.has(opLower) || NON_PORT_EXACT_FILENAMES.has(fullLower) || NON_PORT_TLDS.has(opLower)) return;
      const full = `${port}.${op}`;
      mentioned.add(full);
      if (isValidPortCandidate(port, op)) display.add(full);
    });
  }
  return { mentioned, display };
}

function isDomainPortWiringHeading(title) {
  return !NETWORK_PORT_HEADING_RE.test(title) && DOMAIN_PORT_HEADING_RE.test(title);
}

function hasDomainPortWiringCue(outsideText, fullLine = outsideText) {
  const raw = String(outsideText ?? '');
  if (!DOMAIN_PORT_CUE_RE.test(raw)) return false;
  let scrubbed = String(fullLine ?? raw);
  for (const re of NON_PORT_IDIOM_PATTERNS) {
    scrubbed = scrubbed.replace(re, ' ');
  }
  scrubbed = extractInlineBacktickSpans(scrubbed).outside;
  if (DOMAIN_PORT_DIRECT_CUE_RE.test(scrubbed)) return true;
  if (!DOMAIN_PORT_BIND_WORD_RE.test(scrubbed)) return false;
  return DOMAIN_PORT_BIND_CONTEXT_RE.test(scrubbed) || DIRECT_BIND_PORT_OP_RE.test(String(fullLine ?? ''));
}

function classifyNativeTable(headers, inPortSection) {
  const portCols = [];
  let portNameCol = -1;
  let opCol = -1;
  for (let c = 0; c < headers.length; c++) {
    const h = headers[c];
    if (PORT_TABLE_COL_EXCLUDE_RE.test(h)) continue;
    const isPortCol = PORT_TABLE_COL_PORT_RE.test(h) || (inPortSection && PORT_TABLE_COL_IN_SECTION_RE.test(h));
    if (isPortCol) portCols.push(c);
    if (opCol < 0 && DEP_TABLE_OP_COL_RE.test(h) && !DEP_TABLE_PORT_NAME_COL_RE.test(h)) {
      opCol = c;
    } else if (portNameCol < 0 && DEP_TABLE_PORT_NAME_COL_RE.test(h) && !DEP_TABLE_OP_COL_RE.test(h)) {
      portNameCol = c;
    }
  }
  const splitPair = portNameCol >= 0 && opCol >= 0 ? { portNameCol, opCol } : null;
  if (!portCols.length && !splitPair) return null;
  return { portCols, splitPair };
}

function extractLeadingBulletPort(rest) {
  const trimmed = String(rest ?? '').trim();
  if (!trimmed) return null;
  const backtick = /^`([^`\r\n]+)`/.exec(trimmed);
  if (backtick) {
    const span = backtick[1].trim();
    let m = BARE_PORT_OP_RE.exec(span);
    if (m) return [m[1], m[2]];
    m = CALL_PORT_OP_RE.exec(span);
    if (m && isSingleCallSpan(span, m[0].length - 1)) return [m[1], m[2]];
    return null;
  }
  const bare = /^([a-z][a-zA-Z0-9_-]*)\.([a-z][a-zA-Z0-9_-]*)(?:\s*\([^()\r\n]*\))?(?=\s*(?::|—|–|->|=>|-\s|$))/.exec(trimmed);
  return bare ? [bare[1], bare[2]] : null;
}

function extractNativeOnlyPortReferences(proseLines, sqlSchemaColumns, { mentionedInDeps = EMPTY_STRING_SET, declaredPortPrefixes = EMPTY_STRING_SET } = {}) {
  const firstLineByPort = new Map();
  const recordPort = (port, op, lineNo) => {
    if (!isValidPortCandidate(port, op, sqlSchemaColumns, declaredPortPrefixes)) return;
    const key = `${port}.${op}`;
    if (!firstLineByPort.has(key)) firstLineByPort.set(key, lineNo);
  };

  const scanBacktickSpans = (spans, lineNo, { onlyDeclaredPrefixes = false } = {}) => {
    for (const rawSpan of spans) {
      const span = rawSpan.trim();
      if (!span) continue;
      let m = BARE_PORT_OP_RE.exec(span);
      if (m) {
        if (!onlyDeclaredPrefixes || declaredPortPrefixes.has(m[1])) recordPort(m[1], m[2], lineNo);
        continue;
      }
      m = CALL_PORT_OP_RE.exec(span);
      if (m && isSingleCallSpan(span, m[0].length - 1)) {
        if (!onlyDeclaredPrefixes || declaredPortPrefixes.has(m[1])) recordPort(m[1], m[2], lineNo);
        continue;
      }
      m = BRACE_PORT_OP_RE.exec(span);
      if (m) {
        if (!onlyDeclaredPrefixes || declaredPortPrefixes.has(m[1])) {
          for (const op of m[2].split(',').map(s => s.trim()).filter(Boolean)) {
            recordPort(m[1], op, lineNo);
          }
        }
      }
    }
  };

  const scanUnbacktickedText = (chunk, lineNo) => {
    if (!chunk.includes('.')) return;
    const cleanedChunk = stripUrlsAndMarkdownLinks(chunk);
    scanDottedPortTokens(cleanedChunk, (port, op) => recordPort(port, op, lineNo));
  };

  const scanScopedChunk = (chunk, lineNo) => {
    const { spans, outside } = extractInlineBacktickSpans(chunk);
    scanBacktickSpans(spans, lineNo);
    scanUnbacktickedText(outside, lineNo);
  };

  let inPortSection = false;
  let portSectionDepth = 0;
  let inMarkdownTable = false;
  let activeTableSpec = null;
  let inCueBulletList = false;
  let cueAwaitingList = false;
  let pendingBulletGroup = [];

  const flushBulletGroup = () => {
    if (!pendingBulletGroup.length) return;
    const hasKnownSibling = pendingBulletGroup.some(item => item.lead && mentionedInDeps.has(`${item.lead[0]}.${item.lead[1]}`));
    for (const item of pendingBulletGroup) {
      if (hasKnownSibling && item.lead) {
        recordPort(item.lead[0], item.lead[1], item.lineNo);
      } else {
        scanBacktickSpans(item.spans, item.lineNo, { onlyDeclaredPrefixes: true });
      }
    }
    pendingBulletGroup = [];
  };

  for (let idx = 0; idx < proseLines.length; idx++) {
    const { lineNo, text: line } = proseLines[idx];
    const headingMatch = /^ {0,3}(#{2,6})\s+(.+)$/.exec(line);
    if (headingMatch) {
      flushBulletGroup();
      const depth = headingMatch[1].length;
      const title = headingMatch[2].trim();
      if (isDomainPortWiringHeading(title)) {
        inPortSection = true;
        portSectionDepth = depth;
      } else if (depth <= portSectionDepth) {
        inPortSection = false;
        portSectionDepth = 0;
      }
      inMarkdownTable = false;
      activeTableSpec = null;
      inCueBulletList = false;
      cueAwaitingList = false;
      continue;
    }

    if (line.includes('|') && idx + 1 < proseLines.length && isMarkdownTableSeparator(proseLines[idx + 1].text)) {
      flushBulletGroup();
      const headers = splitMarkdownTableRow(line) ?? [];
      inMarkdownTable = true;
      activeTableSpec = classifyNativeTable(headers, inPortSection);
      inCueBulletList = false;
      cueAwaitingList = false;
      continue;
    }
    if (inMarkdownTable) {
      if (isMarkdownTableSeparator(line)) continue;
      if (!line.includes('|')) {
        inMarkdownTable = false;
        activeTableSpec = null;
      } else {
        if (activeTableSpec) {
          const cells = splitMarkdownTableRow(line) ?? [];
          for (const colIdx of activeTableSpec.portCols) {
            if (colIdx < cells.length) scanScopedChunk(cells[colIdx], lineNo);
          }
          if (activeTableSpec.splitPair) {
            const { portNameCol, opCol } = activeTableSpec.splitPair;
            if (portNameCol < cells.length && opCol < cells.length) {
              const portName = cleanSingleIdentifier(cells[portNameCol], { allowCallArgs: false });
              if (portName) {
                for (const op of extractOpsFromTableCell(cells[opCol])) {
                  recordPort(portName, op, lineNo);
                }
              }
            }
          }
        }
        continue;
      }
    }

    const trimmed = line.trim();
    if (!trimmed) {
      flushBulletGroup();
      if (cueAwaitingList) {
        cueAwaitingList = false;
      } else {
        inCueBulletList = false;
      }
      continue;
    }

    const bulletMatch = BULLET_LINE_RE.exec(line);
    const { spans, outside } = extractInlineBacktickSpans(line);
    const lineHasCue = hasDomainPortWiringCue(outside, line);

    if (bulletMatch) {
      cueAwaitingList = false;
      const lead = extractLeadingBulletPort(bulletMatch[2]);
      if (inPortSection || inCueBulletList || lineHasCue) {
        flushBulletGroup();
        if (lead) {
          // On a leading-port bullet (`- \`port.op\`: description` or `- \`port.op\` - description`), scan the LHS fully and only high-signal declared prefixes on the RHS.
          const body = bulletMatch[2];
          const sepIdx = (() => {
            let inTicks = false;
            for (let i = 0; i < body.length; i++) {
              if (body[i] === '`') { inTicks = !inTicks; continue; }
              if (inTicks) continue;
              if (body[i] === ':' || body[i] === '—' || body[i] === '–') return i;
              if ((body[i] === '-' || body[i] === '=') && body[i + 1] === '>') return i;
              if (body[i] === '-' && i > 0 && body[i - 1] === ' ' && body[i + 1] === ' ') return i;
            }
            return -1;
          })();
          if (sepIdx > 0) {
            scanScopedChunk(body.slice(0, sepIdx), lineNo);
            const rhs = extractInlineBacktickSpans(body.slice(sepIdx + 1));
            scanBacktickSpans(rhs.spans, lineNo, { onlyDeclaredPrefixes: true });
          } else {
            scanBacktickSpans(spans, lineNo);
            scanUnbacktickedText(outside, lineNo);
          }
        } else {
          scanBacktickSpans(spans, lineNo);
          scanUnbacktickedText(outside, lineNo);
        }
      } else {
        pendingBulletGroup.push({ lineNo, lead, spans });
      }
      continue;
    }

    flushBulletGroup();
    if (inPortSection || lineHasCue) {
      scanBacktickSpans(spans, lineNo);
      scanUnbacktickedText(outside, lineNo);
      inCueBulletList = lineHasCue;
      cueAwaitingList = lineHasCue && trimmed.endsWith(':');
    } else {
      inCueBulletList = false;
      cueAwaitingList = false;
      // Outside port-wiring sections/tables/cues: only flag high-signal <declaredPrefix>.<unknownOp> in backticks.
      scanBacktickSpans(spans, lineNo, { onlyDeclaredPrefixes: true });
    }
  }
  flushBulletGroup();

  return [...firstLineByPort.entries()]
    .map(([port, line]) => ({ port, line }))
    .sort((a, b) => a.line - b.line || a.port.localeCompare(b.port));
}

function collectNativeOnlyPortParityFindings(text, dependencySources, { path = 'prompts/service.prompt.md', dependencyPaths = [] } = {}) {
  if (!hasNativeOnlyFrontmatter(text)) return [];
  const rawDeps = Array.isArray(dependencySources) ? dependencySources : (dependencySources ? [dependencySources] : []);
  const deps = rawDeps
    .map(item => (typeof item === 'string' ? { path: '', text: item, isPrompt: true } : item))
    .filter(item => item && typeof item.text === 'string');
  if (!deps.length) return [];

  const mentionedInDeps = new Set();
  const displayPorts = new Set();
  const declaredPortPrefixes = new Set();
  for (const dep of deps) {
    const { mentioned, display } = extractDeclaredPortsFromDependency(dep.text, { isPrompt: dep.isPrompt !== false });
    for (const p of mentioned) mentionedInDeps.add(p);
    for (const p of display) {
      displayPorts.add(p);
      const dot = p.indexOf('.');
      if (dot > 0) declaredPortPrefixes.add(p.slice(0, dot));
    }
  }

  const cleaned = stripPromptMetadataPreservingLines(text);
  const { fences, proseLines } = scanMarkdownLinesAndFences(cleaned);
  const sqlSchemaColumns = extractSqlSchemaColumns(fences);
  const refs = extractNativeOnlyPortReferences(proseLines, sqlSchemaColumns, { mentionedInDeps, declaredPortPrefixes });
  if (!refs.length) return [];

  const linkedLabels = (dependencyPaths.length ? dependencyPaths : deps.map(d => d.path).filter(Boolean)).sort();
  const depSummary = linkedLabels.length ? linkedLabels.join(', ') : 'linked checkable dependencies';
  const sortedDisplay = [...displayPorts].sort();
  const declaredHint = sortedDisplay.length
    ? `; declared ports: ${sortedDisplay.slice(0, 12).join(', ')}${sortedDisplay.length > 12 ? ', …' : ''}`
    : '';

  const findings = [];
  for (const { port, line } of refs) {
    if (mentionedInDeps.has(port)) continue;
    const detail = `Port "${port}" wired in native-only prompt is not declared by linked checkable dependencies (${depSummary}${declaredHint}).`;
    findings.push({
      filePath: path,
      line,
      order: 4,
      code: 'native-only-unknown-port',
      category: 'native-only port parity',
      defaultSeverity: 'error',
      detail,
      error: `Error: native-only port parity: ${path}:${line} [native-only-unknown-port] ${detail}`,
    });
  }
  return findings;
}

export function lintNativeOnlyPortParity(text, dependencySources, { path = 'prompts/service.prompt.md', dependencyPaths = [] } = {}) {
  return collectNativeOnlyPortParityFindings(text, dependencySources, { path, dependencyPaths }).map(r => r.error);
}

const NATIVE_CONTRACT_BOUNDARY_HEADING_RE = /\b(?:boundary|runtime|storage|schema|ddl|database|table|tables|sqlite|postgres|transaction|transactions|locking|lock|concurrency|http|https|wire|route|routes|endpoint|endpoints|api|protocol|cli|subcommands?|flags?|commands?|os|process|subprocess|sandbox|tty|pty|socket|filesystem|file\s+layout|auth|authentication|authorization|crypto|kms|tls|execution|adapter|driver|transport|persistence|layout|contract|interface)\b/i;
const NATIVE_CONTRACT_ERROR_HEADING_RE = /\b(?:errors?|failures?|failure\s+modes?|error\s+mapping|degradation|refusals?|recovery|fallback|timeouts?|retries|exceptions?)\b/i;
const NATIVE_CONTRACT_VERIFY_HEADING_RE = /\b(?:verification|verify|native\s+tests?|native\s+test\s+cases?|native\s+verification|smoke\s+tests?|smoke\s+checks?|integration\s+tests?|real[- ]host|live[- ]host|end[- ]to[- ]end|e2e|test\s+cases?|testing)\b/i;
const NATIVE_CONTRACT_ERROR_CUE_RE = /\b(?:exit\s+code|status\s+code|(?:http|status(?:\s+code)?|error)\s+[45]\d\d|stderr|error\s+mapping|error\s+code|fail(?:s|ed|ure)?\s+closed|rollback|timeout|timed?\s+out|retry|retries|reject(?:s|ed)?|refus(?:e|es|ed)|never\s+throws?|throws?\s+on|unreadable|unavailable|degrade(?:s|d)?|offline|permission\s+denied|enoent|eperm|eacces|econnrefused|deadlock|busy|conflict|lock\s+contention|atomic(?:ally)?)\b/i;
const NATIVE_CONTRACT_VERIFY_CUE_RE = /\b(?:real[- ]host|live[- ]host|live[- ]local|--live-local|smoke\s+(?:test|tests|check|checks)|integration\s+(?:test|tests)|native\s+(?:test|tests|verification|smoke|probe|probes)|non[- ]mocked|real\s+(?:binary|subprocess|process|sandbox|tty|device|sqlite|postgres|database|driver|server|http|socket|filesystem|kernel|host))\b/i;
const PORT_WIRING_PHRASE_RE = /\b(?:port\s+wiring|port\s+bindings?|bound\s+ports?|wired\s+ports?|injected\s+ports?|external\s+ports?|port\s+adapters?|port\s+map(?:ping)?|port\s+interface|port\s+contract|dependency\s+wiring|ports?)\b/gi;

function isThematicBreak(trimmed) {
  if (trimmed.length < 3) return false;
  let marker = null;
  let count = 0;
  for (let i = 0; i < trimmed.length; i++) {
    const ch = trimmed[i];
    if (ch === ' ' || ch === '\t') continue;
    if (ch !== '-' && ch !== '*' && ch !== '_') return false;
    if (marker === null) marker = ch;
    else if (ch !== marker) return false;
    count++;
  }
  return count >= 3;
}

function isPortOnlyContractHeading(title) {
  if (!isDomainPortWiringHeading(title)) return false;
  const remainder = title.replace(PORT_WIRING_PHRASE_RE, ' ');
  return !NATIVE_CONTRACT_BOUNDARY_HEADING_RE.test(remainder);
}

function collectNativeOnlyContractFindings(text, { path = 'prompts/service.prompt.md' } = {}) {
  if (!isNativeOnlyPrompt(text)) return [];
  const cleaned = stripPromptMetadataPreservingLines(text);
  const { fences, proseLines } = scanMarkdownLinesAndFences(cleaned);

  // Track heading-level section flags via a stack so sibling subheadings never leak flags.
  const emptyFlags = { depth: 0, inDependencies: false, inPortOnly: false, boundary: false, error: false, verify: false };
  const sectionStack = [];
  const currentFlags = () => sectionStack.at(-1) ?? emptyFlags;
  let hasBoundarySurface = false;
  let hasErrorMapping = false;
  let hasNativeVerification = false;
  const headingEvents = [];

  for (let idx = 0; idx < proseLines.length; idx++) {
    const { lineNo, text: line } = proseLines[idx];
    const heading = /^ {0,3}(#{2,6})\s+(.+)$/.exec(line);
    if (heading) {
      const depth = heading[1].length;
      const title = heading[2].trim();
      while (sectionStack.length > 0 && sectionStack.at(-1).depth >= depth) sectionStack.pop();
      const parent = currentFlags();
      const inDependencies = parent.inDependencies || (depth === 2 && /^dependencies\b/i.test(title));
      let nextFlags;
      if (inDependencies) {
        nextFlags = { depth, inDependencies: true, inPortOnly: false, boundary: false, error: false, verify: false };
      } else {
        const portOnly = isPortOnlyContractHeading(title);
        const ownBoundary = !portOnly && NATIVE_CONTRACT_BOUNDARY_HEADING_RE.test(title);
        const ownError = NATIVE_CONTRACT_ERROR_HEADING_RE.test(title);
        const ownVerify = NATIVE_CONTRACT_VERIFY_HEADING_RE.test(title);
        nextFlags = {
          depth,
          inDependencies: false,
          inPortOnly: portOnly ? true : (ownBoundary ? false : parent.inPortOnly),
          boundary: parent.boundary || ownBoundary,
          error: parent.error || ownError,
          verify: parent.verify || ownVerify,
        };
      }
      sectionStack.push(nextFlags);
      headingEvents.push({ lineNo, flags: nextFlags });
      continue;
    }

    const active = currentFlags();
    if (active.inDependencies) continue;

    const trimmed = line.trim();
    if (!trimmed || /^ {0,3}#\s+/.test(line) || isThematicBreak(trimmed)) continue;

    if (active.boundary) hasBoundarySurface = true;
    if (active.error) hasErrorMapping = true;
    if (active.verify) hasNativeVerification = true;

    if (!active.inPortOnly && !hasBoundarySurface && line.includes('|') && idx + 1 < proseLines.length && isMarkdownTableSeparator(proseLines[idx + 1].text)) {
      hasBoundarySurface = true;
    }
    if (!hasErrorMapping && NATIVE_CONTRACT_ERROR_CUE_RE.test(trimmed)) {
      hasErrorMapping = true;
    }
    if (!hasNativeVerification && NATIVE_CONTRACT_VERIFY_CUE_RE.test(trimmed)) {
      hasNativeVerification = true;
    }
  }

  // Non-blank fences outside `## Dependencies` satisfy their enclosing section heading, and declarative schema fences outside port-only sections satisfy boundary/runtime surface.
  let headingIdx = -1;
  for (const fence of fences) {
    if (!fence.bodyLines.some(item => item.text.trim().length > 0)) continue;
    while (headingIdx + 1 < headingEvents.length && headingEvents[headingIdx + 1].lineNo < fence.openLine) headingIdx++;
    const active = headingIdx >= 0 ? headingEvents[headingIdx].flags : emptyFlags;
    if (active.inDependencies) continue;
    if (active.boundary) hasBoundarySurface = true;
    if (active.error) hasErrorMapping = true;
    if (active.verify) hasNativeVerification = true;
    if (!active.inPortOnly && DECLARATIVE_SCHEMA_FENCE_LANGS.has(fence.lang)) {
      hasBoundarySurface = true;
    }
    if (!hasErrorMapping || !hasNativeVerification) {
      for (const item of fence.bodyLines) {
        if (!hasErrorMapping && NATIVE_CONTRACT_ERROR_CUE_RE.test(item.text)) hasErrorMapping = true;
        if (!hasNativeVerification && NATIVE_CONTRACT_VERIFY_CUE_RE.test(item.text)) hasNativeVerification = true;
        if (hasErrorMapping && hasNativeVerification) break;
      }
    }
  }

  const missing = [];
  if (!hasBoundarySurface) missing.push('boundary/runtime contract (storage/DDL, transaction/locking, wire/HTTP/CLI/OS/auth surface)');
  if (!hasErrorMapping) missing.push('error mapping / failure behavior');
  if (!hasNativeVerification) missing.push('real-host / native verification cases');
  if (!missing.length) return [];

  const detail = `Native-only prompt is missing required specification sections: ${missing.join('; ')}. Document the concrete boundary/runtime contract, error mapping, and executable non-mocked real-host verification cases.`;
  return [{
    filePath: path,
    line: 1,
    order: 3,
    code: 'native-only-contract-incomplete',
    category: 'native-only contract',
    defaultSeverity: 'warn',
    detail,
    warning: `Warning: native-only contract: ${path}:1 [native-only-contract-incomplete] ${detail}`,
  }];
}

export function lintNativeOnlyContract(text, { path = 'prompts/service.prompt.md' } = {}) {
  return collectNativeOnlyContractFindings(text, { path }).map(r => r.warning);
}

function collectPromptSizeFindings(promptText, codeFiles, { path = 'prompts/module.prompt.md' } = {}) {
  const rawList = Array.isArray(codeFiles) ? codeFiles : (codeFiles !== undefined && codeFiles !== null ? [codeFiles] : []);
  const entries = rawList
    .map(item => (typeof item === 'string' ? { path: '', text: item } : item))
    .filter(item => item && typeof item.text === 'string');
  if (!entries.length) return [];

  const promptLines = countPromptProseLines(promptText);
  const codeLines = entries.reduce((sum, item) => sum + countFileLines(item.text), 0);
  if (promptLines < codeLines) return [];

  const targetPaths = entries.map(item => item.path).filter(Boolean).join(', ') || 'owned code';
  const detail = `Prompt spans ${promptLines} lines while generated code (${targetPaths}) spans ${codeLines} lines. Keep prompt lines strictly smaller than generated code lines (< ${codeLines}) by stating domain decisions concisely instead of implementation detail.`;
  return [{
    filePath: path,
    line: 1,
    order: 0,
    code: 'prompt-larger-than-code',
    category: 'prompt size',
    detail,
    warning: `Warning: prompt size: ${path}:1 [prompt-larger-than-code] ${detail}`,
  }];
}

export function lintPromptSize(promptText, codeFiles, { path = 'prompts/module.prompt.md' } = {}) {
  return collectPromptSizeFindings(promptText, codeFiles, { path }).map(r => r.warning);
}

function collectPromptStructureFindings(text, { path = 'prompts/module.prompt.md', hasOwnedCode = false } = {}) {
  const raw = String(text ?? '');
  const hasRuntimeInterface = hasRuntimeInterfaceMetadata(raw);
  const cleaned = stripPromptMetadataPreservingLines(raw);
  const { fences, proseLines } = scanMarkdownLinesAndFences(cleaned);

  let hasTitle = false;
  let hasDependenciesHeading = false;
  let nonAppearanceH2Count = 0;
  let hasPeerPromptLink = false;
  let hasSvgDrawing = false;
  let hasMarkdownTable = false;
  let nonEmptyProseCount = 0;
  const branchLines = [];
  const stateTransitionLines = [];

  for (let idx = 0; idx < proseLines.length; idx++) {
    const { lineNo, text: line } = proseLines[idx];
    const trimmed = line.trim();
    if (!trimmed) continue;

    if (/^ {0,3}#\s+\S/.test(line)) {
      hasTitle = true;
      continue;
    }

    const h2 = /^ {0,3}##\s+(.+)$/.exec(line);
    if (h2) {
      const headingTitle = h2[1].trim();
      if (/^dependencies\b/i.test(headingTitle)) hasDependenciesHeading = true;
      else if (!/^appearance\b/i.test(headingTitle)) nonAppearanceH2Count++;
      continue;
    }

    if (/^ {0,3}#{3,6}\s+/.test(line)) continue;

    nonEmptyProseCount++;
    if (/\]\([^)\s]*\.prompt\.md(?:#[^)\s]*)?\)/i.test(line)) hasPeerPromptLink = true;
    if (/!\[[^\]]*\]\([^)\s]*\.ui\.svg[^)\s]*\)/i.test(line)) hasSvgDrawing = true;

    if (line.includes('|') && idx + 1 < proseLines.length) {
      const nextTrimmed = proseLines[idx + 1].text.trim();
      if (/^\|?\s*:?-{2,}:?\s*(?:\|\s*:?-{2,}:?\s*)+\|?$/.test(nextTrimmed)) {
        hasMarkdownTable = true;
      }
    }

    if (/\b(?:if|when|whenever|unless|otherwise)\b/i.test(trimmed)) {
      branchLines.push(lineNo);
    }
    if (/\b(?:transitions?\s+(?:from|to)|moves?\s+from\s+\S+\s+to\s+\S+|state\s+machine)\b/i.test(trimmed)) {
      stateTransitionLines.push(lineNo);
    }
  }

  const hasMermaidFence = fences.some(f => f.lang === 'mermaid');
  const findings = [];

  if (!hasTitle) {
    const detail = 'Prompt has no top-level "# <Title>" heading. Start every prompt with "# <Title>" and a plain-English opening sentence.';
    findings.push({
      filePath: path,
      line: 1,
      order: 0,
      code: 'prompt-missing-title',
      category: 'prompt structure',
      detail,
      warning: `Warning: prompt structure: ${path}:1 [prompt-missing-title] ${detail}`,
    });
  }

  if (!hasDependenciesHeading && (hasOwnedCode || hasRuntimeInterface || hasPeerPromptLink || nonAppearanceH2Count >= 2)) {
    const detail = 'Prompt has no "## Dependencies" section. Add "## Dependencies" listing peer prompt links (or "None." when standalone).';
    findings.push({
      filePath: path,
      line: 1,
      order: 1,
      code: 'prompt-missing-dependencies',
      category: 'prompt structure',
      detail,
      warning: `Warning: prompt structure: ${path}:1 [prompt-missing-dependencies] ${detail}`,
    });
  }

  if (
    !hasMermaidFence
    && !hasSvgDrawing
    && !hasMarkdownTable
    && ((nonEmptyProseCount >= DIAGRAM_MIN_PROSE_LINES && branchLines.length >= DIAGRAM_MIN_BRANCH_LINES) || stateTransitionLines.length >= 3)
  ) {
    const lineNo = stateTransitionLines[0] ?? branchLines[0] ?? 1;
    const detail = 'Prompt describes multi-branch or state-transition rules without a diagram or decision table. Add a ```mermaid``` diagram or Markdown table where applicable.';
    findings.push({
      filePath: path,
      line: lineNo,
      order: 2,
      code: 'prompt-missing-diagram',
      category: 'prompt structure',
      detail,
      warning: `Warning: prompt structure: ${path}:${lineNo} [prompt-missing-diagram] ${detail}`,
    });
  }

  findings.sort((a, b) => a.line - b.line || a.order - b.order);
  return findings;
}

export function lintPromptStructure(text, { path = 'prompts/module.prompt.md', hasOwnedCode = false } = {}) {
  return collectPromptStructureFindings(text, { path, hasOwnedCode }).map(r => r.warning);
}

function decodeSimpleEscapes(raw) {
  return raw.replace(/\\(.)/gs, (_, ch) => {
    if (ch === 'n') return '\n';
    if (ch === 'r') return '\r';
    if (ch === 't') return '\t';
    return ch;
  });
}

const newlinesIn = str => {
  let n = 0;
  for (let i = 0; i < str.length; i++) if (str[i] === '\n') n++;
  return '\n'.repeat(n);
};

// Mask comments and string/template bodies into __STR_k__ placeholders while keeping 1-based line numbers
// and capturing real per-line lexical comments/code presence in one linear O(N) pass.
function tokenizeTestCode(source, { hashComments = false } = {}) {
  const literals = [];
  const lineComments = [];
  const lineHasCode = [];
  const lineHasComment = [];
  let lineNo = 1;

  const markCodeLines = (startLine, rawSpan) => {
    lineHasCode[startLine - 1] = true;
    let nl = 0;
    for (let k = 0; k < rawSpan.length; k++) {
      if (rawSpan[k] === '\n') {
        nl++;
        lineHasCode[startLine - 1 + nl] = true;
      }
    }
    return nl;
  };
  const recordCommentSpan = (startLine, rawComment) => {
    const parts = rawComment.split('\n');
    for (let k = 0; k < parts.length; k++) {
      const idx = startLine - 1 + k;
      lineHasComment[idx] = true;
      lineComments[idx] = lineComments[idx] ? `${lineComments[idx]} ${parts[k]}` : parts[k];
    }
    return parts.length - 1;
  };
  const addLit = (val, rawSpan) => {
    const id = literals.length;
    literals.push(val);
    const nl = markCodeLines(lineNo, rawSpan);
    lineNo += nl;
    return `__STR_${id}__${'\n'.repeat(nl)}`;
  };

  let out = '';
  let i = 0;
  let prevToken = '';
  const templateStack = [];
  const canStartRegex = () => !prevToken || [
    '(', ',', '=', ':', '[', '!', '&', '|', '?', '{', '}', ';', '+', '-', '*', '%', '<', '>', '^', '~',
    'return', 'throw', 'case', 'in', 'of', 'typeof', 'void', 'delete', 'await', 'yield',
  ].includes(prevToken);

  const consumeTemplateChunk = startIdx => {
    let j = startIdx;
    while (j < source.length && source[j] !== '`') {
      if (source[j] === '\\') { j += 2; continue; }
      if (source[j] === '$' && source[j + 1] === '{') {
        const rawChunk = source.slice(startIdx, j);
        const tok = addLit(decodeSimpleEscapes(rawChunk), rawChunk);
        templateStack.push({ depth: 1 });
        prevToken = '(';
        return { text: `(${tok} + (`, next: j + 2 };
      }
      j++;
    }
    const rawChunk = source.slice(startIdx, j);
    const tok = addLit(decodeSimpleEscapes(rawChunk), rawChunk);
    prevToken = 'str';
    return { text: `${tok})`, next: j < source.length ? j + 1 : j };
  };

  while (i < source.length) {
    const ch = source[i];
    const next = source[i + 1];

    if (!hashComments && ch === '/' && next === '/') {
      const end = source.indexOf('\n', i + 2);
      const body = end < 0 ? source.slice(i + 2) : source.slice(i + 2, end);
      recordCommentSpan(lineNo, body);
      if (end < 0) break;
      out += '\n';
      lineNo++;
      i = end + 1;
      continue;
    }
    if (hashComments && ch === '#') {
      const end = source.indexOf('\n', i + 1);
      const body = end < 0 ? source.slice(i + 1) : source.slice(i + 1, end);
      recordCommentSpan(lineNo, body);
      if (end < 0) break;
      out += '\n';
      lineNo++;
      i = end + 1;
      continue;
    }
    if (!hashComments && ch === '/' && next === '*') {
      const end = source.indexOf('*/', i + 2);
      const body = end < 0 ? source.slice(i + 2) : source.slice(i + 2, end);
      const nl = recordCommentSpan(lineNo, body);
      out += '\n'.repeat(nl);
      lineNo += nl;
      i = end < 0 ? source.length : end + 2;
      continue;
    }
    if (ch === "'" || ch === '"') {
      if (hashComments && source[i + 1] === ch && source[i + 2] === ch) {
        let j = i + 3;
        let end = -1;
        while (j < source.length) {
          if (source[j] === '\\') { j += 2; continue; }
          if (source[j] === ch && source[j + 1] === ch && source[j + 2] === ch) {
            end = j;
            break;
          }
          j++;
        }
        const body = end < 0 ? source.slice(i + 3) : source.slice(i + 3, end);
        out += addLit(body, body);
        prevToken = 'str';
        i = end < 0 ? source.length : end + 3;
        continue;
      }
      let j = i + 1;
      while (j < source.length && source[j] !== ch && source[j] !== '\n') {
        if (source[j] === '\\') j += 2;
        else j++;
      }
      const rawBody = source.slice(i + 1, j);
      out += addLit(decodeSimpleEscapes(rawBody), rawBody);
      prevToken = 'str';
      i = j < source.length && source[j] === ch ? j + 1 : j;
      continue;
    }
    if (!hashComments && ch === '`') {
      let j = i + 1;
      let hasInterp = false;
      while (j < source.length && source[j] !== '`') {
        if (source[j] === '\\') { j += 2; continue; }
        if (source[j] === '$' && source[j + 1] === '{') { hasInterp = true; break; }
        j++;
      }
      if (!hasInterp) {
        const rawBody = source.slice(i + 1, j);
        out += addLit(decodeSimpleEscapes(rawBody), rawBody);
        prevToken = 'str';
        i = j < source.length ? j + 1 : j;
      } else {
        const step = consumeTemplateChunk(i + 1);
        out += step.text;
        i = step.next;
      }
      continue;
    }
    if (templateStack.length) {
      if (ch === '{') {
        templateStack.at(-1).depth++;
        lineHasCode[lineNo - 1] = true;
        out += ch;
        prevToken = '{';
        i++;
        continue;
      }
      if (ch === '}' && --templateStack.at(-1).depth === 0) {
        templateStack.pop();
        lineHasCode[lineNo - 1] = true;
        out += ') + ';
        const step = consumeTemplateChunk(i + 1);
        out += step.text;
        i = step.next;
        continue;
      }
    }
    if (!hashComments && ch === '/' && next !== '/' && next !== '*' && canStartRegex()) {
      let j = i + 1;
      let inClass = false;
      let closed = false;
      while (j < source.length && source[j] !== '\n') {
        if (source[j] === '\\') {
          if (j + 1 < source.length && source[j + 1] !== '\n') { j += 2; continue; }
          break;
        }
        if (source[j] === '[') inClass = true;
        else if (source[j] === ']') inClass = false;
        else if (source[j] === '/' && !inClass) { closed = true; j++; break; }
        j++;
      }
      if (closed) {
        while (j < source.length && /[A-Za-z]/.test(source[j])) j++;
        lineHasCode[lineNo - 1] = true;
        out += '/__RE__/';
        prevToken = 'regex';
        i = j;
        continue;
      }
    }
    if (/\s/.test(ch)) {
      if (ch === '\n') lineNo++;
      out += ch;
      i++;
      continue;
    }
    if (/[A-Za-z_$]/.test(ch)) {
      let j = i + 1;
      while (j < source.length && /[A-Za-z0-9_$]/.test(source[j])) j++;
      const word = source.slice(i, j);
      lineHasCode[lineNo - 1] = true;
      out += word;
      prevToken = word;
      i = j;
      continue;
    }
    lineHasCode[lineNo - 1] = true;
    out += ch;
    prevToken = ch;
    i++;
  }

  return { skeleton: out, literals, lineComments, lineHasCode, lineHasComment };
}

function buildLineStarts(text) {
  const starts = [0];
  for (let i = 0; i < text.length; i++) if (text[i] === '\n') starts.push(i + 1);
  return starts;
}

function lineNumberAt(lineStarts, index) {
  let lo = 0, hi = lineStarts.length - 1;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    if (lineStarts[mid] <= index) lo = mid + 1;
    else hi = mid - 1;
  }
  return lo;
}

function parseCallArgs(skeleton, openParenIdx) {
  let depth = 1;
  let k = openParenIdx + 1;
  let argStart = k;
  const args = [];
  while (k < skeleton.length && depth > 0) {
    const ch = skeleton[k];
    if (ch === '(') depth++;
    else if (ch === ')') {
      depth--;
      if (depth === 0) {
        args.push(skeleton.slice(argStart, k));
        return { args, endIdx: k + 1 };
      }
    } else if (ch === ',' && depth === 1) {
      args.push(skeleton.slice(argStart, k));
      argStart = k + 1;
    }
    k++;
  }
  return null;
}

function normalizeCandidateRepoPath(rawCandidate, testDir) {
  if (!rawCandidate || typeof rawCandidate !== 'string') return null;
  let cleaned = rawCandidate.trim().replace(/^file:\/\//i, '').replace(/\\/g, '/');
  if (!cleaned || /[\r\n\0]/.test(cleaned)) return null;
  if (/(?:^|\/)(?:fixtures|harbor)(?:\/|$)/i.test(cleaned)) return null;

  let normalized;
  if (cleaned.startsWith('./') || cleaned.startsWith('../')) {
    normalized = posix.normalize(posix.join(testDir, cleaned));
  } else {
    const anchored = /(?:^|\/)((?:prompts|src)\/[A-Za-z0-9_./-]+)$/.exec(cleaned);
    normalized = anchored ? posix.normalize(anchored[1]) : posix.normalize(cleaned.replace(/^\/+/, ''));
  }

  if (!normalized || normalized.startsWith('..') || normalized.includes('/../')) return null;
  if (/(?:^|\/)(?:fixtures|harbor)(?:\/|$)/i.test(normalized)) return null;
  if (normalized.endsWith('.prompt.md') || normalized.startsWith('prompts/') || normalized.startsWith('src/')) {
    return normalized;
  }
  return null;
}

function referencesSandbox(expr, sandboxVars, literals) {
  if (/\b(?:tmpdir|mkdtempSync|mkdtemp)\s*\(/.test(expr)) return true;
  if (/\b(?:setup|f|w|ctx|env|fixture|sandbox|run)\s*\.\s*(?:repo|root|cwd|dir|worktree|mergeCheckout|primary|home|state)\b/.test(expr)) return true;
  for (const match of expr.matchAll(/__STR_(\d+)__/g)) {
    const val = literals?.[Number(match[1])] ?? '';
    if (/(?:^|\/)(?:fixtures|harbor)(?:\/|$)/i.test(val)) return true;
  }
  for (const match of expr.matchAll(/\b([A-Za-z_$][\w$]*)\b/g)) {
    const id = match[1];
    if (sandboxVars.has(id)) return true;
  }
  return false;
}

const IGNORED_PATH_HELPER_IDS = new Set([
  'join', 'resolve', 'posix', 'path', 'URL', 'new', 'fileURLToPath', 'import', 'meta', 'url', 'dirname',
  'process', 'cwd', 'root', 'packageRoot', 'repoRoot', 'String',
]);

function resolveTargetPath(argExpr, testDir, literals, pathVars, sandboxVars) {
  if (!argExpr || referencesSandbox(argExpr, sandboxVars, literals)) return null;

  const parts = [];
  const tokenRe = /__STR_(\d+)__|\b([A-Za-z_$][\w$]*)\b/g;
  for (const m of argExpr.matchAll(tokenRe)) {
    if (m[1] !== undefined) {
      const val = literals[Number(m[1])];
      if (typeof val === 'string' && !/^(?:utf-?8|ascii|latin1|r|rb)$/i.test(val)) {
        if (val.length > 0) parts.push({ kind: 'lit', val });
      }
    } else if (m[2]) {
      const id = m[2];
      if (pathVars.has(id)) parts.push({ kind: 'lit', val: pathVars.get(id) });
      else if (!IGNORED_PATH_HELPER_IDS.has(id)) parts.push({ kind: 'dyn', val: '*' });
    }
  }
  const litParts = parts.filter(p => p.kind === 'lit');
  if (!litParts.length) return null;

  const collapsed = [];
  for (const p of parts) {
    if (p.kind === 'dyn' && collapsed.at(-1)?.kind === 'dyn') continue;
    collapsed.push(p);
  }
  while (collapsed[0]?.kind === 'dyn') collapsed.shift();
  while (collapsed.at(-1)?.kind === 'dyn') collapsed.pop();
  if (!collapsed.length) return null;

  const isImportMetaRel = /\bimport\.meta\.(?:url|dirname)\b/.test(argExpr) && collapsed.length === 1 && !collapsed[0].val.startsWith('.');
  let joined = '';
  for (let idx = 0; idx < collapsed.length; idx++) {
    const cur = collapsed[idx];
    if (idx === 0) {
      joined = isImportMetaRel ? `./${cur.val}` : cur.val;
      continue;
    }
    const prev = collapsed[idx - 1];
    if (cur.kind === 'dyn' || prev.kind === 'dyn') {
      joined = `${joined}${cur.val}`;
    } else if (joined.endsWith('/') || cur.val.startsWith('/')) {
      joined = `${joined}${cur.val}`;
    } else {
      joined = `${joined}/${cur.val}`;
    }
  }

  return normalizeCandidateRepoPath(joined, testDir);
}

export function isInspectableTestCodePath(path) {
  return isTestOwnedPath(path)
    && TEST_CODE_EXT.test(path)
    && !SKIP_TEST_SUBDIR.test(path)
    && !SEAM_TEST_FILE.test(path);
}

function collectFakeTestWarnings(text, { path = 'test/example.test.mjs' } = {}) {
  if (!canonicalRepoPath(path) || SKIP_TEST_SUBDIR.test(path) || SEAM_TEST_FILE.test(path) || !TEST_CODE_EXT.test(path)) {
    return [];
  }
  const hashComments = /\.(?:py|rb)$/i.test(path);
  const testDir = posix.dirname(path) === '.' ? '' : posix.dirname(path);
  const { skeleton, literals } = tokenizeTestCode(String(text ?? ''), { hashComments });
  const lineStarts = buildLineStarts(skeleton);

  const sandboxVars = new Set(['harborDir', 'fixturesDir', 'fixtureDir']);
  for (const cb of skeleton.matchAll(/\bharbor\s*\([^,)]+,\s*(?:async\s+)?\(?([A-Za-z_$][\w$]*)\)?\s*=>/g)) {
    sandboxVars.add(cb[1]);
  }
  const sandboxInitRe = /(?:\b(?:const|let|var)\s+|,\s*)(?:\{([^}]+)\}|([A-Za-z_$][\w$]*))\s*=\s*(?:await\s+)?(?:[A-Za-z_$][\w$.]*\s*\(\s*)*(?:mkdtempSync|mkdtemp|temp|harbor|fixture|nativeFixture|layoutFixture|makeRepo|createTempRepo|setupRepo|fix2World)\s*\(/g;
  for (const m of skeleton.matchAll(sandboxInitRe)) {
    if (m[2]) sandboxVars.add(m[2]);
    else if (m[1]) {
      for (const part of m[1].split(',')) {
        const name = part.split(':').pop().split('=')[0].trim();
        if (/^[A-Za-z_$][\w$]*$/.test(name)) sandboxVars.add(name);
      }
    }
  }
  const assignments = [];
  const assignHeadRe = /(?:\b(?:const|let|var)\s+|,\s*)([A-Za-z_$][\w$]*)\s*=\s*(?!=)/g;
  for (const m of skeleton.matchAll(assignHeadRe)) {
    const ident = m[1];
    let k = m.index + m[0].length;
    let depth = 0;
    while (k < skeleton.length) {
      const ch = skeleton[k];
      if (ch === '(' || ch === '[' || ch === '{') depth++;
      else if (ch === ')' || ch === ']' || ch === '}') {
        if (depth === 0) break;
        depth--;
      } else if (depth === 0 && (ch === ',' || ch === ';' || ch === '\n')) {
        break;
      }
      k++;
    }
    assignments.push([ident, skeleton.slice(m.index + m[0].length, k)]);
  }
  for (let pass = 0; pass < 4; pass++) {
    for (const [ident, rhs] of assignments) {
      if (!sandboxVars.has(ident) && referencesSandbox(rhs, sandboxVars, literals)) sandboxVars.add(ident);
    }
  }

  const pathVars = new Map();
  for (let pass = 0; pass < 2; pass++) {
    for (const [ident, rhs] of assignments) {
      if (sandboxVars.has(ident) || pathVars.has(ident)) continue;
      if (/\b(?:readFileSync|readFile|existsSync|statSync|lstatSync)\b/.test(rhs)) continue;
      if (/^\s*[\[{]/.test(rhs) || /[\]}]/.test(rhs)) continue;
      const resolved = resolveTargetPath(rhs, testDir, literals, pathVars, sandboxVars);
      if (resolved) pathVars.set(ident, resolved);
    }
  }

  const findings = [];
  const sourceTextVars = new Map();
  const callRe = /(?:^|[^\w$])(?:(?:fs|fsPromises|promises)\s*\.\s*)?(readFileSync|readFile|existsSync|statSync|lstatSync|accessSync)\s*\(/g;

  for (const match of skeleton.matchAll(callRe)) {
    const fnName = match[1];
    const fnOffset = match.index + match[0].lastIndexOf(fnName);
    const openParenIdx = skeleton.indexOf('(', fnOffset + fnName.length);
    if (openParenIdx < 0) continue;
    const parsed = parseCallArgs(skeleton, openParenIdx);
    if (!parsed || !parsed.args.length) continue;

    const target = resolveTargetPath(parsed.args[0], testDir, literals, pathVars, sandboxVars);
    if (!target) continue;
    const callLine = lineNumberAt(lineStarts, fnOffset);

    if (fnName === 'existsSync' || fnName === 'statSync' || fnName === 'lstatSync' || fnName === 'accessSync') {
      if (target.startsWith('prompts/') || target.startsWith('src/')) {
        const detail = `Test checks file existence on "${target}" instead of exercising behavior. Import the module or run the CLI command and assert its observable output.`;
        findings.push({
          filePath: path,
          line: callLine,
          order: 1,
          code: 'fake-test-exists-check',
          category: 'fake test',
          target,
          detail,
          warning: `Warning: fake test: ${path}:${callLine} [fake-test-exists-check] ${detail}`,
        });
      }
      continue;
    }

    if (target.endsWith('.prompt.md')) {
      const detail = `Test reads prompt file "${target}" directly. Call exported module functions or CLI commands to verify observable behavior instead of asserting on prompt prose.`;
      findings.push({
        filePath: path,
        line: callLine,
        order: 0,
        code: 'fake-test-prompt-read',
        category: 'fake test',
        target,
        detail,
        warning: `Warning: fake test: ${path}:${callLine} [fake-test-prompt-read] ${detail}`,
      });
      continue;
    }

    if (SRC_CODE_PATH.test(target)) {
      const before = skeleton.slice(Math.max(0, match.index - 120), match.index + 1);
      const after = skeleton.slice(parsed.endIdx, Math.min(skeleton.length, parsed.endIdx + 160));
      const inlineChained = /^\s*\.\s*(?:includes|match|matchAll|search|indexOf|startsWith|endsWith)\s*\(/.test(after);
      const inlineWrapped = /(?:\.test|\bassert\s*\.\s*(?:match|doesNotMatch)|\bexpect)\s*\(\s*(?:await\s+)?$/.test(before);
      if (inlineChained || inlineWrapped) {
        const detail = `Test reads "${target}" as text and matches source strings instead of testing behavior. Import "${target}" (or run the CLI) and assert outputs, state changes or exit codes.`;
        findings.push({
          filePath: path,
          line: callLine,
          order: 2,
          code: 'fake-test-source-match',
          category: 'fake test',
          target,
          detail,
          warning: `Warning: fake test: ${path}:${callLine} [fake-test-source-match] ${detail}`,
        });
      } else {
        const assignMatch = /(?:const|let|var)\s+([A-Za-z_$][\w$]*)\s*=\s*(?:await\s+)?$/.exec(before);
        if (assignMatch && !sourceTextVars.has(assignMatch[1])) {
          sourceTextVars.set(assignMatch[1], { target, afterIdx: parsed.endIdx });
        }
      }
    }
  }

  for (const [ident, { target, afterIdx }] of sourceTextVars.entries()) {
    const rest = skeleton.slice(afterIdx);
    const escapedIdent = ident.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const assertPatterns = [
      new RegExp(`\\b${escapedIdent}\\s*\\.\\s*(?:includes|match|matchAll|search|indexOf|startsWith|endsWith)\\s*\\(`),
      new RegExp(`\\.test\\s*\\(\\s*${escapedIdent}\\b`),
      new RegExp(`\\bassert\\s*\\.\\s*(?:match|doesNotMatch)\\s*\\(\\s*${escapedIdent}\\b`),
      new RegExp(`\\bexpect\\s*\\(\\s*${escapedIdent}\\s*\\)\\s*\\.(?:not\\s*\\.)?(?:toMatch|toContain)\\s*\\(`),
    ];
    let earliestOffset = null;
    for (const re of assertPatterns) {
      const m = re.exec(rest);
      if (m && (earliestOffset === null || m.index < earliestOffset)) {
        earliestOffset = m.index;
      }
    }
    if (earliestOffset !== null) {
      const matchLine = lineNumberAt(lineStarts, afterIdx + earliestOffset);
      const detail = `Test reads "${target}" as text and matches source strings instead of testing behavior. Import "${target}" (or run the CLI) and assert outputs, state changes or exit codes.`;
      findings.push({
        filePath: path,
        line: matchLine,
        order: 2,
        code: 'fake-test-source-match',
        category: 'fake test',
        target,
        detail,
        warning: `Warning: fake test: ${path}:${matchLine} [fake-test-source-match] ${detail}`,
      });
    }
  }

  findings.sort((a, b) => a.line - b.line || a.order - b.order);
  const seen = new Set();
  return findings.filter(item => {
    if (seen.has(item.warning)) return false;
    seen.add(item.warning);
    return true;
  });
}

export function lintFakeTests(text, { path = 'test/example.test.mjs' } = {}) {
  return collectFakeTestWarnings(text, { path }).map(item => item.warning);
}

function isTestOrBuiltinSpecifier(spec, testDir) {
  if (!spec || typeof spec !== 'string') return true;
  const clean = spec.trim().split('?')[0].split('#')[0];
  if (!clean || clean.startsWith('node:') || TEST_FRAMEWORK_PACKAGES.has(clean)) return true;
  if (clean.startsWith('./') || clean.startsWith('../')) {
    const resolved = posix.normalize(posix.join(testDir, clean));
    if (
      /^(?:tests?|__tests__|fixtures|helpers)\//i.test(resolved)
      || /(?:^|\/)(?:fixtures|helpers|harbor)\//i.test(resolved)
      || isTestOwnedPath(resolved)
    ) {
      return true;
    }
    return false;
  }
  if (/^(?:tests?|__tests__|fixtures|helpers)(?:\/|\.|$)/i.test(clean)) return true;
  return false;
}

function resolveProductionModuleTarget(spec, testDir) {
  if (!spec || typeof spec !== 'string') return null;
  const clean = spec.trim().split('?')[0].split('#')[0];
  if (clean.startsWith('./') || clean.startsWith('../')) {
    const resolved = posix.normalize(posix.join(testDir, clean));
    if (resolved && !resolved.startsWith('..') && !resolved.includes('/../')) return resolved;
  }
  return null;
}

function isPrivateModuleSpecifier(spec) {
  const clean = spec.trim().split('?')[0].split('#')[0];
  if (PRIVATE_MODULE_SEGMENT_RE.test(clean)) return true;
  const slashPath = clean.replace(/\\/g, '/');
  if (!DUNDER_BASENAME_RE.test(slashPath) && PRIVATE_MODULE_BASENAME_RE.test(slashPath)) return true;
  if (!slashPath.includes('/') && clean.includes('.')) {
    const segments = clean.split('.');
    if (segments.some(seg => PRIVATE_SYMBOL_RE.test(seg) && !/^__.*__$/.test(seg))) return true;
  }
  return false;
}

function parseBindingClause(clause) {
  const importedSymbols = [];
  const localBindings = [];
  const trimmed = clause.trim().replace(/^type\s+/, '');
  if (!trimmed) return { importedSymbols, localBindings };

  const nsMatch = /\*\s+as\s+([A-Za-z_$][\w$]*)/.exec(trimmed);
  if (nsMatch) localBindings.push(nsMatch[1]);

  const braceStart = trimmed.indexOf('{');
  const braceEnd = trimmed.lastIndexOf('}');
  if (braceStart >= 0 && braceEnd > braceStart) {
    const before = trimmed.slice(0, braceStart).replace(/,\s*$/, '').trim();
    if (before && /^[A-Za-z_$][\w$]*$/.test(before)) {
      localBindings.push(before);
    }
    const inner = trimmed.slice(braceStart + 1, braceEnd);
    for (const part of inner.split(',')) {
      const piece = part.trim().replace(/^type\s+/, '');
      if (!piece) continue;
      const asMatch = /^([A-Za-z_$][\w$]*)\s+(?:as|:)\s+([A-Za-z_$][\w$]*)(?:\s*=.*)?$/.exec(piece);
      if (asMatch) {
        importedSymbols.push(asMatch[1]);
        localBindings.push(asMatch[2]);
      } else {
        const simple = /^([A-Za-z_$][\w$]*)(?:\s*=.*)?$/.exec(piece);
        if (simple) {
          importedSymbols.push(simple[1]);
          localBindings.push(simple[1]);
        }
      }
    }
  } else if (!nsMatch && /^[A-Za-z_$][\w$]*$/.test(trimmed)) {
    localBindings.push(trimmed);
  }
  return { importedSymbols, localBindings };
}

function collectPublicInterfaceTestWarnings(text, { path = 'test/example.test.mjs' } = {}) {
  if (!canonicalRepoPath(path) || SKIP_TEST_SUBDIR.test(path) || SEAM_TEST_FILE.test(path) || !TEST_CODE_EXT.test(path)) {
    return [];
  }
  const isPython = /\.py$/i.test(path);
  const hashComments = /\.(?:py|rb)$/i.test(path);
  const testDir = posix.dirname(path) === '.' ? '' : posix.dirname(path);
  const { skeleton, literals } = tokenizeTestCode(String(text ?? ''), { hashComments });
  const lineStarts = buildLineStarts(skeleton);

  const findings = [];
  const prodBindings = new Map(); // localIdent -> resolved target path | null

  const recordImport = (spec, clause, offset) => {
    if (!spec || isTestOrBuiltinSpecifier(spec, testDir)) return;
    const line = lineNumberAt(lineStarts, offset);
    const target = resolveProductionModuleTarget(spec, testDir);

    if (isPrivateModuleSpecifier(spec)) {
      const detail = `Test imports private module path "${spec}". Import only the module's public entry interface so internal refactors do not break tests.`;
      findings.push({
        filePath: path,
        line,
        order: 0,
        code: 'test-private-import',
        category: 'public-interface test',
        target,
        detail,
        warning: `Warning: public-interface test: ${path}:${line} [test-private-import] ${detail}`,
      });
    }

    if (clause) {
      const { importedSymbols, localBindings } = parseBindingClause(clause);
      for (const sym of importedSymbols) {
        if (PRIVATE_SYMBOL_RE.test(sym) && !/^__.*__$/.test(sym)) {
          const detail = `Test imports private internal symbol "${sym}" from "${spec}". Test observable behavior through public exports instead of private helpers.`;
          findings.push({
            filePath: path,
            line,
            order: 1,
            code: 'test-private-import',
            category: 'public-interface test',
            target,
            detail,
            warning: `Warning: public-interface test: ${path}:${line} [test-private-import] ${detail}`,
          });
        }
      }
      for (const local of localBindings) {
        if (!prodBindings.has(local)) prodBindings.set(local, target);
      }
    }
  };

  // 1. Static ESM imports: import ... from 'spec'
  for (const m of skeleton.matchAll(/\bimport\s+([\s\S]*?)\s+from\s+__STR_(\d+)__/g)) {
    const spec = literals[Number(m[2])];
    recordImport(spec, m[1], m.index);
  }
  // Bare side-effect imports: import 'spec'
  for (const m of skeleton.matchAll(/\bimport\s+__STR_(\d+)__/g)) {
    const spec = literals[Number(m[1])];
    recordImport(spec, '', m.index);
  }
  // Assigned dynamic import / require: const X = await import('spec') / const X = require('spec')
  for (const m of skeleton.matchAll(/\b(?:const|let|var)\s+([^=;]+?)\s*=\s*(?:await\s+)?(?:import|require)\s*\(\s*__STR_(\d+)__\s*\)/g)) {
    const spec = literals[Number(m[2])];
    recordImport(spec, m[1], m.index);
  }
  // Unassigned dynamic import('spec') / require('spec')
  for (const m of skeleton.matchAll(/(?<![\w$.])(?:import|require)\s*\(\s*__STR_(\d+)__\s*\)/g)) {
    const before = skeleton.slice(Math.max(0, m.index - 80), m.index);
    if (/=\s*(?:await\s+)?$/.test(before)) continue;
    const spec = literals[Number(m[1])];
    recordImport(spec, '', m.index);
  }

  // Python imports: from pkg.mod import a, _b  /  import pkg._internal
  if (isPython) {
    for (const m of skeleton.matchAll(/^[ \t]*from\s+([A-Za-z0-9_.]+)\s+import\s+([^\n;#]+)/gm)) {
      const modSpec = m[1];
      if (isTestOrBuiltinSpecifier(modSpec, testDir)) continue;
      const line = lineNumberAt(lineStarts, m.index);
      if (isPrivateModuleSpecifier(modSpec)) {
        const detail = `Test imports private module path "${modSpec}". Import only the module's public entry interface so internal refactors do not break tests.`;
        findings.push({
          filePath: path,
          line,
          order: 0,
          code: 'test-private-import',
          category: 'public-interface test',
          target: null,
          detail,
          warning: `Warning: public-interface test: ${path}:${line} [test-private-import] ${detail}`,
        });
      }
      for (const rawPart of m[2].replace(/[()]/g, '').split(',')) {
        const piece = rawPart.trim();
        if (!piece) continue;
        const [orig, alias] = piece.split(/\s+as\s+/);
        const sym = orig.trim();
        const local = (alias ?? orig).trim();
        if (PRIVATE_SYMBOL_RE.test(sym) && !/^__.*__$/.test(sym)) {
          const detail = `Test imports private internal symbol "${sym}" from "${modSpec}". Test observable behavior through public exports instead of private helpers.`;
          findings.push({
            filePath: path,
            line,
            order: 1,
            code: 'test-private-import',
            category: 'public-interface test',
            target: null,
            detail,
            warning: `Warning: public-interface test: ${path}:${line} [test-private-import] ${detail}`,
          });
        }
        if (/^[A-Za-z_]\w*$/.test(local)) prodBindings.set(local, null);
      }
    }
    for (const m of skeleton.matchAll(/^[ \t]*import\s+([A-Za-z0-9_., \t]+)$/gm)) {
      const line = lineNumberAt(lineStarts, m.index);
      for (const item of m[1].split(',')) {
        const [modName, alias] = item.trim().split(/\s+as\s+/);
        if (!modName || isTestOrBuiltinSpecifier(modName, testDir)) continue;
        if (isPrivateModuleSpecifier(modName)) {
          const detail = `Test imports private module path "${modName}". Import only the module's public entry interface so internal refactors do not break tests.`;
          findings.push({
            filePath: path,
            line,
            order: 0,
            code: 'test-private-import',
            category: 'public-interface test',
            target: null,
            detail,
            warning: `Warning: public-interface test: ${path}:${line} [test-private-import] ${detail}`,
          });
        }
        const local = (alias ?? modName.split('.')[0]).trim();
        if (/^[A-Za-z_]\w*$/.test(local)) prodBindings.set(local, null);
      }
    }
  }

  // Propagate instances constructed or returned from imported production factories/classes:
  // e.g. const svc = new OrderService(...) or const store = createStore(...)
  for (let pass = 0; pass < 2; pass++) {
    for (const m of skeleton.matchAll(/\b(?:const|let|var)?\s*([A-Za-z_$][\w$]*)\s*=\s*(?:await\s+)?(?:new\s+)?([A-Za-z_$][\w$]*)\s*\(/g)) {
      const lhs = m[1];
      const callee = m[2];
      if (!prodBindings.has(lhs) && prodBindings.has(callee)) {
        prodBindings.set(lhs, prodBindings.get(callee));
      }
    }
  }

  // 2. Private member access on imported production modules or their instances: mod._secret / instance._cache
  for (const m of skeleton.matchAll(/\b([A-Za-z_$][\w$]*)\s*(?:\?\.|\.)\s*(_[A-Za-z0-9][\w$]*)\b/g)) {
    const obj = m[1];
    const member = m[2];
    if (!prodBindings.has(obj)) continue;
    if (/^__.*__$/.test(member)) continue;
    const line = lineNumberAt(lineStarts, m.index);
    const target = prodBindings.get(obj) ?? null;
    const detail = `Test accesses private member "${obj}.${member}". Exercise only public methods and properties instead of reaching into module internals.`;
    findings.push({
      filePath: path,
      line,
      order: 2,
      code: 'test-private-access',
      category: 'public-interface test',
      target,
      detail,
      warning: `Warning: public-interface test: ${path}:${line} [test-private-access] ${detail}`,
    });
  }

  // 3. Rewire and private introspection hooks anywhere in test code
  for (const m of skeleton.matchAll(/(?:\.\s*(__get__|__set__|__Rewire__|__ResetDependency__|__private|__internal)\b|\b(rewire)\s*\(\s*__STR_(\d+)__\s*\))/g)) {
    const hook = m[1] ?? m[2];
    const target = m[3] !== undefined ? resolveProductionModuleTarget(literals[Number(m[3])], testDir) : null;
    const line = lineNumberAt(lineStarts, m.index);
    const detail = `Test reaches into private module internals via "${hook}". Test the module through its public interface and injected ports.`;
    findings.push({
      filePath: path,
      line,
      order: 3,
      code: 'test-private-access',
      category: 'public-interface test',
      target,
      detail,
      warning: `Warning: public-interface test: ${path}:${line} [test-private-access] ${detail}`,
    });
  }

  // 4. VM evaluation of production src/ files to extract unexported internals
  const srcReadVars = new Map();
  for (const m of skeleton.matchAll(/\b(?:const|let|var)\s+([A-Za-z_$][\w$]*)\s*=\s*(?:await\s+)?(?:fs\s*\.\s*)?(?:readFileSync|readFile)\s*\(\s*__STR_(\d+)__/g)) {
    const candidate = normalizeCandidateRepoPath(literals[Number(m[2])], testDir);
    if (candidate && SRC_CODE_PATH.test(candidate)) srcReadVars.set(m[1], candidate);
  }
  if (srcReadVars.size > 0) {
    for (const m of skeleton.matchAll(/\b(?:runInNewContext|runInContext|runInThisContext|Script)\s*\(\s*([A-Za-z_$][\w$]*)\b/g)) {
      const target = srcReadVars.get(m[1]);
      if (!target) continue;
      const line = lineNumberAt(lineStarts, m.index);
      const detail = `Test evaluates raw source from "${target}" to reach unexported internals. Import "${target}" through its public exports instead.`;
      findings.push({
        filePath: path,
        line,
        order: 4,
        code: 'test-private-access',
        category: 'public-interface test',
        target,
        detail,
        warning: `Warning: public-interface test: ${path}:${line} [test-private-access] ${detail}`,
      });
    }
  }

  findings.sort((a, b) => a.line - b.line || a.order - b.order);
  const seen = new Set();
  return findings.filter(item => {
    if (seen.has(item.warning)) return false;
    seen.add(item.warning);
    return true;
  });
}

export function lintPublicInterfaceTests(text, { path = 'test/example.test.mjs' } = {}) {
  return collectPublicInterfaceTestWarnings(text, { path }).map(item => item.warning);
}

const SLEEP_ALLOW_COMMENT_RE = /\b(?:pdd-allow-sleep|sleep-ok|allow-sleep)\b/i;
const SKIP_ALLOW_COMMENT_RE = /\bpdd-allow-skip\b/i;
const TRACKING_HASH_ISSUE_RE = /(?:^|[\s([,:;'"`])#[1-9]\d*\b|(?<![A-Za-z0-9_.\-/])[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+#[1-9]\d*\b/;
const TRACKING_TICKET_RE = /\b[A-Z]{2,10}-[1-9]\d*\b/;
const TRACKING_WORD_ISSUE_RE = /\bissue\s+#?[1-9]\d*\b/i;
const TRACKING_GH_URL_RE = /https:\/\/github\.com\/[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+\/issues\/[1-9]\d*\b/i;
const PLACEHOLDER_SKIP_REASONS = new Set([
  'todo', 'skip', 'skipped', 'wip', 'later', 'flaky', 'broken', 'fixme', 'temp', 'temporary', 'disabled', 'tbd', 'xxx', 'none', 'na', 'n/a',
]);

function hasTrackingIssueRef(value) {
  const s = String(value ?? '');
  return TRACKING_HASH_ISSUE_RE.test(s)
    || TRACKING_TICKET_RE.test(s)
    || TRACKING_WORD_ISSUE_RE.test(s)
    || TRACKING_GH_URL_RE.test(s);
}

function hasSubstantiveSkipReason(value) {
  const trimmed = String(value ?? '').trim();
  if (!trimmed) return false;
  if (hasTrackingIssueRef(trimmed)) return true;
  if (PLACEHOLDER_SKIP_REASONS.has(trimmed.toLowerCase())) return false;
  return trimmed.length >= 12 && /\s/.test(trimmed);
}

function buildDelimiterMaps(text) {
  const n = text.length;
  const closeParen = new Int32Array(n).fill(-1);
  const openParen = new Int32Array(n).fill(-1);
  const closeBrace = new Int32Array(n).fill(-1);
  const closeBracket = new Int32Array(n).fill(-1);
  const parenStack = [];
  const braceStack = [];
  const bracketStack = [];
  for (let i = 0; i < n; i++) {
    const ch = text[i];
    if (ch === '(') parenStack.push(i);
    else if (ch === ')' && parenStack.length > 0) {
      const open = parenStack.pop();
      closeParen[open] = i;
      openParen[i] = open;
    } else if (ch === '{') braceStack.push(i);
    else if (ch === '}' && braceStack.length > 0) closeBrace[braceStack.pop()] = i;
    else if (ch === '[') bracketStack.push(i);
    else if (ch === ']' && bracketStack.length > 0) closeBracket[bracketStack.pop()] = i;
  }
  return { closeParen, openParen, closeBrace, closeBracket };
}

function parseTopLevelArgsLinear(text, openParenIdx, closeParen, closeBrace, closeBracket, maxArgs = 4) {
  const endParen = closeParen[openParenIdx];
  if (endParen < 0) return null;
  const args = [];
  const argStarts = [];
  let argStart = openParenIdx + 1;
  let k = argStart;
  while (k < endParen) {
    const ch = text[k];
    if (ch === '(' && closeParen[k] > k && closeParen[k] < endParen) {
      k = closeParen[k] + 1;
      continue;
    }
    if (ch === '{' && closeBrace[k] > k && closeBrace[k] < endParen) {
      k = closeBrace[k] + 1;
      continue;
    }
    if (ch === '[' && closeBracket[k] > k && closeBracket[k] < endParen) {
      k = closeBracket[k] + 1;
      continue;
    }
    if (ch === ',') {
      args.push(text.slice(argStart, k));
      argStarts.push(argStart);
      argStart = k + 1;
      if (args.length >= maxArgs) return { args, argStarts, endIdx: endParen + 1 };
    }
    k++;
  }
  const tail = text.slice(argStart, endParen);
  if (args.length > 0 || tail.trim().length > 0) {
    args.push(tail);
    argStarts.push(argStart);
  }
  return { args, argStarts, endIdx: endParen + 1 };
}

function getAdjacentCommentText(lineComments, lineHasCode, lineHasComment, lineNo) {
  const idx = lineNo - 1;
  if (idx < 0) return '';
  const parts = [];
  if (lineComments[idx]) parts.push(lineComments[idx]);
  for (let back = 1; back <= 6; back++) {
    const prevIdx = idx - back;
    if (prevIdx < 0) break;
    if (!lineHasComment[prevIdx] || lineHasCode[prevIdx]) break;
    if (lineComments[prevIdx]) parts.push(lineComments[prevIdx]);
  }
  return parts.join('\n');
}

// Single-pass O(N) outer-parenthesis stripping: finds all candidate paired outer `(...)`
// and computes the minimum interior nesting depth in one linear scan before slicing once.
function stripOuterParens(expr) {
  const s = String(expr ?? '').trim();
  if (!s.startsWith('(') || !s.endsWith(')')) return s;
  const pairs = [];
  let lo = 0;
  let hi = s.length - 1;
  while (lo < hi) {
    while (lo < hi && /\s/.test(s[lo])) lo++;
    while (lo < hi && /\s/.test(s[hi])) hi--;
    if (lo < hi && s[lo] === '(' && s[hi] === ')') {
      pairs.push([lo, hi]);
      lo++;
      hi--;
    } else {
      break;
    }
  }
  if (!pairs.length) return s;

  const innerLo = pairs[pairs.length - 1][0];
  const innerHi = pairs[pairs.length - 1][1];
  let depth = pairs.length;
  let minInteriorDepth = pairs.length;
  for (let i = innerLo + 1; i < innerHi; i++) {
    const ch = s[i];
    if (ch === '(') depth++;
    else if (ch === ')') {
      depth--;
      if (depth < 0) return s;
      if (depth < minInteriorDepth) minInteriorDepth = depth;
    }
  }
  if (depth !== pairs.length || minInteriorDepth <= 0) return s;
  const [cutLo, cutHi] = pairs[minInteriorDepth - 1];
  return s.slice(cutLo + 1, cutHi).trim();
}

const SIMPLE_NUM_RE = /^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[+-]?\d+)?$/i;

function evalSimpleNumericLiteral(expr) {
  const s = stripOuterParens(expr).replace(/_/g, '');
  if (!s) return null;
  if (SIMPLE_NUM_RE.test(s)) {
    const num = Number(s);
    return Number.isFinite(num) ? num : null;
  }
  if (/^[0-9.eE+\s*]+$/.test(s) && s.includes('*')) {
    const factors = s.split('*').map(p => p.trim());
    if (!factors.length || factors.some(f => !SIMPLE_NUM_RE.test(f))) return null;
    let prod = 1;
    for (const f of factors) prod *= Number(f);
    return Number.isFinite(prod) ? prod : null;
  }
  return null;
}

function collectParamIdentifiers(paramSlice, targetSet) {
  for (const m of paramSlice.matchAll(/(?<![\w$.])([A-Za-z_$][\w$]*)(?![\w$])/g)) {
    targetSet.add(m[1]);
  }
}

function collectAllParameterNames(skeleton, hashComments, closeParen, openParen) {
  const paramNames = new Set();
  if (!hashComments) {
    // Arrow function parameters: `ident =>` or `(...) =>`
    for (const m of skeleton.matchAll(/=>/g)) {
      let p = m.index - 1;
      while (p >= 0 && /\s/.test(skeleton[p])) p--;
      if (p < 0) continue;
      if (skeleton[p] === ')') {
        const open = openParen[p];
        if (open >= 0 && p - open <= 300) {
          collectParamIdentifiers(skeleton.slice(open + 1, p), paramNames);
        }
      } else if (/[\w$]/.test(skeleton[p])) {
        let start = p;
        while (start > 0 && /[\w$]/.test(skeleton[start - 1])) start--;
        const word = skeleton.slice(start, p + 1);
        if (/^[A-Za-z_$][\w$]*$/.test(word)) paramNames.add(word);
      }
    }
    // Named/anonymous function declarations/expressions: `function [name](...)`
    for (const m of skeleton.matchAll(/\bfunction\b/g)) {
      let k = m.index + m[0].length;
      const limit = Math.min(skeleton.length, k + 80);
      while (k < limit && skeleton[k] !== '(' && skeleton[k] !== '{' && skeleton[k] !== ';') k++;
      if (k < limit && skeleton[k] === '(' && closeParen[k] > k && closeParen[k] - k <= 300) {
        collectParamIdentifiers(skeleton.slice(k + 1, closeParen[k]), paramNames);
      }
    }
  } else {
    // Python `def name(...):` and `lambda ...:`
    for (const m of skeleton.matchAll(/\bdef\b/g)) {
      let k = m.index + m[0].length;
      const limit = Math.min(skeleton.length, k + 80);
      while (k < limit && skeleton[k] !== '(' && skeleton[k] !== '\n') k++;
      if (k < limit && skeleton[k] === '(' && closeParen[k] > k && closeParen[k] - k <= 300) {
        collectParamIdentifiers(skeleton.slice(k + 1, closeParen[k]), paramNames);
      }
    }
    for (const m of skeleton.matchAll(/\blambda\b/g)) {
      const head = skeleton.slice(m.index + 6, m.index + 207);
      const colon = head.indexOf(':');
      const nl = head.indexOf('\n');
      if (colon > 0 && (nl < 0 || colon < nl) && colon <= 194) {
        collectParamIdentifiers(head.slice(0, colon), paramNames);
      }
    }
  }
  return paramNames;
}

function collectPositiveNumericVars(skeleton, hashComments, closeParen, openParen, closeBrace, closeBracket) {
  const paramNames = collectAllParameterNames(skeleton, hashComments, closeParen, openParen);
  const declCounts = new Map();
  const positiveCandidates = new Set();
  const disqualified = new Set(paramNames);

  if (!hashComments) {
    // Linear scan over const/let/var declarations; only single-declared, non-reassigned, non-param `const` bindings qualify.
    for (const m of skeleton.matchAll(/\b(const|let|var)\b/g)) {
      const kind = m[1];
      let k = m.index + kind.length;
      const limit = Math.min(skeleton.length, k + 512);
      while (k < limit) {
        while (k < limit && /[ \t]/.test(skeleton[k])) k++;
        if (k >= limit || skeleton[k] === ';' || skeleton[k] === '\n') break;
        if (skeleton[k] === '{' || skeleton[k] === '[') {
          const close = skeleton[k] === '{' ? closeBrace[k] : closeBracket[k];
          if (close > k && close < limit) {
            collectParamIdentifiers(skeleton.slice(k + 1, close), disqualified);
            k = close + 1;
          }
          break;
        }
        const idStart = k;
        while (k < limit && /[\w$]/.test(skeleton[k])) k++;
        const ident = skeleton.slice(idStart, k);
        if (!/^[A-Za-z_$][\w$]*$/.test(ident)) break;
        declCounts.set(ident, (declCounts.get(ident) ?? 0) + 1);
        while (k < limit && /[ \t]/.test(skeleton[k])) k++;
        if (skeleton[k] !== '=' || skeleton[k + 1] === '=') {
          disqualified.add(ident);
          if (skeleton[k] === ',') { k++; continue; }
          break;
        }
        k++;
        const rhsStart = k;
        while (k < limit) {
          const ch = skeleton[k];
          if (ch === '(' && closeParen[k] > k && closeParen[k] < limit) { k = closeParen[k] + 1; continue; }
          if (ch === '{' && closeBrace[k] > k && closeBrace[k] < limit) { k = closeBrace[k] + 1; continue; }
          if (ch === '[' && closeBracket[k] > k && closeBracket[k] < limit) { k = closeBracket[k] + 1; continue; }
          if (ch === ',' || ch === ';' || ch === '\n') break;
          k++;
        }
        const rhs = skeleton.slice(rhsStart, k).trim();
        const val = evalSimpleNumericLiteral(rhs);
        if (kind === 'const' && val !== null && val > 0) positiveCandidates.add(ident);
        else disqualified.add(ident);
        if (skeleton[k] === ',') { k++; continue; }
        break;
      }
    }
    // Disqualify any identifier mutated via assignment or increment/decrement.
    for (const m of skeleton.matchAll(/(?<![.\w$])([A-Za-z_$][\w$]*)\s*(?:[+\-*/%&|^]?=(?![=>])|\+\+|--)/g)) {
      const before = skeleton.slice(Math.max(0, m.index - 12), m.index);
      if (!/\b(?:const|let|var)\s+$/.test(before)) disqualified.add(m[1]);
    }
  } else {
    for (const m of skeleton.matchAll(/(?:^|\n)[ \t]*([A-Za-z_][A-Za-z0-9_]*)[ \t]*=(?!=)[ \t]*([^\n;]+)/g)) {
      const ident = m[1];
      declCounts.set(ident, (declCounts.get(ident) ?? 0) + 1);
      const val = evalSimpleNumericLiteral(m[2]);
      if (val !== null && val > 0) positiveCandidates.add(ident);
      else disqualified.add(ident);
    }
  }

  const positiveVars = new Set();
  for (const ident of positiveCandidates) {
    if (declCounts.get(ident) === 1 && !disqualified.has(ident)) {
      positiveVars.add(ident);
    }
  }
  return positiveVars;
}

function collectEnclosingPromiseWrapperParams(skeleton, promiseIndex, openParen) {
  const params = new Set();
  const windowStart = Math.max(0, promiseIndex - 120);
  const before = skeleton.slice(windowStart, promiseIndex);
  const arrowIdx = before.lastIndexOf('=>');
  if (arrowIdx >= 0) {
    let p = windowStart + arrowIdx - 1;
    while (p >= windowStart && /\s/.test(skeleton[p])) p--;
    if (p >= windowStart && skeleton[p] === ')' && openParen[p] >= 0 && p - openParen[p] <= 120) {
      collectParamIdentifiers(skeleton.slice(openParen[p] + 1, p), params);
    } else if (p >= windowStart && /[\w$]/.test(skeleton[p])) {
      let start = p;
      while (start > 0 && /[\w$]/.test(skeleton[start - 1])) start--;
      params.add(skeleton.slice(start, p + 1));
    }
  }
  const fnMatch = /\bfunction(?:\s+[A-Za-z_$][\w$]*)?\s*\(([^()]{1,120})\)\s*\{[^{}]{0,60}$/.exec(before);
  if (fnMatch) collectParamIdentifiers(fnMatch[1], params);
  return params;
}

function isPositiveDelayExpression(argExpr, positiveVars, excludedIdents = EMPTY_STRING_SET) {
  const s = stripOuterParens(argExpr);
  if (!s) return false;
  const num = evalSimpleNumericLiteral(s);
  if (num !== null) return num > 0;
  if (/^[A-Za-z_$][\w$]*$/.test(s) && positiveVars.has(s) && !excludedIdents.has(s)) return true;
  return false;
}

function isUnconditionalResolveCallback(cbArg, resolveParam, rejectParam) {
  const trimmed = stripOuterParens(cbArg);
  if (!trimmed) return false;
  if (trimmed === resolveParam) return true;
  if (rejectParam) {
    const escapedReject = rejectParam.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    if (new RegExp(`(?<![\\w$])${escapedReject}(?![\\w$])`).test(trimmed)) return false;
  }
  if (/\b(?:reject|abort|kill|destroy|clearInterval|clearTimeout|throw|Error|exit)\b/.test(trimmed)) return false;
  const escaped = resolveParam.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const arrowOrFn = /^(?:async\s+)?(?:\([^()]*\)|[A-Za-z_$][\w$]*)\s*=>|^function\b/.test(trimmed);
  if (!arrowOrFn) return false;
  return new RegExp(`(?<![\\w$])${escaped}\\s*\\(`).test(trimmed);
}

function scanTimersPromiseImportsLinear(skeleton, literals, timersPromiseFns, timersPromiseNs) {
  // 1. Static ESM imports: isolate each `import` statement without crossing `;`, another `import`, or `\n` outside `{...}`.
  for (const m of skeleton.matchAll(/\bimport\b/g)) {
    const start = m.index;
    if (start > 0 && skeleton[start - 1] === '.') continue;
    let k = start + 6;
    while (k < skeleton.length && (skeleton[k] === ' ' || skeleton[k] === '\t')) k++;
    if (k >= skeleton.length || skeleton[k] === '(' || skeleton[k] === '.') continue;
    if (skeleton.startsWith('__STR_', k)) continue; // side-effect import `import '...'`
    let braceDepth = 0;
    const limit = Math.min(skeleton.length, k + 240);
    let end = k;
    while (end < limit) {
      const ch = skeleton[end];
      if (ch === '{') braceDepth++;
      else if (ch === '}' && braceDepth > 0) braceDepth--;
      else if (ch === ';') break;
      else if (ch === '\n' && braceDepth === 0) break;
      else if (braceDepth === 0 && ch === 'i' && skeleton.startsWith('import', end)
        && (end === k || !/[\w$]/.test(skeleton[end - 1]))
        && !/[\w$]/.test(skeleton[end + 6] ?? '')) {
        break;
      }
      end++;
    }
    const stmt = skeleton.slice(k, end);
    const fromMatch = /\bfrom\s+__STR_(\d+)__/.exec(stmt);
    if (!fromMatch) continue;
    const spec = String(literals[Number(fromMatch[1])] ?? '').trim();
    if (spec !== 'node:timers/promises' && spec !== 'timers/promises') continue;
    const clause = stmt.slice(0, fromMatch.index).trim();
    const nsMatch = /\*\s+as\s+([A-Za-z_$][\w$]*)/.exec(clause);
    if (nsMatch) timersPromiseNs.add(nsMatch[1]);
    const braceStart = clause.indexOf('{');
    const braceEnd = clause.lastIndexOf('}');
    if (braceStart >= 0 && braceEnd > braceStart) {
      const before = clause.slice(0, braceStart).replace(/,\s*$/, '').trim();
      if (/^[A-Za-z_$][\w$]*$/.test(before)) timersPromiseNs.add(before);
      for (const part of clause.slice(braceStart + 1, braceEnd).split(',')) {
        const piece = part.trim();
        const asM = /^setTimeout\s+as\s+([A-Za-z_$][\w$]*)$/.exec(piece);
        if (asM) timersPromiseFns.add(asM[1]);
        else if (piece === 'setTimeout') timersPromiseFns.add('setTimeout');
      }
    } else if (!nsMatch && /^[A-Za-z_$][\w$]*$/.test(clause)) {
      timersPromiseNs.add(clause);
    }
  }

  // 2. Dynamic `import(...)` / `require(...)` assignments: strictly linear forward scan up to `=`, `;`, or `\n`.
  for (const m of skeleton.matchAll(/\b(?:const|let|var)\b/g)) {
    const start = m.index + m[0].length;
    const limit = Math.min(skeleton.length, start + 160);
    let eqIdx = -1;
    let braceDepth = 0;
    for (let k = start; k < limit; k++) {
      const ch = skeleton[k];
      if (ch === '{') braceDepth++;
      else if (ch === '}' && braceDepth > 0) braceDepth--;
      else if (ch === ';' || (ch === '\n' && braceDepth === 0)) break;
      else if (ch === '=' && braceDepth === 0) {
        if (skeleton[k + 1] !== '=' && skeleton[k + 1] !== '>') eqIdx = k;
        break;
      }
    }
    if (eqIdx < 0) continue;
    const rhsSlice = skeleton.slice(eqIdx + 1, Math.min(skeleton.length, eqIdx + 96));
    const callMatch = /^\s*(?:await\s+)?(?:import|require)\s*\(\s*__STR_(\d+)__\s*\)/.exec(rhsSlice);
    if (!callMatch) continue;
    const spec = String(literals[Number(callMatch[1])] ?? '').trim();
    if (spec !== 'node:timers/promises' && spec !== 'timers/promises') continue;
    const lhs = skeleton.slice(start, eqIdx).trim();
    const braceStart = lhs.indexOf('{');
    const braceEnd = lhs.lastIndexOf('}');
    if (braceStart >= 0 && braceEnd > braceStart) {
      for (const part of lhs.slice(braceStart + 1, braceEnd).split(',')) {
        const piece = part.trim();
        const alias = /^setTimeout\s*:\s*([A-Za-z_$][\w$]*)$/.exec(piece);
        if (alias) timersPromiseFns.add(alias[1]);
        else if (piece === 'setTimeout') timersPromiseFns.add('setTimeout');
      }
    } else if (/^[A-Za-z_$][\w$]*$/.test(lhs)) {
      timersPromiseNs.add(lhs);
    }
  }
}

function collectTestFixedSleepFindings(text, { path = 'test/example.test.mjs' } = {}) {
  if (!canonicalRepoPath(path) || !isInspectableTestCodePath(path)) return [];
  const raw = String(text ?? '');
  const hashComments = /\.(?:py|rb)$/i.test(path);
  const { skeleton, literals, lineComments, lineHasCode, lineHasComment } = tokenizeTestCode(raw, { hashComments });
  const lineStarts = buildLineStarts(skeleton);
  const { closeParen, openParen, closeBrace, closeBracket } = buildDelimiterMaps(skeleton);
  const positiveVars = collectPositiveNumericVars(skeleton, hashComments, closeParen, openParen, closeBrace, closeBracket);
  const findings = [];
  const seenLines = new Set();

  const recordFinding = (offset, snippet) => {
    const line = lineNumberAt(lineStarts, offset);
    if (seenLines.has(line)) return;
    const commentCtx = getAdjacentCommentText(lineComments, lineHasCode, lineHasComment, line);
    if (SLEEP_ALLOW_COMMENT_RE.test(commentCtx) || hasTrackingIssueRef(commentCtx)) return;
    seenLines.add(line);
    const detail = `Fixed-duration sleep (${snippet}) in test code introduces timing flakiness. Wait on a deterministic event, condition, or injected clock instead (or annotate with // pdd-allow-sleep: <reason> or a tracking #issue).`;
    findings.push({
      filePath: path,
      line,
      order: 20,
      code: 'test-fixed-sleep',
      category: 'test hygiene',
      defaultSeverity: 'warn',
      detail,
      warning: `Warning: test hygiene: ${path}:${line} [test-fixed-sleep] ${detail}`,
    });
  };

  if (!hashComments) {
    const timersPromiseFns = new Set();
    const timersPromiseNs = new Set(['timersPromises']);
    scanTimersPromiseImportsLinear(skeleton, literals, timersPromiseFns, timersPromiseNs);

    // 1. JS/TS: new Promise((resolve) => setTimeout(resolve, <positive ms>))
    for (const m of skeleton.matchAll(/\bnew\s+Promise\s*\(/g)) {
      const openIdx = m.index + m[0].length - 1;
      const endIdx = closeParen[openIdx];
      if (endIdx < 0 || endIdx - openIdx > 600) continue;
      const body = skeleton.slice(openIdx + 1, endIdx);
      const execMatch = /^\s*(?:async\s+)?(?:\(\s*([A-Za-z_$][\w$]*)(?:\s*,\s*([A-Za-z_$][\w$]*))?\s*\)\s*=>|([A-Za-z_$][\w$]*)\s*=>|function(?:\s+[A-Za-z_$][\w$]*)?\s*\(\s*([A-Za-z_$][\w$]*)(?:\s*,\s*([A-Za-z_$][\w$]*))?\s*\))/.exec(body);
      if (!execMatch) continue;
      const resolveParam = execMatch[1] ?? execMatch[3] ?? execMatch[4];
      const rejectParam = execMatch[2] ?? execMatch[5] ?? null;
      if (!resolveParam || resolveParam === '_') continue;
      const rest = body.slice(execMatch[0].length);
      if (/\b(?:addEventListener|once|on|reject|abort|clearInterval|clearTimeout)\b/.test(rest)) continue;
      const stMatch = /\bsetTimeout\s*\(/.exec(rest);
      if (!stMatch) continue;
      const stOpenInSkel = openIdx + 1 + execMatch[0].length + stMatch.index + stMatch[0].length - 1;
      const parsed = parseTopLevelArgsLinear(skeleton, stOpenInSkel, closeParen, closeBrace, closeBracket, 3);
      if (!parsed || parsed.args.length < 2) continue;
      if (!isUnconditionalResolveCallback(parsed.args[0], resolveParam, rejectParam)) continue;
      const wrapperParams = collectEnclosingPromiseWrapperParams(skeleton, m.index, openParen);
      if (!isPositiveDelayExpression(parsed.args[1], positiveVars, wrapperParams)) continue;
      recordFinding(m.index, 'new Promise(...setTimeout...)');
    }

    // 2. JS/TS: timers/promises setTimeout(<ms>) & timersPromises.setTimeout(<ms>) / timers.promises.setTimeout(<ms>)
    for (const m of skeleton.matchAll(/(?<![\w$])([A-Za-z_$][\w$]*)\s*\.\s*(?:promises\s*\.\s*)?setTimeout\s*\(/g)) {
      const ns = m[1];
      const hasPromisesSegment = /\.\s*promises\s*\./.test(m[0]);
      if (!hasPromisesSegment && !timersPromiseNs.has(ns)) continue;
      const openIdx = m.index + m[0].length - 1;
      const parsed = parseTopLevelArgsLinear(skeleton, openIdx, closeParen, closeBrace, closeBracket, 2);
      if (!parsed || parsed.args.length < 1) continue;
      if (!isPositiveDelayExpression(parsed.args[0], positiveVars)) continue;
      recordFinding(m.index, `${ns}.setTimeout(...)`);
    }
    if (timersPromiseFns.size > 0) {
      for (const m of skeleton.matchAll(/(?<![.\w$])([A-Za-z_$][\w$]*)\s*\(/g)) {
        const fn = m[1];
        if (!timersPromiseFns.has(fn)) continue;
        const before = skeleton.slice(Math.max(0, m.index - 24), m.index);
        if (/\bfunction\s*$/.test(before)) continue;
        const openIdx = m.index + m[0].length - 1;
        const parsed = parseTopLevelArgsLinear(skeleton, openIdx, closeParen, closeBrace, closeBracket, 2);
        if (!parsed || parsed.args.length < 1) continue;
        if (!isPositiveDelayExpression(parsed.args[0], positiveVars)) continue;
        recordFinding(m.index, `timers/promises ${fn}(...)`);
      }
    }

    // 3. JS/TS: Atomics.wait(arr, idx, val, <positive timeout>)
    for (const m of skeleton.matchAll(/\bAtomics\s*\.\s*wait\s*\(/g)) {
      const openIdx = m.index + m[0].length - 1;
      const parsed = parseTopLevelArgsLinear(skeleton, openIdx, closeParen, closeBrace, closeBracket, 4);
      if (!parsed || parsed.args.length < 4) continue;
      if (!isPositiveDelayExpression(parsed.args[3], positiveVars)) continue;
      recordFinding(m.index, 'Atomics.wait(...)');
    }
  }

  // 4. Python (and JS): time.sleep(<secs>) / asyncio.sleep(<secs>)
  for (const m of skeleton.matchAll(/\b(time|asyncio)\s*\.\s*sleep\s*\(/g)) {
    const openIdx = m.index + m[0].length - 1;
    const parsed = parseTopLevelArgsLinear(skeleton, openIdx, closeParen, closeBrace, closeBracket, 2);
    if (!parsed || parsed.args.length < 1) continue;
    if (!isPositiveDelayExpression(parsed.args[0], positiveVars)) continue;
    recordFinding(m.index, `${m[1]}.sleep(...)`);
  }

  // 5. Standalone sleep(<ms>) in JS/TS/Python (excluding function/def declarations and method defs)
  for (const m of skeleton.matchAll(/(?<![.\w$])sleep\s*\(/g)) {
    const before = skeleton.slice(Math.max(0, m.index - 24), m.index);
    if (/(?:\bfunction|\bdef)\s*$/.test(before)) continue;
    const openIdx = m.index + m[0].length - 1;
    const endIdx = closeParen[openIdx];
    if (endIdx < 0) continue;
    const after = skeleton.slice(endIdx + 1, Math.min(skeleton.length, endIdx + 16));
    if (/^\s*\{/.test(after)) continue;
    const parsed = parseTopLevelArgsLinear(skeleton, openIdx, closeParen, closeBrace, closeBracket, 2);
    if (!parsed || parsed.args.length < 1) continue;
    if (!isPositiveDelayExpression(parsed.args[0], positiveVars)) continue;
    recordFinding(m.index, 'sleep(...)');
  }

  findings.sort((a, b) => a.line - b.line || a.order - b.order);
  return findings;
}

export function lintTestFixedSleeps(text, { path = 'test/example.test.mjs' } = {}) {
  return collectTestFixedSleepFindings(text, { path }).map(item => item.warning);
}

function resolveSingleLiteralString(expr, literals) {
  const trimmed = String(expr ?? '').trim();
  if (trimmed.length > 32) return null;
  const m = /^__STR_(\d+)__$/.exec(trimmed);
  if (!m) return null;
  const val = literals[Number(m[1])];
  return typeof val === 'string' ? val : null;
}

function extractExprStringText(expr, literals) {
  const bounded = String(expr ?? '').slice(0, 512);
  const parts = [];
  for (const m of bounded.matchAll(/__STR_(\d+)__/g)) {
    const val = literals[Number(m[1])];
    if (typeof val === 'string') parts.push(val);
  }
  return parts.join(' ');
}

// Strict O(1)-jump linear property extractor using precomputed delimiter maps.
function extractOptionPropertyValueLinear(skeleton, openBraceIdx, closeParen, closeBrace, closeBracket, propName, literals) {
  const endBrace = closeBrace[openBraceIdx];
  if (endBrace < 0) return null;
  let propStart = openBraceIdx + 1;
  let k = propStart;
  while (k <= endBrace) {
    if (k < endBrace) {
      const ch = skeleton[k];
      if (ch === '(' && closeParen[k] > k && closeParen[k] < endBrace) { k = closeParen[k] + 1; continue; }
      if (ch === '{' && closeBrace[k] > k && closeBrace[k] < endBrace) { k = closeBrace[k] + 1; continue; }
      if (ch === '[' && closeBracket[k] > k && closeBracket[k] < endBrace) { k = closeBracket[k] + 1; continue; }
      if (ch !== ',') { k++; continue; }
    }
    // Inspect top-level property segment [propStart, k)
    let colonIdx = -1;
    let scan = propStart;
    while (scan < k) {
      const ch = skeleton[scan];
      if (ch === '(' && closeParen[scan] > scan && closeParen[scan] < k) { scan = closeParen[scan] + 1; continue; }
      if (ch === '{' && closeBrace[scan] > scan && closeBrace[scan] < k) { scan = closeBrace[scan] + 1; continue; }
      if (ch === '[' && closeBracket[scan] > scan && closeBracket[scan] < k) { scan = closeBracket[scan] + 1; continue; }
      if (ch === ':') { colonIdx = scan; break; }
      scan++;
    }
    if (colonIdx >= 0) {
      const rawKey = skeleton.slice(propStart, colonIdx).trim();
      const key = resolveSingleLiteralString(rawKey, literals) ?? rawKey;
      if (key === propName) return skeleton.slice(colonIdx + 1, k).trim();
    }
    propStart = k + 1;
    k++;
  }
  return null;
}

function findOpeningBraceAtArg(skeleton, argStart, argLength, closeBrace) {
  let k = argStart;
  const end = argStart + argLength;
  while (k < end && /\s/.test(skeleton[k])) k++;
  if (k >= end || skeleton[k] !== '{') return -1;
  const closeIdx = closeBrace[k];
  if (closeIdx < 0 || closeIdx >= end) return -1;
  for (let tail = closeIdx + 1; tail < end; tail++) {
    if (!/\s/.test(skeleton[tail])) return -1;
  }
  return k;
}

function collectTestUnexcusedSkipFindings(text, { path = 'test/example.test.mjs' } = {}) {
  if (!canonicalRepoPath(path) || !isInspectableTestCodePath(path)) return [];
  const raw = String(text ?? '');
  const hashComments = /\.(?:py|rb)$/i.test(path);
  const { skeleton, literals, lineComments, lineHasCode, lineHasComment } = tokenizeTestCode(raw, { hashComments });
  const lineStarts = buildLineStarts(skeleton);
  const { closeParen, closeBrace, closeBracket } = buildDelimiterMaps(skeleton);
  const findings = [];
  const seenLines = new Set();

  const hasCommentExcuse = line => {
    const commentCtx = getAdjacentCommentText(lineComments, lineHasCode, lineHasComment, line);
    return SKIP_ALLOW_COMMENT_RE.test(commentCtx) || hasTrackingIssueRef(commentCtx);
  };

  const recordSkip = (offset, label) => {
    const line = lineNumberAt(lineStarts, offset);
    if (seenLines.has(line)) return;
    if (hasCommentExcuse(line)) return;
    seenLines.add(line);
    const detail = `Unexcused skipped test (${label}) without a tracking issue reference or substantive reason. Cite an issue (e.g. #1234) or use a conditional guard instead of silently skipping tests.`;
    findings.push({
      filePath: path,
      line,
      order: 21,
      code: 'test-unexcused-skip',
      category: 'test hygiene',
      defaultSeverity: 'warn',
      detail,
      warning: `Warning: test hygiene: ${path}:${line} [test-unexcused-skip] ${detail}`,
    });
  };

  if (!hashComments) {
    // 1. JS/TS: test.skip(, it.skip(, describe.skip(, suite.skip(, xit(, xtest(, xdescribe(
    const directSkipRe = /(?<![\w$.])((?:test|it|describe|suite)\s*\.\s*skip|xit|xtest|xdescribe)\s*\(/g;
    for (const m of skeleton.matchAll(directSkipRe)) {
      const openIdx = m.index + m[0].length - 1;
      const parsed = parseTopLevelArgsLinear(skeleton, openIdx, closeParen, closeBrace, closeBracket, 2);
      const titleText = parsed?.args?.[0] ? extractExprStringText(parsed.args[0], literals) : '';
      if (titleText && hasTrackingIssueRef(titleText)) continue;
      recordSkip(m.index, m[1].replace(/\s+/g, ''));
    }

    // 2. JS/TS: test(..., { skip: true | "" | placeholder }) and 1st-arg test({ skip: true }, fn)
    const optsSkipRe = /(?<![\w$.])(test|it|describe|suite)\s*\(/g;
    for (const m of skeleton.matchAll(optsSkipRe)) {
      const openIdx = m.index + m[0].length - 1;
      const parsed = parseTopLevelArgsLinear(skeleton, openIdx, closeParen, closeBrace, closeBracket, 3);
      if (!parsed || parsed.args.length < 2) continue;
      let optsIdx = -1;
      let openBraceIdx = findOpeningBraceAtArg(skeleton, parsed.argStarts[1], parsed.args[1].length, closeBrace);
      if (openBraceIdx >= 0) {
        optsIdx = 1;
      } else {
        openBraceIdx = findOpeningBraceAtArg(skeleton, parsed.argStarts[0], parsed.args[0].length, closeBrace);
        if (openBraceIdx >= 0) optsIdx = 0;
      }
      if (optsIdx < 0) continue;
      const skipVal = extractOptionPropertyValueLinear(skeleton, openBraceIdx, closeParen, closeBrace, closeBracket, 'skip', literals);
      if (skipVal === null) continue;
      const cleanedVal = stripOuterParens(skipVal);
      if (!cleanedVal || cleanedVal === 'false' || cleanedVal === 'undefined' || cleanedVal === 'null') continue;
      if (optsIdx === 1) {
        const titleText = extractExprStringText(parsed.args[0], literals);
        if (titleText && hasTrackingIssueRef(titleText)) continue;
      }
      if (cleanedVal === 'true' || cleanedVal === '!0') {
        recordSkip(m.index, optsIdx === 0 ? `${m[1]}({ skip: true }, ...)` : `${m[1]}(..., { skip: true })`);
        continue;
      }
      const skipStr = resolveSingleLiteralString(cleanedVal, literals);
      if (skipStr !== null) {
        if (!hasSubstantiveSkipReason(skipStr)) {
          recordSkip(m.index, `${m[1]}(..., { skip: ${JSON.stringify(skipStr)} })`);
        }
      }
      // Dynamic / conditional skip expression (e.g., !process.env.FOO, process.platform === 'win32') is allowed.
    }

    // 3. JS/TS: t.skip() / ctx.skip() with missing, empty, or placeholder reason
    const ctxSkipRe = /(?<![\w$.])(t|ctx)\s*\.\s*skip\s*\(/g;
    for (const m of skeleton.matchAll(ctxSkipRe)) {
      const openIdx = m.index + m[0].length - 1;
      const parsed = parseTopLevelArgsLinear(skeleton, openIdx, closeParen, closeBrace, closeBracket, 2);
      if (!parsed) continue;
      if (parsed.args.length === 0 || !parsed.args[0].trim()) {
        recordSkip(m.index, `${m[1]}.skip()`);
        continue;
      }
      const reasonStr = resolveSingleLiteralString(parsed.args[0], literals);
      if (reasonStr !== null && !hasSubstantiveSkipReason(reasonStr)) {
        recordSkip(m.index, `${m[1]}.skip(${JSON.stringify(reasonStr)})`);
      }
    }
  } else {
    // 4. Python: @pytest.mark.skip / @pytest.mark.skip(...) / @unittest.skip(...)
    // Note: @pytest.mark.skipif and @unittest.skipIf / @unittest.skipUnless do NOT match because of the word boundary after `skip`.
    const pySkipRe = /@(pytest\s*\.\s*mark\s*\.\s*skip|unittest\s*\.\s*skip)\b/g;
    for (const m of skeleton.matchAll(pySkipRe)) {
      const afterPos = m.index + m[0].length;
      const label = `@${m[1].replace(/\s+/g, '')}`;
      let wsEnd = afterPos;
      while (wsEnd < skeleton.length && (skeleton[wsEnd] === ' ' || skeleton[wsEnd] === '\t')) wsEnd++;
      if (skeleton[wsEnd] !== '(') {
        recordSkip(m.index, label);
        continue;
      }
      const parsed = parseTopLevelArgsLinear(skeleton, wsEnd, closeParen, closeBrace, closeBracket, 4);
      if (!parsed || parsed.args.length === 0 || parsed.args.every(a => !a.trim())) {
        recordSkip(m.index, `${label}()`);
        continue;
      }
      let reasonExpr = null;
      for (const arg of parsed.args) {
        const kv = /^\s*reason\s*=\s*([\s\S]+)$/.exec(arg);
        if (kv) { reasonExpr = kv[1].trim(); break; }
      }
      if (reasonExpr === null && !parsed.args[0].includes('=')) {
        reasonExpr = parsed.args[0].trim();
      }
      if (!reasonExpr) {
        recordSkip(m.index, `${label}(...)`);
        continue;
      }
      const reasonStr = resolveSingleLiteralString(reasonExpr, literals);
      if (reasonStr !== null && !hasSubstantiveSkipReason(reasonStr)) {
        recordSkip(m.index, `${label}(reason=${JSON.stringify(reasonStr)})`);
      }
    }
    // Also detect bare pytest.skip() inside Python test bodies with missing/empty/placeholder reason.
    for (const m of skeleton.matchAll(/(?<![.\w])pytest\s*\.\s*skip\s*\(/g)) {
      const openIdx = m.index + m[0].length - 1;
      const parsed = parseTopLevelArgsLinear(skeleton, openIdx, closeParen, closeBrace, closeBracket, 3);
      if (!parsed) continue;
      if (parsed.args.length === 0 || parsed.args.every(a => !a.trim())) {
        recordSkip(m.index, 'pytest.skip()');
        continue;
      }
      let reasonExpr = null;
      for (const arg of parsed.args) {
        const kv = /^\s*(?:reason|msg)\s*=\s*([\s\S]+)$/.exec(arg);
        if (kv) { reasonExpr = kv[1].trim(); break; }
      }
      if (reasonExpr === null && !parsed.args[0].includes('=')) reasonExpr = parsed.args[0].trim();
      if (!reasonExpr) {
        recordSkip(m.index, 'pytest.skip(...)');
        continue;
      }
      const reasonStr = resolveSingleLiteralString(reasonExpr, literals);
      if (reasonStr !== null && !hasSubstantiveSkipReason(reasonStr)) {
        recordSkip(m.index, `pytest.skip(${JSON.stringify(reasonStr)})`);
      }
    }
  }

  findings.sort((a, b) => a.line - b.line || a.order - b.order);
  return findings;
}

export function lintTestUnexcusedSkips(text, { path = 'test/example.test.mjs' } = {}) {
  return collectTestUnexcusedSkipFindings(text, { path }).map(item => item.warning);
}

const VALIDATION_WARNING_RE = /^Warning: validation lint: (.+):(\d+) \[([^\]]+)\] (.+)$/;

function parseValidationWarnings(rawWarnings, fallbackPath) {
  return rawWarnings.map((warning, idx) => {
    const match = VALIDATION_WARNING_RE.exec(warning);
    if (!match) {
      return {
        filePath: fallbackPath,
        line: 1,
        order: 30 + idx,
        code: 'silent-validation-skip',
        category: 'validation lint',
        detail: warning,
        warning,
      };
    }
    return {
      filePath: match[1],
      line: Number(match[2]) || 1,
      order: 30 + idx,
      code: match[3],
      category: 'validation lint',
      detail: match[4],
      warning,
    };
  });
}

function collectValidationCodeFindings(text, { path = 'test/example.test.mjs', kind = 'test', hasRealE2eCoverage = false, nativeOnlyTargets } = {}) {
  const { warnings } = lintValidationCode({ path, kind, text, hasRealE2eCoverage, nativeOnlyTargets });
  return parseValidationWarnings(warnings, path);
}

/**
 * Flag silent validation bypasses (such as real-binding-unavailable local skips or unconditional E2E skips).
 */
export function lintValidationSkips(text, { path = 'src/module.mjs', kind = 'code' } = {}) {
  return collectValidationCodeFindings(text, { path, kind, hasRealE2eCoverage: true })
    .filter(item => item.code === 'silent-validation-skip')
    .map(item => item.warning);
}

/**
 * Flag mock-only tests targeting runtime boundaries when no real E2E coverage exists.
 */
export function lintBoundaryMockOnlyTests(text, { path = 'test/example.test.mjs', hasRealE2eCoverage = false, nativeOnlyTargets } = {}) {
  return collectValidationCodeFindings(text, { path, kind: 'test', hasRealE2eCoverage, nativeOnlyTargets })
    .filter(item => item.code === 'boundary-mock-only-test')
    .map(item => item.warning);
}

const MAX_GLOB_WILDCARDS = 12;
const MAX_REGEX_GROUP_DEPTH = 16;

function encodeGlobSegment(segment) {
  let out = '';
  for (const ch of segment) {
    if (ch === '*') out += '[^/]*';
    else if (ch === '?') out += '[^/]';
    else if ('+^$()[]{}|.\\'.includes(ch)) out += `\\${ch}`;
    else out += ch;
  }
  return out;
}

function globToRegExp(glob) {
  const clean = String(glob ?? '').trim().replace(/\\/g, '/').replace(/^\.\//, '').replace(/\/+/g, '/').replace(/^\/+|\/+$/g, '');
  if (!clean || clean.length > 256) return null;
  const rawSegments = clean.split('/');
  const segments = [];
  for (const rawSeg of rawSegments) {
    const collapsed = /^\*+$/.test(rawSeg)
      ? (rawSeg.length >= 2 ? '**' : '*')
      : rawSeg.replace(/\*+/g, '*');
    if (collapsed === '**' && segments.at(-1) === '**') continue;
    segments.push(collapsed);
  }
  let wildcardCount = 0;
  for (const seg of segments) {
    if (seg === '**') wildcardCount += 1;
    else wildcardCount += (seg.match(/[*?]/g) ?? []).length;
  }
  if (wildcardCount > MAX_GLOB_WILDCARDS) return null;

  let re = '^';
  for (let idx = 0; idx < segments.length; idx++) {
    const seg = segments[idx];
    if (seg === '**') {
      if (segments.length === 1) re += '.*';
      else if (idx === 0) re += '(?:.*/)?';
      else if (idx === segments.length - 1) re += '/.*';
      else re += '(?:/.*)?';
      continue;
    }
    if (idx > 0 && segments[idx - 1] !== '**') re += '/';
    else if (idx > 0 && segments[idx - 1] === '**' && idx - 1 > 0) re += '/';
    re += encodeGlobSegment(seg);
  }
  re += '$';
  return new RegExp(re);
}

function readRegexQuantifier(pattern, pos) {
  if (pos >= pattern.length) return null;
  const ch = pattern[pos];
  if (ch === '*' || ch === '+') {
    const lazy = pattern[pos + 1] === '?' ? 1 : 0;
    return { len: 1 + lazy, unbounded: true, repeats: true };
  }
  if (ch === '?') {
    const lazy = pattern[pos + 1] === '?' ? 1 : 0;
    return { len: 1 + lazy, unbounded: false, repeats: false };
  }
  if (ch === '{') {
    const m = /^\{(\d+)(?:,(\d*))?\}(\?)?/.exec(pattern.slice(pos));
    if (!m) return null;
    const min = Number(m[1]);
    const hasComma = m[2] !== undefined;
    const max = hasComma ? (m[2] === '' ? Infinity : Number(m[2])) : min;
    if (max < min) return null;
    return { len: m[0].length, unbounded: max === Infinity, repeats: max > 1 };
  }
  return null;
}

function isSafeRegexPattern(pattern, cleanFlags) {
  const ignoreCase = cleanFlags.includes('i');
  const normChar = ch => (ignoreCase ? ch.toLowerCase() : ch);
  const stack = [];
  const newBranch = () => ({ firstChar: null, pureLiteralPrefix: true, len: 0 });
  const recordAtomOnTop = (literalChar = null) => {
    if (!stack.length) return;
    const branch = stack.at(-1).branches.at(-1);
    if (branch.len === 0) {
      if (literalChar !== null && branch.pureLiteralPrefix) branch.firstChar = normChar(literalChar);
      else branch.pureLiteralPrefix = false;
    }
    branch.len += 1;
  };
  const markQuantifierOnTop = quant => {
    if (!stack.length) return;
    const top = stack.at(-1);
    top.hasInnerQuantifier = true;
    if (quant.unbounded) top.hasUnboundedQuantifier = true;
  };

  let inCharClass = false;
  let i = 0;
  while (i < pattern.length) {
    const ch = pattern[i];
    if (inCharClass) {
      if (ch === '\\') { i += 2; continue; }
      if (ch === ']') {
        inCharClass = false;
        i += 1;
        const q = readRegexQuantifier(pattern, i);
        if (q) { markQuantifierOnTop(q); i += q.len; }
        continue;
      }
      i += 1;
      continue;
    }

    if (ch === '\\') {
      const esc = pattern[i + 1];
      if (!esc) return false;
      if (/^[1-9]$/.test(esc) || esc === 'k') return false;
      let step = 2;
      if ((esc === 'p' || esc === 'P' || esc === 'u') && pattern[i + 2] === '{') {
        const close = pattern.indexOf('}', i + 3);
        if (close < 0) return false;
        step = close - i + 1;
      }
      if (esc === 'b' || esc === 'B') {
        i += step;
        continue;
      }
      const isClassEscape = /^[dDwWsSpP]$/.test(esc);
      recordAtomOnTop(isClassEscape ? null : esc);
      i += step;
      const q = readRegexQuantifier(pattern, i);
      if (q) { markQuantifierOnTop(q); i += q.len; }
      continue;
    }

    if (ch === '[') {
      inCharClass = true;
      recordAtomOnTop(null);
      i += 1;
      continue;
    }

    if (ch === '(') {
      if (stack.length >= MAX_REGEX_GROUP_DEPTH) return false;
      let kind = 'normal';
      let step = 1;
      if (pattern[i + 1] === '?') {
        const rest = pattern.slice(i + 2);
        if (rest.startsWith(':')) { step = 3; }
        else if (rest.startsWith('=') || rest.startsWith('!')) { kind = 'lookaround'; step = 3; }
        else if (rest.startsWith('<=') || rest.startsWith('<!')) { kind = 'lookaround'; step = 4; }
        else if (rest.startsWith('<')) {
          const close = rest.indexOf('>');
          if (close <= 1) return false;
          step = 2 + close + 1;
        } else {
          return false;
        }
      }
      if (kind === 'normal') recordAtomOnTop(null);
      stack.push({ kind, hasInnerQuantifier: false, hasUnboundedQuantifier: false, branches: [newBranch()] });
      i += step;
      continue;
    }

    if (ch === '|') {
      if (stack.length) stack.at(-1).branches.push(newBranch());
      i += 1;
      continue;
    }

    if (ch === ')') {
      if (!stack.length) return false;
      const frame = stack.pop();
      if (frame.kind === 'lookaround' && frame.hasUnboundedQuantifier) return false;
      i += 1;
      const q = readRegexQuantifier(pattern, i);
      if (q) {
        if (frame.kind === 'lookaround') return false;
        if (frame.hasInnerQuantifier) return false;
        if (q.repeats && frame.branches.length > 1) {
          const starts = [];
          for (const br of frame.branches) {
            if (br.len === 0 || !br.pureLiteralPrefix || br.firstChar === null) return false;
            starts.push(br.firstChar);
          }
          if (new Set(starts).size !== frame.branches.length) return false;
        }
        markQuantifierOnTop(q);
        i += q.len;
      }
      if (stack.length && frame.kind === 'normal') {
        if (frame.hasInnerQuantifier) stack.at(-1).hasInnerQuantifier = true;
        if (frame.hasUnboundedQuantifier) stack.at(-1).hasUnboundedQuantifier = true;
      }
      continue;
    }

    if (ch === '^' || ch === '$') {
      i += 1;
      continue;
    }

    const strayQuant = readRegexQuantifier(pattern, i);
    if (strayQuant) {
      markQuantifierOnTop(strayQuant);
      i += strayQuant.len;
      continue;
    }

    recordAtomOnTop(ch === '.' ? null : ch);
    i += 1;
    const q = readRegexQuantifier(pattern, i);
    if (q) { markQuantifierOnTop(q); i += q.len; }
  }

  return !inCharClass && stack.length === 0;
}

function parseRegexSafe(pattern, flags = '') {
  if (typeof pattern !== 'string' || !pattern.length || pattern.length > 512) return null;
  if (typeof flags !== 'string' || flags.length > 8) return null;
  const cleanFlags = [...new Set(flags.replace(/[gy]/g, '').split(''))].join('');
  if (!/^[imsu]*$/.test(cleanFlags)) return null;
  if (!isSafeRegexPattern(pattern, cleanFlags)) return null;
  try {
    return new RegExp(pattern, cleanFlags);
  } catch {
    return null;
  }
}

const VALID_TARGETS = new Set(['prompt', 'story', 'test', 'code', 'all']);
const VALID_SEVERITIES = new Set(['off', 'warn', 'error']);

function mergeLintConfigSection(rawLint, { sourcePath, disabledRules, ruleSeverities, customRules, configErrors }) {
  const addConfigError = detail => configErrors.push({
    filePath: sourcePath,
    line: 1,
    order: 0,
    code: 'lint-config-invalid',
    category: 'lint config',
    detail,
  });

  if (typeof rawLint !== 'object' || rawLint === null || Array.isArray(rawLint)) {
    addConfigError(`"lint" in ${sourcePath} must be a JSON object.`);
    return;
  }

  if (rawLint.disable !== undefined) {
    if (!Array.isArray(rawLint.disable) || rawLint.disable.some(id => typeof id !== 'string' || !RULE_ID_RE.test(id))) {
      addConfigError(`"lint.disable" in ${sourcePath} must be an array of valid rule IDs.`);
    } else {
      for (const id of rawLint.disable) disabledRules.add(id);
    }
  }

  if (rawLint.rules !== undefined) {
    if (!rawLint.rules || typeof rawLint.rules !== 'object' || Array.isArray(rawLint.rules)) {
      addConfigError(`"lint.rules" in ${sourcePath} must be an object mapping rule IDs to "off", "warn", or "error".`);
    } else {
      for (const [id, spec] of Object.entries(rawLint.rules)) {
        if (!RULE_ID_RE.test(id)) {
          addConfigError(`Invalid rule ID "${id}" in "lint.rules".`);
          continue;
        }
        const sev = typeof spec === 'string' ? spec : (spec && typeof spec === 'object' && !Array.isArray(spec) ? spec.severity : null);
        if (!VALID_SEVERITIES.has(sev)) {
          addConfigError(`Rule "${id}" in "lint.rules" must use severity "off", "warn", or "error".`);
          continue;
        }
        ruleSeverities.set(id, sev);
        if (sev === 'off') disabledRules.add(id);
        else disabledRules.delete(id);
      }
    }
  }

  if (rawLint.custom_rules !== undefined) {
    if (!Array.isArray(rawLint.custom_rules)) {
      addConfigError(`"lint.custom_rules" in ${sourcePath} must be an array of rule objects.`);
    } else {
      for (let idx = 0; idx < rawLint.custom_rules.length; idx++) {
        const rawRule = rawLint.custom_rules[idx];
        if (!rawRule || typeof rawRule !== 'object' || Array.isArray(rawRule)) {
          addConfigError(`Entry ${idx} in "lint.custom_rules" must be an object.`);
          continue;
        }
        const id = rawRule.id;
        if (typeof id !== 'string' || !RULE_ID_RE.test(id)) {
          addConfigError(`Entry ${idx} in "lint.custom_rules" requires a valid "id" (letters, digits, "-", "_", ".").`);
          continue;
        }
        const rawTarget = rawRule.target ?? (rawRule.include ? 'all' : 'prompt');
        const targetList = Array.isArray(rawTarget) ? rawTarget : [rawTarget];
        if (!targetList.length || targetList.some(t => typeof t !== 'string' || !VALID_TARGETS.has(t))) {
          addConfigError(`Custom rule "${id}" has invalid "target" (choose "prompt", "story", "test", "code", or "all").`);
          continue;
        }
        const severity = rawRule.severity ?? 'warn';
        if (!VALID_SEVERITIES.has(severity)) {
          addConfigError(`Custom rule "${id}" has invalid "severity" (choose "off", "warn", or "error").`);
          continue;
        }

        const toGlobs = (val, fieldName) => {
          if (val === undefined) return [];
          const arr = typeof val === 'string' ? [val] : (Array.isArray(val) ? val : null);
          if (!arr || arr.some(g => typeof g !== 'string')) {
            addConfigError(`Custom rule "${id}" field "${fieldName}" must be a glob string or array of strings.`);
            return null;
          }
          const compiled = arr.map(globToRegExp);
          if (compiled.some(r => r === null)) {
            addConfigError(`Custom rule "${id}" field "${fieldName}" contains an invalid glob.`);
            return null;
          }
          return compiled;
        };

        const includeMatchers = toGlobs(rawRule.include, 'include');
        const excludeMatchers = toGlobs(rawRule.exclude, 'exclude');
        if (includeMatchers === null || excludeMatchers === null) continue;

        let forbidRegex = null;
        if (rawRule.forbid_pattern !== undefined) {
          forbidRegex = parseRegexSafe(rawRule.forbid_pattern, rawRule.flags ?? '');
          if (!forbidRegex) {
            addConfigError(`Custom rule "${id}" has an invalid "forbid_pattern" regular expression.`);
            continue;
          }
        }

        let requireRegex = null;
        if (rawRule.require_pattern !== undefined) {
          requireRegex = parseRegexSafe(rawRule.require_pattern, rawRule.flags ?? '');
          if (!requireRegex) {
            addConfigError(`Custom rule "${id}" has an invalid "require_pattern" regular expression.`);
            continue;
          }
        }

        let requireHeading = null;
        if (rawRule.require_heading !== undefined) {
          if (typeof rawRule.require_heading !== 'string' || !rawRule.require_heading.trim()) {
            addConfigError(`Custom rule "${id}" field "require_heading" must be a nonblank string.`);
            continue;
          }
          requireHeading = rawRule.require_heading.trim();
        }

        let maxLines = null;
        if (rawRule.max_lines !== undefined) {
          if (!Number.isInteger(rawRule.max_lines) || rawRule.max_lines < 1) {
            addConfigError(`Custom rule "${id}" field "max_lines" must be a positive integer.`);
            continue;
          }
          maxLines = rawRule.max_lines;
        }

        if (!forbidRegex && !requireRegex && !requireHeading && maxLines === null) {
          addConfigError(`Custom rule "${id}" must specify at least one check ("forbid_pattern", "require_pattern", "require_heading", or "max_lines").`);
          continue;
        }

        const message = typeof rawRule.message === 'string' && rawRule.message.trim()
          ? rawRule.message.trim()
          : `Custom project lint rule "${id}" failed.`;

        customRules.push({
          id,
          targets: new Set(targetList),
          severity,
          includeMatchers,
          excludeMatchers,
          forbidRegex,
          requireRegex,
          requireHeading,
          maxLines,
          message,
        });
      }
    }
  }
}

function loadWorkspaceLintRuleFiles(realRoot, target) {
  let loadedAny = false;
  for (const relDir of ['rules', 'rules/lint']) {
    try {
      const st = lstatSync(join(realRoot, relDir));
      if (st.isSymbolicLink() || !st.isDirectory()) return false;
    } catch {
      return false;
    }
  }

  let entries;
  try {
    entries = readdirSync(join(realRoot, 'rules/lint')).filter(name => name.endsWith('.json')).sort();
  } catch {
    return false;
  }

  for (const name of entries) {
    const relPath = `rules/lint/${name}`;
    const rawText = readSafeUtf8(realRoot, relPath);
    if (rawText === null) continue;
    loadedAny = true;
    let parsed;
    try {
      parsed = JSON.parse(rawText);
    } catch {
      target.configErrors.push({
        filePath: relPath,
        line: 1,
        order: 0,
        code: 'lint-config-invalid',
        category: 'lint config',
        detail: `${relPath} contains invalid JSON.`,
      });
      continue;
    }
    const section = Array.isArray(parsed)
      ? { custom_rules: parsed }
      : (parsed && typeof parsed === 'object' && typeof parsed.id === 'string'
        && !Object.hasOwn(parsed, 'disable') && !Object.hasOwn(parsed, 'rules') && !Object.hasOwn(parsed, 'custom_rules')
        ? { custom_rules: [parsed] }
        : parsed);
    mergeLintConfigSection(section, { sourcePath: relPath, ...target });
  }
  return loadedAny;
}

export function loadProjectLintConfig(rootOrObject) {
  const empty = {
    configured: false,
    disabledRules: new Set(),
    ruleSeverities: new Map(),
    customRules: [],
    configErrors: [],
  };
  if (!rootOrObject) return empty;

  const target = {
    disabledRules: new Set(),
    ruleSeverities: new Map(),
    customRules: [],
    configErrors: [],
  };
  let configured = false;

  if (typeof rootOrObject === 'string') {
    let realRoot;
    try { realRoot = realpathSync(rootOrObject); } catch { return empty; }
    // Workspace-local rules/lint/*.json load first; explicit pdd.json "lint" overrides below.
    if (loadWorkspaceLintRuleFiles(realRoot, target)) configured = true;

    const rawText = readSafeUtf8(realRoot, 'pdd.json');
    if (rawText !== null) {
      let parsed;
      try {
        parsed = JSON.parse(rawText);
      } catch {
        target.configErrors.push({
          filePath: 'pdd.json',
          line: 1,
          order: 0,
          code: 'lint-config-invalid',
          category: 'lint config',
          detail: 'pdd.json contains invalid JSON.',
        });
        return { configured: true, ...target };
      }
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed) && Object.hasOwn(parsed, 'lint') && parsed.lint !== undefined && parsed.lint !== null) {
        configured = true;
        mergeLintConfigSection(parsed.lint, { sourcePath: 'pdd.json', ...target });
      }
    }
    return configured ? { configured: true, ...target } : empty;
  }

  if (typeof rootOrObject === 'object' && !Array.isArray(rootOrObject)) {
    const rawLint = Object.hasOwn(rootOrObject, 'lint') ? rootOrObject.lint : rootOrObject;
    if (rawLint === undefined || rawLint === null) return empty;
    mergeLintConfigSection(rawLint, { sourcePath: 'pdd.json', ...target });
    return { configured: true, ...target };
  }

  return empty;
}

function headingMatches(contentText, requiredHeading) {
  const hasHashes = /^#{1,6}\s+/.test(requiredHeading);
  const lines = contentText.split(/\r?\n/);
  for (const line of lines) {
    if (hasHashes) {
      if (line.trim().toLowerCase() === requiredHeading.toLowerCase()) return true;
    } else {
      const m = /^ {0,3}#{1,6}\s+(.+)$/.exec(line);
      if (m && m[1].trim().toLowerCase() === requiredHeading.toLowerCase()) return true;
    }
  }
  return false;
}

function evaluateCustomRulesOnFile(customRules, { filePath, kind, rawText }) {
  const findings = [];
  const inspectText = kind === 'prompt' ? stripPromptMetadataPreservingLines(rawText) : rawText;
  const lineCount = kind === 'prompt' ? countPromptProseLines(rawText) : countFileLines(rawText);
  const lineStarts = buildLineStarts(inspectText);

  for (let idx = 0; idx < customRules.length; idx++) {
    const rule = customRules[idx];
    if (rule.severity === 'off') continue;
    if (!rule.targets.has('all') && !rule.targets.has(kind)) continue;
    if (rule.includeMatchers.length && !rule.includeMatchers.some(re => re.test(filePath))) continue;
    if (rule.excludeMatchers.some(re => re.test(filePath))) continue;

    if (rule.forbidRegex) {
      const m = rule.forbidRegex.exec(inspectText);
      if (m) {
        const line = lineNumberAt(lineStarts, m.index);
        findings.push({
          filePath,
          line,
          order: 50 + idx,
          code: rule.id,
          category: 'custom rule',
          defaultSeverity: rule.severity,
          detail: rule.message,
        });
      }
    }

    if (rule.requireRegex && !rule.requireRegex.test(inspectText)) {
      findings.push({
        filePath,
        line: 1,
        order: 50 + idx,
        code: rule.id,
        category: 'custom rule',
        defaultSeverity: rule.severity,
        detail: rule.message,
      });
    }

    if (rule.requireHeading && !headingMatches(inspectText, rule.requireHeading)) {
      findings.push({
        filePath,
        line: 1,
        order: 50 + idx,
        code: rule.id,
        category: 'custom rule',
        defaultSeverity: rule.severity,
        detail: rule.message,
      });
    }

    if (rule.maxLines !== null && lineCount > rule.maxLines) {
      findings.push({
        filePath,
        line: 1,
        order: 50 + idx,
        code: rule.id,
        category: 'custom rule',
        defaultSeverity: rule.severity,
        detail: `${rule.message} (${lineCount} lines > max ${rule.maxLines}).`,
      });
    }
  }
  return findings;
}

function isEligibleProductionCodeFile(path) {
  return canonicalRepoPath(path)
    && CODE_FILE_EXT.test(path)
    && !path.endsWith('.prompt.md')
    && !isTestOwnedPath(path)
    && !FIXTURE_DIR.test(path)
    && !EXAMPLE_DIR.test(path)
    && !NON_CODE_DIR.test(path);
}

function scenarioPromptRefs(doc) {
  if (!doc || typeof doc !== 'object') return [];
  const refs = [];
  if (typeof doc.entry_path === 'string') refs.push(doc.entry_path.replace(/^\.\//, ''));
  if (Array.isArray(doc.entry_paths)) {
    for (const p of doc.entry_paths) if (typeof p === 'string') refs.push(p.replace(/^\.\//, ''));
  }
  if (Array.isArray(doc.steps)) {
    for (const step of doc.steps) {
      if (typeof step?.entry_path === 'string') refs.push(step.entry_path.replace(/^\.\//, ''));
    }
  }
  if (Array.isArray(doc.context)) {
    for (const item of doc.context) {
      if (typeof item === 'string') refs.push(item.replace(/^\.\//, ''));
      else if (typeof item?.prompt_path === 'string') refs.push(item.prompt_path.replace(/^\.\//, ''));
    }
  }
  return refs;
}

function buildStoriesByStem(scopedFiles) {
  const storiesByStem = new Map();
  for (const file of scopedFiles) {
    if (!isLintableStoryPath(file)) continue;
    const stem = posix.basename(file).replace(/\.md$/i, '');
    if (!storiesByStem.has(stem)) storiesByStem.set(stem, []);
    storiesByStem.get(stem).push(file);
  }
  return storiesByStem;
}

function inferScenarioStoryPath(doc, scenarioPath, storiesByStem) {
  if (typeof doc?.story_path === 'string' && doc.story_path.trim()) {
    return doc.story_path.trim().replace(/^\.\//, '');
  }
  if (!doc || typeof doc !== 'object' || Array.isArray(doc)) return null;
  const base = posix.basename(scenarioPath, '.json');
  const owners = storiesByStem.has(base) ? [base] : [];
  for (let at = base.lastIndexOf('.'); at > 0; at = base.lastIndexOf('.', at - 1)) {
    if (storiesByStem.has(base.slice(0, at))) owners.push(base.slice(0, at));
  }
  if (owners.length === 1) {
    const matches = storiesByStem.get(owners[0]) ?? [];
    if (matches.length === 1) return matches[0];
  }
  return null;
}

export function lintRepoProject({ root, files, promptPaths, tests, config, workspaceRoot, workspacePolicy } = {}) {
  const empty = { ok: true, configured: false, warnings: [], errors: [], findings: [] };
  if (!root || typeof root !== 'string') return empty;
  let realRoot, policy;
  try {
    realRoot = realpathSync(root);
    if (workspacePolicy !== undefined && workspacePolicy !== null) {
      policy = workspacePolicy;
    } else if (typeof workspaceRoot === 'string' && workspaceRoot.trim()) {
      policy = workspace.policy({ root: realpathSync(workspaceRoot) });
    } else {
      policy = workspace.policy({ root: realRoot });
    }
  } catch {
    return empty;
  }

  let rawFiles;
  try {
    rawFiles = Array.isArray(files) ? files : gitFiles(realRoot);
  } catch {
    return empty;
  }

  const lintConfig = loadProjectLintConfig(config !== undefined ? config : realRoot);
  const allowedFiles = [...new Set(rawFiles)]
    .filter(path => canonicalRepoPath(path) && !isSecretPath(path) && workspace.allows(policy, path))
    .sort();

  const selectedInputs = [
    ...(Array.isArray(promptPaths) ? promptPaths : []).filter(p => typeof p === 'string').map(p => p.replace(/^\.\//, '')),
    ...(Array.isArray(tests) ? tests : []).map(t => (typeof t === 'string' ? t : t?.path)).filter(p => typeof p === 'string').map(p => p.replace(/^\.\//, '')),
  ];
  const allowFixtures = selectedInputs.some(p => FIXTURE_DIR.test(p));
  const scopedFiles = allowFixtures ? allowedFiles : allowedFiles.filter(p => !FIXTURE_DIR.test(p));
  const scopedSet = new Set(scopedFiles);

  // Build prompt <-> production code ownership map across the repository so prompt size, structure, and scoped test checks have ownership facts.
  const allPrompts = scopedFiles.filter(p => p.endsWith('.prompt.md'));
  const prodCodePaths = scopedFiles.filter(isEligibleProductionCodeFile);
  const promptTextCache = new Map();
  const getPromptText = p => {
    if (!promptTextCache.has(p)) promptTextCache.set(p, readSafeUtf8(realRoot, p));
    return promptTextCache.get(p);
  };

  const ownedCodeByPrompt = new Map();
  const promptOwnersByCode = new Map();
  if (allPrompts.length && prodCodePaths.length) {
    const rawBindings = scopedSet.has('pdd-bindings.json') ? readSafeUtf8(realRoot, 'pdd-bindings.json') : null;
    const heads = prodCodePaths.map(p => {
      const txt = readSafeUtf8(realRoot, p);
      return { path: p, content: typeof txt === 'string' ? txt.slice(0, HEAD_BYTES + 1) : null, fullText: txt };
    });
    const codeTextByPath = new Map(heads.filter(h => typeof h.fullText === 'string').map(h => [h.path, h.fullText]));
    const promptRows = allPrompts.map(p => ({ path: p, content: getPromptText(p) })).filter(r => typeof r.content === 'string');
    const ownership = resolveOwners({
      paths: prodCodePaths,
      allPaths: scopedFiles,
      bindings: rawBindings,
      heads: heads.map(({ path: p, content }) => ({ path: p, content })),
      prompts: promptRows,
    });
    for (const row of ownership.files) {
      if (!row.owners.length || !codeTextByPath.has(row.path)) continue;
      promptOwnersByCode.set(row.path, row.owners);
      for (const owner of row.owners) {
        if (!ownedCodeByPrompt.has(owner)) ownedCodeByPrompt.set(owner, []);
        ownedCodeByPrompt.get(owner).push({ path: row.path, text: codeTextByPath.get(row.path) });
      }
    }
  }

  const rawFindings = [...lintConfig.configErrors.map(err => ({ ...err, defaultSeverity: 'error' }))];

  // 1. Prompts: code fences, structure/diagrams, prompt-vs-code size, and custom prompt rules
  const targetPrompts = Array.isArray(promptPaths)
    ? [...new Set(promptPaths.filter(p => typeof p === 'string').map(p => p.replace(/^\.\//, '')).filter(p => scopedSet.has(p) && p.endsWith('.prompt.md')))].sort()
    : allPrompts;

  for (const promptPath of targetPrompts) {
    const content = getPromptText(promptPath);
    if (typeof content !== 'string') continue;
    const ownedCode = ownedCodeByPrompt.get(promptPath) ?? [];

    for (const f of collectPromptCodeBlockFindings(content, { path: promptPath })) {
      rawFindings.push({ ...f, defaultSeverity: 'warn' });
    }
    for (const f of collectPromptStructureFindings(content, { path: promptPath, hasOwnedCode: ownedCode.length > 0 })) {
      rawFindings.push({ ...f, defaultSeverity: 'warn' });
    }
    for (const f of collectPromptSizeFindings(content, ownedCode, { path: promptPath })) {
      rawFindings.push({ ...f, defaultSeverity: 'warn' });
    }
    if (isNativeOnlyPrompt(content)) {
      for (const f of collectNativeOnlyContractFindings(content, { path: promptPath })) {
        rawFindings.push(f);
      }
    }
    if (hasNativeOnlyFrontmatter(content)) {
      const directTargets = extractDependencyLinkTargets(content, promptPath).filter(p => scopedSet.has(p));
      const directCheckablePrompts = [];
      const directContracts = [];
      for (const target of directTargets) {
        if (target.endsWith('.prompt.md')) {
          const depText = getPromptText(target);
          if (typeof depText === 'string' && !isNativeOnlyPrompt(depText)) {
            directCheckablePrompts.push(target);
          }
        } else if (target.endsWith('.md')) {
          directContracts.push(target);
        }
      }
      if (directCheckablePrompts.length > 0) {
        const visited = new Set([promptPath]);
        const queue = [
          ...directCheckablePrompts.map(p => ({ path: p, isPrompt: true })),
          ...directContracts.map(p => ({ path: p, isPrompt: false })),
        ];
        const depSources = [];
        while (queue.length > 0) {
          const cur = queue.shift();
          if (visited.has(cur.path)) continue;
          visited.add(cur.path);
          const depText = cur.isPrompt ? getPromptText(cur.path) : readSafeUtf8(realRoot, cur.path);
          if (typeof depText !== 'string') continue;
          if (cur.isPrompt && isNativeOnlyPrompt(depText)) continue;
          depSources.push({ path: cur.path, text: depText, isPrompt: cur.isPrompt });
          for (const nextTarget of extractDependencyLinkTargets(depText, cur.path)) {
            if (visited.has(nextTarget) || !scopedSet.has(nextTarget)) continue;
            if (nextTarget.endsWith('.prompt.md')) queue.push({ path: nextTarget, isPrompt: true });
            else if (nextTarget.endsWith('.md')) queue.push({ path: nextTarget, isPrompt: false });
          }
        }
        for (const f of collectNativeOnlyPortParityFindings(content, depSources, {
          path: promptPath,
          dependencyPaths: directCheckablePrompts,
        })) {
          rawFindings.push(f);
        }
      }
    }
    if (lintConfig.customRules.length) {
      rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, {
        filePath: promptPath,
        kind: 'prompt',
        rawText: content,
      }));
    }
  }

  // 2. Stories: criteria/quality hygiene and custom Story rules
  let targetStories = [];
  if (promptPaths === undefined && tests === undefined) {
    targetStories = scopedFiles.filter(isLintableStoryPath);
  } else {
    const storyCandidates = new Set();
    const storiesByStem = buildStoriesByStem(scopedFiles);
    if (Array.isArray(tests)) {
      for (const entry of tests) {
        if (entry && typeof entry === 'object' && typeof entry.storyPath === 'string') {
          storyCandidates.add(entry.storyPath.replace(/^\.\//, ''));
        }
        const tPath = typeof entry === 'string' ? entry.replace(/^\.\//, '') : entry?.path?.replace(/^\.\//, '');
        if (tPath && scopedSet.has(tPath)) {
          if (isLintableStoryPath(tPath)) storyCandidates.add(tPath);
          else if (tPath.endsWith('.json')) {
            const raw = readSafeUtf8(realRoot, tPath);
            if (raw) {
              try {
                const doc = JSON.parse(raw);
                const sPath = inferScenarioStoryPath(doc, tPath, storiesByStem);
                if (sPath) storyCandidates.add(sPath);
              } catch {}
            }
          }
        }
      }
    } else if (Array.isArray(promptPaths) && targetPrompts.length > 0) {
      const promptSet = new Set(targetPrompts);
      for (const scenarioPath of scopedFiles.filter(p => /^(?:tests?|__tests__)\/.*\.json$/i.test(p))) {
        const raw = readSafeUtf8(realRoot, scenarioPath);
        if (!raw) continue;
        try {
          const doc = JSON.parse(raw);
          const sPath = inferScenarioStoryPath(doc, scenarioPath, storiesByStem);
          if (sPath && scenarioPromptRefs(doc).some(ref => promptSet.has(ref))) {
            storyCandidates.add(sPath);
          }
        } catch {}
      }
    }
    targetStories = [...storyCandidates].filter(p => scopedSet.has(p) && isLintableStoryPath(p)).sort();
  }

  for (const storyPath of targetStories) {
    const content = readSafeUtf8(realRoot, storyPath);
    if (typeof content !== 'string') continue;
    const res = lintStory(content, { path: storyPath, criteriaHygiene: true });
    for (const problem of res.problems) {
      rawFindings.push({
        filePath: storyPath,
        line: problem.line,
        order: 10,
        code: problem.code,
        category: 'Story hygiene',
        defaultSeverity: 'warn',
        detail: problem.message,
      });
    }
    if (lintConfig.customRules.length) {
      rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, {
        filePath: storyPath,
        kind: 'story',
        rawText: content,
      }));
    }
  }

  // 3. Tests: fake tests, public-interface-only tests, and custom test rules
  const promptFilterSet = Array.isArray(promptPaths) ? new Set(targetPrompts) : null;
  const targetMatchesPromptFilter = target => {
    if (!promptFilterSet) return true;
    if (!target) return false;
    if (promptFilterSet.has(target)) return true;
    const owners = promptOwnersByCode.get(target);
    return Array.isArray(owners) && owners.some(owner => promptFilterSet.has(owner));
  };

  if (!promptFilterSet || promptFilterSet.size > 0) {
    const nativeOnlyTargets = new Set();
    for (const [codePath, owners] of promptOwnersByCode.entries()) {
      if (owners.some(owner => {
        const ownerText = getPromptText(owner);
        return typeof ownerText === 'string' && isNativeOnlyPrompt(ownerText);
      })) {
        const canonical = canonicalTargetPath(codePath);
        if (canonical) nativeOnlyTargets.add(canonical);
      }
    }

    const testEntries = [];
    const realE2eTargets = new Set();
    for (const testPath of scopedFiles.filter(isInspectableTestCodePath)) {
      const content = readSafeUtf8(realRoot, testPath);
      if (typeof content !== 'string') continue;
      const { boundaryTargets } = inspectTestBoundaryTargets(testPath, content, { nativeOnlyTargets });
      const realKinds = detectRealE2eKindsInTest(testPath, content);
      if (realKinds.some(k => k !== 'real-execution')) {
        for (const target of boundaryTargets) {
          if (!target.startsWith('test-stem:')) realE2eTargets.add(target);
        }
      }
      testEntries.push({ testPath, content, boundaryTargets });
    }

    for (const { testPath, content, boundaryTargets } of testEntries) {
      for (const item of collectFakeTestWarnings(content, { path: testPath })) {
        if (!targetMatchesPromptFilter(item.target)) continue;
        rawFindings.push({ ...item, defaultSeverity: 'warn' });
      }
      for (const item of collectPublicInterfaceTestWarnings(content, { path: testPath })) {
        if (!targetMatchesPromptFilter(item.target)) continue;
        rawFindings.push({ ...item, defaultSeverity: 'warn' });
      }
      const hasRealE2eCoverage = boundaryTargets.length > 0
        && boundaryTargets.every(target => !target.startsWith('test-stem:') && realE2eTargets.has(target));
      if (!promptFilterSet) {
        for (const item of collectTestFixedSleepFindings(content, { path: testPath })) {
          rawFindings.push({ ...item, defaultSeverity: 'warn' });
        }
        for (const item of collectTestUnexcusedSkipFindings(content, { path: testPath })) {
          rawFindings.push({ ...item, defaultSeverity: 'warn' });
        }
        for (const item of collectValidationCodeFindings(content, { path: testPath, kind: 'test', hasRealE2eCoverage, nativeOnlyTargets })) {
          rawFindings.push({ ...item, defaultSeverity: 'warn' });
        }
      }
      if (!promptFilterSet && lintConfig.customRules.length) {
        rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, {
          filePath: testPath,
          kind: 'test',
          rawText: content,
        }));
      }
    }
  }

  // 4. Production code: silent validation skip checks and custom code rules
  const hasCustomCodeRules = lintConfig.customRules.some(r => r.severity !== 'off' && (r.targets.has('code') || r.targets.has('all')));
  const targetCodePaths = promptFilterSet
    ? prodCodePaths.filter(codePath => (promptOwnersByCode.get(codePath) ?? []).some(owner => promptFilterSet.has(owner)))
    : prodCodePaths;
  for (const codePath of targetCodePaths) {
    const content = readSafeUtf8(realRoot, codePath);
    if (typeof content !== 'string') continue;
    for (const item of collectValidationCodeFindings(content, { path: codePath, kind: 'code', hasRealE2eCoverage: true })) {
      rawFindings.push({ ...item, defaultSeverity: 'warn' });
    }
    if (hasCustomCodeRules) {
      rawFindings.push(...evaluateCustomRulesOnFile(lintConfig.customRules, {
        filePath: codePath,
        kind: 'code',
        rawText: content,
      }));
    }
  }

  // 5. Product plan audits: prompt inventory drift and unwired boundary operations
  if (tests === undefined && scopedSet.has('product/plan.md')) {
    const planText = readSafeUtf8(realRoot, 'product/plan.md');
    if (typeof planText === 'string' && planText.trim()) {
      const mapText = scopedSet.has('product/map.md') ? (readSafeUtf8(realRoot, 'product/map.md') ?? '') : '';
      const mentionsExamples = /\bexamples\b/i.test(mapText) || /\bexamples\b/i.test(planText);
      const promptFiles = [];
      for (const p of allPrompts) {
        if (!mentionsExamples && EXAMPLE_DIR.test(p)) continue;
        const content = getPromptText(p);
        if (typeof content === 'string') promptFiles.push({ path: p, content });
      }
      const audit = auditProductPlan({ mapText, planText, promptFiles });
      for (const item of audit.findings) {
        if (promptFilterSet && !(Array.isArray(item.relatedPrompts) && item.relatedPrompts.some(p => promptFilterSet.has(p)))) continue;
        rawFindings.push({ ...item, defaultSeverity: 'warn' });
      }
    }
  }

  rawFindings.sort((a, b) => a.filePath.localeCompare(b.filePath) || a.line - b.line || (a.order ?? 0) - (b.order ?? 0) || a.code.localeCompare(b.code));

  const warnings = [];
  const errors = [];
  const findings = [];
  const seenFormatted = new Set();

  for (const item of rawFindings) {
    if (item.code !== 'lint-config-invalid') {
      if (lintConfig.disabledRules.has(item.code)) continue;
    }
    const severity = item.code === 'lint-config-invalid'
      ? 'error'
      : (lintConfig.ruleSeverities.get(item.code) ?? item.defaultSeverity ?? 'warn');
    if (severity === 'off') continue;

    const prefix = severity === 'error' ? 'Error' : 'Warning';
    const formatted = `${prefix}: ${item.category}: ${item.filePath}:${item.line} [${item.code}] ${item.detail}`;
    if (seenFormatted.has(formatted)) continue;
    seenFormatted.add(formatted);

    findings.push({
      path: item.filePath,
      line: item.line,
      code: item.code,
      category: item.category,
      severity,
      message: item.detail,
      formatted,
    });
    if (severity === 'error') errors.push(formatted);
    else warnings.push(formatted);
  }

  return {
    ok: errors.length === 0,
    configured: lintConfig.configured,
    warnings,
    errors,
    findings,
  };
}

export function lintRepoAntiPatterns({ root, files, promptPaths, tests, config, workspaceRoot, workspacePolicy } = {}) {
  return lintRepoProject({ root, files, promptPaths, tests, config, workspaceRoot, workspacePolicy }).warnings;
}
