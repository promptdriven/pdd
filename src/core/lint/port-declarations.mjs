// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Extract declared `<port>.<op>` and `<stem>.<op>` public operations from checkable prompts & contracts (#3619 R1-R8 parity).
import { posix } from 'node:path';
import {
  extractFrontmatterPorts,
  extractRuntimeInterfaceObjects,
  isMarkdownTableSeparator,
  scanMarkdownLinesAndFences,
  splitMarkdownTableRow,
  stripPromptMetadata,
} from './prompt-metadata.mjs';
import { DECLARATIVE_SCHEMA_FENCE_LANGS } from './prompt-rules.mjs';

export const NON_PORT_EXTS = new Set([
  'mjs', 'cjs', 'js', 'jsx', 'ts', 'tsx', 'mts', 'cts', 'py', 'pyi', 'go', 'rs', 'rb', 'java', 'kt', 'cs', 'cc', 'cpp', 'hpp', 'swift', 'php', 'lua', 'sh', 'bash', 'zsh', 'ps1', 'bat',
  'json', 'jsonc', 'jsonl', 'ndjson', 'yaml', 'yml', 'toml', 'ini', 'cfg', 'conf', 'env', 'xml', 'xsd', 'html', 'htm', 'css', 'scss', 'less', 'svg', 'png', 'jpg', 'jpeg', 'gif', 'webp', 'ico',
  'pdf', 'csv', 'tsv', 'txt', 'md', 'mdx', 'rst', 'log', 'sql', 'ddl', 'db', 'sqlite', 'sqlite3', 'wal', 'shm', 'proto', 'graphql', 'gql', 'prisma', 'avsc', 'avro', 'thrift',
  'wasm', 'gz', 'tar', 'zip', 'pem', 'crt', 'cert', 'key', 'pid', 'sock', 'socket', 'service', 'timer', 'example', 'sample', 'tmp', 'bak', 'orig', 'git', 'lockb', 'map',
]);
export const NON_PORT_FILES = new Set(['yarn.lock', 'bun.lock', 'cargo.lock', 'poetry.lock', 'gemfile.lock', 'composer.lock', 'uv.lock', 'flake.lock', 'podfile.lock', 'packages.lock', 'merge-queue.lock']);
export const NON_PORT_TLDS = new Set(['com', 'org', 'net', 'io', 'dev', 'app', 'ai', 'gov', 'edu', 'localhost', 'arpa', 'local']);
export const NON_PORT_PREFIXES = new Set([
  'env', 'process', 'console', 'window', 'document', 'global', 'globalthis', 'module', 'exports', 'import', 'this', 'self', 'super', 'args', 'argv', 'stdin', 'stdout', 'stderr',
  'ports', 'options', 'opts', 'req', 'res', 'request', 'response', 'err', 'error', 'headers', 'params', 'query', 'body', 'payload', 'cookies', 'ctx', 'app', 'router', 'server', 'db', 'pool', 'conn', 'tx', 'cursor', 'session',
  'config', 'excluded', 'sqlite3', 'uvicorn', 'asyncio', 'json', 'sqlalchemy', 'httpx', 'requests', 'fastapi', 'flask', 'express', 'fastify', 'koa', 'django', 'pydantic', 'aiohttp',
  'psycopg', 'psycopg2', 'pg', 'prisma', 'drizzle', 'knex', 'redis', 'ioredis', 'boto3', 'logging', 'logger', 'pathlib', 'subprocess', 'threading', 'multiprocessing',
  'datetime', 'time', 'math', 'random', 'hashlib', 'base64', 'urllib', 'socket', 'ssl', 'node', 'bun', 'deno', 'sys', 'os', 'path', 'posix', 'fs', 'url', 'util',
  'crypto', 'stream', 'events', 'timers', 'zlib', 'net', 'tls', 'dns', 'http', 'https', 'http2', 'child_process', 'worker_threads', 'readline', 'std', 'fmt',
]);
export const NON_PORT_JS_MEMBERS = new Set(['length', 'prototype', 'constructor', 'toString', 'valueOf', 'hasOwnProperty', 'startsWith', 'endsWith', 'forEach', 'flatMap', 'indexOf', 'lastIndexOf', 'toLowerCase', 'toUpperCase', 'charAt', 'substring', 'substr']);

export const VERSION_RE = /^v?\d+$/i;
export const IDENT_RE = /^[a-z][a-zA-Z0-9_-]*$/;
export const TABLE_EXCL_COL_RE = /\b(?:tcp|udp|http|https|listen|network|socket|file|path|table|column|field|type|route|endpoint|url|sql|env|variable|header|status|code|metric|flag|option|description|notes?)\b/i;
export const TABLE_NAME_COL_RE = /\b(?:port|resource|service|adapter|interface|namespace)\b/i;
export const TABLE_OP_COL_RE = /\b(?:operation|operations|op|ops|method|methods|action|actions|export|exports|function|functions|entry|entries|symbol|symbols)\b/i;
export const NET_PORT_HEADING_RE = /\b(?:tcp|udp|http|https|grpc|listen(?:ing)?|network|socket|server|tls|ssl|firewall|docker|container|kubernetes|k8s|ingress|expos(?:e|ed)|stdio|serial|forward(?:ing)?)\b/i;
export const BULLET_RE = /^([ \t]*)(?:[-*+]|\d+[.)])\s+(.+)$/;

const INLINE_BRACE_RE = /(?<![A-Za-z0-9_./:@-])([a-z][a-zA-Z0-9_-]*)\.\{\s*([a-z][a-zA-Z0-9_-]*(?:\s*,\s*[a-z][a-zA-Z0-9_-]*)+)\s*\}/g;
const DEP_PORTS_RE = /\b(?:injected\s+ports?|external\s+ports?|domain\s+ports?|port\s+interface|port\s+contract|ports?|resources?)\b/i;
const DEP_COMBINED_RE = /\b(?:public\s+)?operations?\s+(?:and|&|\/)\s+(?:external\s+|injected\s+|domain\s+)?ports?\b|\b(?:external\s+|injected\s+|domain\s+)?ports?\s+(?:and|&|\/)\s+(?:public\s+)?operations?\b/i;
const DEP_OPS_HEADING_RE = /(?:(?<![A-Za-z0-9_-])(?:operations|commands|subcommands|tools|exports|entrypoints|entry[ \t]+points|public[ \t]+contract|public[ \t]+(?:api|functions?|methods?|actions?|read[ \t]+actions?))(?![A-Za-z0-9_-])|^(?:\d+[.)][ \t]+)?(?:public[ \t]+)?interface$)/i;
const DEP_OPS_EXCLUDE_HEADING_RE = /\b(?:inputs?|outputs?|errors?|allowed|forbidden|external|ports?|resources?|dependencies|consequential|internal|private|failure)\b/i;
const DEP_OP_DETAIL_SUBHEADING_RE = /\b(?:inputs?|outputs?|errors?|parameters?|params?|fields?|returns?|examples?|notes?|schemas?|types?)\b/i;
const DEP_OPS_TABLE_COL_RE = /\b(?:operation|operations|op|ops|command|commands|subcommand|subcommands|tool|tools|export|exports|entrypoint|entrypoints|function|functions|method|methods|action|actions)\b/i;

const GENERIC_PROMPT_DIR_NAMES = new Set([
  'prompts', 'prompt', 'src', 'lib', 'cli', 'docs', 'doc', 'contracts', 'contract',
  'shared', 'common', 'core', 'app', 'apps', 'pkg', 'packages', 'modules', 'module',
  'services', 'service', 'domains', 'domain', 'internal', 'api', 'server', 'web', 'ui',
  'test', 'tests', '__tests__', 'spec', 'specs', 'fixtures', 'examples',
]);
const NON_OP_LABEL_WORDS = new Set([
  'note', 'notes', 'input', 'inputs', 'output', 'outputs', 'result', 'results',
  'error', 'errors', 'example', 'examples', 'rule', 'rules', 'default', 'defaults',
  'field', 'fields', 'param', 'params', 'parameter', 'parameters', 'type', 'types',
  'schema', 'schemas', 'return', 'returns', 'behavior', 'behaviors', 'constraint',
  'constraints', 'invariant', 'invariants', 'overview', 'summary', 'details',
  'status', 'response', 'request', 'precondition', 'postcondition', 'effect', 'effects', 'none',
]);
const HEADING_OP_PREFIX_RE = /^(?:operation|command|subcommand|tool|entrypoint)(?:[ \t]*[:—–][ \t]*|[ \t]+-[ \t]+|[ \t]+)/i;
const HEADING_OP_DELIM_PREFIX_RE = /^(?:operation|command|subcommand|tool|entrypoint)(?:[ \t]*[:—–][ \t]*|[ \t]+-[ \t]+)/i;
const EXPORTED_OP_VERB_RE = /(?<![A-Za-z0-9_./:-])(?:exports?|exporting|exposes?|exposing)(?![A-Za-z0-9_./-])/gi;
const EXPORTED_OP_NEGATION_RE = /\b(?:not|never|without|no|neither|nor|cannot|can't|won't|don't|doesn't|must\s+not|mustn't|should\s+not|shouldn't|may\s+not)\b/i;
const LINE_START_EXPORTED_OP_LABEL_RE = /^[ \t]*(?:(?:[-*+]|\d+[.)])[ \t]+)?(?:public[ \t]+|exported[ \t]+)?(?:operations?|commands?|subcommands?|tools?|exports?|entrypoints?|entry[ \t]+points?)[ \t]*:/i;
const EXPORTED_OP_ARTICLE_WORDS = new Set(['a', 'an', 'the']);
const EXPORTED_OP_MODIFIER_WORDS = new Set(['public', 'exported', 'module', 'async', 'sync', 'peer', 'domain', 'entry']);
const EXPORTED_OP_API_NOUNS = new Set([
  'operation', 'operations', 'function', 'functions', 'method', 'methods',
  'command', 'commands', 'subcommand', 'subcommands', 'tool', 'tools',
  'handler', 'handlers', 'action', 'actions', 'entrypoint', 'entrypoints', 'point', 'points',
]);
const NON_OP_FOLLOWING_NOUNS = new Set([
  'field', 'fields', 'column', 'columns', 'property', 'properties',
  'attribute', 'attributes', 'header', 'headers', 'param', 'params',
  'parameter', 'parameters', 'value', 'values', 'payload', 'payloads',
  'key', 'keys', 'token', 'tokens', 'flag', 'flags', 'secret', 'secrets',
  'metric', 'metrics', 'status', 'error', 'errors', 'record', 'records', 'row', 'rows',
]);
const DATA_EXPORT_FORMAT_RE = /^(?:to|as)[ \t]+(?:a[ \t]+|an[ \t]+|the[ \t]+)?(?:csv|json|xml|yaml|yml|pdf|xlsx|tsv|parquet|html|markdown|file|files)\b/i;
const EXPORT_LEAD_RE = /^(?:takes?|accepts?|returns?|receives?|handles?|runs?|executes?|performs?|computes?|validates?|maps?|reads?|writes?|creates?|updates?|deletes?|is\b|—|–|:|\()/i;
const EMPTY_SET = new Set();

export function isSingleCallSpan(span, openIdx) {
  if (openIdx < 0 || !span.endsWith(')')) return false;
  let depth = 0, quote = null;
  for (let i = openIdx; i < span.length; i++) {
    const ch = span[i];
    if (quote) { if (ch === '\\') i++; else if (ch === quote) quote = null; continue; }
    if (ch === '\'' || ch === '"' || ch === '`') { quote = ch; continue; }
    if (ch === '(') depth++;
    else if (ch === ')' && --depth === 0) return i === span.length - 1;
  }
  return false;
}

export function isValidPortPair(port, op, sqlCols = EMPTY_SET, declaredPrefixes = EMPTY_SET) {
  if (port.length < 2 || op.length < 2 || VERSION_RE.test(port) || VERSION_RE.test(op)) return false;
  const pl = port.toLowerCase(), ol = op.toLowerCase(), full = `${pl}.${ol}`;
  if (NON_PORT_EXTS.has(ol) || NON_PORT_FILES.has(full) || NON_PORT_TLDS.has(ol)) return false;
  if (NON_PORT_PREFIXES.has(pl) && !declaredPrefixes.has(port)) return false;
  return !NON_PORT_JS_MEMBERS.has(op) && !sqlCols.has(full);
}

export function stripUrlsAndLinks(line) {
  let out = String(line ?? '').replace(/\b[a-z][a-z0-9+.-]{0,31}:\/\/\S+/gi, ' ');
  if (out.includes('](')) out = out.replace(/\[([^\[\]\r\n]*)\]\(([^()\r\n]*)\)/g, (_m, label) => ` ${label} `);
  return out;
}

export function scanDottedTokens(text, onPair) {
  if (!text.includes('.')) return;
  if (text.includes('.{')) {
    for (const m of text.matchAll(INLINE_BRACE_RE)) {
      for (const op of m[2].split(',').map(s => s.trim()).filter(Boolean)) onPair(m[1], op);
    }
  }
  for (const m of text.matchAll(/[A-Za-z0-9_./:@-]+/g)) {
    const tok = m[0].replace(/[.:]+$/, '');
    const dot = tok.indexOf('.');
    if (dot <= 0 || dot !== tok.lastIndexOf('.') || tok.includes('/') || tok.includes(':') || tok.includes('@')) continue;
    const port = tok.slice(0, dot), op = tok.slice(dot + 1);
    if (IDENT_RE.test(port) && IDENT_RE.test(op)) onPair(port, op);
  }
}

export function stripSigTail(raw) {
  const s = String(raw ?? '').trim();
  const p = s.indexOf('(');
  if (p > 0) {
    let depth = 0;
    for (let i = p; i < s.length; i++) {
      if (s[i] === '(') depth++;
      else if (s[i] === ')' && --depth === 0) {
        const tail = s.slice(i + 1).trim();
        if (!tail || /^(?:->|=>|:|—|–|returns?\b)/i.test(tail)) return { head: s.slice(0, p).trim(), hasSig: true };
        break;
      }
    }
  }
  const arrow = s.search(/\s*(?:->|=>)\s*/);
  return arrow > 0 ? { head: s.slice(0, arrow).trim(), hasSig: true } : { head: s, hasSig: false };
}

function hasCallParensInToken(text) {
  const s = String(text ?? '').trim().replace(/^\*\*|\*\*$/g, '').replace(/^`|`$/g, '').trim();
  const paren = s.indexOf('(');
  return paren > 0 && isSingleCallSpan(s, paren);
}

export function cleanIdent(raw, allowCall = false) {
  let s = String(raw ?? '').trim().replace(/^\*\*|\*\*$/g, '').replace(/^`|`$/g, '').trim();
  if (allowCall) { const st = stripSigTail(s); if (st.hasSig) s = st.head; }
  return s.length < 2 || VERSION_RE.test(s) || !IDENT_RE.test(s) ? null : s;
}

function extractOpTokensFromTableCell(cell) {
  const ops = [];
  let depth = 0, start = 0;
  const s = String(cell ?? '').trim();
  if (!s) return ops;
  for (let i = 0; i <= s.length; i++) {
    const ch = s[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth = Math.max(0, depth - 1);
    else if (i === s.length || (depth === 0 && (ch === ',' || ch === '/' || ch === ';'))) {
      const part = s.slice(start, i);
      const id = cleanIdent(part, true);
      if (id) ops.push({ ident: id, hasCallParens: hasCallParensInToken(part) });
      start = i + 1;
    }
  }
  return ops;
}

export function splitCellOps(cell) {
  return extractOpTokensFromTableCell(cell).map(item => item.ident);
}

function leadIdent(rest, allowCall = false) {
  const t = String(rest ?? '').trim();
  const w = /^`([^`\r\n]+)`|^\*\*([^*\r\n]+)\*\*/.exec(t);
  if (w) {
    const inner = (w[1] ?? w[2]).trim();
    return (allowCall ? stripSigTail(inner).head : inner).includes('.') ? null : cleanIdent(inner, allowCall);
  }
  const bare = /^([a-z][a-zA-Z0-9_-]*)(?:\s*(\([^()\r\n]*\)))?(?=\s*(?::|—|–|->|=>|-\s|$))/.exec(t);
  return bare && (!bare[2] || allowCall) ? cleanIdent(bare[1], false) : null;
}

function extractLeadingBulletCallOp(rest) {
  const trimmed = String(rest ?? '').trim();
  if (!trimmed) return null;
  const backtick = /^`([^`\r\n]+)`/.exec(trimmed);
  if (backtick) {
    const inner = backtick[1].trim();
    if (inner.includes('.') || !hasCallParensInToken(inner)) return null;
    return cleanIdent(inner, true);
  }
  const bold = /^\*\*([^*\r\n]+)\*\*/.exec(trimmed);
  if (bold) {
    const inner = bold[1].trim();
    if (inner.includes('.') || !hasCallParensInToken(inner)) return null;
    return cleanIdent(inner, true);
  }
  const bare = /^([a-z][a-zA-Z0-9_-]*)\s*(\([^()\r\n]*\))(?=\s*(?::|—|–|->|=>|-\s|$))/.exec(trimmed);
  return bare ? cleanIdent(bare[1], false) : null;
}

function addNormalizedPrefix(set, raw) {
  const s = String(raw ?? '').trim();
  if (!s || s.length < 2) return;
  const variants = [s, s.toLowerCase()];
  if (s.includes('-')) variants.push(s.replace(/-/g, '_'), s.toLowerCase().replace(/-/g, '_'));
  if (s.includes('_')) variants.push(s.replace(/_/g, '-'), s.toLowerCase().replace(/_/g, '-'));
  for (const v of variants) {
    if (v.length >= 2 && !VERSION_RE.test(v) && IDENT_RE.test(v)) set.add(v);
  }
}

function derivePromptPrefixes(depPath) {
  const prefixes = new Set();
  if (typeof depPath !== 'string' || !depPath.trim()) return prefixes;
  const normalized = depPath.trim().replace(/\\/g, '/').replace(/^\.\//, '');
  const base = posix.basename(normalized);
  const stem = base.replace(/\.prompt\.md$/i, '');
  if (stem && stem !== base) addNormalizedPrefix(prefixes, stem);
  const dir = posix.dirname(normalized);
  if (dir && dir !== '.' && dir !== '/') {
    const parentDir = posix.basename(dir);
    if (parentDir && !GENERIC_PROMPT_DIR_NAMES.has(parentDir.toLowerCase())) {
      addNormalizedPrefix(prefixes, parentDir);
    }
  }
  return prefixes;
}

function stripHeadingDescriptionTail(text) {
  let inTicks = false;
  for (let i = 0; i < text.length; i++) {
    const ch = text[i];
    if (ch === '`') { inTicks = !inTicks; continue; }
    if (inTicks) continue;
    if (ch === ':' || ch === '—' || ch === '–') return text.slice(0, i).trim();
    if (ch === '-' && i > 0 && text[i - 1] === ' ' && text[i + 1] === ' ') return text.slice(0, i).trim();
  }
  return text.trim();
}

function extractHeadingOperationNames(title, { requireExplicitSyntax = false } = {}) {
  const raw = String(title ?? '').trim().replace(/^\d+[.)]\s+/, '').trim();
  if (!raw) return [];
  const hasOpKeywordPrefix = HEADING_OP_PREFIX_RE.test(raw);
  const hasOpDelimPrefix = HEADING_OP_DELIM_PREFIX_RE.test(raw);
  const stripped = hasOpKeywordPrefix ? raw.replace(HEADING_OP_PREFIX_RE, '').trim() : raw;
  if (!stripped) return [];
  const head = stripHeadingDescriptionTail(stripped);
  if (!head) return [];
  const hasCallParens = hasCallParensInToken(head);
  const isBacktickedWhole = /^`[^`\r\n]+`$/.test(head) || /^\*\*`[^`\r\n]+`\*\*$/.test(head);
  const isBareCallWhole = /^[a-z][a-zA-Z0-9_-]*\s*\([^()\r\n]*\)$/.test(head);
  if (hasOpKeywordPrefix && !hasOpDelimPrefix && !isBacktickedWhole && !isBareCallWhole) return [];
  if (requireExplicitSyntax) {
    const isCallSyntax = hasCallParens && (isBacktickedWhole || isBareCallWhole);
    const isExplicitKeywordOp = hasOpKeywordPrefix && (isBacktickedWhole || (hasOpDelimPrefix && IDENT_RE.test(head)));
    if (!isCallSyntax && !isExplicitKeywordOp) return [];
  }
  if (!requireExplicitSyntax && head.startsWith('`')) {
    const { ops, rest } = readLeadBacktickOps(head, 0);
    if (ops.length && !hasNonOpSuffix(` ${rest}`, 0, { requireLeadingSpace: true })) return ops;
  }
  if (!requireExplicitSyntax && !hasCallParens && !isBacktickedWhole && /(?:,|\/|\band\b)/i.test(head)) {
    const parts = head.split(/\s*(?:,|\/|\band\b)\s*/i).map(p => p.trim()).filter(Boolean);
    const parsed = parts.map(p => {
      if (stripSigTail(p).head.includes('.')) return null;
      const id = cleanIdent(p, true);
      return id && (hasCallParensInToken(p) || !NON_OP_LABEL_WORDS.has(id.toLowerCase())) ? id : null;
    });
    if (parts.length > 1 && parsed.every(Boolean)) return parsed;
  }
  const ident = cleanIdent(head, true);
  if (!ident) return [];
  if (!hasCallParens && NON_OP_LABEL_WORDS.has(ident.toLowerCase())) return [];
  return [ident];
}

function hasNonOpSuffix(line, afterTickPos, { requireLeadingSpace = true } = {}) {
  const rawTail = line.slice(afterTickPos);
  if (requireLeadingSpace && !/^[ \t]+/.test(rawTail)) return false;
  const tail = rawTail.replace(/^[ \t]+/, '');
  if (DATA_EXPORT_FORMAT_RE.test(tail)) return true;
  const nextWordMatch = /^([A-Za-z][A-Za-z0-9_-]*)/.exec(tail);
  return Boolean(nextWordMatch && NON_OP_FOLLOWING_NOUNS.has(nextWordMatch[1].toLowerCase()));
}

function scanBacktickedOpListFrom(line, startPos, onOp, { allowQualifiers = false } = {}) {
  let pos = startPos;
  if (allowQualifiers) {
    let qualifiers = 0, sawArticle = false, sawApiNoun = false;
    while (pos < line.length && qualifiers < 4) {
      while (pos < line.length && (line[pos] === ' ' || line[pos] === '\t' || line[pos] === ':')) pos++;
      if (line[pos] === '`') break;
      const wordStart = pos;
      while (pos < line.length && /[A-Za-z_-]/.test(line[pos])) pos++;
      const word = line.slice(wordStart, pos).toLowerCase();
      if (EXPORTED_OP_ARTICLE_WORDS.has(word)) sawArticle = true;
      else if (EXPORTED_OP_API_NOUNS.has(word)) sawApiNoun = true;
      else if (!EXPORTED_OP_MODIFIER_WORDS.has(word)) { pos = wordStart; break; }
      qualifiers++;
    }
    if (sawArticle && !sawApiNoun) return pos;
  }
  const collected = [];
  let trailingNonOpSuffix = false, lastItemEndPos = -1, sawInvalidItem = false;
  while (pos < line.length) {
    while (pos < line.length && (line[pos] === ' ' || line[pos] === '\t' || (lastItemEndPos < 0 ? line[pos] === ':' : (line[pos] === ',' || line[pos] === '/')))) pos++;
    if (lastItemEndPos >= 0) {
      const lower7 = line.slice(pos, pos + 7).toLowerCase();
      if (lower7 === 'and/or ' || lower7 === 'and/or\t') { pos += 7; continue; }
      const lower4 = line.slice(pos, pos + 4).toLowerCase();
      if (lower4 === 'and ' || lower4 === 'and\t') { pos += 4; continue; }
      const lower3 = line.slice(pos, pos + 3).toLowerCase();
      if (lower3 === 'or ' || lower3 === 'or\t') { pos += 3; continue; }
    }
    if (line[pos] !== '`') break;
    const endTick = line.indexOf('`', pos + 1);
    if (endTick < 0) break;
    const inner = line.slice(pos + 1, endTick).trim();
    pos = endTick + 1;
    lastItemEndPos = pos;
    const isInvalidToken = !inner || inner.includes('.') || inner.includes('/');
    const hasCallParens = !isInvalidToken && hasCallParensInToken(inner);
    const op = isInvalidToken ? null : cleanIdent(inner, true);
    if (hasNonOpSuffix(line, pos, { requireLeadingSpace: true })) { trailingNonOpSuffix = true; break; }
    if (!op) {
      if (collected.length === 0) break;
      sawInvalidItem = true;
      continue;
    }
    if (!hasCallParens && NON_OP_LABEL_WORDS.has(op.toLowerCase())) continue;
    if (!sawInvalidItem) collected.push({ op, hasCallParens });
  }
  if (!trailingNonOpSuffix && collected.length > 0 && hasNonOpSuffix(line, pos, { requireLeadingSpace: pos === lastItemEndPos })) {
    trailingNonOpSuffix = true;
  }
  if (!trailingNonOpSuffix) for (const item of collected) onOp(item.op);
  return pos;
}

export function computeInlineCodeSpans(line) {
  const runs = [], byLen = new Map();
  for (let i = 0; i < line.length;) {
    if (line[i] !== '`') { i++; continue; }
    const start = i;
    while (i < line.length && line[i] === '`') i++;
    const len = i - start, runIndex = runs.length;
    runs.push({ start, end: i, len });
    let list = byLen.get(len);
    if (!list) { list = []; byLen.set(len, list); }
    list.push(runIndex);
  }
  const spans = [], cursorByLen = new Map();
  for (let i = 0; i < runs.length;) {
    const len = runs[i].len, list = byLen.get(len);
    let c = cursorByLen.get(len) ?? 0;
    while (c < list.length && list[c] <= i) c++;
    cursorByLen.set(len, c);
    if (c < list.length) {
      const j = list[c];
      spans.push([runs[i].start, runs[j].end]);
      cursorByLen.set(len, c + 1);
      i = j + 1;
    } else i++;
  }
  return spans;
}

function extractExportedOpsFromCueLine(line, onOp) {
  if (!line.includes('`')) return;
  const labelMatch = LINE_START_EXPORTED_OP_LABEL_RE.exec(line);
  if (labelMatch) scanBacktickedOpListFrom(line, labelMatch[0].length, onOp, { allowQualifiers: false });
  const codeSpans = computeInlineCodeSpans(line);
  let spanIdx = 0;
  EXPORTED_OP_VERB_RE.lastIndex = 0;
  let m;
  while ((m = EXPORTED_OP_VERB_RE.exec(line)) !== null) {
    const matchStart = m.index, matchEnd = EXPORTED_OP_VERB_RE.lastIndex;
    while (spanIdx < codeSpans.length && codeSpans[spanIdx][1] <= matchStart) spanIdx++;
    if (
      (spanIdx < codeSpans.length && matchStart >= codeSpans[spanIdx][0] && matchStart < codeSpans[spanIdx][1])
      || line[matchStart - 1] === '`'
      || line[matchEnd] === '`'
    ) continue;
    const before = line.slice(Math.max(0, matchStart - 48), matchStart);
    const clauseBefore = before.replace(/^.*[.;?!]/, '');
    if (EXPORTED_OP_NEGATION_RE.test(clauseBefore)) continue;
    const endPos = scanBacktickedOpListFrom(line, matchEnd, onOp, { allowQualifiers: true });
    if (endPos > matchEnd) EXPORTED_OP_VERB_RE.lastIndex = endPos;
  }
}

function classifyDependencyOpsTable(headers) {
  for (let c = 0; c < headers.length; c++) {
    const h = headers[c];
    if (TABLE_EXCL_COL_RE.test(h)) continue;
    if (DEP_OPS_EXCLUDE_HEADING_RE.test(h)) continue;
    if (TABLE_NAME_COL_RE.test(h)) continue;
    if (DEP_OPS_TABLE_COL_RE.test(h)) return c;
  }
  return -1;
}

function readLeadBacktickOps(text, startIdx) {
  const ops = [];
  let sawSig = false, i = startIdx;
  while (i < text.length && (text[i] === ' ' || text[i] === '\t')) i++;
  while (i < text.length && text[i] === '`') {
    const close = text.indexOf('`', i + 1);
    if (close <= i + 1) break;
    const span = text.slice(i + 1, close).trim();
    const { head, hasSig } = stripSigTail(span);
    if (!head.includes('.') && !head.includes('/')) {
      const id = cleanIdent(span, true);
      if (id && (hasSig || !NON_OP_LABEL_WORDS.has(id.toLowerCase()))) { ops.push(id); if (hasSig) sawSig = true; }
    }
    i = close + 1;
    const sep = /^[ \t]*(?:[,/][ \t]*(?:and[ \t]+)?|and[ \t]+)(?=`)/i.exec(text.slice(i, i + 24));
    if (!sep) break;
    i += sep[0].length;
  }
  return { ops, sawSig, rest: text.slice(i).trimStart() };
}

export function extractDeclaredPorts(raw, { isPrompt = true, path = '' } = {}) {
  const mentioned = new Set(), display = new Set(), exportedPeerOps = new Set();
  const promptPrefixes = isPrompt ? derivePromptPrefixes(path) : new Set();

  const addPair = (port, op, strictDisplay = false) => {
    if (port.length < 2 || op.length < 2 || VERSION_RE.test(port) || VERSION_RE.test(op)) return;
    const ol = op.toLowerCase(), fl = `${port.toLowerCase()}.${ol}`;
    if (NON_PORT_EXTS.has(ol) || NON_PORT_FILES.has(fl) || NON_PORT_TLDS.has(ol)) return;
    const full = `${port}.${op}`;
    mentioned.add(full);
    if (!strictDisplay || isValidPortPair(port, op)) display.add(full);
  };
  const addExport = (op, prefixes = promptPrefixes) => {
    const id = cleanIdent(op, true);
    if (!id) return;
    const ol = id.toLowerCase();
    if (NON_PORT_EXTS.has(ol) || NON_PORT_TLDS.has(ol)) return;
    for (const prefix of prefixes) {
      if (prefix.length < 2 || VERSION_RE.test(prefix)) continue;
      if (NON_PORT_FILES.has(`${prefix.toLowerCase()}.${ol}`)) continue;
      const full = `${prefix}.${id}`;
      exportedPeerOps.add(full);
      mentioned.add(full);
      display.add(full);
    }
  };

  if (isPrompt) {
    for (const { port } of extractFrontmatterPorts(raw)) {
      const dot = port.indexOf('.');
      if (dot > 0) addPair(port.slice(0, dot), port.slice(dot + 1));
    }
    const ifaces = extractRuntimeInterfaceObjects(raw);
    for (const iface of ifaces) {
      if (typeof iface.name === 'string' && iface.name.trim()) addNormalizedPrefix(promptPrefixes, iface.name);
    }
    for (const iface of ifaces) {
      for (const res of Array.isArray(iface.resources) ? iface.resources : []) {
        if (typeof res?.name !== 'string' || !res.name.trim()) continue;
        for (const op of Array.isArray(res.operations) ? res.operations : []) {
          if (typeof op?.name === 'string' && op.name.trim()) addPair(res.name.trim(), op.name.trim());
        }
      }
      for (const list of [iface.entries, iface.operations, iface.commands, iface.entry_operations]) {
        for (const item of Array.isArray(list) ? list : []) {
          const rawName = typeof item === 'string'
            ? item
            : (typeof item?.operation === 'string' ? item.operation : (typeof item?.name === 'string' ? item.name : ''));
          const n = rawName.trim();
          if (!n) continue;
          const dot = n.indexOf('.');
          if (dot > 0) addPair(n.slice(0, dot), n.slice(dot + 1));
          else if (promptPrefixes.size > 0) addExport(n, promptPrefixes);
        }
      }
    }
  }

  const { proseLines, fences } = scanMarkdownLinesAndFences(stripPromptMetadata(raw));
  let inDepsSection = false, portsDepth = 0, subPort = null, subDepth = 0, bulletPort = null, bulletIndent = -1;
  let opsSectionDepth = 0, opSubheadingDepth = 0, opDetailDepth = 0, excludedDetailDepth = 0, opsBulletBaseIndent = -1;
  let inTable = false, tPortCol = -1, tOpCol = -1, tSubPort = null, tExpCol = -1;

  for (let idx = 0; idx < proseLines.length; idx++) {
    const line = proseLines[idx].text;
    const hm = /^ {0,3}(#{2,6})\s+(.+)$/.exec(line);
    if (hm) {
      const depth = hm[1].length, title = hm[2].trim();
      const titleHead = stripHeadingDescriptionTail(title);
      inTable = false; tPortCol = -1; tOpCol = -1; tSubPort = null; tExpCol = -1;
      bulletPort = null; bulletIndent = -1; opsBulletBaseIndent = -1;

      if (depth === 2 && /^dependencies\b/i.test(title)) {
        inDepsSection = true;
        portsDepth = 0; opsSectionDepth = 0; opSubheadingDepth = 0; opDetailDepth = 0; excludedDetailDepth = 0;
        subPort = null; subDepth = 0;
        continue;
      }
      if (depth === 2) inDepsSection = false;
      if (inDepsSection) continue;

      if (portsDepth > 0 && depth <= portsDepth) { portsDepth = 0; subPort = null; subDepth = 0; }
      if (excludedDetailDepth > 0 && depth <= excludedDetailDepth) excludedDetailDepth = 0;
      if (opDetailDepth > 0 && depth <= opDetailDepth) opDetailDepth = 0;
      if (opSubheadingDepth > 0 && depth <= opSubheadingDepth) opSubheadingDepth = 0;
      if (opsSectionDepth > 0 && depth <= opsSectionDepth) { opsSectionDepth = 0; opSubheadingDepth = 0; opDetailDepth = 0; }

      if (portsDepth > 0 && depth > portsDepth && portsDepth !== opsSectionDepth) {
        const cleanedTitle = title.replace(/\b(?:ports?|resources?|adapters?|interfaces?)\b/gi, '').trim();
        const ident = cleanIdent(cleanedTitle, false);
        if (ident) { subPort = ident; subDepth = depth; }
        else if (depth <= subDepth) { subPort = null; subDepth = 0; }
        continue;
      }

      let handledAsOp = false;
      if (isPrompt && promptPrefixes.size > 0) {
        if (opsSectionDepth > 0 && depth === opsSectionDepth + 1) {
          const isBarePortHeading = /^(?:ports?|resources?)$/i.test(titleHead) && !titleHead.startsWith('`') && !hasCallParensInToken(titleHead);
          if (!isBarePortHeading) {
            const ops = extractHeadingOperationNames(title, { requireExplicitSyntax: false });
            if (ops.length) {
              for (const op of ops) addExport(op);
              opSubheadingDepth = depth;
              handledAsOp = true;
            }
          }
        } else if (opsSectionDepth === 0 && excludedDetailDepth === 0) {
          const explicitOps = extractHeadingOperationNames(title, { requireExplicitSyntax: true });
          if (explicitOps.length) {
            for (const op of explicitOps) addExport(op);
            handledAsOp = true;
          }
        }
      }

      if (!handledAsOp) {
        const isCombined = !NET_PORT_HEADING_RE.test(title) && DEP_COMBINED_RE.test(title);
        if (isCombined) {
          portsDepth = depth; subPort = null; subDepth = 0;
          if (isPrompt && promptPrefixes.size > 0) { opsSectionDepth = depth; opSubheadingDepth = 0; opDetailDepth = 0; }
        } else if (!NET_PORT_HEADING_RE.test(title) && DEP_PORTS_RE.test(title) && !hasCallParensInToken(titleHead)) {
          portsDepth = depth; subPort = null; subDepth = 0;
        } else if (isPrompt && promptPrefixes.size > 0) {
          if (opsSectionDepth > 0 && depth > opsSectionDepth) {
            if (opDetailDepth === 0 && DEP_OP_DETAIL_SUBHEADING_RE.test(title)) opDetailDepth = depth;
            else if (opSubheadingDepth === 0 || depth === opsSectionDepth + 1) opSubheadingDepth = depth;
          } else if (excludedDetailDepth === 0) {
            if (DEP_OP_DETAIL_SUBHEADING_RE.test(title)) excludedDetailDepth = depth;
            else if (!NET_PORT_HEADING_RE.test(title) && !DEP_OPS_EXCLUDE_HEADING_RE.test(title) && DEP_OPS_HEADING_RE.test(titleHead)) {
              opsSectionDepth = depth; opSubheadingDepth = 0; opDetailDepth = 0;
            }
          }
        }
      }
      continue;
    }

    if (inDepsSection) continue;

    if (line.includes('|') && idx + 1 < proseLines.length && isMarkdownTableSeparator(proseLines[idx + 1].text)) {
      const headers = splitMarkdownTableRow(line) ?? [];
      inTable = true; tPortCol = -1; tOpCol = -1; tSubPort = null; tExpCol = -1;
      for (let c = 0; c < headers.length; c++) {
        const h = headers[c];
        if (TABLE_EXCL_COL_RE.test(h) && !TABLE_NAME_COL_RE.test(h) && !TABLE_OP_COL_RE.test(h)) continue;
        if (tOpCol < 0 && TABLE_OP_COL_RE.test(h) && !TABLE_NAME_COL_RE.test(h)) tOpCol = c;
        else if (tPortCol < 0 && TABLE_NAME_COL_RE.test(h) && !TABLE_OP_COL_RE.test(h) && !TABLE_EXCL_COL_RE.test(h)) tPortCol = c;
      }
      if (tPortCol < 0 && subPort && tOpCol >= 0) tSubPort = subPort;
      if (tPortCol < 0 && !tSubPort && isPrompt && promptPrefixes.size > 0 && portsDepth === 0 && opsSectionDepth > 0 && opSubheadingDepth === 0 && opDetailDepth === 0) {
        tExpCol = classifyDependencyOpsTable(headers);
        if (tExpCol >= 0) tOpCol = -1;
      } else if (tPortCol < 0 && !tSubPort && isPrompt && promptPrefixes.size > 0 && opsSectionDepth > 0 && portsDepth === opsSectionDepth && tOpCol >= 0) {
        tExpCol = tOpCol; tOpCol = -1;
      }
      bulletPort = null; bulletIndent = -1; opsBulletBaseIndent = -1;
      continue;
    }
    if (inTable) {
      if (isMarkdownTableSeparator(line)) continue;
      if (!line.includes('|')) { inTable = false; tPortCol = -1; tOpCol = -1; tSubPort = null; tExpCol = -1; }
      else {
        const cells = splitMarkdownTableRow(line) ?? [];
        if ((tPortCol >= 0 || tSubPort) && tOpCol >= 0 && tOpCol < cells.length) {
          const pn = tPortCol >= 0 ? cleanIdent(cells[tPortCol], false) : tSubPort;
          if (pn) for (const op of splitCellOps(cells[tOpCol])) addPair(pn, op);
        } else if (tExpCol >= 0 && tExpCol < cells.length) {
          for (const { ident, hasCallParens } of extractOpTokensFromTableCell(cells[tExpCol])) {
            if (!hasCallParens && NON_OP_LABEL_WORDS.has(ident.toLowerCase())) continue;
            addExport(ident);
          }
        }
        continue;
      }
    }

    const bm = BULLET_RE.exec(line);
    if (portsDepth > 0 && portsDepth !== opsSectionDepth) {
      if (bm) {
        const indent = bm[1].replace(/\t/g, '  ').length, rest = bm[2].trim();
        if (subPort) { const op = leadIdent(rest, true); if (op) addPair(subPort, op); }
        else if (bulletPort && indent > bulletIndent) { const op = leadIdent(rest, true); if (op) addPair(bulletPort, op); }
        else { const parent = leadIdent(rest, false); bulletPort = parent; bulletIndent = parent ? indent : -1; }
      } else if (line.trim()) { bulletPort = null; bulletIndent = -1; }
      continue;
    }

    if (isPrompt && promptPrefixes.size > 0) {
      if (opsSectionDepth > 0 && opDetailDepth === 0) {
        if (bm) {
          const indent = bm[1].replace(/\t/g, '  ').length, rest = bm[2].trim();
          if (opSubheadingDepth === 0) {
            if (opsBulletBaseIndent < 0 || indent < opsBulletBaseIndent) opsBulletBaseIndent = indent;
            if (indent <= opsBulletBaseIndent) {
              const callOp = extractLeadingBulletCallOp(rest);
              if (callOp) addExport(callOp);
              else {
                const op = leadIdent(rest, true);
                if (op && !NON_OP_LABEL_WORDS.has(op.toLowerCase())) addExport(op);
              }
            }
          } else {
            const callOp = extractLeadingBulletCallOp(rest);
            if (callOp) addExport(callOp);
          }
        } else if (line.trimStart().startsWith('`') && opSubheadingDepth === 0) {
          const { ops, sawSig, rest } = readLeadBacktickOps(line, line.indexOf('`'));
          if (ops.length && (sawSig || EXPORT_LEAD_RE.test(rest))) for (const op of ops) addExport(op);
        } else if (line.trim()) {
          let lineIndent = 0;
          for (let i = 0; i < line.length; i++) {
            if (line[i] === ' ') lineIndent++;
            else if (line[i] === '\t') lineIndent += 2;
            else break;
          }
          if (opsBulletBaseIndent >= 0 && lineIndent <= opsBulletBaseIndent) opsBulletBaseIndent = -1;
        }
      } else {
        opsBulletBaseIndent = -1;
      }
      if (opDetailDepth === 0 && excludedDetailDepth === 0) {
        extractExportedOpsFromCueLine(line, op => addExport(op));
      }
    }
  }

  const scanLines = proseLines.map(x => x.text);
  for (const fence of fences) if (!isPrompt || DECLARATIVE_SCHEMA_FENCE_LANGS.has(fence.lang)) for (const item of fence.bodyLines) scanLines.push(item.text);
  for (const line of scanLines) if (line.includes('.')) scanDottedTokens(stripUrlsAndLinks(line), (p, o) => addPair(p, o, true));
  return { mentioned, display, exportedPeerOps };
}
