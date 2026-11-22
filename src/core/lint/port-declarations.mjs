// Extract declared `<port>.<op>` and `<stem>.<op>` public operations from checkable prompts & contracts.
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
  'ports', 'options', 'opts', 'req', 'res', 'request', 'response', 'err', 'error', 'headers', 'params', 'query', 'body', 'cookies', 'ctx', 'app', 'router', 'server', 'db', 'pool', 'conn', 'tx',
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
export const NET_PORT_HEADING_RE = /\b(?:tcp|udp|http|https|grpc|listen(?:ing)?|network|socket|server|tls|ssl|firewall|docker|container|kubernetes|k8s|ingress|expos(?:e|ed))\b/i;
export const BULLET_RE = /^([ \t]*)(?:[-*+]|\d+[.)])\s+(.+)$/;

const INLINE_BRACE_RE = /(?<![A-Za-z0-9_./:@-])([a-z][a-zA-Z0-9_-]*)\.\{\s*([a-z][a-zA-Z0-9_-]*(?:\s*,\s*[a-z][a-zA-Z0-9_-]*)+)\s*\}/g;
const DEP_PORTS_RE = /\b(?:injected\s+ports?|external\s+ports?|domain\s+ports?|port\s+interface|port\s+contract|ports?|resources?)\b/i;
const DEP_COMBINED_RE = /\b(?:public\s+)?operations?\s+(?:and|&|\/)\s+(?:external\s+|injected\s+|domain\s+)?ports?\b|\b(?:external\s+|injected\s+|domain\s+)?ports?\s+(?:and|&|\/)\s+(?:public\s+)?operations?\b/i;
const DEP_EXPORTS_RE = /\b(?:public\s+(?:operations?|contract|interface|exports?|api|functions?|methods?|actions?|read\s+actions?)|operations?|exports?)\b/i;
const DEP_EXPORTS_EXCL_RE = /\b(?:consequential|internal|private|ports?|resources?|failure|errors?)\b/i;
const EXPORT_LEAD_RE = /^(?:takes?|accepts?|returns?|receives?|handles?|runs?|executes?|performs?|computes?|validates?|maps?|reads?|writes?|creates?|updates?|deletes?|is\b|—|–|:|\()/i;
const EMPTY_SET = new Set();

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
    const tok = m[0].replace(/\.+$/, '');
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

export function cleanIdent(raw, allowCall = false) {
  let s = String(raw ?? '').trim().replace(/^\*\*|\*\*$/g, '').replace(/^`|`$/g, '').trim();
  if (allowCall) { const st = stripSigTail(s); if (st.hasSig) s = st.head; }
  return s.length < 2 || VERSION_RE.test(s) || !IDENT_RE.test(s) ? null : s;
}

export function splitCellOps(cell) {
  const ops = [];
  let depth = 0, start = 0;
  const s = String(cell ?? '').trim();
  for (let i = 0; i <= s.length; i++) {
    const ch = s[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth = Math.max(0, depth - 1);
    else if (i === s.length || (depth === 0 && (ch === ',' || ch === '/' || ch === ';'))) {
      const id = cleanIdent(s.slice(start, i), true);
      if (id) ops.push(id);
      start = i + 1;
    }
  }
  return ops;
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

function readBacktickOps(text, startIdx) {
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
      if (id) { ops.push(id); if (hasSig) sawSig = true; }
    }
    i = close + 1;
    const sep = /^[ \t]*(?:[,/][ \t]*(?:and[ \t]+)?|and[ \t]+)(?=`)/i.exec(text.slice(i, i + 24));
    if (!sep) break;
    i += sep[0].length;
  }
  return { ops, sawSig, rest: text.slice(i).trimStart() };
}

function promptStems(promptPath) {
  if (typeof promptPath !== 'string' || !/\.prompt\.md$/i.test(promptPath)) return [];
  const stem = posix.basename(promptPath).replace(/\.prompt\.md$/i, '');
  return [...new Set(stem.includes('-') ? [stem, stem.replace(/-/g, '_')] : [stem])]
    .filter(s => s.length >= 2 && !VERSION_RE.test(s) && IDENT_RE.test(s));
}

export function extractDeclaredPorts(raw, { isPrompt = true, path = '' } = {}) {
  const mentioned = new Set(), display = new Set();
  const stems = isPrompt ? promptStems(path) : [];
  const addPair = (port, op, strictDisplay = false) => {
    if (port.length < 2 || op.length < 2 || VERSION_RE.test(port) || VERSION_RE.test(op)) return;
    const ol = op.toLowerCase(), fl = `${port.toLowerCase()}.${ol}`;
    if (NON_PORT_EXTS.has(ol) || NON_PORT_FILES.has(fl) || NON_PORT_TLDS.has(ol)) return;
    const full = `${port}.${op}`;
    mentioned.add(full);
    if (!strictDisplay || isValidPortPair(port, op)) display.add(full);
  };
  const addExport = op => { const id = cleanIdent(op, true); if (id) for (const stem of stems) addPair(stem, id); };

  if (isPrompt) {
    for (const { port } of extractFrontmatterPorts(raw)) {
      const dot = port.indexOf('.');
      if (dot > 0) addPair(port.slice(0, dot), port.slice(dot + 1));
    }
    for (const iface of extractRuntimeInterfaceObjects(raw)) {
      for (const res of Array.isArray(iface.resources) ? iface.resources : []) {
        if (typeof res?.name !== 'string' || !res.name.trim()) continue;
        for (const op of Array.isArray(res.operations) ? res.operations : []) {
          if (typeof op?.name === 'string' && op.name.trim()) addPair(res.name.trim(), op.name.trim());
        }
      }
      for (const list of [iface.entries, iface.operations]) {
        for (const item of Array.isArray(list) ? list : []) {
          if (typeof item?.name !== 'string' || !item.name.trim()) continue;
          const n = item.name.trim(), dot = n.indexOf('.');
          if (dot > 0) addPair(n.slice(0, dot), n.slice(dot + 1));
          else addExport(n);
        }
      }
    }
  }

  const { proseLines, fences } = scanMarkdownLinesAndFences(stripPromptMetadata(raw));
  let inPorts = false, portsDepth = 0, subPort = null, subDepth = 0, bulletPort = null, bulletIndent = -1;
  let inExports = false, exportsDepth = 0, inExpSub = false, expSubDepth = 0, expBulletIndent = -1;
  let inTable = false, tPortCol = -1, tOpCol = -1, tSubPort = null, tExpCol = -1;

  for (let idx = 0; idx < proseLines.length; idx++) {
    const line = proseLines[idx].text;
    const hm = /^ {0,3}(#{2,6})\s+(.+)$/.exec(line);
    if (hm) {
      const depth = hm[1].length, title = hm[2].trim();
      inTable = false; tPortCol = -1; tOpCol = -1; tSubPort = null; tExpCol = -1;
      bulletPort = null; bulletIndent = -1; expBulletIndent = -1;

      const subIdent = inPorts && depth > portsDepth && (!inExports || /\b(?:port|resource|adapter|interface)\b/i.test(title))
        ? cleanIdent(title.replace(/\b(?:ports?|resources?|adapters?|interfaces?)\b/gi, '').trim(), false) : null;
      const isCombined = !NET_PORT_HEADING_RE.test(title) && DEP_COMBINED_RE.test(title);
      const isPorts = !subIdent && !NET_PORT_HEADING_RE.test(title) && DEP_PORTS_RE.test(title);
      const isExports = !subIdent && stems.length > 0 && (isCombined || (!DEP_EXPORTS_EXCL_RE.test(title) && DEP_EXPORTS_RE.test(title)));

      if (isCombined || (isPorts && !isExports)) {
        if (!inPorts || depth <= portsDepth) portsDepth = depth;
        inPorts = true; subPort = null; subDepth = 0;
        if (isCombined && stems.length) { inExports = true; exportsDepth = depth; inExpSub = false; expSubDepth = 0; }
        else { inExports = false; exportsDepth = 0; inExpSub = false; expSubDepth = 0; }
      } else if (isExports) {
        if (depth <= portsDepth) { inPorts = false; portsDepth = 0; subPort = null; subDepth = 0; }
        else if (depth <= subDepth) { subPort = null; subDepth = 0; }
        inExports = true; exportsDepth = depth; inExpSub = false; expSubDepth = 0;
      } else {
        if (subIdent) { subPort = subIdent; subDepth = depth; }
        else if (inPorts && depth > portsDepth) { if (depth <= subDepth) { subPort = null; subDepth = 0; } }
        else if (depth <= portsDepth) { inPorts = false; portsDepth = 0; subPort = null; subDepth = 0; }

        if (inExports && depth > exportsDepth && !subPort) {
          const s = title.replace(/^\d+[.)]\s+/, '');
          const ops = s.startsWith('`') ? readBacktickOps(s, 0).ops : (() => {
            const parts = s.split(/\s*(?:,|\/|\band\b)\s*/i).map(p => p.trim()).filter(Boolean);
            const parsed = parts.map(p => (!stripSigTail(p).head.includes('.') ? cleanIdent(p, true) : null));
            return parts.length && parsed.every(Boolean) ? parsed : [];
          })();
          if (ops.length) { for (const op of ops) addExport(op); inExpSub = true; expSubDepth = depth; }
          else if (depth <= expSubDepth) { inExpSub = false; expSubDepth = 0; }
        } else if (depth <= exportsDepth) { inExports = false; exportsDepth = 0; inExpSub = false; expSubDepth = 0; }
      }
      continue;
    }

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
      if (tPortCol < 0 && !tSubPort && inExports && stems.length && tOpCol >= 0) { tExpCol = tOpCol; tOpCol = -1; }
      bulletPort = null; bulletIndent = -1; expBulletIndent = -1;
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
        } else if (tExpCol >= 0 && tExpCol < cells.length) for (const op of splitCellOps(cells[tExpCol])) addExport(op);
        continue;
      }
    }

    const bm = BULLET_RE.exec(line);
    if (inPorts) {
      if (bm) {
        const indent = bm[1].replace(/\t/g, '  ').length, rest = bm[2].trim();
        if (subPort) { const op = leadIdent(rest, true); if (op) addPair(subPort, op); }
        else if (bulletPort && indent > bulletIndent) { const op = leadIdent(rest, true); if (op) addPair(bulletPort, op); }
        else if (!inExports) { const parent = leadIdent(rest, false); bulletPort = parent; bulletIndent = parent ? indent : -1; }
      } else if (line.trim()) { bulletPort = null; bulletIndent = -1; }
    }
    if (inExports && !inExpSub && !subPort && stems.length) {
      if (bm) {
        const indent = bm[1].replace(/\t/g, '  ').length;
        if (expBulletIndent < 0 || indent < expBulletIndent) expBulletIndent = indent;
        if (indent === expBulletIndent) { const op = leadIdent(bm[2].trim(), true); if (op) addExport(op); }
      } else if (line.trimStart().startsWith('`')) {
        const { ops, sawSig, rest } = readBacktickOps(line, line.indexOf('`'));
        if (ops.length && (sawSig || EXPORT_LEAD_RE.test(rest))) for (const op of ops) addExport(op);
      }
    }
    if (stems.length && line.includes('`') && /\bExports?\s+/i.test(line)) {
      for (const m of line.matchAll(/(?:^|[.!?]\s+)Exports?\s+/g)) for (const op of readBacktickOps(line, m.index + m[0].length).ops) addExport(op);
    }
  }

  const scanLines = proseLines.map(x => x.text);
  for (const fence of fences) if (!isPrompt || DECLARATIVE_SCHEMA_FENCE_LANGS.has(fence.lang)) for (const item of fence.bodyLines) scanLines.push(item.text);
  for (const line of scanLines) if (line.includes('.')) scanDottedTokens(stripUrlsAndLinks(line), (p, o) => addPair(p, o, true));
  return { mentioned, display };
}
