// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Native-only port parity check: declared YAML `ports[]`, `## Ports` / `## Port bindings` sections, and Port table columns only.
import { formatTeachingDetail } from './diagnostics.mjs';
import {
  BULLET_RE,
  NET_PORT_HEADING_RE,
  TABLE_EXCL_COL_RE,
  TABLE_NAME_COL_RE,
  TABLE_OP_COL_RE,
  cleanIdent,
  extractDeclaredPorts,
  isValidPortPair,
  scanDottedTokens,
  splitCellOps,
  stripUrlsAndLinks,
} from './port-declarations.mjs';
import {
  extractFrontmatterPorts,
  isMarkdownTableSeparator,
  isNativeOnlyPrompt,
  scanMarkdownLinesAndFences,
  splitMarkdownTableRow,
  stripPromptMetadataPreservingLines,
} from './prompt-metadata.mjs';

const SQL_FENCE_LANGS = new Set(['sql', 'ddl', 'sqlite', 'postgres', 'postgresql', 'mysql']);
const SQL_KEYWORDS = new Set(['primary', 'foreign', 'unique', 'check', 'constraint', 'index', 'key', 'create', 'alter', 'insert', 'select', 'references', 'exclude', 'like']);
const EMPTY_SQL_COLS = new Set();
const BARE_PAIR_RE = /^([a-z][a-zA-Z0-9_-]*)\.([a-z][a-zA-Z0-9_-]*)$/;
const CALL_PAIR_RE = /^([a-z][a-zA-Z0-9_-]*)\.([a-z][a-zA-Z0-9_-]*)\s*\(/;
const BRACE_PAIR_RE = /^([a-z][a-zA-Z0-9_-]*)\.\{\s*([a-z][a-zA-Z0-9_-]*(?:\s*,\s*[a-z][a-zA-Z0-9_-]*)+)\s*\}$/;
const PORT_SECTION_RE = /\b(?:port\s+wiring|port\s+bindings?|bound\s+ports?|wired\s+ports?|injected\s+ports?|external\s+ports?|port\s+adapters?|port\s+map(?:ping)?|port\s+interface|port\s+contract|dependency\s+wiring|ports?)\b/i;
const HOST_PORT_HEADING_RE = /\bhost\s+ports?\b/i;
const TABLE_PORT_COL_RE = /\b(?:port|ports|bound\s+port|wired\s+port|injected\s+port|port\s+op(?:eration)?)\b/i;
const NATIVE_TABLE_ROUTING_COL_RE = /\b(?:prompt|module|handler|target|delegate|dispatch|tool|command|subcommand)\b/i;

function isSingleCall(span, openIdx) {
  if (openIdx < 0) return false;
  let depth = 0, quote = null;
  for (let i = openIdx; i < span.length; i++) {
    const ch = span[i];
    if (quote) { if (ch === '\\') i++; else if (ch === quote) quote = null; continue; }
    if (ch === '\'' || ch === '"' || ch === '`') { quote = ch; continue; }
    if (ch === '(') depth++;
    else if (ch === ')' && --depth === 0) {
      const tail = span.slice(i + 1).trim();
      return !tail || /^(?:->|=>|:|—|–|returns?\b)/i.test(tail);
    }
  }
  return false;
}

function splitBackticks(line) {
  if (!line.includes('`')) return { spans: [], outside: line };
  const spans = [], outside = [];
  let i = 0;
  while (i < line.length) {
    const t = line.indexOf('`', i);
    if (t < 0) { outside.push(line.slice(i)); break; }
    if (t > i) outside.push(line.slice(i, t));
    let n = 0;
    while (t + n < line.length && line[t + n] === '`') n++;
    const close = line.indexOf('`'.repeat(n), t + n);
    if (close < 0) { outside.push(line.slice(t)); break; }
    spans.push(line.slice(t + n, close));
    outside.push(' ');
    i = close + n;
  }
  return { spans, outside: outside.join('') };
}

function extractSqlColumns(fences) {
  const cols = new Set();
  const createRe = /\bCREATE\s+(?:(?:TEMP(?:ORARY)?|UNLOGGED|VIRTUAL)\s+)*(?:TABLE|VIEW)\s+(?:IF\s+NOT\s+EXISTS\s+)?(?:["`\[]?[A-Za-z_]\w*["`\]]?\.)?["`\[]?([A-Za-z_]\w*)["`\]]?(?:\s+USING\s+[A-Za-z_]\w*)?\s*\(/gi;
  const alterRe = /\bALTER\s+TABLE\s+(?:IF\s+EXISTS\s+)?(?:["`\[]?[A-Za-z_]\w*["`\]]?\.)?["`\[]?([A-Za-z_]\w*)["`\]]?\s+ADD\s+(?:COLUMN\s+)?(?:IF\s+NOT\s+EXISTS\s+)?["`\[]?([A-Za-z_]\w*)["`\]]?/gi;
  for (const fence of fences) {
    if (!SQL_FENCE_LANGS.has(fence.lang)) continue;
    const sql = fence.bodyLines.map(x => x.text).join('\n');
    let m;
    while ((m = createRe.exec(sql)) !== null) {
      const table = m[1].toLowerCase();
      let depth = 1, start = createRe.lastIndex;
      for (let i = start; i < sql.length && depth > 0; i++) {
        if (sql[i] === '(') depth++;
        else if (sql[i] === ')') depth--;
        if ((sql[i] === ',' && depth === 1) || depth === 0) {
          const seg = sql.slice(start, i).replace(/--[^\r\n]*/g, ' ').replace(/\/\*[\s\S]*?\*\//g, ' ').trim();
          const cm = /^["`\[]?([A-Za-z_]\w*)["`\]]?(?:\s+|$)/.exec(seg);
          if (cm && !SQL_KEYWORDS.has(cm[1].toLowerCase())) cols.add(`${table}.${cm[1].toLowerCase()}`);
          start = i + 1;
        }
        if (depth === 0) { createRe.lastIndex = i + 1; break; }
      }
      if (depth > 0) { createRe.lastIndex = sql.length; break; }
    }
    while ((m = alterRe.exec(sql)) !== null) {
      const col = m[2].toLowerCase();
      if (!SQL_KEYWORDS.has(col)) cols.add(`${m[1].toLowerCase()}.${col}`);
    }
  }
  return cols;
}

function extractDeclaredWiredRefs(raw, proseLines, sqlCols) {
  const firstLine = new Map();
  const record = (port, op, lineNo, { ignoreSql = false, fromFrontmatter = false } = {}) => {
    if (!isValidPortPair(port, op, ignoreSql ? EMPTY_SQL_COLS : sqlCols)) return;
    const key = `${port}.${op}`;
    if (!firstLine.has(key)) firstLine.set(key, { line: lineNo, fromFrontmatter });
    else if (fromFrontmatter) firstLine.get(key).fromFrontmatter = true;
  };
  const scanChunk = (chunk, lineNo, opts = {}) => {
    const { spans, outside } = splitBackticks(chunk);
    for (const rawSpan of spans) {
      const span = rawSpan.trim().replace(/^(?:(?:async|await)\s+)+/, '');
      let m = BARE_PAIR_RE.exec(span);
      if (m) { record(m[1], m[2], lineNo, opts); continue; }
      m = CALL_PAIR_RE.exec(span);
      if (m && isSingleCall(span, m[0].length - 1)) { record(m[1], m[2], lineNo, opts); continue; }
      m = BRACE_PAIR_RE.exec(span);
      if (m) for (const op of m[2].split(',').map(s => s.trim()).filter(Boolean)) record(m[1], op, lineNo, opts);
    }
    if (outside.includes('.')) scanDottedTokens(stripUrlsAndLinks(outside), (p, o) => record(p, o, lineNo, opts));
  };

  for (const { port, line } of extractFrontmatterPorts(raw)) {
    const m = BARE_PAIR_RE.exec(port);
    if (m) record(m[1], m[2], line, { ignoreSql: true, fromFrontmatter: true });
  }

  let inDeps = false, inPorts = false, portsDepth = 0, inTable = false, portCols = [], splitCols = null;
  for (let idx = 0; idx < proseLines.length; idx++) {
    const { lineNo, text: line } = proseLines[idx];
    const hm = /^ {0,3}(#{2,6})\s+(.+)$/.exec(line);
    if (hm) {
      const depth = hm[1].length, title = hm[2].trim();
      inTable = false; portCols = []; splitCols = null;
      if (depth === 2 && /^dependencies\b/i.test(title)) { inDeps = true; inPorts = false; portsDepth = 0; continue; }
      if (depth === 2) inDeps = false;
      if (inDeps) continue;
      if (!NET_PORT_HEADING_RE.test(title) && !HOST_PORT_HEADING_RE.test(title) && PORT_SECTION_RE.test(title)) { inPorts = true; portsDepth = depth; }
      else if (depth <= portsDepth) { inPorts = false; portsDepth = 0; }
      continue;
    }
    if (inDeps) continue;
    if (line.includes('|') && idx + 1 < proseLines.length && isMarkdownTableSeparator(proseLines[idx + 1].text)) {
      const headers = splitMarkdownTableRow(line) ?? [];
      inTable = true; portCols = []; splitCols = null;
      let pCol = -1, oCol = -1;
      for (let c = 0; c < headers.length; c++) {
        const h = headers[c];
        const isExplicitPortCol = !NET_PORT_HEADING_RE.test(h) && !HOST_PORT_HEADING_RE.test(h) && TABLE_PORT_COL_RE.test(h);
        if (!isExplicitPortCol && TABLE_EXCL_COL_RE.test(h)) continue;
        if (!inPorts && !isExplicitPortCol && NATIVE_TABLE_ROUTING_COL_RE.test(h)) continue;
        if (isExplicitPortCol || (inPorts && /\b(?:operation|operations|binding|bindings)\b/i.test(h))) {
          portCols.push({ col: c, ignoreSql: inPorts || isExplicitPortCol });
        }
        if (oCol < 0 && TABLE_OP_COL_RE.test(h) && !TABLE_NAME_COL_RE.test(h)) oCol = c;
        else if (pCol < 0 && !TABLE_OP_COL_RE.test(h) && (isExplicitPortCol || (inPorts && TABLE_NAME_COL_RE.test(h)))) pCol = c;
      }
      if (pCol >= 0 && oCol >= 0) splitCols = { pCol, oCol, ignoreSql: inPorts };
      continue;
    }
    if (inTable) {
      if (isMarkdownTableSeparator(line)) continue;
      if (!line.includes('|')) { inTable = false; portCols = []; splitCols = null; }
      else {
        const cells = splitMarkdownTableRow(line) ?? [];
        for (const colInfo of portCols) {
          if (colInfo.col < cells.length) scanChunk(cells[colInfo.col], lineNo, { ignoreSql: colInfo.ignoreSql });
        }
        if (splitCols && splitCols.pCol < cells.length && splitCols.oCol < cells.length) {
          const pn = cleanIdent(cells[splitCols.pCol], false);
          if (pn) for (const op of splitCellOps(cells[splitCols.oCol])) record(pn, op, lineNo, { ignoreSql: splitCols.ignoreSql });
        }
        continue;
      }
    }
    if (!inPorts) continue;
    const bm = BULLET_RE.exec(line);
    if (bm) {
      const body = bm[2].trim();
      const lead = /^`([^`\r\n]+)`/.exec(body) ?? /^([a-z][a-zA-Z0-9_-]*\.[a-z][a-zA-Z0-9_-]*)(?:\s*\([^()\r\n]*\))?(?=\s*(?::|—|–|->|=>|-\s|$))/.exec(body);
      const sepMatch = lead ? /(?::|—|–|->|=>| - )/.exec(body.slice(lead[0].length)) : null;
      scanChunk(lead && sepMatch ? body.slice(0, lead[0].length + sepMatch.index) : body, lineNo, { ignoreSql: true });
    } else if (line.trim()) {
      scanChunk(line, lineNo, { ignoreSql: false });
    }
  }
  return [...firstLine.entries()]
    .map(([port, info]) => ({ port, line: info.line, fromFrontmatter: info.fromFrontmatter }))
    .sort((a, b) => a.line - b.line || a.port.localeCompare(b.port));
}

export function collectNativeOnlyPortParityFindings(
  text,
  dependencySources,
  { path = 'prompts/service.prompt.md', dependencyPaths = [], explicitFrontmatterOnly = false } = {},
) {
  if (!isNativeOnlyPrompt(text)) return [];
  const rawDeps = Array.isArray(dependencySources) ? dependencySources : (dependencySources ? [dependencySources] : []);
  const deps = rawDeps
    .map((item, idx) => (typeof item === 'string'
      ? { path: typeof dependencyPaths[idx] === 'string' ? dependencyPaths[idx] : '', text: item, isPrompt: true }
      : item))
    .filter(item => item && typeof item.text === 'string');

  const mentionedInDeps = new Set(), displayPorts = new Set(), exportedPeerOps = new Set();
  for (const dep of deps) {
    const { mentioned, display, exportedPeerOps: peerOps } = extractDeclaredPorts(dep.text, { isPrompt: dep.isPrompt !== false, path: dep.path ?? '' });
    for (const p of mentioned) mentionedInDeps.add(p);
    for (const p of peerOps ?? []) exportedPeerOps.add(p);
    for (const p of display) displayPorts.add(p);
  }

  const { fences, proseLines } = scanMarkdownLinesAndFences(stripPromptMetadataPreservingLines(text));
  const allRefs = extractDeclaredWiredRefs(text, proseLines, extractSqlColumns(fences));
  const refs = explicitFrontmatterOnly ? allRefs.filter(r => r.fromFrontmatter) : allRefs;

  const linkedLabels = (dependencyPaths.length ? dependencyPaths : deps.map(d => d.path).filter(Boolean)).sort();
  const depSummary = linkedLabels.length
    ? linkedLabels.join(', ')
    : (deps.length ? 'linked checkable dependencies' : 'no linked checkable dependencies');

  if (!refs.length) {
    if (explicitFrontmatterOnly || !deps.length) return [];
    const detail = formatTeachingDetail({
      invariant: `Native-only prompt links checkable dependencies (${depSummary}) but declares no ports in frontmatter \`ports:\` or a \`## Ports\` / \`## Port bindings\` section; port parity was not checked`,
      fix: `Declare wired ports in frontmatter \`ports:\` or a \`## Ports\` / \`## Port bindings\` section in ${path}`,
      rerun: 'pdd lint',
    });
    return [{
      filePath: path, line: 1, order: 4, code: 'native-only-no-declared-ports', category: 'native-only port parity',
      defaultSeverity: 'warn', detail, warning: `Warning: native-only port parity: ${path}:1 [native-only-no-declared-ports] ${detail}`,
    }];
  }

  const sortedDisplay = [...displayPorts].sort();
  const declaredHint = sortedDisplay.length ? `; declared ports: ${sortedDisplay.slice(0, 12).join(', ')}${sortedDisplay.length > 12 ? ', …' : ''}` : '';

  const findings = [];
  for (const { port, line } of refs) {
    if (mentionedInDeps.has(port) || exportedPeerOps.has(port)) continue;
    const detail = formatTeachingDetail({
      invariant: `Port "${port}" wired in native-only prompt is not declared by linked checkable dependencies (${depSummary}${declaredHint})`,
      fix: `declare "${port}" in a linked checkable dependency (## Ports or ## Public operations) or fix the port name`,
      rerun: 'pdd lint',
    });
    findings.push({
      filePath: path, line, order: 4, code: 'native-only-unknown-port', category: 'native-only port parity',
      defaultSeverity: 'error', detail, error: `Error: native-only port parity: ${path}:${line} [native-only-unknown-port] ${detail}`,
    });
  }
  return findings;
}

export const lintNativeOnlyPortParity = (text, deps, opts = {}) =>
  collectNativeOnlyPortParityFindings(text, deps, opts).filter(r => r.error).map(r => r.error);
