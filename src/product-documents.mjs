// Generated from prompts/cli/product.prompt.md (sha256: 39c64632cfee9dd0b53ebbe34a676fdb84023e94c6423207497ef136beadd282).
import { posix } from 'node:path';
export const invalid = message => { throw Object.assign(Error(message), { code: 'invalid-product' }); };
const clean = value => String(value ?? '').trim().replace(/^`([^`]*)`$/, '$1').trim();
const csv = value => {
  const s = clean(value);
  return !s || s === '-' ? [] : s.split(',').map(clean).filter(Boolean);
};
const THROUGH = ['prompt-pr', 'code'];
const SHARED_SURFACE_COLS = new Set(['shared surfaces', 'shared surface', 'updates', 'also updates']);
const PROMPT_PATH_COLS = new Set(['prompt', 'prompts', 'file', 'path', 'prompt file', 'prompt path']);
const EXAMPLE_DIR_RE = /(?:^|\/)examples(?:\/|$)/i;
const SIMPLE_ID_RE = /^[a-z][a-zA-Z0-9_-]*$/;
const VERSION_RE = /^v?\d+$/i;
const NON_OP_EXTENSIONS = new Set([
  'md', 'mdx', 'json', 'jsonc', 'jsonl', 'mjs', 'cjs', 'js', 'jsx', 'ts', 'tsx', 'mts', 'cts',
  'py', 'pyi', 'go', 'rs', 'rb', 'java', 'kt', 'cs', 'swift', 'php', 'lua', 'sh', 'bash', 'zsh',
  'sql', 'ddl', 'db', 'sqlite', 'sqlite3', 'yaml', 'yml', 'toml', 'ini', 'cfg', 'conf', 'env',
  'xml', 'xsd', 'html', 'htm', 'css', 'scss', 'svg', 'png', 'jpg', 'jpeg', 'gif', 'webp', 'ico',
  'pdf', 'csv', 'tsv', 'txt', 'rst', 'log', 'lock', 'proto', 'graphql', 'gql', 'prisma',
  'prompt', 'test', 'spec', 'com', 'org', 'net', 'io', 'dev', 'app', 'ai', 'gov', 'edu', 'local', 'localhost', 'example', 'invalid',
]);

function parsePlanThrough(plan) {
  const preamble = plan.split(/^##\s+/m, 1)[0];
  const matches = [...preamble.matchAll(/^Through:[ \t]*(.*)$/gim)];
  if (!matches.length) return undefined;
  if (matches.length > 1) invalid('product/plan.md: duplicate Through declaration.');
  const token = clean(matches[0][1].trim().split(/\s+/)[0] ?? '').toLowerCase();
  if (!THROUGH.includes(token)) invalid(`product/plan.md: invalid Through value ${token || '(empty)'}; use prompt-pr or code.`);
  return token;
}

const columns = {
  Parts: ['Part', 'Folder', 'What it is'], Stories: ['Id', 'Part', 'Story', 'Tag'],
  Journeys: ['Id', 'Journey', 'Stories'], Questions: ['Id', 'Question', 'Recommendation', 'Example', 'Answer'],
  Runs: ['Run', 'Part', 'Slice', 'Stories', 'Needs'], Boundaries: ['From', 'To', 'What crosses', 'Contract'],
};

function countTrailingBackslashes(str) {
  let count = 0;
  for (let i = str.length - 1; i >= 0 && str[i] === '\\'; i--) count++;
  return count;
}

function tableCells(line) {
  const text = line.trim(), cells = [''];
  for (const character of text) {
    const last = cells.length - 1;
    if (character !== '|') cells[last] += character;
    else if (countTrailingBackslashes(cells[last]) % 2) cells[last] = cells[last].slice(0, -1) + '|';
    else cells.push('');
  }
  if (text.startsWith('|')) cells.shift();
  if (cells.at(-1) === '') cells.pop();
  return cells.map(clean);
}

const isSeparatorRow = cells => cells.length > 0 && cells.every(cell => /^:?-+:?$/.test(cell));

function findSectionLines(text, section, { caseInsensitive = false } = {}) {
  const target = caseInsensitive ? section.toLowerCase() : section;
  const rawLines = String(text ?? '').split(/\r?\n/);
  let fence = null;
  let active = null;
  for (let i = 0; i < rawLines.length; i++) {
    const line = rawLines[i];
    const lineNo = i + 1;
    const mark = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(line);
    if (mark) {
      if (!fence) {
        if (!(mark[1][0] === '`' && mark[2].includes('`'))) fence = { char: mark[1][0], len: mark[1].length };
        continue;
      }
      if (/^ {0,3}(`{3,}|~{3,})\s*$/.test(line) && mark[1][0] === fence.char && mark[1].length >= fence.len) {
        fence = null;
      }
      continue;
    }
    if (fence) continue;
    const h2 = /^##[ \t]+(.+)$/.exec(line);
    if (h2) {
      if (active) return active;
      const title = h2[1].trim();
      const matched = caseInsensitive ? title.toLowerCase() === target : title === target;
      if (matched) active = { headingLine: lineNo, lines: [] };
      continue;
    }
    if (active) active.lines.push({ lineNo, text: line });
  }
  return active;
}

const rowsWithMeta = (text, section, file, { required = true } = {}) => {
  const sec = findSectionLines(text, section);
  if (!sec) return { heading: null, rows: [], section: null };
  const table = sec.lines.filter(item => /^\s*\|/.test(item.text)).map(item => ({ lineNo: item.lineNo, cells: tableCells(item.text) }));
  const header = table.shift();
  const heading = header?.cells ?? null;
  if (required && heading) {
    for (const column of columns[section] ?? []) {
      if (!heading.includes(column)) invalid(`${file}: ${section} is missing column ${column}.`);
    }
  }
  const data = heading
    ? table
      .filter(item => !isSeparatorRow(item.cells))
      .map(item => ({ lineNo: item.lineNo, values: Object.fromEntries(heading.map((key, i) => [key, item.cells[i] ?? ''])) }))
    : [];
  return { heading, rows: data, section: sec };
};

const rows = (text, section, file) => rowsWithMeta(text, section, file).rows.map(item => item.values);
const duplicate = (items, key, file) => { const seen = new Set(); for (const item of items) { if (!item[key] || seen.has(item[key])) invalid(`${file}: duplicate or empty ${key} ${item[key]}.`); seen.add(item[key]); } };

function normalizeRepoPath(raw) {
  let s = clean(raw);
  const hash = s.indexOf('#');
  if (hash >= 0) s = s.slice(0, hash);
  s = s.trim();
  while (s.startsWith('./')) s = s.slice(2);
  while (s.endsWith('/')) s = s.slice(0, -1);
  if (!s || s.length > 1000 || s.startsWith('/') || /[\\\x00-\x1f\x7f]/.test(s)) return null;
  if (s.split('/').some(seg => !seg || seg === '.' || seg === '..' || seg.toLowerCase() === '.git')) return null;
  return s;
}

function parseRulesToCheck(mapText) {
  const sec = findSectionLines(mapText, 'Rules to check', { caseInsensitive: true });
  if (!sec) return { hasSection: false, rules: [] };

  const tables = [];
  let current = [];
  for (const item of sec.lines) {
    if (/^\s*\|/.test(item.text)) {
      current.push({ lineNo: item.lineNo, cells: tableCells(item.text) });
    } else if (current.length) {
      tables.push(current);
      current = [];
    }
  }
  if (current.length) tables.push(current);

  if (tables.length > 0) {
    const findCol = (heading, names) => heading.findIndex(col => names.includes(col.toLowerCase()));
    const parseCols = heading => ({
      idIdx: findCol(heading, ['id']),
      ownerIdx: findCol(heading, ['owner']),
      ruleIdx: findCol(heading, ['rule']),
      verifiedIdx: findCol(heading, ['verified by', 'verified_by', 'verified']),
    });
    const rules = [];
    for (const block of tables) {
      let cols = parseCols(block[0].cells);
      if (cols.idIdx < 0) invalid('product/map.md: Rules to check is missing column Id.');
      if (cols.ownerIdx < 0) invalid('product/map.md: Rules to check is missing column Owner.');
      if (cols.ruleIdx < 0) invalid('product/map.md: Rules to check is missing column Rule.');
      if (cols.verifiedIdx < 0) invalid('product/map.md: Rules to check is missing column Verified By.');
      for (let i = 1; i < block.length; i++) {
        const cells = block[i].cells;
        if (isSeparatorRow(cells)) continue;
        if (i + 1 < block.length && isSeparatorRow(block[i + 1].cells)) {
          const nextCols = parseCols(cells);
          if (nextCols.idIdx >= 0 && nextCols.ownerIdx >= 0 && nextCols.ruleIdx >= 0 && nextCols.verifiedIdx >= 0) {
            cols = nextCols;
            continue;
          }
        }
        const id = cells[cols.idIdx] ?? '';
        const owner = cells[cols.ownerIdx] ?? '';
        const rule = cells[cols.ruleIdx] ?? '';
        const rawVerified = cells[cols.verifiedIdx] ?? '';
        const verifiedBy = rawVerified === '-' ? '' : rawVerified;
        rules.push({ id, owner, rule, verifiedBy });
      }
    }
    duplicate(rules, 'id', 'product/map.md');
    for (const entry of rules) {
      if (entry.id === '-') invalid('product/map.md: Rules to check row has invalid Id -.');
      const owners = csv(entry.owner).filter(o => o !== '-');
      if (!entry.owner || entry.owner === '-' || owners.length === 0) invalid(`product/map.md: Rules to check row ${entry.id} is missing Owner.`);
      if (!entry.rule || entry.rule === '-') invalid(`product/map.md: Rules to check row ${entry.id} is missing Rule.`);
    }
    return { hasSection: true, rules };
  }

  // Legacy bullet or prose fallback when no Markdown table exists under ## Rules to check.
  const bulletRules = [];
  const proseRules = [];
  for (const item of sec.lines) {
    const trimmed = item.text.trim();
    if (!trimmed || /^#{3,6}\s+/.test(trimmed)) continue;
    const bullet = /^(?:[-*+]|\d+[.)])\s+(.+)$/.exec(trimmed);
    if (bullet) {
      const text = clean(bullet[1]);
      if (text && text !== '-' && !/^none\.?$/i.test(text)) {
        bulletRules.push({ id: '', owner: 'all', rule: text, verifiedBy: '' });
      }
    } else if (trimmed !== '-' && !/^none\.?$/i.test(trimmed)) {
      proseRules.push({ id: '', owner: 'all', rule: clean(trimmed), verifiedBy: '' });
    }
  }
  return { hasSection: true, rules: bulletRules.length ? bulletRules : proseRules };
}

function stripUrlsLinear(line) {
  const out = String(line ?? '');
  if (!out.includes('://')) return out;
  const parts = [];
  let pos = 0;
  while (pos < out.length) {
    const idx = out.indexOf('://', pos);
    if (idx < 0) { parts.push(out.slice(pos)); break; }
    let schemeStart = idx;
    const minStart = Math.max(pos, idx - 33);
    while (schemeStart > minStart && /[A-Za-z0-9+.-]/.test(out[schemeStart - 1])) schemeStart--;
    const hasPrior = schemeStart > pos && /[A-Za-z0-9+.-]/.test(out[schemeStart - 1]);
    const scheme = out.slice(schemeStart, idx);
    if (!hasPrior && /^[a-z][a-z0-9+.-]{0,31}$/i.test(scheme)) {
      parts.push(out.slice(pos, schemeStart), ' ');
      let urlEnd = idx + 3;
      while (urlEnd < out.length && !/\s/.test(out[urlEnd])) urlEnd++;
      pos = urlEnd;
    } else {
      parts.push(out.slice(pos, idx + 3));
      pos = idx + 3;
    }
  }
  return parts.join('');
}

function scanMarkdownLinksLinear(text, onLink) {
  let pos = 0;
  while (pos < text.length) {
    const mid = text.indexOf('](', pos);
    if (mid < 0) break;
    let open = mid - 1;
    while (open >= pos && text[open] !== '[' && text[open] !== ']' && text[open] !== '\n' && text[open] !== '\r') open--;
    if (open < pos || text[open] !== '[') { pos = mid + 2; continue; }
    let close = mid + 2;
    while (close < text.length && text[close] !== ')' && text[close] !== '(' && text[close] !== '\n' && text[close] !== '\r') close++;
    if (close >= text.length || text[close] !== ')') { pos = mid + 2; continue; }
    onLink(open, close + 1, text.slice(open + 1, mid), text.slice(mid + 2, close));
    pos = close + 1;
  }
}

function stripMarkdownLinkTargetsLinear(text) {
  if (!text.includes('](')) return text;
  const out = [];
  let cursor = 0;
  scanMarkdownLinksLinear(text, (start, end, label) => {
    out.push(text.slice(cursor, start), ' ', label, ' ');
    cursor = end;
  });
  if (!cursor) return text;
  out.push(text.slice(cursor));
  return out.join('');
}

function extractPromptRefsFromLine(line, fallbackFolder) {
  const source = String(line ?? '');
  const rawRefs = [];
  const nonLinkChunks = [];
  let cursor = 0;

  // 1. Markdown links: [label](target) via linear indexOf('](') scan; strip entire link span before Pass-2 so link labels are never re-parsed as separate prompts.
  scanMarkdownLinksLinear(source, (start, end, _label, rawTarget) => {
    nonLinkChunks.push(source.slice(cursor, start), ' ');
    cursor = end;
    let target = rawTarget.trim();
    if (target.startsWith('<') && target.endsWith('>')) target = target.slice(1, -1).trim();
    const space = target.search(/\s/);
    if (space >= 0) target = target.slice(0, space);
    if (target.includes('://') || /^mailto:/i.test(target)) return;
    const hash = target.indexOf('#');
    if (hash >= 0) target = target.slice(0, hash);
    if (target.endsWith('.prompt.md')) rawRefs.push(target);
  });
  nonLinkChunks.push(source.slice(cursor));

  // 2. Linear token scan across backticks and prose outside Markdown links
  const text = stripUrlsLinear(nonLinkChunks.join(''));
  let tokenStart = -1;
  const isDelim = ch => ch === ' ' || ch === '\t' || ch === ',' || ch === ';' || ch === '(' || ch === ')'
    || ch === '[' || ch === ']' || ch === '{' || ch === '}' || ch === '"' || ch === '\''
    || ch === '`' || ch === '<' || ch === '>' || ch === '|';
  const flushToken = end => {
    if (tokenStart < 0) return;
    let tok = text.slice(tokenStart, end);
    tokenStart = -1;
    while (tok.length && (tok.endsWith('.') || tok.endsWith(':') || tok.endsWith('*'))) {
      if (tok.endsWith('.prompt.md')) break;
      tok = tok.slice(0, -1);
    }
    while (tok.length && tok.startsWith('*')) tok = tok.slice(1);
    const hash = tok.indexOf('#');
    if (hash >= 0) tok = tok.slice(0, hash);
    if (tok.endsWith('.prompt.md')) rawRefs.push(tok);
  };
  for (let i = 0; i < text.length; i++) {
    if (isDelim(text[i])) flushToken(i);
    else if (tokenStart < 0) tokenStart = i;
  }
  flushToken(text.length);

  const normalized = [];
  for (const ref of rawRefs) {
    let candidate = ref.trim();
    while (candidate.startsWith('./')) candidate = candidate.slice(2);
    if (candidate.startsWith('../') && !/[\\\x00-\x1f\x7f]/.test(candidate)) {
      candidate = posix.normalize(posix.join('product', candidate));
    } else if (!candidate.includes('/') && fallbackFolder) {
      candidate = `${fallbackFolder}/${candidate}`;
    }
    const norm = normalizeRepoPath(candidate);
    if (norm && norm.endsWith('.prompt.md')) normalized.push(norm);
  }
  return normalized;
}

function buildPartLookups(parts) {
  const folderByPart = new Map();
  const partsByFolderDesc = [];
  for (const p of parts) {
    if (!p?.part) continue;
    const folder = normalizeRepoPath(p.folder ?? '');
    if (folder) {
      folderByPart.set(p.part, folder);
      partsByFolderDesc.push({ part: p.part, folder });
    }
  }
  partsByFolderDesc.sort((a, b) => b.folder.length - a.folder.length || a.part.localeCompare(b.part));
  const inferPart = (path, hintPart = '') => {
    for (const item of partsByFolderDesc) {
      if (path === item.folder || path.startsWith(`${item.folder}/`)) return item.part;
    }
    if (hintPart && folderByPart.has(hintPart)) return hintPart;
    return hintPart;
  };
  return { folderByPart, partsByFolderDesc, inferPart };
}

function isPathWordChar(ch) {
  return Boolean(ch) && (isIdentChar(ch) || ch === '.');
}

function containsFolderPath(text, folder) {
  if (!folder) return false;
  let from = 0;
  while (from <= text.length - folder.length) {
    const idx = text.indexOf(folder, from);
    if (idx < 0) return false;
    from = idx + 1;
    const after = text[idx + folder.length] ?? '';
    if (isPathWordChar(after)) continue;
    // Do not treat child file paths (e.g. `prompts/app/core.prompt.md`) as standalone folder labels (`prompts/app` or `prompts/app/`).
    if (after === '/' && isPathWordChar(text[idx + folder.length + 1] ?? '')) continue;
    const before = idx > 0 ? text[idx - 1] : '';
    if (isPathWordChar(before)) continue;
    if (before === '/') {
      const prefix = text.slice(0, idx);
      const isDotSlash = prefix.endsWith('./') && (idx === 2 || (!isPathWordChar(text[idx - 3]) && text[idx - 3] !== '/'));
      const isDotDotSlash = prefix.endsWith('../') && (idx === 3 || (!isPathWordChar(text[idx - 4]) && text[idx - 4] !== '/'));
      if (!isDotSlash && !isDotDotSlash) continue;
    }
    return true;
  }
  return false;
}

function unwrapHeadingToken(raw) {
  let s = String(raw ?? '').trim();
  for (let i = 0; i < 3; i++) {
    const prev = s;
    s = s.replace(/^\*\*([^*]+)\*\*$/, '$1').trim();
    s = s.replace(/^`([^`]*)`$/, '$1').trim();
    while (s.endsWith(':') || s.endsWith('—') || s.endsWith('–') || s.endsWith(',')) s = s.slice(0, -1).trim();
    if (s === prev) break;
  }
  return s;
}

function matchPartMentionInHeading(text, partsByFolderDesc, folderByPart) {
  const cleaned = clean(text);
  const rawFirst = cleaned.split(/\s+/)[0] ?? '';
  const unwrapped = unwrapHeadingToken(rawFirst);
  const firstWord = unwrapHeadingToken(unwrapped.split(/[:(—–,]/)[0] ?? '');
  if (firstWord && folderByPart.has(firstWord)) {
    return { part: firstWord, folder: folderByPart.get(firstWord) };
  }
  for (const item of partsByFolderDesc) {
    if (containsFolderPath(cleaned, item.folder)) return item;
  }
  return null;
}

function parsePlanPrompts(planText, parts = []) {
  const sec = findSectionLines(planText, 'Prompts', { caseInsensitive: true });
  if (!sec) return { hasSection: false, prompts: [] };
  const { folderByPart, partsByFolderDesc, inferPart } = buildPartLookups(parts);
  const seen = new Map();
  let currentPart = '';
  let currentFolder = '';
  let tableHeader = null;
  let partCol = -1;
  let promptCols = [];

  const record = (path, hintPart, line) => {
    if (seen.has(path)) return;
    seen.set(path, { path, part: inferPart(path, hintPart), line });
  };

  for (const item of sec.lines) {
    const trimmed = item.text.trim();
    if (!trimmed) { tableHeader = null; partCol = -1; promptCols = []; continue; }
    const sub = /^#{3,6}[ \t]+(.+)$/.exec(trimmed);
    if (sub) {
      tableHeader = null; partCol = -1; promptCols = [];
      const matched = matchPartMentionInHeading(sub[1], partsByFolderDesc, folderByPart);
      if (matched) { currentPart = matched.part; currentFolder = matched.folder; }
      else { currentPart = ''; currentFolder = ''; }
      continue;
    }
    if (/^\s*\|/.test(item.text)) {
      const cells = tableCells(item.text);
      if (!tableHeader) {
        tableHeader = cells;
        partCol = cells.findIndex(c => ['part', 'owner'].includes(c.toLowerCase()));
        promptCols = cells
          .map((c, idx) => (PROMPT_PATH_COLS.has(c.toLowerCase()) ? idx : -1))
          .filter(idx => idx >= 0);
        continue;
      }
      if (isSeparatorRow(cells)) continue;
      const rowPart = partCol >= 0 ? clean(cells[partCol] ?? '') : '';
      const rowFolder = (rowPart && folderByPart.get(rowPart)) || currentFolder;
      const cellsToScan = promptCols.length > 0
        ? promptCols.map(idx => cells[idx] ?? '')
        : cells;
      for (const cell of cellsToScan) {
        for (const path of extractPromptRefsFromLine(cell, rowFolder)) {
          record(path, rowPart || currentPart, item.lineNo);
        }
      }
      continue;
    }
    tableHeader = null; partCol = -1; promptCols = [];
    let linePart = currentPart;
    let lineFolder = currentFolder;
    const leadText = trimmed.replace(/^(?:[-*+]|\d+[.)])\s+/, '').replace(/^\*\*([^*\r\n]+)\*\*/, '$1');
    const promptExtIdx = leadText.indexOf('.prompt.md');
    let leadPrefix = leadText;
    if (promptExtIdx >= 0) {
      let cut = promptExtIdx;
      while (cut > 0 && !/\s/.test(leadText[cut - 1])) cut--;
      leadPrefix = leadText.slice(0, cut).trim();
    }
    const leadMatch = leadPrefix ? matchPartMentionInHeading(leadPrefix, partsByFolderDesc, folderByPart) : null;
    if (leadMatch) { linePart = leadMatch.part; lineFolder = leadMatch.folder; }
    for (const path of extractPromptRefsFromLine(trimmed, lineFolder)) {
      record(path, linePart, item.lineNo);
    }
  }
  return { hasSection: true, prompts: [...seen.values()] };
}

function extractBoundaryOpsFromText(text, { requirePartPrefix = false, from = '', to = '', line = 1, knownParts = new Set() } = {}) {
  const withoutUrls = stripMarkdownLinkTargetsLinear(stripUrlsLinear(text));
  const ops = [];
  const isDelim = ch => ch === ' ' || ch === '\t' || ch === ',' || ch === ';' || ch === '(' || ch === ')'
    || ch === '[' || ch === ']' || ch === '{' || ch === '}' || ch === '"' || ch === '\''
    || ch === '`' || ch === '<' || ch === '>' || ch === '|';
  let start = -1;

  const inspect = rawTok => {
    let tok = rawTok;
    while (tok.length && (tok.endsWith('.') || tok.endsWith(':') || tok.endsWith('*'))) tok = tok.slice(0, -1);
    while (tok.length && (tok.startsWith('*') || tok.startsWith('.'))) tok = tok.slice(1);
    if (!tok.includes('.')) return;
    const segs = tok.split('/');
    if (segs.length === 3 && segs[0] === 'prompts') segs.shift();
    if (segs.length !== 1 && segs.length !== 2) return;
    if (requirePartPrefix && segs.length !== 2) return;
    const explicitPart = segs.length === 2 ? segs[0] : '';
    const pair = segs[segs.length - 1];
    if (explicitPart && (!SIMPLE_ID_RE.test(explicitPart) || VERSION_RE.test(explicitPart))) return;
    const dot = pair.indexOf('.');
    if (dot <= 0 || dot !== pair.lastIndexOf('.')) return;
    const target = pair.slice(0, dot);
    const op = pair.slice(dot + 1);
    if (target.length < 2 || op.length < 2) return;
    if (!SIMPLE_ID_RE.test(target) || !SIMPLE_ID_RE.test(op)) return;
    if (VERSION_RE.test(target) || VERSION_RE.test(op)) return;
    if (NON_OP_EXTENSIONS.has(op.toLowerCase())) return;
    const toParts = csv(to);
    const inferredTo = toParts.length === 1 && (!knownParts.size || knownParts.has(toParts[0])) && !['*', 'all'].includes(toParts[0].toLowerCase())
      ? toParts[0]
      : '';
    const part = explicitPart || inferredTo;
    const raw = explicitPart ? `${explicitPart}/${target}.${op}` : `${target}.${op}`;
    ops.push({ raw, explicitPart, part, target, op, shortName: `${target}.${op}`, from, to, line });
  };

  for (let i = 0; i < withoutUrls.length; i++) {
    if (isDelim(withoutUrls[i])) {
      if (start >= 0) { inspect(withoutUrls.slice(start, i)); start = -1; }
    } else if (start < 0) {
      start = i;
    }
  }
  if (start >= 0) inspect(withoutUrls.slice(start));
  return ops;
}

function parsePlanBoundaryOperations(planText, parts = []) {
  const sec = findSectionLines(planText, 'Boundaries', { caseInsensitive: true });
  if (!sec) return { hasSection: false, operations: [] };
  const knownParts = new Set(parts.map(p => p.part).filter(Boolean));
  const seen = new Map();
  const addOp = item => {
    const key = `${item.part}\0${item.shortName}`;
    const existing = seen.get(key);
    if (!existing) { seen.set(key, item); return; }
    if ((!existing.explicitPart && item.explicitPart) || (!existing.from && item.from)) {
      seen.set(key, {
        ...existing,
        ...item,
        explicitPart: existing.explicitPart || item.explicitPart,
        from: existing.from || item.from,
        to: existing.to || item.to,
      });
    }
  };

  let heading = null;
  let inNeverCrosses = false;
  let neverCrossesSawBody = false;
  for (const item of sec.lines) {
    const trimmed = item.text.trim();
    if (!trimmed) {
      heading = null;
      if (inNeverCrosses && neverCrossesSawBody) {
        inNeverCrosses = false;
        neverCrossesSawBody = false;
      }
      continue;
    }
    if (/^\s*\|/.test(item.text)) {
      inNeverCrosses = false;
      neverCrossesSawBody = false;
      const cells = tableCells(item.text);
      if (!heading) { heading = cells; continue; }
      if (isSeparatorRow(cells)) continue;
      const fromIdx = heading.findIndex(c => c.toLowerCase() === 'from');
      const toIdx = heading.findIndex(c => c.toLowerCase() === 'to');
      const crossesIdx = heading.findIndex(c => c.toLowerCase() === 'what crosses');
      const opsIdx = heading.findIndex(c => ['operations', 'operation', 'ops'].includes(c.toLowerCase()));
      const from = fromIdx >= 0 ? (cells[fromIdx] ?? '') : '';
      const to = toIdx >= 0 ? (cells[toIdx] ?? '') : '';
      for (const idx of [crossesIdx, opsIdx]) {
        if (idx < 0 || !cells[idx]) continue;
        for (const op of extractBoundaryOpsFromText(cells[idx], { requirePartPrefix: false, from, to, line: item.lineNo, knownParts })) {
          addOp(op);
        }
      }
      continue;
    }
    heading = null;
    const isSubheading = /^#{3,6}[ \t]+/.test(trimmed);
    const neverMatch = /^(?:#{3,6}[ \t]+|(?:[-*+]|\d+[.)])[ \t]+)?(?:\*\*)?never[ \t]+crosses\b/i.exec(trimmed);
    if (neverMatch) {
      const rest = trimmed
        .slice(neverMatch[0].length)
        .replace(/^\*\*/, '')
        .trim()
        .replace(/^:/, '')
        .trim()
        .replace(/^\*\*/, '')
        .trim();
      inNeverCrosses = true;
      neverCrossesSawBody = rest.length > 0;
      continue;
    }
    if (isSubheading) {
      inNeverCrosses = false;
      neverCrossesSawBody = false;
    }
    if (inNeverCrosses) {
      neverCrossesSawBody = true;
      continue;
    }
    for (const op of extractBoundaryOpsFromText(trimmed, { requirePartPrefix: true, line: item.lineNo, knownParts })) {
      addOp(op);
    }
  }
  return { hasSection: true, operations: [...seen.values()] };
}

function parseSharedSurfaceRunLines(runSection, runs) {
  if (!runSection) return new Map();
  const byRun = new Map(runs.map(r => [r.run, r]));
  const perRun = new Map();
  let currentRun = null;

  const addFor = (runName, list) => {
    if (!byRun.has(runName)) invalid(`product/plan.md: unknown run ${runName}.`);
    if (!perRun.has(runName)) perRun.set(runName, []);
    perRun.get(runName).push(...list);
  };

  const stripLeadingBold = s => String(s ?? '').replace(/^\*\*[ \t]*/, '');

  for (const item of runSection.lines) {
    const trimmed = item.text.trim();
    if (!trimmed || /^\s*\|/.test(item.text)) continue;
    const sub = /^#{3,6}[ \t]+(.+)$/.exec(trimmed);
    if (sub) {
      const rawFirst = sub[1].trim().split(/\s+/)[0] ?? '';
      const unwrapped = unwrapHeadingToken(rawFirst);
      const candidate = unwrapHeadingToken(unwrapped.split(/[:(—–,]/)[0] ?? '');
      currentRun = byRun.has(candidate) ? candidate : null;
      continue;
    }
    const line = trimmed.replace(/^(?:[-*+]|\d+[.)])[ \t]+/, '');
    const paren = /^(?:\*\*)?(?:Shared[ \t]+surfaces?|Also[ \t]+updates)[ \t]*\(([^()\r\n]+)\)(?:\*\*)?[ \t]*:[ \t]*(.*)$/i.exec(line);
    if (paren) {
      addFor(unwrapHeadingToken(paren[1]), csv(stripLeadingBold(paren[2])));
      continue;
    }
    const prefixed = /^([*`]{0,3}[A-Za-z0-9._-]+[*`]{0,3})[ \t]*:[ \t]*(?:\*\*)?(?:Shared[ \t]+surfaces?|Also[ \t]+updates)(?:\*\*)?[ \t]*:[ \t]*(.*)$/i.exec(line);
    if (prefixed) {
      addFor(unwrapHeadingToken(prefixed[1]), csv(stripLeadingBold(prefixed[2])));
      continue;
    }
    const plain = /^(?:\*\*)?(?:Shared[ \t]+surfaces?|Also[ \t]+updates)(?:\*\*)?[ \t]*:[ \t]*(.*)$/i.exec(line);
    if (plain && currentRun) {
      addFor(currentRun, csv(stripLeadingBold(plain[1])));
    }
  }
  return perRun;
}

export function parseProductDocuments({mapText, planText = ''}) {
  const map = String(mapText), plan = String(planText);
  const name = /^#\s+(.+?)(?::\s*map)?\s*$/m.exec(map)?.[1], size = /^Size:\s*(small|medium|large)\b/im.exec(map)?.[1].toLowerCase();
  if (!name || !size) invalid('product/map.md: name or Size is missing.');
  const through = parsePlanThrough(plan);
  const mapRows = section => rows(map, section, 'product/map.md'), planRows = section => rows(plan, section, 'product/plan.md');
  const parts = mapRows('Parts').map(row => ({ part: row.Part, folder: row.Folder, description: row['What it is'] }));
  const stories = mapRows('Stories').map(row => ({ id: row.Id, part: row.Part, story: row.Story, tag: row.Tag }));
  const journeys = mapRows('Journeys').map(row => ({ id: row.Id, journey: row.Journey, stories: csv(row.Stories) }));
  const rulesInfo = parseRulesToCheck(map);
  duplicate(parts, 'part', 'product/map.md'); duplicate(stories, 'id', 'product/map.md'); duplicate(journeys, 'id', 'product/map.md');
  for (const story of stories) if (!parts.some(part => part.part === story.part)) invalid(`product/map.md: unknown part ${story.part}.`);
  for (const journey of journeys) for (const id of journey.stories) if (!stories.some(story => story.id === id)) invalid(`product/map.md: unknown Story ${id}.`);

  const runsMeta = rowsWithMeta(plan, 'Runs', 'product/plan.md');
  const sharedCol = (runsMeta.heading ?? []).find(col => SHARED_SURFACE_COLS.has(col.toLowerCase()));
  let runs = runsMeta.rows.map(({ values: row }) => {
    const partTokens = csv(row.Part);
    const primaryPart = partTokens[0] ?? '';
    const inlineSecondary = partTokens.slice(1);
    const colSecondary = sharedCol ? csv(row[sharedCol]) : [];
    return {
      run: row.Run,
      part: primaryPart,
      slice: row.Slice,
      stories: csv(row.Stories),
      needs: csv(row.Needs),
      _rawShared: [...inlineSecondary, ...colSecondary],
    };
  });
  if (!plan.trim() && size === 'small' && parts.length === 1) {
    runs = [{ run: parts[0].part, part: parts[0].part, slice: '1', stories: stories.filter(story => story.tag === 'CORE').map(story => story.id), needs: [], _rawShared: [] }];
  }
  if (!runs.length) invalid('product/plan.md: no planned runs.');
  duplicate(runs, 'run', 'product/plan.md');

  const perRunShared = parseSharedSurfaceRunLines(runsMeta.section, runs);

  runs = runs.map(entry => {
    const combined = [
      ...entry._rawShared,
      ...(perRunShared.get(entry.run) ?? []),
    ];
    const sharedSurfaces = [];
    for (const surface of combined) {
      if (surface === entry.part) continue;
      if (surface === 'all' || !parts.some(part => part.part === surface)) invalid(`product/plan.md: unknown shared surface ${surface}.`);
      if (!sharedSurfaces.includes(surface)) sharedSurfaces.push(surface);
    }
    return {
      run: entry.run,
      part: entry.part,
      slice: entry.slice,
      stories: entry.stories,
      needs: entry.needs,
      ...(sharedSurfaces.length ? { sharedSurfaces } : {}),
    };
  });

  for (const run of runs) {
    if (run.part !== 'all' && !parts.some(part => part.part === run.part)) invalid(`product/plan.md: unknown part ${run.part}.`);
    const allowedParts = new Set([run.part, ...(run.sharedSurfaces ?? [])]);
    for (const id of run.stories) {
      const ok = run.part === 'all'
        ? journeys.some(j => j.id === id) || stories.some(s => s.id === id && (run.sharedSurfaces ?? []).includes(s.part))
        : stories.some(s => s.id === id && allowedParts.has(s.part));
      if (!ok) invalid(`product/plan.md: unknown Story ${id}.`);
    }
    for (const need of run.needs) if (need !== 'plan PR' && !runs.some(other => other.run === need)) invalid(`product/plan.md: unknown need ${need}.`);
  }

  const promptsInfo = parsePlanPrompts(plan, parts);
  const boundariesInfo = parsePlanBoundaryOperations(plan, parts);
  const boundaries = planRows('Boundaries');
  const product = {
    name,
    size,
    ...(through ? { through } : {}),
    parts,
    stories,
    journeys,
    runs,
    questions: mapRows('Questions').filter(row => !row.Answer || row.Answer === '-').map(row => row.Id),
    ...(rulesInfo.rules.length ? { rulesToCheck: rulesInfo.rules } : {}),
    ...(promptsInfo.prompts.length ? { prompts: promptsInfo.prompts.map(({ path, part }) => ({ path, part })) } : {}),
  };
  return {
    product,
    boundaries,
    prompts: promptsInfo.prompts,
    boundaryOperations: boundariesInfo.operations,
  };
}

export function parseProductWorldWriters({worldText}) {
  // Fences and unrelated tables cannot acquire world-write authority.
  const tables = []; let fence = null, table = [];
  const flush = () => { if (table.length) tables.push(table); table = []; };
  for (const line of String(worldText).split(/\r?\n/)) {
    const mark = /^ {0,3}(`{3,}|~{3,})/.exec(line);
    if (mark) { flush(); if (!fence) fence = mark[1]; else if (mark[1][0] === fence[0] && mark[1].length >= fence.length) fence = null; continue; }
    if (fence) continue;
    if (/^\s*\|/.test(line)) table.push(tableCells(line)); else flush();
  }
  flush();
  const matches = tables.filter(rows => rows[0].includes('Key') && rows[0].includes('Writer'));
  if (matches.length > 1) invalid('contracts/world.md: ambiguous writer tables.');
  if (!matches.length) return [];
  const [heading, ...data] = matches[0], writers = new Map(), result = [];
  for (const row of data.filter(row => !row.every(cell => /^:?-+:?$/.test(cell)))) {
    const key = row[heading.indexOf('Key')], writer = row[heading.indexOf('Writer')];
    if (!key || !writer) invalid('contracts/world.md: declaration has an empty Key or Writer.');
    if (writers.has(key) && writers.get(key) !== writer) throw Object.assign(Error(`${key} has two writers.`), {code:'world-writer-conflict'});
    writers.set(key,writer); result.push({key,writer});
  }
  return result;
}

function parseLenientMapParts(mapText) {
  if (!mapText || typeof mapText !== 'string') return [];
  const meta = rowsWithMeta(mapText, 'Parts', 'product/map.md', { required: false });
  if (!meta.heading || !meta.heading.includes('Part') || !meta.heading.includes('Folder')) return [];
  return meta.rows
    .map(item => ({ part: item.values.Part, folder: item.values.Folder }))
    .filter(item => item.part && item.folder);
}

function stripFrontmatterAndComments(raw) {
  let text = String(raw ?? '');
  if (text.startsWith('---\n') || text.startsWith('---\r\n')) {
    const bodyStart = text.startsWith('---\r\n') ? 5 : 4;
    let pos = bodyStart;
    while (pos <= text.length) {
      const nl = text.indexOf('\n', pos);
      const end = nl < 0 ? text.length : nl;
      const line = text.slice(pos, end).replace(/\r$/, '');
      if (line === '---') { text = text.slice(nl < 0 ? text.length : nl + 1); break; }
      if (nl < 0) break;
      pos = nl + 1;
    }
  }
  // Linear strip of HTML comments without regex backtracking.
  const out = [];
  let cursor = 0;
  while (cursor < text.length) {
    const open = text.indexOf('<!--', cursor);
    if (open < 0) { out.push(text.slice(cursor)); break; }
    out.push(text.slice(cursor, open), ' ');
    const close = text.indexOf('-->', open + 4);
    if (close < 0) break;
    cursor = close + 3;
  }
  return out.join('');
}

function asciiLower(str) {
  return str.replace(/[A-Z]+/g, s => s.toLowerCase());
}

function extractRuntimeInterfacesLinear(raw) {
  const text = String(raw ?? '');
  const lower = asciiLower(text);
  const out = [];
  let pos = 0;
  while (pos < lower.length) {
    const det = lower.indexOf('<details', pos);
    if (det < 0) break;
    const detClose = lower.indexOf('</details>', det + 8);
    if (detClose < 0) break;
    const innerLower = lower.slice(det + 8, detClose);
    const relSum = innerLower.indexOf('<summary');
    const relSumClose = relSum >= 0 ? innerLower.indexOf('</summary>', relSum + 8) : -1;
    if (relSum >= 0 && relSumClose > relSum) {
      const sum = det + 8 + relSum;
      const sumClose = det + 8 + relSumClose;
      if (/runtime\s+interface/i.test(text.slice(sum, sumClose))) {
        const inner = text.slice(sumClose + 10, detClose);
        const fenceStart = inner.indexOf('```');
        if (fenceStart >= 0) {
          const nl = inner.indexOf('\n', fenceStart + 3);
          const fenceEnd = nl >= 0 ? inner.indexOf('```', nl + 1) : -1;
          if (nl >= 0 && fenceEnd > nl) {
            try {
              const parsed = JSON.parse(inner.slice(nl + 1, fenceEnd));
              if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) out.push(parsed);
            } catch {}
          }
        }
      }
    }
    pos = detClose + 10;
  }
  return out;
}

function isIdentChar(ch) {
  if (!ch) return false;
  const c = ch.charCodeAt(0);
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 95 || c === 45;
}

function precedingSegmentBeforeSlash(text, slashIdx) {
  let start = slashIdx - 1;
  while (start >= 0 && isIdentChar(text[start])) start--;
  return text.slice(start + 1, slashIdx);
}

function containsBoundaryOpToken(text, needle, requiredPartPrefix = '') {
  if (!needle) return false;
  let from = 0;
  while (from <= text.length - needle.length) {
    const idx = text.indexOf(needle, from);
    if (idx < 0) return false;
    from = idx + 1;
    const after = text[idx + needle.length] ?? '';
    const afterNext = text[idx + needle.length + 1] ?? '';
    if (isIdentChar(after) || (after === '.' && isIdentChar(afterNext))) continue;
    const before = idx > 0 ? text[idx - 1] : '';
    if (isIdentChar(before) || before === '.') continue;
    if (before === '/') {
      const seg = precedingSegmentBeforeSlash(text, idx - 1);
      if (needle.includes('/')) {
        if (seg && seg !== 'prompts') continue;
      } else if (requiredPartPrefix) {
        if (seg !== requiredPartPrefix) continue;
      }
    }
    return true;
  }
  return false;
}

function containsBraceBoundaryOp(text, target, op, requiredPartPrefix = '') {
  const prefix = `${target}.{`;
  let from = 0;
  while (from < text.length) {
    const idx = text.indexOf(prefix, from);
    if (idx < 0) return false;
    const bodyStart = idx + prefix.length;
    const before = idx > 0 ? text[idx - 1] : '';
    if (isIdentChar(before) || before === '.'
      || (before === '/' && requiredPartPrefix && precedingSegmentBeforeSlash(text, idx - 1) !== requiredPartPrefix)) {
      from = bodyStart;
      continue;
    }
    let stop = bodyStart;
    while (stop < text.length) {
      const ch = text[stop];
      if (ch === '}' || ch === '{' || ch === '\n') break;
      stop++;
    }
    if (stop >= text.length) return false;
    if (text[stop] !== '}') {
      from = text[stop] === '\n' ? stop + 1 : Math.max(bodyStart, stop - prefix.length + 1);
      continue;
    }
    const members = text.slice(bodyStart, stop).split(',').map(s => s.trim());
    if (members.includes(op)) return true;
    from = stop + 1;
  }
  return false;
}

function promptStemNormalized(path) {
  const slash = path.lastIndexOf('/');
  const base = slash >= 0 ? path.slice(slash + 1) : path;
  return base.replace(/\.prompt\.md$/i, '').toLowerCase().replace(/_/g, '-');
}

function runtimeInterfaceWiresOp(ifaces, boundaryOp) {
  const normTarget = boundaryOp.target.toLowerCase().replace(/_/g, '-');
  for (const iface of ifaces) {
    if (Array.isArray(iface.calls)) {
      for (const call of iface.calls) {
        if (call?.target_operation !== boundaryOp.op || typeof call?.target !== 'string') continue;
        if (promptStemNormalized(call.target) !== normTarget) continue;
        if (boundaryOp.explicitPart && !call.target.split('/').includes(boundaryOp.explicitPart)) continue;
        return true;
      }
    }
    if (Array.isArray(iface.resources)) {
      for (const res of iface.resources) {
        if (typeof res?.name !== 'string' || !Array.isArray(res.operations)) continue;
        const rName = res.name.toLowerCase().replace(/_/g, '-');
        const namesMatch = rName === normTarget
          || (boundaryOp.part && (rName === `${boundaryOp.part.toLowerCase()}-${normTarget}` || rName === `${boundaryOp.part.toLowerCase()}/${normTarget}`));
        if (namesMatch && res.operations.some(item => item?.name === boundaryOp.op)) return true;
      }
    }
  }
  return false;
}

export function auditProductPlan({ mapText = '', planText = '', promptFiles = [] } = {}) {
  const plan = String(planText ?? '');
  if (!plan.trim()) return { drift: [], unwiredBoundaries: [], findings: [], warnings: [] };
  const parts = parseLenientMapParts(mapText);
  const { folderByPart, inferPart } = buildPartLookups(parts);
  const knownParts = new Set(parts.map(p => p.part).filter(Boolean));
  const promptsInfo = parsePlanPrompts(plan, parts);
  const boundariesInfo = parsePlanBoundaryOperations(plan, parts);

  const allowExamples = [...folderByPart.values()].some(folder => EXAMPLE_DIR_RE.test(folder))
    || promptsInfo.prompts.some(item => EXAMPLE_DIR_RE.test(item.path));

  const normalizedPrompts = [];
  const seenPromptPaths = new Set();
  for (const item of Array.isArray(promptFiles) ? promptFiles : []) {
    const path = normalizeRepoPath(item?.path ?? '');
    if (!path || !path.endsWith('.prompt.md') || typeof item?.content !== 'string' || seenPromptPaths.has(path)) continue;
    if (!allowExamples && EXAMPLE_DIR_RE.test(path)) continue;
    seenPromptPaths.add(path);
    normalizedPrompts.push({ path, content: item.content });
  }
  normalizedPrompts.sort((a, b) => a.path.localeCompare(b.path));

  const drift = [];
  if (promptsInfo.hasSection && promptsInfo.prompts.length > 0) {
    const declaredSet = new Set(promptsInfo.prompts.map(item => item.path));
    const actualSet = new Set(normalizedPrompts.map(item => item.path));
    const folderSet = new Set();
    for (const folder of folderByPart.values()) folderSet.add(folder);
    for (const item of promptsInfo.prompts) {
      const slash = item.path.lastIndexOf('/');
      if (slash > 0) folderSet.add(item.path.slice(0, slash));
    }
    const trackedFolders = [...folderSet].sort((a, b) => b.length - a.length || a.localeCompare(b));

    for (const item of promptsInfo.prompts) {
      if (actualSet.has(item.path)) continue;
      drift.push({
        filePath: 'product/plan.md',
        line: item.line,
        order: 20,
        code: 'product-prompt-inventory-drift',
        category: 'product plan',
        relatedPrompts: [item.path],
        detail: `Declared prompt \`${item.path}\` in product/plan.md ## Prompts is missing on disk.`,
        statusWarning: `Warning: Prompt inventory drift: ${item.path} is declared in product/plan.md ## Prompts but missing on disk.`,
      });
    }

    for (const item of normalizedPrompts) {
      if (declaredSet.has(item.path)) continue;
      const folder = trackedFolders.find(dir => item.path.startsWith(`${dir}/`));
      if (!folder) continue;
      drift.push({
        filePath: item.path,
        line: 1,
        order: 21,
        code: 'product-prompt-inventory-drift',
        category: 'product plan',
        relatedPrompts: [item.path],
        detail: `Prompt file exists on disk under tracked folder \`${folder}\` but is not listed in product/plan.md ## Prompts.`,
        statusWarning: `Warning: Prompt inventory drift: ${item.path} exists under ${folder} but is not declared in product/plan.md ## Prompts.`,
      });
    }
  }

  const unwiredBoundaries = [];
  if (boundariesInfo.hasSection && boundariesInfo.operations.length > 0) {
    const indexedPrompts = normalizedPrompts.map(item => ({
      path: item.path,
      normStem: promptStemNormalized(item.path),
      cleaned: stripFrontmatterAndComments(item.content),
      ifaces: extractRuntimeInterfacesLinear(item.content),
    }));

    for (const b of boundariesInfo.operations) {
      const ownerPart = b.explicitPart || b.part;
      const ownerFolder = ownerPart ? (folderByPart.get(ownerPart) ?? `prompts/${ownerPart}`) : '';
      const normTarget = b.target.toLowerCase().replace(/_/g, '-');
      const isInOwnerPart = p => {
        if (!ownerPart) return false;
        const pPart = inferPart(p.path);
        if (pPart) return pPart === ownerPart;
        return p.path.startsWith(`${ownerFolder}/`) || p.path.split('/').includes(ownerPart);
      };
      const definingPaths = new Set();
      let matchedByStem = false;

      for (const p of indexedPrompts) {
        if (p.normStem === normTarget && (!ownerPart || isInOwnerPart(p))) {
          definingPaths.add(p.path);
          matchedByStem = true;
        }
        const declaresShort = p.ifaces.some(iface => Array.isArray(iface.entries)
          && iface.entries.some(e => e?.operation === b.shortName));
        if (declaresShort) {
          definingPaths.add(p.path);
        }
        const declaresBare = p.ifaces.some(iface => Array.isArray(iface.entries)
          && iface.entries.some(e => e?.operation === b.op));
        if (declaresBare && p.normStem === normTarget && (!ownerPart || isInOwnerPart(p))) {
          definingPaths.add(p.path);
          matchedByStem = true;
        }
      }
      if (!matchedByStem && ownerPart) {
        for (const p of indexedPrompts) {
          if (!isInOwnerPart(p)) continue;
          const declaresBare = p.ifaces.some(iface => Array.isArray(iface.entries)
            && iface.entries.some(e => e?.operation === b.op));
          if (declaresBare) definingPaths.add(p.path);
        }
      }
      if (!definingPaths.size && !b.explicitPart) {
        for (const p of indexedPrompts) if (p.normStem === normTarget) definingPaths.add(p.path);
      }

      const fromParts = csv(b.from);
      const isCrossPartBoundary = Boolean(
        ownerPart
        && knownParts.has(ownerPart)
        && fromParts.length > 0
        && fromParts.some(fp => knownParts.has(fp))
        && !fromParts.includes(ownerPart)
      );

      const wired = indexedPrompts.some(p => {
        if (definingPaths.has(p.path)) return false;
        if (isCrossPartBoundary && isInOwnerPart(p)) return false;
        if (b.raw.includes('/') && containsBoundaryOpToken(p.cleaned, b.raw, '')) return true;
        if (containsBoundaryOpToken(p.cleaned, b.shortName, ownerPart)) return true;
        if (containsBraceBoundaryOp(p.cleaned, b.target, b.op, ownerPart)) return true;
        return runtimeInterfaceWiresOp(p.ifaces, b);
      });

      if (!wired) {
        unwiredBoundaries.push({
          filePath: 'product/plan.md',
          line: b.line,
          order: 25,
          code: 'product-boundary-unwired',
          category: 'product plan',
          relatedPrompts: [...definingPaths],
          detail: `Declared boundary operation \`${b.raw}\` in product/plan.md ## Boundaries is not referenced by any consumer prompt.`,
          statusWarning: `Warning: Unwired boundary operation: ${b.raw} declared in product/plan.md ## Boundaries is not referenced by any consumer prompt.`,
        });
      }
    }
  }

  const findings = [...drift, ...unwiredBoundaries];
  return {
    drift,
    unwiredBoundaries,
    findings,
    warnings: findings.map(f => f.statusWarning),
  };
}
