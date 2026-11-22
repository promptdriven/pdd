// Generated from prompts/cli/product.prompt.md.
// Pure 0-import markdown table, section, link, and path helpers for product documents and plan audits.
import { posix } from 'node:path';

export const invalid = message => { throw Object.assign(Error(message), { code: 'invalid-product' }); };
export const clean = value => String(value ?? '').trim().replace(/^`([^`]*)`$/, '$1').trim();
export const csv = value => {
  const s = clean(value);
  return !s || s === '-' ? [] : s.split(',').map(clean).filter(Boolean);
};

export const THROUGH = ['prompt-pr', 'code'];
export const SHARED_SURFACE_COLS = new Set(['shared surfaces', 'shared surface', 'updates', 'also updates']);
export const PROMPT_PATH_COLS = new Set(['prompt', 'prompts', 'file', 'path', 'prompt file', 'prompt path']);
export const EXAMPLE_DIR_RE = /(?:^|\/)examples(?:\/|$)/i;
export const SIMPLE_ID_RE = /^[a-z][a-zA-Z0-9_-]*$/;
export const VERSION_RE = /^v?\d+$/i;

export const COLUMNS = {
  Parts: ['Part', 'Folder', 'What it is'],
  Stories: ['Id', 'Part', 'Story', 'Tag'],
  Journeys: ['Id', 'Journey', 'Stories'],
  Questions: ['Id', 'Question', 'Recommendation', 'Example', 'Answer'],
  Runs: ['Run', 'Part', 'Slice', 'Stories', 'Needs'],
  Boundaries: ['From', 'To', 'What crosses', 'Contract'],
};

function countTrailingBackslashes(str) {
  let count = 0;
  for (let i = str.length - 1; i >= 0 && str[i] === '\\'; i--) count++;
  return count;
}

export function tableCells(line) {
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

export const isSeparatorRow = cells => cells.length > 0 && cells.every(cell => /^:?-+:?$/.test(cell));

export function findSectionLines(text, section, { caseInsensitive = false } = {}) {
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

export function rowsWithMeta(text, section, file, { required = true } = {}) {
  const sec = findSectionLines(text, section);
  if (!sec) return { heading: null, rows: [], section: null };
  const table = sec.lines.filter(item => /^\s*\|/.test(item.text)).map(item => ({ lineNo: item.lineNo, cells: tableCells(item.text) }));
  const header = table.shift();
  const heading = header?.cells ?? null;
  if (required && heading) {
    for (const column of COLUMNS[section] ?? []) {
      if (!heading.includes(column)) invalid(`${file}: ${section} is missing column ${column}.`);
    }
  }
  const data = heading
    ? table
      .filter(item => !isSeparatorRow(item.cells))
      .map(item => ({ lineNo: item.lineNo, values: Object.fromEntries(heading.map((key, i) => [key, item.cells[i] ?? ''])) }))
    : [];
  return { heading, rows: data, section: sec };
}

export const rows = (text, section, file) => rowsWithMeta(text, section, file).rows.map(item => item.values);

export function duplicate(items, key, file) {
  const seen = new Set();
  for (const item of items) {
    if (!item[key] || seen.has(item[key])) invalid(`${file}: duplicate or empty ${key} ${item[key]}.`);
    seen.add(item[key]);
  }
}

export function normalizeRepoPath(raw) {
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

export function isIdentChar(ch) {
  if (!ch) return false;
  const c = ch.charCodeAt(0);
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 95 || c === 45;
}

export function stripUrlsLinear(line) {
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

export function scanMarkdownLinksLinear(text, onLink) {
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

export function stripMarkdownLinkTargetsLinear(text) {
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

export function unwrapHeadingToken(raw) {
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

export function buildPartLookups(parts) {
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
    return hintPart;
  };
  return { folderByPart, partsByFolderDesc, inferPart };
}

const isPathWordChar = ch => Boolean(ch) && (isIdentChar(ch) || ch === '.');

export function containsFolderPath(text, folder) {
  if (!folder) return false;
  let from = 0;
  while (from <= text.length - folder.length) {
    const idx = text.indexOf(folder, from);
    if (idx < 0) return false;
    from = idx + 1;
    const after = text[idx + folder.length] ?? '';
    if (isPathWordChar(after)) continue;
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

export function matchPartMentionInHeading(text, partsByFolderDesc, folderByPart) {
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

export function resolvePlanRelativePrompt(raw, fallbackFolder) {
  let candidate = raw.trim();
  while (candidate.startsWith('./')) candidate = candidate.slice(2);
  if (candidate.startsWith('../') && !/[\\\x00-\x1f\x7f]/.test(candidate)) {
    candidate = posix.normalize(posix.join('product', candidate));
  } else if (!candidate.includes('/') && fallbackFolder) {
    candidate = `${fallbackFolder}/${candidate}`;
  }
  const norm = normalizeRepoPath(candidate);
  return norm && norm.endsWith('.prompt.md') ? norm : null;
}
