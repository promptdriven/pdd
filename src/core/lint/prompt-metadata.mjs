// Frontmatter + Runtime interface metadata stripping, Markdown fence/table/dependency scanner.
import { posix } from 'node:path';
import { canonicalRepoPath } from './diagnostics.mjs';

const NATIVE_ONLY_KIND_LINE_RE = /^[ \t]*kind[ \t]*:[ \t]*(?:['"])?native-only(?:['"])?[ \t]*(?:#[^\r\n]*)?$/i;
const blankPreservingLines = segment => segment.replace(/[^\r\n]/g, ' ');
const isTagNameBoundary = ch => ch === '>' || ch === '/' || ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r';

export function findFrontmatterRange(raw) {
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

export function findRuntimeInterfaceSpans(raw) {
  const text = String(raw ?? '');
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
    while (sumStart < lower.length && ' \t\n\r'.includes(lower[sumStart])) sumStart++;
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
      if (closeMatch && closeMatch[1][0] === activeFence.char && closeMatch[1].length >= activeFence.len) activeFence = null;
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
  if (openHeading) headingSpans.push({ ...openHeading, end: text.length, bodyEnd: text.length });

  const spans = [...detailsSpans, ...headingSpans].sort((a, b) => a.start - b.start || a.end - b.end);
  const merged = [];
  for (const span of spans) {
    if (!merged.length || span.start >= merged.at(-1).end) merged.push(span);
  }
  return merged;
}

export const hasRuntimeInterfaceMetadata = raw => findRuntimeInterfaceSpans(raw).length > 0;

export function hasNativeOnlyFrontmatter(raw) {
  const fm = findFrontmatterRange(raw);
  if (!fm) return false;
  const body = String(raw ?? '').slice(fm.bodyStart, fm.bodyEnd);
  for (const line of body.split(/\r?\n/)) {
    if (NATIVE_ONLY_KIND_LINE_RE.test(line)) return true;
  }
  return false;
}

/**
 * Extract explicit YAML `ports: [...]` or block-list `ports:\n  - store.load` entries from frontmatter.
 */
export function extractFrontmatterPorts(raw) {
  const fm = findFrontmatterRange(raw);
  if (!fm) return [];
  const body = String(raw ?? '').slice(fm.bodyStart, fm.bodyEnd);
  const lines = body.split(/\r?\n/);
  const found = [];
  let inList = false;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const lineNo = i + 2; // line 1 is opening ---
    if (!inList) {
      const m = /^[ \t]*ports[ \t]*:[ \t]*(.*)$/i.exec(line);
      if (!m) continue;
      const rest = m[1].replace(/#[^\r\n]*$/, '').trim();
      if (rest.startsWith('[') && rest.endsWith(']')) {
        for (const item of rest.slice(1, -1).split(',')) {
          const val = item.trim().replace(/^['"`]|['"`]$/g, '').trim();
          if (val) found.push({ port: val, line: lineNo });
        }
      } else if (!rest) {
        inList = true;
      }
      continue;
    }
    const itemMatch = /^[ \t]*-[ \t]+(.+)$/.exec(line);
    if (itemMatch) {
      const val = itemMatch[1].replace(/#[^\r\n]*$/, '').trim().replace(/^['"`]|['"`]$/g, '').trim();
      if (val) found.push({ port: val, line: lineNo });
    } else if (line.trim() && !/^[ \t]*#/.test(line)) {
      inList = false;
    }
  }
  return found;
}

export function scanMarkdownLinesAndFences(cleanedText) {
  const lines = String(cleanedText ?? '').split(/\r?\n/);
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
      activeFence = { openLine: lineNo, char: openMatch[1][0], len: openMatch[1].length, lang, bodyLines: [] };
      continue;
    }

    proseLines.push({ lineNo, text: line });
  }
  if (activeFence) fences.push(activeFence);
  return { fences, proseLines };
}

export function extractRuntimeInterfaceObjects(raw) {
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

export function isNativeOnlyPrompt(raw) {
  if (hasNativeOnlyFrontmatter(raw)) return true;
  return extractRuntimeInterfaceObjects(raw).some(obj => obj.kind === 'native-only');
}

function stripMetadataSpans(raw, preserveLines) {
  const text = String(raw ?? '');
  const ranges = [];
  const fm = findFrontmatterRange(text);
  if (fm) ranges.push({ start: fm.start, end: fm.end });
  for (const span of findRuntimeInterfaceSpans(text)) ranges.push({ start: span.start, end: span.end });
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

export const stripPromptMetadataPreservingLines = raw => stripMetadataSpans(raw, true);
export const stripPromptMetadata = raw => stripMetadataSpans(raw, false);

export function countPromptProseLines(raw) {
  const cleaned = stripPromptMetadata(raw).replace(/\s+$/, '');
  return cleaned ? cleaned.split(/\r?\n/).length : 0;
}

export function countFileLines(raw) {
  const text = String(raw ?? '').replace(/\r?\n$/, '');
  return text ? text.split(/\r?\n/).length : 0;
}

export function splitMarkdownTableRow(line) {
  let trimmed = line.trim();
  if (!trimmed.includes('|')) return null;
  if (trimmed.startsWith('|')) trimmed = trimmed.slice(1);
  if (trimmed.endsWith('|')) trimmed = trimmed.slice(0, -1);
  return trimmed.split('|').map(cell => cell.trim());
}

export function isMarkdownTableSeparator(line) {
  if (!line.includes('|') || !line.includes('--')) return false;
  return /^\|?\s*:?-{2,}:?\s*(?:\|\s*:?-{2,}:?\s*)+\|?$/.test(line.trim());
}

/**
 * Extract relative Markdown link targets inside `## Dependencies` with 1-based line numbers.
 */
export function extractDependencyLinks(raw, promptPath) {
  const cleaned = stripPromptMetadataPreservingLines(raw);
  const { proseLines } = scanMarkdownLinesAndFences(cleaned);
  let inDeps = false;
  const seen = new Set();
  const links = [];
  const baseDir = posix.dirname(promptPath);
  const linkRe = /\[[^\[\]\r\n]*\]\(\s*<?([^()\s<>#\r\n]+)(?:#[^()\s<>#\r\n]*)?>?\s*\)/g;

  for (const { lineNo, text: line } of proseLines) {
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
      if (resolved === promptPath) continue;
      const key = `${resolved}:${lineNo}`;
      if (!seen.has(key)) {
        seen.add(key);
        links.push({ rawTarget, target: resolved, canonical: canonicalRepoPath(resolved), line: lineNo });
      }
    }
  }
  return links;
}

export function extractDependencyLinkTargets(raw, promptPath) {
  const targets = new Set();
  for (const link of extractDependencyLinks(raw, promptPath)) {
    if (link.canonical) targets.add(link.target);
  }
  return [...targets].sort();
}
