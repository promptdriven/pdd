// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Frontmatter + Runtime interface metadata stripping, Markdown fence/table/CommonMark relative-link scanner.
import { posix } from 'node:path';
import { canonicalRepoPath } from './diagnostics.mjs';

const NATIVE_ONLY_KIND_LINE_RE = /^[ \t]*kind[ \t]*:[ \t]*(?:['"])?native-only(?:['"])?[ \t]*(?:#[^\r\n]*)?$/i;
const blankPreservingLines = segment => segment.replace(/[^\r\n]/g, ' ');
const isTagNameBoundary = ch => ch === '>' || ch === '/' || ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r';
const normalizeRefLabel = text => String(text ?? '').trim().replace(/\s+/g, ' ').toLowerCase();

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

export function extractFrontmatterPorts(raw) {
  const fm = findFrontmatterRange(raw);
  if (!fm) return [];
  const body = String(raw ?? '').slice(fm.bodyStart, fm.bodyEnd);
  const lines = body.split(/\r?\n/);
  const found = [];
  const pushVal = (rawVal, lineNo) => {
    const cleaned = String(rawVal ?? '').replace(/#[^\r\n]*$/, '').trim().replace(/^['"`]|['"`]$/g, '').trim();
    if (!cleaned) return;
    const bare = cleaned.replace(/^(?:(?:op|port|name)\s*:\s*)+/i, '').replace(/^['"`]|['"`]$/g, '').replace(/\s*\([^()\r\n]*\).*$/, '').trim();
    if (bare) found.push({ port: bare, line: lineNo });
  };
  let inList = false;
  let inFlowList = false;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const lineNo = i + 2;
    if (inFlowList) {
      const stripped = line.replace(/#[^\r\n]*$/, '').trim();
      const closeIdx = stripped.indexOf(']');
      const chunk = closeIdx >= 0 ? stripped.slice(0, closeIdx) : stripped;
      for (const item of chunk.split(',')) pushVal(item, lineNo);
      if (closeIdx >= 0) inFlowList = false;
      continue;
    }
    if (!inList) {
      const m = /^[ \t]*ports[ \t]*:[ \t]*(.*)$/i.exec(line);
      if (!m) continue;
      const rest = m[1].replace(/#[^\r\n]*$/, '').trim();
      if (rest.startsWith('[')) {
        const closeIdx = rest.indexOf(']');
        const chunk = closeIdx >= 0 ? rest.slice(1, closeIdx) : rest.slice(1);
        for (const item of chunk.split(',')) pushVal(item, lineNo);
        if (closeIdx < 0) inFlowList = true;
      } else if (!rest) {
        inList = true;
      }
      continue;
    }
    const itemMatch = /^[ \t]*-[ \t]+(.+)$/.exec(line);
    if (itemMatch) {
      pushVal(itemMatch[1], lineNo);
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
        activeFence.closed = true;
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
      activeFence = { openLine: lineNo, char: openMatch[1][0], len: openMatch[1].length, lang, closed: false, bodyLines: [] };
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

export function stripFrontmatterPreservingLines(raw) {
  const text = String(raw ?? '');
  const fm = findFrontmatterRange(text);
  if (!fm) return text;
  return blankPreservingLines(text.slice(0, fm.end)) + text.slice(fm.end);
}

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
  if (trimmed.endsWith('|') && !trimmed.endsWith('\\|')) trimmed = trimmed.slice(0, -1);
  return trimmed.split(/(?<!\\)\|/).map(cell => cell.trim());
}

export function isMarkdownTableSeparator(line) {
  if (!line.includes('|') || !line.includes('--')) return false;
  return /^\|?\s*:?-{2,}:?\s*(?:\|\s*:?-{2,}:?\s*)+\|?$/.test(line.trim());
}

/**
 * Mask inline code spans across lines within each Markdown paragraph (CommonMark §6.1),
 * preserving exact 1-based line numbers so backtick-quoted links never trigger false positives.
 */
export function stripInlineCodeSpansPreservingLines(proseLines) {
  const out = [];
  let activeTicks = 0;
  let prevLineNo = -1;
  for (const { lineNo, text } of proseLines) {
    if (lineNo !== prevLineNo + 1 || !text.trim() || /^ {0,3}#{1,6}[ \t]+/.test(text)) {
      activeTicks = 0;
    }
    prevLineNo = lineNo;
    if (activeTicks === 0 && !text.includes('`')) {
      out.push({ lineNo, text });
      continue;
    }
    if (activeTicks > 0 && !text.includes('`')) {
      out.push({ lineNo, text: ' '.repeat(text.length) });
      continue;
    }
    const parts = [];
    let i = 0;
    while (i < text.length) {
      const next = text.indexOf('`', i);
      if (next < 0) {
        parts.push(activeTicks > 0 ? ' '.repeat(text.length - i) : text.slice(i));
        break;
      }
      if (next > i) {
        parts.push(activeTicks > 0 ? ' '.repeat(next - i) : text.slice(i, next));
      }
      let j = next + 1;
      while (j < text.length && text[j] === '`') j++;
      const run = j - next;
      if (activeTicks === 0) activeTicks = run;
      else if (run === activeTicks) activeTicks = 0;
      parts.push(' '.repeat(run));
      i = j;
    }
    out.push({ lineNo, text: parts.join('') });
  }
  return out;
}

const REF_LINK_DEF_RE = /^ {0,3}\[([^\]]+)\]:\s*<?([^()\s<>#\r\n]+)(?:#[^()\s<>#\r\n]*)?>?(?:\s+(?:"[^"\n]*"|'[^'\n]*'|\([^)\n]*\)))?\s*$/;

/**
 * Extract relative CommonMark links across a prompt (both inline and reference-style, outside
 * code fences, HTML comments, and inline code spans), marking whether each appears under `## Dependencies`.
 */
export function extractRelativeMarkdownLinks(raw, promptPath) {
  const cleaned = stripPromptMetadataPreservingLines(raw);
  const { proseLines } = scanMarkdownLinesAndFences(cleaned);
  const maskedLines = stripInlineCodeSpansPreservingLines(proseLines);

  const refMap = new Map();
  for (const { text } of maskedLines) {
    const rm = REF_LINK_DEF_RE.exec(text);
    if (rm) refMap.set(normalizeRefLabel(rm[1]), rm[2].trim());
  }

  let inDeps = false;
  let inCallerNav = false;
  const seen = new Set();
  const links = [];
  const baseDir = posix.dirname(promptPath);
  const inlineRe = /!?\[[^\[\]\r\n]*\]\(\s*<?([^()\s<>#\r\n]+)(?:#[^()\s<>#\r\n]*)?>?(?:\s+(?:"[^"\r\n]*"|'[^'\r\n]*'))?\s*\)/g;
  const refUseRe = /!?\[([^[\]\r\n]*)\]\[([^[\]\r\n]*)\]/g;

  const pushTarget = (rawTarget, lineNo) => {
    const trimmed = String(rawTarget ?? '').trim().split('?')[0].split('#')[0];
    if (!trimmed || /^(?:[a-z][a-z0-9+.-]*:|\/\/|#|\/)/i.test(trimmed)) return;
    let decoded = trimmed;
    try { decoded = decodeURIComponent(trimmed); } catch { decoded = trimmed; }
    const resolved = posix.normalize(baseDir === '.' ? decoded : posix.join(baseDir, decoded));
    if (resolved === promptPath) return;
    const key = `${resolved}:${lineNo}:${inDeps ? 1 : 0}`;
    if (!seen.has(key)) {
      seen.add(key);
      links.push({ rawTarget: trimmed, target: resolved, canonical: canonicalRepoPath(resolved), line: lineNo, inDependencies: inDeps, inCallerNavigation: inCallerNav });
    }
  };

  for (const { lineNo, text: line } of maskedLines) {
    const h2 = /^ {0,3}##\s+(.+)$/.exec(line);
    if (h2) {
      const title = h2[1].trim();
      inDeps = /^dependencies\b/i.test(title);
      inCallerNav = /^(?:caller|consumer)\s+navigation\b/i.test(title);
      continue;
    }
    if (REF_LINK_DEF_RE.test(line)) continue;
    let m;
    inlineRe.lastIndex = 0;
    while ((m = inlineRe.exec(line)) !== null) pushTarget(m[1], lineNo);
    refUseRe.lastIndex = 0;
    while ((m = refUseRe.exec(line)) !== null) {
      const label = normalizeRefLabel(m[2] || m[1]);
      if (label && refMap.has(label)) pushTarget(refMap.get(label), lineNo);
    }
  }
  return links;
}

/**
 * Extract relative Markdown link targets inside `## Dependencies` with 1-based line numbers.
 */
export function extractDependencyLinks(raw, promptPath) {
  return extractRelativeMarkdownLinks(raw, promptPath).filter(l => l.inDependencies);
}

export function extractDependencyLinkTargets(raw, promptPath) {
  const targets = new Set();
  for (const link of extractDependencyLinks(raw, promptPath)) {
    if (link.canonical) targets.add(link.target);
  }
  return [...targets].sort();
}
