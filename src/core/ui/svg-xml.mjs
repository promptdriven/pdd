// Generated from prompts/cli/svg-layout.prompt.md.
// Inert XML safety, finite/sane viewBox validation, and workspace-guarded exact-case file reads for .ui.svg lint.
import { lstatSync, readdirSync, readFileSync } from 'node:fs';
import { relative, resolve, sep } from 'node:path';
import { runtimeWorkspaceSlice, workspace } from '../../shared/workspace-policy.mjs';

const { requireRuntimePath } = runtimeWorkspaceSlice();

const MAX_VIEWBOX_ASPECT_RATIO = 50;
const MAX_VIEWBOX_COORD = 1_000_000;
const MIN_VIEWBOX_DIM = 1e-3;
const STRICT_NUMBER_RE = /^[+-]?(?:\d+\.?\d*|\.\d+)(?:e[+-]?\d+)?$/i;

export function decodeXml(text) {
  if (/&(?!(?:amp|lt|gt|quot|apos|#\d+|#x[\da-f]+);)/i.test(text)) throw Error('invalid XML entity');
  return text.replace(/&([^;\s]+);/g, (_, value) => {
    const named = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'" };
    if (value in named) return named[value];
    const number = /^#x[\da-f]+$/i.test(value) ? parseInt(value.slice(2), 16) : /^#\d+$/.test(value) ? Number(value.slice(1)) : NaN;
    if (!Number.isInteger(number) || number <= 0 || number > 0x10ffff || (number >= 0xd800 && number <= 0xdfff)) throw Error('invalid XML entity');
    return String.fromCodePoint(number);
  });
}

function hasExactCaseSegment(dirPath, segment, dirCache) {
  let entries = dirCache?.get(dirPath);
  if (!entries) {
    try {
      entries = new Set(readdirSync(dirPath));
    } catch {
      return false;
    }
    if (dirCache) dirCache.set(dirPath, entries);
  }
  return entries.has(segment);
}

export function safeRead(root, path, policy = null, dirCache = null) {
  requireRuntimePath(policy ?? workspace.policy({ root }), { path, from: 'SVG advice' });
  const absRoot = resolve(root);
  const full = resolve(absRoot, path);
  const rel = relative(absRoot, full);
  if (!rel || rel === '..' || rel.startsWith(`..${sep}`) || resolve(absRoot, rel) !== full) throw Error('path escapes repository');
  const parts = rel.split(sep);
  let cur = absRoot;
  for (let i = 0; i < parts.length; i++) {
    const seg = parts[i];
    if (!hasExactCaseSegment(cur, seg, dirCache)) {
      const nextPath = resolve(cur, seg);
      try {
        lstatSync(nextPath);
        throw Error(`case mismatch on disk for "${rel.split(sep).join('/')}" (fails on case-sensitive Linux CI)`);
      } catch (err) {
        if (err?.message?.startsWith('case mismatch')) throw err;
        throw err;
      }
    }
    cur = resolve(cur, seg);
    const stat = lstatSync(cur);
    if (stat.isSymbolicLink()) throw Error('symlink paths are not allowed');
    if (i === parts.length - 1 && !stat.isFile()) throw Error('not a regular file');
  }
  return readFileSync(full, 'utf8');
}

export function markupTokens(source) {
  const tokens = source.match(/<!--[\s\S]*?(?:-->|$)|<!\[CDATA\[[\s\S]*?\]\]>|<[^>]*>|[^<]+|</g) || [];
  for (const token of tokens) {
    if (token.startsWith('<!--') && (!token.endsWith('-->') || token.slice(4, -3).includes('--') || token.slice(4, -3).endsWith('-'))) {
      throw Error('malformed or nested markup comment');
    }
  }
  return tokens;
}

export function stripComments(source) {
  return markupTokens(String(source ?? '')).filter(token => !token.startsWith('<!--')).join('');
}

/**
 * Validate SVG viewBox attribute: must parse to 4 finite numbers (minX minY width height),
 * width > 0, height > 0, sane coordinate magnitude (<= 1_000_000, dim >= 1e-3), and aspect ratio <= 50:1.
 */
export function validateSvgViewBox(rawViewBox) {
  const trimmed = String(rawViewBox ?? '').trim();
  if (!trimmed || /^,|,$|,\s*,/.test(trimmed)) {
    return `invalid viewBox ${JSON.stringify(rawViewBox)}: expected 4 finite numbers "minX minY width height"`;
  }
  const tokens = trimmed.split(/[\s,]+/).filter(Boolean);
  if (tokens.length !== 4 || tokens.some(t => !STRICT_NUMBER_RE.test(t))) {
    return `invalid viewBox ${JSON.stringify(rawViewBox)}: expected 4 finite numbers "minX minY width height"`;
  }
  const [minX, minY, width, height] = tokens.map(Number);
  if (!Number.isFinite(minX) || !Number.isFinite(minY) || !Number.isFinite(width) || !Number.isFinite(height)) {
    return `invalid viewBox ${JSON.stringify(rawViewBox)}: all 4 numbers must be finite`;
  }
  if (width <= 0 || height <= 0) {
    return `invalid viewBox ${JSON.stringify(rawViewBox)}: width (${width}) and height (${height}) must be positive`;
  }
  if (width < MIN_VIEWBOX_DIM || height < MIN_VIEWBOX_DIM) {
    return `invalid viewBox ${JSON.stringify(rawViewBox)}: dimensions (${width}x${height}) are below minimum usable size`;
  }
  const ratio = Math.max(width / height, height / width);
  if (!Number.isFinite(ratio) || ratio > MAX_VIEWBOX_ASPECT_RATIO) {
    return `invalid viewBox ${JSON.stringify(rawViewBox)}: aspect ratio ${ratio.toFixed(1)}:1 exceeds ${MAX_VIEWBOX_ASPECT_RATIO}:1 limit`;
  }
  if (Math.abs(minX) > MAX_VIEWBOX_COORD || Math.abs(minY) > MAX_VIEWBOX_COORD || width > MAX_VIEWBOX_COORD || height > MAX_VIEWBOX_COORD) {
    return `invalid viewBox ${JSON.stringify(rawViewBox)}: coordinate magnitude exceeds ${MAX_VIEWBOX_COORD} (risks <1px hairline collapse)`;
  }
  return null;
}

// An inert XML validator: no document type, entity expansion, execution or external resource loading.
export function validateSvgXml(source) {
  const tokens = markupTokens(source);
  const active = tokens.filter(token => !token.startsWith('<!--') && !token.startsWith('<![CDATA[')).join('\n');
  for (const match of active.matchAll(/<style\b[^>]*>([\s\S]*?)<\/style>/gi)) {
    if (/@import|url\s*\(/i.test(match[1].replace(/url\(\s*(['"]?)#[^)'"\s]+\1\s*\)/gi, ''))) {
      throw Error('external SVG stylesheet resources are not allowed');
    }
  }
  const stack = [];
  let roots = 0;
  let rootViewBox = undefined;
  for (const token of tokens) {
    if (token.startsWith('<!--')) continue;
    if (token.startsWith('<?')) {
      if (!/^<\?xml\s[\s\S]*\?>$/.test(token)) throw Error('unsafe SVG processing instruction');
      continue;
    }
    if (token.startsWith('</')) {
      const close = /^<\/([\w:-]+)\s*>$/.exec(token);
      if (!close || stack.pop()?.tag !== close[1]) throw Error('malformed XML closing tag');
    } else if (token.startsWith('<') && !token.startsWith('<![CDATA[')) {
      const match = /^<([\w:-]+)((?:\s+[\s\S]*?)?)\s*(\/?)>$/.exec(token);
      if (!match) throw Error('malformed XML element');
      const [, tag, raw, self] = match;
      const attrs = {};
      if (['script', 'foreignobject', 'iframe', 'object', 'embed'].includes(tag.split(':').at(-1).toLowerCase())) {
        throw Error('unsafe SVG content');
      }
      let remainder = raw.trim();
      while (remainder) {
        const attr = /^([\w:-]+)\s*=\s*("[^"]*"|'[^']*')\s*/.exec(remainder);
        if (!attr || attr[1] in attrs) throw Error('malformed XML attributes');
        attrs[attr[1]] = decodeXml(attr[2].slice(1, -1));
        remainder = remainder.slice(attr[0].length);
      }
      if (Object.keys(attrs).some(name => /^on/i.test(name))) throw Error('unsafe SVG content');
      if (!stack.length) {
        if (tag !== 'svg' || roots++) throw Error('expected one SVG root');
        if (Object.hasOwn(attrs, 'viewBox')) rootViewBox = attrs.viewBox;
      }
      const resourceValues = Object.values(attrs).join(' ').replace(/url\(\s*(['"]?)#[^)'"\s]+\1\s*\)/gi, '');
      if (
        Object.entries(attrs).some(([name, value]) => /^(?:href|xlink:href|src)$/i.test(name) && !value.startsWith('#'))
        || /(?:@import|url\s*\()/i.test(resourceValues)
      ) {
        throw Error('external SVG resources are not allowed');
      }
      if (!self) stack.push({ tag });
    } else {
      const text = token.startsWith('<![CDATA[') ? token.slice(9, -3) : decodeXml(token);
      if (!stack.length && text.trim()) throw Error('text outside SVG root');
    }
  }
  if (stack.length || roots !== 1 || tokens.join('') !== source) throw Error('malformed SVG');
  if (rootViewBox !== undefined) {
    const vbErr = validateSvgViewBox(rootViewBox);
    if (vbErr) {
      const err = Error(vbErr);
      err.part = 'viewBox';
      throw err;
    }
  }
  return { ok: true, viewBox: rootViewBox ?? null };
}
