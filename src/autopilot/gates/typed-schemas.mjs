// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: 75fde4547979ce8f760b5cb49996fe40b92c8567837622ceac4c2dd1c41f41ce).
import { createHash, createHmac, timingSafeEqual } from 'node:crypto';
import { redactSecrets } from '../../secret-redaction.mjs';
import { writeAtomicPrivate } from '../../shared/atomic-fs.mjs';

const strArr = (maxItems, extra = {}) => ({ type: 'array', items: { type: 'string', ...extra }, maxItems });
const strictObj = (required, properties) => Object.freeze({ type: 'object', additionalProperties: false, required, properties });

export const buildResultSchema = strictObj(['status', 'summary', 'changedPaths', 'testCommands', 'promptChanged', 'notes'], {
  status: { type: 'string', enum: ['ready', 'blocked', 'needs-decision'] }, summary: { type: 'string', maxLength: 2000 },
  changedPaths: strArr(200), testCommands: strArr(50), promptChanged: { type: 'boolean' }, notes: { type: 'string', maxLength: 4000 },
});
export const reviewResultSchema = strictObj(['verdict', 'mustFix', 'followUps', 'preExisting', 'summary'], {
  verdict: { type: 'string', enum: ['PASS', 'FAIL'] }, mustFix: strArr(50), followUps: strArr(50), preExisting: strArr(50), summary: { type: 'string', maxLength: 2000 },
});
export const gapCheckSchema = strictObj(['missingPathIds', 'unprovedAcIds', 'flags'], {
  missingPathIds: strArr(100), unprovedAcIds: strArr(100), flags: strArr(2, { enum: ['UNMAPPED_CHANGE', 'INSUFFICIENT_SCOPE'] }),
});
export const intakeCardSchema = strictObj(['decision', 'summary', 'acceptanceCriteria', 'touchedPaths', 'requiredCapabilities', 'questions'], {
  decision: { type: 'string', enum: ['ready', 'needs-clarification', 'skip'] }, summary: { type: 'string', maxLength: 2000 },
  acceptanceCriteria: strArr(50), touchedPaths: strArr(100), requiredCapabilities: strArr(30), questions: strArr(10),
});
export const TYPED_SCHEMAS = Object.freeze({ build: buildResultSchema, review: reviewResultSchema, 'gap-check': gapCheckSchema, intake: intakeCardSchema });

const FORBIDDEN_KEYS = new Set(['__proto__', 'constructor', 'prototype', 'confidence', 'score', 'probability', 'certainty', 'confidenceScore']);
const RECEIPT_OUTCOMES = new Set(['proved', 'failed', 'missing_capability', 'service_failure']);
const REQUIRED_RECEIPT_STRINGS = ['repo', 'acRevision', 'targetTip', 'candidateHead', 'integratedTree', 'trustedPolicyDigest', 'recipeDigest', 'testProfile', 'command', 'toolchain', 'artifactDigest'];
// Stateless non-/g regexes for .test(), paired with /g variants ONLY for .replace().
const BIDI_AND_ZW_TEST_RE = /[\uFEFF\u061C\u200B-\u200F\u202A-\u202E\u2060\u2066-\u2069]/;
const CTRL_TEST_RE = /[\x00-\x08\x0B\x0C\x0E-\x1F\x7F-\x9F]/;
const BIDI_AND_ZW_REPLACE_RE = /[\uFEFF\u061C\u200B-\u200F\u202A-\u202E\u2060\u2066-\u2069]/g;
const CTRL_REPLACE_RE = /[\x00-\x08\x0B\x0C\x0E-\x1F\x7F-\x9F]/g;
const isPlainObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
const nonEmptyStr = (v) => typeof v === 'string' && v.trim().length > 0;

/** Hardening 1: Linear O(N) ANSI CSI/OSC (bounded; unterminated sequences never eat trailing text), C0/C1, BOM, ZW, and bidi sanitizer. */
export function sanitizeUntrustedText(raw) {
  const s = String(raw ?? '');
  let out = '';
  for (let i = 0; i < s.length; i += 1) {
    if (s.charCodeAt(i) === 0x1b) {
      const nx = s[i + 1];
      if (nx === '[') {
        const lim = Math.min(s.length, i + 64);
        let j = i + 2;
        while (j < lim && (s.charCodeAt(j) < 0x40 || s.charCodeAt(j) > 0x7e) && s[j] !== '\n' && s[j] !== '\r') j += 1;
        i = (j < lim && s.charCodeAt(j) >= 0x40 && s.charCodeAt(j) <= 0x7e) ? j : i + 1;
        continue;
      }
      if (nx === ']') {
        const lim = Math.min(s.length, i + 2048);
        let j = i + 2, terminated = false;
        while (j < lim && s[j] !== '\n' && s[j] !== '\r') {
          if (s.charCodeAt(j) === 0x07) { terminated = true; break; }
          if (s.charCodeAt(j) === 0x1b && s[j + 1] === '\\') { j += 1; terminated = true; break; }
          j += 1;
        }
        i = terminated ? j : i + 1;
        continue;
      }
      continue;
    }
    out += s[i];
  }
  return out.replace(BIDI_AND_ZW_REPLACE_RE, '').replace(CTRL_REPLACE_RE, '');
}

/** Hardening 2: Dynamic tilde fence strictly longer than any backtick or tilde run in payload. */
export function wrapWithSafeFence(raw, lang = 'text') {
  const clean = sanitizeUntrustedText(raw);
  let maxRun = 3;
  for (const m of clean.matchAll(/`{3,}|~{3,}/g)) if (m[0].length > maxRun) maxRun = m[0].length;
  const fence = '~'.repeat(maxRun + 1);
  return `${fence}${String(lang).replace(/[^A-Za-z0-9_-]/g, '')}\n${clean}\n${fence}`;
}

/** Hardening 3: Size & JSON nesting depth guard (O(N), DoS-safe). */
export function enforceSizeAndDepthBounds(raw, { maxBytes = 262_144, maxDepth = 16 } = {}) {
  const text = String(raw ?? '');
  if (Buffer.byteLength(text, 'utf8') > maxBytes) return { ok: false, error: `Input exceeds ${maxBytes} byte bound.` };
  let depth = 0, inStr = false;
  for (let i = 0; i < text.length; i += 1) {
    const c = text[i];
    if (inStr) { if (c === '\\') { i += 1; continue; } if (c === '"') inStr = false; continue; }
    if (c === '"') inStr = true;
    else if (c === '{' || c === '[') { if (++depth > maxDepth) return { ok: false, error: `JSON nesting depth exceeds ${maxDepth}.` }; }
    else if (c === '}' || c === ']') depth = Math.max(0, depth - 1);
  }
  return { ok: true, error: null };
}

/** Hardening 4: Linear single-pass duplicate JSON object key detector (defeats key-override attacks). */
export function detectDuplicateJsonKeys(jsonText) {
  const s = String(jsonText ?? ''), stack = [];
  for (let i = 0; i < s.length; i += 1) {
    const c = s[i];
    if (c === ' ' || c === '\t' || c === '\r' || c === '\n') continue;
    if (c === '{') { stack.push({ kind: 'obj', expectKey: true, keys: new Set() }); continue; }
    if (c === '[') { stack.push({ kind: 'arr' }); continue; }
    if (c === '}' || c === ']') { stack.pop(); continue; }
    if (c === ',') { const top = stack.at(-1); if (top?.kind === 'obj') top.expectKey = true; continue; }
    if (c === ':') { const top = stack.at(-1); if (top?.kind === 'obj') top.expectKey = false; continue; }
    if (c === '"') {
      let j = i + 1;
      while (j < s.length && s[j] !== '"') j += s[j] === '\\' ? 2 : 1;
      const top = stack.at(-1);
      if (top?.kind === 'obj' && top.expectKey) {
        let key; try { key = JSON.parse(s.slice(i, j + 1)); } catch { return { hasDuplicate: false, duplicateKey: null }; }
        if (top.keys.has(key)) return { hasDuplicate: true, duplicateKey: key };
        top.keys.add(key); top.expectKey = false;
      }
      i = j;
    }
  }
  return { hasDuplicate: false, duplicateKey: null };
}

/** Hardening 5: Safe JSON parse rejecting duplicate/forbidden/unsafe keys and sanitizing decoded string values. */
export function safeJsonParse(raw, { maxBytes = 262_144, maxDepth = 16, sanitizeStrings = true } = {}) {
  const text = String(raw ?? '').replace(/^\uFEFF/, '').trim();
  const bounds = enforceSizeAndDepthBounds(text, { maxBytes, maxDepth });
  if (!bounds.ok) return { ok: false, value: null, error: bounds.error };
  const dup = detectDuplicateJsonKeys(text);
  if (dup.hasDuplicate) return { ok: false, value: null, error: `Duplicate JSON key "${dup.duplicateKey}" rejected.` };
  let parsed;
  try { parsed = JSON.parse(text); } catch (err) { return { ok: false, value: null, error: err?.message ?? 'Invalid JSON.' }; }
  let err = null;
  const walk = (node, depth) => {
    if (err) return node;
    if (depth > maxDepth) { err = 'Max object depth exceeded.'; return node; }
    if (typeof node === 'string') return sanitizeStrings ? sanitizeUntrustedText(node) : node;
    if (Array.isArray(node)) return node.map((item) => walk(item, depth + 1));
    if (isPlainObj(node)) {
      const cleanObj = {};
      for (const k of Object.keys(node)) {
        if (FORBIDDEN_KEYS.has(k) || BIDI_AND_ZW_TEST_RE.test(k) || CTRL_TEST_RE.test(k) || k.includes('\x1b')) { err = `Forbidden or unsafe key "${k}" rejected.`; return node; }
        cleanObj[k] = walk(node[k], depth + 1);
      }
      return cleanObj;
    }
    return node;
  };
  const cleaned = walk(parsed, 0);
  return err ? { ok: false, value: null, error: err } : { ok: true, value: cleaned, error: null };
}

function parseFenceOpenLine(line) {
  const open = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(line);
  if (!open) return null;
  if (open[1][0] === '`' && open[2].includes('`')) return null;
  return {
    ch: open[1][0],
    len: open[1].length,
    lang: (open[2].trim().split(/[\s{`~]/)[0] ?? '').toLowerCase(),
  };
}

function isFenceCloseLine(line, active) {
  const close = /^ {0,3}(`{3,}|~{3,})[ \t]*$/.exec(line);
  return Boolean(close && close[1][0] === active.ch && close[1].length >= active.len);
}

function parseDiffHunkHeader(line) {
  const m = /^@@\s+-(\d+)(?:,(\d+))?\s+\+(\d+)(?:,(\d+))?\s+@@/.exec(line);
  if (!m) return { counted: false, oldRem: 0, newRem: 0 };
  return {
    counted: true,
    oldRem: m[2] === undefined ? 1 : Number(m[2]),
    newRem: m[4] === undefined ? 1 : Number(m[4]),
  };
}

function consumeDiffHunkLine(line, hunk) {
  if (!hunk) return false;
  if (line === '\\ No newline at end of file') return true;
  if (hunk.counted) {
    if (hunk.oldRem <= 0 && hunk.newRem <= 0) return false;
    if (line.startsWith(' ') && hunk.oldRem > 0 && hunk.newRem > 0) {
      hunk.oldRem -= 1;
      hunk.newRem -= 1;
      return true;
    }
    if (line.startsWith('-') && hunk.oldRem > 0) {
      hunk.oldRem -= 1;
      return true;
    }
    if (line.startsWith('+') && hunk.newRem > 0) {
      hunk.newRem -= 1;
      return true;
    }
    return false;
  }
  return /^[ +-]/.test(line);
}

/**
 * Hardening 6 (detailed): Single-pass O(N) injection container stripper.
 * Preserves visible top-level fenced code blocks verbatim (so JSON strings containing `<!--` survive
 * even after introductory prose), while stripping HTML comments (closed, nested, boundary-spliced,
 * abrupt-closing `<!-->`/`<!--->`, and unclosed to EOF), blockquotes, and unified diff hunks
 * (respecting `@@ -a,b +c,d @@` line counts so completed hunks never swallow following bullets/fences).
 */
export function stripInjectionContainersDetailed(raw) {
  const src = sanitizeUntrustedText(raw).replace(/\r\n/g, '\n');
  const segments = [];
  let proseBuf = [];
  let unclosedComment = false;
  let activeHunk = null;
  let pos = 0;
  let nextNewlinePos = src.indexOf('\n', 0);
  let nextCommentPos = src.indexOf('<!--', 0);

  const flushProse = () => {
    if (!proseBuf.length) return;
    segments.push({ fence: false, text: proseBuf.join('') });
    proseBuf = [];
  };

  const popTail3 = () => {
    let tail = '';
    while (tail.length < 3 && proseBuf.length > 0) {
      const chunk = proseBuf.pop();
      const need = 3 - tail.length;
      if (chunk.length > need) {
        proseBuf.push(chunk.slice(0, chunk.length - need));
        tail = chunk.slice(chunk.length - need) + tail;
      } else {
        tail = chunk + tail;
      }
    }
    return tail;
  };

  const closeCommentFrom = (bodyStart) => {
    // HTML5 §13.2.5.42 abrupt-closing comments `<!-->` and `<!--->` close immediately.
    if (src[bodyStart] === '>') return bodyStart + 1;
    if (src[bodyStart] === '-' && src[bodyStart + 1] === '>') return bodyStart + 2;
    const end = src.indexOf('-->', bodyStart);
    return end >= 0 ? end + 3 : -1;
  };

  const consumeCommentAndSplices = (start) => {
    const after = closeCommentFrom(start + 4);
    if (after < 0) {
      unclosedComment = true;
      pos = src.length;
      return;
    }
    pos = after;
    while (pos <= src.length) {
      const tail = popTail3();
      const probe = tail + src.slice(pos, pos + 3);
      const spliceIdx = probe.indexOf('<!--');
      if (spliceIdx < 0) {
        if (tail) proseBuf.push(tail);
        break;
      }
      if (spliceIdx > 0) proseBuf.push(tail.slice(0, spliceIdx));
      pos += Math.max(0, spliceIdx + 4 - tail.length);
      const synAfter = closeCommentFrom(pos);
      if (synAfter < 0) {
        unclosedComment = true;
        pos = src.length;
        break;
      }
      pos = synAfter;
    }
  };

  while (pos < src.length && !unclosedComment) {
    const atLineStart = pos === 0 || src[pos - 1] === '\n';
    if (nextNewlinePos >= 0 && nextNewlinePos < pos) {
      nextNewlinePos = src.indexOf('\n', pos);
    }
    const nl = nextNewlinePos;
    const lineEnd = nl < 0 ? src.length : nl;
    const nextLinePos = nl < 0 ? src.length : nl + 1;

    if (atLineStart) {
      const line = src.slice(pos, lineEnd);
      if (activeHunk) {
        if (consumeDiffHunkLine(line, activeHunk)) {
          pos = nextLinePos;
          continue;
        }
        activeHunk = null;
      }
      if (/^@@ /.test(line)) {
        activeHunk = parseDiffHunkHeader(line);
        pos = nextLinePos;
        continue;
      }
      if (/^(?:diff --git |--- [a-z/]|\+\+\+ [a-z/])/i.test(line)) {
        pos = nextLinePos;
        continue;
      }
      if (/^\s*>/.test(line) || /^[+-]\s*(?:\{|```|~~~)/.test(line)) {
        pos = nextLinePos;
        continue;
      }
      const fence = parseFenceOpenLine(line);
      if (fence) {
        flushProse();
        let scanPos = nextLinePos;
        let fenceEnd = src.length;
        while (scanPos < src.length) {
          const snl = src.indexOf('\n', scanPos);
          const sEnd = snl < 0 ? src.length : snl;
          const sNext = snl < 0 ? src.length : snl + 1;
          if (isFenceCloseLine(src.slice(scanPos, sEnd), fence)) {
            fenceEnd = sNext;
            break;
          }
          scanPos = sNext;
        }
        segments.push({ fence: true, text: src.slice(pos, fenceEnd) });
        pos = fenceEnd;
        continue;
      }
    }

    if (nextCommentPos >= 0 && nextCommentPos < pos) {
      nextCommentPos = src.indexOf('<!--', pos);
    }
    if (nextCommentPos < 0 || nextCommentPos >= lineEnd) {
      proseBuf.push(src.slice(pos, nextLinePos));
      pos = nextLinePos;
      continue;
    }
    if (nextCommentPos > pos) proseBuf.push(src.slice(pos, nextCommentPos));
    consumeCommentAndSplices(nextCommentPos);
  }
  flushProse();

  const outLines = [];
  let postHunk = null;
  for (const seg of segments) {
    if (seg.fence) {
      postHunk = null;
      const cleanFence = seg.text.endsWith('\n') ? seg.text.slice(0, -1) : seg.text;
      outLines.push(cleanFence);
      continue;
    }
    const rawSeg = seg.text.endsWith('\n') ? seg.text.slice(0, -1) : seg.text;
    for (const line of rawSeg.split('\n')) {
      if (postHunk) {
        if (consumeDiffHunkLine(line, postHunk)) continue;
        postHunk = null;
      }
      if (/^\s*>/.test(line)) continue;
      if (/^@@ /.test(line)) { postHunk = parseDiffHunkHeader(line); continue; }
      if (/^(?:diff --git |--- [a-z/]|\+\+\+ [a-z/])/i.test(line)) continue;
      if (/^[+-]\s*(?:\{|```|~~~)/.test(line)) continue;
      outLines.push(line);
    }
  }
  return { text: outLines.join('\n'), unclosedComment };
}

/** Hardening 6: Strip HTML comments, blockquotes, and unified diff lines (preserving ordinary `- ` Markdown bullets). */
export function stripInjectionContainers(raw) {
  return stripInjectionContainersDetailed(raw).text;
}

/** Hardening 7: Extract strictly closed JSON fences, prose outside all fences, and detect unclosed/truncated fence attacks. */
export function extractClosedJsonFences(raw) {
  const blocks = [];
  const outsideLines = [];
  let active = null;
  for (const line of String(raw ?? '').split(/\r?\n/)) {
    if (active) {
      if (isFenceCloseLine(line, active)) {
        if (active.lang === 'json' || active.lang === '') blocks.push(active.lines.join('\n').trim());
        active = null;
      } else active.lines.push(line);
      continue;
    }
    const open = parseFenceOpenLine(line);
    if (open) {
      active = { ...open, lines: [] };
      continue;
    }
    outsideLines.push(line);
  }
  return { blocks, outsideText: outsideLines.join('\n'), unclosedFence: Boolean(active) };
}

export const MAX_CANDIDATE_JSON_OBJECTS = 4096;
export const DECISION_JSON_KEY_RE = /"(?:verdict|decision|status|missingPathIds|unprovedAcIds|flags|mustFix|confidence|score|__proto__)"/;

export function hasEmbeddedFenceLine(block) {
  return String(block ?? '').split(/\r?\n/).some((ln) => Boolean(parseFenceOpenLine(ln)));
}

export function scanBalancedJsonStrings(text, maxObjects = MAX_CANDIDATE_JSON_OBJECTS) {
  const s = String(text ?? '');
  const root = [];
  const stack = [];
  let inStr = false;
  let esc = false;
  for (let i = 0; i < s.length; i += 1) {
    const c = s[i];
    if (inStr) {
      if (esc) esc = false;
      else if (c === '\\') esc = true;
      else if (c === '"' || c === '\n') inStr = false;
      continue;
    }
    if (c === '"') {
      if (stack.length > 0) inStr = true;
      continue;
    }
    if (c === '{') {
      stack.push({ start: i, children: [] });
    } else if (c === '}' && stack.length > 0) {
      const frame = stack.pop();
      const target = stack.length > 0 ? stack.at(-1).children : root;
      target.push([frame.start, i + 1]);
    }
  }
  const unclosedObject = stack.length > 0;
  let unclosedDecision = false;
  if (unclosedObject) {
    const unclosedTail = s.slice(stack[0].start);
    if (DECISION_JSON_KEY_RE.test(unclosedTail)) unclosedDecision = true;
  }
  for (const frame of stack) {
    for (const span of frame.children) root.push(span);
  }
  if (root.length > maxObjects) {
    return {
      items: root.slice(0, maxObjects).map(([a, b]) => s.slice(a, b)),
      truncated: true,
      unclosedObject,
      unclosedDecision,
    };
  }
  return {
    items: root.map(([a, b]) => s.slice(a, b)),
    truncated: false,
    unclosedObject,
    unclosedDecision,
  };
}

const normStrArr = (a) => (Array.isArray(a) ? [...new Set(a.map((x) => String(x)))].sort() : null);

/** Hardening 8: Detect conflicting verdict/decision/status/gap-check arrays across multiple candidate objects. */
export function detectConflictingVerdicts(candidates) {
  if (!Array.isArray(candidates) || candidates.length < 2) return false;
  return new Set(candidates.map((c) => JSON.stringify([c?.verdict ?? null, c?.decision ?? null, c?.status ?? null, normStrArr(c?.flags), normStrArr(c?.missingPathIds), normStrArr(c?.unprovedAcIds)]))).size > 1;
}

/** Hardening 9: Strict schema validator (additionalProperties: false, closed enums, bounds, nullable union types). */
export function validateAgainstSchema(value, schema) {
  if (!isPlainObj(schema)) return { ok: false, error: 'Missing schema definition.' };
  if (Array.isArray(schema.type)) {
    const errors = [];
    for (const branchType of schema.type) {
      const sub = validateAgainstSchema(value, { ...schema, type: branchType });
      if (sub.ok) return sub;
      errors.push(sub.error);
    }
    return { ok: false, error: errors[0] || `Value did not match union type [${schema.type.join(', ')}].` };
  }
  if (schema.type === 'null') return value === null ? { ok: true, error: null } : { ok: false, error: 'Expected null.' };
  if (schema.type === 'object') {
    if (!isPlainObj(value)) return { ok: false, error: 'Expected JSON object.' };
    const props = schema.properties ?? {};
    for (const req of schema.required ?? []) if (!Object.hasOwn(value, req)) return { ok: false, error: `Missing required property "${req}".` };
    for (const key of Object.keys(value)) {
      if (FORBIDDEN_KEYS.has(key)) return { ok: false, error: `Forbidden property "${key}".` };
      if (schema.additionalProperties === false && !Object.hasOwn(props, key)) return { ok: false, error: `Unexpected property "${key}".` };
      if (Object.hasOwn(props, key)) { const sub = validateAgainstSchema(value[key], props[key]); if (!sub.ok) return { ok: false, error: `${key}: ${sub.error}` }; }
    }
    return { ok: true, error: null };
  }
  if (schema.type === 'array') {
    if (!Array.isArray(value)) return { ok: false, error: 'Expected array.' };
    if (Number.isInteger(schema.maxItems) && value.length > schema.maxItems) return { ok: false, error: `Array exceeds maxItems ${schema.maxItems}.` };
    if (schema.items) for (let i = 0; i < value.length; i += 1) { const sub = validateAgainstSchema(value[i], schema.items); if (!sub.ok) return { ok: false, error: `[${i}]: ${sub.error}` }; }
    return { ok: true, error: null };
  }
  if (schema.type === 'string') {
    if (typeof value !== 'string') return { ok: false, error: 'Expected string.' };
    if (Number.isInteger(schema.maxLength) && value.length > schema.maxLength) return { ok: false, error: `String exceeds maxLength ${schema.maxLength}.` };
    if (Array.isArray(schema.enum) && !schema.enum.includes(value)) return { ok: false, error: `Value "${value}" not in enum [${schema.enum.join(', ')}].` };
    return { ok: true, error: null };
  }
  if (schema.type === 'boolean') return typeof value === 'boolean' ? { ok: true, error: null } : { ok: false, error: 'Expected boolean.' };
  return { ok: false, error: `Unsupported schema type "${schema.type}".` };
}

/** Hardening 10: Unwrap Claude/Codex structured envelopes while NEVER flipping an outer verdict/decision via nested fields. */
export function unwrapStructuredEnvelope(parsed) {
  if (!isPlainObj(parsed)) return { ok: false, value: null, error: 'Expected JSON object envelope.' };
  if (parsed.is_error === true || parsed.type === 'error' || parsed.type === 'turn.failed') return { ok: false, value: null, error: 'Terminal error envelope rejected.' };
  const hasOuterDecision = Object.hasOwn(parsed, 'verdict') || Object.hasOwn(parsed, 'decision') || Object.hasOwn(parsed, 'missingPathIds') || (Object.hasOwn(parsed, 'status') && ['ready', 'blocked', 'needs-decision'].includes(parsed.status));
  const hasNested = isPlainObj(parsed.structured_output) || (typeof parsed.result === 'string' && parsed.result.trim().startsWith('{'));
  if (hasOuterDecision && hasNested) return { ok: false, value: null, error: 'Conflicting outer decision and nested envelope rejected.' };
  if (isPlainObj(parsed.structured_output)) return { ok: true, value: parsed.structured_output, error: null };
  if (typeof parsed.result === 'string' && parsed.result.trim().startsWith('{')) {
    const inner = safeJsonParse(parsed.result);
    return inner.ok ? { ok: true, value: inner.value, error: null } : { ok: false, value: null, error: inner.error };
  }
  return { ok: true, value: parsed, error: null };
}

const UNSUPPORTED_PROVIDER_SCHEMA_KEYS = new Set(['maxLength', 'minLength', 'maxItems', 'minItems', 'pattern', 'format', '$schema']);

/** Convert a schema to strict Codex/Claude/Agy JSON-schema wire shape (`additionalProperties: false`, all keys required, no unsupported keywords). */
export function toProviderStrictSchema(schema) {
  if (!isPlainObj(schema)) throw new Error('toProviderStrictSchema requires a schema object.');
  const walk = (node) => {
    if (Array.isArray(node)) return node.map(walk);
    if (!isPlainObj(node)) return node;
    const out = {};
    for (const [k, v] of Object.entries(node)) {
      if (UNSUPPORTED_PROVIDER_SCHEMA_KEYS.has(k)) continue;
      if (k === 'properties' && isPlainObj(v)) {
        const cleanProps = {};
        for (const [pk, pv] of Object.entries(v)) cleanProps[pk] = walk(pv);
        out.properties = cleanProps;
      } else if (k === 'items' && isPlainObj(v)) {
        out.items = walk(v);
      } else {
        out[k] = v;
      }
    }
    if (out.type === 'object') {
      out.additionalProperties = false;
      const propKeys = isPlainObj(out.properties) ? Object.keys(out.properties) : [];
      out.required = [...propKeys];
    }
    return out;
  };
  return walk(schema);
}

/** Strict wire schema for Autopilot Core's blind review JSON output (`codex --output-schema`, `claude --json-schema`, `agy --json-schema`). */
export function buildCoreReviewSchema({ includeDecisionFields = false } = {}) {
  const properties = {
    verdict: { type: 'string', enum: ['PASS', 'FAIL'] },
    head: { type: 'string' },
    summary: { type: 'string' },
    mustFix: { type: 'array', items: { type: 'string' } },
    preExisting: { type: 'array', items: { type: 'string' } },
    ...(includeDecisionFields
      ? {
          question: { type: ['string', 'null'] },
          options: { type: 'array', items: { type: 'string' } },
          recommended: { type: ['string', 'null'] },
        }
      : {}),
  };
  return Object.freeze({
    type: 'object',
    additionalProperties: false,
    required: Object.keys(properties),
    properties,
  });
}

/** CLI native schema flag builders (`codex exec --output-schema`, `claude -p --json-schema`, `agy --json-schema`). */
export function buildCodexSchemaArgs({ schemaPath, schema = null, fs = null, strictProvider = false } = {}) {
  if (typeof schemaPath !== 'string' || !schemaPath.trim()) throw new Error('codex --output-schema requires a non-empty schemaPath.');
  const wireSchema = schema !== null ? (strictProvider ? toProviderStrictSchema(schema) : schema) : null;
  if (wireSchema !== null) writeAtomicPrivate(fs, schemaPath, `${JSON.stringify(wireSchema, null, 2)}\n`, 0o700, 0o600);
  return ['--output-schema', schemaPath];
}
export function buildClaudeSchemaArgs({ schema, strictProvider = false } = {}) {
  if (!isPlainObj(schema)) throw new Error('claude --json-schema requires a schema object.');
  const wireSchema = strictProvider ? toProviderStrictSchema(schema) : schema;
  return ['--json-schema', JSON.stringify(wireSchema)];
}
export function buildAgySchemaArgs({ schema, strictProvider = false } = {}) {
  if (!isPlainObj(schema)) throw new Error('agy --json-schema requires a schema object.');
  const wireSchema = strictProvider ? toProviderStrictSchema(schema) : schema;
  return ['--json-schema', JSON.stringify(wireSchema)];
}
export function buildNativeSchemaArgs({ agentKind = '', schema, schemaPath = '', fs = null, strictProvider = false } = {}) {
  const kind = String(agentKind ?? '').trim().toLowerCase();
  if (kind === 'codex') return buildCodexSchemaArgs({ schemaPath, schema, fs, strictProvider });
  if (kind === 'claude') return buildClaudeSchemaArgs({ schema, strictProvider });
  if (kind === 'agy') return buildAgySchemaArgs({ schema, strictProvider });
  return [];
}

const hasDecisionKey = (obj) => isPlainObj(obj) && (Object.hasOwn(obj, 'verdict') || Object.hasOwn(obj, 'decision') || Object.hasOwn(obj, 'status') || Object.hasOwn(obj, 'missingPathIds') || Object.hasOwn(obj, 'unprovedAcIds') || Object.hasOwn(obj, 'flags'));

/** Dual-read parser: prefers strict typed JSON schema output, fails closed on desynced/conflicting/extra-key decision blocks. */
export function parseTypedOrLegacyOutput(raw, { schemaName = null, schema = null, legacyParser = null, maxBytes = 262_144, maxDepth = 16 } = {}) {
  const targetSchema = schema ?? (schemaName ? TYPED_SCHEMAS[schemaName] : null);
  const fail = (source, error, finalRejection = false) => ({ ok: false, source, value: null, reason: 'malformed_output', error, finalRejection });
  if (!targetSchema) return fail('none', 'Unknown schema.', true);
  const text = String(raw ?? '').replace(/^\uFEFF/, '');
  const bounds = enforceSizeAndDepthBounds(text, { maxBytes, maxDepth });
  if (!bounds.ok) return fail('none', bounds.error, true);

  const trimmed = text.trim();
  if (trimmed.startsWith('{')) {
    const parsed = safeJsonParse(trimmed, { maxBytes, maxDepth });
    if (!parsed.ok) return fail('typed-json', parsed.error, true);
    const env = unwrapStructuredEnvelope(parsed.value);
    if (!env.ok) return fail('typed-json', env.error, true);
    const valid = validateAgainstSchema(env.value, targetSchema);
    return valid.ok ? { ok: true, source: 'typed-json', value: env.value, reason: null, error: null, finalRejection: false } : fail('typed-json', valid.error, false);
  }

  const { text: stripped, unclosedComment } = stripInjectionContainersDetailed(text);
  if (unclosedComment) return fail('legacy-fallback', 'Unclosed HTML comment rejected.', true);
  const { blocks, outsideText, unclosedFence } = extractClosedJsonFences(stripped);
  if (unclosedFence) return fail('legacy-fallback', 'Unclosed fenced block rejected.', true);
  if (blocks.some(hasEmbeddedFenceLine)) {
    return fail('legacy-fallback', 'Desynced nested fence rejected.', true);
  }

  // Collect JSON candidates from closed json/unlabeled fences (including heading + JSON blocks)
  // and prose outside other fences (never treating quoted code inside ```diff / ```js / ```markdown fences as review decisions).
  // Fail closed on truncated/unclosed objects, ambiguous unclosed decision boundaries, or cumulative candidate cap overflow.
  const collected = [];
  let totalScanned = 0;
  for (const b of blocks) {
    const scanned = scanBalancedJsonStrings(b);
    totalScanned += scanned.items.length;
    if (scanned.truncated || totalScanned > MAX_CANDIDATE_JSON_OBJECTS) {
      return fail('legacy-fallback', 'Candidate object scan limit exceeded.', true);
    }
    if (scanned.unclosedObject) {
      return fail('legacy-fallback', 'Truncated or unclosed JSON object in fence rejected.', true);
    }
    if (scanned.items.length > 0) collected.push(...scanned.items);
    else if (b.startsWith('{')) collected.push(b);
  }
  const outsideScanned = scanBalancedJsonStrings(outsideText);
  totalScanned += outsideScanned.items.length;
  if (outsideScanned.truncated || totalScanned > MAX_CANDIDATE_JSON_OBJECTS) {
    return fail('legacy-fallback', 'Candidate object scan limit exceeded.', true);
  }
  if (outsideScanned.unclosedDecision) {
    return fail('legacy-fallback', 'Truncated or ambiguous unclosed JSON decision rejected.', true);
  }
  collected.push(...outsideScanned.items);
  const candidateTexts = [...new Set(collected)];
  const validCandidates = [], allDecisionObjects = [];
  for (const snippet of candidateTexts) {
    const p = safeJsonParse(snippet, { maxBytes, maxDepth });
    if (!p.ok) {
      if (blocks.includes(snippet) || DECISION_JSON_KEY_RE.test(snippet)) return fail('legacy-fallback', p.error, true);
      continue;
    }
    const v = validateAgainstSchema(p.value, targetSchema);
    if (hasDecisionKey(p.value)) {
      allDecisionObjects.push(p.value);
      if (!v.ok) return fail('legacy-fallback', `Malformed or extra-key decision block rejected: ${v.error}`, true);
    }
    if (v.ok) validCandidates.push(p.value);
  }
  if (detectConflictingVerdicts(allDecisionObjects) || detectConflictingVerdicts(validCandidates)) return fail('legacy-fallback', 'Conflicting JSON verdicts detected in output.', true);
  if (validCandidates.length > 0) return { ok: true, source: 'legacy-fallback', value: validCandidates.at(-1), reason: null, error: null, finalRejection: false };

  if (typeof legacyParser === 'function') {
    const legacyVal = legacyParser(stripped);
    if (legacyVal !== null && legacyVal !== undefined) {
      const v = validateAgainstSchema(legacyVal, targetSchema);
      return v.ok ? { ok: true, source: 'legacy-fallback', value: legacyVal, reason: null, error: null, finalRejection: false } : fail('legacy-fallback', v.error, true);
    }
  }
  return fail('none', 'No valid typed JSON or legacy structured output found.', false);
}

const canonicalPayload = (obj) => Object.fromEntries(Object.keys(obj).sort().filter((k) => obj[k] !== undefined).map((k) => [k, obj[k]]));
const cleanReceiptStr = (v) => redactSecrets(sanitizeUntrustedText(v)).trim();
const computeReceiptDigest = (core, hmacKey = null) => (hmacKey ? createHmac('sha256', hmacKey) : createHash('sha256')).update(JSON.stringify(canonicalPayload(core))).digest('hex');
const hexEqual = (a, b) => typeof a === 'string' && typeof b === 'string' && a.length === b.length && /^[a-f0-9]{64}$/.test(a) && /^[a-f0-9]{64}$/.test(b) && timingSafeEqual(Buffer.from(a, 'hex'), Buffer.from(b, 'hex'));

/** Deterministic harness PR receipt stamper aligned 100% with evidence-contract.mjs (all 13 fields + optional HMAC-SHA256). */
export function formatHarnessPrReceipt({
  repo, acRevision, targetTip, candidateHead, integratedTree, sourceTreeSha, trustedPolicyDigest, policyDigest,
  recipeDigest, testProfile, command, toolchain, capability = null, outcome, artifactDigest,
  pathId = undefined, pathIds = undefined, hmacKey = null,
} = {}) {
  const rawFields = { repo, acRevision, targetTip, candidateHead, integratedTree: integratedTree ?? sourceTreeSha, trustedPolicyDigest: trustedPolicyDigest ?? policyDigest, recipeDigest, testProfile, command, toolchain, artifactDigest };
  const cleaned = {};
  for (const k of REQUIRED_RECEIPT_STRINGS) {
    if (!nonEmptyStr(rawFields[k])) throw new Error(`formatHarnessPrReceipt requires non-empty ${k}.`);
    cleaned[k] = cleanReceiptStr(rawFields[k]);
    if (!cleaned[k]) throw new Error(`formatHarnessPrReceipt field ${k} is empty after sanitization.`);
  }
  const cleanOutcome = nonEmptyStr(outcome) ? cleanReceiptStr(outcome) : '';
  if (!RECEIPT_OUTCOMES.has(cleanOutcome)) throw new Error(`formatHarnessPrReceipt requires explicit outcome in [${[...RECEIPT_OUTCOMES].join(', ')}].`);
  if (capability !== null && !nonEmptyStr(capability)) throw new Error('formatHarnessPrReceipt capability must be null or a non-empty string.');
  if (hmacKey !== null && hmacKey !== undefined && !(typeof hmacKey === 'string' && hmacKey.length > 0) && !Buffer.isBuffer(hmacKey)) throw new Error('formatHarnessPrReceipt hmacKey must be a non-empty string or Buffer.');

  const core = canonicalPayload({
    ...cleaned, sourceTreeSha: cleaned.integratedTree, policyDigest: cleaned.trustedPolicyDigest,
    capability: capability === null ? null : cleanReceiptStr(capability), outcome: cleanOutcome,
    writtenBy: 'harness', digestAlg: hmacKey ? 'hmac-sha256' : 'sha256',
    ...(nonEmptyStr(pathId) ? { pathId: cleanReceiptStr(pathId) } : {}),
    ...(Array.isArray(pathIds) && pathIds.length ? { pathIds: [...new Set(pathIds.filter(nonEmptyStr).map(cleanReceiptStr))].sort() } : {}),
  });
  const receiptDigest = computeReceiptDigest(core, hmacKey || null);
  const stamped = canonicalPayload({ ...core, receiptDigest });
  const safeJson = JSON.stringify(stamped).replace(/</g, '\\u003c').replace(/>/g, '\\u003e');
  const summary = redactSecrets(`Harness Receipt: outcome=${core.outcome}; integratedTree=${core.integratedTree}; trustedPolicyDigest=${core.trustedPolicyDigest}; recipeDigest=${core.recipeDigest}; receiptDigest=${receiptDigest.slice(0, 16)}`);
  return `<!-- pdd:harness-receipt:v1 ${safeJson} -->\n${summary}`;
}

export function parseHarnessPrReceipt(text, { hmacKey = null, requireKeyed = false } = {}) {
  const matches = [...String(text ?? '').matchAll(/<!--\s*pdd:harness-receipt:v1\b([\s\S]*?)-->/g)];
  if (matches.length === 0) return { ok: false, receipt: null, error: 'Harness receipt marker not found.' };
  if (matches.length > 1) return { ok: false, receipt: null, error: 'Multiple harness receipt markers rejected.' };
  const payload = matches[0][1].trim();
  if (!payload || payload.length > 16_384 || !payload.startsWith('{')) return { ok: false, receipt: null, error: 'Malformed or empty harness receipt marker payload.' };
  const parsed = safeJsonParse(payload);
  if (!parsed.ok || !isPlainObj(parsed.value)) return { ok: false, receipt: null, error: parsed.error || 'Malformed receipt JSON.' };
  const { receiptDigest, ...core } = parsed.value;
  if (core.writtenBy !== 'harness') return { ok: false, receipt: null, error: 'Receipt writtenBy must be "harness".' };
  for (const k of REQUIRED_RECEIPT_STRINGS) if (!nonEmptyStr(core[k])) return { ok: false, receipt: null, error: `Receipt missing required field "${k}".` };
  if (!RECEIPT_OUTCOMES.has(core.outcome)) return { ok: false, receipt: null, error: 'Receipt has invalid outcome.' };
  if (core.capability !== null && !nonEmptyStr(core.capability)) return { ok: false, receipt: null, error: 'Receipt has invalid capability.' };
  if (requireKeyed || hmacKey) {
    if (core.digestAlg !== 'hmac-sha256') return { ok: false, receipt: null, error: 'Unkeyed receipt rejected (HMAC-SHA256 required).' };
    if (!hmacKey) return { ok: false, receipt: null, error: 'hmacKey required to verify keyed receipt.' };
    return hexEqual(receiptDigest, computeReceiptDigest(core, hmacKey)) ? { ok: true, receipt: parsed.value, error: null } : { ok: false, receipt: null, error: 'Harness receipt HMAC mismatch (tampered).' };
  }
  if (core.digestAlg === 'hmac-sha256') return { ok: false, receipt: null, error: 'Keyed harness receipt requires hmacKey for verification.' };
  if (core.digestAlg !== 'sha256') return { ok: false, receipt: null, error: 'Unsupported receipt digestAlg.' };
  return hexEqual(receiptDigest, computeReceiptDigest(core, null)) ? { ok: true, receipt: parsed.value, error: null } : { ok: false, receipt: null, error: 'Harness receipt digest mismatch (tampered).' };
}
