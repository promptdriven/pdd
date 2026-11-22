// Layer-2 strict JSON schemas, CLI native schema flags, fence-hardened dual-read parser, and harness PR receipt stamper.
import { createHash } from 'node:crypto';
import { redactSecrets } from '../../secret-redaction.mjs';
import { writeAtomicPrivate } from '../../shared/atomic-fs.mjs';

const strArr = (maxItems, extra = {}) => ({ type: 'array', items: { type: 'string', ...extra }, maxItems });
const strictObj = (required, properties) => Object.freeze({ type: 'object', additionalProperties: false, required, properties });

export const buildResultSchema = strictObj(
  ['status', 'summary', 'changedPaths', 'testCommands', 'promptChanged', 'notes'],
  {
    status: { type: 'string', enum: ['ready', 'blocked', 'needs-decision'] },
    summary: { type: 'string', maxLength: 2000 },
    changedPaths: strArr(200),
    testCommands: strArr(50),
    promptChanged: { type: 'boolean' },
    notes: { type: 'string', maxLength: 4000 },
  },
);

export const reviewResultSchema = strictObj(
  ['verdict', 'mustFix', 'followUps', 'preExisting', 'summary'],
  {
    verdict: { type: 'string', enum: ['PASS', 'FAIL'] },
    mustFix: strArr(50),
    followUps: strArr(50),
    preExisting: strArr(50),
    summary: { type: 'string', maxLength: 2000 },
  },
);

export const gapCheckSchema = strictObj(
  ['missingPathIds', 'unprovedAcIds', 'flags'],
  {
    missingPathIds: strArr(100),
    unprovedAcIds: strArr(100),
    flags: strArr(2, { enum: ['UNMAPPED_CHANGE', 'INSUFFICIENT_SCOPE'] }),
  },
);

export const intakeCardSchema = strictObj(
  ['decision', 'summary', 'acceptanceCriteria', 'touchedPaths', 'requiredCapabilities', 'questions'],
  {
    decision: { type: 'string', enum: ['ready', 'needs-clarification', 'skip'] },
    summary: { type: 'string', maxLength: 2000 },
    acceptanceCriteria: strArr(50),
    touchedPaths: strArr(100),
    requiredCapabilities: strArr(30),
    questions: strArr(10),
  },
);

export const TYPED_SCHEMAS = Object.freeze({
  build: buildResultSchema,
  review: reviewResultSchema,
  'gap-check': gapCheckSchema,
  intake: intakeCardSchema,
});

const FORBIDDEN_KEYS = new Set(['__proto__', 'constructor', 'prototype', 'confidence', 'score', 'probability', 'certainty', 'confidenceScore']);
const BIDI_AND_ZW_RE = /[\uFEFF\u061C\u200B-\u200F\u202A-\u202E\u2060\u2066-\u2069]/g;
const CTRL_RE = /[\x00-\x08\x0B\x0C\x0E-\x1F\x7F-\x9F]/g;
const isPlainObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);

/** Hardening 1: Linear O(N) ANSI CSI/OSC, C0/C1 control, BOM, zero-width, and bidi override sanitizer. */
export function sanitizeUntrustedText(raw) {
  const s = String(raw ?? '');
  let out = '';
  for (let i = 0; i < s.length; i += 1) {
    if (s.charCodeAt(i) === 0x1b) {
      const nx = s[i + 1];
      if (nx === '[') { i += 2; while (i < s.length && (s.charCodeAt(i) < 0x40 || s.charCodeAt(i) > 0x7e)) i += 1; continue; }
      if (nx === ']') { i += 2; while (i < s.length && s.charCodeAt(i) !== 0x07 && !(s.charCodeAt(i) === 0x1b && s[i + 1] === '\\')) i += 1; if (s.charCodeAt(i) === 0x1b && s[i + 1] === '\\') i += 1; continue; }
      continue;
    }
    out += s[i];
  }
  return out.replace(BIDI_AND_ZW_RE, '').replace(CTRL_RE, '');
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
        top.keys.add(key);
        top.expectKey = false;
      }
      i = j;
    }
  }
  return { hasDuplicate: false, duplicateKey: null };
}

/** Hardening 5: Safe JSON parse rejecting duplicate keys, prototype pollution, and forbidden numeric score keys. */
export function safeJsonParse(raw, { maxBytes = 262_144, maxDepth = 16 } = {}) {
  const text = String(raw ?? '').replace(/^\uFEFF/, '').trim();
  const bounds = enforceSizeAndDepthBounds(text, { maxBytes, maxDepth });
  if (!bounds.ok) return { ok: false, value: null, error: bounds.error };
  const dup = detectDuplicateJsonKeys(text);
  if (dup.hasDuplicate) return { ok: false, value: null, error: `Duplicate JSON key "${dup.duplicateKey}" rejected.` };
  let parsed;
  try { parsed = JSON.parse(text); } catch (err) { return { ok: false, value: null, error: err?.message ?? 'Invalid JSON.' }; }
  const walk = (node, depth) => {
    if (depth > maxDepth) return 'Max object depth exceeded.';
    if (Array.isArray(node)) { for (const item of node) { const e = walk(item, depth + 1); if (e) return e; } return null; }
    if (isPlainObj(node)) {
      for (const k of Object.keys(node)) {
        if (FORBIDDEN_KEYS.has(k) || BIDI_AND_ZW_RE.test(k) || CTRL_RE.test(k)) return `Forbidden or unsafe key "${k}" rejected.`;
        const e = walk(node[k], depth + 1); if (e) return e;
      }
    }
    return null;
  };
  const err = walk(parsed, 0);
  return err ? { ok: false, value: null, error: err } : { ok: true, value: parsed, error: null };
}

/** Hardening 6: Strip HTML comments, Markdown blockquotes, and unified diff lines before legacy fence scanning. */
export function stripInjectionContainers(raw) {
  return sanitizeUntrustedText(raw)
    .replace(/<!--[\s\S]*?-->/g, '')
    .split(/\r?\n/)
    .filter((line) => !/^\s*>/.test(line) && !/^[+-](?![+-]{2})/.test(line))
    .join('\n');
}

/** Hardening 7: Extract strictly closed JSON fences and detect unclosed/truncated fence attacks. */
export function extractClosedJsonFences(raw) {
  const blocks = [];
  let active = null;
  for (const line of String(raw ?? '').split(/\r?\n/)) {
    if (active) {
      const close = /^ {0,3}(`{3,}|~{3,})[ \t]*$/.exec(line);
      if (close && close[1][0] === active.ch && close[1].length >= active.len) {
        if (active.lang === 'json' || active.lang === '') blocks.push(active.lines.join('\n').trim());
        active = null;
      } else active.lines.push(line);
      continue;
    }
    const open = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(line);
    if (open && !(open[1][0] === '`' && open[2].includes('`'))) {
      active = { ch: open[1][0], len: open[1].length, lang: (open[2].trim().split(/[\s{`~]/)[0] ?? '').toLowerCase(), lines: [] };
    }
  }
  return { blocks, unclosedFence: Boolean(active) };
}

/** Hardening 8: Detect conflicting verdict/decision/status across multiple candidate objects. */
export function detectConflictingVerdicts(candidates) {
  if (!Array.isArray(candidates) || candidates.length < 2) return false;
  return new Set(candidates.map((c) => JSON.stringify([c?.verdict ?? null, c?.decision ?? null, c?.status ?? null, c?.flags ?? null]))).size > 1;
}

/** Hardening 9: Strict schema validator (additionalProperties: false, closed enums, bounds). */
export function validateAgainstSchema(value, schema) {
  if (!isPlainObj(schema)) return { ok: false, error: 'Missing schema definition.' };
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

/** Hardening 10: Unwrap Claude/Codex structured envelopes while failing closed on terminal error frames. */
export function unwrapStructuredEnvelope(parsed) {
  if (!isPlainObj(parsed)) return { ok: false, value: null, error: 'Expected JSON object envelope.' };
  if (parsed.is_error === true || parsed.type === 'error' || parsed.type === 'turn.failed') {
    return { ok: false, value: null, error: 'Terminal error envelope rejected.' };
  }
  if (isPlainObj(parsed.structured_output)) return { ok: true, value: parsed.structured_output, error: null };
  if (typeof parsed.result === 'string' && parsed.result.trim().startsWith('{')) {
    const inner = safeJsonParse(parsed.result);
    return inner.ok ? { ok: true, value: inner.value, error: null } : { ok: false, value: null, error: inner.error };
  }
  return { ok: true, value: parsed, error: null };
}

/** CLI native schema flag builders (`codex exec --output-schema`, `claude -p --json-schema`). */
export function buildCodexSchemaArgs({ schemaPath, schema = null, fs = null } = {}) {
  if (typeof schemaPath !== 'string' || !schemaPath.trim()) throw new Error('codex --output-schema requires a non-empty schemaPath.');
  if (schema !== null) writeAtomicPrivate(fs, schemaPath, `${JSON.stringify(schema, null, 2)}\n`, 0o700, 0o600);
  return ['--output-schema', schemaPath];
}

export function buildClaudeSchemaArgs({ schema } = {}) {
  if (!isPlainObj(schema)) throw new Error('claude --json-schema requires a schema object.');
  return ['--json-schema', JSON.stringify(schema)];
}

export function buildNativeSchemaArgs({ agentKind = '', schema, schemaPath = '', fs = null } = {}) {
  const kind = String(agentKind ?? '').trim().toLowerCase();
  if (kind === 'codex') return buildCodexSchemaArgs({ schemaPath, schema, fs });
  if (kind === 'claude') return buildClaudeSchemaArgs({ schema });
  return [];
}

/** Dual-read parser: prefers strict typed JSON schema output, cleanly falls back to legacy fenced/structured text. */
export function parseTypedOrLegacyOutput(raw, { schemaName = null, schema = null, legacyParser = null, maxBytes = 262_144, maxDepth = 16 } = {}) {
  const targetSchema = schema ?? (schemaName ? TYPED_SCHEMAS[schemaName] : null);
  const fail = (source, error) => ({ ok: false, source, value: null, reason: 'malformed_output', error });
  if (!targetSchema) return fail('none', 'Unknown schema.');
  const text = String(raw ?? '').replace(/^\uFEFF/, '');
  const bounds = enforceSizeAndDepthBounds(text, { maxBytes, maxDepth });
  if (!bounds.ok) return fail('none', bounds.error);

  const trimmed = text.trim();
  if (trimmed.startsWith('{')) {
    const parsed = safeJsonParse(trimmed, { maxBytes, maxDepth });
    if (!parsed.ok) return fail('typed-json', parsed.error);
    const env = unwrapStructuredEnvelope(parsed.value);
    if (!env.ok) return fail('typed-json', env.error);
    const valid = validateAgainstSchema(env.value, targetSchema);
    return valid.ok ? { ok: true, source: 'typed-json', value: env.value, reason: null, error: null } : fail('typed-json', valid.error);
  }

  const stripped = stripInjectionContainers(text);
  const { blocks, unclosedFence } = extractClosedJsonFences(stripped);
  if (unclosedFence) return fail('legacy-fallback', 'Unclosed fenced block rejected.');
  const parsedCandidates = [];
  for (const block of blocks) {
    if (!block.startsWith('{')) continue;
    const p = safeJsonParse(block, { maxBytes, maxDepth });
    if (!p.ok) return fail('legacy-fallback', p.error);
    if (validateAgainstSchema(p.value, targetSchema).ok) parsedCandidates.push(p.value);
  }
  if (detectConflictingVerdicts(parsedCandidates)) return fail('legacy-fallback', 'Conflicting JSON verdicts detected in fenced output.');
  if (parsedCandidates.length > 0) return { ok: true, source: 'legacy-fallback', value: parsedCandidates.at(-1), reason: null, error: null };
  if (typeof legacyParser === 'function') {
    const legacyVal = legacyParser(stripped);
    if (legacyVal !== null && legacyVal !== undefined) {
      const v = validateAgainstSchema(legacyVal, targetSchema);
      return v.ok ? { ok: true, source: 'legacy-fallback', value: legacyVal, reason: null, error: null } : fail('legacy-fallback', v.error);
    }
  }
  return fail('none', 'No valid typed JSON or legacy structured output found.');
}

const canonicalPayload = (obj) => Object.fromEntries(Object.keys(obj).sort().filter((k) => obj[k] !== undefined).map((k) => [k, obj[k]]));

/** Deterministic harness PR receipt stamper bound to sourceTreeSha, policyDigest, and recipeDigest. */
export function formatHarnessPrReceipt({
  repo = '', candidateHead = '', sourceTreeSha = '', policyDigest = '', recipeDigest = '',
  acRevision = '', targetTip = '', outcome = 'proved', testProfile = 'default', artifactDigest = '',
} = {}) {
  for (const [k, v] of [['sourceTreeSha', sourceTreeSha], ['policyDigest', policyDigest], ['recipeDigest', recipeDigest]]) {
    if (typeof v !== 'string' || !v.trim()) throw new Error(`formatHarnessPrReceipt requires non-empty ${k}.`);
  }
  const core = canonicalPayload({
    repo: sanitizeUntrustedText(repo).trim(), acRevision: sanitizeUntrustedText(acRevision).trim(),
    targetTip: sanitizeUntrustedText(targetTip).trim(), candidateHead: sanitizeUntrustedText(candidateHead).trim(),
    sourceTreeSha: sanitizeUntrustedText(sourceTreeSha).trim(), policyDigest: sanitizeUntrustedText(policyDigest).trim(),
    recipeDigest: sanitizeUntrustedText(recipeDigest).trim(), testProfile: sanitizeUntrustedText(testProfile).trim() || 'default',
    outcome: sanitizeUntrustedText(outcome).trim() || 'proved', artifactDigest: sanitizeUntrustedText(artifactDigest).trim(),
  });
  const receiptDigest = createHash('sha256').update(JSON.stringify(core)).digest('hex');
  const stamped = canonicalPayload({ ...core, receiptDigest });
  const marker = `<!-- pdd:harness-receipt:v1 ${JSON.stringify(stamped)} -->`;
  const summary = `Harness Receipt: outcome=${core.outcome}; sourceTreeSha=${core.sourceTreeSha}; policyDigest=${core.policyDigest}; recipeDigest=${core.recipeDigest}; receiptDigest=${receiptDigest.slice(0, 16)}`;
  return redactSecrets(`${marker}\n${summary}`);
}

export function parseHarnessPrReceipt(text) {
  const m = /<!-- pdd:harness-receipt:v1 (\{[^\r\n]{2,16000}\}) -->/.exec(String(text ?? ''));
  if (!m) return { ok: false, receipt: null, error: 'Harness receipt marker not found.' };
  const parsed = safeJsonParse(m[1]);
  if (!parsed.ok || !isPlainObj(parsed.value)) return { ok: false, receipt: null, error: parsed.error || 'Malformed receipt JSON.' };
  const { receiptDigest, ...core } = parsed.value;
  if (typeof receiptDigest !== 'string' || !/^[a-f0-9]{64}$/.test(receiptDigest)) return { ok: false, receipt: null, error: 'Invalid receiptDigest.' };
  const expected = createHash('sha256').update(JSON.stringify(canonicalPayload(core))).digest('hex');
  return receiptDigest === expected ? { ok: true, receipt: parsed.value, error: null } : { ok: false, receipt: null, error: 'Harness receipt digest mismatch (tampered).' };
}
