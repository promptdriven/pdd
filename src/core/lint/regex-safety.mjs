// ReDoS-safe regular expression validator and strictly linear DP glob matcher.
export const MAX_GLOB_WILDCARDS = 12;
const MAX_REGEX_GROUP_DEPTH = 16;
const MAX_BRANCH_UNBOUNDED_QUANTIFIERS = 3;

// Escapes whose decoded character can overlap ASCII literals or match character classes.
const NON_LITERAL_ESCAPES = new Set(['d', 'D', 'w', 'W', 's', 'S', 'p', 'P', 'x', 'u', 'c', '0']);
const CONTROL_ESCAPES = { t: '\t', n: '\n', r: '\r', f: '\f', v: '\v' };

function matchSegmentLinear(pattern, text) {
  let pi = 0;
  let ti = 0;
  let starIdx = -1;
  let matchIdx = 0;
  while (ti < text.length) {
    if (pi < pattern.length && (pattern[pi] === '?' || pattern[pi] === text[ti])) {
      pi++;
      ti++;
    } else if (pi < pattern.length && pattern[pi] === '*') {
      starIdx = pi++;
      matchIdx = ti;
    } else if (starIdx !== -1) {
      pi = starIdx + 1;
      ti = ++matchIdx;
    } else {
      return false;
    }
  }
  while (pi < pattern.length && pattern[pi] === '*') pi++;
  return pi === pattern.length;
}

/**
 * Strictly O(P * S) DP path glob matcher (zero regex compilation, zero glob ReDoS).
 */
export function matchGlobSegments(globSegs, pathSegs) {
  const m = globSegs.length;
  const n = pathSegs.length;
  let prev = new Uint8Array(n + 1);
  prev[0] = 1;
  for (let i = 1; i <= m; i++) {
    const g = globSegs[i - 1];
    const curr = new Uint8Array(n + 1);
    if (g === '**') {
      curr[0] = prev[0];
      for (let j = 1; j <= n; j++) {
        curr[j] = prev[j] || curr[j - 1] ? 1 : 0;
      }
    } else {
      for (let j = 1; j <= n; j++) {
        if (prev[j - 1] && matchSegmentLinear(g, pathSegs[j - 1])) curr[j] = 1;
      }
    }
    prev = curr;
  }
  return prev[n] === 1;
}

export function normalizeGlob(glob) {
  const clean = String(glob ?? '')
    .trim()
    .replace(/\\/g, '/')
    .replace(/^\.\//, '')
    .replace(/\/+/g, '/')
    .replace(/^\/+|\/+$/g, '');
  if (!clean || clean.length > 256) return null;
  const rawSegments = clean.split('/');
  const segments = [];
  for (const rawSeg of rawSegments) {
    const collapsed = /^\*+$/.test(rawSeg)
      ? (rawSeg.length >= 2 ? '**' : '*')
      : rawSeg.replace(/\*+/g, '*');
    if (collapsed === '**' && segments.at(-1) === '**') continue;
    segments.push(collapsed);
  }
  let wildcardCount = 0;
  for (const seg of segments) {
    if (seg === '**') wildcardCount += 1;
    else {
      for (let i = 0; i < seg.length; i++) {
        if (seg[i] === '*' || seg[i] === '?') wildcardCount += 1;
      }
    }
  }
  if (wildcardCount > MAX_GLOB_WILDCARDS) return null;
  return { clean, segments };
}

export function compileGlobMatcher(glob) {
  const parsed = normalizeGlob(glob);
  if (!parsed) return null;
  const { clean, segments } = parsed;
  return {
    raw: clean,
    segments,
    test(candidatePath) {
      if (typeof candidatePath !== 'string' || !candidatePath) return false;
      const norm = candidatePath
        .replace(/\\/g, '/')
        .replace(/^\.\//, '')
        .replace(/\/+/g, '/')
        .replace(/^\/+|\/+$/g, '');
      if (!norm) return false;
      return matchGlobSegments(segments, norm.split('/'));
    },
  };
}

function readRegexQuantifier(pattern, pos) {
  if (pos >= pattern.length) return null;
  const ch = pattern[pos];
  if (ch === '*' || ch === '+') {
    const lazy = pattern[pos + 1] === '?' ? 1 : 0;
    return { len: 1 + lazy, unbounded: true, repeats: true, nullable: ch === '*' };
  }
  if (ch === '?') {
    const lazy = pattern[pos + 1] === '?' ? 1 : 0;
    return { len: 1 + lazy, unbounded: false, repeats: false, nullable: true };
  }
  if (ch === '{') {
    const m = /^\{(\d+)(?:,(\d*))?\}(\?)?/.exec(pattern.slice(pos));
    if (!m) return null;
    const min = Number(m[1]);
    const hasComma = m[2] !== undefined;
    const max = hasComma ? (m[2] === '' ? Infinity : Number(m[2])) : min;
    if (max < min) return null;
    return { len: m[0].length, unbounded: max === Infinity, repeats: max > 1, nullable: min === 0 };
  }
  return null;
}

function makeBranch() {
  return { firstChar: null, pureLiteralPrefix: true, len: 0, prevUnbounded: false, unboundedCount: 0 };
}

export function isSafeRegexPattern(pattern, cleanFlags = '') {
  const ignoreCase = cleanFlags.includes('i');
  const unicodeIgnoreCase = ignoreCase && cleanFlags.includes('u');
  const normChar = ch => (ignoreCase ? ch.toLowerCase() : ch);
  // Root frame tracks top-level chained/adjacent unbounded quantifiers and nested alternations cleanly.
  const stack = [{ kind: 'root', hasInnerQuantifier: false, hasUnboundedQuantifier: false, hasAlternation: false, hasAmbiguousAlternation: false, branches: [makeBranch()] }];

  const currentBranch = () => stack.at(-1).branches.at(-1);

  const recordAtom = (literalChar, quant) => {
    const top = stack.at(-1);
    const branch = currentBranch();
    if (branch.len === 0) {
      if (literalChar !== null && branch.pureLiteralPrefix) branch.firstChar = normChar(literalChar);
      else branch.pureLiteralPrefix = false;
    }
    branch.len += 1;
    if (quant) {
      top.hasInnerQuantifier = true;
      if (quant.unbounded) {
        top.hasUnboundedQuantifier = true;
        if (branch.prevUnbounded) return false;
        branch.unboundedCount += 1;
        if (branch.unboundedCount > MAX_BRANCH_UNBOUNDED_QUANTIFIERS) return false;
        branch.prevUnbounded = true;
      } else if (!quant.nullable) {
        branch.prevUnbounded = false;
      }
    } else {
      branch.prevUnbounded = false;
    }
    return true;
  };

  let inCharClass = false;
  let i = 0;
  while (i < pattern.length) {
    const ch = pattern[i];
    if (inCharClass) {
      if (ch === '\\') { i += 2; continue; }
      if (ch === ']') {
        inCharClass = false;
        i += 1;
        const q = readRegexQuantifier(pattern, i);
        if (q) i += q.len;
        if (!recordAtom(null, q)) return false;
        continue;
      }
      i += 1;
      continue;
    }

    if (ch === '\\') {
      const esc = pattern[i + 1];
      if (!esc) return false;
      if (/^[1-9]$/.test(esc) || esc === 'k') return false;
      let step = 2;
      if ((esc === 'p' || esc === 'P' || esc === 'u') && pattern[i + 2] === '{') {
        const close = pattern.indexOf('}', i + 3);
        if (close < 0) return false;
        step = close - i + 1;
      } else if (esc === 'x') {
        if (/^[0-9a-fA-F]{2}/.test(pattern.slice(i + 2, i + 4))) step = 4;
      } else if (esc === 'u') {
        if (/^[0-9a-fA-F]{4}/.test(pattern.slice(i + 2, i + 6))) step = 6;
      } else if (esc === 'c') {
        if (i + 2 < pattern.length) step = 3;
      }
      if (esc === 'b' || esc === 'B') {
        i += step;
        continue;
      }
      i += step;
      const q = readRegexQuantifier(pattern, i);
      if (q) i += q.len;
      const lit = NON_LITERAL_ESCAPES.has(esc) ? null : (CONTROL_ESCAPES[esc] ?? esc);
      if (!recordAtom(lit, q)) return false;
      continue;
    }

    if (ch === '[') {
      inCharClass = true;
      i += 1;
      continue;
    }

    if (ch === '(') {
      if (stack.length > MAX_REGEX_GROUP_DEPTH) return false;
      let kind = 'normal';
      let step = 1;
      if (pattern[i + 1] === '?') {
        const rest = pattern.slice(i + 2);
        if (rest.startsWith(':')) step = 3;
        else if (rest.startsWith('=') || rest.startsWith('!')) { kind = 'lookaround'; step = 3; }
        else if (rest.startsWith('<=') || rest.startsWith('<!')) { kind = 'lookaround'; step = 4; }
        else if (rest.startsWith('<')) {
          const close = rest.indexOf('>');
          if (close <= 1) return false;
          step = 2 + close + 1;
        } else {
          return false;
        }
      }
      stack.push({ kind, hasInnerQuantifier: false, hasUnboundedQuantifier: false, hasAlternation: false, hasAmbiguousAlternation: false, branches: [makeBranch()] });
      i += step;
      continue;
    }

    if (ch === '|') {
      stack.at(-1).branches.push(makeBranch());
      i += 1;
      continue;
    }

    if (ch === ')') {
      if (stack.length <= 1) return false;
      const frame = stack.pop();
      if (frame.kind === 'lookaround' && frame.hasUnboundedQuantifier) return false;
      i += 1;
      const groupHasAlt = frame.branches.length > 1 || frame.hasAlternation;
      let ambiguousAlt = frame.hasAmbiguousAlternation;
      if (frame.branches.length > 1) {
        // Under /iu Unicode case folding, mark alternations ambiguous unconditionally (e.g. (?:(?:s|ſ))+$/iu).
        if (unicodeIgnoreCase) {
          ambiguousAlt = true;
        } else {
          const starts = [];
          for (const br of frame.branches) {
            if (br.len === 0 || !br.pureLiteralPrefix || br.firstChar === null) { ambiguousAlt = true; break; }
            starts.push(br.firstChar);
          }
          if (!ambiguousAlt && new Set(starts).size !== frame.branches.length) ambiguousAlt = true;
        }
      }
      const q = readRegexQuantifier(pattern, i);
      if (q) {
        if (frame.kind === 'lookaround') return false;
        if (frame.hasInnerQuantifier) return false;
        if (q.repeats && (ambiguousAlt || (unicodeIgnoreCase && groupHasAlt))) return false;
        i += q.len;
      }
      if (frame.kind === 'normal') {
        const effectiveQuant = q ?? (frame.hasUnboundedQuantifier ? { unbounded: true, repeats: true, nullable: false } : null);
        if (!recordAtom(null, effectiveQuant)) return false;
        if (frame.hasInnerQuantifier) stack.at(-1).hasInnerQuantifier = true;
        if (frame.hasUnboundedQuantifier) stack.at(-1).hasUnboundedQuantifier = true;
        if (groupHasAlt) stack.at(-1).hasAlternation = true;
        if (ambiguousAlt) stack.at(-1).hasAmbiguousAlternation = true;
      }
      continue;
    }

    if (ch === '^' || ch === '$') {
      i += 1;
      continue;
    }

    const strayQuant = readRegexQuantifier(pattern, i);
    if (strayQuant) return false;

    i += 1;
    const q = readRegexQuantifier(pattern, i);
    if (q) i += q.len;
    if (!recordAtom(ch === '.' ? null : ch, q)) return false;
  }

  return !inCharClass && stack.length === 1;
}

export function parseRegexSafe(pattern, flags = '') {
  if (typeof pattern !== 'string' || !pattern.length || pattern.length > 512) return null;
  if (typeof flags !== 'string' || flags.length > 8) return null;
  const cleanFlags = [...new Set(flags.replace(/[gy]/g, '').split(''))].join('');
  if (!/^[imsu]*$/.test(cleanFlags)) return null;
  if (!isSafeRegexPattern(pattern, cleanFlags)) return null;
  try {
    return new RegExp(pattern, cleanFlags);
  } catch {
    return null;
  }
}
