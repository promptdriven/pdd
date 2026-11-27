// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Strictly linear O(P * S) DP path glob matcher (zero regex compilation, zero glob ReDoS).
export const MAX_GLOB_WILDCARDS = 12;

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
