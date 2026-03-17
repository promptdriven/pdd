// Colors
export const COLORS = {
  background: '#0A0F1A',
  titleBar: '#1E293B',
  editorBg: '#0F172A',
  codeBlockBg: '#1A1F2E',
  lineNumber: '#64748B',
  naturalText: '#CBD5E1',
  codeText: '#94A3B8',
  titleText: '#4A90D9',
  intentLabel: '#4A90D9',
  codeLabel: '#94A3B8',
  annotationText: '#E2E8F0',
  codeBorder: '#94A3B8',
  ambientGlow: '#4A90D9',
} as const;

// Dimensions
export const CANVAS = { width: 1920, height: 1080 } as const;

export const EDITOR = {
  x: 360,
  y: 80,
  width: 1200,
  height: 800,
  titleBarHeight: 30,
  borderRadius: 8,
  gutterWidth: 40,
  lineHeight: 22,
  contentPaddingLeft: 50,
  contentPaddingTop: 48,
} as const;

// Fonts
export const FONTS = {
  mono: "'JetBrains Mono', 'Fira Code', 'Cascadia Code', 'Consolas', monospace",
  sans: "'Inter', -apple-system, 'Segoe UI', sans-serif",
} as const;

// Natural language lines (section 1: lines 1-8)
export const NATURAL_LINES_1 = [
  '# Ad Latency Optimizer',
  'Optimize bid calculation to meet sub-millisecond target.',
  'Accept bid request with up to 50 ad candidates.',
  'Score each candidate using CTR model output.',
  'Return top-k candidates sorted by expected value.',
  'Parallelism constraint: single-threaded hot path only.',
  'Memory budget: 64KB scratch space per request.',
  'Latency SLA: p99 < 800μs end-to-end.',
];

// Code block lines (section 2: lines 9-18)
export const CODE_LINES = [
  '```python',
  'def score_candidates(candidates, ctr_scores):',
  '    # Vectorized scoring — numpy required for latency',
  '    scores = np.multiply(ctr_scores, candidates.bids)',
  '    top_k_idx = np.argpartition(scores, -k)[-k:]',
  '    return candidates[top_k_idx[np.argsort(scores[top_k_idx])[::-1]]]',
  '',
  '    # Fallback: linear scan if k > len(candidates) // 2',
  '    # return sorted(candidates, key=lambda c: c.score, reverse=True)[:k]',
  '```',
];

// Natural language lines (section 3: lines 19-24)
export const NATURAL_LINES_2 = [
  'Handle edge case: empty candidate list returns empty array.',
  'Handle edge case: all scores equal — preserve original order.',
  'Return type: CandidateArray with .bids and .scores views.',
  'Caller expects numpy array, not Python list.',
  'Log p99 latency per request for monitoring dashboard.',
  'Flag requests exceeding 1ms for async investigation.',
];

// Animation timing (in frames, 30fps)
export const TIMING = {
  editorAppear: { start: 0, duration: 20 },
  naturalSection1: { start: 30, end: 120 },
  codeBlockBgSlide: { start: 120, duration: 15 },
  codeTyping: { start: 140, end: 240 },
  codeBlockClose: { start: 240, duration: 20 },
  naturalSection2: { start: 260, end: 340 },
  labelPulse: { start: 340, end: 420 },
  annotationFade: { start: 420, duration: 20 },
  total: 480,
} as const;

export const CHARS_PER_FRAME = 2;
