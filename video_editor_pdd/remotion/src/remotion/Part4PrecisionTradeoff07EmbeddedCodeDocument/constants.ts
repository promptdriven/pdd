// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 480;

// Background
export const BG_COLOR = "#0A0F1A";

// Editor window
export const EDITOR_X = 360;
export const EDITOR_Y = 80;
export const EDITOR_WIDTH = 1200;
export const EDITOR_HEIGHT = 800;
export const TITLE_BAR_HEIGHT = 30;
export const TITLE_BAR_COLOR = "#1E293B";
export const EDITOR_BG = "#0F172A";
export const LINE_NUMBER_COLOR = "#64748B";
export const LINE_GUTTER_WIDTH = 40;
export const FILENAME = "ad_latency_optimizer.prompt";

// Code block
export const CODE_BLOCK_BG = "#1A1F2E";
export const CODE_BORDER_COLOR = "#94A3B8";
export const CODE_BORDER_OPACITY = 0.3;
export const CODE_BORDER_WIDTH = 3;

// Colors
export const NL_TEXT_COLOR = "#CBD5E1";
export const NL_GLOW_COLOR = "#4A90D9";
export const CODE_TEXT_COLOR = "#94A3B8";
export const TITLE_TEXT_COLOR = "#4A90D9";
export const LABEL_NL_COLOR = "#4A90D9";
export const LABEL_CODE_COLOR = "#94A3B8";
export const ANNOTATION_TEXT_COLOR = "#E2E8F0";

// Typography
export const FONT_MONO = "JetBrains Mono, Fira Code, Consolas, monospace";
export const FONT_SANS = "Inter, system-ui, sans-serif";

// Line content
export const NATURAL_LANGUAGE_1 = [
  "# Ad Latency Optimizer",
  "Optimize bid calculation to meet sub-millisecond target.",
  "Accept bid request with up to 50 ad candidates.",
  "Score each candidate using CTR model output.",
  "Return top-k candidates sorted by expected value.",
  "Latency budget: 800μs total, 200μs for scoring.",
  "Must handle variable candidate counts gracefully.",
  "Fall back to pre-computed rankings if budget exceeded.",
];

export const CODE_LINES = [
  "```python",
  "def score_candidates(candidates, ctr_scores):",
  "    # Vectorized scoring — numpy required for latency",
  "    scores = np.multiply(ctr_scores, candidates.bids)",
  "    top_k_idx = np.argpartition(scores, -k)[-k:]",
  "    return candidates[top_k_idx[np.argsort(scores[top_k_idx])[::-1]]]",
  "    # Fallback: if len(candidates) < k, return all sorted",
  "    if len(candidates) <= k:",
  "        return sorted(candidates, key=lambda c: c.score, reverse=True)",
  "```",
];

export const NATURAL_LANGUAGE_2 = [
  "Handle edge case: empty candidate list returns empty array.",
  "Type: List[AdCandidate] → List[AdCandidate]",
  "Preserve candidate metadata through scoring pipeline.",
  "Log latency percentiles for monitoring.",
  "Alert if p99 latency exceeds 1ms.",
  "Cache model weights across requests within same session.",
];

// Animation timing (frames)
export const EDITOR_APPEAR_START = 0;
export const EDITOR_APPEAR_END = 30;
export const NL1_TYPE_START = 30;
export const NL1_TYPE_END = 120;
export const CODE_BG_START = 120;
export const CODE_BG_END = 140;
export const CODE_TYPE_START = 140;
export const CODE_TYPE_END = 240;
export const NL2_TYPE_START = 260;
export const NL2_TYPE_END = 340;
export const LABELS_PULSE_START = 340;
export const LABELS_PULSE_END = 420;
export const ANNOTATION_START = 420;
export const ANNOTATION_END = 480;

// Label positions
export const LABEL_X = 1400;
export const LINE_HEIGHT = 22;
export const CONTENT_START_Y = 50; // relative to editor content area
