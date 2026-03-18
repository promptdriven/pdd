// ─── Colors ───────────────────────────────────────────────────────────────────
export const COLORS = {
  background: '#0A0F1A',
  noiseTexture: '#1E293B',
  quoteText: '#E2E8F0',
  highlightBlue: '#4A90D9',
  highlightAmber: '#D9944A',
  attribution: '#64748B',
  reframeText: '#CBD5E1',
  decorativeQuote: '#334155',
  ruleLine: '#334155',
} as const;

// ─── Dimensions ───────────────────────────────────────────────────────────────
export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

// ─── Quote Data ───────────────────────────────────────────────────────────────
export const QUOTE_TEXT =
  "This is either the way of the future or it's going to crash and burn spectacularly.";

export const ATTRIBUTION_TEXT =
  '— Research engineer, after seeing PDD for the first time';

export const REFRAME_TEXT =
  "He's right — it's a contrarian bet. But the economics are on our side.";

// ─── Highlighted Phrases ──────────────────────────────────────────────────────
export interface HighlightedPhrase {
  text: string;
  color: string;
  weight?: number;
  italic?: boolean;
  opacity?: number;
  glowBlur?: number;
  glowOpacity?: number;
}

export const HIGHLIGHTED_PHRASES: HighlightedPhrase[] = [
  {
    text: 'the way of the future',
    color: COLORS.highlightBlue,
    weight: 600,
    glowBlur: 4,
    glowOpacity: 0.15,
  },
  {
    text: 'crash and burn',
    color: COLORS.highlightAmber,
    weight: 600,
    glowBlur: 4,
    glowOpacity: 0.15,
  },
  {
    text: 'spectacularly',
    color: COLORS.highlightAmber,
    opacity: 0.8,
    italic: true,
    glowBlur: 4,
    glowOpacity: 0.15,
  },
];

// ─── Animation Timing (frames) ───────────────────────────────────────────────
export const TIMING = {
  // Background + quote mark fade in
  bgFadeStart: 0,
  bgFadeDuration: 15,
  quoteMarkStart: 0,
  quoteMarkFadeDuration: 15,

  // Word-by-word typing
  wordTypingStart: 20,
  framesPerWord: 4,
  wordFadeDuration: 4,

  // Color highlights
  highlightStart: 90,
  highlightTransitionDuration: 20,

  // Attribution
  attributionStart: 120,
  attributionFadeDuration: 15,

  // Narrator reframe
  reframeStart: 210,
  reframeSlideDistance: 15,
  reframeSlideDuration: 20,
  ruleDrawDuration: 10,

  // Economics pulse
  economicsPulseStart: 260, // absolute frame
  economicsPulseDuration: 20,
  economicsPulseScale: 1.08,

  // Total
  totalFrames: 300,
} as const;
