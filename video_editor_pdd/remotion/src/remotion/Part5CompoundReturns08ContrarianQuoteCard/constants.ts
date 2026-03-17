// Part5CompoundReturns08ContrarianQuoteCard – constants

export const COLORS = {
  background: "#0A0F1A",
  noiseTexture: "#1E293B",
  quoteText: "#E2E8F0",
  blueHighlight: "#4A90D9",
  amberHighlight: "#D9944A",
  attribution: "#64748B",
  reframeText: "#CBD5E1",
  decorativeQuote: "#334155",
  ruleLine: "#334155",
} as const;

export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const QUOTE_TEXT =
  "This is either the way of the future or it's going to crash and burn spectacularly.";

export const ATTRIBUTION_TEXT =
  "— Research engineer, after seeing PDD for the first time";

export const REFRAME_TEXT =
  "He's right — it's a contrarian bet. But the economics are on our side.";

export const HIGHLIGHT_PHRASES = [
  { text: "the way of the future", color: COLORS.blueHighlight },
  { text: "crash and burn", color: COLORS.amberHighlight },
  { text: "spectacularly.", color: COLORS.amberHighlight, italic: true, dimmed: true },
] as const;

// Animation frame markers
export const FRAMES = {
  bgFadeEnd: 20,
  quoteStart: 20,
  wordsPerFrame: 4, // frames per word reveal
  highlightStart: 90,
  highlightDuration: 20,
  attributionStart: 120,
  attributionFadeDuration: 15,
  reframeStart: 210,
  reframeSlideFrames: 20,
  economicsPulseStart: 260, // absolute
  economicsPulseDuration: 20,
  total: 300,
} as const;
