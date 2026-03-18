// ── Colors ──
export const BG_BLACK = '#000000';
export const BG_LEFT_PANEL = '#0F172A';
export const BG_RIGHT_PANEL = '#0A0F1A';
export const SPLIT_LINE_COLOR = '#334155';

export const RED = '#EF4444';
export const GREEN = '#5AAA6E';
export const AMBER = '#D9944A';
export const TEXT_PRIMARY = '#E2E8F0';
export const TEXT_SECONDARY = '#94A3B8';
export const TEXT_MUTED = '#64748B';

// ── Dimensions ──
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const SPLIT_X = 960;
export const PANEL_WIDTH = 958;
export const ROW_HEIGHT = 60;
export const HEADER_Y = 40;

// ── Timeline bar ──
export const TIMELINE_Y = 820;
export const TIMELINE_HEIGHT = 100;
export const TIMELINE_MARGIN_X = 60;

// ── Callout ──
export const CALLOUT_Y = 970;

// ── Traditional rows data ──
export const TRADITIONAL_ROWS = [
  { bug: 'Bug found: null crash', action: 'Patch: add null check' },
  { bug: 'Same bug: different module', action: 'Patch: add null check' },
  { bug: 'New bug: unicode failure', action: 'Patch: encode input' },
  { bug: 'Regression: null check broke edge case', action: 'Patch: add condition' },
  { bug: 'Performance bug: O(n²)', action: 'Patch: optimize loop' },
  { bug: 'Another null crash: API layer', action: 'Patch: add null check' },
  { bug: 'Encoding bug: API response', action: 'Patch: decode output' },
  { bug: 'Null again: third module', action: 'Patch: add null check' },
  { bug: 'Type coercion bug', action: 'Patch: add cast' },
  { bug: 'Race condition found', action: 'Patch: add mutex' },
];

// ── PDD rows data ──
export const PDD_ROWS = [
  { text: 'Bug found: null crash', icon: 'alert' as const },
  { text: 'pdd bug user_parser', icon: 'wall' as const },
  { text: 'pdd fix user_parser → All tests pass ✓', icon: 'check' as const },
];

// ── Animation frames ──
export const FRAME = {
  SPLIT_DRAW_START: 0,
  SPLIT_DRAW_DUR: 15,
  HEADERS_START: 0,
  HEADERS_DUR: 20,
  // Left row appearances: staggered from frame 20
  LEFT_ROW_START: 20,
  LEFT_ROW_STAGGER: 20,
  // Right row appearances: staggered from frame 20
  RIGHT_ROW_1_START: 20,
  RIGHT_ROW_2_START: 60,
  RIGHT_ROW_3_START: 120,
  // PDD extras
  PDD_SUBTITLE_START: 150,
  PDD_MOLD_START: 200,
  // Left auto-scroll starts
  LEFT_SCROLL_START: 200,
  // Timeline
  TIMELINE_START: 280,
  TIMELINE_DRAW_DUR: 60,
  // Callout
  CALLOUT_START: 380,
  CALLOUT_DUR: 20,
  // Total
  TOTAL: 480,
} as const;

// ── Ratchet steps for the staircase ──
export const RATCHET_STEPS = 6;
