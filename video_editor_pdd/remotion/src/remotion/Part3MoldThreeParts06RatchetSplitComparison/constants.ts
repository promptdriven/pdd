// constants.ts — Colors, dimensions, and data for Ratchet Split Comparison

export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 480;

// Layout
export const SPLIT_X = 960;
export const LEFT_PANEL_WIDTH = 958;
export const RIGHT_PANEL_X = 962;
export const RIGHT_PANEL_WIDTH = 958;

// Colors
export const BG_COLOR = '#000000';
export const LEFT_BG = '#0F172A';
export const RIGHT_BG = '#0A0F1A';
export const SPLIT_LINE_COLOR = '#334155';
export const RED = '#EF4444';
export const GREEN = '#5AAA6E';
export const AMBER = '#D9944A';
export const TEXT_PRIMARY = '#94A3B8';
export const TEXT_SECONDARY = '#64748B';
export const TEXT_LIGHT = '#E2E8F0';

// Typography
export const FONT_MONO = 'JetBrains Mono, monospace';
export const FONT_SANS = 'Inter, sans-serif';

// Row config
export const ROW_HEIGHT = 60;
export const ROW_START_Y = 80;

// Traditional panel rows
export const TRADITIONAL_ROWS = [
  { bug: 'Bug: null crash', fix: 'Patch: add null check', icon: 'x' as const },
  { bug: 'Same bug: different module', fix: 'Patch: add null check', icon: 'x' as const },
  { bug: 'New bug: unicode failure', fix: 'Patch: encode input', icon: 'x' as const },
  { bug: 'Regression: null check broke edge', fix: 'Patch: add condition', icon: 'x' as const },
  { bug: 'Performance bug: O(n²)', fix: 'Patch: optimize loop', icon: 'x' as const },
  { bug: 'Another null crash', fix: 'Patch: add check again', icon: 'x' as const },
  { bug: 'New module: same bug pattern', fix: 'Patch: copy fix over', icon: 'x' as const },
  { bug: 'Race condition found', fix: 'Patch: add lock', icon: 'warn' as const },
  { bug: 'Null crash in API layer', fix: 'Patch: validate input', icon: 'x' as const },
  { bug: 'Edge case: empty string', fix: 'Patch: add guard', icon: 'x' as const },
];

// PDD panel rows
export const PDD_ROWS = [
  { text: 'Bug found: null crash', icon: 'alert' as const, color: RED },
  { text: 'pdd bug user_parser', icon: 'wall' as const, color: AMBER, isMono: true },
  { text: 'pdd fix user_parser → All tests pass ✓', icon: 'check' as const, color: GREEN, isMono: true },
];

// Animation frame markers
export const FRAMES = {
  splitDraw: { start: 0, end: 15 },
  headersFade: { start: 0, end: 20 },
  leftRow1: 20,
  rightRow1: 20,
  leftRow2: 60,
  leftRow3: 80,
  rightRow2: 60,
  leftRow4: 120,
  leftRow5: 140,
  leftRow6: 160,
  rightRow3: 120,
  pddSubtitle: 130,
  moldIcon: 200,
  autoScrollStart: 200,
  timelineStart: 280,
  timelineDraw: 60,
  calloutStart: 380,
  calloutFade: 20,
};
