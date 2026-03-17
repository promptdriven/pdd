// Part1Economics05ContextWindowShrink constants

// ── Canvas ────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0D1117";
export const TOTAL_FRAMES = 900;

// ── Typography ────────────────────────────────
export const FONT_FAMILY = "'Inter', sans-serif";
export const CODE_FONT_FAMILY = "'JetBrains Mono', monospace";

// ── Grid layout ───────────────────────────────
export const GRID_CENTER_X = 560;
export const GRID_CENTER_Y = 540;
export const GRID_MAX_SIZE = 800; // max extent of grid area

// ── Context window (fixed size throughout) ────
export const CONTEXT_WINDOW_W = 480;
export const CONTEXT_WINDOW_H = 480;
export const CONTEXT_BORDER_COLOR = "#4A90D9";
export const CONTEXT_GLOW_RADIUS = 8;
export const CONTEXT_GLOW_OPACITY = 0.12;
export const CONTEXT_TINT_OPACITY = 0.04;

// ── Grid block colors ─────────────────────────
export const BLOCK_FILL = "#1A2332";
export const BLOCK_BORDER = "#334155";
export const BLOCK_CODE_COLOR = "#94A3B8";

// ── Coverage counter ──────────────────────────
export const COUNTER_X = 1400;
export const COUNTER_Y = 100;

// ── Highlight colors ──────────────────────────
export const RED_HIGHLIGHT = "#E74C3C";
export const GREEN_HIGHLIGHT = "#5AAA6E";

// ── Inset graph ───────────────────────────────
export const INSET_X = 1540;
export const INSET_Y = 750;
export const INSET_W = 320;
export const INSET_H = 200;

// ── Animation timing (frames at 30fps) ────────

// Act 1: Previous dissolves, dark bg (0-30)
export const FADE_IN_START = 0;
export const FADE_IN_END = 30;

// Act 2: 4x4 grid + context window appear (30-90)
export const GRID_APPEAR_START = 30;
export const GRID_APPEAR_END = 60;

// Act 3: Grid morphs 4→8 (90-130)
export const MORPH_4_TO_8_START = 90;
export const MORPH_4_TO_8_END = 130;

// Act 4: Grid morphs 8→16 (180-220)
export const MORPH_8_TO_16_START = 180;
export const MORPH_8_TO_16_END = 220;

// Act 5: Grid morphs 16→32 (270-310)
export const MORPH_16_TO_32_START = 270;
export const MORPH_16_TO_32_END = 310;

// Act 6: Red/green highlights appear (360-480)
export const HIGHLIGHTS_START = 360;
export const HIGHLIGHTS_STAGGER = 5; // frames between each highlight

// Act 7: Inset graph draws (480-600)
export const INSET_APPEAR_START = 480;
export const INSET_APPEAR_END = 510;
export const INSET_LINE_DRAW_START = 510;
export const INSET_LINE_DRAW_END = 540;
export const INSET_LABEL_START = 540;
export const INSET_LABEL_END = 560;

// Act 8: Hold + pulse (600-900)
export const HOLD_START = 600;
export const PULSE_CYCLE = 45;

// ── Grid stage data ───────────────────────────
export interface GridStage {
  gridSize: number;
  coverage: number;
  coverageColor: string;
  morphStart: number;
  morphEnd: number;
}

export const GRID_STAGES: GridStage[] = [
  {
    gridSize: 4,
    coverage: 80,
    coverageColor: "#5AAA6E",
    morphStart: 0,
    morphEnd: 0,
  },
  {
    gridSize: 8,
    coverage: 40,
    coverageColor: "#D9C44A",
    morphStart: MORPH_4_TO_8_START,
    morphEnd: MORPH_4_TO_8_END,
  },
  {
    gridSize: 16,
    coverage: 10,
    coverageColor: "#D9944A",
    morphStart: MORPH_8_TO_16_START,
    morphEnd: MORPH_8_TO_16_END,
  },
  {
    gridSize: 32,
    coverage: 2,
    coverageColor: "#E74C3C",
    morphStart: MORPH_16_TO_32_START,
    morphEnd: MORPH_16_TO_32_END,
  },
];

// ── Inset performance graph data ──────────────
export const PERFORMANCE_DATA = [
  { x: 0, y: 95 },
  { x: 0.15, y: 90 },
  { x: 0.3, y: 82 },
  { x: 0.5, y: 68 },
  { x: 0.7, y: 48 },
  { x: 0.85, y: 30 },
  { x: 1.0, y: 15 },
];

// ── Red highlight positions (inside window, irrelevant code) ──
// Positions as fractions of the context window area
export const RED_HIGHLIGHTS = [
  { row: 2, col: 1 },
  { row: 5, col: 3 },
  { row: 7, col: 6 },
  { row: 4, col: 5 },
];

// ── Green highlight positions (outside window, needed code) ──
// Positions as row/col in the 32x32 grid (outside the window area)
export const GREEN_HIGHLIGHTS = [
  { row: 0, col: 28 },
  { row: 14, col: 30 },
  { row: 26, col: 5 },
  { row: 30, col: 22 },
  { row: 20, col: 1 },
  { row: 28, col: 16 },
];
