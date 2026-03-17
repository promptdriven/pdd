// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A0F1A";
export const DIFF_BG_COLOR = "#0F172A";

// Total duration
export const TOTAL_FRAMES = 480;

// Phase 1: Chip Layout Zoom
export const CHIP_PHASE_START = 0;
export const CHIP_PHASE_END = 240;
export const ZOOM_START = 30;
export const ZOOM_END = 150;
export const ZOOM_HOLD_END = 200;
export const GATE_COUNT_FADE_IN = 30;
export const GATE_COUNT_FADE_DUR = 15;

// Phase 2: Code Diff
export const MORPH_START = 200;
export const MORPH_DURATION = 40;
export const DIFF_START = 240;
export const DIFF_END = 480;
export const DIFF_ACCEL_END = 360; // frame 240+120
export const DIFF_DECEL_START = 420; // frame 240+180
export const DIFF_DECEL_END = 480;

// Chip layout colors
export const CHIP_COLORS = {
  metal1: "#4A90D9",
  metal2: "#3A7ABD",
  poly: "#D9944A",
  diffusion: "#5AAA6E",
  vias: "#E2E8F0",
} as const;

export const CHIP_OPACITIES = {
  metal: 0.4,
  poly: 0.3,
  diffusion: 0.2,
  vias: 0.5,
} as const;

// Code diff colors
export const DIFF_ADDED_COLOR = "#5AAA6E";
export const DIFF_ADDED_BG_OPACITY = 0.15;
export const DIFF_DELETED_COLOR = "#EF4444";
export const DIFF_DELETED_BG_OPACITY = 0.08;
export const DIFF_UNCHANGED_COLOR = "#94A3B8";
export const DIFF_UNCHANGED_OPACITY = 0.3;

// Counter
export const COUNTER_COLOR = "#EF4444";
export const COUNTER_OPACITY = 0.5;
export const TOTAL_LINES_CHANGED = 10247;

// Gate count label
export const GATE_COUNT_COLOR = "#94A3B8";
export const GATE_COUNT_OPACITY = 0.4;

// Typography
export const CODE_FONT = "JetBrains Mono, monospace";
export const CODE_FONT_SIZE = 12;
export const COUNTER_FONT_SIZE = 16;
export const GATE_COUNT_FONT_SIZE = 14;

// Scroll speed
export const INITIAL_SCROLL_SPEED = 2; // px/frame
export const MAX_SCROLL_SPEED = 30; // px/frame

// Gate dimensions at base zoom
export const GATE_W = 2;
export const GATE_H = 3;
export const GATE_GAP = 1;

// Seeded RNG for deterministic chip layout
export function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return s / 2147483647;
  };
}
