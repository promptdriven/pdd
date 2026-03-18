// Component-level constants for Part2ParadigmShift10NetlistZoomUnreviewable

export const DURATION_FRAMES = 480;
export const FPS = 30;

export const BG_COLOR = "#0A0F1A";
export const DIFF_BG_COLOR = "#0F172A";

// Chip layout colors
export const CHIP_COLORS = {
  metal1: "#4A90D9",
  metal2: "#3A7ABD",
  polysilicon: "#D9944A",
  diffusion: "#5AAA6E",
  vias: "#E2E8F0",
} as const;

export const CHIP_OPACITIES = {
  metal1: 0.4,
  metal2: 0.3,
  polysilicon: 0.3,
  diffusion: 0.2,
  vias: 0.5,
} as const;

// Code diff colors
export const DIFF_COLORS = {
  added: "#5AAA6E",
  deleted: "#EF4444",
  unchanged: "#94A3B8",
  addedBg: "rgba(90, 170, 110, 0.15)",
  deletedBg: "rgba(239, 68, 68, 0.08)",
} as const;

// Counter
export const COUNTER_COLOR = "#EF4444";
export const LABEL_COLOR = "#94A3B8";

// Phase timings (frames)
export const PHASE = {
  // Phase 1: Chip layout
  chipStart: 0,
  chipZoomStart: 30,
  chipZoomEnd: 180,
  chipHoldEnd: 200,
  // Morph transition
  morphStart: 200,
  morphEnd: 240,
  // Phase 2: Code diff
  diffStart: 240,
  diffAccelEnd: 360,
  diffMaxSpeedEnd: 420,
  diffEnd: 480,
} as const;

// Zoom
export const ZOOM_INITIAL = 1;
export const ZOOM_FINAL = 8;

// Diff scroll speeds (px/frame)
export const SCROLL_SPEED_INITIAL = 2;
export const SCROLL_SPEED_MAX = 30;

// Final counter value
export const LINES_CHANGED = 10247;

// Gate grid initial dimensions
export const GATE_COLS = 160;
export const GATE_ROWS = 90;
export const GATE_WIDTH = 12;
export const GATE_HEIGHT = 12;

// Canvas dimensions
export const WIDTH = 1920;
export const HEIGHT = 1080;
