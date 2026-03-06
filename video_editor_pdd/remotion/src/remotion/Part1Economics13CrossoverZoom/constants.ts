// Part1Economics13CrossoverZoom constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";

// Chart area (matches Part1Economics03CostCrossoverChart)
export const CHART_X = 200;
export const CHART_Y = 100;
export const CHART_W = 1620;
export const CHART_H = 780;

// Crossover point (normalized 0-1, same as 03)
export const CROSSOVER = { x: 0.42, y: 0.48 };
export const CROSSOVER_PX_X = CHART_X + CROSSOVER.x * CHART_W; // ~880
export const CROSSOVER_PX_Y = CHART_Y + CHART_H * (1 - CROSSOVER.y); // ~506

// Zoom
export const ZOOM_SCALE = 2.5;

// Colors
export const PATCHING_COLOR_START = "#EF4444";
export const PATCHING_COLOR_END = "#F59E0B";
export const GENERATION_COLOR_START = "#3B82F6";
export const GENERATION_COLOR_END = "#22C55E";
export const TOTAL_COST_COLOR = "#94A3B8";
export const AXIS_COLOR = "#94A3B8";
export const AXIS_TITLE_COLOR = "#CBD5E1";
export const GRID_COLOR = "#334155";
export const STARBURST_COLOR = "#F59E0B";
export const CALLOUT_BG = "rgba(15, 23, 42, 0.85)";
export const CONNECTING_LINE_COLOR = "#94A3B8";

// Typography
export const CALLOUT_A_SIZE = 28;
export const CALLOUT_B_SIZE = 26;

// Animation frames (210 total at 30fps = 7s)
export const TOTAL_FRAMES = 210;

// Zoom: frames 0-40
export const ZOOM_START = 0;
export const ZOOM_END = 40;

// Starburst flash: frames 20-50
export const STARBURST_FLASH_START = 20;
export const STARBURST_FLASH_END = 50;

// Starburst settle: frame 50+
export const STARBURST_SETTLE = 50;

// Callout A slides in: frames 50-80
export const CALLOUT_A_START = 50;
export const CALLOUT_A_END = 80;

// Callout B slides in: frames 70-100
export const CALLOUT_B_START = 70;
export const CALLOUT_B_END = 100;

// Connecting lines: frames 80-100
export const LINES_START = 80;
export const LINES_END = 100;

// Hold: frames 100-180
export const HOLD_START = 100;
export const HOLD_END = 180;

// Fade to black: frames 180-210
export const FADE_START = 180;
export const FADE_END = 210;

// Data points (normalized 0-1, identical to 03 chart)
export const PATCHING_POINTS = [
  { x: 0, y: 0.15 },
  { x: 0.2, y: 0.22 },
  { x: 0.4, y: 0.35 },
  { x: 0.6, y: 0.55 },
  { x: 0.8, y: 0.78 },
  { x: 1.0, y: 0.95 },
];

export const GENERATION_POINTS = [
  { x: 0, y: 0.9 },
  { x: 0.2, y: 0.72 },
  { x: 0.4, y: 0.5 },
  { x: 0.6, y: 0.35 },
  { x: 0.8, y: 0.25 },
  { x: 1.0, y: 0.18 },
];

export const TOTAL_COST_POINTS = [
  { x: 0, y: 0.82 },
  { x: 0.2, y: 0.83 },
  { x: 0.4, y: 0.84 },
  { x: 0.6, y: 0.86 },
  { x: 0.8, y: 0.87 },
  { x: 1.0, y: 0.88 },
];
