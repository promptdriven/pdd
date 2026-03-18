// constants.ts — Colors, dimensions, and timing for the 2×2 grid component

// === Canvas ===
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 750;

// === Background ===
export const BG_COLOR = '#0D1117';

// === Grid Geometry ===
export const GRID_X = 640;
export const GRID_Y = 180;
export const GRID_W = 640;
export const GRID_H = 640;
export const GRID_CENTER_X = GRID_X + GRID_W / 2; // 960
export const GRID_CENTER_Y = GRID_Y + GRID_H / 2; // 500

// Quadrant centers
export const TL_CENTER = { x: GRID_X + GRID_W / 4, y: GRID_Y + GRID_H / 4 };
export const TR_CENTER = { x: GRID_X + (3 * GRID_W) / 4, y: GRID_Y + GRID_H / 4 };
export const BL_CENTER = { x: GRID_X + GRID_W / 4, y: GRID_Y + (3 * GRID_H) / 4 };
export const BR_CENTER = { x: GRID_X + (3 * GRID_W) / 4, y: GRID_Y + (3 * GRID_H) / 4 };

// === Colors ===
export const GREEN = '#5AAA6E';
export const RED = '#E74C3C';
export const AMBER = '#D9944A';
export const BORDER_COLOR = '#334155';
export const SUBTEXT_COLOR = '#94A3B8';
export const SUMMARY_COLOR = '#E2E8F0';

// === Animation Timing (frame numbers) ===
export const TIMING = {
  // Phase 1: Grid draws in
  gridStart: 30,
  gridDrawDuration: 60, // frames 30-90
  // Phase 2: Top-left quadrant (GitHub)
  githubStart: 90,
  githubScaleDuration: 20,
  // Phase 3: Bottom-right quadrant (METR)
  metrStart: 180,
  metrScaleDuration: 20,
  // Phase 4: Intermediate quadrants
  amberStart: 270,
  amberFadeDuration: 30,
  // Phase 5: Enterprise circle
  circleStart: 330,
  circleDrawDuration: 25,
  // Phase 6: Summary line
  summaryStart: 420,
  summaryFadeDuration: 20,
} as const;

// === Enterprise Circle ===
export const ENTERPRISE_CIRCLE_RADIUS = 100;
