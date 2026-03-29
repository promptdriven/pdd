// ── Colors ──────────────────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.08;
export const AXIS_COLOR = '#334155';
export const AXIS_LABEL_COLOR = '#94A3B8';
export const PATCHING_COLOR = '#D9944A';
export const PDD_COLOR = '#5AAA6E';
export const GAP_LABEL_COLOR = '#E2E8F0';

// ── Dimensions ──────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Chart area (padded within canvas)
export const CHART_LEFT = 140;
export const CHART_RIGHT = 1750;
export const CHART_TOP = 80;
export const CHART_BOTTOM = 800;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// Grid
export const GRID_SPACING = 150;

// ── Typography ──────────────────────────────────────────────────────────────
export const FONT_FAMILY = 'Inter, sans-serif';

// ── Timing (frames @ 30fps) ────────────────────────────────────────────────
export const TOTAL_FRAMES = 660;
export const FPS = 30;

export const AXES_START = 0;
export const CURVE_DRAW_START = 30;
export const CURVE_DRAW_DURATION = 270; // frames 30-300
export const GAP_FILL_START = 180;
export const GAP_FILL_DURATION = 60;
export const GAP_LABEL_START = 300;
export const GAP_LABEL_FADE = 20;
export const CURVE_LABELS_START = 270;
export const CURVE_LABELS_FADE = 20;
export const THESIS_1_START = 360;
export const THESIS_2_START = 420;
export const THESIS_FADE = 25;
export const HOLD_START = 480;
export const FADEOUT_START = 600;
export const FADEOUT_DURATION = 60;

// ── Data: Patching exponential curve ────────────────────────────────────────
export const PATCHING_DATA: { x: number; y: number }[] = [
  { x: 0, y: 0.10 },
  { x: 1, y: 0.13 },
  { x: 2, y: 0.17 },
  { x: 3, y: 0.23 },
  { x: 4, y: 0.31 },
  { x: 5, y: 0.42 },
  { x: 6, y: 0.55 },
  { x: 7, y: 0.68 },
  { x: 8, y: 0.80 },
  { x: 9, y: 0.88 },
  { x: 10, y: 0.95 },
];

// ── Data: PDD flat sawtooth curve ───────────────────────────────────────────
export const PDD_BASELINE = 0.10;
export const PDD_SAWTOOTH_AMPLITUDE = 0.03;
// Generate sawtooth points between the main data points
// Each integer x has a ramp-up then drop-back pattern
export const PDD_DATA: { x: number; y: number }[] = (() => {
  const points: { x: number; y: number }[] = [];
  for (let i = 0; i <= 10; i++) {
    // Start of cycle: at baseline
    points.push({ x: i, y: PDD_BASELINE });
    if (i < 10) {
      // Ramp up in the middle of the cycle
      points.push({ x: i + 0.5, y: PDD_BASELINE + PDD_SAWTOOTH_AMPLITUDE });
      // Drop back at the end of the cycle
      points.push({ x: i + 0.95, y: PDD_BASELINE });
    }
  }
  return points;
})();

// X-axis range
export const X_MIN = 0;
export const X_MAX = 10;

// Y-axis range (in data units, 0 = no cost, 1 = max cost)
export const Y_MIN = 0;
export const Y_MAX = 1;
