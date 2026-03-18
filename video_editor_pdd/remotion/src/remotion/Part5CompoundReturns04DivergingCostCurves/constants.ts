// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = '#0F172A';
export const GRID_COLOR = '#1E293B';
export const AXIS_COLOR = '#475569';
export const AXIS_LABEL_COLOR = '#64748B';
export const TEXT_COLOR = '#E2E8F0';
export const PATCHING_COLOR = '#D9944A';
export const PDD_COLOR = '#4A90D9';
export const PILL_BG_COLOR = '#1E293B';

// ── Dimensions ──────────────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const CHART_LEFT = 180;
export const CHART_RIGHT = 1700;
export const CHART_TOP = 100;
export const CHART_BOTTOM = 780;
export const AXIS_Y = 820;

// ── Curve Data (pixel coordinates) ─────────────────────────────────
// Patching: exponential rise from shared origin
export const PATCHING_POINTS: [number, number][] = [
  [180, 780],
  [332, 755],   // ~Year 1
  [484, 720],   // ~Year 2
  [636, 670],   // ~Year 3
  [788, 590],   // ~Year 4
  [940, 480],   // ~Year 5
  [1092, 370],  // ~Year 6
  [1244, 270],  // ~Year 7
  [1396, 190],  // ~Year 8
  [1700, 100],  // ~Year 10
];

// PDD: flat / gently declining
export const PDD_POINTS: [number, number][] = [
  [180, 780],
  [332, 770],   // ~Year 1
  [484, 762],   // ~Year 2
  [636, 755],   // ~Year 3
  [788, 750],   // ~Year 4
  [940, 745],   // ~Year 5
  [1092, 740],  // ~Year 6
  [1244, 735],  // ~Year 7
  [1396, 728],  // ~Year 8
  [1700, 720],  // ~Year 10
];

// ── X-axis year labels ─────────────────────────────────────────────
export const YEAR_LABELS: { x: number; label: string }[] = [
  { x: 180, label: 'Year 0' },
  { x: 484, label: 'Year 2' },
  { x: 788, label: 'Year 4' },
  { x: 1092, label: 'Year 6' },
  { x: 1396, label: 'Year 8' },
  { x: 1700, label: 'Year 10' },
];

// ── Timing (frames) ────────────────────────────────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 420;

// Phase starts
export const AXES_START = 0;
export const AXES_DURATION = 30;
export const CURVES_START = 30;
export const CURVES_DURATION = 150;
export const GAP_FILL_START = 180;
export const GAP_FILL_DURATION = 30;
export const LABELS_START = 180;
export const ANNOTATIONS_START = 240;
export const ANNOTATIONS_DURATION = 25;
export const GAP_LABEL_START = 300;
export const GAP_LABEL_DURATION = 20;
export const DOUBLE_ARROW_DURATION = 20;
export const PULSE_CYCLE = 60;
