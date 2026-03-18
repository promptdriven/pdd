// Constants for Part5CompoundReturns03CompoundDebtCurve

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 360;

// Colors
export const BG_COLOR = '#0F172A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.06;
export const AXIS_COLOR = '#475569';
export const AXIS_LABEL_COLOR = '#64748B';
export const DEBT_CURVE_COLOR = '#D9944A';
export const REGEN_COLOR = '#4A90D9';
export const CALLOUT_BG = '#1E293B';
export const TEXT_PRIMARY = '#E2E8F0';
export const TEXT_SECONDARY = '#94A3B8';
export const TEXT_MUTED = '#64748B';

// Chart layout
export const CHART_LEFT = 200;
export const CHART_RIGHT = 1700;
export const CHART_TOP = 200;
export const CHART_BOTTOM = 800;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// Grid spacing
export const H_GRID_SPACING = 100;
export const V_GRID_SPACING = 150;

// X-axis labels
export const X_LABELS = ['Year 1', 'Year 3', 'Year 5', 'Year 7', 'Year 10'];
// Y-axis labels
export const Y_LABELS = ['$', '$$', '$$$', '$$$$'];

// Exponential curve data points (normalized)
export const DEBT_DATA = [
  { x: 0, y: 0.04 },    // ~1.0
  { x: 0.1, y: 0.06 },  // ~1.4
  { x: 0.2, y: 0.1 },   // ~2.1
  { x: 0.35, y: 0.17 },
  { x: 0.5, y: 0.3 },
  { x: 0.6, y: 0.42 },
  { x: 0.7, y: 0.55 },
  { x: 0.8, y: 0.7 },
  { x: 0.9, y: 0.85 },
  { x: 1.0, y: 1.0 },   // ~24.0
];

// Sawtooth config
export const SAWTOOTH_BASELINE_Y = 700;
export const SAWTOOTH_PEAK_Y = 650;
export const SAWTOOTH_TEETH = 5;
export const SAWTOOTH_TOOTH_WIDTH = 300;

// Animation timing (frames)
export const AXES_START = 0;
export const AXES_DURATION = 20;
export const GRID_FADE_DURATION = 30;

export const CURVE_START = 30;
export const CURVE_DURATION = 120;
export const FORMULA_START = 120; // relative to CURVE_START sequence

export const SAWTOOTH_START = 90;
export const SAWTOOTH_DURATION = 120;

export const GAP_FILL_START = 210;
export const GAP_FILL_DURATION = 30;

export const CALLOUT_FADE_START = 210;
export const CALLOUT_FADE_DURATION = 20;

export const STAT_SCALE_START = 270;
export const STAT_SCALE_DURATION = 15;

// CISQ callout position
export const CALLOUT_X = 1100;
export const CALLOUT_Y = 450;
